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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T04
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T05

/-
# Caustic `r = 1024` Halo-16 Walk `w64_m16` Part `2` (`FindAllJohnsonRampKickMuxHiW64T06`)

Certifies part `2` of the `w64_m16` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Kick mask `w64_m16` seg `5`. -/
def rkmMkHi_w64_m16_s5 : List Bool := List.replicate 874 false ++ List.map (Nat.ble 1) [
  1,1,1,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,1,1,1,1,1,0,0,0,0,0,0,1,1,1,1,1,1,1,1]
/-- Part `0` of `rkmMkHi_w64_m16_s6`. -/
def rkmMkHi_w64_m16_s6_p0 : List Bool := List.map (Nat.ble 1) [
  1,0,0,1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,1,0,1,0,1,0,
  0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,0,1,0,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,0,1,0,0,1,0,0,1,0,1,0,1,
  0,0,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1]
/-- Part `1` of `rkmMkHi_w64_m16_s6`. -/
def rkmMkHi_w64_m16_s6_p1 : List Bool := List.map (Nat.ble 1) [
  0,0,0,0,1,0,1,1,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,0,0,1,1,0,0,1,0,0,0,0,0,
  1,0,0,1,0,0,0,0,0,1,0,1,0,1,0,1,1,0,0,0,0,1,0,1,1,0,1,0,0,0,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,
  0,0,0,0,0,1,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0,0,0,1,1,1]
/-- Kick mask `w64_m16` seg `6`. -/
def rkmMkHi_w64_m16_s6 : List Bool :=
  List.replicate 763 false ++ (rkmMkHi_w64_m16_s6_p0 ++ (rkmMkHi_w64_m16_s6_p1))
/-- Kick-mask schedule for `w64_m16` `r = 1024`. -/
def rkmMasksHi_w64_m16_r1024 : List (List Bool) := [
  [], [], [], [], [], rkmMkHi_w64_m16_s5, rkmMkHi_w64_m16_s6, []]
/-- Part `0` of `rkmRowHi_w64_m16_r1024`. -/
def rkmRowHi_w64_m16_r1024_p0 : List ℕ := [95,1414,4238,8427,13766,20054,27121,34861,43327,52584,
  62917,74474,87374,101661,116794,132001,145846,156353,161294,158345,146042,124167,94515,61088,
  29753,7342,0,0,0,0,3980,15365,26498,31165,26880,15701,3927,0,0,0,517,16755,50323,90061,122439,
  135215,121848,84845,37992,4038,0,0,17654,86851,179322,252567,269002,215671,115437,23479,0,196,
  65511,209046,347339,397283,323679,165832,26141,0,18085,171383,379551,496966,435889,232414,37492,
  0,43662,265181,498555,550873,373383,110503,0,16264,221290,468697,523355,333293,76803,0,34181,
  237757,404794,360051,153950,4561,0,81491,220206,240935,126088,11242,0,16595,84882,106275,56217,
  3717,0,192,16080,22979,9166,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Part `1` of `rkmRowHi_w64_m16_r1024`. -/
def rkmRowHi_w64_m16_r1024_p1 : List ℕ := [0,0,9,0,0,0,1195,14068,16412,2436,0,0,4917,8666,4,0,
  1388,22153,18821,42,0,311,4133,0,0,0,0,0,11315,29326,10677,0,0,0,0,150,0,0,0,0,0,996,4,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,20035,12837,0,0,5001,34323,6,0,0,1463,0,0,0,701,0,0,2860,80720,0,11696,1034,
  127760,0,242040,0,16754,40936,332610,0,179244,19960,390725,9046,565333,0,839986,23618,309007,
  137595,0,0,7168,29228,291,27780,0,260018,399106,0,321800,103395,77811,2510,297866,137237,8715,
  150661,1065587,15427,176298,381348,1145398,294075,2733640,66566,43468,0,1039079,1439295,255311]
/-- Part `2` of `rkmRowHi_w64_m16_r1024`. -/
def rkmRowHi_w64_m16_r1024_p2 : List ℕ := [507965,1920641,0,46873,1656948,1159499,145934,962,
  4384151,367237,0,1677126,11469,0,3178551,1897613,195760,787291,10421,338612,1661111,111687,
  158579,2136249,1442708,9356361,1244016,71188,161329,0,533001,0,87539,723248,4229,1220869,727143,
  2277222,7096502,1939023,110146,31118,0,0,31464,524015,626112,14942,2339375,2055508,1567877,
  5921865,1447721,9,895196,25199,65642,171088,4190941,3134,10561774,959736,12545655,17586993,
  37968866,15644792,17343634,6977424,1345994,0,17813637,8033082,251262,1289,4519505,812469,617802,
  7025379,13249586,647278,7595399,547788,1109364,18648530,8814925,21200580,611481,3304894,40938029,
  5974946,10622197,296409,482086,11230646,4896073,42215222,23119813,27618450,618214,305721,0,
  52857364,44850924,7100587,23141396,50980886,6364263,4610188,1371711,3119925,7098773,2407686,
  1438888,622914,18627165,17245951,383847,16385181,736283,5298714,6647,1171178,6713020,4676448,
  2086904,19676044,107944287,940141]
/-- Part `3` of `rkmRowHi_w64_m16_r1024`. -/
def rkmRowHi_w64_m16_r1024_p3 : List ℕ := [73465355,109532733,20606175,41239341,5528597,0,340521,
  1400433,2906731,4843279,66269,17159076,254322,9841980,128350197,55176154,572709696,51222778,
  13657027,418395383,83722875,115133112,5992330,39454626,22911953,86377642,29113920,61649283,
  53856325,24228004,1536823,49544933,2160283,68734718,167865531,35685743,3005555,74044872,
  570350572,122320160,746730036,165166867,26176365,1690329,239195328,754402957,3421283728,
  276756577,248538878,7928570672,339289785,9571424,11912733,501151343,770521867,8092959116,
  560731516,96024387,2175449889,631209252,3385319580,12835464,8073166307,2149714253,194053276,
  4593120815,22427747972,25962579078,13647945204,50173857580,837393077536]
/-- Certified `rowLo12` vector for `w64_m16` `r = 1024`. -/
def rkmRowHi_w64_m16_r1024 : List ℕ :=
  List.replicate 569 0 ++ (rkmRowHi_w64_m16_r1024_p0 ++ (rkmRowHi_w64_m16_r1024_p1
  ++ (rkmRowHi_w64_m16_r1024_p2 ++ (rkmRowHi_w64_m16_r1024_p3))))

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
private abbrev bSV (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem svEq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← sntEq]; unfold bSV at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢; have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [ngEq]; omega
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
private theorem bSlZ_c (z d r p q b bz c : ℕ) (bR v cT : List ℕ) :
    bSlZ z d (r + 1) p q (b :: bz :: bR) v (c :: cT) = uCN (bSV (bHO z v) (Nat.add p bz)
      (Nat.add (Nat.mul b (bHO z cT)) q) d) (bSlZ z d r (Nat.mul b c) bz bR (bTN v) cT) := by
  cases v <;> rfl
private theorem bSlZ_0 (z d : ℕ) {t1 t2 : List ℕ} (p q : ℕ) (v c : List ℕ) :
    bSlZ z d 0 p q t1 v c = bSlZ z d 0 p q t2 v c := rfl
private theorem bSlZ_s {z d r : ℕ} {t1 t2 : List ℕ} (b bz : ℕ)
    (h : ∀ p q v c, bSlZ z d r p q t1 v c = bSlZ z d r p q t2 v c) (p q : ℕ) :
    ∀ (v c : List ℕ), bSlZ z d (r + 1) p q (b :: bz :: t1) v c =
      bSlZ z d (r + 1) p q (b :: bz :: t2) v c
  | [], [] => congrArg (uCN _) (h _ _ _ _) | [], _ :: _ => congrArg (uCN _) (h _ _ _ _)
  | _ :: _, [] => congrArg (uCN _) (h _ _ _ _)
  | _ :: _, _ :: _ => congrArg (uCN _) (h _ _ _ _)
private def bSlZ4Step (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (bR : HbZ4)
    (ih : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _ => [] | 1, p, q, v, c => bSlZ z d 1 p q [b1, z1] v c
  | 2, p, q, v, c => bSlZ z d 2 p q [b1, z1, b2, z2] v c
  | 3, p, q, v, c => bSlZ z d 3 p q [b1, z1, b2, z2, b3, z3] v c
  | 4, p, q, v, c => bSlZ z d 4 p q [b1, z1, b2, z2, b3, z3, b4, z4] v c
  | r + 5, p, q, v, c1 :: c2 :: c3 :: c4 :: cR => match v with
    | v1 :: v2 :: v3 :: v4 :: vR => uCN4 (bSV v1 (Nat.add p z1) (Nat.add (Nat.mul b1 c2) q) d)
        (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
        (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
        (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (bHO z cR)) z3) d)
        (ih (r + 1) (Nat.mul b4 c4) z4 vR cR)
    | _ => uCN4 (bSV (bHO z v) (Nat.add p z1) (Nat.add (Nat.mul b1 c2) q) d)
        (bSV (bHO z (bTN v)) (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
        (bSV (bHO z (bTN (bTN v))) (Nat.add (Nat.mul b2 c2) z3)
          (Nat.add (Nat.mul b3 c4) z2) d)
        (bSV (bHO z (bTN (bTN (bTN v)))) (Nat.add (Nat.mul b3 c3) z4)
          (Nat.add (Nat.mul b4 (bHO z cR)) z3) d)
        (ih (r + 1) (Nat.mul b4 c4) z4 (bTN (bTN (bTN (bTN v)))) cR)
  | r + 5, p, q, v, c => bSlZ z d (r + 5) p q (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) v c
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l => fun r p q v c => bSlZ z d r p q l v c
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
    bSlZ4Step z d b1 z1 b2 z2 b3 z3 b4 z4 bR (bSlZ4 z d bR)
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (r p q : ℕ) (v c : List ℕ),
    bSlZ4 z d hbz r p q v c = bSlZ z d r p q (hbz4L hbz) v c
  | HbZ4.tail _, _, _, _, _, _ => by dsimp only [bSlZ4, hbz4L]
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR, r, p, q, v, c => by
    dsimp only [bSlZ4, hbz4L, hbz4C]; match r with
    | 0 => rfl | 1 => exact bSlZ_s b1 z1 (bSlZ_0 z d) p q v c
    | 2 => exact bSlZ_s b1 z1 (bSlZ_s b2 z2 (bSlZ_0 z d)) p q v c
    | 3 => exact bSlZ_s b1 z1 (bSlZ_s b2 z2 (bSlZ_s b3 z3 (bSlZ_0 z d))) p q v c
    | 4 =>
      exact bSlZ_s b1 z1 (bSlZ_s b2 z2 (bSlZ_s b3 z3 (bSlZ_s b4 z4 (bSlZ_0 z d)))) p q v c
    | r1 + 5 => match c with
      | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl
      | c1 :: c2 :: c3 :: c4 :: cR =>
        have hr : r1 + 5 = ((((r1 + 1) + 1) + 1) + 1) + 1 := by omega
        rcases v with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> (
          rw [hr, bSlZ_c, bSlZ_c, bSlZ_c, bSlZ_c]
          dsimp only [bSlZ4Step, bHO, bTN]; rw [uCN4e]
          exact congrArg (fun x => uCN _ (uCN _ (uCN _ (uCN _ x))))
            (bSlZ4_eq z d bR (r1 + 1) (Nat.mul b4 c4) z4 _ cR))
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
private def drB : ℕ → List Bool → List Bool
  | 0, bs => bs | _, [] => [] | k + 1, _ :: bs => drB k bs
private def bEL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => match bNE a b with | true => bEL as bs | false => false
  | _, _ => false
private theorem elT : ∀ {xs ys : List ℕ}, bEL xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => Bool.noConfusion h | [], _ :: _, h => Bool.noConfusion h
  | a :: xs, b :: ys, h => by
    dsimp only [bEL] at h; revert h; cases hab : bNE a b with
    | false => intro h; exact Bool.noConfusion h | true => intro h; rw [neT hab, elT h]
private def bWCU (w0 st th d : ℕ) (b : List ℕ) (oI : ℕ) (uI : List ℕ)
    (oO : ℕ) (uO : List ℕ) (drE : ℕ) : Bool :=
  fL b fun bF => fL (mkHbZ bz0 bF) fun hbz => fL uI fun inF => fL uO fun outF =>
    match bWI bz0 w0 st th d hbz oI inF 0 with
    | none => false
    | some (oR, uR, dR) => Bool.and (bNE oR oO) (Bool.and (bEL uR outF) (bNE dR drE))
private theorem bWCU_s {w0 st th d : ℕ} {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb) {oI : ℕ} {uI : List ℕ} {oO : ℕ} {uO : List ℕ} {drE : ℕ}
    (h : bWCU w0 st th d b oI uI oO uO drE = true) :
    RkmWinIterSound st d hb oI (bD bz0 uI) oO (bD bz0 uO) drE := by
  unfold bWCU at h; dsimp only [fL] at h; simp only [rkmb_forceList_eq] at h; revert h
  cases hi : bWI bz0 w0 st th d (mkHbZ bz0 b) oI uI 0 with
  | none => intro h; cases h
  | some res =>
    rcases res with ⟨oR, uR, dR⟩; intro h
    change Bool.and (bNE oR oO) (Bool.and (bEL uR uO) (bNE dR drE)) = true at h
    simp only [Bool.and_eq_true] at h; obtain ⟨ho, hu, hd⟩ := h
    have ho1 := neT ho; have hu1 := elT hu; have hd1 := neT hd; subst ho1
    subst hu1; subst hd1; have hit := wiS bz0 w0 hhb st th d oI uI 0 oR uR dR hi
    have h2 : muxWinIterT16HiChk st th 0 d hb oI (bD bz0 uI) oR (bD bz0 uR) dR = true := by
      unfold muxWinIterT16HiChk; simp only [rkmb_forceList_eq]; rw [← hit]
      simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, muxIntListEq_eq_true]
      exact ⟨trivial, trivial, trivial⟩
    exact muxWinIterT16HiChk_sound h2
private def bWCI (w0 st th d : ℕ) (b : List ℕ) (oI : ℕ) (xI : List ℤ)
    (oO : ℕ) (uO : List ℕ) (drE : ℕ) : Bool :=
  fL xI fun inF => match bE bz0 inF with
    | none => false | some uI => bWCU w0 st th d b oI uI oO uO drE
private theorem bWCI_s {w0 st th d : ℕ} {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb) {oI : ℕ} {xI : List ℤ} {oO : ℕ} {uO : List ℕ} {drE : ℕ}
    (h : bWCI w0 st th d b oI xI oO uO drE = true) :
    RkmWinIterSound st d hb oI xI oO (bD bz0 uO) drE := by
  unfold bWCI at h; dsimp only [fL] at h; simp only [rkmb_forceList_eq] at h; revert h
  cases he : bE bz0 xI with
  | none => intro h; cases h
  | some uI => intro h; dsimp only at h; rw [← eS bz0 xI uI he]; exact bWCU_s hhb h
private theorem bChU (kT dT : ℕ) {w0 k1 k2 d o0 o1 o2 d1 d2 : ℕ} {hb x0 : List ℤ}
    {u1 u2 phb : List ℕ} (h1 : RkmWinIterSound k1 d hb o0 x0 o1 (bD bz0 u1) d1)
    (hhbT : uHb phb = rkmDropInts w0 hb)
    (h2 : bWCU w0 k2 100000000 d phb o1 u1 o2 u2 d2 = true)
    (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d hb o0 x0 o2 (bD bz0 u2) dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (bWCU_s hhbT h2)
private theorem swMk {nSub d oI oO drS : ℕ} {hb xI xO : List ℤ}
    (hhb : hb.length = d) (hble : Nat.ble (Nat.add oI (altIntLen xI)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb oI xI oO xO drS) :
    RkmWinSegWalkSound nSub ⟨d, hb, oI, xI, oO, xO, drS⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private theorem swMkM {nP nSub d oI oO drS oPrev drPrev : ℕ}
    {hPr iPr oPr hb xI xO : List ℤ} (mk : List Bool)
    (hprev : RkmWinSegWalkSound nP ⟨d, hPr, oPrev, iPr, oI, oPr, drPrev⟩)
    (hiter : RkmWinIterSound nSub d hb oI xI oO xO drS) (hhb : hb.length = d)
    (hmk : xI = rkmApplyMaskBits mk oPr) :
    RkmWinSegWalkSound nSub ⟨d, hb, oI, xI, oO, xO, drS⟩ := by
  have hin : oI + xI.length ≤ d + 1 := by rw [hmk, rkmApplyMaskBits_length]; exact hprev.2.2.1
  exact ⟨hhb, hin, (hiter hhb hin).1, (hiter hhb hin).2⟩
private def phb_s5_p0 : List ℕ := [540328962279669,539208496570247,538084331690425,536956452979963,
  535824845578168,534689494420742,533550384236569,532407499544437,531260824649681,530110343640769,
  528956040385805,527797898528964,526635901486844,525470032444748,524300274352883,523126609922470,
  521949021621779,520767491672072,519582002043459,518392534450660,517199070348677,516001590928366,
  514800077111912,513594509548201,512384868608091,511171134379569,509953286662803,508731304965082,
  507505168495632,506274856160321,505040346556236,503801617966130,502558648352749,501311415353014,
  500059896272072,498804068077203,497543907391579,496279390487879,495010493281742,493737191325064,
  492459459799133,491177273507590,489890606869225,488599433910581,487303728258387,486003463131788,
  484698611334393,483389145246106,482075036814759,480756257547529,479432778502126,478104570277763,
  476771603005881,475433846340638,474091269449139,472743841001415,471391529160127,470034301569998,
  468672125346958,467304967066994,465932792754694,464555567871480,463173257303510,461785825349244,
  460393235706668,458995451460151,457592435066931,456184148343218,454770552449897,453351607877814,
  451927274432641,450497511219296,449062276625900,447621528307261,446175223167874,444723317344393,
  443265766187590,441802524243758,440333545235543,438858782042187,437378186679162,435891710277157,
  434399303060419,432900914324390,431396492412650,429885984693098,428369337533382,426846496275518,
  425317405209673,423782007547093,422240245392119,420692059713265,419137390313330,417576175798474,
  416008353546251,414433859672526,412852628997244,411264595008997,409669689828338,408067844169787,
  406458987302474,404843047009351,403219949544924,401589619591423,399951980213349,398306952810318,
  396654457068133,394994410907984,393326730433715,391651329877039,389968121540621,388277015738922,
  386577920736693,384870742685011,383155385554723,381431751067184,379699738622147,377959245222655,
  376210165396788,374452391116109,372685811710618,370910313780049,369125781101312,367332094531861,
  365529131908787,363716767943381,361894874110940,360063318535528]
private def phb_s5_p1 : List ℕ := [358221965869426,356370677166956,354509309752365,352637717081413,
  350755748596308,348863249573585,346960060964500,345046019227502,343120956152280,341184698674868,
  339237068683257,337277882812887,335306952231400,333324082411927,331329072894179,329321717032517,
  327301801730123,325269107158333,323223406460103,321164465436498,319092042214999,317005886898335,
  314905741192408,312791338011785,310662401061077,308518644390378,306359771922779,304185476951777,
  301995441606209,299789336280112,297566819024647,295327534898974,293071115276630,290797177103632,
  288505322104133,286195135929032,283866187242456,281518026740474,279150186095810,276762176821614,
  274353489046585,271923590192832,269471923546880,266997906713086,264500929937392,261980354287927,
  259435509677187,256865692708644,254270164328341,251648147259458,248998823194817,246321329718854,
  243614756926474,240878143701519,238110473612025,235310670372914,232477592819083,229610029322772,
  226706691578216,223766207663733,220787114275844,217767848011414,214706735551208,211601982570821,
  208451661171369,205253695581116,202005845828166,198705689020949,195350597793716,191937715374060,
  188463926602120,184925824068014,181319668323357,177641340848093,173886288092327,170049454431923,
  166125201229537,162107208311199,157988352951503,153760559755203,149414612395204,144939914648452,
  140324182971264,135553045000879,130609506211139,125473227601428,120119525523793,114517950653104,
  108630207037182,102406992908535,95782990012395,88668472556053,80934244623273,72381987847174,
  62677810015780,51170580129421,36179035075236]
private def phb_s5 : List ℕ :=
  phb_s5_p0 ++ (phb_s5_p1)
private def u5_o : List ℕ := [9999999625933844,9999999743364415,10000000316093828,
  10000000851626877,10000000834437856,9999999968849779,9999998786367453,9999998076062495,
  9999998770961712,10000000928946222,10000003428612016,10000004114332387,10000001665630631,
  9999996825273690,9999992479756904,9999992163040207,9999997731872459,10000007562926358,
  10000015959338423,10000016033029293,10000004180994364,9999984362025190,9999967376735681,
  9999966406864461,9999988684371073,10000028208983227,10000065106386106,10000073766021127,
  10000036851138184,9999960207349920,9999877185530375,9999837263134312,9999881952433411,
  10000017679954816,10000199046952688,10000337807144403,10000337635013865,10000144831666935,
  9999791882378084,9999408356252129,9999185688414108,9999300502048039,9999821876402377,
  10000644553665115,10001483686916623,10001949717951287,10001691003150120,10000556733198556,
  9998720426538364,9996702469255084,9995263667230432,9995182118069966,9996971336908068,
  10000627686680570,10005497211366205,10010325313784614,10013503005264282,10013463233334122,
  10009135644238303,10000341745558937,9988022480041574,9974228194328049,9961856043737178,
  9954184386418797,9954296463466758,9964513936362587,9985953956170021,10018292352226281,
  10059772527993948,10107445107413695,10157583978301063,10206194087199282,10249520945743988,
  10284481624577311,10308959675153659,10321940548810442,10323488975547051,10314598736410929,
  10296955632625471,10272662574635015,10243968618171992,10213036466584467,10181768084981383,
  10151696486226299,10123940765259639,10099212553624876,10077861784370407,10059943502909453,
  10045294506023263,10033607304310878,10024495509121011,10017545257547203,10012353725833206,
  10008553085090781,10005824343727120,10003901649615089,10002571642908846,10001667862902354,
  10001064501624077,10000668501953513,10000413105854728,10000251044068314,10000149999930868,
  10000087949966149,10000050598346352,10000028413913299,10000015542990555,10000008088228433,
  10000003928266152,10000001597601973,10000000481815816]
private def xo_s5b : List ℤ := bD bz0 u5_o
private def c5_1 : List ℕ := [10000000198666367,10000000227227181,9999999866580627,
  9999999448451966,9999999347765180,9999999942481896,10000000904268328,10000001594013397,
  10000001421699257,10000000008265572,9999997811692184,9999996234548189,9999996930191323,
  10000000285347424,10000005002605966,10000008229559159,10000007047865077,10000000337189363,
  9999990345991546,9999982575955748,9999983451047856,9999995729634223,10000016215465211,
  10000035106120536,10000039586724912,10000020761817749,9999980446778131,9999934484366502,
  9999908395844147,9999925840305416,9999994601741695,10000096313941766,10000187411670373,
  10000212978509942,10000132513505161,9999945924607220,9999707927806987,9999519566625876,
  9999494769926474,9999710758543652,10000159359458205,10000722411368515,10001187532987779,
  10001309511294203,10000902347984621,9999934444654663,9998588939307347,9997259225967770,
  9996466387071545,9996710062904094,9998288410987646,10001141088417081,10004770021614608,
  10008273691058636,10010507575023112,10010344735580994,10006982042750428,10000220308201618,
  9990648017952347,9979674615788924,9969395229505247,9962303281813389,9960902154837354,
  9967289064118805,9982788771990652,10007702491590338,10041216846249411,10081481278033877,
  10125835730921840,10171143710859897,10214171764783874,10251956105222683,10282105290655498,
  10303002547985770,10313894812445343,10314870583900995,10306746861596030,10290894550460810,
  10269032549839443,10243023384909336,10214691449238667,10185681720347721,10157365125678272,
  10130790489397844,10106677255466904,10085439596659723,10067231162569551,10052001326572350,
  10039552584703214,10029594921045482,10021791782042081,10015795479566918,10011273584776914,
  10007924785693284,10005487921014386,10003744597286453,10002517847413692,10001668591315858,
  10001089804850703,10000701508646522,10000444966949336,10000278017733872,10000171100287406,
  10000103558385774,10000061626329316,10000035920188926,10000020456880070,10000011231456577,
  10000005941703843,10000002886364021,10000001180934408,10000000370214095]
private def hb_s6 : List ℤ := altBuildHbFrom 1856 1024 19587930735 0 1024
private def xi_s6 : List ℤ := rkmApplyMaskBits (drB 844 rkmMkHi_w64_m16_s5) xo_s5b
private def phb_s6_p0 : List ℕ := [710760761107562,710292130629101,709820734544520,709346573830995,
  708869649435963,708389962277058,707907513242048,707422303188767,706934332945048,706443603308648,
  705950115047183,705453868898045,704954865568332,704453105734762,703948590043598,703441319110563,
  702931293520752,702418513828547,701902980557525,701384694200370,700863655218773,700339864043341,
  699813321073493,699284026677365,698751981191701,698217184921749,697679638141155,697139341091851,
  696596293983940,696050496995587,695501950272893,694950653929783,694396608047877,693839812676369,
  693280267831897,692717973498415,692152929627057,691585136136005,691014592910351,690441299801952,
  689865256629292,689286463177333,688704919197366,688120624406862,687533578489314,686943781094084,
  686351231836239,685755930296391,685157876020529,684557068519853,683953507270599,683347191713866,
  682738121255436,682126295265600,681511713078962,680894373994265,680274277274189,679651422145165,
  679025807797176,678397433383554,677766298020780,677132400788276,676495740728193,675856316845200,
  675214128106262,674569173440425,673921451738584,673270961853264,672617702598378,671961672749000,
  671302871041118,670641296171397,669976946796928,669309821534977,668639918962731,667967237617037,
  667291775994143,666613532549424,665932505697113,665248693810029,664562095219289,663872708214030,
  663180531041114,662485561904841,661787798966643,661087240344788,660383884114067,659677728305484,
  658968770905939,658257009857906,657542443059104,656825068362164,656104883574296,655381886456944,
  654656074725434,653927446048630,653195998048566,652461728300088,651724634330480,650984713619092,
  650241963596958,649496381646408,648747965100673,647996711243492,647242617308700,646485680479821,
  645725897889649,644963266619824,644197783700399,643429446109409,642658250772418,641884194562077,
  641107274297661,640327486744606,639544828614034,638759296562280,637970887190400,637179597043679,
  636385422611127,635588360324975,634788406560150,633985557633756,633179809804537,632371159272336,
  631559602177545,630745134600546,629927752561143,629107452017985]
private def phb_s6_p1 : List ℕ := [628284228867985,627458078945719,626628998022825,625796981807391,
  624962025943332,624124126009753,623283277520311,622439475922561,621592716597292,620742994857853,
  619890305949468,619034645048545,618176007261962,617314387626359,616449781107400,615582182599037,
  614711586922756,613837988826814,612961382985460,612081763998144,611199126388719,610313464604623,
  609424773016049,608533045915104,607638277514956,606740461948960,605839593269775,604935665448465,
  604028672373589,603118607850266,602205465599239,601289239255906,600369922369353,599447508401357,
  598521990725380,597593362625540,596661617295575,595726747837775,594788747261910,593847608484129,
  592903324325849,591955887512619,591005290672964,590051526337218,589094586936323,588134464800622,
  587171152158619,586204641135725,585234923752978,584261991925744,583285837462394,582306452062956,
  581323827317744,580337954705964,579348825594298,578356431235454,577360762766700,576361811208363,
  575359567462311,574354022310397,573345166412885,572332990306836,571317484404476,570298638991529,
  569276444225517,568250890134033,567221966612980,566189663424780,565153970196542,564114876418211,
  563072371440661,562026444473776,560977084584472,559924280694701,558868021579404,557808295864427,
  556745092024409,555678398380608,554608203098706,553534494186561,552457259491911,551376486700048,
  550292163331431,549204276739263,548112814107013,547017762445891,545919108592278,544816839205097,
  543710940763136,542601399562312,541488201712888,540371333136629,539250779563895,538126526530683,
  536998559375605,535866863236802,534731423048795,533592223539271,532449249225802,531302484412494,
  530151913186567,528997519414859,527839286740263,526677198578078,525511238112287,524341388291760,
  523167631826362,521989951182989,520808328581509,519622745990617,518433185123601,517239627434007,
  516042054111216,514840446075919,513634783975483,512425048179226,511211218773574,509993275557113,
  508771198035523,507544965416400,506314556603959,505079950193606,503841124466394,502598057383339,
  501350726579609,500099109358572,498843182685700,497582923182334]
private def phb_s6_p2 : List ℕ := [496318307119291,495049310410322,493775908605406,492498076883883,
  491215790047421,489929022512802,488637748304534,487341941047275,486041573958073,484736619838403,
  483427051066002,482112839586505,480793956904852,479470374076485,478142061698310,476808989899429,
  475471128331616,474128446159562,472780912050839,471428494165611,470071160146066,468708877105554,
  467341611617440,465969329703651,464591996822897,463209577858584,461822037106373,460429338261402,
  459031444405147,457628317991900,456219920834878,454806214091919,453387158250773,451962713113959,
  450532837783188,449097490643317,447656629345836,446210210791858,444758191114598,443300525661328,
  441837168974776,440368074773958,438893195934422,437412484467877,435925891501181,434433367254675,
  432934861019828,431430321136166,429919694967464,428402928877163,426879968202991,425350757230750,
  423815239167231,422273356112234,420725049029646,419170257717543,417608920777273,416040975581479,
  414466358241015,412885003570716,411296845053959,409701814805972,408099843535844,406490860507157,
  404874793497200,403251568754698,401621110955973,399983343159493,398338186758712,396685561433133,
  395025385097510,393357573849110,391682041912918,389998701584724,388307463171954,386608234932168,
  384900923009082,383185431366012,381461661716608,379729513452733,377988883569354,376239666586281,
  374481754466605,372715036531646,370939399372248,369154726756205,367360899531631,365557795526035,
  363745289440884,361923252741396,360091553541295,358250056482247,356398622607680,354537109230651,
  352665369795430,350783253732418,348890606306017,346987268455011,345073076625024,343147862592556,
  341211453280069,339263670561587,337304331058171,335333245922655,333350220612917,331355054652949,
  329347541380905,327327467683258,325294613714107,323248752598617,321189650119488,319117064385235,
  317030745478990,314930435086401,312815866101090,310686762206003,308542837428811,306383795669386,
  304209330197175,302019123116089,299812844794318,297590153256208,295350693533086,293094096969582,
  290819980481676,288527945762290,286217578429830,283888447114599]
private def phb_s6_p3 : List ℕ := [281540102477433,279172076154332,276783879620140,274375002963573,
  271944913564978,269493054667224,267018843828998,264521671248428,262000897943538,259455853774279,
  256885835288967,254290103375688,251667880696671,249018348880570,246340645444192,243633860411091,
  240897032589740,238129145468473,235329122677809,232495822963161,229628034601756,226724469186805,
  223783754689044,220804427690247,217784924664680,214723572161895,211618575716778,208468007279268,
  205269790914853,202021686475986,198721270881101,195365916558420,191952766511517,188478705336250,
  184940325355538,181333886827762,177655270909905,173899923694996,170062789162454,166138228232770,
  162119920236369,158000741889301,153772617163075,149426329007881,144951280369744,140335186741744,
  135563674634086,130619748187956,125483066807819,120128944910110,114526930781961,108638725468147,
  102415023335092,95790501005980,88675425652092,80940591226068,72387663809537,62682725007772,
  51174592761507,36181872118644]
private def phb_s6 : List ℕ :=
  phb_s6_p0 ++ (phb_s6_p1 ++ (phb_s6_p2 ++ (phb_s6_p3)))
private def u6_o_p0 : List ℕ := [10000000107070726,9999999609517169,10000001004972796,
  9999998176619236,10000002945453105,9999995736687563,10000005809958674,9999992348256467,
  10000009563659547,9999988243045595,10000014125591792,9999983391294597,10000019262343951,
  9999977985754847,10000024807843227,9999972366994200,10000030333213149,9999967041216338,
  10000035198073546,9999962977864884,10000038418238822,9999960955985433,10000038924211746,
  9999962141169164,10000035784981975,9999967346394517,10000028405260216,9999976812959343,
  10000017182693371,9999989481252158,10000003692711398,10000003038593598,9999991003142577,
  10000013580262853,9999983579688991,10000016693296245,9999986042183603,10000007783825501,
  10000002204292087,9999983923182490,10000033756510638,9999944966656486,10000079258014930,
  9999894105413381,10000134068772092,9999837005728868,10000191865128435,9999780097607674,
  10000246714380096,9999727902286458,10000295985273481,9999680952224247,10000341771431819,
  9999634974097270,10000389808935109,9999583332248414,10000446050419045,9999522339579945,
  10000510501512811,9999457177610726,10000571988236349,9999405302645406,10000607328834948,
  9999393985369880,10000587676289002,9999450096888401,10000491735630758,9999585976043221,
  10000319256378946,9999788138586308,10000097859157352,10000016124263160,9999877414267237,
  10000214592038934,9999714010631410,10000331739437049,9999651199625358,10000335643754634,
  9999707529706471,10000221358393917,9999874170554515,10000010951763765,10000116353016349,
  9999752112648564,10000373491064400,9999518211602633,10000560882838783,9999400911782427,
  10000586652665423,9999482265969565,10000391609918672,9999785275145052,10000000783813428,
  10000229584596350,9999549782160029,10000632576609519,9999250423856982,10000779318565551,
  9999290174659032,10000541636714048,9999710322611888,9999983308976930,10000336482683459,
  9999377994251050,10000825275317854,9999093321402330,10000842632714033,9999367385568651,
  10000302793463330,10000095437137489,9999508156716272,10000808913784775,9999021739266369,
  10000956102288539,9999263681641731,10000356503636407,10000106569931435,9999448424133077,
  10000874983445651,9999002367483429,10000886169369234,9999435292480720,10000111869966053,
  10000358063604387,9999275034491302,10000895219224266,9999171198154831,10000550598004531]
private def u6_o_p1 : List ℕ := [9999856717337870,9999723263628011,10000593686544314,
  9999273588655064,10000650456606710,9999596900585348,10000068743267239,10000249584073099,
  9999537378832136,10000520478925093,9999575116802454,10000223070696984,10000011845011160,
  9999793642068356,10000309854990432,9999692370337529,10000219770011527,9999910071774273,
  9999966470320587,10000114861786560,9999858822366734,10000122752444531,9999915610713171,
  10000051007457593,9999964943517909,10000031312256083,9999979057816883,9999984612488427,
  10000082017701662,9999840593662000,10000207904151019,9999815381239342,10000069329013767,
  10000115319918339,9999698084797288,10000400288747921,9999660991772977,10000108958203633,
  10000216423149041,9999500381674136,10000595816498284,9999574173246643,10000030114433437,
  10000431401643305,9999258548613168,10000727848611926,9999641007497419,9999779428244498,
  10000742789613559,9999059614234999,10000685338849999,9999930017773710,9999380121799815,
  10001037440252128,9999048428692879,10000376171361466,10000418851997517,9998967556050451,
  10001136031888594,9999347434842439,9999811281722128,10000958278361313,9998754614882500,
  10000879266060096,9999967147780347,9999145580275529,10001303207941762,9998945804259839,
  10000220688032801,10000756524419960,9998661546833747,10001185447464882,9999641462250460,
  9999305337338489,10001377256512915,9998719336314373,10000433549607691,10000691747351895,
  9998563726357721,10001340074497124,9999568111731305,9999237408009862,10001518384558706,
  9998647648301882,10000338600732466,10000910661768957,9998390508496477,10001295101096180,
  9999857971305187,9998876307073977,10001678159706682,9998860309569734,9999840188072083,
  10001370693239286,9998320881669030,10000859598667429,10000551696214883,9998399363656445,
  10001559963249563,9999559161850709,9999006173310564,10001743652875149,9998729374919338,
  9999893880659151,10001415688793650,9998283540624664,10000778676150846,10000730158131525,
  9998288127059226,10001437030538683,9999904219122956,9998678041854642,10001751951246235,
  9999140521552843,9999311409611665,10001713108064183,9998579214321359,10000028178885499,
  10001387252765483,9998283684244464,10000693014165023,10000878919471704,9998250695155536,
  10001217057496583,10000295553108835,9998432643823695,10001560932338308,9999725060351943]
private def u6_o_p2 : List ℕ := [9998761627407367,10001725997032236,9999226136377535,
  9999168756046599,10001740320291625,9998827205085626,9999595713598595,10001645403726895,
  9998533057368003,10000000063478783,10001485366000971,9998332182372212,10000354587514101,
  10001300552894605,9998205046972289,10000644529050229,10001123824328556,9998130349607519,
  10000863284853791,10000979501794661,9998090150549396,10001008419630009,10000883194950470,
  9998072908296971,10001079103815176,10000841863330325,9998075037029711,10001075172761390,
  10000853413530362,9998101093311380,10000998007763842,10000906041595053,9998162249331001,
  10000853657749238,10000977989165562,9998271898807452,10000656983214119,10001038896968400,
  9998439030637217,10000436387314990,10001054705212688,9998658250811153,10000235124214283,
  10000998649351733,9998899931434880,10000105513579199,10000868231720746,9999104609845961,
  10000090993300188,10000704764566753,9999192156550519,10000195127882596,10000604084494210,
  9999093826817423,10000345654976251,10000700149389221,9998809552210565,10000375528682767,
  10001105249561012,9998472039229383,10000056546551264,10001806185009214,9998373192628934,
  9999212744038197,10002557670109166,9998889027292876,9997902663603109,10002862045312268,
  10000264840161440,9996576293770368,10002140550907228,10002317603539691,9996040965133277,
  10000118088511190,10004254515682399,9997099300241507,9997248791778793,10004865446766752,
  9999935053116113,9994829799325441,10003182786204252,10003614400235755,9994510430351884,
  9999329528804694,10006182544058715,9997261468103679,9994986052251225,10005586783548067,
  10002311992531427,9992925812718314,10001186433284562,10006828742689942,9995403639366746,
  9995052860926970,10007138686163391,10001897173689071,9991685565189300,10001656577901792,
  10007969698695066,9994962628526562,9993737184361893,10007700487922185,10003567632882537,
  9990687512776162,9999645451879969,10009765480273900,9997082443474215,9990858289499293,
  10005877101115095,10007652004419455,9991721749159366,9994431684041324,10010005735700491,
  10003166120416444,9988942995581449,9999316518692810,10011511973065268,9998299555162201,
  9988498958787846,10003870530621431,10011177963118480,9994230470014060,9989300537600657,
  10007383530477054,10010213812048208,9991275323569796,9990145089066069,10009812354757095]
private def u6_o_p3 : List ℕ := [10009740313767795,9989344121070562,9990030724293934,
  10011239190230418,10010620325281125,9988489030654033,9988254104984543,10011378146783642,
  10013367299394397,9989298818129462,9984530654257621,10009282711296773,10017987805430527,
  9993157868534102,9979234523357394,10002982597746267,10023439844751089,10002797975879692,
  9974759017108224,9989057130278486,10024762820581902,10021402252181074,9980087203494705,
  9967072171992794,10008323185392068,10042318227272524,10011601511074315,9956092329722289,
  9961143782810080,10029610848877686,10066578074701800,10008965591242338,9923072698296362,
  9928371504499122,10038820602072929,10128311361072202,10073448870922499,9906338732009381,
  9797625504421676,9888436735607142,10153360782737407,10427699542837816,10552923994423877,
  10491523812009062,10322426522189463,10153936148743779,10047495311225185]
private def u6_o : List ℕ :=
  u6_o_p0 ++ (u6_o_p1 ++ (u6_o_p2 ++ (u6_o_p3)))
private def xo_s6 : List ℤ := bD bz0 u6_o
private def c6_1_p0 : List ℕ := [9999999874081821,10000000441861549,9999998979450858,
  10000001999919919,9999996382206290,10000006226410914,9999989763964916,10000015944136188,
  9999976670862201,10000031986565091,9999958801371275,10000049936111754,9999942925162460,
  10000062232259126,9999934243285153,10000066501899737,9999939447005993,10000042117689818,
  9999994999010514,9999952756604820,10000092062910616,9999899287511832,10000058498660198,
  10000016128572559,9999936770904957,10000045391521215,9999992842664814,10000025746614099,
  9999871964233726,10000220604153079,9999838691136128,10000010692185744,10000011796727116,
  10000170800310078,9999560727681986,10000600454976080,9999357267643962,10000711383620044,
  9999302918994870,10000594852744683,9999308870646220,10000947901776124,9998693567087531,
  10001546770823276,9999040059474083,9999629569777226,10001714370006590,9997750185158058,
  10001180201104495,10000573818259112,9998440954827092,10001757296862815,9998923326902041,
  9999517768394688,10000198846025118,10001796258484864,10000447432313139,9997237828944501,
  10001183956516360,10000877045196802,9997792485963467,10002377666100163,10001206283388014,
  9994527703552549,10000046659457141,10007778447663561,10001509486650747,9994300989964474,
  9998506775738277,10003732892562936,10003198908675998,10003650208910047,10005073975523159,
  10000147898303641,9993077676477987,9996980946561164,10012170325480456,10022217527116701,
  10014494003545548,9996037950386429,9985722594661087,9994912927791957,10018134482133088,
  10039811585528549,10047207361798964,10038144337547656,10020151655052642,10004701374675784,
  10001529865499398,10015664526077429,10047151926058256,10092306273768505,10145360592869667,
  10199923550040990,10250059960980050,10291006547467650,10319570039522641,10334252871238230,
  10335146754028749,10323650864377892,10302081057678985,10273245159922104,10240047036696839,
  10205168268125069,10170850172224050,10138781563199840,10110077448594828,10085327887377086,
  10064689342396444,10047995984967406,10034870008241411,10024819241454760,10017314151397373,
  10011842649298862,10007944681313584,10005228679591562,10003376762318195,10002140255851286,
  10001331368533186,10000812909077749,10000487068564453,10000286421357330,10000165137918343,
  10000093219118879,10000051442451622,10000027552474032,10000014282060939,10000006954430859]
private def c6_1_p1 : List ℕ := [10000003072118466,10000001128295023,10000000210542036]
private def c6_1 : List ℕ :=
  c6_1_p0 ++ (c6_1_p1)
private def c6_2_p0 : List ℕ := [10000000239440607,9999999222833602,10000001618092830,
  9999997181383658,10000004508181636,9999993128843558,10000010111406121,9999985592888106,
  10000019856405504,9999973584786288,10000033836381748,9999958371388915,10000049057300480,
  9999944799905859,10000059047080866,9999940389843735,10000056000675531,9999952528872953,
  10000033492746259,9999985990322802,9999989986702317,10000035821396316,9999941712010006,
  10000070243163239,9999935591488809,10000036947132668,10000008717834646,9999939482606344,
  10000101466844144,9999881409196244,10000112531613797,9999899851837843,10000105039031392,
  9999859812685796,10000196616560441,9999748378505654,10000294665905731,9999652141749613,
  10000453038490820,9999375472193588,10000809653651677,9999089130162968,10000870969768206,
  9999255871489722,10000662211361044,9999298124770897,10000780156686108,9999294086753544,
  10000354005188533,10000218544530083,9999177488415534,10001247463321286,9998706511832075,
  10000785709367259,10000273514028595,9998505978355546,10002172695048611,9998198956217144,
  10000561535883825,10000763386649771,9998611455446772,10001077754288718,9999722377205530,
  9999722046749224,10000239978281172,10000038150607104,10000070381543383,9999383393544178,
  10000856273971664,9999824050250465,9998947321901797,10001658444550325,9999410167909792,
  9998420568743603,10002394516937699,9999628560282636,9997511657364225,10002516122132653,
  10000869070213769,9996749337233333,10001162233471172,10002233089260036,9997510144524237,
  9999860033179748,10002861506604610,9997900387191687,9997337231750944,10003808885725538,
  10002449193242746,9995437329068065,9997552165298452,10004186925200371,10002323734909634,
  9996870582864325,9998069488374407,10001845981167808,10001362746626420,9999944430184949,
  10000726930664208,9999624488072434,9996284330859341,9997729580193939,10004756144608266,
  10007017361530026,9998738835893941,9989993373601425,9993924884472433,10007777965646732,
  10015061871944103,10006068641876940,9990008100031455,9984551246448808,9996463995343432,
  10015041944128790,10023420482355160,10014399989284769,9995837403524750,9982926863164672,
  9986051371472151,10004125217023882,10026759152810733,10041724625719030,10041959060475926,
  10028455945434322,10008794726744074,9993275760563617,9990957839557228,10007054053162470]
private def c6_2_p1 : List ℕ := [10042071560401016,10092365655882368,10151514792748571,
  10211955121356216,10266475516494301,10309335204060658,10336907491046755,10347854986579061,
  10342914462677094,10324416466468666,10295675130352655,10260377194248584,10222063518002620,
  10183759281261219,10147769021009424,10115619119318740,10088115055784777,10065468837490871,
  10047458618442109,10033587394248463,10023219937821527,10015688339946796,10010363288030445,
  10006695220070977,10004231477589882,10002616874938417,10001583631819164,10000937883803532,
  10000543572011087,10000308125117861,10000170707929817,10000092320799294,10000048558299162,
  10000024674697154,10000011992900313,10000005445145833,10000002146556759,10000000575625288]
private def c6_2 : List ℕ :=
  c6_2_p0 ++ (c6_2_p1)
private def c6_3_p0 : List ℕ := [9999999742196084,10000000824058578,9999998245774791,
  10000003178459378,9999994876485904,10000007460989829,9999989760397563,10000013832633389,
  9999981611650859,10000023727704906,9999970133836133,10000036412552946,9999957050105076,
  10000048843182085,9999946655962641,10000055625627359,9999945117536403,10000050443401359,
  9999958101990415,10000029226273616,9999987068102554,9999994179154269,10000025084318878,
  9999957922060395,10000053324334350,9999944888234599,10000044371464809,9999980114687646,
  9999983463560067,10000059529908508,9999899024909114,10000132426374140,9999851309195061,
  10000151119861876,9999851336391785,10000155277356234,9999815950181725,10000240731496477,
  9999679361599195,10000411655058899,9999497864789144,10000588116219139,9999326803863081,
  10000759157014848,9999166045322347,10000869198785002,9999165354391452,10000722600074955,
  9999438706034484,10000398521914395,9999739739496411,10000118117407202,10000094808478136,
  9999585652512348,10000770965152015,9999015858853614,10000857055349410,9999681713302115,
  9999504598334333,10001283544716960,9998277198945017,10001608655742376,9999068042005343,
  9999894901148229,10001117886993673,9998349058420029,10001407318234380,9999505872510123,
  9999447094716680,10001100073196238,9999106509660009,10000250034589159,10000252433662646,
  9999698594698963,10000079880988447,10000001761122936,10000227861873024,9999497217349484,
  10000377899577109,10000275753969325,9999011923381173,10000987279863356,10000015329290331,
  9998718201984773,10001535366440829,9999735091200126,9998507617328700,10001946809565270,
  9999618619424743,9998194123825065,10002232085426273,9999871342965177,9997651785491470,
  10002195203985717,10000700035457455,9997131635782850,10001434052235922,10001866065868978,
  9997269130706479,10000031399733589,10002654278355373,9998217111634861,9998535835935731,
  10002723402962251,9999769932126288,9997251407323321,10001881590852891,10002166718121580,
  9996838458393671,9998575811735990,10003918447356742,10000863764186292,9995896433914149,
  9999394116692403,10003738999249269,10000568684318782,9997098264478715,9999465744285308,
  10001733009261697,10000216722705666,9999495218730011,10000592148601545,9999602790591788,
  9998114277284393,10000636912101116,10003589145513473,10000266363744139,9994623822084223]
private def c6_3_p1 : List ℕ := [9996820525352862,10005529923278267,10007634608612383,
  9998238035398598,9989770020770883,9994913085665937,10007981541452853,10011755412605275,
  10000329045359015,9987158702966479,9988456990090731,10003638951458931,10016189882611925,
  10012394064840861,9995867379364033,9983120211884309,9986760656762832,10003967624224896,
  10020050274681257,10021780346598888,10007932393415305,9989222913908891,9979564028763941,
  9986370703881635,10006486651082853,10029100926960306,10042498754674457,10040208021864914,
  10023654360264455,10000946055477647,9983226460165010,9980569271839519,9998941926970389,
  10038918903708570,10096077404078605,10162557227747062,10229123874336818,10287143695925681,
  10330065258535201,10354211725832668,10358886487367221,10345931663422219,10318953272147399,
  10282438613434168,10240949592138810,10198512218664433,10158252047206647,10122263292811867,
  10091661836921018,10066756197459484,10047270807834840,10032569881321930,10021848897182852,
  10014277613470651,10009092343119457,10005644570545041,10003416841451816,10002017103921491,
  10001161346750020,10000652007271298,10000356774772598,10000190121326134,10000098521049835,
  10000049479356564,10000023883830198,10000010878466179,10000004504562685,10000001567389037,
  10000000365480258]
private def c6_3 : List ℕ :=
  c6_3_p0 ++ (c6_3_p1)
private def c6_4_p0 : List ℕ := [9999999779753455,10000000712638936,9999998402063082,
  10000002991599044,9999995256425391,10000006793485892,9999990514626268,10000012699761190,
  9999983560002666,10000020756223990,9999974266232424,10000031265030775,9999962998509240,
  10000042540091077,9999952526288220,10000051150721514,9999947305541635,10000051488834477,
  9999952713370912,10000039805331346,9999971091957863,10000015068553316,10000000769324150,
  9999982930496600,10000031754637657,9999957301437286,10000047325471761,9999956650745052,
  10000029232485997,9999995100526526,9999971907571345,10000066336035435,9999895191845151,
  10000138091488109,9999837798546571,10000176174106544,9999816740421028,10000191043674024,
  9999790556703358,10000247330298421,9999690827569423,10000392519594472,9999511782752463,
  10000583736195822,9999332585377923,10000732011267871,9999225077183665,10000794520809552,
  9999213996682917,10000739486312387,9999355637560854,10000497391370541,9999690381592314,
  10000104996365635,10000090427906209,9999738049194618,10000409800287782,9999464865248199,
  10000615217271562,9999410405192125,10000380093977356,10000053009890334,9999351523076703,
  10001224354085238,9998465394278616,10001387550667236,9999237819580657,9999847889248491,
  10001024401591167,9998475113195981,10001465421487382,9999125864309201,9999984826100030,
  10000844855786669,9998733655101941,10001096884663641,9999562769648821,9999655909352755,
  10000808191690461,9999267108034904,10000274054311435,10000163590334254,9999729360418311,
  10000092798642292,10000049242321253,10000083819346602,9999627904001826,10000436527154757,
  9999958660412312,9999404128380247,10000917822264062,9999490229576088,9999544645535929,
  10001231728775879,9998937796324486,9999900030980034,10001361737345794,9998463436432247,
  10000269411937831,10001413562953792,9998113820980529,10000515520253606,10001500743136863,
  9997871728183105,10000564495813564,10001715547257766,9997723845024593,10000334716376622,
  10002103851110804,9997768594494539,9999727234906153,10002541365208306,9998226070381147,
  9998806236371644,10002691992988848,9999198407319290,9997915911032119,10002266457991821,
  10000467774811399,9997440204967084,10001275720418809,10001732436950814,9997557194129324,
  9999730197591344,10002752666201083,9998732604599209,9997691280919401,10002487011619203]
private def c6_4_p1 : List ℕ := [10001425131896281,9996768339106735,9999544790732247,
  10003516814680083,9999677697191691,9996575240251797,10000759343713983,10003027617069545,
  9999148008799951,9997630605915513,10000715860883248,10001489020077042,9999468572579514,
  9999556570354703,10000493790276805,9999319321021886,9999212048847420,10001742275927569,
  10001565832817161,9997491006879140,9997111851328030,10002657585910827,10004664407531721,
  9998214628208387,9993432290616752,9999412597283771,10007741543117741,10004653505030293,
  9993429640558790,9990766598899915,10001730752993883,10011353186424581,10005665217226967,
  9991640241300667,9987992251832006,10000140863365574,10013085694066306,10010518247176177,
  9994896739109730,9984188621140726,9990792599450655,10007907214269717,10017562768639488,
  10009746499318403,9992033876852182,9981375163948901,9987891591644778,10006310684437349,
  10021426357692580,10021107905254185,10005497891507060,9986079017151878,9976883144178219,
  9985062341722455,10006925776975299,10030857081269051,10044243683191045,10040061892469373,
  10019990437231668,9993322583604847,9972954568413209,9970574299524152,9992917741751211,
  10040105525647234,10106140594603675,10180973626968195,10253248276436890,10312879118679435,
  10352870051365800,10370118843669099,10365263023017362,10341832051737098,10305058270420933,
  10260678415907581,10213964700788252,10169104556415099,10128939350604118,10094996410260081,
  10067712085943830,10046741803326106,10031273999898528,10020294948425188,10012780470030887,
  10007813354583069,10004638504582955,10002674529976960,10001497688847713,10000814463049111,
  10000429981902459,10000220091527182,10000108992104818,10000052046614255,10000023692791434,
  10000010169664643,10000003930220270,10000001254343358,10000000168611946]
private def c6_4 : List ℕ :=
  c6_4_p0 ++ (c6_4_p1)
private def c6_5_p0 : List ℕ := [10000000397603152,9999998845623802,10000002190415602,
  9999996395738773,10000005470873718,9999992284068760,10000010327689570,9999986532140061,
  10000017148728391,9999978818621076,10000025649597021,9999969391936079,10000035620022590,
  9999959503937460,10000044858796323,9999951749821054,10000050001031795,9999950411503174,
  10000046675515492,9999959104435649,10000032103708746,9999979226799086,10000007620220602,
  10000006562840482,9999979647937366,10000031923456253,9999960531480896,10000041159666635,
  9999964504965180,10000021250535319,10000001467463470,9999968699987957,10000065940051542,
  9999897752496968,10000136493113797,9999834628947770,10000187055646253,9999797713271730,
  10000214819895983,9999769460314862,10000256471459353,9999701080228583,10000360755212232,
  9999559919518864,10000529661944602,9999381442445953,10000694647644109,9999252095495234,
  10000772138366733,9999234834391405,10000727341591911,9999341085356501,10000558562924931,
  9999575032926590,10000260148370717,9999926920705081,9999881233621048,10000292352203398,
  9999575049945090,10000499668097575,9999493605075189,10000437240696980,9999717906529881,
  10000030433242425,10000314066241328,9999288814906106,10001069068035977,9998744195448857,
  10001145725633372,9999312237507008,9999960680578857,10000824389916219,9998608934322104,
  10001512986492153,9998877399487512,10000354218868488,10000504803509576,9998867225621134,
  10001305590041434,9999017309251585,10000316893973944,10000409345868253,9999103551098947,
  10000952280870428,9999416132857196,10000004500945525,10000470400789527,9999396011336453,
  10000387142439023,9999961060336465,9999833999972189,10000120932836267,10000030114710704,
  9999958741967495,9999826047432906,10000418283058373,9999627146855554,9999925486919460,
  10000644590413749,9999158509143403,10000380831987071,10000494999525788,9998873761448519,
  10000937741709830,10000047308841156,9998876543452365,10001392598283020,9999489183166431,
  9999090212489713,10001680503934919,9998975564408086,9999374900995703,10001837538619117,
  9998583491195769,9999611246589415,10001935974174419,9998329026325137,9999722645594822,
  10002044742538071,9998206066504466,9999657986137204,10002206474535823,9998233395546245,
  9999374013958441,10002402979403367,9998484219155252,9998867825086723,10002514182113399]
private def c6_5_p1 : List ℕ := [9999044107596117,9998251160489056,10002354611005689,
  9999894272392589,9997747740035468,10001810952328298,10000875602831759,9997559094562924,
  10000900347345560,10001808052986695,9997815799100524,9999646520634702,10002500800593470,
  9998759907799908,9998125214950664,10002410878935397,10000661989703103,9997103678238106,
  10000691459851266,10002726706424683,9998169991290410,9997885370081341,10002561430710738,
  10001327339618726,9997158546226753,9999408279733664,10002716652253508,10000043975487314,
  9997732994390922,10000281420291116,10001573581759684,9999564031286056,9999288298166197,
  10000524349808587,9999755550536201,9999332973524694,10001218052636640,10000975925223801,
  9997872230265377,9998451882373881,10002873594370599,10002462502188354,9996693841401931,
  9996246900695425,10003203873249977,10005351173441694,9997719775627385,9992994689890141,
  10000238725203026,10008173363185776,10003060839675995,9992069320040342,9992802433375962,
  10005196502116929,10010707164286643,10000370615092578,9988695660646470,9992695541479958,
  10007330012839482,10012499646898140,10000780702781535,9987351765234325,9989800873005951,
  10005533453515479,10015371293952113,10007218088950089,9990163696995771,9983433179340778,
  9994665772591025,10012122562924929,10017744907550582,10005678736104838,9987429113883927,
  9980192383566699,9990971948175884,10010983214040393,10023823156595045,10019034173286322,
  9999841742916278,9980130564793235,9974277582276940,9987641999962341,10013622092408226,
  10038063535856803,10047450205752495,10036004548361624,10008386994862692,9977459721856336,
  9958871083565949,9965145344307124,10001559514916388,10064926128610893,10145146463293685,
  10228524391290606,10301517810836916,10353787759146967,10379886170205018,10379464360901838,
  10356312942551432,10316759443247149,10267966474066108,10216534222355779,10167616154854179,
  10124570122830791,10089037933086268,10061290085098891,10040674699031228,10026045618694373,
  10016102404190046,10009615680601122,10005547859349605,10003092890546429,10001666038701508,
  10000866796509239,10000435272841577,10000210595382048,10000097956119787,10000043542314665,
  10000018286839077,10000007105515681,10000002355083545,10000000460419792]
private def c6_5 : List ℕ :=
  c6_5_p0 ++ (c6_5_p1)
private def c6_6_p0 : List ℕ := [9999999619173735,10000001085286560,9999997945908533,
  10000003404170257,9999994836200029,10000007226770762,9999990361699502,10000012533628518,
  9999984203368096,10000019392656579,9999976501048376,10000027808878431,9999967738680932,
  10000036758212287,9999959006044491,10000044488355557,9999953039956060,10000048034842163,
  9999952936909256,10000043769608270,9999961902634705,10000029860045177,9999980574251568,
  10000007404605266,10000005240626483,9999982503824121,10000027863748569,9999965301735698,
  10000036694764625,9999967391125596,10000021337030892,9999997299135091,9999977337138028,
  10000053439948205,9999912550361938,10000121955594548,9999845946183319,10000181868117982,
  9999795520968461,10000222610193378,9999760865863759,10000258592571258,9999713877637334,
  10000326323298793,9999618201563316,10000451908896857,9999468345669909,10000612261946330,
  9999316622662879,10000734551486598,9999242495172563,10000747538793673,9999295899236759,
  10000629658395700,9999472036490729,10000402551878687,9999742979967194,10000096386992847,
  10000070943374850,9999768600476971,10000366844502758,9999542836613710,10000484448456609,
  9999562375824176,10000314165214203,9999879834500373,9999869562897598,10000414831745199,
  9999302222006721,10000927236119947,9998963456341654,10000958368974294,9999348251483254,
  10000135010498760,10000493352202494,9998935871806556,10001385093018678,9998684592582662,
  10000836040309158,9999919980427761,9999297527500631,10001235662122865,9998670241552071,
  10000961055443659,9999717561718887,9999559166942663,10000939684363471,9998953695456135,
  10000753199464973,9999792354552271,9999647373712628,10000698314211278,9999294901702123,
  10000408917685494,10000011880195274,9999668799127883,10000403544859391,9999750392254929,
  10000032799731443,10000069199959070,9999990915670861,9999909445328697,10000051177898541,
  10000177105266780,9999573815897467,10000424107018762,9999954232033798,9999486086209994,
  10000828946604111,9999430939185435,9999813944456402,10000928984341109,9998929913019479,
  10000409403647170,10000642150853921,9998691733274871,10001021230896023,10000094623051199,
  9998766908856198,10001473395511801,9999473114468302,9999066645491493,10001716073138706,
  9998919265563205,9999456895221161,10001791384288641,9998497432259960,9999824839384780]
private def c6_6_p1 : List ℕ := [10001778020979424,9998210932649430,10000099874160657,
  10001753988394909,9998033104915297,10000244006119650,10001779781062229,9997939414640084,
  10000230612839590,10001889533649300,9997933698357961,10000034384455503,10002074964830736,
  9998060213644484,9999646866931287,10002269287459525,9998382215608595,9999111412528501,
  10002359930617512,9998929809403454,9998531817619723,10002244037550698,9999671762755069,
  9998024543135502,10001862263049529,10000559353462438,9997692565811711,10001138880766875,
  10001545824357554,9997729367163789,9999947592938964,10002407998110773,9998521101939894,
  9998378851143937,10002490913094021,10000310290466165,9997256099341513,10001042637316040,
  10002307973927276,9997933240140921,9998556374995795,10002584515899159,10000461647299445,
  9997401932262431,10000380380246170,10002222303054613,9999074629187040,9998390822502915,
  10001118528966343,10000891382322586,9999014614935846,9999846160643631,10000602122218106,
  9999431753065359,9999930622907568,10001276279251319,9999491820108245,9998008225221036,
  10001034992569391,10002744262787828,9998573549530471,9996435167280106,10001598703171233,
  10004475779919361,9998549112458692,9994532810594025,10000855083961215,10006458268558853,
  10000330274573498,9992745840210677,9997787747670871,10007511339994329,10004769998818619,
  9993264702324534,9992302270937250,10004386003301810,10010220168723703,9999797020049480,
  9988921446444613,9994720626062930,10008987713301248,10010432831517878,9996480460065344,
  9987044301934779,9995773133077563,10010852212681577,10011614108190401,9996627800462970,
  9985296795120205,9992391201277781,10009487342228144,10015857724415785,10003640831676636,
  9986656272236017,9984039850991546,9998939962306220,10015704532262828,10016864704149905,
  10000840359508744,9982897569121332,9980107185682109,9995721730133118,10016821110957364,
  10025795649507717,10014790197160251,9991514301378886,9973082134833654,9973657001957273,
  9994980768482594,10025514687727308,10047669230894564,10047995945775713,10024483433778579,
  9987643865458023,9955702270556014,9946849951300108,9972228242623365,10032284454176008,
  10117291280320587,10211114031289335,10296359349733835,10359003144512336,10391214284862595,
  10391980220735709,10365905362046796,10320984246049413,10266204892505357,10209626764603192]
private def c6_6_p2 : List ℕ := [10157241478461538,10112621678336560,10077161144815125,
  10050639199905784,10031865182717767,10019239071080330,10011150001329984,10006203916475479,
  10003313788287531,10001698634968191,10000835002447968,10000392998980775,10000176804140191,
  10000075719678856,10000030539931360,10000011360322809,10000003718408211,10000000932225128]
private def c6_6 : List ℕ :=
  c6_6_p0 ++ (c6_6_p1 ++ (c6_6_p2))
private def c6_7_p0 : List ℕ := [10000000120893158,9999999515738879,10000001319180480,
  9999997653915809,10000003691851976,9999994547748778,10000007531552656,9999990106155066,
  10000012650018511,9999984214446671,10000019197613013,9999977040075164,10000026989462595,
  9999968956540821,10000035195124987,9999960923939105,10000042362237074,9999955151771979,
  10000046180756307,9999954165595564,10000043643223516,9999960595546139,10000032827779375,
  9999975756812832,10000013999549650,9999997315641901,9999991148359370,10000019335197646,
  9999972373471748,10000032492473959,9999967466185635,10000026868368385,9999985055789460,
  9999996448975983,10000028021932196,9999942728469494,10000089597428717,9999876943973335,
  10000155226640666,9999815687782128,10000209491529452,9999769165534706,10000249961210480,
  9999730000117805,10000294729213893,9999672085044220,10000372446464173,9999570613119065,
  10000496492737693,9999431368692068,10000638068110739,9999304596257021,10000731297255703,
  9999261575851349,10000712923701629,9999345528317233,10000565975291089,9999547014809686,
  10000321627879913,9999821862263920,10000029005289654,10000117994558620,9999746997361519,
  10000363481527925,9999565448566853,10000451184207391,9999597621411201,10000284550679622,
  9999896300955697,9999875955207079,10000373531301378,9999388101218056,10000801258662496,
  9999098832938610,10000873358694777,9999309275882470,10000350481447529,10000111993608390,
  9999384665903516,10001040119273831,9998743714727815,10001166666843798,9999247193945232,
  10000101247045146,10000606718030218,9998852318652206,10001335682022698,9998902053747681,
  10000511684314300,10000217538963501,9999167964463320,10001121340201994,9998997812383814,
  10000546360714502,10000054615888407,9999430100840586,10000819123535769,9999262876508236,
  10000390840289214,10000055103514094,9999589588885501,10000539979653129,9999578341878217,
  10000151582664721,10000110717338917,9999765866729520,10000192537426932,9999926459186062,
  10000006334707051,9999946479540016,10000150519107209,9999847479733488,9999966596239355,
  10000332910011857,9999481413496463,10000373350178631,10000106874410957,9999356087643259,
  10000835672592971,9999541929500197,9999684244539482,10000976189554981,9998982500191361,
  10000328881915337,10000666816864384,9998732464612359,10000990852531014,10000037101383852]
private def c6_7_p1 : List ℕ := [9998887835366250,10001426715840099,9999321855386922,
  9999357715688063,10001547138392139,9998715834486552,9999972387840984,10001396205362838,
  9998311706742830,10000578238507325,10001082854923003,9998108857228293,10001082630509851,
  10000719168748718,9998052632974146,10001454130479520,10000389665932906,9998071124929720,
  10001701764087724,10000147124560972,9998099012164647,10001848619516453,10000022783230598,
  9998089835358025,10001910006551475,10000036423057197,9998024429389633,10001880929082402,
  10000197367694425,9997917228477825,10001737852918093,10000495603546708,9997813938766299,
  10001455956964140,10000893868888287,9997774153347541,10001027595013177,10001338130426469,
  9997848997221587,10000457274007626,10001779398711628,9998089086983327,9999734410932020,
  10002156883503653,9998594020629218,9998851231826342,10002309176310582,9999515390542724,
  9997942822991968,10001910166828909,10000872781901637,9997464588300660,10000658057872351,
  10002213641123668,9998072464719173,9998808443566527,10002554328532696,9999909761312483,
  9997536808433927,10001207356786874,10001825076154709,9998113197394993,9999069113236124,
  10002043954671664,10000069698171497,9998254334045698,10000548776707598,10001141066683979,
  9999178646192111,9999606250678937,10000739943103411,9999635907504144,9999638287628595,
  10001051969447575,9999776014065082,9998359539351676,10000922093128188,10002139754273554,
  9998350805554217,9997414363603761,10002340825832165,10003028856963021,9997051095875991,
  9996470882108796,10003430583684372,10004149250362049,9996269318464519,9995056055381886,
  10003763599029005,10005938985793760,9996596707660274,9992899937428049,10002488874183980,
  10008293480433535,9999145703217153,9990755986322029,9998397436843827,10009508178528248,
  10004793379511910,9991484305782059,9991727989795340,10005757692473693,10011134465331700,
  9998866408221409,9987840394336569,9995293551664012,10010253076496405,10010290876323872,
  9995011230272471,9986422915587550,9997048435855934,10012364441850688,10011263411767588,
  9994776676769942,9984359157555509,9993685509523351,10011457221549912,10015924446635858,
  10001407735752595,9984586349099174,9984750543472316,10002146046209954,10018223532958224,
  10015781353635639,9996619753588904,9979286827808150,9980802860181383,10000827025058196]
private def c6_7_p2 : List ℕ := [10022307489014270,10026561431277901,10008893320332338,
  9982211147825698,9966997779405056,9976261726638920,10006448414474942,10039773083839756,
  10055401287008965,10041937637221945,10004064682831719,9960446892281543,9934960961011124,
  9946207008675992,10000179718021855,10088685232308141,10193184358917204,10291645110598827,
  10365377364255528,10403539928597031,10404406000448181,10373812381640632,10322014995006735,
  10260311217382225,10198429262482053,10143125080693527,10097926405225144,10063668016434407,
  10039381837900578,10023191919221928,10013007225491344,10006947218084722,10003531938562062,
  10001707642382648,10000784133023214,10000341081719209,10000140006888989,10000053820983527,
  10000019126885621,10000005967182640,10000001454406118,10000000119496963]
private def c6_7 : List ℕ :=
  c6_7_p0 ++ (c6_7_p1 ++ (c6_7_p2))
private def c6_8_p0 : List ℕ := [9999999710197273,10000000833737795,9999998324019944,
  10000002900514496,9999995616465565,10000006133463018,9999991682279974,10000010695260798,
  9999986579417483,10000016507023491,9999980166542878,10000023399076014,9999972784365584,
  10000031035211450,9999965233278400,10000038359915549,9999958665523595,10000043560187600,
  9999955269374922,10000044474541589,9999957440222489,10000038858702424,9999966885741314,
  10000025514004654,9999983533651942,10000006193986563,10000004424200778,9999985593313775,
  10000022773596993,9999971571732007,10000030106148062,9999972995740957,10000018400371572,
  9999996170708328,9999983582848998,10000041768031162,9999928894675688,10000102908664550,
  9999864751151445,10000166553940985,9999804630666948,10000220799867233,9999756717085566,
  10000264131474467,9999714514629705,10000310509798281,9999657713238581,10000383084109914,
  9999566262688485,10000493070419721,9999442949588696,10000619575133672,9999327063607229,
  10000708761694690,9999280405853239,10000700412221689,9999350574769047,10000567953878518,
  9999539172340544,10000334780866849,9999802711224584,10000056065342043,10000081204001304,
  9999793191064563,10000312271286680,9999612465423259,10000421717987851,9999594937757787,
  10000330656326157,9999802262951791,10000014012390923,10000203310335766,9999571229706577,
  10000631015263452,9999223748563252,10000833071498879,9999222714470100,10000596811355256,
  9999702261871752,9999910156123184,10000508374770698,9999122892015014,10001104825955930,
  9998887529998505,10000861636344227,9999620862256133,9999765958837934,10000819460025972,
  9998795887023367,10001257627261027,9999055127152791,10000349774456824,10000343307541340,
  9999090608030732,10001163193441129,9998971576727188,10000566713976394,10000046346355217,
  9999410210115580,10000880891880979,9999159546370578,10000515288897819,9999949205003493,
  9999629221335361,10000601302982455,9999420445541361,10000347484143052,9999974645577671,
  9999756531884909,10000356792448322,9999702581845211,10000134700588854,10000020372925825,
  9999915237099969,10000055126251059,9999994907143594,10000023496133665,9999866763287402,
  10000253091158934,9999753706031105,10000033509537924,10000310956963613,9999432175036538,
  10000509018806688,9999918655265019,9999497855889559,10000860216545791,9999304668288385]
private def c6_8_p1 : List ℕ := [10000032880135174,10000739645900911,9998901483465923,
  10000744475329548,10000151779008255,9998982643044023,10001244317660872,9999378501339388,
  9999523532888285,10001304592010910,9998748806629359,10000293912634655,10000930434124878,
  9998463791092504,10001028213378085,10000284598577659,9998551537177279,10001546926262625,
  9999567945284714,9998918295389338,10001791055913309,9998934847227778,9999426311720472,
  10001795101558120,9998461945816508,9999953368895423,10001639901932574,9998158023454216,
  10000418874535749,10001413487095696,9997990011393286,10000783758126031,10001189760238079,
  9997909507988941,10001036944565561,10001021311566853,9997872512400140,10001179191276591,
  10000940170371498,9997851237691335,10001212460773246,10000959192279600,9997838606789603,
  10001136708784039,10001072889966480,9997845381580387,10000953020375913,10001261209545598,
  9997890735603315,10000666796880386,10001498360251699,9997994509861876,10000281218062781,
  10001762288677066,9998184269686834,9999783421819877,10002025424955555,9998520984796307,
  9999150687340546,10002208844223837,9999113047867482,9998413103499064,10002128490010715,
  10000053166206246,9997763825375155,10001526620494112,10001247535558319,9997605265300289,
  10000281107627044,10002246723169702,9998351325419024,9998730489195467,10002351829530929,
  9999946808263049,9997753977939450,10001206513404331,10001513208640815,9998154280211064,
  9999487651507646,10001872774869575,9999611417033782,9998597955037815,10000930782723571,
  10000665854995463,9998991277665123,10000085823009401,10000652981294716,9999342634773001,
  10000019941758097,10000940024886680,9999136402407873,9999089788889454,10001744817430383,
  10000607675126429,9997431859341332,9999892813156975,10003283538315506,9999493130665862,
  9996117339724706,10001157176797965,10004389790080795,9998220179697912,9995148332357569,
  10002321767499320,10005326965391424,9997267834510095,9994125413457241,10002951117601539,
  10006539829310525,9997099642633314,9992662419329675,10002479692426589,10008231927482632,
  9998427272705194,9990887903793489,10000067707124465,10009767555304144,10002096616769574,
  9990124907048748,9995147631020181,10009027427708432,10007904517649460,9993160509512502,
  9989333222295559,10003135370954114,10012307535476883,10001850874797033,9988066621318406]
private def c6_8_p2 : List ℕ := [9992641515665653,10008849099617901,10012082743948570,
  9997147125787389,9985796072559880,9994726052595377,10011691129467015,10013036902164031,
  9996455628222124,9983830899496926,9991948886284384,10010853949928218,10016904018131119,
  10002272238058144,9984121078568562,9983881520560500,10002479881843916,10019623448840016,
  10016299291276416,9994984425014237,9976879613264515,9980545557416236,10003927375664997,
  10026333930339468,10027156722959670,10003865663822224,9974299211518268,9962545142933429,
  9980443571155695,10018614293424159,10052590924627861,10058836335960264,10029743333246644,
  9978747612028690,9933599930324804,9922618558431197,9961648494004535,10047802921065228,
  10161758261548179,10276175356050198,10365704541142417,10414421671126948,10418590957179104,
  10384982173236269,10326527711914991,10257499343144297,10189837054490451,10131323091970869,
  10085452377270975,10052383538947055,10030275300879155,10016498926835136,10008473776912374,
  10004097015200564,10001861210983873,10000792213680619,10000314598040002,10000115733947726,
  10000038932369005,10000011608953611,10000002825108394,10000000321848601]
private def c6_8 : List ℕ :=
  c6_8_p0 ++ (c6_8_p1 ++ (c6_8_p2))
private def c6_9_p0 : List ℕ := [10000000183780002,9999999432692324,10000001271357852,
  9999997678689291,10000003589354508,9999994759751536,10000007129668117,9999990692886527,
  10000011831036606,9999985441873980,10000017541205103,9999979102762497,10000024326489009,
  9999972092714014,10000031533438072,9999964988203056,10000038183234801,9999959138099936,
  10000042720299653,9999956411426111,10000043209314841,9999958798080777,10000037623855627,
  9999967731357052,10000025191532045,9999983206906818,10000007387051825,10000002476669363,
  9999988218554739,10000019782990813,9999974591296449,10000027604734090,9999974464316018,
  10000018579211764,9999993859949702,9999988344892568,10000034351626346,9999938669559085,
  10000091253677407,9999877277641652,10000154233935425,9999815651268212,10000212005990811,
  9999762944232769,10000259760950504,9999718608681655,10000304212366042,9999669466480326,
  10000362733588131,9999597374809387,10000450590349590,9999494995233780,10000562586625466,
  9999382198414376,10000663735066927,9999306756770398,10000699646025387,9999321926578792,
  10000626471359072,9999454036684428,10000440400587287,9999683573616604,10000182006271396,
  9999954576679777,9999914770346860,10000202206517993,9999701765579843,10000366117835654,
  9999601945240996,10000387079046798,9999672173708842,10000218394693628,9999937126024665,
  9999872843036434,10000332620692066,9999472008741439,10000683969982541,9999228146720146,
  10000768319918244,9999340567923715,10000445097230535,9999857821246167,9999785896379290,
  10000571666971228,9999134305637373,10001028824128142,9998993369024428,10000774970038706,
  9999644324867286,9999823159070724,10000703577410358,9998912596584739,10001211700783333,
  9998979299267348,10000547499892904,10000084431412212,9999307825438105,10001090077369050,
  9998846586675767,10000864224342606,9999678184005714,9999709910769700,10000768095123211,
  9999037929509469,10000827174870187,9999565004064711,9999941247824226,10000476001515104,
  9999317908990600,10000630160825061,9999629760020259,10000021170794081,10000279596779505,
  9999570574466682,10000396695613180,9999773693380887,10000013374602341,10000144154724367,
  9999807420551185,10000144966898184,9999933544149713,10000027055270727,9999949527262513,
  10000093705040317,9999922765751195,9999951922987108,10000242477499904,9999621192792881]
private def c6_9_p1 : List ℕ := [10000318265804088,9999978658413078,9999614321655586,
  10000654870003640,9999433745459961,10000095863005380,10000521039283591,9999098084350138,
  10000757212356730,9999892777647143,9999316399229084,10001109386502977,9999148429939998,
  10000017762594003,10000887090022573,9998734086202192,10000827783826392,10000187428892155,
  9998869854549920,10001353996340898,9999337776288635,9999479580443326,10001395654852124,
  9998673677794486,10000305958716724,10000983094728261,9998388501419604,10001073432815933,
  10000294504674843,9998502269994627,10001598764669303,9999540915733566,9998914404488269,
  10001821179952979,9998884568397168,9999480007252189,10001775911660984,9998408359939756,
  10000068668742331,10001547551338185,9998123818186483,10000593213123726,10001229761163944,
  9997996898998733,10001011425849232,10000901230409436,9997974349670930,10001314673844993,
  10000617539323819,9998003490116068,10001512401135524,10000411631870587,9998043762937642,
  10001619352324095,10000298787114060,9998070642513931,10001648682375979,10000281103837809,
  9998074421998023,10001610293211430,10000352295787617,9998055349055310,10001510462373233,
  10000504366843853,9998017283901371,10001349193605518,10000735544264236,9997967831265037,
  10001110732282343,10001053177435426,9997931811402581,10000752134232022,10001458945988129,
  9997976717114668,10000210753243749,10001906318445126,9998228988577105,9999453798786082,
  10002248244397029,9998837886111332,9998570000545084,10002231733362061,9999856744634687,
  9997845311146414,10001610082259890,10001081814668330,9997705419046556,10000383336537262,
  10001998416814362,9998434813963092,9999008813759167,10002035934998421,9999788918781748,
  9998257401054563,10001116219462914,10000942309442273,9998556416531532,9999968091648064,
  10001178165083537,9999372384168814,9999488062011308,10000823409124343,9999730727585053,
  9999479865354637,10000895520337433,9999824732292422,9998815637468920,10001080235126258,
  10001065016099230,9997996521516931,9999435709284201,10002792439144880,9999772213831250,
  9996644264467002,10001196076777384,10003664660202805,9997768508718987,9996258445553150,
  10003250170867543,10003643237943509,9995799712318593,9996554309966030,10005059112490033,
  10003232813896255,9994176187336222,9996910636819628,10006498936371277,10003096810819822]
private def c6_9_p2 : List ℕ := [9992917130269557,9996669568700032,10007554831423255,
  10003855316256279,9992137040811268,9995281433852160,10007914359631559,10005933807682151,
  9992430043059342,9992544642228350,10006652696230096,10009142827943015,9995020178352259,
  9989270567561625,10002427721437241,10011816141169244,10000981914225163,9988085450015141,
  9994997245522030,10010534813850493,10009116099481645,9992703989238197,9987500274685303,
  10002073348715227,10013997297892838,10004714476847750,9987779140779591,9988372597910894,
  10006154774260078,10015922654761513,10003570269473651,9985639676992985,9986449330786981,
  10005465979614876,10018260308697003,10008132770766798,9987047130030618,9980683445985607,
  9997466802239275,10018730230384483,10020118250466634,9998749021169328,9976451458900937,
  9976953310730863,10001635535511241,10027844917681839,10030197264531141,10004064478352341,
  9970282000879939,9958013631687134,9980949574514997,10025900621332130,10061699398159649,
  10060887493488966,10018640445435040,9956936394885248,9912643970790360,9917927423150856,
  9984468218652367,10099065544957690,10230983516436618,10345599111719690,10417161666840292,
  10435599139799618,10406187669952491,10344169232462395,10267770623908604,10192553062078225,
  10128505097388809,10079783517218097,10046131420173822,10024840118617756,10012442477521253,
  10005784964861409,10002487798040315,10000984481204766,10000355669818776,10000115881872719,
  10000033283654386,10000007910017481,10000001247599141]
private def c6_9 : List ℕ :=
  c6_9_p0 ++ (c6_9_p1 ++ (c6_9_p2))
private def c6_10_p0 : List ℕ := [9999999871146075,10000000486612372,9999998742234112,
  10000002166439055,9999996617620228,10000004949760420,9999993251463362,10000008803598740,
  9999988824824544,10000013768051625,9999983391677854,10000019724424258,9999977088502614,
  10000026300544741,9999970268228797,10000033056345161,9999963802278636,10000038903317561,
  9999959022000907,10000042323462284,9999957514310643,10000041436254004,9999960997667230,
  10000034917774360,9999970707921809,10000022307582006,9999985932872561,10000005163587367,
  10000003909274104,9999987639604604,10000019300030348,9999976130031782,10000025256749080,
  9999977507969530,10000015075647929,9999997245839427,9999985312486689,10000036714324381,
  9999937318984783,10000091640364217,9999877747632600,10000153221190575,9999816617816315,
  10000211627109126,9999762361315979,10000261504928205,9999716005852357,10000306625704092,
  9999668587323249,10000360175403708,9999605268316394,10000435870392849,9999517103088857,
  10000533907096505,9999415067783380,10000630515573967,9999335447998373,10000680729155015,
  9999326535503547,10000639283668606,9999422981788783,10000488397262601,9999622009795814,
  10000252563052381,9999880013799143,9999989038494001,10000132100004054,9999763906783873,
  10000316189819795,9999633486881113,10000381969456982,9999641893200241,10000291896040047,
  9999816471841339,10000037125640248,10000137438180087,9999676018399611,10000501020795762,
  9999356218864583,10000727237786997,9999269476342508,10000641348805300,9999541172655021,
  10000196404317347,10000117678054942,9999557997258026,10000726001996167,9999083777800240,
  10000965923891453,9999153520771301,10000557770619371,9999863788544370,9999655341234012,
  10000783971862283,9998925397388596,10001130673880178,9999083316050773,10000466968443164,
  10000114402137879,9999324467211061,10001058266824440,9998852608814845,10000911756591616,
  9999580266936729,9999821584477354,10000697293393473,9999022056565200,10000942230329697,
  9999381546857377,10000128659102877,10000356833778916,9999319778247111,10000750654754176,
  9999429096675675,10000228739230206,10000142124396773,9999586706426708,10000506212626598,
  9999585112755597,10000199740203144,10000041975622189,9999782144984814,10000276052193748,
  9999778198572951,10000107925925469,9999996766712972,9999954396486720,10000038610761912]
private def c6_10_p1 : List ℕ := [9999981690999008,10000036084819723,9999890954134225,
  10000195624572682,9999786315146370,10000096939083143,10000142466596482,9999607897237620,
  10000487668805888,9999684660690709,9999908134208233,10000535336865391,9999255613103084,
  10000541196328392,10000020950613287,9999351084712063,10000960728523153,9999278918594126,
  10000015663461327,10000762778167331,9998866958437222,10000827135944720,10000014917296717,
  9999101524307752,10001264599279412,9999152532443540,9999869088611835,10001069837147588,
  9998643152449198,10000769537954941,10000349784006107,9998717426535758,10001391320276613,
  9999440908849891,9999308637800067,10001512554446737,9998696115714056,10000159758034168,
  10001144372031269,9998333845840033,10000981630762439,10000457704356721,9998397625832461,
  10001567037754799,9999672044751091,9998798809593370,10001831640087704,9998968752599013,
  9999390243713160,10001795639252742,9998451824298979,10000029022079224,10001539891231537,
  9998148940948712,10000611716414512,10001163044815997,9998033698070912,10001083296079858,
  10000752389086811,9998053034123926,10001428587846089,10000371124367120,9998149065856439,
  10001658051487282,10000057027902601,9998271882446076,10001793977254399,9999826740638062,
  9998385779454971,10001861039320019,9999682716795199,9998468422159608,10001881220094045,
  9999619617734061,9998506978542049,10001872435977409,9999630667590117,9998493055857309,
  10001846148605728,9999715231930782,9998418913443174,10001802552830474,9999885180506903,
  9998280269472790,10001720881537881,10000165621918761,9998090130741378,10001549868246049,
  10000581835511107,9997900865903166,10001211233619831,10001125720305122,9997822328235002,
  10000631617783419,10001711490319293,9998009272936477,9999808324259524,10002149890121630,
  9998593620548436,9998883616623199,10002188926619516,9999565456906751,9998163865619909,
  10001653307916751,10000669281913726,9998002096360122,10000638834429208,10001447883033958,
  9998532357164230,9999590841721226,10001533389439104,9999437190235491,9999050538251430,
  10001041488599396,10000095700715370,9999115229922368,10000592751420385,10000235560403294,
  9999192963260111,10000588751435718,10000452972649274,9998756980837290,10000359505317712,
  10001472661925424,9998607952169539,9998828367529803,10002373408709957,10000379914813358]
private def c6_10_p2 : List ℕ := [9996921486264127,10000759816148638,10003372542312220,
  9997939401848267,9996780994193818,10003343570508409,10002662059581615,9995526947946821,
  9998203395329224,10005372021831960,10000737676968016,9993978687758547,10000403334521761,
  10006448578790596,9998467282696599,9993287108734012,10002578901510649,10006889773414312,
  9996509769006753,9992941677751020,10004227856749404,10007291892933555,9995242955135175,
  9992349710315076,10005037331694614,10008173007493333,9994985206520501,9991130051545000,
  10004618002725228,10009709070213067,9996237993724910,9989398103522983,10002363676057383,
  10011392319512896,9999630514025808,9988144887220570,9997789575194338,10011709450057381,
  10005267433428304,9989359380899568,9991440023939398,10008327850253703,10011658570137759,
  9995498784250935,9986141409123800,9999104128594963,10014125887116869,10007369463668082,
  9988717188911974,9986529335772992,10004661090249156,10016758604777907,10004904550167149,
  9985372614449490,9985549553492290,10005910018244165,10019395097576762,10007559862410904,
  9984774145004466,9979956469042281,10000354100263177,10022373777595580,10019414117255258,
  9992944704711249,9971465543141011,9979588145434955,10011370712955586,10035508533015972,
  10026170864754587,9988652795709355,9955833470113795,9959508734363686,10002379873824114,
  10054146764376930,10073993410490248,10041220742195700,9971412827349027,9907957982362663,
  9896373277513329,9958836760680431,10083591285644015,10232820353764857,10361765986176068,
  10437533058775638,10448949284041668,10405426045059257,10328420523068314,10241238460843743,
  10161673602226163,10099168139499457,10055721539717545,10028649143828541,10013436899104989,
  10005718101966844,10002189338476570,10000744528796790,10000220195397314,10000054460297636,
  10000010247291877,10000000995228009]
private def c6_10 : List ℕ :=
  c6_10_p0 ++ (c6_10_p1 ++ (c6_10_p2))
private def c6_11_p0 : List ℕ := [9999999884716046,10000000433199719,9999998872677212,
  10000002000882404,9999996800791163,10000004683077220,9999993635299619,10000008343950495,
  9999989416936226,10000012998681121,9999984236968009,10000018655474638,9999978277053314,
  10000024940390174,9999971848408585,10000031363767474,9999965534977267,10000037138033147,
  9999960581415891,10000040988116350,9999958332599350,10000041300916932,9999960387338397,
  10000036568025953,9999967799944484,10000026295423531,9999980761983072,10000011271689320,
  9999997247396768,9999994402330858,10000013117998190,9999980868546099,10000022607093866,
  9999977089713885,10000019315515544,9999988729070663,9999998496669885,10000018916396143,
  9999959270969579,10000066212857129,9999905495337134,10000124542585673,9999845051038411,
  10000184845855587,9999786690806087,10000239704650873,9999735832041754,10000287268858038,
  9999689994260657,10000334080384052,9999639003701622,10000392291283892,9999571061892946,
  10000470720104390,9999483760411763,10000562776346175,9999394088376827,10000640483963038,
  9999339138835637,10000661652331965,9999361375895809,10000589666410060,9999485215966444,
  10000416904477665,9999698731755454,10000174782617443,9999954203065960,9999922693324379,
  10000186644236227,9999724845613027,10000337079743576,9999632073381181,10000364005531759,
  9999676846039174,10000244875757776,9999869065416932,9999986640199430,10000177999015620,
  9999651354235393,10000506333401209,9999370470186588,10000697140555842,9999308504476018,
  10000602330084373,9999570013890226,10000187030432525,10000101478819488,9999600789314744,
  10000662827328945,9999152444741976,10000914036741440,9999163421952898,10000611326773732,
  9999738825421763,9999837883082759,10000582785548315,9999086677858909,10001072985111922,
  9998991086754966,10000715648668055,9999755045092065,9999700184273756,10000784713035944,
  9998919995123421,10001098887296920,9999172230185954,10000336055313062,10000238980925248,
  9999268676237976,10000997884128694,9999035456803748,10000651067432378,9999835226742072,
  9999664551400565,10000693673891406,9999191638472847,10000663373092194,9999671501394793,
  9999929879296719,10000397579998385,9999443226785124,10000517146072943,9999681302930566,
  10000050017930106,10000188408008746,9999678464917352,10000323169169207,9999781151567104]
private def c6_11_p1 : List ℕ := [10000069626554615,10000057826626085,9999879136529676,
  10000117267436816,9999920020248853,10000053176086830,9999938216487169,10000092260362446,
  9999901351505221,10000034498214583,10000106247636960,9999733129699441,10000346314944062,
  9999743621543500,9999989599760842,10000348533138618,9999425411919216,10000525215351843,
  9999832463988930,9999650485131754,10000749596546311,9999222680444667,10000360873924271,
  10000313184991073,9999123381574431,10000982294080253,9999478834988793,9999716971916249,
  10000976679362805,9998865835211034,10000622830509786,10000290329058036,9998926573503773,
  10001240199531251,9999344484223315,9999643099426385,10001187905323081,9998691728939432,
  10000608715073035,10000503565784670,9998666181443477,10001330749700185,9999542971428111,
  9999249111501394,10001501686599440,9998733753761521,10000158212102988,10001098534005165,
  9998366404392050,10001036128795105,10000318631111322,9998512661386855,10001611466335759,
  9999442107948168,9999062818878457,10001770616386780,9998710008910410,9999818434582535,
  10001544190411980,9998260575727904,10000582842287871,10001050385559373,9998123623403803,
  10001216025617822,10000431500434773,9998251099163575,10001650845670012,9999809539348686,
  9998557213361505,10001881906898367,9999265704627403,9998951595751617,10001943562882490,
  9998838842413423,9999360014992072,10001887007145507,9998534814053543,9999731990117637,
  10001763860035743,9998338939916022,10000039772923760,10001617568477212,9998226518180424,
  10000273681381498,10001480257589359,9998170338467319,10000434935799143,10001374907443678,
  9998145438131304,10000528522977292,10001318823898025,9998131759500793,10000556260853724,
  10001326829954874,9998119064505676,10000510523571772,10001411191467326,9998112811382028,
  10000371437436768,10001575172822222,9998141729578616,10000111122359141,10001799994471708,
  9998260670380457,9999709621248116,10002029270413571,9998541144555016,9999181959547926,
  10002161850727982,9999041553973967,9998607648678871,10002069185831321,9999758805467227,
  9998141731059000,10001648401937592,10000580235953485,9997978715692567,10000904595862868,
  10001277758866327,9998253549953472,10000017268582397,10001592769404983,9998911019379322,
  9999306844480406,10001416019091656,9999652960033724,9999038894762960,10000949345927208]
private def c6_11_p2 : List ℕ := [10000102868668673,9999148700653981,10000625246422821,
  10000181626990881,9999184285096548,10000661582895612,10000352879193484,9998773500587279,
  10000579478889325,10001201271654618,9998387107855118,9999486437982442,10002354583777658,
  9999321623995456,9997477894744669,10002070821543000,10002011760570297,9996673766082653,
  9999103173017854,10004168444182044,9999375883173946,9995562466788303,10002299104437145,
  10004100943345786,9996110645697841,9996769060595991,10005214423341554,10001965477058740,
  9993827434870696,9999533455334232,10006739075700961,9998887182103617,9993048444518900,
  10002649755171330,10006888676214316,9995940286022201,9993350086857855,10005294950662450,
  10006339340725834,9993663515682852,9993944958723553,10007182902831704,10005883130482141,
  9992162209413860,9994104603710842,10008298597771236,10006146580537914,9991453792547583,
  9993328350790942,10008539036707153,10007479830959128,9991789045536012,9991452447305075,
  10007474434982761,10009810404158135,9993773879201298,9988845450635178,10004354039262357,
  10012400175022296,9998251339926989,9986730282612569,9998338469573215,10013342901214471,
  10005815486393910,9987959638731385,9989655093746260,10008728226257678,10014375538508404,
  9996963715055688,9983516319024954,9995353501604854,10015027591324545,10012764632573586,
  9991115185204818,9981383394466165,9998332123040265,10018910691804734,10014172786720212,
  9989139334153382,9976659125215720,9994433886063043,10021582849143962,10024004198257458,
  9996314819057189,9969513761021500,9975853794703772,10011689623033286,10039702886766883,
  10027721335530675,9983110386947047,9947852536277259,9959460117544072,10014980332800315,
  10070734911838414,10077397962812053,10020442906139326,9933941986515406,9878908692303803,
  9904065118312176,10016769390192343,10180982078552828,10339272715799103,10442143229115236,
  10467607409747127,10423645025996439,10337176022553035,10238803317619069,10151443030823734,
  10086146218714973,10043867809422224,10019882493279842,10007936577128570,10002741232467794,
  10000794508070971,10000181936716633,10000028015496496]
private def c6_11 : List ℕ :=
  c6_11_p0 ++ (c6_11_p1 ++ (c6_11_p2))
private def c6_12_p0 : List ℕ := [9999999869532094,10000000481491276,9999998772207758,
  10000002128511186,9999996660900382,10000004816413989,9999993522326705,10000008438376379,
  9999989357473263,10000012993301912,9999984333363199,10000018438429100,9999978605060771,
  10000024504086431,9999972410522973,10000030655434472,9999966399549966,10000036167124015,
  9999961584047031,10000040008243749,9999959192223083,10000040689629305,9999960617281834,
  10000036831234483,9999966950027183,10000027872976474,9999978403005900,10000014337303972,
  9999993546925333,9999998531292716,10000008938134169,9999984715388681,10000019613731133,
  9999978647856691,10000019664753974,9999985937427131,10000004225881653,10000010144532025,
  9999971108770233,10000051493164611,9999922537705606,10000105758350144,9999864552168487,
  10000165473524856,9999805225321487,10000222718065760,9999751074699068,10000273277248145,
  9999703470975381,10000319482125614,9999656592774157,10000369830235717,9999600174971068,
  10000434075148777,9999527333118310,10000514130778646,9999443912300738,10000594949144705,
  9999373900757826,10000644524829057,9999354619582779,10000624591610324,9999420100047247,
  10000510853034735,9999580562824580,10000310035440297,9999811029477957,10000063682065417,
  10000057441810830,9999833468451411,10000256501988637,9999678691477401,10000356675445494,
  9999640482008051,10000328211537212,9999737104911970,10000165326959479,9999960440899621,
  9999893022399946,10000263648355033,9999583901036522,10000547040129600,9999361942538757,
  10000671942881205,9999364499898151,10000523066919972,9999661432232278,10000096854945489,
  10000176487487206,9999552661045365,10000677140909583,9999172514209722,10000867128916355,
  9999222133584700,10000559881596104,9999764191038311,9999850692619694,10000532387537656,
  9999158892962340,10001007413276074,9999016123103179,10000757918429338,9999638708251515,
  9999869870795044,10000609195259674,9999038990238364,10001092047634759,9999040774090390,
  10000586756846303,9999934607929248,9999531645005150,10000869209435820,9998973701890212,
  10000897832587535,9999474413173378,10000023987877562,10000455452080216,9999227724529417,
  10000841089227535,9999342767894043,10000295529463623,10000118595785331,9999547021966854,
  10000612285903840,9999433888630433,10000353547834240,9999937351015766,9999796000315589]
private def c6_12_p1 : List ℕ := [10000365051843324,9999614526122034,10000282633367153,
  9999887002619074,9999946151880954,10000162130705087,9999810574676778,10000150297588998,
  9999916371989302,10000029728526523,9999990999258441,10000012002786763,9999993099288695,
  9999963700397559,10000119320974191,9999796138072916,10000226378965021,9999864713279437,
  9999932947092677,10000304940311234,9999547248721378,10000398709719802,9999880916396567,
  9999716162049973,10000611561517292,9999333609269779,10000369081105432,10000171299042749,
  9999312136796274,10000887356737262,9999381608179816,9999980310802410,10000703263472073,
  9998952058450208,10000827962425113,9999875116831032,9999307925797368,10001159119794815,
  9999015728968110,10000232817440805,10000686783321257,9998757118249060,10001090188807229,
  9999712901082129,9999284657459565,10001323159189165,9998848165196330,10000273022652824,
  10000802641937363,9998583568117330,10001164471906869,9999831336207588,9999032053084861,
  10001519082471585,9998899733512893,9999944563800042,10001211914804991,9998407062421366,
  10000907417865316,10000419006106774,9998505067997885,10001559845626751,9999469632007636,
  9999099079702628,10001721891388987,9998680286837679,9999949948373971,10001409443745544,
  9998247675931078,10000796876623440,10000770761117151,9998221807833842,10001445081889255,
  10000000337597858,9998538227955410,10001800480105911,9999269971707509,9999072613450444,
  10001860434354493,9998692118934770,9999693263050858,10001682844603941,9998314065100404,
  10000293804192535,10001350811397546,9998131619458810,10000806677019900,10000946334518736,
  9998108842992674,10001202179852723,10000534379909274,9998197083156474,10001479715763707,
  10000157859649066,9998348029984433,10001656735565890,9999839416332868,9998520330342993,
  10001759796097588,9999586547237892,9998681583913384,10001817369963978,9999398699809766,
  9998806599083604,10001854897322939,9999273813586284,9998875308893511,10001890824983904,
  9999214469223883,9998871245184903,10001931953435579,9999231663223198,9998783877683334,
  10001968966245986,9999344969119759,9998614306701735,10001972369398011,9999576571055610,
  9998384545239799,10001894049647322,9999938036222411,9998146178710263,10001677546905952,
  10000411420395572,9997981519833529,10001280732440685,10000931539992626,9997988039548196]
private def c6_12_p2 : List ℕ := [10000708576809512,10001382422063018,9998240588363240,
  10000043001498984,10001624408988598,9998736657575704,9999443550055342,10001561805664880,
  9999354134760042,9999088824282055,10001230538923582,9999873859046353,9999054179615210,
  10000837220409448,10000111114735685,9999193110582792,10000655953700726,10000117241402905,
  9999166930556077,10000759561566440,10000270697938308,9998742935781473,10000765567813674,
  10001011700917740,9998238713654959,9999981074179998,10002208039666699,9998606917700929,
  9998183398208868,10002722777184383,10000608942096748,9996504849469817,10001119600380320,
  10003417785629712,9997074261934863,9997552330539388,10004366150372163,10000768485795608,
  9994884216102814,10001292468480211,10005027069275449,9996633518544758,9995869691552237,
  10005132145930652,10002590651812913,9993629362628981,9999354279629083,10006984092149353,
  9998544541019701,9993015981071213,10003498422148747,10006462380919014,9994670273957828,
  9994443611580706,10006863763670486,10004417887158365,9991922935196935,9996810097186931,
  10008993537072715,10001993956786641,9990332370611631,9999074448131881,10010167808007941,
  10000056309684307,9989436837071583,10000561092378672,10010912491645120,9999114001691769,
  9988742562931616,10000883927044593,10011617652874504,9999478891900398,9988012804717008,
  9999759438438971,10012329140847193,10001447368996264,9987436201232107,9996847868922437,
  10012547143404617,10005395569360204,9987957523959093,9991844282825178,10010706279226333,
  10011255575005762,9991873009961415,9985750090108843,10003959976817740,10016355756814947,
  10001839195156114,9983480993557761,9991243820044424,10013662008102637,10015553168881020,
  9992939263320175,9979754106887339,9996813802743847,10020203880732253,10015438248525787,
  9987331069054314,9974535124831573,9996616567129305,10026226357852779,10023709450430251,
  9988888771340427,9963612447635826,9981484557348091,10025799400588343,10045981068834696,
  10014242489981173,9959139696810500,9938980298616754,9982389283261902,10056283946977176,
  10092785041351978,10049705020987528,9950169082001510,9868568916979326,9877016288449356,
  9995826067304847,10182691486798703,10362195076559678,10469809433692843,10481013041403130,
  10412778446710957,10304580627223545,10195333167449111,10109079955849801,10052747906640757]
private def c6_12_p3 : List ℕ := [10021778698094129,10007469332644519,10002013114383178,
  10000369409620245]
private def c6_12 : List ℕ :=
  c6_12_p0 ++ (c6_12_p1 ++ (c6_12_p2 ++ (c6_12_p3)))
private def c6_13_p0 : List ℕ := [10000000132206372,9999999518210297,10000001214810218,
  9999997907606901,10000003284314028,9999995247774892,10000006402317030,9999991685290793,
  10000010424617587,9999987315755827,10000015283097547,9999982020226748,10000020815026778,
  9999976221085296,10000026767486586,9999970262418844,10000032575289691,9999964862025562,
  10000037388698268,9999960994835159,10000040007392829,9999959842558272,10000039228414233,
  9999962709564279,10000034036228819,9999970411387398,10000024036457216,9999982551178117,
  10000010211177354,9999997290530228,9999995298830686,10000011205367882,9999983686254171,
  10000019263437195,9999980678268352,10000016015176601,9999991183628786,9999997362014131,
  10000018225685139,9999962050502863,10000061233085222,9999912594888685,10000115733067266,
  9999854836600956,10000174702110803,9999796379059692,10000231104228913,9999742980388526,
  10000281374276637,9999695451794253,10000327503901900,9999648671217072,10000377102287617,
  9999594016737661,10000438345375752,9999525850505532,10000512323620068,9999449429988774,
  10000585768465967,9999386055372262,10000630429634919,9999369024002567,10000611725084206,
  9999429770851021,10000505889287550,9999579962740042,10000316279210739,9999799725828040,
  10000078823043769,10000040116162711,9999851212479313,10000240070637183,9999692278173959,
  10000347227686337,9999644159082399,10000331971397055,9999723983967656,10000189915962143,
  9999922614741028,9999944514768763,10000200090499693,9999654833157512,10000476628186850,
  9999420932908085,10000636830959808,9999363646667864,10000568945130309,9999566863995542,
  10000236227093746,10000004575432208,9999736634127878,10000507813073597,9999297047251600,
  10000816260927065,9999176724407101,10000711989315027,9999512255236150,10000174740081180,
  10000184909226903,9999465078442863,10000813195096125,9999037325719744,10000943353361973,
  9999256041667731,10000389432406508,10000059178472114,9999487251065577,10000871536439227,
  9998951698399595,10000991828915232,9999295679641580,10000246857447231,10000272029047442,
  9999278085847106,10000985001719372,9999009419328459,10000737691647033,9999702549940791,
  9999794875411545,10000627966142289,9999145489663295,10000828695321549,9999428764327668,
  10000171532069314,10000243021487133,9999451269869520,10000663853398045,9999427762637839]
private def c6_13_p1 : List ℕ := [10000323327933346,9999989712216213,9999736196965631,
  10000420102580137,9999572592996481,10000306043233634,9999885343462043,9999925457503924,
  10000202019431691,9999759785685792,10000197903280636,9999889297313464,10000022735989396,
  10000033853519514,9999948273589763,10000047514611856,9999951495517537,10000073347396653,
  9999883965769357,10000144420447824,9999882973776199,10000011489351829,10000151494098116,
  9999696280140457,10000355524510734,9999755939638780,9999980257077255,10000336243616282,
  9999449589905197,10000526112084249,9999771602909984,9999765377913609,10000644137275864,
  9999226123670263,10000515275331804,10000043010509309,9999363965488422,10000947265829881,
  9999220288760670,10000180687794222,10000558999649037,9998955391536006,10000990712787693,
  9999608497777496,9999546393446098,10001087568019659,9998855467185855,10000564085165248,
  10000355254079745,9998893387514506,10001254112943744,9999311358782905,9999708478011793,
  10001132887522907,9998662374794243,10000760488111116,10000285903388433,9998807201518614,
  10001406571141620,9999230782092009,9999638878434737,10001301975540327,9998544630100489,
  10000692191318871,10000536338381190,9998544620001565,10001453740377674,9999503005679076,
  9999184792909422,10001616739500254,9998651940480857,10000156249752740,10001169507641483,
  9998284809232551,10001077063987063,10000328780305208,9998473611128303,10001655967243979,
  9999400590737961,9999095281213870,10001769501146426,9998652400292682,9999926401808755,
  10001454385690683,9998240514217094,10000740840553074,10000848714672116,9998198404110916,
  10001373948004268,10000122396910651,9998467207376529,10001745302661532,9999424362407702,
  9998940611514612,10001850066510695,9998854023649078,9999505151375859,10001733916679901,
  9998457432666382,10000067589966688,10001465200261841,9998236584047195,10000565788157181,
  10001113790234908,9998165037766377,10000969508971936,10000737700925410,9998202570448316,
  10001273715484661,10000378428649294,9998306133519358,10001490268142835,10000061570237349,
  9998436101511309,10001639528036027,9999801203913439,9998559022535453,10001743477459389,
  9999605056403278,9998648219815356,10001820165496337,9999479404772490,9998684055238248,
  10001879174618165,9999432815295901,9998655161624461,10001918166619076,9999476401721251]
private def c6_13_p2 : List ℕ := [9998561184042404,10001921392498241,9999621070093829,
  9998417167436074,10001860729267291,9999870209600879,9998257118096396,10001702488064222,
  10000210013770459,9998133928715911,10001420128790280,10000599164738938,9998111012900642,
  10001012778368331,10000965496957621,9998242163983994,10000523833166659,10001217967631853,
  9998540216317009,10000047480998385,10001281435869400,9998945968074837,9999705001327876,
  10001150686383402,9999324198664475,9999579239101391,10000935791107934,9999519180996923,
  9999623809154661,10000844679389992,9999479765410463,9999613927293034,10001052216818277,
  9999395314970411,9999238650836134,10001476171110940,9999698181848487,9998385802393301,
  10001624207678783,10000778481682364,9997484563470891,10000784943508153,10002451405765850,
  9997524388743142,9998695788325273,10003612544258121,9999376099089116,9996291255773792,
  10002742677461483,10002634132537675,9995597988627982,9999372323217746,10005105792928752,
  9998184735498825,9995359605533785,10004114881799100,10003094758063024,9994229214426570,
  9999208293894649,10006469890889954,9998172814547418,9993876448226529,10004320460424682,
  10004841166027783,9993664076424993,9997133279486257,10007658479259025,10000502441269280,
  9991783596035698,10001958088048384,10008058298844986,9995723499748926,9992685651334157,
  10006292082446255,10006155901290239,9992075173425660,9995239465906771,10009163816613001,
  10003288381978954,9989950977981604,9998130589403481,10010651668009375,10000599991890071,
  9988943158375129,10000453684099170,10011350461008082,9998751872258272,9988389418660216,
  10001752332084798,10011902477063905,9998063474285083,9987725991297592,10001759606431890,
  10012748400660488,9998841925898923,9986690726115829,10000040679487707,10013876336948013,
  10001700959753213,9985726149824132,9995843919555941,10014206173405231,10007327388701826,
  9986736177549579,9988957791742825,10010980091300771,10014873336161270,9993058858655443,
  9981901995945751,10000924450811840,10019692301080421,10006935886019743,9981669279559426,
  9984135871186083,10012478889221278,10023905826586072,9999033819252619,9972637661677980,
  9984548271571944,10021238170677722,10031883922295522,9997966403153643,9961553658814058,
  9972746034169122,10023355836151038,10052249675433612,10018209433368925,9953183705113444]
private def c6_13_p3 : List ℕ := [9931534588885492,9987907530893556,10073965203311241,
  10101551488998304,10029178340701162,9907051313259200,9839664895831759,9902669433337981,
  10086303073821768,10306382048549903,10464546353759901,10506632564792580,10441365732273768,
  10318590666912673,10192683951373491,10097180501819984,10039997880331760,10012762984607319,
  10002748670855006]
private def c6_13 : List ℕ :=
  c6_13_p0 ++ (c6_13_p1 ++ (c6_13_p2 ++ (c6_13_p3)))
private def c6_14_p0 : List ℕ := [10000000108277675,9999999601332714,10000001034284832,
  9999998116557521,10000003037053228,9999995624665628,10000005943432847,9999992160909675,
  10000009814848118,9999987937055515,10000014474854441,9999982971007392,10000019800663153,
  9999977360175801,10000025499639581,9999971535002255,10000031222226736,9999966202033813,
  10000036073247084,9999962093751010,10000039165075625,9999960363854242,10000039207547541,
  9999962161250662,10000035288795144,9999968325191671,10000026876981669,9999978950741033,
  10000014522674681,9999992629425970,10000000206051904,10000006505127309,9999987723476401,
  10000016390706188,9999981787312096,10000017195835285,9999987316207792,10000004412869441,
  10000007944614732,9999975684659900,10000044472290591,9999931959588214,10000094277808975,
  9999877618224802,10000151563763385,9999819273766240,10000209316728499,9999763356134578,
  10000262353616980,9999713319923712,10000309839553420,9999667305285036,10000356220839336,
  9999618701862143,10000408874975634,9999560525348082,10000472821188662,9999491826847189,
  10000543463376906,9999424078811786,10000602077456400,9999382214043646,10000618974736604,
  9999397842450568,10000564621092010,9999494426630932,10000425792119774,9999671908672411,
  10000217366988893,9999900117445382,9999982853788101,10000125957458757,9999780500084515,
  10000291376648105,9999663259238608,10000352500322052,9999662940144829,10000290586685669,
  9999784904517698,10000113908183473,10000007547586488,9999857968119602,10000280242454488,
  9999589395519908,10000519983854800,9999405285212589,10000621733383118,9999408858702747,
  10000497789000081,9999656440343646,10000138810877383,10000097930666334,9999659044452493,
  10000559495757036,9999277608313274,10000802019379662,9999220896732762,10000647244307308,
  9999584455827166,10000109539723524,10000229952227645,9999448081209217,10000801677403540,
  9999069816142215,10000904375736649,9999284049718171,10000386907866126,10000029767207153,
  9999542692014698,10000808327792707,9998996681803555,10000990494437708,9999238304431932,
  10000358957718922,10000130338544917,9999407997434672,10000912764100235,9998989829805871,
  10000856965331792,9999508031036483,10000011241433756,10000456345835540,9999214600470975,
  10000890418857199,9999249408558891,10000415562722331,10000010297984770,9999599113138696]
private def c6_14_p1 : List ℕ := [10000647112893461,9999310994346301,10000531857246594,
  9999759854813985,9999913068441126,10000349076454192,9999523723564818,10000448226630971,
  9999705297337141,10000080282273786,10000120581938390,9999750587672560,10000280574576070,
  9999775688631422,10000118081832369,9999991730150059,9999931311085069,10000098718665479,
  9999908600676052,10000071275547388,9999938398941234,10000069620277736,9999918306689900,
  10000070298834820,9999988125845656,9999907223886619,10000208525825649,9999724684124502,
  10000235811200827,9999928744150952,9999825876301417,10000398222048362,9999517851690753,
  10000350574606341,9999976158904721,9999629133237326,10000645642437912,9999358800906586,
  10000317339266282,10000205259826143,9999316201638348,10000865948124912,9999375286735701,
  10000042630866252,10000608600824801,9999006274661540,10000888673930918,9999687550948137,
  9999538778385796,10001032617209150,9998915757841917,10000560178584529,10000286046915958,
  9998988796436444,10001215162692723,9999235517312491,9999880497555766,10000965042487500,
  9998698938869203,10000921087311996,9999987052986463,9999071849298880,10001366842512129,
  9998967047394481,10000091712253672,10000929790770252,9998566913678574,10001099950264871,
  9999901695322299,9999008415518167,10001508029764546,9998888647004535,10000013595034361,
  10001122873317629,9998419435347804,10001043080540238,10000178201158937,9998686386566355,
  10001617407527775,9999136836204790,9999520624407570,10001527907927250,9998433003407457,
  10000544087520333,10000866813581592,9998297443618097,10001370772797147,9999920936716431,
  9998716682123102,10001753775203871,9999018588374221,9999499059433068,10001635204850866,
  9998407960464683,10000385434457368,10001113280828144,9998202231636787,10001146339732916,
  10000369337392054,9998385611941637,10001637644466041,9999593503592224,9998856456936597,
  10001811826176399,9998933623774618,9999479747168393,10001698671950855,9998474412871127,
  10000128750748480,10001373155868504,9998239539932077,10000709529189929,10000923824830305,
  9998207931172036,10001169115174901,10000431116724693,9998333064102731,10001490748229030,
  9999954922648220,9998560253561471,10001684708787855,9999532214888417,9998837875032030,
  10001777011730080,9999179676793501,9999123271299602,10001800535165994,9998899661758950]
private def c6_14_p2 : List ℕ := [9999384109447691,10001787846520927,9998686813091705,
  9999597118842894,10001766920604794,9998533950113207,9999745708380332,10001758223127950,
  9998436662734649,9999818427360545,10001772449904048,9998396240993266,9999808738429661,
  10001808788654829,9998420091925414,9999716423601714,10001853999031227,9998519716635626,
  9999551336706763,10001882834818579,9998704875975190,9999337311678732,10001861881497581,
  9998975459075891,9999114655260032,10001758127355840,9999311019392657,9998937029660934,
  10001554018299538,9999663622660156,9998858849143912,10001265866051943,9999960469210575,
  9998909992549413,10000957676236003,10000126283908459,9999063027796856,10000734704999377,
  10000129387976881,9999211174256742,10000699372364607,10000038397359697,9999188156968694,
  10000865922757740,10000050639006769,9998859348403701,10001068142107651,10000432611897892,
  9998275846446676,10000941835284202,10001334049896322,9997805964876173,10000085066540586,
  10002528299005247,9998081238147034,9998416622041378,10003280913048736,9999617378285647,
  9996546835374981,10002622775963193,10002209936651970,9995756490364744,10000103213774816,
  10004574949816152,9997265498179601,9996588880815426,10004827377096113,10001046458527814,
  9994281548332917,10001866243090830,10005126714843919,9995446571890475,9996810289996627,
  10006353299052772,10000369808436164,9993126462618913,10002712120560158,10006043712948685,
  9994550032577925,9995925238542612,10007383588672505,10001359235248837,9991735624276712,
  10001644878476320,10008058268679911,9995484385613691,9993097488904445,10006933862176563,
  10005040175748367,9991288211340393,9997246618543675,10009789180857341,10000309019735249,
  9989791336300536,10002076306498199,10010081894971697,9995747604880602,9990444259624891,
  10006135723316785,10008785372920631,9992299742604099,9992084040194330,10008962847233643,
  10007073946789115,9990032466531594,9993634249438568,10010769567299795,10005882673786102,
  9988579537116830,9994292111022778,10011952436639475,10005921799754865,9987638997181082,
  9993397751188823,10012588182143474,10007813338637585,9987491653548865,9990417496757753,
  10011924719890777,10011867358936960,9989418978407181,9985478693543951,10008188464944754,
  10017262128705103,9995543345220734,9980364595865797,9999129278530104,10020937774188461]
private def c6_14_p3 : List ℕ := [10007928267074806,9979914522635645,9983537819462491,
  10015542123800275,10025268076549593,9994353549098416,9968513366397792,9989751891622621,
  10030429040251502,10029867037077640,9983166725613577,9953845757994008,9988060034450539,
  10046645291994209,10050352603417800,9983647732163297,9923311322778054,9950612970457485,
  10050005373724979,10115586317930531,10062303046200939,9921891291990410,9822880887559506,
  9877091766065618,10083903552022334,10334797419129170,10500702638067888,10518917018536888,
  10415441796068421,10264675590128796,10133452338646320,10051046034928961,10012970355130838]
private def c6_14 : List ℕ :=
  c6_14_p0 ++ (c6_14_p1 ++ (c6_14_p2 ++ (c6_14_p3)))
private def hb_s7 : List ℤ := altBuildHbFrom 1856 1024 19528840000 0 1024
private def xi_s7 : List ℤ := rkmApplyMaskBits (drB 594 rkmMkHi_w64_m16_s6) xo_s6
private def phb_s7_p0 : List ℕ := [734911648344331,734647395652253,734380239417356,734110182703770,
  733837228545718,733561379947582,733282639883966,733001011299756,732716497110183,732429100200879,
  732138823427930,731845669617936,731549641568061,731250742046084,730948973790448,730644339510307,
  730336841885575,730026483566967,729713267176042,729397195305244,729078270517943,728756495348469,
  728431872302150,728104403855343,727774092455473,727440940521054,727104950441725,726766124578277,
  726424465262673,726079974798076,725732655458874,725382509490691,725029539110416,724673746506214,
  724315133837543,723953703235165,723589456801165,723222396608952,722852524703276,722479843100226,
  722104353787245,721726058723125,721344959838013,720961059033409,720574358182167,720184859128487,
  719792563687915,719397473647330,718999590764942,718598916770277,718195453364164,717789202218726,
  717380164977358,716968343254717,716553738636693,716136352680399,715716186914138,715293242837385,
  714867521920759,714439025605992,714007755305905,713573712404367,713136898256272,712697314187495,
  712254961494858,711809841446090,711361955279788,710911304205371,710457889403036,710001712023713,
  709542773189013,709081073991181,708616615493040,708149398727941,707679424699701,707206694382549,
  706731208721063,706252968630109,705771974994777,705288228670313,704801730482052,704312481225346,
  703820481665494,703325732537664,702828234546821,702327988367641,701824994644439,701319253991079,
  700810766990892,700299534196585,699785556130160,699268833282810,698749366114837,698227155055547,
  697702200503155,697174502824685,696644062355867,696110879401027,695574954232985,695036287092945,
  694494878190375,693950727702902,693403835776188,692854202523813,692301828027151,691746712335247,
  691188855464690,690628257399481,690064918090903,689498837457384,688930015384363,688358451724143,
  687784146295757,687207098884814,686627309243356,686044777089707,685459502108315,684871483949598,
  684280722229786,683687216530755,683090966399864,682491971349788,681890230858342,681285744368312,
  680678511287273,680068530987413,679455802805347,678840326041931]
private def phb_s7_p1 : List ℕ := [678222099962070,677601123794529,676977396731733,676350917929569,
  675721686507185,675089701546778,674454962093390,673817467154690,673177215700763,672534206663882,
  671888438938292,671239911379975,670588622806426,669934571996411,669277757689734,668618178586990,
  667955833349322,667290720598166,666622838915002,665952186841093,665278762877219,664602565483418,
  663923593078706,663241844040809,662557316705881,661870009368219,661179920279974,660487047650862,
  659791389647863,659092944394920,658391709972633,657687684417946,656980865723831,656271251838969,
  655558840667421,654843630068297,654125617855421,653404801796989,652681179615222,651954748986013,
  651225507538572,650493452855059,649758582470219,649020893871007,648280384496205,647537051736039,
  646790892931786,646041905375380,645290086308999,644535432924664,643777942363819,643017611716906,
  642254438022940,641488418269071,640719549390138,639947828268226,639173251732205,638395816557268,
  637615519464460,636832357120203,636046326135806,635257423066974,634465644413312,633670986617810,
  632873446066335,632073019087097,631269701950130,630463490866738,629654381988957,628842371408994,
  628027455158660,627209629208795,626388889468690,625565231785486,624738651943577,623909145664000,
  623076708603808,622241336355445,621403024446102,620561768337065,619717563423060,618870405031572,
  618020288422171,617167208785815,616311161244144,615452140848769,614590142580542,613725161348819,
  612857191990708,611986229270309,611112267877935,610235302429331,609355327464868,608472337448734,
  607586326768106,606697289732311,605805220571972,604910113438143,604011962401423,603110761451067,
  602206504494066,601299185354231,600388797771243,599475335399705,598558791808160,597639160478110,
  596716434803006,595790608087228,594861673545045,593929624299555,592994453381615,592056153728746,
  591114718184019,590170139494928,589222410312235,588271523188808,587317470578423,586360244834559,
  585399838209165,584436242851406,583469450806392,582499454013877,581526244306944,580549813410658,
  579570152940703,578587254401991,577601109187247,576611708575566]
private def phb_s7_p2 : List ℕ := [575619043730953,574623105700824,573623885414493,572621373681623,
  571615561190650,570606438507183,569593996072374,568578224201248,567559113081020,566536652769367,
  565510833192674,564481644144244,563449075282481,562413116129033,561373756066901,560330984338518,
  559284790043782,558235162138065,557182089430169,556125560580254,555065564097726,554002088339075,
  552935121505684,551864651641585,550790666631179,549713154196906,548632101896872,547547497122431,
  546459327095716,545367578867121,544272239312736,543173295131732,542070732843683,540964538785850,
  539854699110397,538741199781556,537624026572737,536503165063569,535378600636893,534250318475684,
  533118303559910,531982540663331,530843014350224,529699708972045,528552608664018,527401697341650,
  526246958697178,525088376195930,523925933072622,522759612327558,521589396722764,520415268778027,
  519237210766853,518055204712332,516869232382916,515679275288101,514485314674015,513287331518902,
  512085306528514,510879220131385,509669052474017,508454783415935,507236392524646,506013859070470,
  504787162021259,503556280036994,502321191464245,501081874330512,499838306338433,498590464859843,
  497338326929703,496081869239880,494821068132774,493555899594798,492286339249687,491012362351661,
  489733943778400,488451058023864,487163679190921,485871780983795,484575336700331,483274319224051,
  481968701016023,480658454106511,479343550086417,478023960098500,476699654828365,475370604495225,
  474036778842408,472698147127622,471354678112961,470006340054641,468653100692461,467294927238981,
  465931786368405,464563644205159,463190466312156,461812217678736,460428862708270,459040365205417,
  457646688363022,456247794748644,454843646290696,453434204264192,452019429276077,450599281250134,
  449173719411451,447742702270426,446306187606301,444864132450204,443416493067684,441963224940716,
  440504282749158,439039620351642,437569190765876,436092946148334,434610837773310,433122816011315,
  431628830306789,430128829155103,428622760078818,427110569603180,425592203230818,424067605415604,
  422536719535658,420999487865446,419455851546950,417905750559857]
private def phb_s7_p3 : List ℕ := [416349123690734,414785908501152,413216041294699,411639457082854,
  410056089549653,408465871015112,406868732397350,405264603173337,403653411338238,402035083363260,
  400409544151956,398776716994902,397136523522683,395488883657103,393833715560546,392170935583383,
  390500458209359,388822195998837,387136059529822,385441957336630,383739795846112,382029479311298,
  380310909742338,378583986834599,376848607893781,375104667757895,373352058715946,371590670423139,
  369820389812437,368041101002272,366252685200201,364455020602290,362647982287993,360831442110278,
  359005268580728,357169326749346,355323478078746,353467580312429,351601487336778,349725049036416,
  347838111142534,345940515073756,344032097769098,342112691512537,340182123748660,338240216888838,
  336286788107333,334321649126670,332344605991602,330355458830894,328354001606136,326340021846699,
  324313300369887,322273610985279,320220720182134,318154386798681,316074361671972,313980387266910,
  311872197282895,309749516236437,307612059017895,305459530420386,303291624638666,301108024735641,
  298908402073899,296692415709421,294459711744364,292209922635478,289942666454389,287657546095587,
  285354148427542,283032043381864,280690782974907,278329900255580,275948908172457,273547298352500,
  271124539782802,268680077385799,266213330477222,263723691094783,261210522184118,258673155626783,
  256110890093189,253522988701097,250908676457722,248267137460491,245597511828059,242898892329094,
  240170320671691,237410783410682,234619207423662,231794454898857,228935317768886,226040511513685,
  223108668242980,220138328953224,217127934835359,214075817487216,210980187857032,207839123711077,
  204650555377289,201412249465956,198121790205201,194776557949818,191373704322055,187910123315983,
  184382417534429,180786858517420,177119339847216,173375321354575,169549762271369,165637040529450,
  161630854526748,157524102468063,153308732687784,148975555941094,144514007142055,139911838842309,
  135154720912439,130225708764887,125104523165408,119766552999216,114181438416853,108310995999209,
  102106068852570,95501530660564,88407919290695,80696418470324]
private def phb_s7_p4 : List ℕ := [72169292593236,62493630593327,51020214826415,36072722589472]
private def phb_s7 : List ℕ :=
  phb_s7_p0 ++ (phb_s7_p1 ++ (phb_s7_p2 ++ (phb_s7_p3 ++ (phb_s7_p4))))
private def u7_o_p0 : List ℕ := [9999999761863171,10000000656633584,9999998660650801,
  10000002295914278,9999996581213756,10000004816978426,9999993653324317,10000008127161084,
  9999989918068528,10000012118913151,9999985671963776,10000016598981372,9999980927153294,
  10000021529442660,9999976028358939,10000026482491778,9999971190251896,10000031080193564,
  9999966900940332,10000034769571200,9999963939990374,10000036835155123,9999962987661242,
  10000036521665607,9999964798858693,10000033145914006,9999969786261463,10000026480545707,
  9999977978125511,10000016961214782,9999988412279059,10000005973405567,9999999415011796,
  9999995780531675,10000008063786659,9999989552073070,10000010985405362,9999990909440824,
  10000004563678656,10000002985639886,9999986188871479,10000027843345448,9999954807431959,
  10000065416314310,9999911720612064,10000113375306971,9999860076413534,10000167440351469,
  9999804780547299,10000222712634185,9999750597484768,10000274934538017,9999700783751203,
  10000322287893133,9999655687621169,10000365751943544,9999613086293561,10000408433984176,
  9999569499968378,10000453190996791,9999523556770033,10000499351182353,9999479080155319,
  10000539497666030,9999446985246038,10000559213786782,9999444474534041,10000539754660111,
  9999490026161066,10000465033141961,9999595239020459,10000330094059371,9999756708087004,
  10000147813025468,9999951918323887,9999949685787272,10000141841046360,9999779305425205,
  10000281560070651,9999679615165936,10000334136935806,9999678447961042,10000282906264689,
  9999779720780677,10000137312603792,9999961266162028,9999930620157819,10000180360100220,
  9999712953941579,10000381929001958,9999542297768178,10000507512021535,9999474684317018,
  10000506667611022,9999551117567053,10000352517583043,9999778843207368,10000062071474778,
  10000113307334259,9999709527975192,10000452305309267,9999418936260330,10000660159965710,
  9999323746683557,10000622002738736,9999502639977842,10000310830149902,9999920326508906,
  9999828366407309,10000413552620990,9999385185005070,10000746953968176,9999212097173939,
  10000726526521105,9999435176157860,10000319284670401,9999979826538752,9999707917475083,
  10000571583439421,9999226324215342,10000862556566789,9999182182334867,10000639692373866,
  9999648769723844,9999996120082702,10000366555575515,9999327443360532,10000863682900237]
private def u7_o_p1 : List ℕ := [9999100192836321,10000768649836571,9999509980614961,
  10000114464359051,10000285135430639,9999371986489283,10000842213466390,9999118968622538,
  10000734914273888,9999565266947352,10000046715409941,10000342482435242,9999354797186259,
  10000793832727149,9999242358897434,10000549964062228,9999774855613935,9999864890352649,
  10000443067279966,9999373139433434,10000648450530210,9999487311576505,10000263633104858,
  10000028226790392,9999713575041571,10000448946179308,9999516401240189,10000394701175690,
  9999781420057283,10000010610530563,10000171513488271,9999715591270619,10000309190002185,
  9999746654543856,10000145561953153,9999976348479250,9999922366443323,10000136480342515,
  9999851593585124,10000124086052570,9999917597123885,10000042046258298,9999986099946310,
  9999998197420017,10000013465607925,9999967464188879,10000065442138221,9999891315601308,
  10000147586680292,9999839224089987,10000129638751396,9999951765243744,9999930006898761,
  10000192193311452,9999723788244583,10000285711274966,9999793028647089,10000059452745869,
  10000106787666464,9999772272300802,10000250696904289,9999840128115682,9999987625038257,
  10000194872473219,9999693557560707,10000294792957523,9999835783815127,9999977103662881,
  10000175286576735,9999778103844914,10000153832125259,9999968134580508,9999951555422588,
  10000018626799604,10000113504069276,9999736023155077,10000328850935248,9999739067033687,
  10000110678960209,10000009019608446,9999986999346932,9999917636029702,10000169923496504,
  9999850774013514,10000026722511808,10000082037031901,9999936709914678,9999927201450337,
  10000189183910401,9999840052050612,10000009945521741,10000104421702121,9999932815892986,
  9999935777955482,10000129786678647,9999934719999396,9999974946881399,10000022185848469,
  10000036640291417,9999979403998089,9999920016065849,10000120371046437,9999963907403280,
  9999984651906926,9999882659565729,10000299148347358,9999729097060912,10000072370780860,
  9999971825196829,10000228325288732,9999657133965473,10000160293130733,10000029831786293,
  10000063182620624,9999804130886971,10000047109450031,10000135587512127,10000003652568261,
  9999815906774153,10000022510874787,10000109427317211,10000211092851757,9999558287092228,
  10000044012840227,10000265751190938,10000189771541819,9999484964272628,9999883206532323]
private def u7_o_p2 : List ℕ := [10000649575315358,9999871738563446,9999712960067884,
  9999640071679685,10000734322610027,10000101619155065,9999419028243748,9999701118652286,
  10000782678652732,10000252714963571,9999090515286984,9999849589938762,10001074105815013,
  9999688715891907,9999286517399054,10000528538226298,10000123974082515,9999842430111594,
  9999757728516093,10000328562986465,9999825301382531,10000324275273355,9999846332556663,
  9999332481564865,10000789346973626,10000045200001557,9999275126686698,10000479151613107,
  10000436547279101,9999792282835746,9999296630219926,10000528054996224,9999749040239394,
  10000545749721499,9998810128836014,10000281808338994,10000577478321396,10000775132664783,
  9998772168712027,10000699886077403,10001810970583099,9999584396185340,10000366091664133,
  10000050512266603,10001176950768128,10001357304636571,9999337117711907,10000870315132592,
  10001543470080109,10000148477421448,10000374103594252,10001444823181208,10001234398938189,
  9999460386797731,10000188640969418,10002251434395287,10000763599977051,10000028939276589,
  10001452637274580,10000264696373457,9999882252639459,10001940447279746,10001535136981387,
  10000600046576097,10001044892967399,10000259689107516,10000739502647808,10001446439315890,
  10000491796431111,10000555819759078,10001619189304357,10001358725951680,10003216414783097,
  10001272952954840,9999575588328992,10000559257029854,10000124901997420,9999112331896525,
  10000103143415962,9999546529928898,9998991961768145,9999777357231953,9998737472389395,
  9998989674624331,9998333355031136,9997178475935633,9998449913854665,9999510517352608,
  9999665996185220,10000142466526646,10000086830802963,9999665018011660,10000881487597761,
  10000948870945416,10000279840800164,10001687099865178,10001591302397378,10001409747382002,
  10002591086203879,10001360811285919,9999839225936560,10001103746672506,9999683656453804,
  9999586192440108,10000571227157504,9997795223112626,9999786406761051,9996592513710765,
  10001137259508607,9996300417422996,10004351282783528,9993680513993206,10004112947666063,
  9995677833230738,9997200920584323,9998682231804702,9999977219149922,9995621781696567,
  10002991867223621,9999341140777562,9999806474612702,10002283510860041,9998941030959574,
  9999056397670459,10002808141053650,9996202404041894,10000962134304972,9997086426864678]
private def u7_o_p3 : List ℕ := [10000897725530064,9998789137869488,9995524007740595,
  10003126591872078,9995237993432932,9999060428870688,10001975534721236,9993444118892376,
  10002601968167967,9996583230851966,9999297966817699,9999148076986388,9996491186487636,
  10002370305195046,9993345078008979,10004965904482676,9994587076256466,9999056135226800,
  9999289480721155,10000114789599067,9992572095220673,10006854681022763,9997177709364954,
  9995031851693489,10007297687841141,9997319652891661,9997695267233012,10001328798983115,
  10001923928915239,9997178049729011,10001709270301400,9998642865071255,9999053152524346,
  10004473517865610,9995689577612442,9999222846827771,10004205459158560,9998984331949342,
  9997540508439702,10000239138996922,9998760191631777,10002748547597264,10002320107662679,
  9998397789841729,10004593366522111,9989452778231624,9998872792703438,10008728791092624,
  9989376613560042,9995302999645273,10006579384258047,10002508894955044,10000113580717865,
  9999258859550413,10001340997351184,9998137488095007,10002358343081001,9999584972125919,
  9995700050584613,10000661902960308,10003294791011304,10011486772364337,9992414336913480,
  10024088951539057,9992685393214837,10003853139364933,9979387686853704,10009307618281019,
  10010887607626602,10002605521616693,9993561110477936,9995055759006360,9990548444934989,
  9994446670517576,10008009303531181,9992503715342104,10005079792882457,9998602714964208,
  9992803586067099,9998372611635541,10008448238178187,9986886109134023,9993868647631991,
  9998108748326669,9991237469250696,10024039611290826,9988782557761041,10027483959281549,
  10013009323953268,9994726117873532,9998542275014827,9984376461351452,10027623994582727,
  9941350661616058,10016793600173196,10015922713594662,9910799880597960,10018577418165635,
  9996748630300679,10003609080598338,9977455992500488,9972084126643567,10090118473170212,
  9976162632103330,10009956801149469,10046799316032988,9974718524150086,10058341096906317,
  9996259740550239,9909991602049170,10046522608789834,10014087898388790,9932069835473220,
  10149916563939803,10161286673523628,9883017981896912,10224152815451712,10915249438726751]
private def u7_o : List ℕ :=
  u7_o_p0 ++ (u7_o_p1 ++ (u7_o_p2 ++ (u7_o_p3)))
private def xo_s7 : List ℤ := bD bz0 u7_o
private def c7_1_p0 : List ℕ := [10000000112976674,9999999591249141,10000001042455458,
  9999998128685047,10000002994886307,9999995698919603,10000005831097986,9999992343985644,
  10000009544770250,9999988287543610,10000014036948096,9999983540991955,10000019045328499,
  9999978272507608,10000024449232388,9999972807316529,10000029804941317,9999967642087201,
  10000034563427258,9999963595997385,10000037834195636,9999961483003679,10000038518415016,
  9999962348002765,10000035848396906,9999966947298026,10000029216242582,9999975556130062,
  10000018841122191,9999987450653125,10000006078301666,10000000416258744,9999993608118083,
  10000011243497978,9999985457767666,10000015614164441,9999985966144106,10000009223263670,
  9999999120441857,9999988908607965,10000026837422008,9999953797123265,10000068695110709,
  9999906080889921,10000120998407879,9999850705644686,10000178027576341,9999793639316123,
  10000233831150499,9999740046179520,10000284722681581,9999691757664495,10000330887298976,
  9999646544827413,10000376651885953,9999598893980049,10000427560463553,9999544080599770,
  10000485923594586,9999483507903050,10000545643363139,9999428997331894,10000589381666702,
  9999402602832544,10000591729331012,9999430521724338,10000528683883662,9999531317826006,
  10000390305745449,9999703632324946,10000190938871492,9999920268628628,9999969402218484,
  10000133216493814,9999778714437929,10000288811323049,9999668656193793,10000345626781944,
  9999669478089781,10000286474169113,9999784345759994,10000121951162707,9999989522691280,
  9999887887653709,10000237897510728,9999642232577911,10000461511393005,9999461459987501,
  10000578722666789,9999426867469723,10000516173654054,9999593573990923,10000248225268156,
  9999947467222898,9999836393622655,10000377770570281,9999435742364716,10000697839968811,
  9999243526387931,10000725704273074,9999398414050832,10000392513397122,9999879820619746,
  9999817724903942,10000473817502364,9999289615825894,10000851751603456,9999131318631319,
  10000748833661211,9999498012151269,10000160809098192,10000221815746611,9999420212102196,
  10000845209610223,9999038171354127,10000897754665224,9999344107052865,10000276642423745,
  10000166882034646,9999417998832539,10000876607200582,9999018820708892,10000866918051624,
  9999443710099003,10000120106938927,10000337686360506,9999294647544978,10000892603420057]
private def c7_1_p1 : List ℕ := [9999145039272377,10000606276019630,9999783665205888,
  9999791242048642,10000555986246620,9999263129339201,10000712202935257,9999498381255167,
  10000175190099398,10000168535733086,9999566696105389,10000553114482896,9999490889450027,
  10000331509424126,9999913779928710,9999850981856471,10000308785725126,9999641286517459,
  10000302096045305,9999826556514800,10000023144127526,10000100822443072,9999831467501583,
  10000174391619127,9999865489736295,10000076594344309,9999973467936724,9999997402072249,
  10000013797966108,9999977932145236,10000043619249593,9999916291709669,10000129715883604,
  9999845887898953,10000126559530722,9999967237834970,9999889145677596,10000255306945329,
  9999665947008373,10000292855388739,9999877278104735,9999877144359653,10000338438205630,
  9999589307807978,10000282498819721,9999993634777689,9999743823852989,10000318834955616,
  9999880600958918,9999822650434692,10000279402709379,9999921315784151,9999853677509191,
  10000038237247318,10000260479414803,9999775685158318,9999886449668494,10000086117883610,
  10000235737226327,9999965133475873,9999651151665361,10000069143994755,10000181782936360,
  10000139372567336,9999449685547695,10000293724837454,10000493498393491,10000702738425899,
  10000067561206294,10000182479157649,10000642774140315,10001156805717093,10000320229615535,
  10000039783753000,10000661801302150,10001293551565094,10000502808479666,10000017002219327,
  10000626677365893,10001434207949069,10000855671640097,10000188286378135,10000492011231784,
  10001266420577398,10000831422301637,10000187196652314,10000483079234755,10001270062456872,
  10001044874190859,10000154092666458,10000689103396506,10001309825973255,10001129820860128,
  10000112956194243,10001044039610758,10001123863776169,10001141540543362,10000509692869325,
  10000887374566436,10000837695357778,10001520310685930,10001315150049973,10000011124956874,
  10000132023507953,10002207036784979,10002271500387781,10000767168370717,10000040024394290,
  10000855201258708,9999495480626187,9998903653125862,9998894199383199,9998963421206127,
  9999588332003388,9998837957081638,9998344198362060,9998937072481780,10000463568686332,
  9998925807761810,9997290270034942,9998294775330737,9999522871629543,9998996760127220,
  10000187397280904,10000825346445557,10000938363420759,10000897154903472,10000289460383486]
private def c7_1_p2 : List ℕ := [10001526296453979,10001949130149047,10001069442818314,
  9999581869587296,10001313610762516,10002801190714794,10001002686711310,10000903781691044,
  10001270090380276,9999370374114489,9998727197337482,9999794529181578,9999387617896132,
  9998085701674005,9999364169790545,9998312381106105,9999644998540131,9997670201203870,
  9999935460773502,9999545621378878,9997861256420625,9999179074058733,9999340225771170,
  9999013346963463,9999159000857012,9997930819095143,9997771603765128,9999404606835852,
  9999702610856957,10000169661590216,10001815537531600,10001148345376078,9999931508150917,
  10000471707981792,9999470935657865,9998488826084187,9999499257566314,9998821710154356,
  9998228971717990,9999357746239539,9998608258026770,9998289907494110,9999327302523950,
  9998425080403943,9998436243444899,9999295712496905,9998221849269873,9998726965597032,
  9999015946778094,9998478250917495,9998384969329837,9999526687017880,9998021988130356,
  9998633253628261,9999502622723812,9998409321633875,9998113007775506,9999438582996706,
  9999527608175860,9998078261826274,9998535870203121,9998864101007792,9999660699711552,
  10000125590770173,9998344091812941,9999455055541240,10001677989419857,9999911881751554,
  9999738550761140,10001346479611630,9998826915632103,9998859436430459,10001820455048326,
  9999187501673082,9998392461800757,10002084736717489,10000306544432201,9996793614799960,
  10003130821262401,10000388925708452,9996004233577998,10004496987521066,9996817169113758,
  10002585624971728,9996870773996530,10003311395794932,9996852001765730,10002953071012242,
  9997209912913093,10003783741476546,9997426685925867,9998546087267793,10000275467942392,
  9995262998515841,9997357984086240,10003145453582420,9993036015870712,10004633558295281,
  10004878491034095,10001120518089098,9998378465362801,9996957732960376,10007258040267597,
  9998638190305168,9994751152797442,10006530105919665,9993641903117829,10000934444942843,
  10008026354544790,10002034648296007,10003952939003039,10004854445084784,10004390206031327,
  9996546289305209,10012549460790674,9996907012018995,9993805975010634,9990525792039917,
  10002403891066469,10003201187736764,10000828047503924,10000279448955419,9996664317375522,
  10002193222090405,9988606967547647,9985902755451587,10001303191510470,10004268938376023]
private def c7_1_p3 : List ℕ := [10002020720908533,10009779025397033,10001408644724403,
  9981230069326183,9993879064392744,10004175731698581,10000249155965619,9999363610678998,
  9991407760719912,10001842834191391,10006089588084072,10001466296758140,10007218654974530,
  10013578345489066,10013711109840925,10006489038093940,9998403845471352,9994760325570840,
  9989510008755795,9992718534262344,9986091436832172,9991953378595291,9990684752783524,
  9976740157502202,10008959904034978,9972557193831726,9987078684044769,9979999736870481,
  10008255575050347,9994605117048422,10008991136038920,10009336464735341,10005555793559659,
  10019572335971711,10010714073232891,10004366644545799,10023829188983947,10052581380773119,
  9993718340142894,9966578188213926,9995577751105417,10030377232888254,10034580933751715,
  9927740238896872,9976881739999535,10022605074648788,9985858987494402,10076506140227626,
  10036667707998170,10039663732193634,10124790184343616,10035684768968708,10093779032329856,
  10198449047205506,10074222940328107,10108378602606639,10363903892085908,10568523683001909,
  10544237838019717,10346218034670954,10135192222141619]
private def c7_1 : List ℕ :=
  c7_1_p0 ++ (c7_1_p1 ++ (c7_1_p2 ++ (c7_1_p3)))
private def c7_2_p0 : List ℕ := [10000000139527136,9999999509173543,10000001199198876,
  9999997973797881,10000003166847040,9999995432317662,10000006113965457,9999992125143843,
  10000009829429938,9999988055128410,10000014279568735,9999983337085374,10000019213166304,
  9999978164685831,10000024482443224,9999972854680934,10000029673225162,9999967852399331,
  10000034264401462,9999963965569495,10000037412728994,9999961932091817,10000038094514156,
  9999962717147517,10000035569707424,9999967086910763,10000029285357858,9999975207577718,
  10000019499671929,9999986479088144,10000007332180672,9999998941510085,9999995249121768,
  10000009558045500,9999987015432779,10000014376343758,9999986666646912,10000009283421368,
  9999998084650724,9999991058189228,10000023473767536,9999958482211100,10000062697984190,
  9999913228497773,10000112940169884,9999859409705314,10000168961959181,9999802705806009,
  10000225047975267,9999748400661331,10000276899044661,9999699073551734,10000323801373242,
  9999653891869201,10000368505414133,9999608415149236,10000416026878204,9999558020653640,
  10000469515936447,9999502104529171,10000525780598223,9999448666201650,10000571853777917,
  9999415481057118,10000586159323936,9999426285217918,10000544897088641,9999501754418530,
  10000433491515085,9999647927216947,10000256746152147,9999847928850952,10000043545822563,
  10000062411980624,9999840968532238,10000240152022765,9999699875448670,10000334788524143,
  9999658335581706,10000319794470362,9999729775712505,10000195704091438,9999899845731290,
  9999989278325476,10000130341574219,9999749088757561,10000363755289323,9999540297702697,
  10000529200080826,9999436606875068,10000554804009512,9999501486160762,10000393672166663,
  9999755705827743,10000059795778952,10000144404289917,9999651510674135,10000529463516024,
  9999336114688611,10000731284247466,9999282919876017,10000615656721391,9999567343897312,
  10000185156682828,10000098622919474,9999617345416015,10000627065885845,9999206363643830,
  10000852224082917,9999213834279858,10000596874969288,9999693961578111,9999954249033248,
  10000403366256217,9999294852961119,10000894186913326,9999070986614044,10000794206672397,
  9999493591139981,10000114125476930,10000308689940639,9999323570463341,10000910096523420,
  9999045009447049,10000796127961583,9999535850777761,10000030979420838,10000404911151797]
private def c7_2_p1 : List ℕ := [9999258269210163,10000899771507990,9999157963009488,
  10000585278664162,9999803359996226,9999776272894815,10000568541636892,9999247184636509,
  10000736368055055,9999466311072662,10000208783284270,10000144333704006,9999570220624405,
  10000576361993511,9999443270397357,10000392018751025,9999858016642307,9999884608611259,
  10000308382394792,9999607765108734,10000358757006148,9999765122396341,10000069809760389,
  10000083215992070,9999816389701010,10000214041995330,9999817624328990,10000113763585197,
  9999960952758886,9999982456176852,10000046576961701,9999946116925575,10000054289832622,
  9999937753597845,10000081717237308,9999897621639362,10000103524239270,9999935337090787,
  9999979217945976,10000135558100910,9999760120733816,10000284127085530,9999768536001130,
  10000080556299318,10000124186611600,9999696580881352,10000374147626651,9999707782482540,
  10000083945097264,10000153929579363,9999704386995576,10000256117032755,9999946632724894,
  9999813894310998,10000300398367497,9999787713567139,10000006922088020,10000121982654178,
  9999951291885736,9999860143864669,10000210304674430,9999954331571901,9999817107488236,
  10000206627691565,9999965521276146,9999974359437688,9999830559739400,10000327360529899,
  9999811113952435,10000025874996843,9999830529095488,10000299621725132,9999987804437881,
  9999771921846526,9999888377475560,10000404616454543,9999968986444255,9999767158725255,
  9999846907306444,10000271210297843,10000176430830323,9999834170464454,9999628416943738,
  10000265482039188,10000465968329264,9999821532387175,9999274211702342,10000050676518689,
  10000600103273178,10000064207520243,9999540718153656,10000225912667245,10001072408818508,
  10000404106837716,9999951278983515,10000243357015446,10001334191292409,10000593519630870,
  10000178213332175,10000110101648019,10001381727123442,10000670782224021,10000164735512888,
  10000623478275821,10001437678599551,10000645838765877,10000174479010975,10000833272311861,
  10001084876897417,10000461156658678,10000754277096667,10000473614926028,10000909502645987,
  10001051621693281,10000960876111795,9999965705857284,10000817698601715,10002248834073160,
  10000415786051138,9999849464712636,10000920444800570,10001966210361621,10001157173573307,
  10000604761749914,10000272292518717,10000821768760926,10001340173896062,10001213130599198]
private def c7_2_p2 : List ℕ := [10000839670378532,10002433998222694,10001812783212066,
  9999227635279605,9999951603782837,10000359864819013,9999802592724577,9998411951356243,
  9998487543197311,9999196907650943,9999555332269460,9999476779304713,9998715301583289,
  9999222866445881,9998576619818748,9996852930735247,9998903045340010,10000552239369865,
  9999576357365470,9998517600430164,10001815846699968,10000335725917123,10001653197199534,
  10000856828642726,10001024478416348,10000583754056463,10000274370597023,10002637096496174,
  10001867659118479,10000770541220903,10001810073660964,10000621118413371,9999384025461844,
  9999991636075313,9999555275258549,9998990017046876,9998986640575794,9998233553709056,
  9998841525724095,9999934824445451,9998508168245658,9998156056648573,9999526652689078,
  9998922945686707,9999086800092376,9999962067722852,9998256172139597,9997788396852793,
  9998547315895848,9997949606590350,9999343422598067,10000948530502841,10000267069427457,
  10001304993738488,10000817082795791,9999931808063261,9999788435158014,9999789406691393,
  9998432973313752,9999394807204528,9998955887555598,9998191650847997,9999227893172294,
  9998815313490763,9998180758047959,9998905525326722,9999246401934576,9997889345018713,
  9998698563818718,9999492884761713,9998082537760326,9998471794713060,9998932666622753,
  9998740986585029,9999214325294880,9997928811066657,9997862010009837,10000551347601118,
  9998979735709766,9996917243523564,9999813182638798,9999045239765347,9997820134426505,
  9999924736223534,9999698829836614,9996696779353024,10001231263658975,10002793384602164,
  9994627642111769,10006024530833649,9996600807627111,10001334891181391,9997868469045156,
  10003379764713910,9996083807758220,10002644747024399,9998068258968127,10001809019699049,
  9998929304217777,9999378359584705,10001808706681641,9998774058519535,9998492052157925,
  10004701807749545,9994404638824077,10003052252920773,10000447340237016,9996498390179461,
  10003915817225842,9999856729592040,10000060175212410,9997660110598495,9998927325534328,
  10004064939398105,9987474877292023,9999591384074370,10005792948992930,9996499658960733,
  10003661041607735,10000813580262346,10000158984148126,9997962000523231,10009097375662434,
  9992558525734819,10001967700828077,9998902006505402,9997903876231498,10000781876103211]
private def c7_2_p3 : List ℕ := [10007378499125988,10005051133868765,9996593594113922,
  10006394791929455,10007122015332185,10007823075492672,9998858010078462,9990191830499990,
  9999954464416994,10001652089051511,9993330585970734,10001675476999007,10010596858270416,
  9994487829995633,9994994570190621,9996576306053463,9982917010295479,9996723936279296,
  10008176394943292,10010631520124466,10000314156633281,9987730897470504,9995861575866940,
  10002128750034945,9997056179244745,9995070578300671,9997816280217958,10001330220439585,
  9995896231792926,10002528361538533,10005341281861892,10013197678026539,10018199408057719,
  9997786189376538,10019094543704952,9979592770451573,10003217171104714,9989001413099285,
  9992446901660624,9977656225245368,9999197197931183,9993066579978818,9979402309487416,
  9985968127035604,9979981604858019,9992002828413783,10000266954947709,10001417848055643,
  9994507238739828,10030476264352158,10007965419966852,9983582633616018,10029995109229490,
  10040473621998271,10044820983412322,9949228726465155,9987768986994042,10069480584312505,
  9971808930677744,9999165416533187,9968308172951188,9957591362258906,10059234832259137,
  9992098051679969,10046530606940588,10113857979708370,10002098920618774,10102453421403891,
  10184992919011859,10063099281569947,10064962233294088,10342144806491449,10606393736077355,
  10574525898312731,10302080190258517]
private def c7_2 : List ℕ :=
  c7_2_p0 ++ (c7_2_p1 ++ (c7_2_p2 ++ (c7_2_p3)))
private def c7_3_p0 : List ℕ := [10000000244040486,9999999320398479,10000001393214255,
  9999997614424488,10000003533190817,9999995032717829,10000006553674096,9999991602206270,
  10000010380068979,9999987546901867,10000014809130462,9999982813845107,10000019690055687,
  9999977719266251,10000024869700383,9999972548630633,10000029912309487,9999967826164721,
  10000034265954862,9999964076895160,10000037123087563,9999962293499162,10000037629066572,
  9999963211199186,10000034981863415,9999967609564546,10000028833314979,9999975582490564,
  10000019317151960,9999986429822003,10000007616682649,9999998362836949,9999996067760710,
  10000008568716850,9999988160926006,10000013238100078,9999987775667249,10000008422330843,
  9999998573621786,9999991122147615,10000022776928500,9999959914901938,10000060506600849,
  9999916164750543,10000109305717215,9999863596228735,10000164403802468,9999807418167144,
  10000220386557192,9999752852530178,10000272747332836,9999702969791184,10000320069128683,
  9999657643990029,10000364355586657,9999613428456957,10000409690870255,9999566070964837,
  10000459486075198,9999514159441759,10000512081291126,9999463261928911,10000557473687719,
  9999428094616519,10000577187637386,9999429614286781,10000549048274160,9999488628022631,
  10000456564298913,9999614851139367,10000298870986419,9999798644792236,10000097148707084,
  10000008066187954,9999892074452883,10000196247629946,9999732943995338,10000315537534892,
  9999661740299103,10000333324755360,9999699308926430,10000242002065903,9999839530175571,
  10000060966269502,10000050847927206,9999832081101492,10000282562216946,9999613377013550,
  10000471404065044,9999471409097631,10000550536211105,9999468789410088,10000467234764969,
  9999641316752503,10000210130724793,9999968836886835,9999836033362502,10000356535383808,
  9999474233529632,10000650436439400,9999288216732544,10000696865795216,9999399467556541,
  10000427680560768,9999806030775329,9999924632984309,10000347544161375,9999413943172567,
  10000755765696310,9999172230658606,10000785188468511,9999373520287117,10000367935853362,
  9999956730187980,9999699776241918,10000607615089015,9999174870857163,10000910167186715,
  9999159952921958,10000618721744250,9999720707850728,9999879909207416,10000504871688083,
  9999201532088846,10000938246152903,9999109898344515,10000658596060971,9999711335051830]
private def c7_3_p1 : List ℕ := [9999857832275073,10000539421754477,9999186213376367,
  10000902137716541,9999215754572328,10000489285482018,9999910524141025,9999682865257436,
  10000631399016323,9999220972845511,10000729460192969,9999496458920269,10000167394541342,
  10000187207627883,9999532203455297,10000606735760519,9999421253522095,10000405006740560,
  9999855399249675,9999875388531813,10000330078065018,9999576019700380,10000394907489626,
  9999732880143069,10000089273125698,10000082624357133,9999797345258367,10000247679396454,
  9999779712686938,10000143756482166,9999948639117219,9999973066954059,10000073632442133,
  9999912643998675,10000079779848968,9999932638343647,10000062034488612,9999934866374452,
  10000066020370149,9999951642193976,9999999850662964,10000078154739493,9999834311167908,
  10000228209495457,9999769912887159,10000151334034590,9999997462927505,9999828069881183,
  10000306828902947,9999658153488516,10000251120715790,9999936899423418,9999855630984649,
  10000274834410759,9999739662190284,10000102388464264,10000119544967706,9999715062413189,
  10000300319561966,9999837515613387,9999969147978220,10000142861807448,9999900716306102,
  9999954784159820,10000141629312556,9999925213097515,9999879381653894,10000277631692227,
  9999741510766671,10000108661003741,9999979186998200,10000112884949672,9999730449296844,
  10000271569997638,9999912178678195,9999938505187697,10000003116075831,10000131718764923,
  9999889027333662,9999990004356474,9999976151956271,10000181603624149,9999864767404840,
  9999876265894460,10000149547488810,10000163291878509,9999731946598348,9999945818555572,
  10000193534607497,10000122690523369,9999779808316371,9999871558650879,10000146005798505,
  10000239514570171,9999904352315015,9999581619491247,10000199649565001,10000335955650427,
  10000050953149988,9999296758063762,10000254341383585,10000434618075494,10000155313817649,
  9999112360561165,10000129908201511,10000553136387104,10000230285845882,9999382450848666,
  9999854408932426,10000560365482963,10000126233739973,9999169912765702,9999820163323505,
  10000662071146102,10000373453556389,9999271312389744,10000523854866391,10000847628019157,
  10000260180280047,10000134557647916,10000730710473217,10000885096244716,10000120264222848,
  10000788024777973,10000254305690409,10000727857706892,10001218079383083,10000478054055569]
private def c7_3_p2 : List ℕ := [9999984120808473,10001443783532145,10001281279246194,
  9999971394344099,10000070154704520,10001542186654945,10001169744212737,10000210539302124,
  10000441590916274,10000321890585842,10002016011608960,10001138478971308,9999678076440599,
  10000668395241015,10001613591488376,10000863924253520,10000425455784943,10001720343281139,
  10001368020811222,9999953399186009,10000252716724448,10000681183749489,10002457785610404,
  10001443710185121,10001058282270961,10000677868498599,10002777423723500,9999236472297525,
  10000111902831764,10000587516033826,9998316791400963,9998381387671192,9999257178844374,
  10000649046402477,9999351140210928,9998075595689370,9999059723031803,9998111401973174,
  9998068150199449,9999599205591868,9998559840223821,9998383331212242,10000523528708128,
  10000872906837418,10000663422595773,10001096435543176,10000415907132593,10000520920013458,
  10001222939159241,10000871778990250,10002021336377869,10002581953048665,10000519601434742,
  10000822491060563,10001599283154673,9999891373787804,9999674994610647,9999611951219276,
  9998169667157335,9999641609639505,9999201507972361,9998600295966953,9998770739288176,
  9998730985177552,9998352233653958,9999948113122089,9999510826180026,9998891660591076,
  9999113250815366,9997529878658850,9997684320500592,9998723762282354,9998993384410306,
  9999754010586461,10001218831004019,10000661978911743,10000140204131468,10001152882415552,
  9999712163114895,9998941648977238,10000005296293083,9998939683285361,9998453592141035,
  9999182446006493,9998550945146901,9998950725462161,9998943503259405,9997357565656168,
  9999900754954721,9999374168174065,9996823015578011,9998811779393867,10000254114019184,
  9998210509979291,9996378504837708,10003330387388184,9992250610404984,10004353058725971,
  9996564384187628,9998850558288995,9997172101133939,10002449385605351,9994889860101339,
  10001122692241254,9998062147835004,9998507810043930,9999293310281549,9999610504997874,
  10000776525920410,10000367024179035,9997474612767650,10004858515162823,9995390615541461,
  10001462399135691,10001976797645134,9995517536554056,10003737840302483,9998880652186801,
  9998666763683889,10002132480598104,9997753132201594,10002920406706618,9995466611405830,
  10004323169980031,10001356500741379,9991388300631717,10007326587685006,9999961655071372]
private def c7_3_p3 : List ℕ := [9997374311564169,9998384689098323,10008234242369330,
  9993370993083328,10003197568389180,9994940716160493,9994089215319700,10001611895773613,
  10001022297628809,9998834226265243,9999339238711929,10004940545281805,9996834981615093,
  10003107843074155,10004380563920095,9996522056937648,9996690073607710,9997803417387697,
  10004508360163270,10005746834042271,9995859478925447,9998063442868373,10015376110226264,
  10005473367561130,9997991544450491,10009556617238166,9994450770719854,9993994750330258,
  10000024261345261,9997963021190194,10001994485073794,10004632210078114,10004912084283706,
  9992840215660656,9980809318737184,9993250398095329,10007141453382115,10008014972972878,
  9995536890518160,9998570046037999,9999182210442169,9993612821356251,10003236997167511,
  9985482025177450,10014974589770954,9981008170732967,10005645028071010,9995287381574429,
  10007206674041190,10008762113435140,10021724090751951,10004588803766595,9998493667598079,
  10010159532496826,9989860600951859,9988222286720943,9988850492096352,9993681656988851,
  9989306170853684,9995489147396135,9968576381833370,9985022152175647,10003817258051697,
  9967193369411699,10007916692221975,10009093379113861,10026405939939166,9975026928169485,
  9984579575657678,10102682856253859,9992302509404092,9987632206824586,10020614806618823,
  9991940262230878,10057981439381971,9956510059216496,9961053512892468,10029090358050730,
  9941719147394822,10055274351565691,10082864947579934,9986814830609415,10099266396909437,
  10185542225770652,10040177391337014,10036342212518092,10387528301884570,10689038536305109,
  10535932486519045]
private def c7_3 : List ℕ :=
  c7_3_p0 ++ (c7_3_p1 ++ (c7_3_p2 ++ (c7_3_p3)))
private def c7_4_p0 : List ℕ := [9999999892666665,10000000381537730,9999999036762115,
  10000001739848333,9999997174149241,10000004105756370,9999994435684761,10000007255856349,
  9999990927723755,10000011145296016,9999986702013863,10000015575877154,9999982001920649,
  10000020465115752,9999976961287715,10000025508312669,9999971972072542,10000030428485385,
  9999967474234562,10000034451270781,9999964075229764,10000036962194593,9999962598797736,
  10000037107963926,9999963910099107,10000034232734286,9999968552047252,10000027876311204,
  9999976515862326,10000018465284656,9999987124952089,10000007081565529,9999998556087828,
  9999996172200894,10000008101969998,9999988936571586,10000012134515757,9999989179315843,
  10000006884476961,10000000213890908,9999989409657504,10000024324194495,9999958621284204,
  10000061540509403,9999915548536754,10000109590552287,9999863689462589,10000164055093605,
  9999808008331063,10000219662236353,9999753510852911,10000272124894997,9999703441197005,
  10000319633562225,9999658165779998,10000363548700665,9999614807037450,10000407401044710,
  9999569568781405,10000454426007534,9999520950952650,10000503611481823,9999473166204372,
  10000546803737630,9999438681649121,10000567879266403,9999436353904750,10000546391562151,
  9999485906248890,10000465715379914,9999598721560898,10000321968887994,9999769344510258,
  10000131097172114,9999971566520421,9999928524723891,10000162753184905,9999760620716976,
  10000296222660373,9999670714211129,10000336048321154,9999684294937649,10000269038615261,
  9999801402183952,10000108635400469,9999995807460231,9999891748497664,10000221625820560,
  9999671679411985,10000420363293477,9999509911209229,10000530102850250,9999465770903555,
  10000498152580160,9999579949040630,10000301719092999,9999850982591810,9999971942174944,
  10000214953788118,9999605796132608,10000546364196556,9999347616135347,10000696174026635,
  9999333107186543,10000561603960630,9999613608248244,10000156844571743,10000102542564310,
  9999638969771475,10000585032525994,9999257756924861,10000807063762408,9999235716911649,
  10000613063474703,9999631519424932,10000060939190472,10000266612348810,9999435484017686,
  10000783540366454,9999116679985633,10000840590180585,9999345214390017,10000350859305260,
  10000022411756625,9999599799471770,10000711861073329,9999104899123786,10000909448952910]
private def c7_4_p1 : List ℕ := [9999253741171443,10000433399383674,9999968392761971,
  9999623275042182,10000704483616991,9999120252001591,10000862917174587,9999342712987725,
  10000310309025521,10000097393812584,9999529737708768,10000721324604424,9999205899934483,
  10000676593687764,9999595709906512,10000050614079030,10000293176152795,9999457991976612,
  10000639162541831,9999429486938286,10000365746829055,9999911505863636,9999816587570255,
  10000380134436286,9999541831401192,10000410400154686,9999735451076484,10000071539978554,
  10000110896082163,9999763830763871,10000280321258042,9999754175722508,10000157069550088,
  9999950745903371,9999955684775854,10000102011237468,9999880896261679,10000105432129854,
  9999921891071868,10000053431776997,9999961068327256,10000031150248781,9999981327381834,
  9999989054902277,10000062230324657,9999873950580104,10000180434532716,9999802956870409,
  10000154039518102,9999951247329695,9999904357567066,10000233696626857,9999687685532319,
  10000293345513697,9999826804905739,9999990999007689,10000181719486599,9999730303412989,
  10000228651060784,9999929028967115,9999866645616046,10000286533289499,9999687879970297,
  10000198336191399,9999989663529702,9999855922874098,10000179715229011,9999908457783348,
  9999963230101187,10000088467236662,9999997341094606,9999828230965006,10000306926679011,
  9999700409863602,10000165705803319,9999966277641141,10000026499634183,9999863343163090,
  10000225490196104,9999832248437828,9999999582249617,10000105856697077,9999967410643755,
  9999867761142515,10000192581167871,9999914587484349,9999960584793938,10000026578663311,
  10000066534232644,9999931439375857,9999977753797633,10000023811772880,10000108658004075,
  9999846817074974,9999978364862724,10000169404599429,9999968798625850,9999824650906079,
  10000063058864466,10000229342633929,9999771002188580,9999991734143707,9999973714454580,
  10000300491950898,9999729317741369,10000012368457107,9999871899946982,10000426433968960,
  9999800561293598,9999804453051415,9999914671555246,10000480878623694,9999988664200594,
  9999480228274287,9999982952533229,10000619013373010,9999940161886703,9999495087264646,
  9999827061261051,10000772246756558,9999957950490951,9999494989708822,9999677259911459,
  10000734315174937,10000350406774928,9999061265193331,10000044668164532,10000572142674785]
private def c7_4_p2 : List ℕ := [10000126389556336,9999053726677303,10000406229156038,
  10000616648164271,9999654148048486,9999770499189646,10000263165500223,9999727794197721,
  10000063043780701,9999902711503364,9999666223497555,10000337024367852,10000447881037942,
  9999806882907954,9999733563813711,10001608728159721,10000319294967583,9999690515381756,
  10000778605172180,10000835971761767,10000759947315848,10000143782157116,10000138090872614,
  10001290499290602,10001483418569471,10000131776870490,9999484354247774,10002059522238750,
  10000965989137584,10000436974089265,9999826067376324,10001644700453445,10000219907535827,
  10001268045831972,10000320326548945,10001182492725092,10001654579055448,9998848541020006,
  10000968369287950,10002442721626800,10000983096884894,10000452625226988,10000719373373734,
  10001078550417067,10000047881147492,10000686283961776,10002494678818957,10000960642679311,
  10000484840160089,10002426779701851,10001722120771156,10000603291547037,10000542794631462,
  9998894995488672,9998646374557713,10000254968536033,9999828136607353,9999204039481871,
  9999201842933048,9998465393062969,9999160716611827,9998905539687726,9997402604498120,
  9998496475732501,9999297014322045,9998243472831586,10000844383905670,10000948308298670,
  10000164202125073,10000330741127911,10000397465417112,10000566932826750,10001996482304168,
  10001297411171493,10001137066590426,10002213872763529,10001227320021737,10001427193771225,
  10000886912453702,9999469624688295,9999549820372364,9999787868557647,9999107451163738,
  9999188471918994,9999154620801959,9997744881219890,9998685692753790,9999714175273014,
  9998880906570551,9999869568422213,9999663439144366,9997593857318318,9997983124485699,
  9998326128914899,9997566688460311,9999666792962360,9999620877459475,10000365405274872,
  10001543262795055,9999293590524063,10001163893134065,9999712665149619,10001425341865028,
  9994203643069111,10006111682748897,9993639011385542,10000966391265199,9998267701341411,
  9999287550518245,9997035882244903,10002069691546582,9994764229494387,9999930147693615,
  10000277622460628,9997157074605974,9998466526483445,9999395134866922,9997508121510797,
  10000651373203451,9995625327024902,10002382256306793,9995927898224136,9998220313122142,
  10002921785509403,9993876835416656,10001061315467584,9999069019573962,9995721090177929]
private def c7_4_p3 : List ℕ := [10003102257959199,9996519665348372,10002287647401715,
  9998271724504298,10000908253849143,10002022580798971,9994013407092396,10007329496332119,
  9995422531768433,9999122508532612,10002059179308387,10003523263601965,9990395059273017,
  10007253988599748,10000423932539543,9995959725194738,10002617927495254,9998889187361615,
  10000432319686883,10000049592854389,9999848251804922,9996262804098999,10006177961648080,
  10002268246173263,9995418172161875,10000595173151569,9996337322741281,9996378912205283,
  10000347022720945,10000196635840787,9999186460128544,9999447693309976,9998598016570129,
  10008880148190798,10003927241760427,9985990586767275,10005458694477121,10004778897322928,
  9994154707699198,10001716780432480,10000579504075533,10001704495399660,10006363251260228,
  10008339147206200,10005994167629524,9999038615711350,10001973805746290,9996442033803050,
  9992414388880862,9997914043936012,10012654968898165,10010526851537539,9982620454096005,
  9996806221563590,9981270133293461,10015948500093060,9987529940309144,10009415022179666,
  9997956697882464,9997687162862307,9994243860704167,10002227003183971,9994928925709493,
  9996233236241301,10003316610834741,9983585986309096,10001294218849594,10011051540730890,
  10010685848662099,10006497277841555,10017549117494416,10000335788074490,10004096070881127,
  9993490661237057,9973666700617542,10018076142955878,9977783470038454,9987499293002952,
  9982517359619438,9991298713122124,9986436069913221,9940858514452302,10065858338071509,
  9993700017167930,9948222411494703,10044774442909239,10012265243126659,10054519795494581,
  9983566725722753,9985464472685515,10078467357664683,9963452360301973,10011413167510466,
  9998943954763154,9917284389659795,10045593218939465,10053858184843905,9962388895705921,
  10108749835472488,10187389121148009,9986075179001489,10047293257864495,10561687133909836,
  10769371780817266]
private def c7_4 : List ℕ :=
  c7_4_p0 ++ (c7_4_p1 ++ (c7_4_p2 ++ (c7_4_p3)))
private def rkmWalksHi_w64_m16_r1024 : List RkmWinSegWalk := [
  ⟨64, rkmHbWin_w64_m16_s0, 0, rkmXsWin_w64_m16_s0_in, 0, rkmXsWin_w64_m16_s0_out, 665633573⟩,
  ⟨128, rkmHbWin_w64_m16_s1, 0, rkmXsWin_w64_m16_s1_in, 0, rkmXsWin_w64_m16_s1_out, 1380127811⟩,
  ⟨256, rkmHbWin_w64_m16_s2, 0, rkmXsWin_w64_m16_s2_in, 58, rkmXsWin_w64_m16_s2_out, 10243149830⟩,
  ⟨512, rkmHbWin_w64_m16_s3, 58, rkmXsWin_w64_m16_s3_in,
    222, rkmXsWin_w64_m16_s3_out, 22153324956⟩,
  ⟨1024, rkmHbWin_w64_m16_s4a, 222, rkmXsWin_w64_m16_s4a_in,
    580, rkmXsWin_w64_m16_s4b_out, 49167225065⟩,
  ⟨1024, rkmHbWin_w64_m16_s5a, 580, rkmXsWin_w64_m16_s5a_in, 844, xo_s5b, 47498279950⟩,
  ⟨1024, hb_s6, 844, xi_s6, 594, xo_s6, 22664265303⟩,
  ⟨1024, hb_s7, 594, xi_s7, 523, xo_s7, 3225874091⟩
  ]
private def bAll6 (a b c d e f : Bool) : Bool :=
  match a, b, c, d, e, f with
  | true, true, true, true, true, true => true | _, _, _, _, _, _ => false
private theorem bAll6_elim {a b c d e f : Bool} (h : bAll6 a b c d e f = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    first | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | exact Bool.noConfusion h
private abbrev m16B0 : Bool :=
  muxIntListEq (uHb phb_s5) (altBuildHbFrom 1856 1024 19586394833 799 225)
private abbrev m16B1 : Bool :=
  muxIntListEq (uHb phb_s6) (altBuildHbFrom 1856 1024 19587930735 580 444)
private abbrev m16B2 : Bool :=
  muxIntListEq (uHb phb_s7) (altBuildHbFrom 1856 1024 19528840000 508 516)
private abbrev m16B3 : Bool :=
  Nat.ble (Nat.add 222 (altIntLen rkmXsWin_w64_m16_s4a_in)) (Nat.add 1024 1)
private abbrev m16B4 : Bool := muxIntListEq rkmXsWin_w64_m16_s4a_out rkmXsWin_w64_m16_s4b_in
private abbrev m16B5 : Bool :=
  Nat.ble (Nat.add 580 (altIntLen rkmXsWin_w64_m16_s5a_in)) (Nat.add 1024 1)
private theorem rkmStatOk_w64_m16 :
    bAll6 m16B0 m16B1 m16B2 m16B3 m16B4 m16B5 = true := by decide +kernel
private theorem rkmStatOk_m16_p :
    m16B0 = true ∧ m16B1 = true ∧ m16B2 = true ∧ m16B3 = true ∧ m16B4 = true ∧ m16B5 = true :=
  @bAll6_elim m16B0 m16B1 m16B2 m16B3 m16B4 m16B5 rkmStatOk_w64_m16
private theorem hhbMk {b : List ℕ} {s w : ℕ}
    (h : muxIntListEq (uHb b) (altBuildHbFrom 1856 1024 s w (1024 - w)) = true) :
    uHb b = rkmDropInts w (altBuildHbFrom 1856 1024 s 0 1024) :=
  ((@muxIntListEq_eq_true _ _).mp h).trans (drHb 1856 1024 s w 1024)
private theorem hhbT_s5 : uHb phb_s5 = rkmDropInts 799 rkmHbWin_w64_m16_s5a :=
  hhbMk rkmStatOk_m16_p.1
private theorem hhbT_s6 : uHb phb_s6 = rkmDropInts 580 hb_s6 := hhbMk rkmStatOk_m16_p.2.1
private theorem hhbT_s7 : uHb phb_s7 = rkmDropInts 508 hb_s7 := hhbMk rkmStatOk_m16_p.2.2.1
private theorem rkmBleHi_w64_m16_s4 : m16B3 = true := rkmStatOk_m16_p.2.2.2.1
private theorem rkmEqXs_w64_m16_s4 : m16B4 = true := rkmStatOk_m16_p.2.2.2.2.1
private theorem rkmBleHi_w64_m16_s5 : m16B5 = true := rkmStatOk_m16_p.2.2.2.2.2
private theorem rkmWC_w64_m16_s5b_0 : bWCI 799 22 100000000 1024 phb_s5
    815 rkmXsWin_w64_m16_s5a_out 829 c5_1 3455081646 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5b_1 : bWCU 799 21 100000000 1024 phb_s5
    829 c5_1 844 u5_o 3725943784 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_0 : bWCI 580 27 100000000 1024 phb_s6
    844 xi_s6 841 c6_1 3276659926 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_1 : bWCU 580 23 100000000 1024 phb_s6
    841 c6_1 818 c6_2 2093427033 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_2 : bWCU 580 20 100000000 1024 phb_s6
    818 c6_2 797 c6_3 2442371234 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_3 : bWCU 580 18 100000000 1024 phb_s6
    797 c6_3 777 c6_4 2082833291 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_4 : bWCU 580 17 100000000 1024 phb_s6
    777 c6_4 758 c6_5 2003846479 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_5 : bWCU 580 16 100000000 1024 phb_s6
    758 c6_5 739 c6_6 1744655223 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_6 : bWCU 580 15 100000000 1024 phb_s6
    739 c6_6 720 c6_7 1532112591 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_7 : bWCU 580 14 100000000 1024 phb_s6
    720 c6_7 703 c6_8 1451138123 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_8 : bWCU 580 13 100000000 1024 phb_s6
    703 c6_8 686 c6_9 1288455303 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_9 : bWCU 580 13 100000000 1024 phb_s6
    686 c6_9 669 c6_10 1149458610 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_10 : bWCU 580 12 100000000 1024 phb_s6
    669 c6_10 653 c6_11 778272039 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_11 : bWCU 580 12 100000000 1024 phb_s6
    653 c6_11 637 c6_12 817002024 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_12 : bWCU 580 11 100000000 1024 phb_s6
    637 c6_12 622 c6_13 738133014 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_13 : bWCU 580 10 100000000 1024 phb_s6
    622 c6_13 608 c6_14 631555821 = true := by decide +kernel
private theorem rkmWC_w64_m16_s6_14 : bWCU 580 10 100000000 1024 phb_s6
    608 c6_14 594 u6_o 634344592 = true := by decide +kernel
private theorem rkmWC_w64_m16_s7_0 : bWCI 508 10 100000000 1024 phb_s7
    594 xi_s7 580 c7_1 653692707 = true := by decide +kernel
private theorem rkmWC_w64_m16_s7_1 : bWCU 508 10 100000000 1024 phb_s7
    580 c7_1 566 c7_2 672488721 = true := by decide +kernel
private theorem rkmWC_w64_m16_s7_2 : bWCU 508 10 100000000 1024 phb_s7
    566 c7_2 552 c7_3 645554991 = true := by decide +kernel
private theorem rkmWC_w64_m16_s7_3 : bWCU 508 10 100000000 1024 phb_s7
    552 c7_3 537 c7_4 611716568 = true := by decide +kernel
private theorem rkmWC_w64_m16_s7_4 : bWCU 508 10 100000000 1024 phb_s7
    537 c7_4 523 u7_o 642421104 = true := by decide +kernel
private theorem rkmRowOk_w64_m16 :
    rkmCheckRowFromWinWalks 16 512 1024 [4, 8, 16, 32, 64, 116, 116, 116]
      [4333381, 3920635, 6415160, 6046259, 7528059, 5307913, 4524812, 976442]
      [12, 21, 66, 117, 254, 271, 231, 50]
      rkmMasksHi_w64_m16_r1024 rkmWalksHi_w64_m16_r1024 rkmRowHi_w64_m16_r1024
      = true := by decide +kernel
private theorem rkmWinIterSnd_w64_m16_s5b :
    RkmWinIterSound 43 1024 rkmHbWin_w64_m16_s5a 815 rkmXsWin_w64_m16_s5a_out
      844 xo_s5b 7181025430 :=
  bChU 43 7181025430 (bWCI_s hhbT_s5 rkmWC_w64_m16_s5b_0) hhbT_s5 rkmWC_w64_m16_s5b_1 rfl rfl
private theorem rkmWinIter_w64_m16_s6 :
    RkmWinIterSound 231 1024 hb_s6 844 xi_s6
      594 xo_s6 22664265303 :=
  bChU 231 22664265303 (bChU 221 22029920711 (bChU 211 21398364890 (bChU 200 20660231876 (bChU
    188 19843229852 (bChU 176 19064957813 (bChU 163 17915499203 (bChU 150 16627043900 (bChU 136
    15175905777 (bChU 121 13643793186 (bChU 105 11899137963 (bChU 88 9895291484 (bChU 70
    7812458193 (bChU 50 5370086959 (bWCI_s hhbT_s6 rkmWC_w64_m16_s6_0) hhbT_s6 rkmWC_w64_m16_s6_1
    rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_2 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_3 rfl rfl) hhbT_s6
    rkmWC_w64_m16_s6_4 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_5 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_6
    rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_7 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_8 rfl rfl) hhbT_s6
    rkmWC_w64_m16_s6_9 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_10 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_11
    rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_12 rfl rfl) hhbT_s6 rkmWC_w64_m16_s6_13 rfl rfl) hhbT_s6
    rkmWC_w64_m16_s6_14 rfl rfl
private theorem rkmWinIter_w64_m16_s7 :
    RkmWinIterSound 50 1024 hb_s7 594 xi_s7
      523 xo_s7 3225874091 :=
  bChU 50 3225874091 (bChU 40 2583452987 (bChU 30 1971736419 (bChU 20 1326181428 (bWCI_s hhbT_s7
    rkmWC_w64_m16_s7_0) hhbT_s7 rkmWC_w64_m16_s7_1 rfl rfl) hhbT_s7 rkmWC_w64_m16_s7_2 rfl rfl)
    hhbT_s7 rkmWC_w64_m16_s7_3 rfl rfl) hhbT_s7 rkmWC_w64_m16_s7_4 rfl rfl
private theorem rkmWinChain_w64_m16_s4_full :
    RkmWinIterSound 254 1024 rkmHbWin_w64_m16_s4a 222 rkmXsWin_w64_m16_s4a_in
      580 rkmXsWin_w64_m16_s4b_out 49167225065 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w64_m16_s4a) (hb2 := rkmHbWin_w64_m16_s4b)
    (x1 := rkmXsWin_w64_m16_s4a_out) (x1' := rkmXsWin_w64_m16_s4b_in) rfl rfl
    (muxIntListEq_eq_true.mpr rfl) rfl rkmEqXs_w64_m16_s4
    rkmWinIterSnd_w64_m16_s4a rkmWinIterSnd_w64_m16_s4b
private theorem rkmWinSegWalkSnd_w64_m16_s4 :
    RkmWinSegWalkSound 254 ⟨1024, rkmHbWin_w64_m16_s4a, 222, rkmXsWin_w64_m16_s4a_in,
      580, rkmXsWin_w64_m16_s4b_out, 49167225065⟩ :=
  @swMk 254 1024 222 580 49167225065
    rkmHbWin_w64_m16_s4a rkmXsWin_w64_m16_s4a_in rkmXsWin_w64_m16_s4b_out
    (rkmw_buildHbFrom_length 1024 1024 29638027559 1024 0)
    rkmBleHi_w64_m16_s4 rkmWinChain_w64_m16_s4_full
private theorem rkmWinChain_w64_m16_s5_full :
    RkmWinIterSound 271 1024 rkmHbWin_w64_m16_s5a 580 rkmXsWin_w64_m16_s5a_in
      844 xo_s5b 47498279950 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w64_m16_s5a) (hb2 := rkmHbWin_w64_m16_s5a)
    (x1 := rkmXsWin_w64_m16_s5a_out) (x1' := rkmXsWin_w64_m16_s5a_out) rfl rfl
    (muxIntListEq_eq_true.mpr rfl) rfl (muxIntListEq_eq_true.mpr rfl)
    rkmWinIterSnd_w64_m16_s5a rkmWinIterSnd_w64_m16_s5b
private theorem rkmWinSegWalkSnd_w64_m16_s5 :
    RkmWinSegWalkSound 271 ⟨1024, rkmHbWin_w64_m16_s5a, 580, rkmXsWin_w64_m16_s5a_in,
      844, xo_s5b, 47498279950⟩ :=
  @swMk 271 1024 580 844 47498279950
    rkmHbWin_w64_m16_s5a rkmXsWin_w64_m16_s5a_in xo_s5b
    (rkmw_buildHbFrom_length 1856 1024 19586394833 1024 0)
    rkmBleHi_w64_m16_s5 rkmWinChain_w64_m16_s5_full
private theorem rkmWinSegWalkSnd_w64_m16_s6 :
    RkmWinSegWalkSound 231 ⟨1024, hb_s6, 844, xi_s6, 594, xo_s6, 22664265303⟩ :=
  swMkM (drB 844 rkmMkHi_w64_m16_s5) rkmWinSegWalkSnd_w64_m16_s5
    rkmWinIter_w64_m16_s6 (rkmw_buildHbFrom_length 1856 1024 19587930735 1024 0) rfl
private theorem rkmWinSegWalkSnd_w64_m16_s7 :
    RkmWinSegWalkSound 50 ⟨1024, hb_s7, 594, xi_s7, 523, xo_s7, 3225874091⟩ :=
  swMkM (drB 594 rkmMkHi_w64_m16_s6) rkmWinSegWalkSnd_w64_m16_s6
    rkmWinIter_w64_m16_s7 (rkmw_buildHbFrom_length 1856 1024 19528840000 1024 0) rfl
private theorem rkmWalksSndHi_w64_m16_r1024 :
    RkmWinSegWalksSound [12, 21, 66, 117, 254, 271, 231, 50] rkmWalksHi_w64_m16_r1024 :=
  ⟨rkmWinSegWalkSnd_w64_m16_s0, ⟨rkmWinSegWalkSnd_w64_m16_s1, ⟨rkmWinSegWalkSnd_w64_m16_s2,
    ⟨rkmWinSegWalkSnd_w64_m16_s3, ⟨rkmWinSegWalkSnd_w64_m16_s4, ⟨rkmWinSegWalkSnd_w64_m16_s5,
    ⟨rkmWinSegWalkSnd_w64_m16_s6, ⟨rkmWinSegWalkSnd_w64_m16_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic `w64_m16` `r = 1024` hit certificate (`m = 16`). -/
theorem rkmTrajHitHi_w64_m16 :
    RkmAnchorHitSound 16 ⟨1024, [4, 8, 16, 32, 64, 116, 116, 116],
      [4333381, 3920635, 6415160, 6046259, 7528059, 5307913, 4524812, 976442],
      [12, 21, 66, 117, 254, 271, 231, 50], rkmMasksHi_w64_m16_r1024, rkmRowHi_w64_m16_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 16 512 1024 [4, 8, 16, 32, 64, 116, 116, 116]
    [4333381, 3920635, 6415160, 6046259, 7528059, 5307913, 4524812, 976442]
    [12, 21, 66, 117, 254, 271, 231, 50]
    rkmMasksHi_w64_m16_r1024 rkmWalksHi_w64_m16_r1024 rkmRowHi_w64_m16_r1024
    rkmWalksSndHi_w64_m16_r1024 rkmRowOk_w64_m16
/-- Cumulative `w64_m16` part `2` lane witness. -/
theorem rkmHiLane_w64_m16_wint2 : @rkmTrajHitHi_w64_m16 = @rkmTrajHitHi_w64_m16 :=
  (And.intro (Eq.refl rkmHiLane_w64_m16_wint1) rfl).right
/-- Module lane witness for `FindAllJohnsonRampKickMuxHiW64T06`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T06 :
    @rkmHiLane_w64_m16_wint2 = @rkmHiLane_w64_m16_wint2 := rfl

end
end QuantumComputation.Specs.DickeSol
