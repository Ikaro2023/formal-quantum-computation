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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T07
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T08

/-
# Caustic `r = 1024` Halo-16 Walk `w64_m32` Part `2` (`FindAllJohnsonRampKickMuxHiW64T09`)

Certifies part `2` of the `w64_m32` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Kick mask `w64_m32` seg `5`. -/
def rkmMkHi_w64_m32_s5 : List Bool := List.replicate 880 false ++ [
  true, false, false, true, true, true, false, false, false, false, false, false, true, true, true,
  true, true, false, false, false, false, false, false, false, true, true, true, true, true, true,
  true]
/-- Kick mask `w64_m32` seg `6`. -/
def rkmMkHi_w64_m32_s6 : List Bool := List.replicate 737 false ++ [
  true, false, false, false, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, true, false,
  false, true, false, false, true, false, true, false, false, true, false, true, false, false,
  true, false, true, true, false, true, false, false, true, false, true, false, false, true, false,
  false, true, false, true, false, false, true, false, false, true, false, true, false, true,
  false, true, false, false, true, false, false, true, false, true, true, false, true, false, true,
  false, true, true, false, true, false, false, true, false, false, true, false, true, false, true,
  false, false, true, false, true, true, false, true, true, false, true, false, false, true, false,
  false, true, false, true, false, true, true, false, false, false, true, false, true, true, false,
  true, true, false, true, true, false, true, true, false, true, true, false, true, true, false,
  true, true, false, true, true, false, false, true, false, false, false, false, false, false,
  true, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false, true,
  true, false, false, false, true, true, false, false, true, false, false, false, false, false,
  true, false, false, true, false, false, false, false, false, true, false, true, false, true,
  true, false, false, false, true, false, false, true, false, true, true, false, true, true, false,
  true, false, false, true, true, false, false, false, false, true, true, false, true, false,
  false, true, true, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, true, false, false, false, true, true, true]
/-- Kick-mask schedule for `w64_m32` `r = 1024`. -/
def rkmMasksHi_w64_m32_r1024 : List (List Bool) := [
  [], [], [], [], [], rkmMkHi_w64_m32_s5, rkmMkHi_w64_m32_s6, []]
/-- Certified `rowLo12` vector for `w64_m32` `r = 1024`. -/
def rkmRowHi_w64_m32_r1024 : List ℕ := List.replicate 565 0 ++ [
  379, 1430, 2791, 4230, 5623, 7017, 8544, 10448, 13088, 16879, 22295, 29882, 40022, 52860, 67976,
  84409, 100432, 113729, 122039, 123248, 116398, 101789, 81134, 57524, 34476, 15594, 3622, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 291, 9938, 31405, 58416, 81201, 89901, 78975, 51108, 18521, 249,
  0, 0, 11698, 57583, 116827, 162140, 172261, 140899, 80950, 21959, 0, 0, 9145, 76529, 176687,
  256723, 269897, 201739, 87500, 5041, 0, 27785, 177521, 363762, 456566, 381148, 182559, 16544, 0,
  76168, 326197, 547563, 553492, 331319, 68917, 0, 49455, 302024, 532236, 522922, 282677, 39079, 0,
  70588, 291128, 420218, 327200, 112082, 0, 1598, 110085, 246583, 255590, 136619, 18016, 0, 2453,
  38085, 51879, 23894, 104, 0, 0, 2512, 2700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3164, 22570,
  27877, 9328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2579, 5362, 0, 0, 97, 3515, 42, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 728, 0, 0, 0, 0, 2408, 5874, 0, 0, 0, 0, 0, 0, 10228, 8205, 0, 0, 0, 3485, 0, 0, 0, 0, 0, 0,
  1683, 0, 0, 1146, 0, 6919, 40965, 723, 0, 0, 0, 0, 0, 0, 0, 0, 72, 3995, 32, 19951, 6707, 0, 0,
  1, 0, 1224, 0, 49678, 0, 308930, 2126, 18030, 100025, 295315, 22164, 283884, 115814, 541036,
  110737, 444093, 8015, 718770, 24933, 453186, 99871, 24518, 146983, 115187, 20321, 0, 9585, 0,
  59824, 137102, 1669, 767429, 37290, 44925, 3661, 197136, 530211, 592, 282052, 801705, 49966, 0,
  70098, 1917537, 4028, 1094270, 1072051, 138703, 196983, 228, 24105, 2615605, 150662, 30002,
  470238, 572206, 7809, 30888, 2764994, 1057245, 562888, 240264, 3380752, 80679, 641442, 1697790,
  0, 14947, 2421496, 439254, 1765309, 308226, 0, 454560, 2144700, 0, 1291678, 844, 1919450,
  9013554, 443241, 611, 563536, 19117, 25228, 0, 625568, 0, 421911, 888037, 54225, 3138625,
  5549668, 2193424, 1102341, 39510, 44438, 75802, 0, 1048084, 0, 173814, 2392928, 626599, 2915608,
  7899874, 22503, 512548, 713251, 418973, 1213525, 1860759, 776554, 15284522, 2860235, 34574417,
  21939529, 25486388, 1034771, 0, 4994539, 15457066, 2057234, 19978140, 120876, 289058, 1588497,
  1391567, 3309368, 6878282, 9473004, 3136418, 990654, 4995063, 907564, 4147465, 30872923, 1852609,
  314425, 25687318, 16863068, 38387914, 2346256, 13400563, 741824, 10570234, 33906, 11661653,
  1267620, 44940583, 56196867, 105845603, 6964731, 1432921, 73477742, 11505110, 654204, 27977939,
  6687862, 619392, 7807, 19162147, 31106526, 12148660, 2671278, 57836, 33277287, 91441595,
  54142650, 5847726, 1035174, 5965312, 970140, 291153, 3284177, 1447631, 523356, 43589388, 2252755,
  12737641, 1237475, 800, 5282303, 4686055, 21663645, 1477619, 92338343, 58342344, 21252357,
  2191259, 6810788, 8587077, 77567, 64839, 817698, 1554770, 2388513, 238835921, 37215054, 46584774,
  1653105, 281675, 13772663, 1979743, 1012, 379920, 0, 723646, 28603225, 90059328, 76472518,
  156977142, 11947772, 82502919, 3695736, 46057719, 519737392, 151835808, 40216137, 556818052,
  457163653, 790748450, 1058933402, 183455538, 446932680, 847133547, 2708173959, 2036348065,
  170677, 5925285380, 2334230135, 38893762, 3378013, 312455202, 3053455, 3314531696, 5104946755,
  378855296, 663049080, 905160211, 1745032771, 2040795184, 676606224, 7928051688, 996656530,
  1188430348, 6555532700, 14094691616, 36081742095, 13157493787, 24967110328, 858681712687]

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
private theorem pzig_len : ∀ (ws : List ℕ), (pzig ws).length = ws.length
  | [] => rfl
  | _ :: ws => by dsimp only [pzig]; simp only [List.length_cons, pzig_len ws]
private theorem pzig1_len (ws : List ℕ) (n : ℕ) (h : ws.length = n) :
    (pzigCat [ws]).length = n := by
  dsimp only [pzigCat]; rw [List.append_nil, pzig_len ws, h]
private theorem rkmLenApp (n1 n2 nT : ℕ) {a b : List ℤ}
    (h1 : a.length = n1) (h2 : b.length = n2) (ht : n1 + n2 = nT) :
    (a ++ b).length = nT := by rw [List.length_append, h1, h2, ht]
private theorem rkmSegWalk_mkHi {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d) (hin : offIn + xsIn.length ≤ d + 1)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ :=
  ⟨hhb, hin, (hiter hhb hin).1, (hiter hhb hin).2⟩
private def rkmHbWin_w64_m32_s7 : List ℤ := altBuildHbFrom 1856 1024 19398096153 0 1024
private def rkmXsWin_w64_m32_s6b_in : List ℤ := pzigCat
  [
   [463578026,1408838451,3094471716,5547985355,8538288986,12751396819,17999043836,24400912657,
    32380388160,42138127371,53816890128,67806672167,84149183946,102842109619,124241950146,
    147815532157,173304972710,200057397843,226993629678,253104240603,276852694446,296146173963,
    309522508202,314704057411,309873130552,293810931787,265279142996,224027899629,171258196228,
    108262977221,37903487228,36111389602,109696237185,178765471368,239241246101,288596823936,
    325616656503,350797846488,367226158673,379276755544,392931848163,414675783302,450165335535,
    503086632462,575062526031,663848493530,764007542371,867999999336,965952157975,1048500431822,
    1107969384029,1138815829512,1138896151749,1109572675698,1053616759167,974704834168,
    875709965193,757682181584,620007098981,462530290330,286306588043,97209479048,92321097300,
    264053025689,395228760386,462450775657,447656142380,343581683359,155798772364,95458815332,
    379111964711,659436449456,901983323123,1078671448038,1170415193997,1165489923928,
    1055434262543,834209572608,498658619627,55262063600,468856669986,1015694469711,1494565434906,
    1792652377767,1800176186232,1448383176479,745678907610,201001104552,1193215328629,
    1980988154828,2332863875081,2112326727862,1334754174659,183628433378,1030486349256,
    1958833394193,2325331821216,2019553064915,1139454041520,35567177388,1136100070921,
    1826126747190,1913384232331,1408997246092,515400641869,451899874411,1178545828782,
    1455525754873,1240542722034,657214443735,61218606693,662064598812,962441392907,904553719886,
    562391842673,98886884368,305170826122,523513885999,526850240712,377024337059,178898159984,
    16412606115,90014037499,176939659790,287002860849,407361440762,450144045515,301314055434,
    79781955770,577687370745,931632483916,865926919145,282920214118,606051847098,1329988368611,
    1402901832968,646502074075,620462088479,1689610932194,1857129179485],
   [891336707692,736381605982,2059542357679,2191438386878,929045046805,1028791599103,
    2451271475156,2353646047721,691735698946,1520722552106,2818785782503,2262862283602,
    134690804475,2169843908779,3048077439138,1815597097437,743220270609,2848356906624,
    2958828456631,917933403246,1851164657150,3316720216015,2333829593910,437299331224,
    2938522300903,3230361199200,1012857957861,2050552330931,3551826842848,2234466820987,
    924325831607,3394640647298,3107225501435,212134870828,2925638732600,3629504989887,
    1211309014722,2315943036166,3870799304265,2003448705484,1704616679680,3926222957111,
    2574352060454,1187100245844,3885361089417,2940622745132,816732526376,3814794563263,
    3129953614366,613223352762,3754427042301,3171292644776,571828361512,3721698619995,
    3092917374072,674533300694,3724993116835,2920653671606,906596230978,3774595015635,
    2667633378328,1276874002534,3881586475317,2307896935712,1827537761080,4024441217565,
    1744202021554,2603805276424,4084392676349,812049184104,3559631675616,3793510236779,
    620148662309,4424705830324,2790564690013,2439669690991,4659494817782,877658951079,
    4088520548933,3681884105258,1597686305748,4659467174401,1408876550730,3599532219904,
    3514906018187,1277211364819,3966914751706,1109181260647,2877691042947,2558096406362,
    992491526468,2645573230929,753911037366,1569798006446,1642155091743,58461150302,
    1385264139150,1522152589723,132967092965,2258618684500,1673263594069,1997351905157,
    3496797687430,768259026960,4873548186239,1179261853236,5510337499210,3492489486141,
    5308441580893,5823978871598,4332529423540,7905606489817,2752118214963,9582734097370,
    781496004994,10814886620053,1366888248944,11655103621312,3509503424519,12218971930473,
    5500346048598,12652209486322,7226623473805,13102028979279,8597978667250,13695529468968,
    9535282465937,14525046076551,9959838192148,15641257350960,9783918771483,17048096571537,
    8898328982064,18694060417656,7161723071009,20446306305273,4400427616108,22044026018616,
    443301088067,23041646084353],
   [4784474915979,22780826463424,11103024566108,20447836827231,17893032492317,15267451203982,
    23962304245768,6833349969535,27566366894917,4473561764825,26655159612284,17061995730988,
    19424216531615,27810758127803,5311069882010,32190374724848,13522854074688,25540020393177,
    30873215444621,6149519125946,37153247414536,20746371285144,23935657023037,41368701102315,
    8265221681087,38047156499478,43165157283572,1945660042661,50121853342039,48393614377575,
    6011501836304,61521183213126,62001979178644,763888768462,71259181936597,88713955554165,
    27481417722625,73412329968242,139438298151182,114777706335334,3105372772966,131686702479011,
    202167152330323,145829848492501,43501584374794,315805455600756,591370326061010,
    796064769152388,887479443443774,862836577174220,750267015298450,591773559023590,
    426965779120260,283192148092642,173124515708468,97630368091790,50750831629558,24263037366452,
    10625763446836,4236474092568,1523460098200,487115682572,134979651812,30664079076,4764988868]]
private def rkmXsWin_w64_m32_s6b_out : List ℤ := pzigCat
  [
   [266651048,957694387,2395933032,4165623303,6692703034,9969792615,13896812346,18752654309,
    24609549374,31469601845,39632997602,49039194021,60128117346,72739731091,86958265736,
    103076922821,120575249818,139610159697,159865808742,180873898939,202123292930,222842253483,
    242224931188,259335917521,272791112650,281806528115,284846272360,280810006631,269087122046,
    248670049241,219351818016,181007681973,134348794472,80553452457,21021684308,42090470246,
    106308367555,169448209396,228618131313,281941685726,327825047457,365308853134,394762602065,
    417117817800,434846330159,450832093374,468452773097,491528404060,523162740209,565557828848,
    619974924933,685230020594,759186456257,837414469784,914032601107,983027459716,1037413281257,
    1071297268678,1080304292293,1061578544056,1014662749531,941432141688,845025152567,
    730460850404,602918730665,467792803412,330008480885,193756205092,63023839115,57975988123,
    164718945620,250980833043,310029232432,334061840587,315425903332,248817887937,132342413154,
    30506015374,229175698243,447548412248,663253221071,851020652396,986018521303,1046585418356,
    1018597401531,897175122280,687362895145,404412569566,71657370759,282428940861,625657347878,
    925822614573,1151674635034,1274692944053,1271759033414,1127703317569,839257892038,
    420950599253,92204935485,642223937324,1151386528081,1531897807698,1700636556809,
    1598149400464,1208329548207,570245128776,218415925846,1013571896299,1651443309086,
    1984055968999,1917142141178,1440801503837,640001906382,316469053572,1211788679023,
    1833255637166,2027009565957,1741256523968,1044954868807,112518080942,819038334400,
    1513463564609,1799820076162,1618119706793,1034621515054,222118974295,592549127703,
    1192989920138,1433392044659,1276479559310,797096003515,152985930908,465348866940,
    892756677069,1033574981172,882009085665,514827685768,59638939077,348504938219,605651830792],
   [665537376171,544400543520,305794922761,33920392280,194618282354,333118885001,371400519310,
    328904293793,238703306482,129725076501,15562057748,102233823090,223019037637,332272507646,
    393808590139,359720150380,196189619729,87072217285,416983363752,668317506349,708383579546,
    462525119473,30585940187,604490191540,1014388619083,1040254347732,601026137047,175845966357,
    976076482730,1421909755345,1251508307852,468093729901,620522209193,1514620612682,
    1752297876917,1150745513428,67528328648,1343142049117,2034121190122,1742683633913,
    547162736756,997285972930,2110486601095,2184107416044,1119974805639,579421256475,
    2042042887494,2473867263943,1595470062974,173303405492,1904245007345,2646391310778,
    1954701835059,163551915568,1763399901642,2747962911793,2204843683230,398426511231,
    1672493821737,2821896396368,2358983569567,512600606082,1667038841872,2898678349023,
    2426163872982,492307413427,1769266128987,2991335947888,2401881065687,323337740734,
    1987344457156,3090272092065,2263691762248,10878641332,2312222362917,3159262175384,
    1970573960371,522565264125,2708434084220,3131072605697,1469079725810,1205353494070,
    3101479784637,2907356429066,710619891891,2009294719075,3364232394916,2371793373549,
    313853560571,2809913672634,3317700909573,1430318049106,1520798151440,3387313231783,
    2769450818776,85692680295,2684600479289,3452208397146,1606254540933,1475817226041,
    3438742852136,2752534591415,73854168781,2846861300624,3385023702751,1249475361738,
    1875744828352,3497796726047,2309844898560,736855936916,3176001055147,3020077495406,
    393007663083,2549005968351,3375151108722,1393418230633,1751828415105,3425314567506,
    2203429745763,900091546347,3249807447134,2811052258597,79396165889,2936513741096,
    3237532174257,654140334932,2567293776506,3522750461461,1268665760732,2212353517308,
    3710480092997,1747066363690,1925935573940,3837952169279,2078815507486,1746195984096,
    3927685150221,2254033670128,1693111438328,3982668610279],
   [2262218789136,1765195365714,3984321658733,2096603926600,1935100400184,3896570637759,
    1763888447738,2146737301390,3677838678087,1298481628520,2319402227582,3301728129289,
    774545609134,2363298475194,2784921234429,307339507470,2213384150032,2212231210183,
    29886850598,1876144425002,1741070856981,38948772054,1472063143932,1564156201061,316492924862,
    1243150508638,1816876951769,659691606966,1484949256698,2446693093893,675833881032,
    2390377487586,3104467506891,95923446297,3837865544494,3154647278903,1921762895205,
    5235227766498,1895993800395,4542881291657,5578420230212,1003390634438,6975624589917,
    3851467629240,5019223372374,7692061814041,282283360797,8567923892798,5319650151071,
    5819675121417,9436617257730,328078072422,10308862099305,5925504800060,7439145258814,
    10697211814217,1692057061119,12318517325060,5125373329891,10213092049739,10953508249370,
    4966973792060,14147161082633,1987220871834,13899873080008,8885037181997,10344986659657,
    14143759101410,4375706196114,16722570775499,2696989285082,16266440348548,9514800586043,
    13051559650305,14966393091886,7798809228274,18355012306061,1436901951115,19434106777704,
    5115047015925,18343527260181,11104119254170,15488246549272,16023804696975,11405530605483,
    19628491130268,6648265142864,21899141437711,1701366600375,22983805343888,3062950098677,
    23133128700103,7398947329144,22643894636138,11177432569491,21816814762143,14360593455328,
    20933190362740,16972002443495,20244350153399,19062350189456,19973507066162,20676249692187,
    20320918095617,21817115026716,21468513447954,22412998261195,23573046340149,22280935471146,
    26743809275534,21096340484895,30996518233699,18370739721610,36180132471060,13445475805995,
    41864640410473,5511181957888,47167322410708,6305708296106,50485484689571,22678287490755,
    49149738198350,43424492579600,39205619708589,66222949861369,15912106583702,84808570497706,
    24154288057644,87556739676547,78776270148161,58141068723462,133594221328184,19454661381900,
    153268699625555,144662817826607,75607440346402,256240284277988,148746850250270,
    185032086329285,404294430891357],
   [225059807376033,303868794248332,853559138336318,1105825502595922,984270675513080,
    646248619645334,308764781295306,95324697184258]]
private def rkmXsWin_w64_m32_s7_in_p0 : List ℤ := pzigCat
  [
   [266651048,957694387,2395933032,4165623303,6692703034,9969792615,13896812346,18752654309,
    24609549374,31469601845,39632997602,49039194021,60128117346,72739731091,86958265736,
    103076922821,120575249818,139610159697,159865808742,180873898939,202123292930,222842253483,
    242224931188,259335917521,272791112650,281806528115,284846272360,280810006631,269087122046,
    248670049241,219351818016,181007681973,134348794472,80553452457,21021684308,42090470246,
    106308367555,169448209396,228618131313,281941685726,327825047457,365308853134,394762602065,
    417117817800,434846330159,450832093374,468452773097,491528404060,523162740209,565557828848,
    619974924933,685230020594,759186456257,837414469784,914032601107,983027459716,1037413281257,
    1071297268678,1080304292293,1061578544056,1014662749531,941432141688,845025152567,
    730460850404,602918730665,467792803412,330008480885,193756205092,63023839115,57975988123,
    164718945620,250980833043,310029232432,334061840587,315425903332,248817887937,132342413154,
    30506015374,229175698243,447548412248,663253221071,851020652396,986018521303,1046585418356,
    1018597401531,897175122280,687362895145]]
private def rkmXsWin_w64_m32_s7_in_p1 : List ℤ := pzigCat
  [
   [404412569566,71657370759,282428940861,625657347878,925822614573,1151674635034,1274692944053,
    1271759033414,1127703317569,839257892038,420950599253,92204935485,642223937324,1151386528081,
    1531897807698,1700636556809,1598149400464,1208329548207,570245128776,218415925846,
    1013571896299,1651443309086,1984055968999,1917142141178,1440801503837,640001906382,
    316469053572,1211788679023,1833255637166,2027009565957,1741256523968,1044954868807,
    112518080942,819038334400,1513463564609,1799820076162,1618119706793,1034621515054,
    222118974295,592549127703,1192989920138,1433392044659,1276479559310,797096003515,
    152985930908,465348866940,892756677069,1033574981172,882009085665,514827685768,59638939077,
    348504938219,605651830792,665537376172,544400543520,305794922761,33920392280,194618282354,
    333118885002,371400519310,328904293793,238703306482,129725076501,15562057748,102233823090,
    223019037637,332272507646,393808590139,359720150380,196189619729,87072217285,416983363752,
    668317506349,708383579546,462525119473,30585940187,604490191540,1014388619084,1040254347732,
    601026137048,175845966357,976076482730,1421909755346,1251508307852,468093729901,620522209194,
    1514620612682]]
private def rkmXsWin_w64_m32_s7_in_p2 : List ℤ := pzigCat
  [
   [1752297876918,1150745513428,67528328648,1343142049118,2034121190122,1742683633914,
    547162736756,997285972930,2110486601096,2184107416044,1119974805640,579421256476,
    2042042887494,2473867263944,1595470062974,173303405492,1904245007346,2646391310778,
    1954701835060,163551915568,1763399901642,2747962911794,2204843683230,398426511231,
    1672493821738,2821896396368,2358983569568,512600606082,1667038841872,2898678349024,
    2426163872982,492307413427,1769266128988,2991335947888,2401881065688,323337740734,
    1987344457155,3090272092065,2263691762247,10878641332,2312222362917,3159262175383,
    1970573960371,522565264125,2708434084219,3131072605697,1469079725809,1205353494069,
    3101479784637,2907356429065,710619891891,2009294719076,3364232394916,2371793373550,
    313853560572,2809913672634,3317700909574,1430318049106,1520798151440,3387313231784,
    2769450818776,85692680295,2684600479290,3452208397146,1606254540934,1475817226041,
    3438742852135,2752534591415,73854168781,2846861300623,3385023702751,1249475361737,
    1875744828351,3497796726047,2309844898559,736855936915,3176001055147,3020077495405,
    393007663083,2549005968351,3375151108721,1393418230633,1751828415105,3425314567505,
    2203429745763,900091546348,3249807447134]]
private def rkmXsWin_w64_m32_s7_in_p3 : List ℤ := pzigCat
  [
   [2811052258598,79396165890,2936513741096,3237532174257,654140334932,2567293776505,
    3522750461461,1268665760731,2212353517307,3710480092997,1747066363689,1925935573939,
    3837952169279,2078815507485,1746195984095,3927685150221,2254033670127,1693111438327,
    3982668610279,2262218789135,1765195365713,3984321658733,2096603926599,1935100400183,
    3896570637759,1763888447737,2146737301389,3677838678087,1298481628519,2319402227581,
    3301728129289,774545609134,2363298475193,2784921234429,307339507470,2213384150032,
    2212231210183,29886850598,1876144425002,1741070856982,38948772054,1472063143931,
    1564156201061,316492924862,1243150508638,1816876951769,659691606966,1484949256698,
    2446693093893,675833881032,2390377487586,3104467506891,95923446297,3837865544494,
    3154647278903,1921762895205,5235227766498,1895993800395,4542881291657,5578420230212,
    1003390634438,6975624589917,3851467629240,5019223372373,7692061814041,282283360797,
    8567923892797,5319650151072,5819675121417,9436617257730,328078072422,10308862099306,
    5925504800059,7439145258814,10697211814217,1692057061120,12318517325060,5125373329891,
    10213092049739,10953508249370,4966973792060,14147161082634,1987220871834,13899873080008,
    8885037181998,10344986659657,14143759101410]]
private def rkmXsWin_w64_m32_s7_in_p4 : List ℤ := pzigCat
  [
   [4375706196114,16722570775499,2696989285082,16266440348547,9514800586043,13051559650306,
    14966393091886,7798809228273,18355012306062,1436901951115,19434106777704,5115047015925,
    18343527260182,11104119254170,15488246549272,16023804696976,11405530605483,19628491130267,
    6648265142863,21899141437711,1701366600376,22983805343887,3062950098677,23133128700104,
    7398947329144,22643894636138,11177432569492,21816814762144,14360593455328,20933190362740,
    16972002443495,20244350153399,19062350189455,19973507066161,20676249692187,20320918095618,
    21817115026716,21468513447954,22412998261196,23573046340150,22280935471146,26743809275533,
    21096340484895,30996518233699,18370739721610,36180132471060,13445475805995,41864640410473,
    5511181957888,47167322410708,6305708296106,50485484689571,22678287490755,49149738198350,
    43424492579600,39205619708589,66222949861369,15912106583702,84808570497706,24154288057644,
    87556739676547,78776270148161,58141068723462,133594221328184,19454661381900,153268699625556,
    144662817826608,75607440346402,256240284277988,148746850250270,185032086329286,
    404294430891358,225059807376034,303868794248332,853559138336318,1105825502595922,
    984270675513080,646248619645334,308764781295306,95324697184258]]
private def rkmXsWin_w64_m32_s7_in : List ℤ :=
  rkmXsWin_w64_m32_s7_in_p0 ++ (rkmXsWin_w64_m32_s7_in_p1 ++ (rkmXsWin_w64_m32_s7_in_p2 ++
    (rkmXsWin_w64_m32_s7_in_p3 ++ rkmXsWin_w64_m32_s7_in_p4)))
private def rkmXsWin_w64_m32_s7_out : List ℤ := pzigCat
  [
   [424856714,1191390625,2493299350,4421262357,6864020550,10062948629,13782310328,18272868987,
    23562232268,29710434845,36983118502,45162209381,54583400464,65192485213,77133697178,
    90484677869,104937682486,120757062993,137563171832,155212969173,173354803428,191541083351,
    209499415660,226078476329,240952751460,253290827555,262039474600,266608160955,265745734914,
    259013288665,245748860676,225318505181,197568102652,162566086139,120643700934,72694965647,
    19603960796,36986246776,95711077237,154591987824,211737962423,265754599440,314708688017,
    357842433528,394491981417,424529351996,448925723015,468826554498,486380532847,503718258550,
    523282934185,547654495830,578686278489,617476377188,664570213169,718950702038,778663689969,
    840283104612,899904024129,952656749428,993312838527,1017519743604,1020970791031,
    1001180093194,956924874785,888520521746,798524117331,690198122564,568593708833,439229100202,
    307756046979,180022330942,60707250727,45607046057,135205586388,205229339849,252699616304,
    275058279821,270387148498,236378119933,172034479186,77294948721,45532009121,191603892696,
    353044765651,518226301964,673270431709,802228739040,888754775535,918506659586,880889260553,
    770981169766,591029753921,350475737540,66844600379,237268621371,535158480310,798770476647,
    1002435782694,1124168852699,1148924650920,1069568668335,887872757830,615214554307,
    271273654914,115657402128,510104060979,872117115716,1159520816641,1332193062408,
    1357867927309,1217144800420,910445223837,460857701874,83465699074,652218908545,1161501161512,
    1525088629817,1670229261542,1553578678601,1173375949418,576094446389,146585491647,
    870807834642,1461108791573,1798785829848,1806775602461,1470042622832,843879060183,
    46216521576,763611375816,1417970797641,1777925661778,1765101623067,1382183969248,
    714207681109,90011352051,850207833074,1397960636621,1615319711524],
   [1462862908225,988410256678,313206806851,398813698543,982419836500,1311979492409,
    1329954716544,1058076607709,587295157284,49479331171,417919137709,709150593582,774381031685,
    627994248208,339356560383,7839716156,268133648330,419111195287,422786817370,305226270153,
    126924118628,41856343056,148936719081,177434078070,149679020801,110855949452,101151404581,
    130366787800,166818378553,151975704808,37482137881,177796685191,431359903888,619311037955,
    652770468516,512010346753,265219541756,29744357387,101554984771,114776833616,67178120193,
    22148915858,15698696114,96808242961,252103154364,420427281237,465305071474,292719289645,
    38935364173,338712348622,437440285833,331994354284,168504872415,80230544698,67515818929,
    49454739568,1635860538,36017188641,42748962078,103350690397,257484622958,372858098659,
    277025595032,31658844979,68423640533,133477819399,417013392812,472139551773,320195406162,
    223311884245,244516551438,215533797033,149835769352,272579999943,521117882916,500015350167,
    171626135280,37713262589,291767625476,436933849035,201278006968,47726590529,220524418258,
    252702153721,23443650886,89348800561,400913401694,217458941225,320328857649,386574640466,
    210095592045,485209296950,723636597591,372658569358,74627719907,117373804908,9062201676,
    38606875657,262100727419,121549754684,182361635014,241772235848,336001030967,445275325399,
    330433941148,601337821714,482640260713,95205397037,60146325601,322223193958,133840745165,
    388857700257,234482674072,764613075238,104567934399,1430464500991,411087994058,587396570614,
    951372283366,1405693965561,616594436177,1384451883732,999466191782,1789937864345,
    984382428269,1651641324018,497898984478,2014441018829,634649013820,1665217480892,
    950886132005,632009406057,1085604322178,997623012524,603945405499,155179422468,514654361012,
    166502498737,808019963948,1059382305237],
   [400576465959,2070895088070,705055170071,742750354883,439864937584,1206836917184,
    1775147513433,367562037366,1381007473489,2109594557704,765903616303,101505909479,
    848359950437,3088337366154,445797049194,2410982312379,2389632611212,1063695435952,
    1206491429750,349127846181,629360587333,3553400352078,1095141524300,665262403113,
    1690313327038,1831721217018,495588480824,670341260118,3644488457170,2375283254960,
    1819351914711,1299170550286,3996198261148,886918583714,1920637022168,2924819382676,
    314791162885,563365038020,3431065331680,1644360544192,2976132998908,1429198141386,
    70020177140,1667256989222,3247793160342,2298445309,2591874560376,377003339600,3089718788378,
    6323349970530,1650362991340,368312057822,1820215854566,595370185181,636508593503,
    127757899272,1900692629047,25563456409,1617928438577,2203548971421,784562791759,
    3862067034499,5030380298429,3280876562077,2418682938225,716383832437,740448062814,
    869481159953,99210680185,2366353871846,78078459614,1152657682292,3412652339340,1901995740496,
    3733864402482,5940176596194,618862779806,1750684140768,2007919125240,1613398344613,
    2522036416028,3047026793461,2081281070386,8137918341117,3701280212922,12078836274421,
    9686763611096,10415642536437,2353308925842,143442912453,4788527013485,8181928735147,
    3187446762940,9258216160757,1014181468137,1394117683416,2839546496775,2678128325932,
    3957167635292,5564129491135,6474482937578,3860821197175,2309466342268,4788761568177,
    2224157542653,4391899203524,11431515130467,3041046127026,1440307658365,10455365070199,
    8531766755274,12710429585293,3382332781800,7640189583307,2041419050640,6821212756603,
    687112748466,7148666246895,2570606932834,13726381042567,15311747250640,20895091831865,
    5596989214004,2712928276650,17462665113213,7102670388876,1936492192162,10897668668021,
    5491014007290,1892864118644,495563828980,9073751397851,11473478337886,7289819289789,
    3587642957264,799823180968,11856127266381,19443853112730,15035171221207,5155248232172],
   [2353704211315,5203631355686,2288748163487,1398008697341,3943293762757,2725184802546,
    1765701871661,13523285364236,3320670142333,7456799938767,2543671724429,375463991154,
    4915486213419,4648293206259,9627677763471,2749981785008,19537401771684,15595265434149,
    9538889248256,3279414879597,5538330885066,6179576745941,875855264343,828110167896,
    2127368183946,2812642900358,3409796989228,31227467721318,12519661895394,13969441275155,
    2890297199336,1380296769459,7741141295053,3132900813528,382488939573,1551589335525,
    198206943243,2020182591523,11015229979632,19298752009070,17808546702766,25376937162302,
    7231943507842,18485056831371,4163693361493,13892000937196,45914332683743,24963167987603,
    13002072338608,47512818130982,43081604610371,56559332878032,65401347088136,27407985240145,
    42600398058403,58529950614233,104399070703314,90570660137065,1145098485240,154270583829002,
    96946575309499,12791806122836,3994708423988,35671638061438,3813661660019,115462772632181,
    143216653409774,39247244289949,51818312065253,60490594405704,83866012005647,90669155498542,
    52342144337074,178398048032551,63458568117986,69266069511848,162251321606467,237760966072838,
    380222726804126,229731071641219,316338518203160,1853620441332702]]
private def rkmPhb_w64_m32_s6b : List ℕ := uNatCatN
  [
   [709346573830995,708869649435963,708389962277058,707907513242048,707422303188767,
    706934332945048,706443603308648,705950115047183,705453868898045,704954865568332,
    704453105734762,703948590043598,703441319110563,702931293520752,702418513828547,
    701902980557525,701384694200370,700863655218773,700339864043341,699813321073493,
    699284026677365,698751981191701,698217184921749,697679638141155,697139341091851,
    696596293983940,696050496995587,695501950272893,694950653929783,694396608047877,
    693839812676369,693280267831897,692717973498415,692152929627057,691585136136005,
    691014592910351,690441299801952,689865256629292,689286463177333,688704919197366,
    688120624406862,687533578489314,686943781094084,686351231836239,685755930296391,
    685157876020529,684557068519853,683953507270599,683347191713866,682738121255436,
    682126295265600,681511713078962,680894373994265,680274277274189,679651422145165,
    679025807797176,678397433383554,677766298020780,677132400788276,676495740728193,
    675856316845200,675214128106262,674569173440425,673921451738584,673270961853264,
    672617702598378,671961672749000,671302871041118,670641296171397,669976946796928,
    669309821534977,668639918962731,667967237617037,667291775994143,666613532549424,
    665932505697113,665248693810029,664562095219289,663872708214030,663180531041114,
    662485561904841,661787798966643,661087240344788,660383884114067,659677728305484,
    658968770905939,658257009857906,657542443059104,656825068362164,656104883574296,
    655381886456944,654656074725434,653927446048630,653195998048566,652461728300088,
    651724634330480,650984713619092,650241963596958,649496381646408,648747965100673,
    647996711243492,647242617308700,646485680479821,645725897889649,644963266619824,
    644197783700399,643429446109409,642658250772418,641884194562077,641107274297661,
    640327486744606,639544828614034,638759296562280,637970887190400,637179597043679,
    636385422611127,635588360324975,634788406560150,633985557633756,633179809804537,
    632371159272336,631559602177545,630745134600546,629927752561143,629107452017985,
    628284228867985,627458078945719,626628998022825,625796981807391,624962025943332,
    624124126009753,623283277520311,622439475922561,621592716597292,620742994857853,
    619890305949468,619034645048545,618176007261962,617314387626359,616449781107400],
   [615582182599037,614711586922756,613837988826814,612961382985460,612081763998144,
    611199126388719,610313464604623,609424773016049,608533045915104,607638277514956,
    606740461948960,605839593269775,604935665448465,604028672373589,603118607850266,
    602205465599239,601289239255906,600369922369353,599447508401357,598521990725380,
    597593362625540,596661617295575,595726747837775,594788747261910,593847608484129,
    592903324325849,591955887512619,591005290672964,590051526337218,589094586936323,
    588134464800622,587171152158619,586204641135725,585234923752978,584261991925744,
    583285837462394,582306452062956,581323827317744,580337954705964,579348825594298,
    578356431235454,577360762766700,576361811208363,575359567462311,574354022310397,
    573345166412885,572332990306836,571317484404476,570298638991529,569276444225517,
    568250890134033,567221966612980,566189663424780,565153970196542,564114876418211,
    563072371440661,562026444473776,560977084584472,559924280694701,558868021579404,
    557808295864427,556745092024409,555678398380608,554608203098706,553534494186561,
    552457259491911,551376486700048,550292163331431,549204276739263,548112814107013,
    547017762445891,545919108592278,544816839205097,543710940763136,542601399562312,
    541488201712888,540371333136629,539250779563895,538126526530683,536998559375605,
    535866863236802,534731423048795,533592223539271,532449249225802,531302484412494,
    530151913186567,528997519414859,527839286740263,526677198578078,525511238112287,
    524341388291760,523167631826362,521989951182989,520808328581509,519622745990617,
    518433185123601,517239627434007,516042054111216,514840446075919,513634783975483,
    512425048179226,511211218773574,509993275557113,508771198035523,507544965416400,
    506314556603959,505079950193606,503841124466394,502598057383339,501350726579609,
    500099109358572,498843182685700,497582923182334,496318307119291,495049310410322,
    493775908605406,492498076883883,491215790047421,489929022512802,488637748304534,
    487341941047275,486041573958073,484736619838403,483427051066002,482112839586505,
    480793956904852,479470374076485,478142061698310,476808989899429,475471128331616,
    474128446159562,472780912050839,471428494165611,470071160146066,468708877105554,
    467341611617440,465969329703651,464591996822897,463209577858584,461822037106373],
   [460429338261402,459031444405147,457628317991900,456219920834878,454806214091919,
    453387158250773,451962713113959,450532837783188,449097490643317,447656629345836,
    446210210791858,444758191114598,443300525661328,441837168974776,440368074773958,
    438893195934422,437412484467877,435925891501181,434433367254675,432934861019828,
    431430321136166,429919694967464,428402928877163,426879968202991,425350757230750,
    423815239167231,422273356112234,420725049029646,419170257717543,417608920777273,
    416040975581479,414466358241015,412885003570716,411296845053959,409701814805972,
    408099843535844,406490860507157,404874793497200,403251568754698,401621110955973,
    399983343159493,398338186758712,396685561433133,395025385097510,393357573849110,
    391682041912918,389998701584724,388307463171954,386608234932168,384900923009082,
    383185431366012,381461661716608,379729513452733,377988883569354,376239666586281,
    374481754466605,372715036531646,370939399372248,369154726756205,367360899531631,
    365557795526035,363745289440884,361923252741396,360091553541295,358250056482247,
    356398622607680,354537109230651,352665369795430,350783253732418,348890606306017,
    346987268455011,345073076625024,343147862592556,341211453280069,339263670561587,
    337304331058171,335333245922655,333350220612917,331355054652949,329347541380905,
    327327467683258,325294613714107,323248752598617,321189650119488,319117064385235,
    317030745478990,314930435086401,312815866101090,310686762206003,308542837428811,
    306383795669386,304209330197175,302019123116089,299812844794318,297590153256208,
    295350693533086,293094096969582,290819980481676,288527945762290,286217578429830,
    283888447114599,281540102477433,279172076154332,276783879620140,274375002963573,
    271944913564978,269493054667224,267018843828998,264521671248428,262000897943538,
    259455853774279,256885835288967,254290103375688,251667880696671,249018348880570,
    246340645444192,243633860411091,240897032589740,238129145468473,235329122677809,
    232495822963161,229628034601756,226724469186805,223783754689044,220804427690247,
    217784924664680,214723572161895,211618575716778,208468007279268,205269790914853,
    202021686475986,198721270881101,195365916558420,191952766511517,188478705336250,
    184940325355538,181333886827762,177655270909905,173899923694996,170062789162454],
   [166138228232770,162119920236369,158000741889301,153772617163075,149426329007881,
    144951280369744,140335186741744,135563674634086,130619748187956,125483066807819,
    120128944910110,114526930781961,108638725468147,102415023335092,95790501005980,
    88675425652092,80940591226068,72387663809537,62682725007772,51174592761507,36181872118644]]
private def rkmPhb_w64_m32_s7 : List ℕ := uNatCatN
  [
   [729991480218131,729728996674325,729463629026662,729195380318756,728924253564517,
    728650251748213,728373377824532,728093634718647,727811025326270,727525552513714,
    727237219117944,726946027946637,726651981778229,726355083361968,726055335417966,
    725752740637238,725447301681756,725139021184489,724827901749445,724513945951713,
    724197156337499,723877535424168,723555085700273,723229809625594,722901709631170,
    722570788119323,722237047463694,721900490009268,721561118072396,721218933940823,
    720873939873707,720526138101642,720175530826671,719822120222312,719465908433564,
    719106897576925,718745089740406,718380486983536,718013091337373,717642904804512,
    717269929359087,716894166946778,716515619484808,716134288861949,715750176938514,
    715363285546359,714973616488872,714581171540972,714185952449096,713787960931191,
    713387198676700,712983667346550,712577368573136,712168303960302,711756475083323,
    711341883488886,710924530695063,710504418191289,710081547438338,709655919868291,
    709227536884507,708796399861594,708362510145372,707925869052841,707486477872140,
    707044337862512,706599450254261,706151816248708,705701437018150,705248313705811,
    704792447425794,704333839263030,703872490273228,703408401482819,702941573888901,
    702472008459180,701999706131910,701524667815833,701046894390112,700566386704268,
    700083145578111,699597171801667,699108466135112,698617029308693,698122862022653,
    697625964947154,697126338722195,696623983957531,696118901232587,695611091096372,
    695100554067390,694587290633549,694071301252067,693552586349375,693031146321025,
    692506981531582,691980092314527,691450478972151,690918141775447,690383080964003,
    689845296745886,689304789297532,688761558763630,688215605256997,687666928858465,
    687115529616749,686561407548327,686004562637308,685444994835300,684882704061279,
    684317690201447,683749953109101,683179492604482,682606308474635,682030400473264,
    681451768320575,680870411703132,680286330273692,679699523651055,679109991419895,
    678517733130604,677922748299116,677325036406745,676724596900005,676121429190439,
    675515532654438,674906906633058,674295550431835,673681463320597,673064644533271,
    672445093267689,671822808685390,671197789911418,670570036034116,669939546104917,
    669306319138136,668670354110752,668031649962187,667390205594088,666746019870098],
   [666099091615626,665449419617616,664797002624309,664141839344998,663483928449790,
    662823268569351,662159858294658,661493696176739,660824780726412,660153110414024,
    659478683669178,658801498880458,658121554395159,657438848518997,656753379515824,
    656065145607344,655374144972806,654680375748716,653983836028521,653284523862310,
    652582437256492,651877574173479,651169932531366,650459510203595,649746305018628,
    649030314759601,648311537163986,647589969923234,646865610682429,646138457039917,
    645408506546948,644675756707301,643940204976905,643201848763460,642460685426043,
    641716712274715,640969926570120,640220325523078,639467906294170,638712665993319,
    637954601679361,637193710359618,636429988989450,635663434471816,634894043656816,
    634121813341234,633346740268068,632568821126054,631788052549191,631004431116245,
    630217953350252,629428615718018,628636414629605,627841346437808,627043407437629,
    626242593865740,625438901899938,624632327658591,623822867200078,623010516522215,
    622195271561677,621377128193409,620556082230031,619732129421223,618905265453116,
    618075485947662,617242786461996,616407162487793,615568609450607,614727122709208,
    613882697554902,613035329210842,612185012831330,611331743501105,610475516234622,
    609616325975318,608754167594867,607889035892421,607020925593844,606149831350925,
    605275747740588,604398669264084,603518590346165,602635505334257,601749408497611,
    600860294026436,599968156031030,599072988540888,598174785503794,597273540784908,
    596369248165823,595461901343623,594551493929910,593638019449828,592721471341056,
    591801842952802,590879127544763,589953318286080,589024408254267,588092390434126,
    587157257716644,586219002897869,585277618677769,584333097659066,583385432346058,
    582434615143419,581480638354968,580523494182432,579563174724177,578599671973921,
    577632977819423,576663084041149,575689982310914,574713664190505,573734121130270,
    572751344467692,571765325425931,570776055112340,569783524516960,568787724510983,
    567788645845185,566786279148338,565780614925587,564771643556801,563759355294888,
    562743740264090,561724788458231,560702489738949,559676833833884,558647810334835,
    557615408695883,556579618231482,555540428114507,554497827374270,553451804894497,
    552402349411271,551349449510922,550293093627895,549233270042562,548169966879001],
   [547103172102725,546032873518370,544959058767342,543881715325406,542800830500243,
    541716391428944,540628385075462,539536798228015,538441617496428,537342829309433,
    536240419911903,535134375362040,534024681528497,532911324087449,531794288519597,
    530673560107113,529549123930525,528420964865529,527289067579744,526153416529392,
    525013995955910,523870789882489,522723782110544,521572956216104,520418295546123,
    519259783214721,518097402099328,516931134836760,515760963819200,514586871190092,
    513408838839947,512226848402053,511040881248093,509850918483661,508656940943680,
    507458929187718,506256863495189,505050723860460,503840489987830,502626141286403,
    501407656864841,500185015525992,498958195761394,497727175745653,496491933330684,
    495252446039816,494008691061759,492760645244426,491508285088603,490251586741471,
    488990525989962,487725078253967,486455218579358,485180921630855,483902161684704,
    482618912621180,481331147916894,480038840636912,478741963426672,477440488503692,
    476134387649071,474823632198765,473508193034637,472188040575278,470863144766583,
    469533475072076,468199000462986,466859689408052,465515509863051,464166429260053,
    462812414496374,461453431923235,460089447334103,458720425952709,457346332420741,
    455967130785183,454582784485301,453193256339260,451798508530361,450398502592875,
    448993199397482,447582559136272,446166541307317,444745104698783,443318207372577,
    441885806647501,440447859081901,439004320455797,437555145752460,436100289139435,
    434639703948973,433173342657856,431701156866591,430223097277955,428739113674853,
    427249154897474,425753168819712,424251102324822,422742901280287,421228510511856,
    419707873776726,418180933735833,416647631925206,415107908726362,413561703335689,
    412008953732777,410449596647655,408883567526895,407310800498511,405731228335633,
    404144782418875,402551392697353,400950987648298,399343494235187,397728837864335,
    396106942339882,394477729817088,392841120753876,391197033860522,389545386047427,
    387886092370857,386219065976579,384544218041267,382861457711593,381170692040872,
    379471825923152,377764762024615,376049400712159,374325639979013,372593375367240,
    370852499886958,369102903932122,367344475192669,365577098562847,363800656045517,
    362015026652213,360220086298722,358415707695942,356601760235762,354778109871661],
   [352944618993750,351101146297924,349247546648783,347383670935961,345509365923464,
    343624474091603,341728833471075,339822277468699,337904634684305,335975728718206,
    334035377968665,332083395418708,330119588411600,328143758414228,326155700767590,
    324155204423529,322142051666757,320116017821179,318076870939387,316024371474166,
    313958271930693,311878316498045,309784240658482,307675770772849,305552623640290,
    303414506030305,301261114184991,299092133289119,296907236905473,294706086372626,
    292488330162049,290253603191162,288001526088567,285731704407340,283443727781829,
    281137169022915,278811583146162,276466506326676,274101454773796,271715923517996,
    269309385101453,266881288162800,264431055905395,261958084437205,259461740968888,
    256941361854993,254396250461271,251825674838844,249228865183434,246605011054864,
    243953258328618,241272705847197,238562401734374,235821339329907,233048452695852,
    230242611637980,227402616176816,224527190392044,221614975551293,218664522418914,
    215674282621938,212642598928001,209567694262881,206447659262031,203280438109663,
    200063812368407,196795382439766,193472546216823,190092474391464,186652081752194,
    183147993647111,179576506577950,175933541619071,172214588997264,168414641691893,
    164528115274057,160548750330353,156469492611466,152282344356972,147978177843230,
    143546498716612,138975141524338,134249872075934,129353859226347,124266959509003,
    118964726578341,113417003841394,107585863513647,101422477802419,94862156406233,
    87816036133614,80156163125412,71686125597710,62075241294384,50678639025641,35831218919868]]
private def bAll4 (a b c d : Bool) : Bool :=
  match a, b, c, d with | true, true, true, true => true | _, _, _, _ => false
private theorem bAll4_elim {a b c d : Bool} (h : bAll4 a b c d = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | exact ⟨rfl, rfl, rfl, rfl⟩ | exact Bool.noConfusion h
private theorem rkmStatOk_hiw64t09 : bAll4
  (
    muxIntListEq (uHb rkmPhb_w64_m32_s6b)
      (altBuildHbFrom 1856 1024 19587930735 583 441))
  (
    muxIntListEq (uHb rkmPhb_w64_m32_s7)
      (altBuildHbFrom 1856 1024 19398096153 508 516))
  (
    muxIntListEq rkmXsWin_w64_m32_s6a_out rkmXsWin_w64_m32_s6b_in)
  (
    Nat.ble (Nat.add 844 (altIntLen rkmXsWin_w64_m32_s6a_in)) (Nat.add 1024 1))
  = true := by decide +kernel
private theorem rkmStatOk_hiw64t09_p :
    muxIntListEq (uHb rkmPhb_w64_m32_s6b)
      (altBuildHbFrom 1856 1024 19587930735 583 441) = true ∧
    muxIntListEq (uHb rkmPhb_w64_m32_s7)
      (altBuildHbFrom 1856 1024 19398096153 508 516) = true ∧
    muxIntListEq rkmXsWin_w64_m32_s6a_out rkmXsWin_w64_m32_s6b_in = true ∧
    Nat.ble (Nat.add 844 (altIntLen rkmXsWin_w64_m32_s6a_in)) (Nat.add 1024 1) = true :=
  @bAll4_elim
  (
    muxIntListEq (uHb rkmPhb_w64_m32_s6b)
      (altBuildHbFrom 1856 1024 19587930735 583 441))
  (
    muxIntListEq (uHb rkmPhb_w64_m32_s7)
      (altBuildHbFrom 1856 1024 19398096153 508 516))
  (
    muxIntListEq rkmXsWin_w64_m32_s6a_out rkmXsWin_w64_m32_s6b_in)
  (
    Nat.ble (Nat.add 844 (altIntLen rkmXsWin_w64_m32_s6a_in)) (Nat.add 1024 1))
  rkmStatOk_hiw64t09
private theorem rkmHhb_w64_m32_s6b :
    uHb rkmPhb_w64_m32_s6b = rkmDropInts 583 rkmHbWin_w64_m32_s6a :=
  (muxIntListEq_eq_true.mp rkmStatOk_hiw64t09_p.1).trans
    (drHb 1856 1024 19587930735 583 1024)
private theorem rkmHhb_w64_m32_s7 :
    uHb rkmPhb_w64_m32_s7 = rkmDropInts 508 rkmHbWin_w64_m32_s7 :=
  (muxIntListEq_eq_true.mp rkmStatOk_hiw64t09_p.2.1).trans
    (drHb 1856 1024 19398096153 508 1024)
private def rkmC_w64_m32_s6b_1 : List ℤ := pzigCat
  [
   [416852332,1268858491,2818136112,5148821843,8076938596,12083348291,16983324966,23069140311,
    30709538504,39889758803,50888725922,64084610683,79354971340,97231655129,117403572354,
    139650810755,164031571310,189828803733,216033831802,241959587743,265873659010,286404145271,
    301849556398,310215671793,309628634732,298745331207,276249362868,241651325609,195332137846,
    138132967563,72540709854,1368189835,71831876959,142829815642,207931195569,263971737512,
    308387074749,341186587334,363564904095,378463732668,390976000715,406888882454,431795539187,
    471090049220,527728912931,602135506040,691690047873,790865673812,891452497101,984575896880,
    1061013785195,1113217851958,1136694029881,1129431163012,1092577345839,1029359908252,
    943536844265,838166098322,715559816621,575851252188,419308842739,248340398012,68283460549,
    109783273127,269080016008,389230955289,449252692472,432024776167,329976382140,147602089755,
    97457976411,376241243866,653464150289,894655387272,1069929633857,1158308811988,1148026100367,
    1033681899220,813925401565,491693910420,77085923171,406003709337,910577023410,1364070573667,
    1673235556574,1741304661073,1496518925200,924673835535,92335990204,849083903586,
    1686005670923,2194825765356,2207948094625,1675147386080,696656450015,487536242441,
    1558157284010,2210019384663,2248553360836,1658580359971,616909667320,559584395678,
    1515435077131,1970339362690,1810298012937,1120906005160,151140161337,776278930695,
    1375550053786,1488667773437,1128716067982,460408044849,268938419931,819033007320,
    1035292805963,892261795506,488407581639,2983555851,404970311546,601094137561,570148557640,
    378117778649,134894479678,65054305868,184245622259,244694633290,290431560541,334997595420,
    334480502903,210731905042,78165879332,467160597613,772396071904,771163495249,347228615276,
    385234743962,1078000958465,1306499021640,827502018933,217031224139],
   [1301186988286,1772720724173,1248315476852,91229711882,1523491868035,2168243370586,
    1535118545055,106666086831,1809469745988,2490930197653,1630997089564,327888636188,
    2183833216645,2711080665900,1481259384991,784293293491,2618193563960,2758083081947,
    1029495200602,1461724086478,3020856160571,2520690200444,234525671297,2279006448287,
    3225449859728,1865667191523,885779373127,3048743120604,2996493865581,697109369240,
    2179342888854,3451878198133,2088407119470,930564510718,3280458924819,3072741036334,
    394294988807,2659780756789,3598878426444,1579384577273,1802265321765,3730687983044,
    2514468155139,892881331087,3587149605822,3175967069957,62289476823,3296153351434,
    3594713042227,615005724096,2965047185202,3824724804055,1108679718920,2669318506810,
    3921845996559,1418819945904,2452219089902,3933098071525,1563454967742,2332148330760,
    3895595938687,1569117057200,2314582026268,3840584588629,1459123314598,2408630970528,
    3792947762171,1236708428984,2637163830914,3758150120181,863721671678,3030219853720,
    3688492223453,251550192048,3583124723526,3445123601747,703023082041,4178779749360,
    2796043317709,2013872264755,4519732637912,1513745661933,3454869421921,4165949197552,
    405179567748,4482477981915,2775850529746,2506634647162,4416956264779,500405996346,
    3903481264504,2952154775647,1797500199853,3805326587972,671744949461,2960425851377,
    2328881105178,1117188967008,2579665682345,701012117226,1553639531200,1650404823905,
    93862081622,1374079092510,1544172290859,43624497613,2150066702228,1805206560143,
    1624576592253,3520784632914,60291656472,4556823479479,2175380431672,4602280687368,
    4598137014313,3608204565833,6753320840066,1736560644530,8312683590405,729370809656,
    9113390045320,3475573687547,9148880223029,6227187755554,8531645345660,8787325936969,
    7446087816453,11047287080360,6105368985672,12975210594409,4719672369987,14594087946154,
    3476121370648,15955902381073,2530649539161,17119726666184,2007210773684,18133529578759,
    2005041997673,19021334799776],
   [2608849445266,19768888163599,3899376834225,20303596138026,5954786178378,20465865122113,
    8830376045611,19979939958476,12502918208080,18443163854129,16781234459431,15367896385066,
    21199115620708,10297064774687,24938856574223,3001197717586,26835399801238,6271877400116,
    25507717017815,16535351615997,19650370556096,25839605585782,8558412322963,31199090599973,
    7017069032515,29018226687008,23801914704888,16556085173887,35481380679491,5400923380153,
    34168366323450,29864931197982,14806337560125,43617494965035,18633472063145,32358331002836,
    48589119698518,7781106661498,47204972149907,54932197344711,2143115490971,60485618357812,
    68252775873788,6612493188636,72344646175133,95055261007787,31327530909295,77218819992208,
    147256267322584,116670268457588,7986156575781,152047936318537,217440573321683,
    139381532221935,79894582108788,376092800584986,657548762122892,846633794001314,
    906760485776140,846373393291400,704561872921334,529804004369938,362502776352194,
    226552546953284,129497617378210,67646685241590,32202151924726,13897111148350,5392449975112,
    1857645152434,556572023208,139682860304,26908042122,2860965328]]
private def rkmC_w64_m32_s6b_2 : List ℤ := pzigCat
  [
   [410161752,1238189561,2730685582,4968775559,7793705546,11685066061,16449900576,22334034479,
    29651498402,38415333745,48952066416,61598231851,76169134250,93147359111,112371615148,
    133733772855,157149976478,181937261325,207379925712,232863275217,256792780722,277948846069,
    294593553796,304928282219,307501862910,300558683749,282599359950,253365488677,212390375540,
    160532665355,99577522754,31682648883,39909514631,111240494306,178931044355,239310576552,
    289823501845,329114805460,357413780931,376607272670,390622652965,404188147196,422915528803,
    452360868476,496379404633,557556320180,635302748563,725937721360,823721410953,920576891578,
    1007175596427,1075563790342,1118717259451,1132308605832,1115362239895,1069325096674,
    997342544771,903682267164,791667198355,663772600680,521387663861,365663874124,198923634307,
    27433245586,138590263994,283846265459,389471464128,436837336077,410779370488,304096478649,
    121319315426,120532086120,394538524885,666383849548,901355113847,1069690666338,1149473010215,
    1128824279822,1004356333487,778542736184,458941870959,59882446276,394278261150,862648423997,
    1284051574966,1580472297841,1669314530596,1483697966589,1000565609828,262723096377,
    612281861245,1444826000732,2030123581277,2194102085824,1850408724595,1040555277602,
    58151378772,1169910554751,1993671627220,2292904174239,1972875948180,1119367332193,
    20864550591,1113237481860,1838700754459,1995560310204,1562779328337,703034374752,
    296602569342,1121487363007,1532741629072,1440487664627,921665941938,180962523311,
    526675851455,983245953658,1076388015419,823920426648,353491361553,152899192671,526889022896,
    670647426877,582719513470,342057883197,63479152740,155639507598,272531492277,303708908894,
    294789920971,275250076400,229596580559,108768571424,120192549994,417321318205,652092577330,
    653481611693,318092297114,286561511966,899016491447,1167953358246],
   [850453309239,3261029099,1005470453882,1596245668597,1356688093544,298912170817,1063186843381,
    1951735381602,1772086836957,513839897848,1164074468756,2267909892137,2061912155094,
    567489311191,1373850888335,2564613690076,2196208794921,409586865484,1721535978660,
    2827807736959,2131475455608,7302515189,2194348706743,2999052315148,1805761391311,
    649349343109,2725626800132,2970356556379,1148872124792,1524197568994,3176261987833,
    2589628872622,118494906373,2491223416213,3321296944804,1701017618701,1227856037185,
    3286125788918,2874293289169,236749508630,2637779715688,3494909321377,1593237068036,
    1624236590568,3589829026243,2657634762006,488155334348,3286750366647,3368890433070,
    587012839813,2747133244285,3754797842084,1493115568793,2118770906833,3890003483916,
    2187006402185,1513484003547,3861542162896,2670790896623,1001299346957,3747430620106,
    2971809315825,616035165649,3607631585668,3128798818931,365401452767,3484751826848,
    3182817853265,243820611405,3411517629406,3171507170831,247461526327,3418818062824,
    3118722060435,390833247321,3534789934548,3016197299317,717362671681,3769367948638,
    2800215096511,1289307495421,4073457545822,2339958395227,2140316419331,4291718987140,
    1470244847583,3188981598313,4148856126196,96773920483,4153717155839,3333506910154,
    1641769226108,4562887218447,1711915279358,3262484475756,3962506961969,416466781565,
    4060338656454,2301514260473,2270239501567,3561631978962,214651401479,3006781129059,
    2062541940596,1245433498094,2488869846341,629465236684,1527336590250,1643516301817,
    136921702634,1356416114532,1583513391593,44247068192,2076867931626,1924671355635,
    1319076889357,3514043612076,516815667531,4191492621221,2923618223618,3654594296030,
    5271833612809,1946893032499,7005031640758,622787270379,7764113402629,3611734812104,
    7426574976784,6573463565695,6077020597773,9152905251528,3939712964746,11133888471683,
    1301268203717,12444098604872,1553119666223,13131292515865,4382660381110,13324978054630,
    7009601306729],
   [13197749585421,9321115168864,12931896097168,11257951225513,12697839227839,12798206509104,
    12642914335198,13938200658581,12889181119319,14671992527276,13535073190002,14968381362713,
    14654953345535,14747715583524,16285634383376,13860108664395,18396898516725,12080985469736,
    20840433701198,9134936293751,23291836577507,4764187003934,25205691050588,1158232306734,
    25813882935157,8479921487239,24188068918346,16608637375376,19388715378593,24355985334219,
    10732442296238,29822359895414,1746477299280,30458051095273,16592606155805,23623631922982,
    30204786271492,8006800847557,36814224994667,14216262567825,30196760683726,35638457475682,
    7528428937351,44249709825993,25668958007465,28243455706312,52084560147612,13753284530832,
    46225357004613,59319037214909,5531584799409,62486707217562,72364287694048,6138889163572,
    78591290035713,99941799837491,26637776469657,90675884257484,157442653238180,109524308766164,
    35167738134293,184478145139397,229709502091797,110924139288725,151349135771460,
    471761335917704,746547302929666,900431033266256,910750548709770,803354272937932,
    630262193789672,444480814936086,283311761841250,163524306284776,85384571809320,
    40179483963194,16918928412402,6301652178750,2037563696116,553680277204,118363603324,
    16438327622]]
private def rkmC_w64_m32_s6b_3 : List ℤ := pzigCat
  [
   [424206216,1267984415,2766889018,4985249131,7757416546,11578389859,16252180972,22026218695,
    29184216014,37702733723,47897452748,60103427151,74163425368,90557254563,109081033632,
    129636220761,152197686840,176188934259,200968838666,225902926813,249510665390,270804738123,
    288199927446,299907438377,304442796496,300184532249,285751369536,260625703927,224065922836,
    176647392277,119727903618,55196970971,14087613209,84826353388,153696864399,216804698802,
    271592856687,316137825840,349673765149,373520466316,390298492877,403734667910,419385589351,
    442249235094,476962630455,527006608868,593363588799,674437460066,766263239209,861931839186,
    953442801067,1032181233064,1090334470487,1121894646784,1123698700935,1094939022364,
    1037916152433,956269362068,853841198021,734922659954,602070291723,456963949002,301878785661,
    140012843898,22721135110,175649418795,304714106704,392863365877,423068755370,382454958919,
    265824269982,78130038439,163687997523,432936103970,696724243105,921084743878,1076231716989,
    1141293820848,1104547014865,964267052246,726527891947,402842707082,10980445793,422490405479,
    859166487840,1245871077869,1515678680248,1598518794847,1436374384032,1005335969497,
    336380183516,475181377604,1276642502247,1884937641422,2131803895831,1915742916716,
    1242528049955,241547156234,853871755442,1762937272077,2235960966632,2130543647925,
    1463723615132,415632344871,718532098417,1615678753604,2023234184055,1839115636274,
    1142425240859,164556462994,787199865108,1430123119137,1594668662736,1271893548107,
    604208420548,170839935558,804718553103,1119036411108,1055439748869,681223435612,153531204285,
    341275623879,653759955350,716083451645,553387933644,261219741223,40184716099,256430416578,
    350852343369,343607798618,283966953755,210784730000,127268058879,4897953474,179734122644,
    399236508905,558783236378,531112460843,237480498668,270965945428],
   [789254695777,1032022568356,786659735033,68689393552,823923029534,1421479844717,1328831742604,
    481322397677,750489287739,1707612433498,1794796145639,854647302242,673178390780,
    1940880644691,2163667253140,1113568243905,678169766705,2173961689254,2432372541235,
    1210329012884,822810149518,2437744177111,2590423821228,1108511748897,1136675092459,
    2729287230622,2604773277743,774157152254,1619537699100,3003427774437,2412690956804,
    178538431879,2230357702867,3163148294616,1926540882563,682096486453,2864603945540,
    3055915704739,1060205137744,1741750134338,3327089190571,2492680680214,210339019280,
    2807454481307,3328749477362,1316278223949,1749781600105,3511828156984,2547357356851,
    456671226599,3151281913008,3347650914685,814998027758,2434226646594,3715092574397,
    1899014346962,1554093943810,3730248716319,2720608198468,667104915392,3507612861845,
    3275476536042,123551681037,3159644834513,3601449380434,764901325055,2776987210015,
    3754999553972,1243326828019,2422736545771,3795179558568,1570687440491,2136163864163,
    3777076862914,1771484337617,1942271319013,3749690749086,1870332118307,1863866140613,
    3753582035292,1875923791637,1932286018369,3812692836032,1765453539725,2186279354555,
    3914872933218,1473544249021,2653484935091,3983893514516,901303592547,3305138715235,
    3862100896166,36225956576,4000135541189,3333890212808,1319835102424,4455796226205,
    2223308568600,2726196980770,4308906414407,558143173026,3806311804124,3309617793157,
    1290544679247,4048367828032,1585971836727,2665905834167,3234674414320,241486541916,
    3005088446555,1768311102686,1365315670462,2376192474391,547845304644,1492158734336,
    1627039073619,186029681168,1334668541740,1636654370569,133582029278,2031312736116,
    2042945146707,1064558525069,3500268745616,995339677355,3819987177005,3483977408006,
    2737014247994,5622008592695,430188262069,6771901065868,2601207501705,6592583719585,
    5727184600626,5071970443634,8366965978421,2463692211987,10110736929534,826907380837,
    10767724605973],
   [4360493598070,10353020577370,7756138455035,9034140500187,10744020113048,7065744597910,
    13181290655405,4727415705165,15039315496450,2278809129310,16376006197173,66721979440,
    17303964655728,2150623251449,17962207231659,3864418019580,18494041606854,5134397390825,
    19032756641441,5902562227276,19687859008006,6103115961415,20531736648517,5644380490508,
    21577917203184,4399670550043,22752428450981,2217722716774,23860692794448,1042828398188,
    24563147397477,5450408997739,24369634043702,10917404515276,22667207936993,17102951635163,
    18789239876484,23308331574220,12143802845135,28370807971129,2445239316494,30598394726816,
    9881392604842,27893059169517,23124493319373,18337133743558,33795237276048,1453726050727,
    36832875529701,20075313971031,27217741542090,39178136074312,3189739472815,45044766878779,
    29608605557643,27176164180394,54912412702950,15514876812352,48644359265127,62123511058579,
    3168109471607,68676307697328,73969932639262,2305730077049,90792665897797,101696764472307,
    10406929522045,114775368499690,166612424946058,87075150921506,82530709868979,225894091971007,
    227878343758265,45990479460541,268149949978276,603006405665690,847595750969212,
    940047032699728,882197006852316,722372434603698,524104862866908,339478322534456,
    196806530928650,101968604211380,46961026941612,19027774660956,6665409858208,1958228657900,
    454590278994,71196433774]]
private def rkmC_w64_m32_s6b_4 : List ℤ := pzigCat
  [
   [455226188,1346689233,2903760068,5167814667,7947569876,11762545617,16399495162,22123473839,
    29213252960,37613932949,47627476186,59563397381,73253142332,89207508951,107212906482,
    127185081911,149094162542,172374554569,196473318336,220841988975,244076636704,265262875505,
    282866932738,295254354905,301075504356,298712360263,286727328416,264516361235,231308490492,
    187550907835,134172741314,72641654003,5567539042,63968597968,132884762301,197526505936,
    255253837021,303717507428,341628080309,369577048308,389430272427,404255949238,418754973733,
    437561744920,465681602039,507054050650,563635475971,635475705300,719973605137,811675090972,
    904014456657,988556943134,1057011852381,1102701484516,1120539904499,1108054641276,
    1066039019685,996717022682,904251769289,793189929930,667339194235,529768780534,383011489417,
    229383474950,73097789087,79281719359,217548779346,328049499259,395194425830,404592876019,
    345094987954,213796395925,17913780522,225539528644,489712906667,742357139888,950961977427,
    1086959476830,1130157883875,1071169213712,909989409817,655466716430,323122518773,65725610527,
    482733379958,890043992847,1239480696024,1473345623267,1531844461288,1366855450429,
    959262510806,335098119409,423152089575,1182171249236,1779000056693,2057646666000,
    1914101566739,1335865584502,420701262229,633266550917,1569752292718,2142671372341,
    2186929130030,1674024001141,730727571692,389922761290,1379073508313,1962584919384,
    1984540451065,1456371079780,551626479937,449878195491,1250612883976,1628731829681,
    1504231533872,954693198909,181433885574,562781670422,1057479120989,1181556347098,
    940464673787,452058189970,103022579920,546844232085,760618948668,715172796631,468110134988,
    132695234381,171115279639,360178096264,410947227701,353954774740,245565726409,131421107862,
    23065624203,95702602997,240015874076,389560614591,475475259352,406066023779],
   [128927909064,305805850432,728398391429,908159724268,675203866939,43537945890,740481745790,
    1281961196383,1234555689536,516439848863,585242338217,1512697892354,1717918687109,
    989203017050,371129985048,1651949316391,2103295996962,1381429433625,196225895607,
    1769918642820,2403798196667,1650151263674,131376275192,1925433840423,2637773410320,
    1770312312731,222359089901,2153566625700,2808683787451,1717865797408,496580652300,
    2459078675427,2892450463378,1459699386523,963941883607,2809786977134,2829777192955,
    953331172410,1607371562392,3125715339703,2526345215544,164230562167,2358245585171,
    3266039245488,1868101240629,895992015143,3062646641896,3033060265587,768408789128,
    2108879564932,3457164106117,2213581931246,743310419306,3181010279185,3188629152014,
    693761508145,2394885077533,3623024386106,1949751768553,1337723971861,3578753720240,
    2889602959207,223326359199,3189082443492,3481589185005,795817918748,2602224879452,
    3764363011955,1635749411812,1947101990456,3811912004345,2269840433894,1316827728800,
    3706311352037,2711025658622,767403121530,3522613539043,2995218740242,325096011984,
    3323185304567,3168538452318,2612794643,3159218497047,3276264175262,212298858865,
    3075721680283,3353628530160,290725641379,3112769858845,3411858312900,204387769789,
    3297910816913,3422376054724,100446229868,3625660932369,3303550930420,678538192158,
    4025422214295,2925696259630,1539064376242,4336609627873,2153216958816,2583030284696,
    4318216824347,932258507288,3557964453076,3730522440285,600934772519,4092122718830,
    2491858288873,2067732520709,3858144942022,837895165021,2958598132995,2831281803906,
    674729419254,2947811166955,1457950798514,1466145062478,2245941991377,465190071466,
    1449136524064,1607612242263,240953103522,1312590833222,1702765858717,224551541792,
    2009200592446,2165858536179,848850563669,3492649846618,1401754898523,3464143115033,
    3907537872080,1881570056800,5741864400125,900690033030,6217807218752,4160540639937,
    5073614962429],
   [7075271082060,2485805755518,8963240295359,1049298315386,9430239553348,4893303198181,
    8406356213889,8437160525796,6092668627036,11221024766315,2861105147729,12989908220690,
    856026012041,13690205595765,4656675557840,13428609952998,8226551304577,12413565794609,
    11363478705694,10898823144316,13975372859255,9137806513593,16060606047078,7356943531102,
    17682926076703,5742978297301,18942620812006,4446163657250,19951263818469,3590499808521,
    20807206001852,3287630467386,21572571781467,3646180768925,22248742888096,4773309094564,
    22754920358163,6760561462977,22910520668476,9655248330126,22428858905601,13417617720549,
    20925812126426,17867022409880,17947366761355,22616469472375,13023128670426,26992699174504,
    5770407039307,29946279831291,3902554319087,30005341249964,15437284429288,25414504900009,
    27144925641877,14678240149992,35846204007330,2367482909096,37102138733913,23160881046349,
    26540356812402,41362660119510,2472341371539,47130173679915,30417475410397,30170660466176,
    57473764203506,12226269751038,55228314688887,62629534057481,6438252698148,79056556268924,
    70743885546578,21049639090257,107886040872171,95519442952841,21656087815222,147858072459886,
    166153487481760,39621585145046,151786726249175,264888115192993,191061396852845,
    74921142046564,437133521682266,759311930395494,937175624215970,939152710307144,
    801982841351502,596612892605186,390602034367750,225743792616224,114879027121158,
    51052155038742,19498625470772,6218075928060,1564001528260,267785535080]]
private def rkmC_w64_m32_s6b_5 : List ℤ := pzigCat
  [
   [503210878,1473150651,3136830902,5507057795,8352018612,12227384949,16887553036,22623163071,
    29720361824,38095617913,48050572252,59870108269,73346393338,89018199011,106646108684,
    126173442821,147584561728,170299766615,193802426230,217588121089,240312969536,261185262227,
    278715909356,291343257709,297790684034,296495485937,286100846228,265975814837,235211740604,
    194137499075,143501402762,84587648829,19714668874,48434140196,116985848273,182315342024,
    241758765521,292869783402,334167406587,365676572490,388468616329,405017054958,419529650393,
    436230693636,459959916831,494824433388,543495371219,607115812344,684312204809,770922142122,
    861406254245,948123502820,1023112183607,1079034545802,1109706437187,1111382614274,
    1083147078591,1026042442168,943724013781,840406926874,720536851765,588505607132,447467702205,
    299973567590,149657723325,776504686,139386440064,260314936021,349370130886,392578937671,
    377108480790,295373562581,146727669132,59696756384,304959925879,562220805084,800061244507,
    987027728648,1097015930385,1111903691418,1024192881305,837122703302,562653714603,
    219199898728,168078307222,569020062183,946407113744,1254999720677,1444659934078,
    1465492108759,1278884282150,872616563439,274257164460,441105593926,1153353709971,
    1716322692312,1988628136827,1872239806080,1348130134685,496444829928,509965090920,
    1438707081913,2054851399866,2187174703471,1782571324104,930185461293,153036064225,
    1179580207026,1871975633345,2044472176532,1660072259977,843184857620,159537231998,
    1054791439781,1591979785880,1639421964191,1218284477788,488013102385,311169087195,
    937859865530,1224896705135,1123967771050,708756319787,140589199626,391887044536,735150305739,
    813932043544,644755940915,318937201538,38765007526,316491642009,450618430214,438120339269,
    324995782884,174138613029,33083245520,83153873160,185668894543,286599304696,371108595557],
   [388042128682,274796994313,5188647062,365260428962,691689667709,789454857998,533025255931,
    46067998689,727881903014,1177009340073,1105790666676,450562238367,540829618769,1386849040416,
    1603867393191,984385780880,238163273838,1456732394665,1988173342628,1461360623283,
    72357400946,1463134106916,2274417087225,1835187411160,309750967291,1481472963085,
    2498261759336,2090104248537,421457297558,1569256663410,2691352571831,2219677389930,
    374000190447,1760953331631,2866435634468,2210045655105,143500612250,2066417645386,
    3006969298061,2029973586514,287950822674,2466422054697,3060781922892,1629536023231,
    923153700629,2899638945718,2934697878633,951554083050,1727580809032,3246110902599,
    2501493264656,36189334576,2592828196557,3317464539264,1632512310643,1284559426925,
    3298344070970,2874806425733,269917844084,2585890800610,3500479778601,1712645675750,
    1446094168324,3513500869321,2813419552196,158502967688,3044538585581,3481313660936,
    1055362478463,2275098672257,3735843238474,2058896976389,1380709322143,3660720553788,
    2797160286609,496817475769,3363849459832,3275979431599,290478334668,2947994309548,
    3538285017465,940927318098,2496794389570,3644553240757,1449238901288,2071074384454,
    3658761463201,1830572508848,1714102821340,3641855348207,2107263523978,1460477410624,
    3646643970631,2294705409434,1344717326776,3712029125627,2387646739056,1404939146280,
    3851402028231,2350041569492,1676372709416,4036661366781,2113303447996,2170581963646,
    4182094894917,1593961998936,2840460589628,4142796298915,737928819794,3547303784030,
    3746299630491,415070201935,4055543160854,2871974095359,1672886287067,4093921373540,
    1561506353245,2696777170147,3495496715124,96161224951,3128898338979,2366526093368,
    1063340973842,2833004564795,1145255195530,1539388337196,2104347688095,390284522700,
    1400084924322,1592346846955,302077497664,1294998807932,1782666975919,315868660864,
    2009039129576,2296640358435,663940025285,3498408604416,1756423249829,3133953818357],
   [4234491298326,1098747235196,5703859358879,2041914957542,5467595171414,5322266335309,
    3410153779767,7744496890936,30099932651,8590253257601,4060255091312,7585211481948,
    7799821967789,4900500723333,10513140322432,1034446306720,11752273251137,3361083319132,
    11394418607440,7647393299147,9595771699831,11319042594044,6697312823720,14063162865631,
    3120139740293,15765134874536,724920779901,16474454329817,4497294548980,16355725792988,
    7957482144073,15635129802661,10970076712168,14558272249114,13489424950885,13360986433401,
    15534427632918,12255161985734,17160301499703,11423580818827,18428368532232,11022122761108,
    19379516202207,11180887852463,20010548717232,12001604126666,20256297540123,13548081872775,
    19978822241872,15829269292216,18964974032293,18774032855193,16931458109858,22196383442112,
    13540372837291,25743723683811,8433978279774,28824099025426,1320043365333,30518103457559,
    7847236442297,29532854494826,18549787277972,24324709049009,29291533883155,13554470057290,
    37283782335068,3037178676932,38569853041089,23455358196265,28960278525854,42369897811558,
    6071096025403,50779789885455,27287801887019,37847986619628,58837353682840,2362033503500,
    65642299965907,58216738811931,25123008942446,91441250426080,57724690945210,52167873993785,
    124920387732965,72604171507145,73108756575318,181744381585342,140111270041774,43228317711493,
    235280184888105,275091346572071,87590580013107,269834620618270,650860777586626,
    910378215561242,976534260769928,867302042890756,657941832833984,431994226679156,
    246272278199578,121319705701234,50946750538786,17749263924238,4854770621334,903722110838]]
private def rkmC_w64_m32_s6b_6 : List ℤ := pzigCat
  [
   [444489795,1301822188,2792926535,4979513454,7711852213,11443939460,15890983019,21282368086,
    27956513777,35946671612,45421603787,56572979028,69423156007,84334688180,101030143667,
    119738446942,140296210197,162114605430,185161568485,208398084954,231110765685,252391800092,
    270783949781,285051502502,293885464667,295496319486,289013711611,273134174294,247180387023,
    211162569160,165287322583,110635670074,49223574745,16989301901,84846925678,151421046767,
    213822068918,269185508115,315708071318,352697290695,380238478508,400454462313,416081302092,
    431031456423,450015749066,477280515101,516333592356,569498415845,636508682160,715581941645,
    802317588628,890244785423,972066046816,1040069192881,1087130950794,1108259255171,
    1100015145886,1062043873259,996360998536,906405821791,796885842790,672678690823,537645866686,
    395654676213,249683442624,103190184653,38805413345,169285956404,278396197183,353800438330,
    383231042817,355350740106,263640639249,109113352830,98807391432,341369667479,591807253022,
    820101255425,995845728014,1093459028131,1096156684460,997297942093,800744874178,520093972111,
    175673948020,206112961510,594178555053,952484381986,1239520929717,1410133286524,
    1421308246215,1239959384454,855577320331,292472625110,383336967184,1065963165041,
    1622439123322,1920998040345,1863616513760,1418964550079,644665891592,313227115684,
    1245311250435,1926218385584,2174786143841,1908675028788,1175583913415,151115199514,
    903051580248,1709498233779,2054002016734,1848862399197,1161724792648,196022811631,
    769735263039,1465157643172,1708740849149,1459914643746,823708750237,12636332538,724511362842,
    1181180404717,1252661720008,958281186645,425043984896,162579243856,626108139501,846043284434,
    792097725235,521109073182,147359941587,202698916145,431946368358,499549513703,424610803380,
    265554425283,88644046170,60029516814,167585711365,245944825500],
   [306733387119,338750291068,304046951935,160072308636,101413895496,419102168149,663185501718,
    683997309241,395037361428,152281004988,750191965705,1104466511948,978170422205,339388713852,
    573422167256,1327334203319,1497145356854,905940856593,232314701085,1370622861950,
    1888358868333,1433582292528,158044897513,1307114474219,2158688784338,1865849177147,
    506251558918,1221217910350,2349081395389,2187184248494,753616277681,1182803408413,
    2506536170862,2402077509065,865851443972,1240873169158,2666218051609,2514796732956,
    820575512141,1424198346837,2841181885778,2514972435077,596527258116,1742556687710,
    3015857790463,2370375245230,171874773409,2181123043749,3138240941218,2024417962255,
    467334970759,2687207580018,3113711104783,1407068786730,1304170103664,3150458909413,
    2807975123102,464116543891,2252314285857,3387023689328,2071916559961,788714443399,
    3112717632816,3147863655357,809163320690,2183228215092,3548839026653,2190257651956,
    897994269270,3325298697299,3149203724376,452499951517,2642745903395,3626712758308,
    1652197602783,1703550819047,3671541184710,2580887053551,690674175537,3390193904424,
    3202838103665,263064818328,2904969494756,3543230888567,1080133449922,2325914857012,
    3661043151089,1732749521716,1737052250896,3628108203919,2227933710032,1195657926150,
    3516347256605,2593432143468,738272838978,3391378168055,2864038271638,390913605166,
    3310326001343,3068465900510,179332959224,3318648814211,3217078792928,136321074594,
    3443084696571,3290339564646,300709607082,3679375121073,3233141085364,704629813136,
    3975109156233,2960795845222,1345747664120,4217830530247,2386509246918,2152133008952,
    4244922811155,1472634282196,2957235503276,3889906375321,295259541372,3515086328520,
    3072267794385,918218792235,3586027697658,1897427233563,1832764038391,3086963148428,
    691750270319,2169562326109,2227852809108,120949358426,1941951319995,1489070900090,
    320299917820,1586669317569,1322371712552,203253430790,1757742360763,1663898269318],
   [573409894090,2723900893005,1654079223968,2134293202484,3734121703779,84016787412,
    4497459016014,3103069199089,3340019196393,5702974919166,449052419134,6797331464205,
    3325604003432,5830425408386,6830554841999,2920122513221,9018088381258,1252292984775,
    9248180299601,5708679717090,7410177249724,9476779854001,3869477428817,11826866598788,
    701070745519,12393355226953,5527180215968,11178896990378,9911853700381,8475000193735,
    13351937770998,4740031483156,15581464049277,479417932991,16558598212714,3850710717237,
    16413669879119,7901655978870,15385076784088,11454336736055,13757771537375,14413147883416,
    11817838724116,16783298170201,9822952589359,18638478114814,7991254218584,20088336239201,
    6501466511801,21248041587680,5500097068662,22212179656477,5110226838907,23033310727900,
    5438261930978,23705591984651,6575402304157,24151486384302,8593652165804,24210648011173,
    11532838796349,23626023234826,15375776666874,22029787590921,19996720140739,18935166716802,
    25069189417496,13763471123121,29927117609189,5962878197688,33409633725552,4716713320216,
    33790665758987,17771625965523,28957438842686,31398489978802,16996007342543,42072233580245,
    2721524593731,44568244468936,27953867839908,32920964071013,51659341078905,3294879737186,
    60823420913920,40094346638004,39635000286219,77802253048073,18115863805593,75882623446132,
    89973517994908,6370515538193,115980968122611,112705795411785,22095235457768,169005607070084,
    178437413018126,12614673650616,209783582112965,301993886656429,149741997228803,
    209841041803912,621012947192556,913401082001366,995359243306458,881635983811500,
    657254312340832,417852437454090,226692074143542,103868084419722,39201884841848,
    11552432054356,2309415248330]]
private def rkmC_w64_m32_s6b_7 : List ℤ := pzigCat
  [
   [285316478,1043522225,2644267878,4593550667,7305167274,10796412947,15022081434,20336472641,
    26736558268,34212125057,43353937200,53943152395,66335984214,80580100471,96540255250,
    114475064935,134275760210,155378858621,177749344498,200561730241,223121462474,244485992323,
    263471189494,278911324241,289391812518,293428675637,290009989304,277627848481,255793479018,
    224113054403,182474973218,132078688513,73961715398,10263028907,56337193307,123206029508,
    187293446705,245713439584,296639613835,338288578280,370628981939,394696223734,412543899765,
    427674752178,444161767697,466004985736,497567850529,541483768036,599125127833,669874869244,
    750589450433,836412846506,921039763769,996668488968,1056238906553,1093218774888,
    1103022427459,1083645541732,1035133276697,959766973720,861945556127,746172937660,
    617507377133,480252731450,337914848003,194072252120,52560310463,81772118179,201336305918,
    296937916933,357323074864,370805472141,328098208654,224417973859,61733838778,148979274602,
    388864095751,631766692148,847979539615,1008760979172,1089931542325,1075713542814,
    961383936089,751992637808,462543910945,115547724576,261633854958,637141612591,975168035290,
    1237496999571,1383691425962,1376286039111,1188231237570,812552648199,272821498920,
    370292384906,1020887415517,1558242163200,1860231224759,1833046376518,1440708156177,
    726246905488,184069419428,1101090424721,1812469824278,2135818066065,1971863173754,
    1339593791137,380234129412,670880754196,1545453350953,2015417604684,1958530623671,
    1396791016774,492192639967,499801721985,1304334949404,1707771680853,1619827843538,
    1095258902429,311625461042,489641814100,1079183291997,1308181437628,1145805902737,
    679186790568,76393462723,473120911049,817782122628,884608827729,693168098422,336752148985,
    56368275303,367446218498,522614090587,509916071262,370331756117,172900910834,15662555350,
    155635159697],
   [240705586992,285577678785,302809612032,285879627483,207591844472,41444308719,204287639211,
    463980039940,623326551209,565551842582,240992480135,275778148027,784313976284,1030184547127,
    829718257772,189306396857,650427174349,1294700654010,1378825307939,773958144618,301514681354,
    1343216552741,1793826203846,1344584157855,141175281144,1239497212528,2061468777487,
    1824986271442,574700016055,1071528382373,2220701444170,2192512509977,929683845138,
    919837283762,2326663669287,2455445348318,1169168254833,844160354253,2430412510598,
    2631726978097,1274186341176,884087293078,2566185827389,2731491602752,1229665185867,
    1063899291019,2746553742826,2746387728005,1015772751200,1393317380590,2956345307847,
    2642225357174,605869205741,1862973801679,3145176254284,2357303363919,24449937707,
    2429671042710,3219642548209,1811455872190,874430753890,2994119765547,3041489443506,
    931169560003,1880199520503,3381107431196,2446812903813,297591747403,2865914987748,
    3337613134077,1306882040444,1745762204984,3509343444033,2594095251792,348739314076,
    3057321804131,3386875995436,1027273825963,2180210257275,3658754339928,2175689415913,
    1099032683403,3487718643834,2994173769597,1664680011,3002693211446,3467745232455,
    983180419608,2339271001472,3641569473969,1789132994810,1612716034786,3589648483337,
    2401017226366,905877481496,3394681611977,2839321690026,270394678088,3134381676255,
    3144429409384,266068448647,2876850343747,3363104160338,688666192441,2679931252563,
    3536815764398,983488884591,2591071485077,3690646004116,1128343169671,2645027038105,
    3823109956082,1089291625483,2854942300509,3898342132716,826758784701,3198153308901,
    3844114097622,314322532093,3600424287229,3566050553628,430493078074,3930998964707,
    2983003180192,1313535393428,4022608051075,2081949497510,2150058707154,3731008479951,
    974528607482,2702224698192,3027174308143,89787707865,2783367474630,2078878290863,
    803227471675,2405718856388,1239276047105,987327056543,1874594158206],
   [869923358733,807966505355,1689933960998,1023603109741,826327381709,2184928163218,
    1189692649359,1689464073585,3051008195022,427543521359,3476942856113,3167787017274,
    1915539324552,5128756441927,1197698098058,5204070701346,4679735914943,3069351876067,
    7144075867186,722695575389,7562490268851,5010225785848,5612558324528,8476387090979,
    1722055131573,10087288712026,3143474334585,9364163510569,7822482654486,6438773845500,
    11290717780147,1926206139077,12886842592964,3301726295983,12397287869103,8355897138430,
    10011399061080,12513425478477,6198854284819,15319570743434,1557336341094,16606000022451,
    3323181073870,16448380823910,7957071002635,15090699593465,12011904808028,12865205557278,
    15317609344997,10121927626359,17845999630850,7181255129382,19675443292883,4308249691483,
    20951404795124,1706573172436,21849715214365,474309845048,22546199183078,2124052586751,
    23194197514581,3154757189722,23908057043608,3484890215067,24752038328115,3027260269156,
    25729089401170,1678626144073,26768172130649,684364424565,27702012507994,4198003295166,
    28230284797569,8980302747523,27871893784208,15052064637014,25925621091755,22188076529357,
    21487207879846,29701180964614,13599638606341,36208066981613,1599851419830,39493184978074,
    14313144812834,36620660615829,32328116781743,24491618859562,48185191721504,1160829884895,
    54575247590071,31548254995377,41961207910412,64119280254170,3338079540233,76878346817795,
    55440798782595,45854699739796,104792895902008,37643485300674,92860866937321,137677181315307,
    25994828679909,146672569641880,203648899625918,60422481933880,183896036477281,
    320309210026125,196336018165973,169820479485120,610313872998436,927980900746222,
    1013611927756282,883982835965764,638618233585894,386503735145918,195049293661580,
    80320862339188,25641687584892,5524614728792]]
private def rkmC_w64_m32_s6b_8 : List ℤ := pzigCat
  [
   [263046079,961114492,2446010259,4315426260,6979269837,10411967938,14493748513,19545288700,
    25723865337,33058085010,41831451051,51936132818,63889829435,77576820174,92998317933,
    110429785964,129307902127,149858338452,171641939811,193948241912,216263117679,237613438568,
    256866319963,273183659552,284808518069,290704885918,289640476781,280228873464,261733115303,
    233728838700,195958663191,149223828346,94411923739,33404937096,31603716670,98041078097,
    162910484276,223553391557,277691179750,323293893771,360034581212,387938580549,408615276232,
    425043736763,440397337032,459076840091,485002229832,521382405855,570607345386,633045218895,
    706883397458,788794708259,872861949428,952536655989,1020662408310,1070132710115,
    1095408372744,1092862970203,1060868973790,1000898440409,915691263832,809617422769,
    687887120646,555311067381,416307520844,274881080763,134198588816,1296194092,126285307977,
    233695869220,314193838655,357415488196,353352623925,293866296358,176324009863,4466637598,
    209824461138,446538522319,679990693392,881628764499,1023526508702,1083774286655,
    1048555273898,914575823829,689359865866,389496428427,38869917902,333250556294,694831182995,
    1010772581716,1244816678373,1361279706488,1328106132001,1123953802744,746814949689,
    221119023890,395252046258,1012943148601,1521832847618,1809825524133,1789348780086,
    1425037955289,752350515982,116593689272,1008835791633,1725507374090,2089111328195,
    1992775830058,1436736175507,537160003906,494684796868,1403372418165,1957223799296,
    2013250375007,1559321285782,722028441143,267844744359,1140876201872,1665695635823,
    1715280783528,1301954233613,567573812962,261910735860,947769746103,1309823362682,
    1275055332369,891085122484,302539896593,301306938171,747475061400,928389641981,827117644116,
    511335292529,101774485978,271461086458,508984598719,568953778728,469695976655,272225312460,
    52166731353],
   [129200221331,243348448070,292917482263,297078768882,270834002097,211091176028,99281578575,
    76205971917,294664756172,489417912827,562104743288,428008567831,74009226936,403730724826,
    813745695061,940630586524,655185436975,7990207798,753125396076,1270016961817,1241347015086,
    595184964241,429377566995,1357814552012,1698197294471,1203638962492,40237673487,
    1247280822453,1986522320894,1732100573853,537206749960,1025554593144,2131502542033,
    2141877613404,979187069647,782295626701,2191759722422,2437115303569,1320153530684,
    587648529044,2228146940417,2643068960204,1541881691997,489718453789,2290323946824,
    2785345031449,1636254055860,519744209878,2410403324399,2877419428594,1593505837745,
    697763523039,2599510638090,2910868233767,1393742784062,1034766503220,2843374217795,
    2849992360856,1005693300807,1527296343865,3094417657218,2629913271507,395885986722,
    2141508737864,3261929626725,2162328794540,450275282186,2790746314227,3207303705360,
    1358315344613,1490003347301,3310476258098,2756518501991,177382245806,2571694591416,
    3449682793147,1755418772414,1288305887138,3392510688673,2921509525978,186812001487,
    2724495523907,3529205999844,1553016895775,1675742433317,3585847127152,2615695477787,
    483272367873,3199462815134,3292400911747,661816993418,2520669308458,3591312894279,
    1637602447388,1696909619350,3576948590177,2390065252128,847489900618,3338894627577,
    2917931440656,52353859122,2969211650085,3255783686234,644196727089,2550059722013,
    3456194353482,1225256771927,2149482337283,3577001354456,1688617866805,1822557019297,
    3670378735328,2034249246227,1614622883239,3774085981046,2253988344743,1561855918439,
    3903269523198,2325231992105,1687013536749,4041806575600,2211685524877,1989370761335,
    4137455870216,1873925241207,2429443199879,4105890786562,1293440339033,2916451099099,
    3851063786346,503882695385,3309849519457,3305595309564,381582161964,3450231529249,
    2486527846610,1170870318522,3228586415267,1538721098162,1648902883574],
   [2674679723741,723040628716,1695103894952,2014696356565,305673977676,1420158262304,
    1617082620619,357936567418,1217093420018,1775447794813,569169368156,1601014150306,
    2388226610849,262861834054,2806724465804,2755092840259,1221029240061,4328432271906,
    1795220628143,3843290082657,4820901533068,1168518602642,6326389561863,2771771976502,
    5398938412020,6448402598443,2117399663697,8392097032216,2528746126567,7756489766089,
    7066534179390,4573121343516,10083485806387,339601990506,10668868975256,5711786368635,
    8620313073765,10236748385482,4403580247888,12919184550161,1068155894540,13265388027328,
    6724023550187,11306422117263,11599601335304,7488353730286,15012617844969,2496070505105,
    16632463552108,2929748625669,16457281665551,8136250060628,14733796581174,12646835423585,
    11852825493291,16191265637294,8251708327356,18691732626505,4339262411587,20222942823086,
    450856826544,20961546323825,3169577816572,21137664706144,6365331124195,20995838389727,
    9050154169070,20767133905656,11184421028229,20653352013823,12751723539850,20818302281434,
    13735208299105,21386023246389,14096543770200,22440124003228,13756046737163,24017647934137,
    12572044754886,26091068653980,10324045063561,28528504290099,6711209930920,31024162074364,
    1385691118639,33007984272433,5944665827143,33559708050194,15322486834338,31387085607925,
    26251988727439,24936449552778,37349450967474,12716452705867,45985508471515,6058535738543,
    48038627428148,30307338283824,38121437954083,55214751729185,11278200196486,70239497354428,
    32429597441272,59646478674579,80701502495321,9924589870190,104173586287808,74269061923728,
    62671784722251,149817919121825,67244590555665,121276659000124,219662713223430,98515397871906,
    163620981466307,335893819524637,228883405785139,153273763149280,624074331854780,
    956978216993292,1029770852597510,869925349458072,597904596849962,336392631589584,
    152481948903420,53084746410498,12386813854378]]
private def rkmC_w64_m32_s6b_9 : List ℤ := pzigCat
  [
   [256484672,932409451,2363372402,4165275091,6753461078,10116982729,14139309010,19093087917,
    25088845054,32173029921,40677845034,50530149373,62140274290,75335896203,90213125420,
    107141864273,125558306450,145509539475,166640865458,188484789631,210494558818,231729154643,
    251196924910,267907881423,280375791406,287756792555,288446274936,281295864063,265705934512,
    240644326949,206276382124,162779384105,110974561646,52594610567,10539371617,76156308704,
    141141330103,203204831236,259686157185,308588830684,348925633519,380495649178,404253372571,
    422470400964,437991148607,454835617100,476727045763,507343202134,549472761303,604181968382,
    671068517341,747726555798,829353278559,910427956028,983713714887,1042266502496,1080118009415,
    1092089673004,1075729239691,1030597630848,958386146599,862999797598,749184189525,
    621828617430,486292632887,346670459638,207036551211,71257464576,56609338958,170880686843,
    264098976826,327805723271,352111275802,328479204471,250970127758,118391214703,63267183441,
    280460137440,512946473855,734611036380,917986917367,1037261421852,1072204296325,
    1011704838656,854949117731,611358214970,300082860757,53588617933,419452780510,764516850235,
    1054988188588,1256999442229,1338436916942,1273312273145,1046039609918,659431013421,
    141214192350,452113982058,1036337651177,1509263874864,1769028833209,1736183197492,
    1379138313439,731485157022,103882479854,966723750685,1670309020108,2045762268199,
    1985759016490,1480117739243,628238147700,377855735384,1296992275913,1900096448640,
    2033545095831,1662936012002,887179837521,85996665037,997182633032,1607609226441,
    1765906149644,1450848228121,773181960924,60638848038,811587823677,1278907329312,
    1356923519877,1058233369748,501762798927,130753677247,654424233048,935326157495,923938835852,
    661590991365,255727637062,159773078512,467790014243,600706218642,553185003809,372579228442],
   [134872371447,85041657641,238074765968,309928422505,314213497976,275258549335,209607870168,
    116156655179,15272107599,184821535898,363116363191,485387960278,471598387581,269971799224,
    99148623150,522871161915,821492230970,821795842097,451835517350,194471490232,862902270087,
    1233290976460,1072179383507,373059890520,597750477816,1393042739123,1588590714260,
    1011733182275,130821587807,1311672193648,1923188769807,1592729401618,410394105281,
    1069081099773,2081451214484,2051163327579,923871308040,759861602164,2115421874283,
    2380393665716,1350325822943,466923712877,2092795196084,2604341104929,1665405126408,
    247159239260,2074112411875,2758745115098,1864565810271,137872151761,2105742371628,
    2873368727903,1948128999240,162616447884,2216319103095,2962266134512,1909328139487,
    338884676657,2415559351358,3016696613977,1727401413464,679502624834,2690730291207,
    3000428489330,1367187966195,1186224321057,2997637918086,2846196165971,787022631522,
    1835095871862,3250274436543,2460359570082,40815895208,2552116310175,3311830718664,
    1741664287569,1093224545407,3185370043652,3002865135233,627492031260,2242387338174,
    3490496610903,2150113822812,823900512704,3209121178601,3172363620452,697007872063,
    2341318584661,3580872083532,2020086729761,1146409105611,3418428535830,2965450396867,
    124201976986,2823392996638,3474091750147,1279024665618,1967023660018,3577705580353,
    2205198793352,1008265064576,3361457692871,2862594333136,68253971506,2930410344271,
    3265376039510,777126654083,2385009185615,3462599838790,1492889818021,1810394387057,
    3518791313096,2073873751623,1272020018523,3501264686046,2531418980369,819803804025,
    3470545934554,2880374824317,492713977957,3474026282542,3128222702153,322434545605,
    3539298181164,3267267104215,333608119579,3667530945858,3271508670321,537776737319,
    3827746409052,3101815466705,921457652293,3954510491868,2721520049569,1430982685649,
    3957105473218,2121946858361,1963966767381,3744697232636,1353026061267],
   [2378233247933,3271006159682,543666893247,2532632625501,2586686273012,113904760436,
    2360837380441,1868197714998,435332390598,1954042274455,1382201550688,369726484438,
    1594211963663,1352092630172,122413759950,1665414849299,1752023510742,170018322538,
    2409696761819,2143702788144,1057849399348,3606817042687,1736148392944,2972847590800,
    4400712689019,190740915665,5287800423016,3556428454689,3585972895997,6481258233460,
    267141905877,7080603141295,4812235061674,4816610724284,8241778667757,308456368845,
    9153891146746,4972450070521,7058608107347,9299590735886,2478682155598,11297450751599,
    3316072963480,10339964354664,8778295998669,6643170300729,12554883647908,1092901309784,
    13815340319347,5082347925060,12371299339574,10660136911585,8606824637029,14693775436804,
    3284763282948,16652613965471,2684741867968,16436055284272,8450298180515,14292606662565,
    13357739700382,10691304664944,17012614783723,6188125811669,19277224345774,1316222164876,
    20224301156059,3486929125166,20070715629038,7912430328221,19110450704971,11782530339062,
    17658829527280,15030797522953,16014596238793,17673725839748,14437656516756,19778191649163,
    13142417251289,21431793089230,12302336690498,22717985008167,12060262839367,23693055576714,
    12541818571318,24362661478705,13866272693453,24655165181076,16144969946826,24386889296595,
    19460259351779,23227317603962,23808677153348,20674884677037,29003160632899,16072308455528,
    34534640943660,8689863571623,39416166334333,2089346182453,42036362879066,16447592121572,
    40069507009103,33600116437207,30559352285858,50947953531140,10523024776233,62954614936609,
    21214940537923,60528443809588,60359111624838,32974257221939,92682757304469,25057486733407,
    92760677111498,101604531461180,31377433455251,153323181538481,100384767302403,98220091881286,
    231049032134758,126448162884354,153976273054965,353564516973497,247386011017209,
    165000535215476,667240051010014,1000587789322296,1038514390380884,832284617404588,
    530669989879662,267747816995012,102473229771286,26050718203922]]
private def rkmC_w64_m32_s6b_10 : List ℤ := pzigCat
  [
   [258393387,933791004,2352390095,4122053576,6662211589,9967990976,13934144781,18828955496,
    24735148409,31672980024,39961728673,49553291304,60878300909,73762940026,88270313417,
    104720031866,122615671447,142095274486,162802625193,184206078318,205774954971,226751998692,
    246294458275,263347722214,276388983201,284664799724,286731651755,281426176428,268027464851,
    245517640716,213886272131,173194558356,124203321887,68213445218,6856347517,57500073031,
    122235009644,185106572739,243172310848,294655679191,338078510622,372732334159,399581189488,
    419820797883,436219367642,452310968179,471566345496,497740017771,534090378472,582107864849,
    642425205820,713340274423,791429703846,871673497923,947682178676,1012604597027,1059981527570,
    1084079190261,1081459118762,1050228640597,991067568918,906777884947,801370108258,
    680110744435,548419655836,410803394187,272112540160,135987096545,6428997236,111728426534,
    213165440915,290471044456,335208535257,338970416348,294359527311,197439732138,49750644981,
    141277014899,360293557320,585942137053,792786434134,954107619489,1046194571572,1051837311197,
    962269209964,779900032913,516866534436,193982908803,161249475985,517769943140,842945809369,
    1103590070904,1268725881569,1310451871890,1207875222935,952009698258,550971732777,
    35837257340,536036912684,1084593571961,1514971896196,1734375118601,1673374937198,
    1306760241635,669370796128,139700388774,970090664257,1646887265198,2010729509131,
    1959344405862,1479506468109,660418142232,319468968836,1232604169347,1856780911106,
    2034886958125,1720326240554,992883287161,40906099028,887337064692,1552530917981,
    1789462895076,1552774604253,927812675050,102581120829,688964021385,1234758803184,
    1405231152979,1184477126242,667223243377,23761124672,555812231624,918940668543,989976577966,
    784673773083,395260449578,46018538836,410668113261,610293644814,617783122515],
   [464783769738,222106690173,28207261061,220940853984,324773856273,341886571198,297095836819,
    218377990422,121763578255,8003380084,126761032448,274113403421,399296139890,443527507963,
    348795012148,95112951701,268024879937,616995787660,790836906159,663970101984,220718018611,
    405000886877,958016957498,1163052564771,860953517486,112768582883,788065783971,1423692050748,
    1445825116275,767018451424,356776684236,1410234730529,1853452850550,1401600135235,
    205216718528,1182377675294,2056640266515,1921768936506,777368671759,837958473873,
    2093758128454,2297062192681,1280384708628,469037105382,2033253819995,2545395680762,
    1676949267893,146577691887,1943881919262,2703899956315,1960162874354,85120716925,
    1883597001163,2814279348982,2136027827815,198935732394,1893475466542,2907283090127,
    2210386354938,176941566441,1998582164191,2996654480524,2177769902063,3344588390,
    2207902311168,3073516195015,2016712610838,336153118810,2510288838427,3100978185348,
    1688584091879,848992096309,2865905765590,3011303415081,1145345966418,1520386769724,
    3193977698043,2707559759772,347619215743,2288788149141,3361867716340,2079558346081,
    698784221627,3015606125848,3188578706225,1046584812050,1889011147240,3467296987689,
    2488335790534,362972026652,2969926842737,3348259777152,1172594998953,1920930707265,
    3548266283986,2421273166487,607861206975,3168130218360,3222097388341,706502050754,
    2376381659350,3540982069273,1832908482784,1365019083344,3435278778941,2669838408652,
    302483936044,3012039241141,3193184702566,689423230911,2391163608507,3434554222612,
    1540874508383,1681167360681,3457595704918,2227982806827,968273546583,3338594504652,
    2757987459423,313866222725,3152791498892,3156420190731,239877453182,2966877598198,
    3452918946183,663863959542,2833631709196,3670615956761,935277696984,2788260220700,
    3817415202481,1034412362220,2844497732308,3881521038207,946526423984,2989024508900,
    3832432828727,670102071026,3177155969980,3629206567979],
   [230185358496,3334006656788,3239509106679,308578425105,3367563132442,2666393208441,
    836389426269,3198435001916,1977024297137,1214848278559,2806210787368,1314262007619,
    1325789302509,2276423632498,868413879813,1147608791395,1817395042860,793652879461,
    831219872839,1704636588650,1079127251267,714081423197,2132521278286,1436696814163,
    1208154191397,3005081048458,1307602302787,2541066739475,3784547532598,85858292805,
    4432682991815,3566094919458,2443117844200,5922964628027,1508508840912,5636384656968,
    5616802244157,2459384386521,7876057632516,2466021470893,7045960126073,7164772925912,
    3185771308072,9711709392011,2426207764370,9003504449666,7859525176289,5120145152189,
    11281619826530,800151020635,11568888547635,7035462408160,8588615884176,11871889280211,
    3119058101397,14091587272358,3487716677193,13226840498411,9741389513722,9556964138906,
    14394446898549,3914317827595,16679420928264,2602493699913,16376678796549,8907961076794,
    13741758230640,14136462865165,9350033480665,17748957054704,3917906989722,19546919212077,
    1853652065728,19617975857976,7387202882469,18247503836247,12283946169530,15823755393492,
    16330885609825,12757839530863,19478525052444,9426274201520,21800334875265,6139017917397,
    23448677398012,3130522051730,24616287812645,566131245239,25505911512144,1440184489605,
    26308637592849,2800755812846,27189837327136,3427913513963,28274038362767,3205701642550,
    29626316541590,1967927110227,31220430992519,512976158019,32892980191088,4511647631104,
    34282120807491,10300328348605,34763790667600,18049330848512,33397177142961,27667491424445,
    28898830341940,38554551699942,19682435646759,49216093783179,4085045115268,56704586722822,
    18933339924178,56051252777025,48177037775813,40430758217672,77575058801188,3470380842349,
    93651718226213,55067171505561,75848874842290,120546072316646,3147294950673,152961422821941,
    125849186035145,81784240102950,242124787383342,143782289346100,159560739909375,
    376362919374933,248786582311813,212022595707682,743616113589818,1054323775172050,
    1029128356963554,761256326808710,433801628471612,184341814606306],
   [51422594310204]]
private theorem rkmWC_w64_m32_s6b_0 : bWinChk 583 6 100000000 1024 rkmPhb_w64_m32_s6b
    679 rkmXsWin_w64_m32_s6b_in 671 rkmC_w64_m32_s6b_1 379790489 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_1 : bWinChk 583 6 100000000 1024 rkmPhb_w64_m32_s6b
    671 rkmC_w64_m32_s6b_1 663 rkmC_w64_m32_s6b_2 363985872 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_2 : bWinChk 583 6 100000000 1024 rkmPhb_w64_m32_s6b
    663 rkmC_w64_m32_s6b_2 655 rkmC_w64_m32_s6b_3 372262316 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_3 : bWinChk 583 6 100000000 1024 rkmPhb_w64_m32_s6b
    655 rkmC_w64_m32_s6b_3 647 rkmC_w64_m32_s6b_4 397170607 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_4 : bWinChk 583 6 100000000 1024 rkmPhb_w64_m32_s6b
    647 rkmC_w64_m32_s6b_4 639 rkmC_w64_m32_s6b_5 437798037 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_5 : bWinChk 583 5 100000000 1024 rkmPhb_w64_m32_s6b
    639 rkmC_w64_m32_s6b_5 632 rkmC_w64_m32_s6b_6 277036892 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_6 : bWinChk 583 5 100000000 1024 rkmPhb_w64_m32_s6b
    632 rkmC_w64_m32_s6b_6 625 rkmC_w64_m32_s6b_7 375404342 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_7 : bWinChk 583 5 100000000 1024 rkmPhb_w64_m32_s6b
    625 rkmC_w64_m32_s6b_7 618 rkmC_w64_m32_s6b_8 318943176 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_8 : bWinChk 583 5 100000000 1024 rkmPhb_w64_m32_s6b
    618 rkmC_w64_m32_s6b_8 611 rkmC_w64_m32_s6b_9 306041722 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_9 : bWinChk 583 5 100000000 1024 rkmPhb_w64_m32_s6b
    611 rkmC_w64_m32_s6b_9 604 rkmC_w64_m32_s6b_10 306046640 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6b_10 : bWinChk 583 5 100000000 1024 rkmPhb_w64_m32_s6b
    604 rkmC_w64_m32_s6b_10 597 rkmXsWin_w64_m32_s6b_out 314564245 = true := by decide +kernel
private theorem rkmWinIterSnd_w64_m32_s6b :
    RkmWinIterSound 60 1024 rkmHbWin_w64_m32_s6a 679 rkmXsWin_w64_m32_s6b_in
      597 rkmXsWin_w64_m32_s6b_out 3849044338 :=
  rkmChS 60 3849044338 (rkmChS 55 3534480093 (rkmChS 50 3228433453 (rkmChS 45 2922391731
    (rkmChS 40 2603448555 (rkmChS 35 2228044213 (rkmChS 30 1951007321 (rkmChS 24 1513209284
    (rkmChS 18 1116038677 (rkmChS 12 743776361 (bWinChk_sound rkmHhb_w64_m32_s6b
    rkmWC_w64_m32_s6b_0) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_1 rfl rfl) rkmHhb_w64_m32_s6b
    rkmWC_w64_m32_s6b_2 rfl rfl) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_3 rfl rfl)
    rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_4 rfl rfl) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_5 rfl
    rfl) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_6 rfl rfl) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_7
    rfl rfl) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_8 rfl rfl) rkmHhb_w64_m32_s6b
    rkmWC_w64_m32_s6b_9 rfl rfl) rkmHhb_w64_m32_s6b rkmWC_w64_m32_s6b_10 rfl rfl
private def rkmC_w64_m32_s7_1 : List ℤ := pzigCat
  [
   [261900301,944831588,2372858797,4133643882,6637566273,9871109966,13732760639,18508439482,
    24277051211,31027963804,39046544421,48251419712,59079525001,71377096370,85238053765,
    100984033408,118082921971,136690785562,156498340053,177073252282,197972022637,218478243968,
    237810461867,255057545046,268894630657,278633725550,282795182827,280255216378,270319634835,
    251952483446,224984235605,189229508544,145159257229,93671533102,36042576225,25631098481,
    89056459946,152255550513,212402792394,267488744271,315733366116,356001026867,388312659610,
    413150339271,432540557824,448976022697,465577881694,486071550537,513618313702,550673220239,
    599098739286,658589967331,727696391732,802848821391,879107827428,950724813551,1010906455038,
    1053731397867,1073926714518,1067785679171,1033915766172,972739145171,886786127952,
    780521478321,658498630922,526643201587,390168592924,253586992969,121560627638,2209251104,
    113572705925,207485116192,278200967301,319011405220,322734338041,283489235294,197180634405,
    64227089436,109718403250,312751049573,526847232886,729673353245,896911832388,1004855837081,
    1035006990234,975774456567,825366696384,592343780607,294023767218,44535503458,393203288311,
    720431297920,994059363901,1185011734830,1268220435205,1224411501614,1043862770339,
    729096232718,298867953345,208281713413,734246097872,1204965568363,1538749083644,
    1661728068459,1523739642132,1115468751449,479904065676,287196917508,1048890988273,
    1650793199262,1955591782849,1876619018520,1405660284593,624008429200,308833596126,
    1187189868859,1806501178910,2016301518933,1760428747598,1096633699931,186292378662,
    745250482662,1466585960691,1801119836318,1675615287673,1138379586060,345068673369,
    486087705879,1136381164906,1446556101573,1357954516646,924601275549,289834405158,
    359376706742,847794724351,1061155867478,973279839173,645601316894,205503202331,192231542563],
   [409060392008,373483583979,142730874172,67223201830,9526565113,252232314381,204843627540,
    350030820480,501096439563,128978039631,136961393105,700895677124,655257316622,68457883655,
    300428726034,182873500793,615137768476,1420630602,195691044058,326028999344,484039744585,
    682382237834,609170811889,345471535284,15830765256,250633432991,185242379320,121485863736,
    333745880775,214928252362,104477975029,390314593462,369628314375,275108221413,416191969819,
    1080237665532,1400676912872,74794452803,151903647704,666560189942,1714023483080,935695205410,
    72194112873,79004277626,1443537033626,1804009518766,624178414926,373465034238,1095550122162,
    2264057696008,1206261998342,658557913456,761364596570,2609465567936,1798795881980,
    789813836312,559559684382,2797811664572,2086265677564,1098445576066,163763944364,
    2829249184138,2495631962734,760183156922,472907921714,2911331439894,2443650254258,
    1273165660784,147446253139,2694441307826,2695210715498,550110665514,1146228671350,
    2764779995668,2899444713316,840552900236,1181488614702,794885157060,2908013589150,
    3865803634410,1826876807042,1984742289605,1746964326547,278051195987,1537937048905,
    3252489479901,1750975758803,926023345555,2233139189617,3062642743075,1648046210835,
    1648488554853,1251560901717,3422314306581,4600464093797,1060799312577,1765822436378,
    1506901858770,118016709408,3361069939784,2660459233688,826012523098,2138859012268,
    3702443034836,2077776766736,1641869034162,618489526550,3303145223126,5068759644972,
    1054539220334,1716930693749,845165474221,812659248967,3251312059595,2381012160219,
    527052681361,3384480060513,3126227044725,898618074297,2473617968275,3432986843413,
    1503053569709,1436439442713,3117832372403,2029766932405,2637231652913,685751625568,
    6225711297635,1999688085791,2011646125799,335726609659,3263342197458,1899947127816,
    921701230008,2224048952766,49331192335,2337591462947,851967424709,1782307864757,
    3644708164839],
   [1572035921863,1940724638295,3884764210181,1690917012513,2054333172107,3958433509765,
    1671503434667,2305687115331,3911140447231,1573355415803,2681320893477,3719708386089,
    1477543723007,3005870424631,3656725856379,826096407537,4190375531383,2316664109861,
    1488492286857,3176419019919,4241496255357,514903841714,1903023531441,3871983687291,
    1320945352137,421905703226,572763101831,1316115068123,97559914303,777223835446,3092461487304,
    38042249718,2486255343461,1206733947782,356706816713,2425540814275,2379751087290,
    423327717138,3385689890655,2604755375352,1718952807884,4586492129369,1883263118486,
    3742205000180,5118444919445,485528689381,6983719163872,6625965321133,84318535324,
    5058125549926,5937518765739,6390374521554,5962611602447,5308696424180,9684315494313,
    604959516808,10296804992479,3131199066854,10559851332081,6064369939270,2347329880798,
    437611060418,11726488612996,2643508209888,14791516349715,9859907806450,2364825048252,
    2681763383526,8631968280825,2099664788911,13418930026076,4696488510047,12173334534496,
    21455274991118,8669070721449,12290655126614,7721564654264,819943759193,2974325131324,
    4204845664760,31213532686139,4194350956008,6442513224207,15377509745598,5120900945115,
    11962812278404,9263935192934,3120579661722,11024825045876,4649551656034,7319845445206,
    32940067207494,3201068562848,9808375146916,17326764261977,16158302215611,2310917502870,
    27577374457835,11392264066585,8276339695421,11902778681266,7907014689600,22550007084802,
    6420477063378,22396406043894,28243347384498,13530933487502,12716653274215,3676226573169,
    27554108372753,30372787491675,8260021505013,7726109975364,24359947630836,6274576474248,
    40941742162778,22953566004072,15987018626356,17210134734103,45517028753475,6867111500899,
    39498092153530,10015584050196,42012314346033,18173149372623,42695826288848,29139995951872,
    40691141120447,43121670733405,33791507291954,59373099002774,18980881740233,75322487063727,
    7048350279953,85385226211404,45736616475730,76892652156185,109694049024607,95240687068102,
    35744995938864],
   [58249665063822,181525772720652,43800067422578,183764516448130,210107654549362,82113282569686,
    336185995973430,322140732498438,130380656724672,513605587586596,998584583059084,
    1130540321502484,878485885073582,479007147115072,165196794724366]]
private def rkmC_w64_m32_s7_2 : List ℤ := pzigCat
  [
   [268354456,963135969,2405998986,4170085851,6673273250,9896490381,13732057142,18463163865,
    24166796328,30840176199,38763638522,47840396469,58488000596,70543693415,84121101072,
    99546423895,116304083320,134556779821,153994389392,174192755773,194737716460,214966480033,
    234157790566,251440582905,265513970218,275725021499,280635660302,279179443843,270674420226,
    254011243059,228946899106,195237400459,153311954656,103947814511,48197919704,12076653142,
    74708803063,137714590936,198299883701,254571350532,304713214071,347329199254,382079194363,
    409161581774,430319043387,447640705836,463893466925,482635622570,507073905269,539871163690,
    583217478251,637385507182,701661278709,773251212446,847973399199,920574087836,984523841955,
    1033940311234,1063206400945,1067848213026,1045538932785,995811020032,920186552625,
    822305631856,706547236699,578666693276,443963107043,307589875672,174424803123,48334649954,
    66444924714,165818315069,244984644502,297929770637,318564395930,300851415931,239633073986,
    133628293991,15115133467,198716542412,403163180603,609759401420,795795981659,937785621034,
    1014613653749,1010293651854,916852973753,736111934824,479335797737,167085142876,174063371164,
    513427454507,819140150722,1060917049069,1211766928134,1249934949897,1161574091594,
    941769836099,598902661316,156954655161,342829477781,841629787810,1268266344469,1548333474446,
    1616249136677,1432553154172,996740015809,356688828572,391241724186,1115181540613,
    1670627192730,1931109286673,1820615829168,1337248077503,562227430510,349704631386,
    1202233546121,1801073804074,2002217933937,1751508778448,1102655002527,208083476564,
    715844869388,1444370948911,1801725413338,1707913437449,1200419811580,422829741155,
    415492809065,1096404224520,1453596516229,1414999465214,1018088560383,394044413568,
    274529990194,808084939463,1079275581558,1045662311507,754153121878,321284330537],
   [104589631343,390098971774,460233976715,327446449788,97081711215,75242932253,79890523442,
    40081742968,84812173793,107078262775,394754027776,401321428065,38626451676,220785429466,
    73482039119,72831282062,547035371847,550942941464,127042299882,10917894361,354482668921,
    625752233713,822090101736,211885046639,838639419480,43094940251,68041972754,458200882192,
    64689487236,155022537558,531423161516,278960897403,326601675918,89066483323,200975957298,
    268628553991,157047587662,41562428784,49572103649,203829369150,670122995843,393075386794,
    616385387502,91844619437,981336196729,463533016101,765928113112,975220753062,199935571480,
    471931713469,928022777690,1506842497940,1185214154470,414369983917,399947855904,
    1121218288186,1776700897064,195702560854,400704281748,1127469984652,2497280439002,
    514039546968,513942452518,1145999549094,2804391685098,1243305724772,204459680610,
    1305302570852,3345812591420,1036076490790,629077273642,1296260333628,3074470546156,
    1798302455200,265518135057,1960628960174,3077189240070,1785395849426,12355495813,
    2372542242312,2207098214940,1373514011660,936796828216,1561587454736,2166255832040,
    3192699857658,1923208278308,410375501645,509290732398,4194470987076,3897801861186,
    1092772746322,90875365552,1076433825286,1188036812783,2073607277247,1769236545561,
    1718479627601,947300134417,2663774634787,3118432669799,2021459656049,748881268154,
    2442451533469,5219259686569,2903454429021,907285748985,2066249827217,570580054068,
    1877586628198,1959490404062,1708504810232,771220694350,3053112414958,4246420197800,
    1359953729314,478955630521,2762025617596,5178418119492,2027082785758,1776809378336,
    2101473762300,1457205150161,2175828121251,513716241239,1764540626519,3711380489667,
    823956314031,3207962995741,776514209403,5232326352505,11882396562,1862654486025,
    4228134633501,1405761421651,1677459062695,1817372838057,1542219433147,4425388531069,
    4414198517443],
   [703416776277,251619626281,223862475036,3301991243032,2125511889396,32072232066,1389497822330,
    678313792191,2752541489377,725499049875,2288077433509,3501502850435,1146934056431,
    2869193386653,3365075782293,1320963854853,3175012832901,3334201289937,946451002263,
    4373647470285,1907137726175,2294481918107,3460195082253,2899045392243,972541202887,
    4653599076337,2747480938091,519957277311,3613053049261,4243742659301,1522328280195,
    948660677743,3475349101531,2498102677651,2012068127137,614271967349,240113342894,
    3251509251875,928596232545,3603808945848,200687618479,367667826247,2794913856852,
    2389595638813,2271772169279,3740533628904,1653176605993,3299039161509,4270611523146,
    724451501026,6715689879785,6434170637108,621171390166,7467901829581,8496913309618,
    6043803900519,5319068171480,6324460922091,6300770961840,5955887080307,5824918502186,
    5310132760217,7492732324910,5773394310021,2749521707563,177283173936,9577138569189,
    5370988442713,5572521784880,14020615117699,9486917740622,9449131446616,2463427574578,
    3583270729245,5375246569289,15118130374876,2995099027833,10260335467923,13358348227814,
    12996425577329,2666281196684,14947629202792,7388854991206,1057496650584,22243723316632,
    12738063187425,19492507538514,2866951823264,5196275982512,20073062188581,8929492815887,
    1218620870766,4563442626759,5496807980558,8549747283202,1328554871793,22544049285668,
    7190138720505,8368471685712,11877007970702,14356237183150,33293426587476,7050565989813,
    1661246642131,7373209391279,5649175026869,25347497820375,11227266387145,15557016072257,
    5219591348068,13432387326134,9545989938788,5024793981246,35331038537550,21190853338208,
    10282790301018,10354239332834,14183395347157,22039031705667,39594643005425,4601682998832,
    3065754525799,11645719581832,22608799703424,27774306700784,40970216406562,11679927778088,
    43314415849169,32920724170851,28243878971008,29065559010414,31549114056115,36861678960671,
    29336539801844,45547409354624,24548406864017,56255312875617,15117266950426,67983467239654,
    1420814935304],
   [79162210821787,24218665646693,73265042368170,90245579469354,128985148232857,39903578690897,
    47938582304460,27571090543729,154530611901376,74986651927762,78606900956508,249439128250612,
    72432655049928,187066776322758,397262588959760,147996388025238,218143820679170,
    729998276883492,1137592504269984,1087184097935034,690767246116690,269468271857272]]
private def rkmC_w64_m32_s7_3 : List ℤ := pzigCat
  [
   [280662741,1001759872,2486706189,4277991394,6804507441,10040068578,13873298761,18595980748,
    24276501321,30905879944,38768662867,47761492308,58299383673,70193734488,83559849623,
    98726961230,115190463667,133142549076,152264192545,172135832784,192357399347,212294254632,
    231272059349,248462222472,262622727157,273125645978,278536909119,277834310934,270351163179,
    254989986172,231468307643,199455622346,159291279993,111666976426,57551946201,1326925015,
    63009515016,125658606823,186500147476,243596543369,295060857798,339452864397,376304241570,
    405488696617,428341298348,446624678103,462948680002,480695684909,502886494958,532248625343,
    571311929138,620831165325,680617356680,748465567985,820908555654,893290356149,959450526144,
    1013594979615,1049894416680,1063442947471,1051213957684,1011864064163,946022155784,
    856524064177,747291743724,623872603233,491541816152,355783152905,221886805658,93952652569,
    23766445823,127333891618,212566795965,274475168506,307684722807,306542194890,265791624289,
    182716123838,57199347419,105760837959,296109572316,498584216371,693016282974,857416457757,
    969599403928,1010657560731,968472437752,838784349673,626854707284,348007088871,24519278970,
    314908485482,639139074971,917378840034,1120919734891,1225922862518,1214887661045,
    1078520958054,818157197985,447798298376,3924081388,492157115327,958397745792,1334510329945,
    1552646268902,1557642165901,1320393408682,850451100559,202811225028,525299009698,
    1205753844169,1703534544328,1905086739397,1746486379734,1235577205889,458086649908,
    434504178726,1253012107837,1814277254754,1984822481713,1716971611384,1066036099987,
    180746344170,730405915866,1449632905343,1806135218056,1720436390439,1224827341110,
    455834731511,383860629291,1079793022144,1462950073443,1453962297366,1080536407957,
    464131597270,217128427996,781886037937,1095211592240,1102293468737,838129830174],
   [410491846331,37435244483,370728069506,504821236713,431216856704,219486632073,9815781977,
    140784415616,128766394019,36886830220,740845753,109771827446,289278629343,327625108404,
    93849864129,257633380235,406750528236,279164685875,178775920272,291986076707,282208981832,
    137692914588,508646360045,385859005172,345436303399,764655633510,642136769267,212509487373,
    290839575334,137436828816,277991054512,130573506869,741865024479,315110935614,179528654453,
    401282941172,190388072768,325042225128,35186397192,228895462080,487854187608,113838651175,
    521571639060,81454477639,197246572090,259328990642,215470818963,188222540005,356895104170,
    394685525510,562536492023,398328452967,122483349040,1121898295556,106909480881,796706329663,
    965890222701,871754196592,543361167236,4479212330,793102009433,996946484296,1258860566682,
    1264267914234,630076577051,579710596460,1372674478636,1355153040868,242635276711,
    426927325108,1572938337094,2316121497720,393529148867,564691942872,2285774732984,
    1964926324150,628897244410,93533423804,2816643046784,2275316572452,551979289362,280146532896,
    3337105638150,2083085752278,228612396990,1209789352336,2680364116968,1763184042376,
    1284689331372,1469466696360,1790505957806,2132529178526,2106275664756,109321653014,
    693600066474,3327960411768,4096394993400,128189358824,453860003429,2409462891752,
    2625112040738,2954784954062,2078312814328,2318523722062,1020329778364,179310939654,
    2142932834651,1682968905985,333688084304,1426510194063,5001986952621,1585933950867,
    147283451654,1828787258849,2388196545929,3248823779999,3043433664085,2993128945181,
    2754082821573,110089437731,2086498564478,941727520714,999928906067,2892356230278,
    5010517260602,983251452528,622712278488,2509836051914,2315570532748,1821614861492,
    5909196273316,1045676068116,2466628597702,1519109497031,1166523992420,1702055289753,
    3590456384815,28899715650,2210183285213,3748716154841],
   [1623169200395,2117113988415,2334230914077,1915216693253,3672980781467,2497324325815,
    406964265750,2025286100809,4056078003057,2526519352873,3932293212511,3421711379647,
    777633963710,554870919332,999100150292,3452709242472,725013114086,88605608075,801361518146,
    1993818049169,2247188216509,492091359285,4129021248565,1351154745299,2441020101281,
    3217544873941,2319899846849,1725070084561,4312237050167,1589524332233,1961887807215,
    4562300360715,1902872226705,1417186224265,4027139151459,3855291511415,618919759653,
    2640728121141,4015008629821,2574570603201,2692611435379,1185402343997,2507223236883,
    5132238231949,318481879377,520588382610,4628295393079,1081417119683,1352507361598,
    2772462697303,2171970609042,3747058196652,3122387592575,1529813340575,5857926557356,
    5581935266237,2313259493369,9216204242326,10476574406263,6591806553688,4049217898691,
    5244252508578,6936971380495,6329164804808,5240618030819,5461917782610,5344250080977,
    3528384329392,93036137061,4326853007423,4201586686334,2779284132962,7627773433687,
    11363684726680,10131456886167,4648487946829,1639368858478,8367338854379,5517505785895,
    6702317231327,13502487282042,9386061025012,16356551435059,14414398143676,200970230327,
    3297615188485,6299658941398,3277428328094,19537738014403,17582938143250,10591627482493,
    15603383114936,7088825385780,10439951464550,1139885916925,8918734750504,19485156161442,
    858722115847,9731329049419,2120163994939,19042429318091,10164643240948,8761078645615,
    3206736223578,14825363991016,633678176013,16294986357702,10638293563401,11888273534536,
    22397339822344,24935941274794,250548703419,8917018450660,5106175176085,7476249561119,
    16088823871641,20581360213327,19720042929771,12177108063828,731981160566,955798644233,
    23694533986458,18498465125136,28421074514976,10205719833742,24642177698796,20659256690911,
    28553761033753,18976834594605,14526231494427,2925951422116,6147074843874,13954348207340,
    48973679776946,45083471938582,21300533758541,48190699929353,8509486802262,39179710128948,
    15784484850307],
   [48256757996261,11707049998388,54569548283026,6447507313581,62454609978611,4106343155647,
    73836321351968,11853201651026,60771642442951,78619880466107,133529408813434,35357640441760,
    106971929753133,25116838042898,74224356325163,52239256275838,123698650304300,29341046613,
    210485350705676,146898161426794,47102970538266,355828548442172,272680783623922,
    82731953295708,399742710391620,979844430070736,1215438208553830,924190759283002,
    414031238880236]]
private def rkmC_w64_m32_s7_4 : List ℤ := pzigCat
  [
   [407651640,1170310937,2500288524,4494691009,7019013292,10305677581,14156354208,18896356799,
    24586577748,31210663521,39056335656,48005444007,58481387498,70273332431,83500546112,
    98486523783,114709744930,132400486129,151243010282,170826368279,190756104156,210403744883,
    229125073450,246130770941,260232426020,270845286577,276539001038,276332729007,269559376272,
    255120964989,232747338408,202067713815,163354590188,117186075875,64443687848,6777134931,
    53978933549,116091040444,176902331453,234539856576,287030948273,332815283258,371278320323,
    402169896740,426613238707,446024951952,462695137223,479809210052,500345673529,527117734074,
    562748335369,608219795648,663853190189,728075388324,797987578487,869354785182,936429586383,
    993741312878,1035406125197,1056159534446,1052414411607,1022154302524,965278416151,
    883847917478,781177593779,662475538372,532942445343,398278597696,264042786343,134630311060,
    14503827447,92444037119,182362485974,250931128523,293496371872,304939517337,280281855510,
    216258115967,111195846266,32172812164,206655348881,400202344760,595616490433,772779690952,
    910007249989,987108409774,988582595141,905678552242,738479687801,496690609212,198166622293,
    131587447009,463312255506,765841229865,1009253978758,1168031912177,1221635981180,
    1157238877039,971361841178,670763140725,275297823830,181167891346,651849401867,1077815672794,
    1395287091239,1543914202084,1478623369669,1182401998096,675585978161,20315127822,
    683528159628,1312417536145,1741150411016,1869653226987,1649396788302,1099869736969,
    313539442240,557965202692,1333335211427,1840910109896,1960499221329,1656096273864,
    988415607251,106534207240,786270252906,1481223362031,1815481089022,1714965718395,
    1213865247000,445230509605,392529399863,1089577810636,1479050696659,1479536627746,
    1114147278715,499503596956,190720631658,775068738269,1114510805214,1147577054401],
   [900609399806,474644769869,9984047142,357438038214,535739645463,502979694110,310551555289,
    60493970800,135042323178,204607855301,154062271902,63943092025,36506355086,112988795907,
    219547964372,210568826935,3622802734,303149119720,480610962051,391638679216,157189743695,
    16568383388,986684491,120698205835,450723877618,693376660555,563877372866,296566133859,
    248918278266,184189947199,236831975181,489924011886,3274148631,498797449377,295061929342,
    207974581463,574060816736,248224550271,352207433817,89207778921,310609149876,310518924720,
    178079862383,157827903278,638380912605,33998483890,102325131066,35714942986,321480294444,
    119251965954,136186015176,313746274292,459856883768,220773567277,425717537804,328536327800,
    405334772176,621460191019,125355206754,331029598702,761006943182,822097836831,566144089395,
    6593655119,1467215656702,167882390349,614005433687,915399903773,766696231278,464269262190,
    473304231321,1011020179253,1031036299226,1091516447650,827173650582,708991858767,
    815716045922,2139655569346,51181585912,218848705425,668628517484,2445987450392,556537974618,
    167069084763,928685140012,2965837559974,781755077220,395166737939,2011543552732,
    2857057533520,465233982522,545477193510,2264033554624,2276533844092,1030348607064,
    1392903576058,1281353959668,2060959606782,2060708399868,1405665326610,474957158638,
    2403813283822,3977611233754,17382764195,299545327311,1927284951444,3888933205906,
    2037704820336,1102215748624,603411825230,1438971249206,2405241137082,2294380087504,
    1721125537300,4474815854176,2426500917010,1957485852693,19372587750,1016416954988,
    1006783923985,2776972531923,2936910868555,1330478845785,982600384425,1618489784917,
    2247663472201,1483164528673,3324771843039,5972785419129,1507776277731,1002855120166,
    991007747031,2417460447241,3832387976808,492808547756,3949629703624,1310728763386,
    2084569690814,885378938466,1134252394972],
   [5437903790202,2799582987678,1693483593940,3767447904838,717846257606,1279768840935,
    213416717959,1367730632361,1881474487545,1663953945631,3460062784331,2250140137185,
    201118276821,3464569020477,4137224424371,1066243038935,2108429852295,1752033469801,
    336171714389,4036657257819,4226931253627,2589669740153,3610847993973,1280929480317,
    2194987062676,244345118041,3198995751028,1324746764068,69233259686,259269153706,572733560287,
    2868686653121,712112695415,2338028079319,3677173013885,931638010807,2767320791835,
    3843843891883,1709896792943,1570760703825,4629425788439,2560665520595,827116833143,
    3871711846663,3361522753375,2401063040425,2570748864225,1357048640381,4275277660605,
    4449936564641,684990808010,2695077551307,6143175798097,68211621974,1801741052269,
    4141704104539,35692823928,497162653319,6761130294277,3312080287646,5071748340362,
    10175991465297,11933155710222,6697810944287,2771851307332,4291923018795,6601453894484,
    7411097362875,5091357407820,4024828145209,3970332025844,2580225802249,859039188761,
    3384730467028,2537689018305,2268355654687,8947684119952,11370781932083,6545738453602,
    310080693798,6160722938125,7768718041144,618265430789,86340373957,4923173652061,
    1713490015131,7389361530494,26562201381681,1619353625134,8508540617854,2416197230559,
    1458129594587,15289513197026,18732165887481,19646409774658,4703536782937,2451446094238,
    4104114305061,1225178362089,3529008192415,3319311506840,16605550001236,3829448713088,
    5061019790391,22230884438674,2352460337380,18247156713788,4579981287125,12832080489217,
    3354538442620,17386404077493,6048998747064,7921914168295,10172415660866,11359564635156,
    6512547049318,12499242282365,15186629435566,18456162886476,18706656404010,12327081259896,
    9359968412386,3140686217503,5049476429434,21077864502201,29397028129953,275173269321,
    9955202814399,2534602233340,4310825990859,27388495363032,10451027242040,24837530891356,
    33925166493862,6080374976606,11224391195497,24911420442741,24719567016327,4607809595631,
    6423852886211],
   [9825458458931,35738246043038,67843964167060,12289940262934,47373238842105,11088627624177,
    40957662478722,675828079600,53072080803089,6185875094051,56509818129882,13045923578274,
    70406402811251,6020701139583,46152163005394,73439937993120,122320631411267,39840786938083,
    139369737436538,43266436501683,14826453438444,52571087844643,78547250545119,122040616682796,
    13185279061597,94904354066264,227719835054432,3943858359118,207920334260460,369188021478774,
    124051329474054,133863480121398,690997463455082,1214353423911610,1144893236901462,
    599875857894932]]
private def rkmC_w64_m32_s7_5 : List ℤ := pzigCat
  [
   [454477609,1289808048,2708796141,4771822742,7308197459,10629934940,14568265687,19426522778,
    25113753403,31668400694,39620061963,48617607588,58970085381,70753089272,83953745775,
    98704996252,114868361423,132264517444,150911738865,170198649662,189862230387,209224232998,
    227671989959,244425480524,258343110429,268900726596,274673290465,274725607152,268392992235,
    254565792328,232995759463,203287726358,165686061455,120693833106,69110677225,12496430114,
    47428164110,108987379035,169588274866,227460392751,280630655658,327487402515,367268773266,
    399551352909,425294256902,445715173547,462918709212,479828706869,499215900466,523922133699,
    556725241686,598857854499,650931406982,711734400835,778915337286,848771416665,915989378156,
    975290640909,1020775874660,1047108936621,1050399968652,1027989620719,979045557074,
    904991407609,808649528284,694800538273,568368931482,435139990999,300922962062,170421486135,
    48350031284,61364361762,155006697877,228648580384,278216337825,299182864356,286998301667,
    238262985118,150477160391,24835492486,133793177116,316092137567,507620427862,690436268185,
    844036335058,948156633271,985420587656,943570050617,818276529152,614328588857,344897195718,
    31785164017,298109702867,614563222754,887124707353,1088402954816,1195500067013,1192614916858,
    1072284099777,836445696218,498281374467,83079316522,371404715282,815445676617,1192117463284,
    1441930090367,1513121414810,1372355358683,1014417080674,471251632193,187105549809,
    859197569330,1425880265137,1772993946930,1816341781195,1523228118816,928065977375,
    131441745882,714412331808,1435174214545,1872860084364,1923456210243,1565378304934,
    869891925471,11485351591,879748289168,1535039103587,1826760987564,1690776141233,
    1167540106490,392095277921,440805901575,1126400425514,1502918652393,1493143095496,
    1120343377129,499639385166,197229087088,790776096401,1141292576144],
   [1184407457627,943237100942,514150194615,35582113020,355627400836,563536191179,557971255184,
    379024430517,118937892058,114523825550,239524941207,233865031352,143510455729,54175460182,
    37118060357,94268835358,145898812455,86755020496,116624028802,366461060461,484487710852,
    363032249613,79825750160,164708241082,256807803215,292062414572,426288947923,610678752864,
    601014641187,302252626932,34710902268,137457849271,101122936726,146374932627,113418315422,
    269291909758,671092693491,510748265286,43374603157,2938973017,166032356687,94375385405,
    317625645726,32177963138,57518079919,557334253831,495556088788,144313466664,50815421177,
    33389436673,402287262997,60880525764,269165792138,250270299538,128855642035,114543178312,
    589163210657,103152224138,43917211709,257324875696,349645292007,562748694792,192324431860,
    369217804546,429082376371,675355276798,446364628678,582319514240,912853569165,139794427370,
    708613584816,783733208286,790870271097,735496702407,63089542913,1528774050156,154158474013,
    737676675975,352913283169,538394729576,860930508412,1593642485363,491413158917,838408591198,
    1191317692004,795423026161,100780560830,1454380295926,1591344283962,535831372401,
    366379928935,2110886409024,1675556995080,937154500725,545926969814,2541513423052,
    1212680696136,408197230137,1581692587214,1984431020020,1326212568622,771231553386,
    1313817904948,1742230376454,1773247376520,2224855329072,138895453947,1866934619770,
    3138296238218,1460971807902,541496348001,2119794008770,3690594435472,2077789385362,
    122408842756,706495921550,1449939275780,3530022117128,2419818464092,52219481129,
    2554253871636,1924761158360,478095255495,1993533195658,4462082384236,3592659498990,
    948867782186,676292349810,1342586894128,1114469453902,833947345089,3153336808197,
    767008756309,1897480610085,2550243694989,1904038772625,2782275472992,5630051848765,
    3724167041101,3271748607411],
   [1825270023825,1709275365647,2541016374187,554308722368,243262390433,1464655409670,
    4527711319640,912550166222,12036803902,2843232994764,2007375979248,2207028559026,
    4243846995298,3216765843342,2484424296610,1957463243484,820405635539,127483286013,
    804211309772,3253090851033,3056350574285,245664156339,2608763990433,2293092993705,
    2045701547347,4214670878021,2394687859071,211631469500,3130030153465,440811642399,
    3401371580019,4577855463729,3325410927981,2753904831609,2244481075051,1598589722998,
    978554500378,1006323259802,3003690729022,183087572053,454040956603,384369456554,
    1778770242379,3108133866167,654509794041,2060514191767,4464894077399,1263921627303,
    1692380625273,4109581756739,2412610346887,2591539918427,2275888770739,1922028719449,
    5165718226905,2569337328583,918128105290,5763407503563,4074494785407,214070002362,
    3196735427451,5177630319905,528348902412,3414144202963,8569810565973,10641800514594,
    14056555730817,3448483624596,3826526300619,2426401535372,6320836853039,8494379172792,
    4730570357731,2845258414870,2070048327053,1337196335616,436919934464,3051544876525,
    1202069201248,3671571195070,8957335541629,10352955358080,6185011121531,1837671993777,
    7487053611302,7041920071365,3226779612124,766667276908,2377778105787,1064519430008,
    6377811431697,16785438853714,12054464591149,2523423601203,11228254125874,1576677706615,
    23571608470919,12807412315868,20093699884629,11030217885848,940398826120,370653866667,
    215888565421,4794556344422,3972063410588,615598194873,3697389034384,1647855839389,
    17864846466381,18181925949036,508263668237,7256007031088,4679416323044,1642429848863,
    27640034025912,1277530096364,11611122148618,7796366047031,3816437152337,7021442594397,
    4137375609315,13550461988591,15234368475174,10671938924788,1982236255435,4350191490587,
    10816289644740,10245686915238,25258028739136,12132516706882,3316039219112,23300392226784,
    10799635216187,13816418537509,25735524233613,7984516636,18049948138539,5012074579813,
    11952468853378,2410321028296],
   [19013800829280,32434165466280,26490755878028,14287194327750,14690983058951,28296750404407,
    7702757798025,10166841494693,32555589312541,5844439131562,70986700033574,45155929467234,
    32835081702209,24419230937989,38569907800476,14578058799950,50717531670175,28174941442061,
    67080684261048,4837182014388,32462503344713,71135301855723,101395738358762,55081727911916,
    156516207983079,54047723895784,23954741338738,18968783632156,40587490340764,141916468886231,
    42260962478806,25285044840670,37188202322403,227224650943262,68298207695566,47975905300310,
    344933443154868,260457456906486,22276046461292,356348065758730,1064068409613232,
    1309823327434522,820926364970042]]
private def rkmC_w64_m32_s7_6 : List ℤ := pzigCat
  [
   [502143508,1414740343,2941516752,5118641571,7730422646,11113512877,15096288400,20037117323,
    25824940826,32455094621,40452929314,49432883281,59809222094,71655199647,84835570544,
    99450989079,115475419516,132778247209,151233030004,170182093377,189617198624,208744219351,
    226804581948,243287967889,256986159002,267260764701,272960819156,273072211745,266857038794,
    253468602447,232308351978,203319440945,166462322480,122383398439,71710254536,15997346563,
    43179077973,104193802236,164504502847,222423207166,275973780807,323546810106,364322404083,
    397741071976,424586823377,445869452194,463572240499,480462073546,499132499231,522351673560,
    552899365295,592181722530,641149056147,698929928266,763538750251,831609774376,898264331079,
    958594262866,1006785420305,1037403328118,1046260700283,1030300919368,988238062689,
    920866269808,830396435857,721165493716,597919470321,466485317354,332675655173,201395225980,
    77714420293,34238638269,130808522278,208365261229,263253246768,291410037391,288761375714,
    252051649739,178427499188,68112646753,75765182115,246087101660,430837757595,614332902184,
    777649229139,901081161524,966388362139,959071283206,871404362819,703849772026,465101712421,
    173060679046,148211466280,470009565537,762178074702,996201398247,1147069547192,1196333235141,
    1133176880182,955563036239,671881204220,301214850781,126160206251,568420787882,975517433891,
    1291995585688,1464820594511,1452038606980,1232072072347,813286355868,238678578563,
    414616530573,1043491221872,1535203640625,1788178518812,1734977592327,1362129745630,
    718655876655,85083922841,896098244646,1548792187241,1900110315848,1865138512561,
    1440515242854,709816406557,170303972161,1004581934578,1604711034039,1834127166258,
    1643887937081,1084919297320,296900178709,526637888509,1187595095348,1533118224765,
    1493545027614,1098320800283,464396584098,237593327852,830097576733],
   [1176711464224,1214450888221,966255308862,528413132323,37787857872,368964845310,593672343427,
    602733336622,430026344317,161688276438,96707384402,259130407887,289021188876,210864031981,
    95229779346,17825465403,14746759622,55883333741,61950104740,35334245228,226122875961,
    404427773162,430135286397,242219066174,73094662092,339683992791,441588889128,425049408635,
    425493286090,480595449169,458503442540,229562376501,111670481833,294270487404,187359816383,
    41094735639,184222895678,286696458595,461615157092,532885061375,240964081190,198057702772,
    268757792443,6473090156,13017209122,271707264270,302708706811,89066233986,194124353421,
    355594451434,90698975952,534790002599,158761379318,197619447998,135051280212,190976064373,
    72613771365,325298622017,579521899980,73978955423,107517881038,388136796917,78550446126,
    345776726675,607753975310,13656723704,158191102910,582315496265,362444186978,307854756693,
    26463539366,471255643255,566031878164,380744015904,5311649345,581221500935,854980572528,
    655625522616,472983413896,850789711243,194968715349,1441572642778,314049022660,184216656809,
    1362708991469,582933050864,1025150693772,24254921216,1329808577113,515097716876,
    1091819876204,284954189161,1354046749985,132625332109,1168205935898,31859516543,
    1529964576803,1006412758706,2124940272632,139744669597,1054851786101,1945904160754,
    1496720518032,397119476969,203792668840,1558210587720,1501556836436,34470280177,
    1375361458764,663479650210,1802938384702,1691971229112,425173894808,529764139378,
    3016653431836,1987755010060,96762859959,967338225870,3575822717720,1774617693502,
    265615718828,999530981504,1502362978832,4023705956932,2196366396836,934371310455,
    1688739371346,2736929880138,1176383734230,1476605718974,3331895112106,2117639738228,
    414227909799,607827381380,2000676467452,4772817198718,1897248858416,1833487947230,
    1277081413978,4725198719722],
   [2464279955255,1046054929352,523293926550,3454143566789,2830054767589,1282358154889,
    1267292775792,1921118490191,3669228433011,1985545423879,4089268455423,3039942472651,
    767337862915,3438342930695,2466865334375,1789929833750,1635466390382,1378356715838,
    2252038015930,785137885322,1361365670760,2591362529596,1545041019630,4038466456066,
    5194270687976,735674057486,1708036474234,2628207913214,479430784377,1160786318447,
    632234926501,3893775066841,299035127372,1970417260023,3217126994931,2541220613701,
    3095569648729,2876541242671,38671917233,1738740880849,2444458933817,1868232774677,
    5314516009507,3846296079159,2121012635497,2324509310933,92671900053,2561464417526,
    799551984866,576225255968,2757388266554,692625777509,2034234024145,526848430084,
    2026928972333,3098346603621,1676746998035,2721583463629,1801468093951,2414688106317,
    5443666157773,135373192424,1507601200387,6214032846419,2385306394667,383354599328,
    4552765411165,6126430006123,6115259682464,15329947071791,8609607990826,7818974877711,
    2565024110067,5360755002747,4705261025024,9970807960925,2495908031670,4140660060133,
    2223581407523,1658905468839,383629379919,1934628492090,404697747458,4363346741735,
    9380623779212,9476764369573,3994029657256,2838725740636,8375845860905,7719172603048,
    2751947492207,2325565313131,3980539482134,4574241623657,6626613961862,10450582768337,
    12044148911410,3596982504813,9014876539641,4768103920760,14259283004712,24988182724905,
    19662074018914,4767714358987,2299965611434,2509454400363,10019695860455,7824783660061,
    46768473747,2527203954896,2325331907269,938429981223,10565218229708,12309287683727,
    18295251018280,233925696264,9325861214025,1452532360370,10451318750553,19507044488294,
    6240191151187,4815372062154,3460628302006,14735656737770,12245335962514,13210611436366,
    7093662467325,5467023253624,5167920278103,16095022867779,7800246651865,14112627536894,
    2239297719380,3401129968482,2046731386713,4653533809777,28446780770620,5470700544216,
    17288240749042,12713568534986],
   [24588865013728,10562446593803,15042394236447,6165481732859,22887887663805,10459669187941,
    335805055535,4586454583801,7123350641686,18813888528068,30441693568814,36848611802574,
    6000188224286,23602133347143,5745763623329,3060909260455,44663741964271,30244703845349,
    53881736007584,67495004149726,13137085427295,27267967680941,30302058380058,38156098841152,
    67153814575081,10390674395863,19504150193196,67656056167708,73499897350049,77898611697267,
    162762973652956,50309879999761,53653452527263,16571817316884,24461142516517,122277491782584,
    74922322102799,64191925819037,65971989478770,111134664733763,117421729528436,164539161907822,
    25607487006987,204288823303432,369146893569812,76260013783986,79910450502564,786093643571216,
    1377810056309356,1063384255931962]]
private def rkmC_w64_m32_s7_7 : List ℤ := pzigCat
  [
   [666761233,1723522208,3222348963,5438784644,8254164207,11693423982,15895380167,20753378680,
    26659570643,33507810024,41474603985,50639050544,60979829321,72881961162,86071369623,
    100702984118,116664886345,133807608564,152064396873,170809904640,190035501963,208829339350,
    226497504419,242671607826,256064077517,265981772812,271363406203,271348803454,265112534221,
    251742663360,230833519053,202280796794,165844684521,122381391356,72455320435,17394557522,
    41106592928,101553642407,161583424874,219362112831,273080305276,321132136987,362499168518,
    396840487979,424492665766,446584236177,464719629422,481690279003,499848222074,522000483401,
    550847249892,587844787693,634151655202,689200022725,751387773306,817655206499,883424514872,
    944055752505,993887337410,1027595662345,1040837041888,1030147066665,993795518236,
    932123974525,846923765300,742090798411,622004047870,492422364255,359229828716,227575875985,
    102746267730,11047271230,110029547389,190605816832,249426926969,282940914554,287571696555,
    260201968028,197875645309,100340528212,30465846238,189130364097,365727875292,546665035727,
    714729043644,851209219753,937743185530,958504596191,903289198296,769046053285,560563803072,
    291932155611,16015138837,336628957750,640535451243,898683948000,1084567257713,1177534015664,
    1163806074291,1037915532392,804345137927,477485525164,82001942465,346721019231,764963865006,
    1122203481551,1367193558728,1454388504645,1352307886590,1052980087993,577825765044,
    19169999726,654471188437,1225784350614,1628076897313,1774272866754,1616509829749,
    1160233967980,471525627953,330598495617,1093783891426,1662061236837,1910733896460,
    1776353658807,1275894739744,508150563741,365167134011,1153351574408,1680633113575,
    1829480126282,1568521922773,963393655962,161036610139,646493449035,1268638442634,
    1564519141223,1477371796582,1046025156337,392860149820,311052381810],
   [892426942443,1219769570934,1236383059437,969259680366,516412104889,15093514152,399018339102,
    628993342239,640268769202,465482429185,187922758490,88927180966,276249293697,330453781236,
    264104231179,135922549886,20618572401,30780966397,18884505696,5280623868,26195104154,
    142635060719,298421248850,387020502763,308948512766,54576984195,268238189727,501230099426,
    553317982649,469972598438,375147042829,332443984990,274904836765,101507179100,155032851230,
    301527529829,179009629402,134154191226,387753232123,438177900438,371842031209,298972236120,
    154564583421,130567052861,361799310364,278060962609,15687714034,2135591993,275438986946,
    370604680443,106980331028,97988815520,50082482099,134745083162,383574051689,234913062342,
    209412415716,108170014935,423267227129,431750437152,118772572339,290220660768,422447861233,
    31310580792,68246983227,570479052292,407220842699,90061505010,371155847769,326761565026,
    156624849305,579413833566,373861949559,168248239401,318099485111,444803177100,68141797372,
    87561928744,362016700719,628246320502,262868197767,558730507201,113985714177,148551737920,
    966545844528,953338951929,150739061887,440468415118,1257454741990,7887905256,680498067023,
    293624113781,1546569880754,829168457052,1056118626711,638189684341,989443408278,602441043328,
    696737282077,948786235851,1302338610620,958334737532,1228604683501,1088330226339,
    1669415925016,97721836078,2057073388225,274400342470,1429104480840,446247043300,
    1180964055419,1495559909188,986969399100,314860337010,370417096114,589447791088,754402495644,
    1685595228272,290253318942,45230997569,1735360781552,2510975404428,153178293147,54553731139,
    3103917154262,1647486719772,720573667892,886834317596,1070115530440,3678403953096,
    1957123464312,964007058463,1084874784366,3664850472412,2266913344022,409898305088,
    2536878977774,1110158745226,1442906826054,132743884726],
   [3982664022186,2161198841996,3182102364060,2736828058435,2227260988314,3881678147490,
    201592683606,3101270438148,3389389121826,2372312168018,856666445314,1868166943138,
    3040561511380,2043074784949,3230077809157,429294747891,1527871953351,707764422051,
    232578359460,3517846672601,3792061379399,1266843919973,3015302074291,3828958454933,
    2538025237091,2441238665533,245647552596,2006166405090,37140944977,2459830993922,
    2116514807350,724475014829,1673455881622,4912587822528,1556849154154,4584475486106,
    2212297849136,2042215301236,2979471874852,224416160056,1777846080021,393678959027,
    1824339806607,1416602692345,603984366073,4130834670011,2820192762785,2324907076585,
    2878501769865,733861257671,396174491951,3181365642801,3245501128603,2837821475231,
    5583910891853,3144341377467,262258867350,1606710166147,816607977946,3138132948130,
    413667346938,553489859840,791333205670,1436218354187,552782031400,3393391564985,
    3040302655115,849792765988,3399706201653,4861174586383,2453087216909,4186793243810,
    14646509042767,9294750553014,11421488453561,918003566720,2937958257491,909904689215,
    9933020561443,5697430460162,6625160116921,3317212457715,1929142911641,3170125309051,
    2651018322787,1846157499811,4031021153923,2330142802736,11688796324479,6433572588406,
    2795352069299,4982217856731,9198240231550,6893679290025,2031194776590,3800977371358,
    6590899496695,5962298535820,6830646262303,8696655965752,9180626247599,4287010334014,
    3009101788264,4464236910755,7962016740315,24820777494986,24548264947451,7685523055000,
    3731635565046,3368948980851,111684733839,509925472095,1722374850004,5179083151994,
    1014614356050,5908008231433,14848947116301,9060653162880,15394778571647,6087343571474,
    4658581492568,12070311702027,12593048204694,3723904996261,16912132645246,9926329882837,
    5201185861673,1053634172177,6932283938838,1951496898541,4932422689700,4457324952487,
    15727285036478,15920027564428,5859064689828,4616064861226,13252511718054,12115523981157,
    14219202845947,1350070501533],
   [4864111021555,20545908482078,11344473404981,295105146069,1942092986220,19274462059248,
    2602684275148,14292259101460,32146579598812,5938299046122,1362785856246,3244957891009,
    20215711518421,14454396865377,9494984325351,9307089982631,1682484600535,217429365078,
    17265950195488,46597428622880,28102614390804,13362870045745,563112787635,12892452915702,
    40508128396423,62390814552969,25990774738594,68898223198848,15202631237172,44306372363455,
    57057803048766,11096799742330,15596929346647,65110652161381,37539934615474,102078063454578,
    158486848765637,31162400065248,80429515756464,44136796187015,18789354779480,95198225190421,
    82973832130040,64110650863416,112700756134671,70723108702312,89097371918403,44452518485933,
    191280520111760,13976054880030,32417549154526,360834871925942,228086293227776,58027717532779,
    440527482480148,1321326705063652,1307133280431102]]
private def rkmC_w64_m32_s7_8 : List ℤ := pzigCat
  [
   [216961853,778189800,1983791145,3623591568,5963757955,8841375230,12344899135,16712138814,
    21760108385,27796014108,34649214083,42723199668,52117981013,62539276670,74481875909,
    87699608822,102325878197,118334613924,135407861681,153408554978,172088808553,190895594372,
    209451724325,226820942306,242489052895,255514351638,264908834445,269983231406,269586258011,
    263053754712,249497265655,228626103136,200209480981,163950671834,120854663385,71436242470,
    16891367645,41105463507,101023505700,160623430589,218255954812,271964247045,320152892618,
    361970021143,396879965490,425099555869,447840130764,466399711059,483440213896,501332627773,
    522662669790,550178969825,585444373220,629540422309,682258185346,742218341383,806589378668,
    871330631947,931744006464,982549301493,1018256570740,1034722656045,1028109570960,
    996466196021,939601309836,858908561007,757930112316,640812460083,513194517786,380837400395,
    249019886218,123326365995,8156370824,92623048370,175509333381,237335709944,274810057451,
    284766695898,264435162667,211013889020,123946336953,4258227204,143813617160,311923350537,
    488342347920,657625412707,802307333618,904314699015,947191505574,919087730787,814215430412,
    634085387413,389299447392,97472427749,217111182301,526413435584,801443491885,1014699411822,
    1143674310235,1172059478098,1091526405825,903264686924,617748163275,255237418642,
    153866266922,571090436379,950732987200,1244682116923,1406938814618,1400778949709,
    1207416079816,832158514221,309635334208,295872557200,896686370365,1393113250546,
    1690573989079,1719439355826,1451763684763,914347298114,188974420663,597524564265,
    1295112798214,1761190870827,1891569010172,1647052356755,1067233314554,265971293291,
    589693130537,1315293781570,1751749807593,1802185603142,1457752459405,800693419602,
    13832330934,794714766661,1362006285204,1590189106717,1438647159300,960299347701],
   [284716950548,416403813910,974310198451,1267276579776,1247402095129,949734272890,477046309351,
    32944526005,446380803922,669566956293,671463703624,485889975167,196298408536,94229084958,
    297271048501,365347738678,305180817989,168705354388,27851591783,59224252999,75862558870,
    53295981271,48915215568,106380681933,216992910810,311483695633,297400969454,122787805785,
    172021014763,462411127512,614797226371,578538410760,420091193299,261880169836,170072329777,
    104600076132,11150476512,166216491679,229524329050,78149714553,237238814387,496404933720,
    512412632721,315389349114,88429752399,61761886735,183360456072,305254849667,317378734300,
    151738467177,9856100091,67591271763,274044606702,239067511307,98278618583,340546959342,
    246297726225,98239596908,143969901407,148244957448,21219600596,38645738466,456026389345,
    594904055654,191238780323,20778277967,289252436089,404765894846,161498410847,279172832072,
    570784451327,282916193396,1540717256,386697706256,551352602965,150529735742,134006435913,
    274975087062,19814069865,180789589180,493397743093,62405720436,60705612615,583944313214,
    3027527567,687909435465,380946868316,252860761259,421508269070,631139753609,414941711388,
    534486635542,23642589441,945497585219,55857188075,502927748856,427445926482,643602312115,
    868400826451,767471511892,1527293137798,479021955263,881338740749,293516217888,1642532553320,
    197404112998,1013477688225,1292998368,1675165274460,261823983283,1972573113565,1267111527440,
    1154417116404,616908913775,1393476642191,1703999065656,404624614282,1522394244837,
    403435520899,750978072920,237383473183,92639083572,621663340,455923076732,1110879794488,
    720387295238,511206117637,406637264784,2670375869228,168319253663,769917241583,2180404112588,
    1360829030688,913485777472,318228726994,456028068498,2838201243760,2036556954220,
    447913432917,48214590075],
   [4472828566234,1505190309828,979921492876,206873474203,3437961234884,246646290166,
    3108377486344,908820546596,2995444238434,2028478399200,2370367713907,3244293883144,
    4226317056956,1329702001040,804969274350,1453136412646,1946075111870,42037464247,
    2147501041582,4708879698590,994723869012,1211299418790,4365949540184,2345786828914,
    1114643959100,616736738786,2873242917417,2041971328431,972124295944,852693109769,
    1965076053135,1522104363979,3200403601409,1355674606241,2804743359651,5083773205073,
    2797401252163,680459370669,3487838471079,2420197158768,1647595247374,442328333036,
    1209222580486,422951799994,1641352852962,4121714673430,2189242920408,2640127531074,
    4517138527686,2019772939674,2757874935720,737865443278,1682905113987,202715906793,
    383965693811,1964806449971,1424942974437,2375911058015,4729820778911,1976948760573,
    725163817255,2879665731253,303009828105,1215265154377,5320295240225,3656835205267,
    2988633924013,4631958990133,504046946451,822335541259,1328696387836,2618390010206,
    1285652441261,2408433514510,273653665852,1814769772526,10467023824429,12094444032078,
    13202265137425,2934709088268,3746132216245,1864545406949,5447164802207,3956581877786,
    10543531069613,629999158680,504022551793,5705893748735,3015816556337,1170141080481,
    4377812480401,459515274554,8825227796279,4595340898354,9255380308707,2295145499833,
    4717073422986,11978759669261,2938433588176,2753545691317,7783204131485,6890989810078,
    7911606293017,6808200358066,6726951276679,7550344965388,4295854864543,810161534515,
    1068279164820,6997775907372,20369679360921,25039332929662,13185220904177,5507962735231,
    10192451933986,1375079810369,3174070605291,409663561802,240648417082,1994108932992,
    3088272815937,2695611796962,10330423093959,18980597628324,4205523760489,5505006572049,
    5603971159126,20433828392773,6930589528420,8994630059565,6885248873774,8181133996207,
    881461951077,7367253100830,11740770710420,6892229412709,301794827266,6650263783403,
    5528757244924,3647932960136],
   [5386279782059,2698729567095,18187396519774,6051239688894,5758576619400,22625334128842,
    2019031572267,7388173823032,22868765754139,3785777472893,2923381887784,10458537014396,
    9909084506339,3543178406073,15671707025748,4023405122453,8162962801740,25488886548758,
    16167293627106,16792938348720,7797930336534,9639771150635,12234288551903,15550516878195,
    12482303262747,3594762537787,14113770423605,6150004164199,40439312414012,43222381951864,
    2055488332363,2567905286772,35985162811518,26738697952845,70530777689905,23943776395441,
    87077023477604,9850297308427,574498626438,15060061619050,51489887354152,4872142302011,
    128435383929807,137599169724560,619513588519,106019157975183,60045640948944,14380982912327,
    69847692370786,74399886445577,58955183382345,138845237659436,75241477091649,35648768708306,
    5319551581654,154136304093701,102903176569304,106596429962064,71875806825921,226355608968344,
    370105685276176,32705051449861,108585615386870,1135171875948736,1529036945839128]]
private def rkmC_w64_m32_s7_9 : List ℤ := pzigCat
  [
   [591296586,1620722357,3242333610,5431695671,8014491744,11545169135,15607762876,20428818181,
    26212056054,32876408909,40595219208,49481583241,59536351972,71096673807,83848566838,
    97957764681,113377278902,130011804287,147747914256,165941058831,184628958698,203070833939,
    220659963524,236906117029,250584729188,261170803753,267652591644,269107809673,264756239594,
    253787503227,235660050390,210105130013,176902158164,136665928641,89774006560,37355173969,
    19111744121,78089124866,137664410575,196176083472,251359549491,301850525760,346529167393,
    384303050560,415527240609,440565179016,460904104959,478516038306,495551826091,514988097934,
    539058401905,569996349698,609239019235,657040800402,712756231695,774284167678,838105947413,
    900350182956,955557697163,998676375838,1024929503825,1030048310292,1011381607619,
    967591209962,899392217021,808903788516,699936626559,577663659828,447519541071,315118588018,
    186265829559,65571270414,42390221436,134114370759,206317842758,255866964273,280232082740,
    276077127377,241115723294,173900091811,74132577184,55572707500,209801229715,379250372514,
    551090996565,709751295066,837718932849,917916707604,936027863393,881609573556,751709915413,
    550702541112,291011325503,7579659079,320074224312,617939720609,872892324906,1059338955017,
    1156414009744,1150778104017,1037581736828,820686782745,514140392044,140807808457,
    267049129459,669924170098,1023308031961,1280886719784,1401048103533,1352843237208,
    1123004375989,722905209234,191630113925,404784954917,979322760646,1436922499775,
    1689461070832,1675361645311,1374955225936,820210292725,95851228016,672588916844,
    1340212544875,1771338946476,1869936533291,1603246991568,1013958403881,216349080938,
    626312182416,1334853670797,1755619417028,1796322967231,1449061786826,794852224877,
    14773869047,793110334604,1362556852405,1598278590106,1457533678243,988321014210],
   [316093642677,390939755057,964384226822,1278854153835,1281068924686,998862130883,529464672766,
    8587831219,428292533807,681172985956,710521322637,542154480434,253038116319,54431067265,
    287087918620,388094575467,351483934356,219242020979,59971578146,61398827062,111171714053,
    100854390040,76490864783,88179705946,154234821201,239365046420,268642120439,172269415622,
    60227938256,355042457459,585273052252,647125531571,528997229032,319772411581,139410527008,
    45217403423,728582984,61258366658,138263796123,134797533312,35962727418,322510204807,
    533081415572,496361475317,233282522406,62560680936,224975215719,260108418818,265513210571,
    256883846776,169970031693,35199792444,7175184185,127594653734,180453331425,34125995055,
    347872778906,395142105813,149403663904,21537586390,71367200092,188757916993,175344080980,
    255467750543,484629438082,463654278215,93854140304,40744814376,318653503804,543617548461,
    296844088488,177242187681,412840387534,376039869223,77084672410,234111284119,542531067476,
    223871291709,128894115153,178822806567,378632928218,141120545741,218318090740,323277556185,
    39902088701,105318314064,70092976403,709825698104,805053757131,42664946602,165472617369,
    604662278688,49673683937,301674440865,64743073771,466644665090,404904490725,441067661031,
    318676288636,677407416816,140997964104,670702536503,764273204473,1043287844972,494039681708,
    920631949971,1080017185223,867358296654,1250740972250,230401160043,1155621617039,
    326495661252,2238543897116,967891034233,716295093139,1113524835662,1514684658174,
    1660917138883,656704358175,1685956696392,182018287370,1435921297151,674914168458,
    796573195754,147299675075,469074467131,360621062715,56290558565,170970334366,105060898816,
    1207486620083,1066641592252,1944388308218,1392170326409,232377031268,1836056833450,
    660301887212,330254574476,220612083005,1261783539518],
   [1855023966116,1349616964734,1995878250719,2806267070796,2211848839344,1653849170858,
    2003924972585,3266710367446,1583257029230,2136868246638,1311731593158,39766135007,
    3585399914208,59734276699,720781138416,4694709814582,2157861597254,415543241177,146397581388,
    3212388127736,2732540713740,628754493320,3209097817522,2052500189030,1337261262969,
    1924031262940,3477777453628,1033504021080,2233843668334,2673730552422,1918654982696,
    4281443485452,3131155698834,1420534666087,705856311769,1235901986733,412001405405,
    226579703728,1825055956789,3198076133603,1108775494602,3900887640399,3376626513827,
    2207748572779,4510599123851,3222448064057,881156323529,385047448903,1955106513944,
    1041289703114,1115003778329,2214529299844,1557634288278,1947084658926,3446636258280,
    2409343710218,3535729607748,4487046141318,1775972406192,270716866908,951512846560,
    1174751715361,992755979339,889057505070,3060875007619,3616951764261,1501391872361,
    3763492569121,2581331699731,1036730366992,2610557984109,1883430282643,3085862782187,
    5156755589635,2231556362781,5859067407589,221142986172,3014981179799,7810685985842,
    11276793286423,14262363611824,5984895056491,875259908018,80967983731,1437323273738,
    7003538273927,4859382164922,7371076932825,2362763128455,1497882628688,5093279876361,
    4686147672459,953927848242,5818043294413,1525068331762,9614700748487,3364735927308,
    4667166300205,6972987365381,6294167341914,11414794605257,1332021401971,2186024175244,
    10651886134787,6324720969388,10373277795965,2958766225388,8775722702821,3612363319786,
    3872067813429,19695340515,2522356193717,12410469823092,21638004599463,21088412141554,
    7394614950131,9302481302007,12158375449466,1563963820149,6527548537229,2325199867900,
    1523189034816,1964882348466,5332821213295,6240222193162,9539570112359,13054843187616,
    7167129035719,9678579661831,15641589472618,9517443904067,14323131405656,7570407869359,
    36851760542,11082789797503,2719461145299,565959726748,47497285516,12897672734899,
    7243540135476],
   [4835529906312,7683175942892,953669986141,6463093825757,1090464454475,10631674852204,
    8081220559743,6635738249989,15494565975446,5030630138293,18296749651096,4046914103094,
    21572973407626,5696541190720,6211915582887,17652436526415,737103468616,12321100960622,
    13081304655471,1293885549102,8658542465960,6509886491139,6361078707924,15321753131008,
    16746454906720,23657942105844,13539007402204,1046472786288,6311615112377,18612404184305,
    11380326136719,1203276178847,23951581824577,18354934368311,35743590208926,44201752982404,
    7823683621721,20733761839566,37960452139388,2441092463979,107004560177683,15929522766002,
    33419325386574,14558509031098,10472396147991,7025786346016,123980037620552,135030396111433,
    5258477599759,114130683524424,83885687386791,9933806975358,39976218220333,70640075823624,
    29174900487784,142656042461781,105000472509226,15703331007407,9437590918735,84549737651950,
    151258018251777,20541514927263,153812123510952,73528753477831,70971734961952,412684443161080,
    81320740643088,94544684377943,905250116593186,1676003351875014]]
private def rkmC_w64_m32_s7_10 : List ℤ := pzigCat
  [
   [484160096,1353258881,2806828878,4903688373,7464501234,10763752071,14583380416,19280048641,
    24844847010,31216206643,38690586490,47138522953,56992558848,67974265909,80242060988,
    94087925917,108974486342,125167855277,142357014460,160340276879,178832415422,197161469089,
    214824751602,231358592033,245746890536,257311892075,264959133896,268033747501,265619285968,
    256835907379,241369516254,218371483753,188041338524,150512192591,106081678286,55972709665,
    1124862066,56779455518,116046984969,174837946496,231228848853,283646104406,330717253649,
    371239282760,405221339259,432826992742,455119028713,473660252576,490699389337,508851609978,
    530244729373,557593975942,592436421657,635560664304,687000550905,744966648916,807170815397,
    869608693922,927652819329,976464796194,1010691794001,1026128884604,1019160900817,
    987784074430,931819155933,852388001308,752507382713,636842044416,510215978243,378722347312,
    247943965141,123121025686,8954655489,90629233147,171962131816,232344164437,268924988060,
    278939036223,260152172734,210593169703,129323299128,17629049587,121116234013,279784074414,
    448439678275,613413692504,758477578745,867217255280,923391621523,914375176244,832705248209,
    677547003732,456210079063,183269355394,119714960978,426612663235,709552506260,940910545431,
    1096611970802,1159004679283,1117324066622,970159859431,724881330996,398475411827,16880201950,
    386485298874,771284251597,1093843791242,1311201036435,1385788165636,1292391416777,
    1024509334798,599157355479,60267864770,524404121700,1068889113173,1482128205898,
    1683966608477,1621156132396,1282657794935,707513486228,16557613030,764637694607,
    1396727509226,1785188904993,1842548876296,1544753481649,939621656806,142626432609,
    684959456355,1369939694326,1765098765297,1784338315562,1424077851647,765860638232,
    40495177224,811829514215,1374821662358,1606695086467,1465500301394],
   [997611019351,325469196874,384907023812,966808101273,1293451813216,1308139184387,
    1034817808458,566313719579,36390211376,418113266098,693726783913,744262620006,589209862401,
    300994075154,19773177878,276360452331,404988582046,390231303249,265006304512,94260142731,
    53791581267,134338476708,142572889575,112505271134,93142344555,117661967620,177344442505,
    219370150772,175541014729,8134931200,253432472422,512723455715,654471657112,613664195343,
    420150032228,181944910573,10048179584,55685057008,59334757193,64852590164,74961042907,
    20549043980,153432093062,389810220619,524080784174,419607567339,111168376106,206960368524,
    353488597607,317094494214,225266709827,171973798448,130342379563,55556804190,2452399332,
    25316420544,65597057833,45004602555,293597359522,418724641169,243341632734,27279895564,
    45923580623,189398054493,358940661858,334499043835,318060661364,376537677121,286213865342,
    56226989895,85570671914,443133965101,587864713154,285728483601,86978755710,303010063145,
    416173224312,179906245255,136795487316,371248743231,245678824454,104856541812,92440814952,
    497831600733,280948131258,80485114252,29174593590,35323784710,475513502975,548215193622,
    454271228145,571144739412,237762089683,184675147325,225418833067,354263847934,296376259648,
    70287760049,623482878483,153543652794,454347216264,188927242115,272741489287,379334800592,
    106146643332,6260513212,906295034419,50230064228,1026094670542,417578190560,1100643524491,
    498621854085,1088057034230,455834423076,581709298923,1881486546261,1395733296686,
    1165930169490,890116954527,1176042886007,1698665301640,929486081106,1506053582481,
    81918562642,2243531521738,439912017341,1036647960843,748508622656,608374229532,377328260917,
    448672964313,475595691948,127412763318,684782325524,256989805273,1426496066151,1448255402214,
    33070890372,1993216973773,600270530920],
   [940260441484,356864574786,704028472017,799311343510,277508394772,2682879514948,1777945440437,
    582260703278,1159808198318,3259253362652,2177802299893,568518499248,2825473854742,
    911003507996,1753897771268,1151633022301,2059414318758,3125886854122,317718903617,
    2088583110044,2816794689308,372346773132,361099050993,2476370995562,4617893725062,
    690308046966,203998675375,2896596560376,867409943032,718468453012,4399696995078,
    2228659984440,78518104635,1686029192344,1261249250678,1339026364838,3454185161164,
    497638685480,1578394345838,3941932946044,3962130961812,2497705746924,1774629914404,
    3102147776205,1358459600082,303018736128,2627491138033,177300463769,734020954455,
    2453501977489,1223213833895,2744469051007,3844910191471,2956857698667,5099857255481,
    1466673710857,879904380008,360913841783,667448710166,451452498026,277022667494,2231977934306,
    2173230771078,1142799829048,3881533911298,4483671419712,2298909632782,3754912661472,
    1383305683860,1459004268861,1319464523310,613562775792,2739650784663,34497339734,
    3237889601053,4283708364139,1289862356201,3442081827903,1654232598778,4468551837109,
    1949158375042,9820040362233,6336138140434,16991852585223,5505684175952,3739180264673,
    2543839060567,235950293359,6584943887846,5536561751517,5796721143864,982519725001,
    2921627379847,2923363192010,1857906900783,6331509224701,3229219845546,6294048807139,
    1879511450742,8408973344677,649504046030,63182711312,10615436380133,5780743349916,
    7419335301535,5871854779211,6373966991086,12620410744415,4942573121234,9680281458379,
    2398807179950,7265323991645,1882562885288,5504197588495,761142416049,10267936546703,
    13301654575170,22889234148099,14828236186638,575972873193,12294145352093,12030018171354,
    164153464180,8712165527309,4480440868274,1866667638406,797379564862,7981832868745,
    8897165123012,8472527408245,9004161342072,3196499858933,10048066205157,18792219114780,
    13973863171673,6139360177584,8092416799653,4848876301006,1414866104624,6022430268438],
   [459632674552,3215051758323,13593098145269,5905716459198,4026024486793,6297217909941,
    5290679112681,1830386063468,7319950671074,9678792629660,8953497603619,4041164709413,
    15467239956350,14651804811615,6463191057354,7224254552777,9107112296070,1182887436894,
    8938924086966,14504531421106,20045861078750,5762185517576,22030597173831,1954424047910,
    5563599229684,11046865099075,3831647678264,2937519927426,4974530996171,3024237578444,
    5451232340996,14680289932106,24203868130552,17368398621288,13161810158382,943254756132,
    20236817434715,7175211090919,2147924524134,29851620489401,32879657521951,38520879129324,
    26841966284928,4624151870892,4365951365114,88751568130126,43306773640935,65042102319447,
    8842949026181,22594340215008,38916871859880,90573773754577,139264370074876,16748765973166,
    126191346184493,95000698243684,13949640288241,12387662680716,57707857273353,9228612149303,
    130873259194340,130487516993113,21365981405702,34205404278450,55276708675551,121067505228930,
    68046193552975,131883640427991,139574205600972,14281770047561,73102135320763,366388818368194,
    235128435436688,211256358248347,624059349997292,1786069031885102]]
private theorem rkmWC_w64_m32_s7_0 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    597 rkmXsWin_w64_m32_s7_in 590 rkmC_w64_m32_s7_1 312792356 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_1 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    590 rkmC_w64_m32_s7_1 583 rkmC_w64_m32_s7_2 317658763 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_2 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    583 rkmC_w64_m32_s7_2 576 rkmC_w64_m32_s7_3 331211072 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_3 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    576 rkmC_w64_m32_s7_3 569 rkmC_w64_m32_s7_4 278599812 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_4 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    569 rkmC_w64_m32_s7_4 562 rkmC_w64_m32_s7_5 330350815 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_5 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    562 rkmC_w64_m32_s7_5 555 rkmC_w64_m32_s7_6 368088832 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_6 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    555 rkmC_w64_m32_s7_6 548 rkmC_w64_m32_s7_7 306003885 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_7 : bWinChk 508 5 100000000 1024 rkmPhb_w64_m32_s7
    548 rkmC_w64_m32_s7_7 540 rkmC_w64_m32_s7_8 261361490 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_8 : bWinChk 508 4 100000000 1024 rkmPhb_w64_m32_s7
    540 rkmC_w64_m32_s7_8 535 rkmC_w64_m32_s7_9 333178396 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_9 : bWinChk 508 4 100000000 1024 rkmPhb_w64_m32_s7
    535 rkmC_w64_m32_s7_9 529 rkmC_w64_m32_s7_10 228475498 = true := by decide +kernel
private theorem rkmWC_w64_m32_s7_10 : bWinChk 508 4 100000000 1024 rkmPhb_w64_m32_s7
    529 rkmC_w64_m32_s7_10 523 rkmXsWin_w64_m32_s7_out 196730961 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s7 :
    RkmWinIterSound 52 1024 rkmHbWin_w64_m32_s7 597 rkmXsWin_w64_m32_s7_in
      523 rkmXsWin_w64_m32_s7_out 3264451880 :=
  rkmChS 52 3264451880 (rkmChS 48 3067720919 (rkmChS 44 2839245421 (rkmChS 40 2506067025
    (rkmChS 35 2244705535 (rkmChS 30 1938701650 (rkmChS 25 1570612818 (rkmChS 20 1240262003
    (rkmChS 15 961662191 (rkmChS 10 630451119 (bWinChk_sound rkmHhb_w64_m32_s7
    rkmWC_w64_m32_s7_0) rkmHhb_w64_m32_s7 rkmWC_w64_m32_s7_1 rfl rfl) rkmHhb_w64_m32_s7
    rkmWC_w64_m32_s7_2 rfl rfl) rkmHhb_w64_m32_s7 rkmWC_w64_m32_s7_3 rfl rfl) rkmHhb_w64_m32_s7
    rkmWC_w64_m32_s7_4 rfl rfl) rkmHhb_w64_m32_s7 rkmWC_w64_m32_s7_5 rfl rfl) rkmHhb_w64_m32_s7
    rkmWC_w64_m32_s7_6 rfl rfl) rkmHhb_w64_m32_s7 rkmWC_w64_m32_s7_7 rfl rfl) rkmHhb_w64_m32_s7
    rkmWC_w64_m32_s7_8 rfl rfl) rkmHhb_w64_m32_s7 rkmWC_w64_m32_s7_9 rfl rfl) rkmHhb_w64_m32_s7
    rkmWC_w64_m32_s7_10 rfl rfl
private def rkmWalksHi_w64_m32_r1024 : List RkmWinSegWalk := [
  ⟨64, rkmHbWin_w64_m32_s0, 0, rkmXsWin_w64_m32_s0_in,
    0, rkmXsWin_w64_m32_s0_out, 699772370⟩,
  ⟨128, rkmHbWin_w64_m32_s1, 0, rkmXsWin_w64_m32_s1_in,
    0, rkmXsWin_w64_m32_s1_out, 1334447977⟩,
  ⟨256, rkmHbWin_w64_m32_s2, 0, rkmXsWin_w64_m32_s2_in,
    58, rkmXsWin_w64_m32_s2_out, 10258512904⟩,
  ⟨512, rkmHbWin_w64_m32_s3, 58, rkmXsWin_w64_m32_s3_in,
    222, rkmXsWin_w64_m32_s3_out, 22538690937⟩,
  ⟨1024, rkmHbWin_w64_m32_s4, 222, rkmXsWin_w64_m32_s4_in,
    581, rkmXsWin_w64_m32_s4_out, 49608454206⟩,
  ⟨1024, rkmHbWin_w64_m32_s5, 581, rkmXsWin_w64_m32_s5_in,
    844, rkmXsWin_w64_m32_s5_out, 47942080659⟩,
  ⟨1024, rkmHbWin_w64_m32_s6a, 844, rkmXsWin_w64_m32_s6a_in,
    597, rkmXsWin_w64_m32_s6b_out, 23168857434⟩,
  ⟨1024, rkmHbWin_w64_m32_s7, 597, rkmXsWin_w64_m32_s7_in,
    523, rkmXsWin_w64_m32_s7_out, 3264451880⟩
  ]
private theorem rkmRowOk_w64_m32 :
    rkmCheckRowFromWinWalks 32 256 1024 [2, 4, 8, 16, 32, 58, 58, 58]
      [4346337, 3916706, 6415160, 6046259, 7528059, 5307913, 4524812, 1008701]
      [12, 21, 66, 117, 254, 271, 231, 52]
      rkmMasksHi_w64_m32_r1024 rkmWalksHi_w64_m32_r1024 rkmRowHi_w64_m32_r1024
      = true := by decide +kernel
private theorem rkmWinChain_w64_m32_s6_full :
    RkmWinIterSound 231 1024 rkmHbWin_w64_m32_s6a 844 rkmXsWin_w64_m32_s6a_in
      597 rkmXsWin_w64_m32_s6b_out 23168857434 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w64_m32_s6a) (hb2 := rkmHbWin_w64_m32_s6a)
    (x1 := rkmXsWin_w64_m32_s6a_out) (x1' := rkmXsWin_w64_m32_s6b_in) rfl rfl
    (muxIntListEq_eq_true.mpr rfl) rfl rkmStatOk_hiw64t09_p.2.2.1
    rkmWinIterSnd_w64_m32_s6a rkmWinIterSnd_w64_m32_s6b
private theorem rkmWinSegWalkSnd_w64_m32_s6 :
    RkmWinSegWalkSound 231 ⟨1024, rkmHbWin_w64_m32_s6a, 844, rkmXsWin_w64_m32_s6a_in,
      597, rkmXsWin_w64_m32_s6b_out, 23168857434⟩ :=
  @rkmSegWalk_mk 231 1024 844 597 23168857434
    rkmHbWin_w64_m32_s6a rkmXsWin_w64_m32_s6a_in rkmXsWin_w64_m32_s6b_out
    (rkmw_buildHbFrom_length 1856 1024 19587930735 1024 0)
    rkmStatOk_hiw64t09_p.2.2.2 rkmWinChain_w64_m32_s6_full
private theorem rkmHbLen_w64_m32_s7 : rkmHbWin_w64_m32_s7.length = 1024 := by
  rw [show rkmHbWin_w64_m32_s7 =
      altBuildHbFrom 1856 1024 19398096153 0 1024 from rfl]
  exact rkmw_buildHbFrom_length 1856 1024 19398096153 1024 0
private theorem rkmInLe_w64_m32_s7 :
    597 + rkmXsWin_w64_m32_s7_in.length ≤ 1024 + 1 := by
  have h3 := @rkmLenApp 87 80 167 rkmXsWin_w64_m32_s7_in_p3 rkmXsWin_w64_m32_s7_in_p4
    (pzig1_len _ 87 rfl) (pzig1_len _ 80 rfl) rfl
  have h2 := @rkmLenApp 87 167 254 rkmXsWin_w64_m32_s7_in_p2 _ (pzig1_len _ 87 rfl) h3 rfl
  have h1 := @rkmLenApp 87 254 341 rkmXsWin_w64_m32_s7_in_p1 _ (pzig1_len _ 87 rfl) h2 rfl
  have h0 : rkmXsWin_w64_m32_s7_in.length = 428 :=
    @rkmLenApp 87 341 428 rkmXsWin_w64_m32_s7_in_p0 _ (pzig1_len _ 87 rfl) h1 rfl
  exact Nat.le_trans (Nat.add_le_add_left (Nat.le_of_eq h0) 597)
    (Nat.le_refl 1025)
private theorem rkmWinSegWalkSnd_w64_m32_s7 :
    RkmWinSegWalkSound 52 ⟨1024, rkmHbWin_w64_m32_s7, 597, rkmXsWin_w64_m32_s7_in,
      523, rkmXsWin_w64_m32_s7_out, 3264451880⟩ :=
  @rkmSegWalk_mkHi 52 1024 597 523 3264451880
    rkmHbWin_w64_m32_s7 rkmXsWin_w64_m32_s7_in rkmXsWin_w64_m32_s7_out
    rkmHbLen_w64_m32_s7 rkmInLe_w64_m32_s7 rkmWinIter_w64_m32_s7
private theorem rkmWalksSndHi_w64_m32_r1024 :
    RkmWinSegWalksSound [12, 21, 66, 117, 254, 271, 231, 52] rkmWalksHi_w64_m32_r1024 :=
  ⟨rkmWinSegWalkSnd_w64_m32_s0, ⟨rkmWinSegWalkSnd_w64_m32_s1,
    ⟨rkmWinSegWalkSnd_w64_m32_s2, ⟨rkmWinSegWalkSnd_w64_m32_s3,
    ⟨rkmWinSegWalkSnd_w64_m32_s4, ⟨rkmWinSegWalkSnd_w64_m32_s5,
    ⟨rkmWinSegWalkSnd_w64_m32_s6, ⟨rkmWinSegWalkSnd_w64_m32_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic `w64_m32` `r = 1024` hit certificate (`m = 32`). -/
theorem rkmTrajHitHi_w64_m32 :
    RkmAnchorHitSound 32 ⟨1024, [2, 4, 8, 16, 32, 58, 58, 58],
      [4346337, 3916706, 6415160, 6046259, 7528059, 5307913, 4524812, 1008701],
      [12, 21, 66, 117, 254, 271, 231, 52], rkmMasksHi_w64_m32_r1024, rkmRowHi_w64_m32_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 32 256 1024 [2, 4, 8, 16, 32, 58, 58, 58]
    [4346337, 3916706, 6415160, 6046259, 7528059, 5307913, 4524812, 1008701]
    [12, 21, 66, 117, 254, 271, 231, 52] rkmMasksHi_w64_m32_r1024
    rkmWalksHi_w64_m32_r1024 rkmRowHi_w64_m32_r1024 rkmWalksSndHi_w64_m32_r1024 rkmRowOk_w64_m32
/-- Cumulative `w64_m32` part `2` lane witness. -/
theorem rkmHiLane_w64_m32_wint2 :
    @rkmTrajHitHi_w64_m32 = @rkmTrajHitHi_w64_m32 :=
  (And.intro (Eq.refl rkmHiLane_w64_m32_wint1) rfl).right
/-- Module lane witness for `FindAllJohnsonRampKickMuxHiW64T09`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T09 :
    @rkmHiLane_w64_m32_wint2 = @rkmHiLane_w64_m32_wint2 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T07)
    (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T08) rfl)).right.right

end
end QuantumComputation.Specs.DickeSol
