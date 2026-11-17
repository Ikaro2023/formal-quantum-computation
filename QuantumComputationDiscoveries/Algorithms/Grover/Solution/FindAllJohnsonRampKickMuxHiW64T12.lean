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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T10
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T11

/-
# Caustic `r = 1024` Halo-16 Walk `w64` Part `12` (`FindAllJohnsonRampKickMuxHiW64T12`)

Certifies part `12` of `w_hi64_m64_r1024` (`m = 64`) halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Part `0` of `rkmMkHi_w64_s5`. -/
def rkmMkHi_w64_s5_p0 : List Bool := let t := true; let f := false; [t, t, t, f, f, t, t, t, t, t,
  t, t, t, f, f, f, f, f, t, t, t, t, t, f, f, f, f, f, f, t, t, t, t, t, t, t, t]
/-- Kick mask `w64` seg `5`. -/
def rkmMkHi_w64_s5 : List Bool :=
  List.replicate 874 false ++ rkmMkHi_w64_s5_p0
/-- Part `0` of `rkmMkHi_w64_s6`. -/
def rkmMkHi_w64_s6_p0 : List Bool := let t := true; let f := false; [t, f, f, t, f, t, t, f, t, f,
  t, t, f, t, f, f, t, f, t, f, f, t, f, t, t, f, t, f, f, t, f, t, t, f, t, f, f, t, f, t, t, f,
  t, f, t, f, t, f, f, t, f, t, t, f, t, t, f, t, f, t, f, t, f, f, t, f, f, t, f, t, t, f, t, f,
  t, f, t, t, f, t, t, f, t, f, f, t, f, f, t, f, f, t, f, t, f, t, f, f, f, t, t, f, t, t, f, t,
  t, f, t, t, f, t, t, f, t, t, f, t, t, f, t, t, f, t, t, f, t, t, f, f, f, f, t, f, t, t, t, f,
  f, f, f, f, f, f, f, f, f, t, f, f, f, f, f, f, f, f, f, f, t, f, f, t, t, f, f, f, t, t, f, f,
  t, f, f, f, f, f, t, f, f, t, f, f, f, f, f, t, f, t, f, t, f, t, t, f, f, f, f, t, f, t, t, f,
  t, f, f, f, f, f, t, t, f, f, t, t, t, t, f, f, f, f, t, t, f, f, f, f, f, f, f, f, f, f, f, f,
  f, f, f, f, f, f, f, f, f, f, f, f, f, t, t, f, f, f, t, t, t]
/-- Kick mask `w64` seg `6`. -/
def rkmMkHi_w64_s6 : List Bool :=
  List.replicate 763 false ++ rkmMkHi_w64_s6_p0
/-- Kick-mask schedule for `w64` `r = 1024`. -/
def rkmMasksHi_w64_m64_r1024 : List (List Bool) := [
  [], [], [], [], [], rkmMkHi_w64_s5, rkmMkHi_w64_s6, []]
/-- Alias for `rkmMasksHi_w64_m64_r1024`. -/
abbrev rkmMasksHi_w64_r1024 : List (List Bool) := rkmMasksHi_w64_m64_r1024
/-- Part `0` of `rkmRowHi_w64_m64_r1024`. -/
def rkmRowHi_w64_m64_r1024_p0 : List ℕ := [103, 1442, 4280, 8484, 13833, 20136, 27213, 34955,
  43407, 52632, 62903, 74344, 87080, 101154, 116039, 130984, 144571, 154898, 159806, 157009,
  145046, 123665, 94571, 61602, 30465, 7877, 0, 0, 0, 0, 3421, 14474, 25743, 30890, 27208, 16432,
  4534, 0, 0, 0, 181, 14443, 46494, 85678, 118713, 133298, 122511, 87896, 41869, 6041, 0, 0, 12223,
  74875, 165010, 241861, 267039, 223646, 128915, 33269, 0, 0, 47138, 180784, 324118, 392333,
  340429, 193687, 44119, 0, 5516, 130338, 336040, 479953, 457816, 277857, 68661, 0, 16257, 201778,
  448675, 554818, 429012, 169403, 3299, 631, 150529, 410605, 532352, 402067, 139499, 17, 5889,
  169702, 373619, 399291, 223982, 31577, 0, 39655, 184395, 256103, 175796, 40242, 0, 2560, 64019,
  111864, 81957, 17981, 0, 0, 10049, 25280, 16976, 1294, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 6758, 16661, 8789, 0, 0, 223, 8420, 3683, 0, 0, 9647, 25216, 8627, 0, 0, 3231,
  3536, 0, 0, 0, 0, 17, 18601, 26999, 4444, 0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 1020, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13649, 18116, 0, 0, 62, 28902, 3684, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  39280, 7685, 330, 0, 46401, 191, 152813, 125498, 46, 0, 203140, 41845, 108447, 7241, 249432,
  26932, 347786, 67791, 529896, 421755, 156044, 596525, 0, 48192, 0, 91741, 19711, 0, 0, 21837,
  377816, 14219, 293505, 256291, 0, 63942, 6566, 685760, 115162, 5759, 454710, 325938, 0, 5584,
  917591, 680132, 600406, 1643462, 263948, 387360, 372829, 40050, 343579, 1507598, 1183836, 39616,
  201828, 1372087, 176534, 0, 1336700, 2924766, 119410, 0, 3131737, 254419, 94096, 2290139, 0,
  1936, 1692437, 997885, 1338660, 1094157, 1, 304370, 1715145, 3588, 1174432, 3628, 1083715,
  9535660, 2939644, 62103, 818700, 0, 98680, 24681, 399481, 20757, 141656, 748952, 35164, 1596735,
  6005292, 3421573, 1273029, 462578, 8601, 8427, 137825, 580845, 30745, 33024, 1879276, 601986,
  1409508, 8433730, 896171, 621244, 1477507, 756403, 2006647, 2318453, 2126500, 17099471, 4751086,
  42248688, 19930891, 16527562, 161714, 67162, 2016109, 20534976, 1864288, 16559910, 1829279,
  708813, 1710206, 393050, 5625246, 9168206, 9202430, 2280761, 452081, 3049054, 3994722, 8087483,
  28843896, 267653, 0, 31619113, 14062297, 20464908, 75344, 1003363, 6654663, 1987670, 33536402,
  16154322, 44959965, 2808161, 879539, 2443371, 16798150, 23710500, 62226614, 414914, 25843010,
  54156042, 2075209, 7244606, 1756040, 5958899, 8925428, 1629577, 0, 1650477, 18127595, 14160773,
  322828, 12475326, 72025, 16043521, 12040353, 5554696, 26312841, 7144514, 691230, 80720, 31739883,
  4535680, 68975883, 4312472, 43529819, 209531996, 34478, 38793532, 9012307, 35061147, 8607309, 0,
  1208242, 597045, 414687, 25609818, 5953447, 16950386, 5167705, 46788845, 103747505, 27604778,
  93036392, 107444764, 52206981, 106785800, 1868388, 11815132, 117288507, 58046771, 19880455,
  4517550, 79644692, 67297609, 40777155, 226436907, 63557492, 280628781, 101097146, 171084849,
  9470452, 348057968, 821942103, 401353322, 1619321648, 19584960, 30958274, 844650865, 2449426867,
  2358955759, 184682298, 6339422129, 1467817145, 82181465, 36696165, 505678867, 22599468,
  3629814455, 4802388779, 193758101, 779235429, 965670732, 1818673093, 1706950664, 1053310756,
  7859992087, 684182789, 1495050427, 7036914945, 11985398680, 38681744896, 12709019256,
  19794539835, 863196370133]
/-- Certified `rowLo12` vector for `w64` `r = 1024`. -/
def rkmRowHi_w64_m64_r1024 : List ℕ :=
  List.replicate 566 0 ++ rkmRowHi_w64_m64_r1024_p0
/-- Alias for `rkmRowHi_w64_m64_r1024`. -/
abbrev rkmRowHi_w64_r1024 : List ℕ := rkmRowHi_w64_m64_r1024

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
private def rkmHbWin_w64_s7 : List ℤ := altBuildHbFrom 1856 1024 19575653846 0 1024
private def rkmXsWin_w64_s6b_in : List ℤ := pzigCat
  [
   [498277394,1482219811,3087669864,5508724993,8531372778,12127431241,16622472676,21618519901,
    27406707186,34030754861,41206275728,48914326827,57274841304,65711228013,73794362796,
    81450543169,87612686224,91711463943,93115214570,91053649769,84671526802,73876891501,
    58772832792,39496554791,17327006384,6034585258,28908761549,48546093154,62296961745,
    67632854122,62389587609,44429204134,13169413199,30683925991,85790223442,149014919359,
    215892219046,282046996619,343275747404,396575449351,441139830636,479831751021,517715299420,
    562115263505,621646657742,703471905313,810928261434,941827793059,1087798727684,1234254669419,
    1361863150762,1451568617147,1487137459946,1458252387081,1362312229584,1204109184275,
    993053271804,740347967143,457618622482,157533216955,145562887927,432926964892,678703745021,
    851489205332,918823326491,855657788152,650777347617,311632075282,133729285576,638315880201,
    1139540216576,1561302093111,1818091372154,1823244050647,1507668143426,850787127717,
    86264763783,1139766895454,2057146182867,2555648832038,2418736987297,1596878070232,
    267511339445,1188625451151,2302174618938,2686173849575,2195911298514,1001318531735,
    467191192941,1682126776780,2225395251715,1947166759718,1011494725741,184862762097,
    1177812850122,1617606306255,1394899563872,668757159297,211323691925,860365740730,
    1030113363311,722260315512,176545717011,274142561893,408666263208,254802786321,50575264254,
    41043883855,253435369600,443245059699,290561835746,282901737842,946672236095,1138697028050,
    513274712037,682349916181,1657955729494,1609007263623,372112025252,1320722491022,
    2268094720735,1665294192772,218960175838,2114034633509,2601356969090,1183571670603,
    1232903956617,2882633209680,2420665652715,30883335148,2543892563888,3235217649917,
    1320514351978,1809856597066,3596509094013,2403346080634,938576807320,3617717168937,
    3194431090472,128229145642],
   [3461420143041,3714561713646,503886781573,3280624857661,4032763863632,899905118689,
    3192669821061,4213739982360,1026025905915,3269001166141,4280006407090,851769934425,
    3521675806265,4194734798228,358591906149,3888974845245,3878544200404,428180102366,
    4244278539365,3260121015114,1421031445610,4443924826299,2314809187066,2505963552958,
    4370379390277,1030856386464,3584197448510,3876483588051,649991305807,4476137872392,
    2661934075365,2706859997995,4676114515028,380068381597,4614622288547,3335235797962,
    2734200091862,5047110974215,45228121806,5108718444776,2679233046185,3781016903705,
    4415159322722,1712152794760,4960952532973,384859679410,4437384181446,1963875629845,
    3211202378303,2740050852216,1712482420344,2671655643043,300355341171,1883144828582,
    804254371215,576118251997,1525485158968,1039611016299,1902968288101,2787236644880,
    2047213628420,4539303093529,2099770672191,6219100357130,2208244846976,7790446423871,
    2520518308085,9235347086274,3191401583638,10517529136467,4384865521543,11533519495446,
    6255168799930,12064137076885,8895397751593,11744607126606,12248701298732,10072649201863,
    15980994688087,6490700217244,19327669209486,613010232241,20999838971121,7347816276563,
    19364725167498,16086831602170,13108136928779,23065967453739,2233488997242,25148158863130,
    11240661955852,19817066872693,23328001449899,6394066437946,28554843541142,12493749863236,
    21267261143351,28846866289861,190281044820,30424312301126,24976787884292,10428535811601,
    35263818840179,21117104261833,17304550818392,39216895341378,21043062136828,20206524109339,
    44683924148533,28046697068883,16647032285178,51305950426862,45679611687424,1938486757870,
    47458691189229,64384844862751,32338046946279,32414400357966,91416019379702,107627133750352,
    67053272742022,13178103045133,92884823516901,127181321678607,85427578005953,37413560968718,
    220425028683192,425659321135004,611397065885956,744304741165040,806744920215068,
    798087319248668,731150571508746,626126693977274,504405780670984,383984801008720,
    277124101757978,190057176156054,124073035007878,77190217394818],
   [45799141964116,25925238848560,14001423657370,7211927564766,3540280784018,1654275338270,
    734457429534,308553997340,121988664800,44766156386,14819551106,3875142540,550002230]]
private def rkmXsWin_w64_s6b_out : List ℤ := pzigCat
  [
   [214141452,780965661,2009945592,3646761527,5890906210,8526624873,11619917348,15303487065,
    19127319094,23513908809,28251183584,33217410805,38524687902,44028490305,49615686454,
    55266011599,60666426298,65917567323,70396147092,74044270231,76836477644,78088029133,
    77848423492,75717661671,71569963950,65307210965,56810520432,46374081313,34365386742,
    21037495683,7385422796,6077187196,17993714845,27160525706,32840622017,33386592490,
    27915632793,15567651002,4408584174,32153635019,67513021276,110066687027,158516029860,
    211789173237,268137544184,325988542263,383730256870,439804784651,493428760192,544195427083,
    591970546962,638095551505,683542863638,730051805459,779617870218,833335503171,892100838090,
    955320840109,1021003025622,1085644778547,1143976472698,1189394709187,1214657669896,
    1212029260239,1175352578004,1099806223197,983471261516,828047913557,638512757892,
    423722827383,195718314704,32248526320,245171465525,429184077868,571978737179,663478874098,
    697600749283,671287509268,584940587057,442716787834,251658890969,21903527530,232706032698,
    495774702871,746982128800,963576794733,1121765677566,1198176435145,1173305330846,
    1035468060869,783219837344,429449709895,1567626856,459169192700,900435679941,1265153219038,
    1499152286035,1558637131102,1419650681935,1083273428096,579354776223,33382046139,
    672965366918,1244011497899,1650550635708,1813357195339,1685265428066,1265228862697,
    605586926660,190874274978,983686567455,1617827569550,1956521467261,1912204577078,
    1472636716537,713007272814,213139862870,1103151733845,1749966891302,1995265033141,
    1772338738468,1129415038559,223739932106,716127208774,1449931017395,1790438448532,
    1657603690337,1101196009062,286565324259,553472743977,1187373088628,1452822689871,
    1300913213420,806198829303,137486534478,499168146198,925242335727,1040957850186,849766395091,
    446141393968],
   [23690022320,412715863287,619709980864,615259324941,439540023054,179856451453,67059358825,
    229723573120,282355266531,245504889062,168778573657,102014915186,70112964181,62624512166,
    41884366233,30775023145,164035403324,318812675999,415808302038,369237521315,138658027534,
    230639836678,603830405423,800577495842,678016454045,217916407266,432846298082,999236651727,
    1191632996568,851653506713,60228866874,862803286610,1482902773663,1455697223852,717985005161,
    441143511003,1485579227118,1880771530001,1370677699998,139964452579,1239756400369,
    2074880504256,1903142614241,752342722932,837703995034,2064887899097,2272063777188,
    1305130315121,377436555743,1916556722626,2490770234999,1758532120192,65704439305,
    1708839448941,2606415883524,2108391480321,441376065602,1513048839920,2676906332505,
    2370894929764,717075499079,1389325323021,2754513025830,2561327371253,867099215382,
    1383494703790,2872547284557,2680148994248,863776537389,1525183980275,3036769117412,
    2704703396235,677201464932,1821323537914,3218983007045,2590202192360,284057389625,
    2247385852045,3356319413364,2279380860531,319623855833,2741386478572,3358236661939,
    1719197334858,1103392429766,3201272687109,3119926499126,881676298581,1987653378871,
    3487305750298,2541250161323,212238681697,2831377587300,3432918750671,1557352301692,
    1460316263050,3423745881547,2874061077366,191561754087,2643916290715,3503902492470,
    1718956894313,1377180776669,3426216128366,2841571357281,56357770998,2774505530966,
    3432631511071,1386028330046,1757838943408,3498609688927,2434114993166,591106217670,
    3134712352609,3121864676616,549879296113,2476745185265,3451994064472,1547727244929,
    1662487906801,3480640583250,2345589828747,808572802809,3290807453790,2933885263993,126957566,
    2970732001942,3335635255575,709175028202,2601105789210,3589906055421,1289058100458,
    2247648657112,3739300784961,1726569707582,1959003589322,3819698901207,2016839260018,
    1766389900940,3854183406057],
   [2158207630352,1683726660650,3849925940577,2150345522780,1706827060724,3797813377239,
    1996015527684,1812083190106,3675501337997,1707315498476,1955978331124,3456202385095,
    1313966428238,2077793936800,3121938725565,872774629980,2109410425376,2683498377693,
    470248428566,1997298703466,2200137130239,211027158398,1736463441492,1790780308077,
    181986600376,1409529133506,1615686898961,390255765192,1208168988420,1812346365153,
    691309952502,1400298778442,2380895578869,751057365534,2210499122024,3055921541233,
    113093102528,3612370018428,3253614742131,1574511923605,5115340218332,2221945414247,
    4194672793781,5724090624536,529680322880,6847412459263,4281101814456,4635207079382,
    7918069733445,236177022380,8509031364798,5801399516985,5502416442413,9730893533504,
    129893767773,10340401349117,6365572408504,7228800471510,10979139296231,1340942390611,
    12365088117430,5477063792641,10027895497549,11173567096134,4623985062854,14148374563371,
    2372866569124,13657485379884,9192721266507,9894278146059,14277372326782,3794347378142,
    16628869621399,3313155803584,15939397390132,10074742946875,12525631276213,15400975844370,
    7135265765074,18624974447675,709096240061,19530960547800,5835113051569,18283421001413,
    11754202230190,15304008838910,16556501681267,11136631917351,20011471400982,6332240832888,
    22114008837101,1366962614379,23023946130536,3400889675597,23002082424307,7741061242862,
    22355926236960,11539059971879,21398924798685,14767060954108,20427624096416,17449352860407,
    19709821867861,19624709514190,19480627535590,21311757858875,19938551412131,22478380460836,
    21240650562250,23021938691933,23491790030913,22756293567284,26734598788794,21402363741075,
    30938691484757,18565422593546,35975610861054,13684262931795,41530953285211,5965195492534,
    46879689502178,5595951759384,50481965783551,21885739443027,49525641163804,42804504362148,
    39825593010589,65855656014411,16646370784136,84636454545048,23203022148630,87815340555421,
    77712434379839,59221697755372,133156149403600,17931182484676,153854603407275,143256991001755,
    77641204145858,256622722144404],
   [146897741844998,187322535981237,404748991156647,223126528785715,306721565474814,
    855399085675632,1105847988847754,983047624018124,644853044378926,307872297487558,
    94990622450370]]
private def rkmXsWin_w64_s7_in_p0 : List ℤ := pzigCat
  [
   [214141452,780965661,2009945592,3646761527,5890906210,8526624873,11619917348,15303487065,
    19127319094,23513908809,28251183584,33217410805,38524687902,44028490305,49615686454,
    55266011599,60666426298,65917567323,70396147092,74044270231,76836477644,78088029133,
    77848423492,75717661671,71569963950,65307210965,56810520432,46374081313,34365386742,
    21037495683,7385422796,6077187196,17993714845,27160525706,32840622017,33386592490,
    27915632793,15567651002,4408584174,32153635019,67513021276,110066687027,158516029860,
    211789173237,268137544184,325988542263,383730256870,439804784651,493428760192,544195427083,
    591970546962,638095551505,683542863638,730051805459,779617870218,833335503171,892100838090,
    955320840109,1021003025622,1085644778547,1143976472698,1189394709187,1214657669896,
    1212029260239,1175352578004,1099806223197,983471261516,828047913557,638512757892,
    423722827383,195718314704,32248526320,245171465525,429184077868,571978737179,663478874098,
    697600749283,671287509268,584940587057,442716787834,251658890969,21903527530,232706032698,
    495774702871,746982128800,963576794733,1121765677566]]
private def rkmXsWin_w64_s7_in_p1 : List ℤ := pzigCat
  [
   [1198176435145,1173305330846,1035468060869,783219837344,429449709895,1567626856,459169192700,
    900435679941,1265153219038,1499152286035,1558637131102,1419650681935,1083273428096,
    579354776223,33382046139,672965366918,1244011497899,1650550635708,1813357195339,
    1685265428066,1265228862697,605586926660,190874274978,983686567455,1617827569550,
    1956521467261,1912204577078,1472636716537,713007272814,213139862870,1103151733845,
    1749966891302,1995265033141,1772338738468,1129415038559,223739932106,716127208774,
    1449931017395,1790438448532,1657603690337,1101196009062,286565324259,553472743977,
    1187373088628,1452822689871,1300913213420,806198829303,137486534478,499168146198,
    925242335727,1040957850186,849766395091,446141393968,23690022320,412715863287,619709980864,
    615259324941,439540023054,179856451453,67059358825,229723573120,282355266531,245504889062,
    168778573657,102014915186,70112964181,62624512166,41884366233,30775023145,164035403324,
    318812675999,415808302038,369237521315,138658027534,230639836678,603830405423,800577495842,
    678016454045,217916407266,432846298082,999236651727,1191632996568,851653506714,60228866874,
    862803286610,1482902773664,1455697223852]]
private def rkmXsWin_w64_s7_in_p2 : List ℤ := pzigCat
  [
   [717985005162,441143511004,1485579227118,1880771530002,1370677699998,139964452580,
    1239756400370,2074880504256,1903142614242,752342722932,837703995034,2064887899098,
    2272063777188,1305130315122,377436555743,1916556722626,2490770235000,1758532120192,
    65704439306,1708839448942,2606415883524,2108391480322,441376065602,1513048839920,
    2676906332506,2370894929764,717075499080,1389325323022,2754513025830,2561327371254,
    867099215382,1383494703790,2872547284558,2680148994248,863776537390,1525183980276,
    3036769117412,2704703396236,677201464932,1821323537913,3218983007045,2590202192359,
    284057389625,2247385852045,3356319413363,2279380860531,319623855834,2741386478571,
    3358236661939,1719197334857,1103392429765,3201272687109,3119926499125,881676298581,
    1987653378872,3487305750298,2541250161324,212238681697,2831377587300,3432918750672,
    1557352301692,1460316263050,3423745881548,2874061077366,191561754088,2643916290716,
    3503902492470,1718956894314,1377180776669,3426216128365,2841571357281,56357770997,
    2774505530965,3432631511071,1386028330045,1757838943407,3498609688927,2434114993165,
    591106217670,3134712352609,3121864676615,549879296113,2476745185265,3451994064471,
    1547727244929,1662487906801,3480640583249]]
private def rkmXsWin_w64_s7_in_p3 : List ℤ := pzigCat
  [
   [2345589828747,808572802810,3290807453790,2933885263994,126957566,2970732001942,3335635255575,
    709175028201,2601105789209,3589906055421,1289058100457,2247648657111,3739300784961,
    1726569707581,1959003589321,3819698901207,2016839260017,1766389900939,3854183406057,
    2158207630351,1683726660649,3849925940577,2150345522779,1706827060723,3797813377239,
    1996015527683,1812083190105,3675501337997,1707315498475,1955978331123,3456202385095,
    1313966428237,2077793936799,3121938725565,872774629979,2109410425375,2683498377693,
    470248428566,1997298703466,2200137130239,211027158397,1736463441492,1790780308078,
    181986600375,1409529133505,1615686898961,390255765192,1208168988420,1812346365153,
    691309952502,1400298778442,2380895578869,751057365534,2210499122024,3055921541233,
    113093102527,3612370018428,3253614742131,1574511923605,5115340218332,2221945414247,
    4194672793781,5724090624536,529680322880,6847412459263,4281101814456,4635207079381,
    7918069733445,236177022380,8509031364797,5801399516986,5502416442413,9730893533504,
    129893767773,10340401349118,6365572408503,7228800471510,10979139296231,1340942390612,
    12365088117430,5477063792641,10027895497549,11173567096134,4623985062854,14148374563372,
    2372866569124,13657485379884]]
private def rkmXsWin_w64_s7_in_p4 : List ℤ := pzigCat
  [
   [9192721266508,9894278146059,14277372326782,3794347378142,16628869621399,3313155803584,
    15939397390131,10074742946875,12525631276214,15400975844370,7135265765073,18624974447675,
    709096240062,19530960547799,5835113051569,18283421001413,11754202230190,15304008838910,
    16556501681268,11136631917351,20011471400981,6332240832887,22114008837101,1366962614380,
    23023946130536,3400889675597,23002082424307,7741061242862,22355926236960,11539059971880,
    21398924798686,14767060954108,20427624096416,17449352860408,19709821867862,19624709514189,
    19480627535589,21311757858875,19938551412131,22478380460836,21240650562250,23021938691934,
    23491790030914,22756293567284,26734598788794,21402363741075,30938691484757,18565422593546,
    35975610861054,13684262931795,41530953285211,5965195492534,46879689502178,5595951759384,
    50481965783551,21885739443027,49525641163804,42804504362148,39825593010589,65855656014411,
    16646370784136,84636454545048,23203022148630,87815340555421,77712434379839,59221697755372,
    133156149403600,17931182484676,153854603407276,143256991001756,77641204145858,
    256622722144404,146897741844998,187322535981238,404748991156648,223126528785716,
    306721565474814,855399085675632,1105847988847754,983047624018124,644853044378926,
    307872297487558,94990622450370]]
private def rkmXsWin_w64_s7_in : List ℤ :=
  rkmXsWin_w64_s7_in_p0 ++ (rkmXsWin_w64_s7_in_p1 ++ (rkmXsWin_w64_s7_in_p2 ++
    (rkmXsWin_w64_s7_in_p3 ++ rkmXsWin_w64_s7_in_p4)))
private def rkmXsWin_w64_s7_out : List ℤ := pzigCat
  [
   [531379190,1448442369,2902276384,4868725687,7098039908,9900739139,13006331688,16625776437,
    20481317064,24497589087,29062691502,33652300915,38492922872,43435250731,48323841154,
    53234040339,57978379276,62350881849,66338901596,69576181065,72156221524,73645662205,
    73864288816,72747372369,70052052392,65915043501,59953068156,52435695433,43574064812,
    33478511841,22710119924,11575739185,1001754842,8495687508,16028237621,20541591200,
    21486168047,17522409634,8218197873,6982580605,28744917892,56921276293,91580475732,
    132069133693,177786826452,227850116391,280912059108,335771294171,391347562810,446225672623,
    499596270334,550599266917,599174230108,645292931409,689292338262,732052894769,774199889946,
    816972904379,860686163676,905548494507,951458295926,996651610545,1039195539006,1075811457201,
    1102504010704,1114877082733,1107848917540,1077061133291,1018683969854,930411475551,
    811759919232,664452761195,492880467696,303728073379,105597568588,90547353276,273718188791,
    432368897538,555988878175,636259726860,666879317461,645266771576,571744173591,450056748756,
    287263009241,92819144866,121410243220,342383925015,555725077498,746613309055,900781001778,
    1004457249193,1045562094514,1015394092671,908309429778,724605805923,470831568446,
    160779784741,184224224599,536491168522,862631492981,1127790734464,1298948280723,
    1348876715494,1261185606295,1033457533686,680161698271,232618124788,263036632622,
    749589050617,1165736330638,1453987665499,1568090804582,1482286649415,1195559127652,
    735455972931,156858223310,463920551338,1037408844503,1474739453628,1700932915925,
    1668602837004,1369603279799,839428610818,155911315673,570376108921,1213756435810,
    1655024466073,1805083018472,1625340232861,1138534755626,430264158151,365659074597,
    1091323389812,1596929603349,1774608980200,1583536205477,1062353894766,323933489011,
    468859224045],
   [1139258795766,1537848163575,1579150583864,1261897034959,670767166680,46068432216,
    713639322063,1174186405182,1327493186511,1153922468764,716571846391,142085749754,
    416590314214,821404424003,984284492680,887927255131,583554229132,172284348377,227825826835,
    515863899286,633362799099,575956614754,387338509355,139447793340,91654785136,249435420115,
    310510509496,284513839381,205355412436,113412601073,39517237000,5167846624,30112260151,
    56789251092,104210527613,176440609312,255353190639,304787759516,284960550543,170625804008,
    30516246814,272309142411,479785350432,573523534919,502871021010,272805153433,48366492173,
    345298714752,498893014477,436759335872,170885829669,196971964961,511809435388,632958086259,
    501139714662,174672977933,192877039029,429064843738,434310194973,242663335452,6793046571,
    93158305919,34268211139,323961422438,588142865007,643993916676,448706732587,140825083380,
    58036631674,18085427803,186392489845,336809354316,265025842963,19191206526,167000146942,
    98093670161,174176349179,379280489174,295049251121,8058443441,223445085824,136217851013,
    135975716889,278192326848,149690739375,59032865567,92602789184,23591451628,40419839809,
    126153362913,249686725484,151730084765,35893512098,210840082403,549030013854,584561181655,
    238769367008,39955171765,331259001888,655377939827,436768745074,37718023998,56145007095,
    286282193991,248808510000,169258637462,181754798927,262933571817,317604328246,49956776062,
    115247662688,711748298021,490705955266,351761701616,179844811261,746182071675,343096674866,
    1097187767560,1023875737137,329177389777,146826010310,1216783570914,724486120951,
    973988472787,485566994510,1314224932362,643588322051,1494828795989,836096824372,
    1771239116600,1614214062457,1105409618177,1860060740886,93161886197,754418605757,
    192165339859,921137447952,596157717411,148276514950,59298581527],
   [610913463499,1544696237142,553861428275,1398882834445,1327865041730,156792800794,
    821099166439,477442531475,1971572258792,994073739313,467158312002,1664003742101,
    1457180375354,39783928896,464835850071,2231179613785,1964761809406,1865077746482,
    2879311283235,1342877602896,1560125738532,1536555184126,715615419472,1487673469351,
    2771045057532,2491444109608,713440788839,1213866874370,2658082000140,1155681630652,
    189039892531,2627674129260,3735748694012,1006477537675,227633557423,3854702031554,
    1324159797106,928864865822,3342000566748,293138698436,403381085305,2917233609426,
    2313244121388,2629368824052,2407398843114,318641035734,1418755043220,2934630290522,
    435188125060,2482783996908,435847968866,2397392019724,6491331598336,3744437359172,
    813772754924,2125000597062,17660518909,943631405545,629568972464,1579450516001,603513887171,
    1068107088925,2046200072773,690408391681,2842599080823,5216498125787,4014857977365,
    2571931719185,1675622390991,500859151368,498970032001,1057859162119,1839623411922,
    666054302382,678817277236,3057093373504,1867114928208,2689813547434,6123535635226,
    2208686152132,1891741425576,2746414186414,2054788491197,3148483004034,3360652567857,
    3231863872968,8585659944049,4674756008610,13315156710577,9244163934794,8446179507083,
    1119636561546,833676646622,3155154106225,9378465290557,3046137888620,8454132576857,
    3020376200887,1999181076290,2930856661121,1569235013662,5058878925840,6371167958083,
    6382460243552,3335797099289,1660099714660,3807667492027,4312719158983,6003058768342,
    11056661168523,1350064658120,118836587000,11561533523597,7815304605148,9362989943807,
    864339492801,2318720363995,5474685550511,3135054136438,11897483100987,8353846492192,
    13725796888731,3666872882500,2191034991991,3441616519209,8512467865695,10054044212886,
    16092127968359,1603637600237,10482562630446,15033516181209,3196476394330,5698520039800,
    2965672552787,5197530266965,6290449574408,2868457033973,154731214554,2884777239858,
    8830661367453],
   [7841519194972,1451719559936,7379444143273,852112713206,8326231403216,7255200993867,
    5029039195958,10574567355325,5661203571376,1978164963234,883590004183,11582990493722,
    4574786337063,16925702528701,4468657396588,13510784812468,29265798512531,686732799552,
    12772249261572,6319459642967,12157849296168,6183001988247,1424739551,2513761057302,
    1860734165204,1603283904901,10436587240433,5195296127524,8549527891428,4861876411166,
    13995832825498,20686662226608,10823408492298,19606433197565,21046471644007,14766238216636,
    20982801385826,3049139296222,7189988031601,21975322110649,15553044735625,9232859362672,
    4566264879873,18164133353351,16722382399760,13086756947622,30410999690141,16259948990909,
    33819315170716,20424773757811,26475239798499,6470178613757,37627981842004,57654423639569,
    40382967291500,80796949927304,9166338287068,11443390534621,58441113859589,99298727933344,
    97453522959939,27494931451735,159556334525728,76939561910691,18446157038706,12430830432798,
    45289967451344,9823138073982,120811241280269,138913897655426,28154762191003,56144935728077,
    62465844444642,85607165475617,82945877195820,65224857005698,177628551096579,52629134271528,
    77647122205324,168088001389935,219271049495126,393668862865176,225783930410175,
    281701497475174,1858482595221906]]
private def rkmPhb_w64_s6b : List ℕ := uNatCatN
  [
   [710760761107562,710292130629101,709820734544520,709346573830995,708869649435963,
    708389962277058,707907513242048,707422303188767,706934332945048,706443603308648,
    705950115047183,705453868898045,704954865568332,704453105734762,703948590043598,
    703441319110563,702931293520752,702418513828547,701902980557525,701384694200370,
    700863655218773,700339864043341,699813321073493,699284026677365,698751981191701,
    698217184921749,697679638141155,697139341091851,696596293983940,696050496995587,
    695501950272893,694950653929783,694396608047877,693839812676369,693280267831897,
    692717973498415,692152929627057,691585136136005,691014592910351,690441299801952,
    689865256629292,689286463177333,688704919197366,688120624406862,687533578489314,
    686943781094084,686351231836239,685755930296391,685157876020529,684557068519853,
    683953507270599,683347191713866,682738121255436,682126295265600,681511713078962,
    680894373994265,680274277274189,679651422145165,679025807797176,678397433383554,
    677766298020780,677132400788276,676495740728193,675856316845200,675214128106262,
    674569173440425,673921451738584,673270961853264,672617702598378,671961672749000,
    671302871041118,670641296171397,669976946796928,669309821534977,668639918962731,
    667967237617037,667291775994143,666613532549424,665932505697113,665248693810029,
    664562095219289,663872708214030,663180531041114,662485561904841,661787798966643,
    661087240344788,660383884114067,659677728305484,658968770905939,658257009857906,
    657542443059104,656825068362164,656104883574296,655381886456944,654656074725434,
    653927446048630,653195998048566,652461728300088,651724634330480,650984713619092,
    650241963596958,649496381646408,648747965100673,647996711243492,647242617308700,
    646485680479821,645725897889649,644963266619824,644197783700399,643429446109409,
    642658250772418,641884194562077,641107274297661,640327486744606,639544828614034,
    638759296562280,637970887190400,637179597043679,636385422611127,635588360324975,
    634788406560150,633985557633756,633179809804537,632371159272336,631559602177545,
    630745134600546,629927752561143,629107452017985,628284228867985,627458078945719,
    626628998022825,625796981807391,624962025943332,624124126009753,623283277520311,
    622439475922561,621592716597292,620742994857853,619890305949468,619034645048545],
   [618176007261962,617314387626359,616449781107400,615582182599037,614711586922756,
    613837988826814,612961382985460,612081763998144,611199126388719,610313464604623,
    609424773016049,608533045915104,607638277514956,606740461948960,605839593269775,
    604935665448465,604028672373589,603118607850266,602205465599239,601289239255906,
    600369922369353,599447508401357,598521990725380,597593362625540,596661617295575,
    595726747837775,594788747261910,593847608484129,592903324325849,591955887512619,
    591005290672964,590051526337218,589094586936323,588134464800622,587171152158619,
    586204641135725,585234923752978,584261991925744,583285837462394,582306452062956,
    581323827317744,580337954705964,579348825594298,578356431235454,577360762766700,
    576361811208363,575359567462311,574354022310397,573345166412885,572332990306836,
    571317484404476,570298638991529,569276444225517,568250890134033,567221966612980,
    566189663424780,565153970196542,564114876418211,563072371440661,562026444473776,
    560977084584472,559924280694701,558868021579404,557808295864427,556745092024409,
    555678398380608,554608203098706,553534494186561,552457259491911,551376486700048,
    550292163331431,549204276739263,548112814107013,547017762445891,545919108592278,
    544816839205097,543710940763136,542601399562312,541488201712888,540371333136629,
    539250779563895,538126526530683,536998559375605,535866863236802,534731423048795,
    533592223539271,532449249225802,531302484412494,530151913186567,528997519414859,
    527839286740263,526677198578078,525511238112287,524341388291760,523167631826362,
    521989951182989,520808328581509,519622745990617,518433185123601,517239627434007,
    516042054111216,514840446075919,513634783975483,512425048179226,511211218773574,
    509993275557113,508771198035523,507544965416400,506314556603959,505079950193606,
    503841124466394,502598057383339,501350726579609,500099109358572,498843182685700,
    497582923182334,496318307119291,495049310410322,493775908605406,492498076883883,
    491215790047421,489929022512802,488637748304534,487341941047275,486041573958073,
    484736619838403,483427051066002,482112839586505,480793956904852,479470374076485,
    478142061698310,476808989899429,475471128331616,474128446159562,472780912050839,
    471428494165611,470071160146066,468708877105554,467341611617440,465969329703651],
   [464591996822897,463209577858584,461822037106373,460429338261402,459031444405147,
    457628317991900,456219920834878,454806214091919,453387158250773,451962713113959,
    450532837783188,449097490643317,447656629345836,446210210791858,444758191114598,
    443300525661328,441837168974776,440368074773958,438893195934422,437412484467877,
    435925891501181,434433367254675,432934861019828,431430321136166,429919694967464,
    428402928877163,426879968202991,425350757230750,423815239167231,422273356112234,
    420725049029646,419170257717543,417608920777273,416040975581479,414466358241015,
    412885003570716,411296845053959,409701814805972,408099843535844,406490860507157,
    404874793497200,403251568754698,401621110955973,399983343159493,398338186758712,
    396685561433133,395025385097510,393357573849110,391682041912918,389998701584724,
    388307463171954,386608234932168,384900923009082,383185431366012,381461661716608,
    379729513452733,377988883569354,376239666586281,374481754466605,372715036531646,
    370939399372248,369154726756205,367360899531631,365557795526035,363745289440884,
    361923252741396,360091553541295,358250056482247,356398622607680,354537109230651,
    352665369795430,350783253732418,348890606306017,346987268455011,345073076625024,
    343147862592556,341211453280069,339263670561587,337304331058171,335333245922655,
    333350220612917,331355054652949,329347541380905,327327467683258,325294613714107,
    323248752598617,321189650119488,319117064385235,317030745478990,314930435086401,
    312815866101090,310686762206003,308542837428811,306383795669386,304209330197175,
    302019123116089,299812844794318,297590153256208,295350693533086,293094096969582,
    290819980481676,288527945762290,286217578429830,283888447114599,281540102477433,
    279172076154332,276783879620140,274375002963573,271944913564978,269493054667224,
    267018843828998,264521671248428,262000897943538,259455853774279,256885835288967,
    254290103375688,251667880696671,249018348880570,246340645444192,243633860411091,
    240897032589740,238129145468473,235329122677809,232495822963161,229628034601756,
    226724469186805,223783754689044,220804427690247,217784924664680,214723572161895,
    211618575716778,208468007279268,205269790914853,202021686475986,198721270881101,
    195365916558420,191952766511517,188478705336250,184940325355538,181333886827762],
   [177655270909905,173899923694996,170062789162454,166138228232770,162119920236369,
    158000741889301,153772617163075,149426329007881,144951280369744,140335186741744,
    135563674634086,130619748187956,125483066807819,120128944910110,114526930781961,
    108638725468147,102415023335092,95790501005980,88675425652092,80940591226068,72387663809537,
    62682725007772,51174592761507,36181872118644]]
private def rkmPhb_w64_s7 : List ℕ := uNatCatN
  [
   [737450516873437,737194380963034,736935325154576,736673352609878,736408466460573,
    736140669808180,735869965724171,735596357250045,735319847397385,735040439147926,
    734758135453614,734472939236668,734184853389635,733893880775451,733600024227491,
    733303286549623,733003670516261,732701178872413,732395814333728,732087579586542,
    731776477287926,731462510065723,731145680518593,730825991216048,730503444698494,
    730178043477265,729849790034656,729518686823955,729184736269477,728847940766589,
    728508302681739,728165824352482,727820508087503,727472356166638,727121370840899,
    726767554332486,726410908834811,726051436512506,725689139501445,725324019908749,
    724956079812799,724585321263244,724211746281009,723835356858299,723456154958603,
    723074142516694,722689321438631,722301693601756,721911260854692,721518025017335,
    721121987880849,720723151207659,720321516731434,719917086157084,719509861160738,
    719099843389732,718687034462592,718271435969011,717853049469833,717431876497027,
    717007918553660,716581177113878,716151653622869,715719349496839,715284266122978,
    714846404859424,714405767035231,713962353950332,713516166875493,713067207052281,
    712615475693013,712160973980717,711703703069080,711243664082404,710780858115550,
    710315286233890,709846949473251,709375848839858,708901985310274,708425359831342,
    707945973320121,707463826663822,706978920719743,706491256315195,706000834247438,
    705507655283606,705011720160629,704513029585160,704011584233496,703507384751493,
    703000431754488,702490725827210,701978267523693,701463057367187,700945095850065,
    700424383433731,699900920548520,699374707593603,698845744936883,698314032914893,
    697779571832692,697242361963753,696702403549856,696159696800973,695614241895157,
    695066038978418,694515088164609,693961389535299,693404943139650,692845748994292,
    692283807083187,691719117357501,691151679735467,690581494102248,690008560309795,
    689432878176705,688854447488074,688273267995351,687689339416183,687102661434262,
    686513233699169,685921055826212,685326127396266,684728447955606,684128017015737,
    683524834053223,682918898509513,682310209790764,681698767267658,681084570275219,
    680467618112628,679847910043028,679225445293335,678600223054038,677972242479001,
    677341502685259,676708002752810,676071741724406,675432718605339,674790932363223],
   [674146381927774,673499066190583,672848984004893,672196134185362,671540515507829,
    670882126709078,670220966486588,669557033498292,668890326362324,668220843656761,
    667548583919370,666873545647338,666195727297010,665515127283613,664831743980984,
    664145575721288,663456620794734,662764877449283,662070343890358,661373018280547,
    660672898739295,659969983342600,659264270122700,658555757067759,657844442121537,
    657130323183072,656413398106342,655693664699931,654971120726684,654245763903362,
    653517591900287,652786602340986,652052792801823,651316160811633,650576703851347,
    649834419353607,649089304702383,648341357232580,647590574229638,646836952929125,
    646080490516332,645321184125849,644559030841145,643794027694136,643026171664748,
    642255459680474,641481888615926,640705455292371,639926156477271,639143988883813,
    638358949170424,637571033940293,636780239740868,635986563063362,635190000342240,
    634390547954703,633588202220161,632782959399705,631974815695558,631163767250532,
    630349810147466,629532940408658,628713153995290,627890446806847,627064814680515,
    626236253390583,625404758647828,624570326098896,623732951325663,622892629844597,
    622049357106108,621203128493877,620353939324193,619501784845260,618646660236508,
    617788560607883,616927480999134,616063416379082,615196361644879,614326311621257,
    613453261059764,612577204637986,611698136958760,610816052549370,609930945860733,
    609042811266572,608151643062572,607257435465527,606360182612468,605459878559783,
    604556517282315,603650092672452,602740598539197,601828028607227,600912376515931,
    599993635818437,599071799980619,598146862380094,597218816305189,596287654953907,
    595353371432861,594415958756203,593475409844522,592531717523734,591584874523947,
    590634873478307,589681706921828,588725367290197,587765846918565,586803138040304,
    585837232785763,584868123180981,583895801146390,582920258495495,581941486933526,
    580959478056069,579974223347670,578985714180422,577993941812515,576998897386771,
    576000571929147,574998956347212,573994041428598,572985817839421,571974276122673,
    570959406696592,569941199852987,568919645755550,567894734438125,566866455802947,
    565834799618855,564799755519460,563761313001292,562719461421902,561674189997935,
    560625487803160,559573343766473,558517746669848,557458685146264,556396147677579],
   [555330122592373,554260598063747,553187562107071,552111002577703,551030907168651,
    549947263408199,548860058657472,547769280107975,546674914779058,545576949515353,
    544475370984143,543370165672691,542261319885505,541148819741552,540032651171420,
    538912799914414,537789251515596,536661991322767,535531004483382,534396275941405,
    533257790434096,532115532488730,530969486419250,529819636322850,528665966076480,
    527508459333284,526347099518955,525181869828019,524012753220029,522839732415688,
    521662789892882,520481907882622,519297068364904,518108253064478,516915443446514,
    515718620712183,514517765794132,513312859351860,512103881766989,510890813138424,
    509673633277412,508452321702479,507226857634255,505997219990173,504763387379058,
    503525338095573,502283050114548,501036501085168,499785668325026,498530528814033,
    497271059188181,496007235733160,494739034377817,493466430687455,492189399856972,
    490907916703828,489621955660839,488331490768794,487036495668882,485736943594938,
    484432807365482,483124059375566,481810671588407,480492615526804,479169862264341,
    477842382416353,476510146130661,475173123078065,473831282442578,472484592911411,
    471133022664685,469776539364867,468415110145920,467048701602159,465677279776807,
    464300810150224,462919257627823,461532586527646,460140760567584,458743742852251,
    457341495859473,455933981426400,454521160735214,453102994298431,451679441943763,
    450250462798554,448816015273744,447376057047366,445930545047544,444479435434990,
    443022683584959,441560244068671,440092070634149,438618116186478,437138332767441,
    435652671534529,434161082739284,432663515704956,431159918803450,429650239431530,
    428134423986255,426612417839614,425084165312327,423549609646780,422008692979063,
    420461356310066,418907539475595,417347181115481,415780218641618,414206588204905,
    412626224661031,411039061535062,409445030984776,407844063762688,406236089176715,
    404621035049414,402998827675732,401369391779202,399732650466516,398088525180393,
    396436935650680,394777799843579,393111033908940,391436552125512,389754266844052,
    388064088428204,386365925193025,384659683341058,382945266895811,381222577632535,
    379491515006152,377751976076184,376003855428555,374247045094067,372481434463411,
    370706910198509,368923356140007,367130653210695,365328679314656,363517309231889],
   [361696414508173,359865863339891,358025520453548,356175246979662,354314900320721,
    352444334012850,350563397580822,348671936386018,346769791466917,344856799371652,
    342932791982156,340997596329372,339051034398964,337092922926927,335123073184457,
    333141290751363,331147375277286,329141120229909,327122312629273,325090732767268,
    323046153911255,320988341990732,318917055265820,316832043976290,314733049969688,
    312619806307051,310492036844505,308349455788958,306191767225866,304018664616920,
    301829830265275,299624934745722,297403636296941,295165580172740,292910397948806,
    290637706781220,288347108612544,286038189320905,283710517806968,281363645013195,
    278997102869138,276610403155828,274203036281573,271774469960540,269324147784553,
    266851487677348,264355880219250,261836686828772,259293237785879,256724830079780,
    254130725061808,251510145881392,248862274680108,246186249515331,243481160980948,
    240746048487869,237979896161533,235181628307083,232350104385222,229484113432632,
    226582367850046,223643496468128,220666036785861,217648426257465,214588992481336,
    211485942117060,208337348322994,205141136465733,201895067801762,198596720768200,
    195243469440120,191832458611740,188360574831523,184824412558177,181220234393994,
    177543924077474,173790930555843,169956200977422,166034099797038,162018310306644,
    157901713686867,153676238970927,149332674885875,144860431019520,140247230564354,
    135478709039280,130537881237771,125404419312919,120053653153043,114455150131123,
    108570635296106,102350833917106,95730463559247,88619847634562,80889861076594,72342294274308,
    62643438118945,51142518684697,36159194846918]]
private def bAll4 (a b c d : Bool) : Bool :=
  match a, b, c, d with | true, true, true, true => true | _, _, _, _ => false
private theorem bAll4_elim {a b c d : Bool} (h : bAll4 a b c d = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | exact ⟨rfl, rfl, rfl, rfl⟩ | exact Bool.noConfusion h
private theorem rkmStatOk_hiw64t12 : bAll4
  (
    muxIntListEq (uHb rkmPhb_w64_s6b)
      (altBuildHbFrom 1856 1024 19587930735 580 444))
  (
    muxIntListEq (uHb rkmPhb_w64_s7)
      (altBuildHbFrom 1856 1024 19575653846 505 519))
  (
    muxIntListEq rkmXsWin_w64_s6a_out rkmXsWin_w64_s6b_in)
  (
    Nat.ble (Nat.add 844 (altIntLen rkmXsWin_w64_s6a_in)) (Nat.add 1024 1))
  = true := by decide +kernel
private theorem rkmStatOk_hiw64t12_p :
    muxIntListEq (uHb rkmPhb_w64_s6b)
      (altBuildHbFrom 1856 1024 19587930735 580 444) = true ∧
    muxIntListEq (uHb rkmPhb_w64_s7)
      (altBuildHbFrom 1856 1024 19575653846 505 519) = true ∧
    muxIntListEq rkmXsWin_w64_s6a_out rkmXsWin_w64_s6b_in = true ∧
    Nat.ble (Nat.add 844 (altIntLen rkmXsWin_w64_s6a_in)) (Nat.add 1024 1) = true :=
  @bAll4_elim
  (
    muxIntListEq (uHb rkmPhb_w64_s6b)
      (altBuildHbFrom 1856 1024 19587930735 580 444))
  (
    muxIntListEq (uHb rkmPhb_w64_s7)
      (altBuildHbFrom 1856 1024 19575653846 505 519))
  (
    muxIntListEq rkmXsWin_w64_s6a_out rkmXsWin_w64_s6b_in)
  (
    Nat.ble (Nat.add 844 (altIntLen rkmXsWin_w64_s6a_in)) (Nat.add 1024 1))
  rkmStatOk_hiw64t12
private theorem rkmHhb_w64_s6b :
    uHb rkmPhb_w64_s6b = rkmDropInts 580 rkmHbWin_w64_s6a :=
  (muxIntListEq_eq_true.mp rkmStatOk_hiw64t12_p.1).trans
    (drHb 1856 1024 19587930735 580 1024)
private theorem rkmHhb_w64_s7 :
    uHb rkmPhb_w64_s7 = rkmDropInts 505 rkmHbWin_w64_s7 :=
  (muxIntListEq_eq_true.mp rkmStatOk_hiw64t12_p.2.1).trans
    (drHb 1856 1024 19575653846 505 1024)
private def rkmC_w64_s6b_1 : List ℤ := pzigCat
  [
   [557385733,1626572590,3315311475,5796028432,8814218945,12364085826,16808074779,21707451858,
    27364849123,33777844374,40655945993,48038932766,56043549997,64062301792,71747435973,
    79099600140,85132170927,89373949366,91185969415,89890436440,84808369089,75768361720,
    62593216225,45377391168,25245784947,3378932640,18789412638,38657941183,54064377242,
    62713077311,62135131186,50338098237,26612761856,9522722284,57325445337,114390085726,
    177768984957,243658421076,308034518663,367168059724,419379036713,464429906762,504564591103,
    545120564176,592739780301,654239543328,735579031863,839442013352,963427359985,1099392453258,
    1234655870439,1351930988090,1433064763859,1462652659414,1430220796381,1332010563632,
    1171710163175,959112361508,707023253947,429066419944,139666985741,146779477055,413836458630,
    641389210141,804685350922,877266483187,836058116034,666639155601,370141975016,31979720432,
    498658743729,972414176282,1385401128607,1664557822824,1739877351489,1555926726820,
    1087438287881,358275456348,540679579218,1446828400727,2145003066722,2418180732383,
    2120486466866,1248657749609,18324274123,1343322816454,2323186409855,2626573802204,
    2126488438397,968543580256,464046941970,1682882201515,2277123123406,2069323550385,
    1178862234750,32610490428,1109907660545,1680908226036,1590300229581,941009975178,35662882485,
    754642805883,1138833596506,1018140802273,516817734088,86912079468,502409462217,575795140928,
    365098615599,87347656162,40611583242,33980049340,156582108763,93531988656,245717800662,
    670912750627,800914712124,360927115679,526021451819,1314241263990,1368450849147,460626463356,
    949283375324,1926080034595,1689296130706,234303148639,1547171496631,2410957736534,
    1641040904897,360503182849,2251137078514,2644885844549,1134603701886,1308289648546,
    2926931617677,2433813269252,48522790881,2515249302483,3247721833358,1428372759311],
   [1647277161949,3531489085866,2570196625205,604224999211,3402792920906,3374477901535,
    393028816102,3041091175674,3865358378299,1217177860102,2617492361026,4130194225525,
    1817683944064,2264982270302,4268267589273,2184581038470,2073732592892,4354095809121,
    2315456538658,2093095219102,4415084793087,2198921179782,2329164946260,4426719326389,
    1821525487444,2739845582924,4328151350921,1187568944348,3244413165844,4054006443535,
    325872357114,3754281306468,3551373373899,736630138977,4188957386750,2741424969829,
    1999358678129,4413176258638,1460376867205,3403173913419,4105486169328,464329595544,
    4592266355577,2758460544868,2865391422084,4747951150943,96894181904,4800586408010,
    2966767852743,3142258841961,4714174834474,606060541120,4939606381007,1842826187390,
    3855885309316,3485957556561,2047849378685,4018974867628,182029397728,3523923080749,
    1213319344166,2326558216504,1848693383647,830274241781,1669804522660,613725537171,
    791644770255,1774957107504,584422981085,2557206206839,2242173884152,2975373446728,
    3997867431771,3116950993997,5722468568294,3106813676418,7345280807943,3084425323109,
    8843166845678,3195524220838,10216985526121,3593878215865,11457738943512,4441855681860,
    12506104032617,5897981370323,13211936095866,8083975381576,13303421949009,11026071052833,
    12377672566356,14564465972134,9934730600021,18231238928653,5500637199156,21135079626794,
    1107182381306,21969967555119,9395285059803,19311987251354,17888637918220,12241157198441,
    24205374857391,1038861648470,25614749765692,12394475465652,19826971114475,24369948811967,
    6015360866104,29403314657308,13243809663334,21709470179117,29704708417571,311150286516,
    31345243639822,25097587574876,11756859505955,36466653651787,20192088665311,20005039436412,
    40798576925270,19110118721982,24511155566555,47172913379663,25447856676665,23014590218606,
    55885839930050,43187331431636,7670129924807,57871093254823,66986475651137,22704025111615,
    50281696230564,106335280338610,107552853680584,46764292293798,47553831735943,125170060634775,
    137684053028333,59445227433699],
   [103135903275818,315992947807860,531405336504302,704475705709116,805643395076442,
    825850978684618,774499188920750,672771861401806,545685143045334,415558195526218,
    298267025089584,202316590610870,129930269664580,79096050431046,45671039661062,25017001142540,
    12995468061434,6397022524924,2979886989668,1310826892218,542587641974,210307602814,
    75432502298,24429306272,6654273556,1127808768]]
private def rkmC_w64_s6b_2 : List ℤ := pzigCat
  [
   [760929174,2096353769,3919461578,6470111409,9661537634,13321306675,17711653512,22796190135,
    28260727752,34577813897,41385440772,48571121085,56167396346,63858058603,71173360136,
    78024622395,83797711966,87644266803,89417848976,88228798943,83602634312,75318009705,
    63175464824,47263828631,28616088684,8092075095,13063642267,32406023408,48045791585,
    57829025706,59451332339,51017197256,31588886223,349839694,42211806400,94385036907,
    154067644936,217976866583,282521668748,344244453119,400866724616,450839912573,495040177138,
    536771269797,580483390526,632172252101,698142346940,782386952611,885930856540,1005585296699,
    1133073219114,1255285405197,1356886732198,1421436369143,1434552514016,1386937761437,
    1275914224192,1105344136801,884894193274,628924194477,352536042842,71121910419,199894748999,
    444878536100,646851693937,786149557706,841415851243,793796099904,631458169373,354248094494,
    20443554228,456774180791,902476686630,1294635140139,1566564040914,1657052675405,
    1520774201064,1137992274113,525541966000,252035446700,1077697388599,1790090115822,
    2211497686119,2191561706234,1662472627761,685529366644,534128499096,1681862605365,
    2418814797764,2494611667123,1847629206254,650845694561,727760998543,1843154244606,
    2331665617685,2046601581054,1114544968455,113528376901,1197281338420,1774002795099,
    1687498399448,1032151888421,99242069072,747508164948,1212195722225,1171956622124,
    708879327679,61116658470,486127104690,725705782635,616858607998,290604085089,34017698493,
    184131677732,138905399949,32760260544,43320367585,233118173044,465209330661,479163103566,
    103056022567,551038316293,1079711787678,1029466252167,252836318948,885846699806,
    1660074228659,1449248025236,224536196217,1320537373375,2157228808018,1617995806999,
    74622488745,1859489191832,2503216109625,1461937699810,664162215946,2454618772213,
    2613669687626,915041534039],
   [1537886288271,3001045376220,2324128056539,129610996809,2613884488578,3215624991539,
    1340480042514,1685447966544,3504355773373,2563368038088,521693899950,3296383087037,
    3404417510226,623413727419,2781976137653,3872878039438,1596345120193,2152095152001,
    4060938452388,2337700851407,1557014511899,4087542186406,2848566880451,1097571275869,
    4058985920334,3153215900529,833791319901,4047378004226,3272165680501,793153370345,
    4081500512920,3211241215709,974470005483,4148841133376,2966082655771,1351012431799,
    4211200720382,2533352243569,1881010046509,4224257758090,1908608260897,2528900207131,
    4138942811664,1059933533631,3270002459257,3859798065284,92460817964,4027902794731,
    3179777904340,1613043044162,4542233734177,1803092612552,3347435472076,4293194013563,
    408211938465,4686054925382,2714918999451,3002355891125,4631607555442,188800339904,
    4721017774389,2511574228522,3220177334686,4146437548081,922331263987,4355381776384,
    1261886031881,3351672652751,2656228780386,1699681259206,2979106405679,40247388369,
    2319801488898,1119876715931,1005334662341,1508231205354,559106471245,1086072454473,
    2017793505494,15524324141,3134015367867,1579614760578,3805469179650,3377596254979,
    4043524138111,5220093929218,3936196951408,6981478254051,3612391404281,8602611736804,
    3217658008564,10078629608543,2903014268809,11436059527526,2823270402598,12702387288463,
    3138486628467,13871914490232,4010732972060,14871630929061,5589328382863,15530078761844,
    7978780568904,15553548225401,11181559650997,14521607276056,15007586033740,11930841361483,
    18959065826821,7330941009886,22144973290048,577220440241,23330650834565,7862009781777,
    21212113885906,16705011767930,14871640949345,23902758929905,4251063422066,26890197314238,
    9402721565874,22989010878055,22903899421031,10448913180742,30615377559836,9111940915090,
    25911006866225,28054132016067,6353729686804,34243387475660,20520097953988,19134179502561,
    37902150353925,13006133414295,28734964652456,41345955613016,9547855352420,35510732135399,
    48277213292439,13760805402325],
   [38247490096646,60607001857306,30696520928806,29980308676573,72936701612155,60539385897095,
    5358539907504,83871955735456,122191277512900,89733362287786,2212022467913,105444903513067,
    159262875131857,119528367404473,22353093869484,237816104275910,474754181018808,
    677982785052254,807140206625030,845935445792394,801589819315532,697295982703732,
    562189168276738,422750533501742,297758903443006,196994189613622,122639378979364,
    71914378597168,39730844209884,20672845361448,10120331381622,4653017253460,2003834403442,
    805088363330,299835270760,102340568156,31199961166,7974280214,1188490720]]
private def rkmC_w64_s6b_3 : List ℤ := pzigCat
  [
   [233613115,907042978,2414515125,4286413732,6825745581,10103327048,13868366693,18159748462,
    23148422895,28671995794,34743480767,41438369154,48343217977,55707162246,63117148897,
    70137887268,76706936717,82239262794,86008626425,87936089886,87073561677,83006901274,
    75572935011,64564240062,49982599937,32666766490,13313509433,6887660659,25802091052,
    41860118987,52921147452,56773736211,51631076196,36316380927,9797471678,27599567186,
    74878545693,130625807922,191819992031,255382787620,318354947987,377893325002,431825760065,
    480234995844,524360522225,567233870538,613927089065,669629057896,739108743707,825453243376,
    928595657943,1043846733128,1162858531173,1273104632904,1359552192281,1407402033524,
    1404166808393,1341652179750,1217647468595,1037294212540,810555529709,551720277842,
    277377627339,3678512456,253910098684,479990376185,659205200330,775485813679,811963962114,
    753280248579,590363497496,323906301679,31011385181,442625421348,863420998947,1235758322632,
    1498243111219,1594326371524,1483341829097,1148635369952,605623112927,92243789997,
    850437197582,1539665089657,2012932436144,2134316134659,1819115218638,1074148189865,
    21313492052,1109547794792,2027477832227,2459198179840,2242642547843,1398745425064,
    148689477569,1140134827155,2068395863544,2341683878519,1879709319816,851545891551,
    382703130727,1402012347828,1878669063517,1692455553844,963495580263,6557414157,857878462374,
    1307527209237,1245297180526,758136632251,78724014906,515261817970,813300478471,750039993570,
    419422572509,17928586920,259218027324,319471914531,213763127512,90300114215,81114771526,
    193797485289,291361716936,190211049035,175786628987,646801363998,890463615091,619693464458,
    157570735748,1048791527357,1465377345880,1010016407299,187921314813,1454269473936,
    1947697880191,1226884322768,377977854624,1890255257875,2284709905980,1193488646555],
   [771195322971,2345944553310,2431449444249,868371259252,1373950123132,2782118216399,
    2318178347824,194665511101,2172466907691,3085645875448,1786045799053,899161492765,
    3036603508506,2965161612429,608097100272,2325321375410,3546258535699,1984802306958,
    1237344574696,3561996933429,3023107347534,52529552016,3169760671733,3670886632136,
    1030458175071,2561987318655,3983570763658,1908921353007,1907387256067,4066692602330,
    2555276730417,1329084909303,4031363326186,2984072318725,903871684653,3966811583288,
    3223363303775,670734390711,3927576604162,3296405415701,640026889249,3933603972648,
    3217843070893,800855595643,3978925822362,2996410595285,1130873560489,4045767006678,
    2633393606867,1613434196773,4112109640516,2107772704351,2249643209435,4131990394228,
    1350183240093,3037538365995,3982906809884,245131467781,3891403917625,3422459046298,
    1276351107570,4524634218121,2147861425802,3042104045162,4419843087791,41374097182,
    4461513269914,3056995117187,2469591536579,4630269872502,439836740065,4275884208453,
    2945286078836,2422066928334,4144266633861,21235081003,3830416600528,1955891638731,
    2408780120767,2892176882632,598654497822,2656193116585,891377742228,1523569440796,
    1588024169077,14572700226,1332139230062,1451545012169,236665160989,2405807720880,
    1419558382365,2681565775957,3308228726218,2260360736326,5141881466443,1251220610027,
    6723777166388,171228932185,7961639552615,1820461908832,8857281216132,3533563967753,
    9484159747493,5185694752790,9962311690056,6686257038805,10435689687053,7962982575140,
    11052231983330,8940413980953,11944714093957,9518053583864,13210041073992,9552442891571,
    14883796630293,8847628344808,16905316361990,7161451390519,19070474259627,4242571568410,
    20979367436990,82951644380,22009166500247,5767740614121,21361892662930,12377307085350,
    18231079420171,18980655541223,12065756077608,24173173265974,2852774070823,26216109061375,
    8617875282925,23250050234538,20389068862630,13773143137471,28872315015259,2083626400505,
    29079378945958,20510013552454],
   [17031355602549,33172118226093,5736658962741,30557941137392,29346192593588,9045845000743,
    38554464959853,23133888995227,21088638706916,44574332499280,19654844077184,29520923380685,
    52303268066465,23118438040947,33053071411498,64051235521266,38417563569610,26104551414177,
    76657736745857,67943391264485,1722980615114,87697302131244,129559284203934,91951275573456,
    11423428444381,123972342057967,176216079548645,120745217928071,46444705419556,
    286647166850708,537237612462224,737035787669366,846395400917982,855354796031794,
    779850416594538,650696060805270,501309802680984,358658111743172,239163833759958,
    148974648898516,86776189993370,47273316371972,24067358171326,11431617820284,5052126318624,
    2069003710474,780484363136,268540855840,82904666980,22055540208,4339698888,226715770]]
private def rkmC_w64_s6b_4 : List ℤ := pzigCat
  [
   [432888899,1313033104,2863883781,5058521104,7582146181,10958748290,14858649345,19213923764,
    24213796377,29779293752,35748979037,42254610530,49139181259,56154272598,63351188647,
    70046874044,76178311981,81425609924,84973409657,86477232852,85655570105,81694017948,
    74592606947,64087106868,50315683531,33840752552,15498161697,3715626817,22013364840,
    37712072387,49070156726,53673002739,50160660560,37146121965,13521040240,20599788294,
    64500696567,117057140578,175662905079,237788669608,300656683615,361396455356,417713246825,
    469056446524,515656511397,559608302664,604730572185,655194735430,715781040077,790248692404,
    879868999295,982637990992,1093424590173,1202428593794,1297112094187,1363903956442,
    1389154590925,1362120739000,1277028685079,1133830098162,938174327759,701835877664,
    439656053581,168262588426,95310370730,335374212815,537619337996,688143652623,773040859944,
    779668488163,696912345860,518886219711,248904036786,97072273584,489155476717,883415485848,
    1225882679289,1460778139642,1537380457595,1419967049530,1096496144375,584683490656,
    64735251248,767646620699,1412507019608,1874652093089,2038011797184,1823321345531,
    1219740616470,307131847527,741832349233,1688198147794,2280473794469,2329300091528,
    1777300525957,737514481870,519302794170,1634336188403,2270346049618,2228295994235,
    1522664621200,384941636079,811227117425,1678697790728,1952211990311,1579687575504,
    732871233789,265801646497,1066813829692,1420293485917,1255942866980,692195408979,24847537913,
    623284730406,907398997371,823054751860,463515859863,16783736860,322668988710,441802371501,
    352671210446,171668303593,40054803294,29614712135,93142680076,98751127711,62885631045,
    366826228420,627002007859,596448158476,153011389745,554999338113,1129712511022,1142530079933,
    437405204858,686342338962,1579155214725,1618405452122,642062270355,861327818699],
   [1984243249662,1954567952861,673114571074,1141726433612,2349863049853,2113658097590,
    485669784657,1551051485395,2669183693682,2066012275939,47543978756,2096837747488,
    2905045026795,1741794051596,691032408096,2744327205697,2925556631606,996221172063,
    1747340440253,3311393866796,2453579027147,303146581075,2932958188036,3379080528289,
    1185042938930,2021596392384,3703631018995,2431611990600,863578423604,3525222688091,
    3306494035080,300213276775,3018500486695,3808359591902,1316020307881,2364141852153,
    4013545744486,2114144255629,1708454326029,4027397003604,2685484097765,1151219687485,
    3948787717168,3051966102165,749091142429,3852490541300,3245411095475,525287887011,
    3784021980074,3295844522233,479382896869,3763797593380,3227071197529,599942671911,
    3798191411340,3054180890553,878392494471,3887916089668,2773879513745,1323160988355,
    4021162232930,2343207294077,1959884577489,4143403268482,1663375875827,2793228109913,
    4108449241496,603791451437,3722658946621,3657768216862,895876276684,4451363652769,
    2501871599908,2655158690532,4489650324563,544119886196,4126739228132,3372890280343,
    1831521196105,4514595848492,1095586133367,3677485199453,3284245164342,1520579430520,
    3943720324863,848143164840,3084828434564,2446375207597,1337817502063,2790403242486,
    437211623473,1969207480423,1524717348486,481260807764,1571447707353,1029060826204,
    617630399148,2009376958833,1009188805468,2139185242120,2857696042283,1358585581209,
    4502447073998,184807298465,5639975107055,2226784760816,6124013541404,4477915188569,
    5952502772357,6692101481000,5227575529970,8703757106997,4109362551201,10436695260208,
    2777653348746,11893217436063,1407307249669,13131943236052,157609478474,14241073935779,
    827365271180,15311792796570,1412144842361,16413521139507,1461506008058,17570613619446,
    835515650981,18737302176481,607293272571,19770982979214,2988262284668,20406163317617,
    6361223176309,20246284229956,10634481747020,18794581907593,15481841644049,15546085836028,
    20278671739946,10132242709583],
   [24099573877125,2482387719100,25772758556606,7014570673742,23963775004945,17277158829587,
    17362733031058,26158972794574,5290476158901,30201059954753,10990400915909,25400658806620,
    26841530204786,9780761590511,34569205721047,13244358251451,27015990063250,33763029761748,
    3006411785803,38451611826321,28387038471287,17422993829972,46636304310996,24208621506144,
    28270297546613,55400025456245,25997338265683,34501767912160,68085716883996,39126309349764,
    31807909978985,84396162271695,68974298387673,11990324663958,103554483863392,137331489199734,
    79899330174792,42784214329161,158862789219941,190494751597813,94648209557419,117314819668094,
    388134931159366,642395450781658,817126237959428,881401544249698,839546802824268,
    721130082704112,565422053867792,407717273045030,271609469452086,167583679665604,
    95863729388552,50824786777934,24935038484120,11286991307244,4692399292006,1779389944144,
    609118310328,185108744292,48191606406,9784352194,967358008]]
private def rkmC_w64_s6b_5 : List ℤ := pzigCat
  [
   [750008467,1998320384,3646063367,5968092264,8910110809,12304104540,16315490865,20892067214,
    25871249685,31559070624,37549931253,43918965012,50677291461,57507084506,64300927741,
    70801276290,76396591977,81131555840,84231124397,85208207982,83941833587,79818695954,
    72434644375,62097316654,48651603469,32734599404,15078667319,3245894909,20732560916,
    35574196579,46299852790,50897078581,47510172430,35249380059,12931863968,19541159428,
    61486110981,111855730180,168693368165,229401039648,291623859953,352483722152,409996253713,
    463067027850,511595853675,556777231594,601746450627,649958857808,705515145881,772384048782,
    852170036415,944668027190,1046466107921,1150121288602,1245344585843,1320075015230,
    1361109766567,1357086440912,1299920156281,1186243799348,1018397592697,804880466900,
    557998059683,293699811956,29316515791,218797525671,435382875644,606600830335,720430076572,
    766230101655,733955123248,617134497051,414293619706,131987375313,211737077461,586204522014,
    949640410899,1252431350870,1443176759689,1478285286894,1329175122121,990043901606,
    483320141731,138398411123,795259890874,1386666546497,1803520846832,1947764079633,
    1754146604528,1213283721471,389076667476,577112759450,1485252123659,2115680942782,
    2285641263353,1910378267554,1044352220561,113427602497,1260875348630,2074109391141,
    2309019027344,1886956633841,930707417532,265875827242,1329463357035,1932304262622,
    1904291099103,1288806065752,321393596543,657903640495,1328154686696,1497948393167,
    1163375444968,492804278063,248591438267,801161507316,1002419617733,834005689556,413062572381,
    67238339737,420588252738,540832215061,437044686168,214737498955,11882558316,78888884944,
    60872030971,22550748400,68515353913,229104080280,413129138983,447837000594,198431293489,
    302612344351,815554570518,999424803467,626669629538,219840646684,1119450284607,1515757329888],
   [1061263304507,107439893477,1370135335268,1949318512075,1395866350712,71046919698,
    1622760306795,2289306279058,1575070828107,173039446841,1915455470802,2538532765869,
    1573591389230,448047374840,2271772434111,2693900881884,1361699708209,930760523125,
    2694561711736,2705849416911,864373712148,1652026238042,3114430609737,2428983314888,
    25727332166,2558373964737,3311086916276,1635011511429,1327042418757,3383340681600,
    2913957906421,175651483514,2777150464862,3617067095415,1597782767334,1750714925594,
    3749928825089,2721021787550,571025696360,3442177525563,3467563563016,556520347051,
    2869076739357,3864554604674,1510665007325,2195067791211,3995252791144,2243298498627,
    1545826664441,3958628345698,2756455082013,1002645616909,3843264219012,3078507181903,
    606464105675,3715256019524,3246681463835,370102482335,3617864895226,3297264889445,
    290460081639,3578538341798,3260257894443,362310985269,3615821486382,3150353509565,
    593161255071,3741015412608,2952972910467,1011188474343,3943153650378,2605840741421,
    1652928572647,4154891064220,1993928464147,2518790335923,4215377836914,987371708695,
    3496568590101,3869289187232,459889355226,4296300079787,2853543366932,2170768109372,
    4474356209979,1089157917980,3659308242438,3626203058909,1095515739909,4245351537346,
    1733692657679,2915734054243,3464537454742,556233420086,3499890615409,1599802311324,
    2133402157500,2639499806187,232187838743,2307034900532,1256021038311,976345039621,
    1707851115230,625736083693,1000252717371,1762987300012,545640372293,1948827911435,
    2362647458386,1052175005924,3864160652401,738406874442,4615320027020,3036293441917,
    4412726809945,5400075446904,3278134024708,7450035069651,1396326014387,8935153820378,
    967028171623,9751153207059,3539970535594,9923067285524,6096325239423,9569227864923,
    8480965950204,8861753271862,10612056026935,7993136342071,12467256860598,7153755450652,
    14062372314377,6519009506779,15426414788270,6245323247850,16577926101257,6468867501003,
    17500860591854,7304512309590],
   [18123288110601,8835817040271,18298885239988,11092048252406,17799527129011,14009454038243,
    16329098380106,17384510932646,13568110792707,20834406796427,9244901847626,23782774121626,
    3222143728183,25463039520281,4410710922683,24924818903386,13191093126862,21065329199237,
    22007690015223,12854685911010,28735582043018,31272702755,30190648346519,15700003976223,
    23122482293028,29738130474424,6501483584569,35319268188759,16048689302317,26519918246510,
    35646430600376,2338162768849,40190378408505,29384344691991,19634685805934,49411381399212,
    22801219901348,33756947389729,58531899911255,21077082298925,44495970746310,72501814747876,
    30111117953004,49483848189937,94871602358705,58541465101357,40927714401240,130529696631202,
    137159073538754,42201801715804,102211577907295,203507326941321,182395076729945,
    15534506463213,255391799432666,547837981806716,777676312644430,891788625683772,
    880814691898598,771800594349894,609623640229712,438083404747918,287917366378668,
    173502770679542,95913576095036,48572225842790,22459566435582,9430007829162,3564417190668,
    1197112018158,349580821174,85183129990,15610920926,1340862522]]
private def rkmC_w64_s6b_6 : List ℤ := pzigCat
  [
   [426906080,1275502879,2763574360,4893920981,7380167880,10592677447,14195005364,18319591495,
    23116572842,28312467513,33925977540,40047567323,46300073702,52992550193,59628176766,
    65943025125,72011461004,77265478745,81149385654,83640493031,83928390422,81851842283,
    77110408404,69372593489,58612615946,45251765561,29561949266,12404013065,4980228847,
    21479039456,35189431425,44667805686,48199791031,43973503274,31055992265,8788131502,
    23460378488,64785572391,114163135794,169892191867,229590403700,290956993407,351660123814,
    409366824933,463197104128,512790551095,559037500574,604233152101,651661380472,704565001539,
    766630385530,840038551575,924774627124,1018664325531,1115811143382,1207706881637,
    1283681934668,1331601968853,1340055213476,1300346853083,1207138381918,1060614443877,
    866324050936,634562905463,379576438938,118350216903,132654742231,357322462108,541209178455,
    672695496450,741602599283,739728935958,661429703685,504249701692,271039215691,26833277223,
    368478073800,722356555673,1047352708702,1297247620719,1427656089722,1401970595111,
    1200490563960,826464275139,309284977062,295041061012,907266560157,1433976081344,
    1780050954687,1863790738664,1636889074207,1101131521350,320092048923,579697655205,
    1423001758712,2018996884721,2206401733824,1901497381859,1136575616186,69614819979,
    1042509902321,1906811658992,2277075607003,2034886490584,1237087840701,109214978810,
    1016556249066,1804145142251,2023626657680,1628708594019,769965121558,257654345342,
    1118461618515,1551699058148,1455973996631,913101635638,145533779281,570547612739,
    1006028317850,1053860888017,752698419204,255838954187,236456436793,554662818004,619431250305,
    461015388724,192242634961,51308395547,177608285546,177696902335,120081084232,97878991327,
    158954503212,261062141091,288265576540,130510500029,218985004085,613617874004,805182671455,
    588470967134],
   [38205674196,807100698023,1283722170760,1110437393207,257952396466,883979600884,1673987210739,
    1581751796370,543761990655,926830874699,1985324592780,1946248011081,733664748098,
    1007434931746,2248070431145,2188698029252,782932279525,1175939005649,2495154304918,
    2311712828643,664656081396,1470745890488,2749235371389,2302324163104,337750544827,
    1924727786735,2994384606960,2092844995183,265005428029,2530656183932,3124601817879,
    1546496468092,1186997841236,3165257203219,2915401523598,521031481971,2333761899263,
    3528477845160,2093547380641,973338604635,3366589780572,3203259395777,531130177018,
    2611527809146,3732615070685,1877988760216,1524054561356,3731309308147,2898868931876,
    347986169652,3341485413165,3549148838290,740008026915,2730772895881,3869570975540,
    1641073120759,2048016142443,3944010601110,2322101248493,1401866974253,3865176714524,
    2793646080759,858842816709,3714524755016,3089181433269,450384633407,3555574467298,
    3251438255819,185017542193,3434168338528,3321116081143,62025507485,3385054752470,
    3328837866043,86122778721,3435399944910,3284216053939,277885463569,3599577253244,
    3160660650305,675870503091,3861105491918,2883433730053,1317284243189,4142216844420,
    2334893129903,2193529206363,4279451663498,1396721766329,3187746400527,4035542182010,
    37157779825,4031899836221,3180831453402,1580862652550,4339819151687,1650397079302,
    3043047151184,3768431459147,287122497083,3785237798328,2289061997275,2001398790403,
    3415948833264,398052354957,2789058589223,2125475048746,1036927286610,2452027955981,
    765148328530,1452163235894,1685837762651,177886574444,1331795794722,1536312745903,
    77055209832,1924160962348,1898299421329,1082215990725,3375349167740,788548110767,
    3915897793899,3170360439136,3249585739680,5440096171043,1446399531167,7059608550780,
    1168806446867,7692866239933,4148590915512,7238957996284,7050884743445,5798408570315,
    9530305052032,3603268665882,11382372199219,939940460569,12545613420376,1913742993945,
    13077033605861],
   [4729451078066,13114294563504,7344770328429,12838798222905,9662203022738,12444194944684,
    11634233875921,12115850623723,13242744122544,12018424976766,14475637626121,12289031972711,
    15304250555552,13030575333932,15663587202277,14301575008643,15440743739278,16097532361162,
    14472970668739,18329617304477,12563628953032,20801526605864,9510233840505,23193276957935,
    5141383187768,25044943930748,640255436458,25727436716097,7779215996363,24397480691024,
    15892898367428,20014425224293,23956039317115,11602281616630,29966972473090,1049340732786,
    30997652907173,16356686502687,24130540629294,30268319230410,8288773283391,36844746031015,
    13898333169351,30311168545574,35202381353882,8079817324387,44222165801043,25018376946081,
    28814686424314,51962192557588,13143227339490,46534244171545,58860269392501,4700970037517,
    62834703070192,71815075837312,5180652675984,78987129990043,99207880422583,25153935848531,
    91840501471380,157343170366024,108047922270090,37208663491989,185874177447909,
    229585818099337,109194426391981,154025159782854,474396681442960,748319122236740,
    900979798041264,910197146501548,802114326857700,628807177816544,443165612088152,
    282312551708460,162864870855026,85001249350146,39982363761314,16829425696878,6266044176806,
    2025342479070,550170368150,117574674266,16324416408]]
private def rkmC_w64_s6b_7 : List ℤ := pzigCat
  [
   [639830241,1737821406,3325484097,5582973600,8297287349,11489737820,15354774521,19499376800,
    24277244301,29524704120,35118987953,41195859750,47494954513,53811767962,60325017689,
    66449572430,72169820853,77088620308,80662310191,82752281618,82929910645,80557351848,
    75720015965,67970938612,57500657793,44538445910,29284960501,12738714148,3929566222,
    19866413015,33111575784,42276391351,45864777412,42129977681,30033745288,8971302385,
    21684251511,61239962270,108799799597,162824396370,221317573739,281888459112,342401829089,
    400667350892,455536167097,506543269522,553809120085,599439141254,645912711187,696200320022,
    753694541031,820721459292,898008480191,984553345984,1075884464125,1165254130850,
    1243475831925,1299461034614,1322226208603,1302390564768,1232894958329,1111483962058,
    940850705253,728639347158,486892673929,231065580980,22557872660,257109572281,457455353466,
    611039033279,707168085286,738038168063,698168523166,584542235817,398285741564,146209611117,
    158138659379,491760720444,822554277497,1111570351230,1316536199815,1397441417218,
    1325084758535,1086269276704,690040764103,170648000076,414325346388,988143659641,
    1463368382142,1754679835309,1793640433600,1543140412519,1012152433260,264201401581,
    584164651397,1376475571504,1942526087205,2137700075972,1882630869421,1195954970166,
    206657712083,863416435561,1749294301794,2212015494971,2111006955100,1456561564587,
    418277686888,715550024384,1620434343593,2035501188964,1849099795327,1135944094620,
    133234389487,837772306153,1479694684574,1616701327991,1247156790852,532814172887,
    265485948477,883830176308,1145069835747,1009924744700,575282564883,26355012202,437579056170,
    676062278731,649130292906,418441399795,109438958146,146317865730,267559316669,253372082198,
    170365658633,105693525442,108743171751,156115009900,163147322549,43530157230,214897606576,
    508438091155],
   [650328270126,476744605429,27749383597,668156853548,1101222138147,1016298486894,342094555865,
    649446573213,1438057422344,1527936775957,758697735622,538457280266,1668667443981,
    1947164141938,1120527252639,426839002501,1838346452458,2262100739731,1373223352496,
    382035873138,1999032285013,2490574506758,1497254473305,449256420477,2197847593844,
    2656335822279,1479095356252,669228462302,2471909105607,2760880207922,1280085091875,
    1088124725911,2826004696930,2747665119713,820241584066,1732914553064,3186283818549,
    2479541068330,11435226553,2544796813771,3360754412974,1774193867943,1150225053331,
    3306183143036,3062077361277,519368596034,2470654274806,3639246503255,2035275961656,
    1171684649132,3515373759807,3128451889954,255793202295,2857710480691,3705952994416,
    1554018220753,1892434664925,3810643891600,2575697339133,830381960841,3561337640576,
    3275816021525,172757964300,3098265097666,3680369907625,1025805611196,2547299124568,
    3853049378733,1692588381032,2003720372532,3869850045765,2176438763768,1529002926476,
    3802336543937,2503385893028,1157875986922,3711900869637,2707476893438,910031297574,
    3648435016997,2819299071242,801541931020,3650330717193,2852439263290,855184620362,
    3739436530939,2792306909646,1101715637472,3908334483609,2587074174004,1567799553904,
    4101130160123,2152366374524,2246007940978,4197781414381,1399366219056,3053780855532,
    4020557431617,292322838804,3800829016474,3384284067333,1076309717865,4200277372334,
    2196464387551,2433125426629,3959667251876,581272481877,3359566987983,2957026245554,
    1057170388646,3473194296717,1425684353252,2155505858458,2724145992633,34928353037,
    2352685180106,1594346938863,807530379697,1904298677254,860172841551,877755050821,
    1660861938404,809629427293,1131075255507,2203848288738,529994621139,2528040992273,
    2631316640780,1475466151632,4323688944861,736526280650,4924394198650,3512074705681,
    4116477533617,6117181565416,1986907627200,7909581856319,1064916507086,8488389045002,
    4484101426997],
   [7742346248461,7719144881296,5812167747260,10338045002407,3004517628955,12086821383074,
    307243330517,12893271418921,3766036815074,12835393232128,7086899963501,12091266380521,
    10081071217838,10889001606044,12655531673951,9466134981613,14795914267734,8043400605798,
    16541579587665,6811755754925,17957654337978,5931138254660,19110121888231,5532571616729,
    20041313619680,5723266561044,20751714999363,6586027550403,21185634348276,8173967647208,
    21224435393203,10499218913943,20684593199100,13519836417660,19318891656225,17118813089303,
    16811654792400,21063371926092,12776774818349,24917252384147,6797982182592,27898531492192,
    1404780713840,28750939662077,11604528131563,25816252288752,22548482867530,17547651102561,
    31603214703725,3505824414932,35039470314996,14551320969872,29168635623381,32101184197185,
    12046626674148,42076209041762,14457516710748,36078154518681,41879801892665,8457969082050,
    53456774403426,34579169393950,30689365689195,66798089314383,27029226272307,50962246648046,
    82728555901624,26512691208096,69602636142303,110628559432193,45115724463335,82678864777328,
    165801313772886,122706063497564,33749295994365,199577675527049,248395624391711,
    112219452486361,180122553418760,524930547309136,802923254060592,935581672138498,
    909659943194070,766075234711380,569080828553154,376266021698474,222176187788172,
    117051878103856,54744277352326,22502288220020,7989929363228,2377949207690,559213950078,
    88958448572]]
private def rkmC_w64_s6b_8 : List ℤ := pzigCat
  [
   [249878721,926409760,2375067045,4145309160,6542194479,9485902488,12811656903,16736138706,
    21151934635,25870573300,31240034229,36830969968,42800321695,49079755078,55312602227,
    61500766494,67457643753,72670152006,77233141689,80451243204,82019916275,81704505664,
    78986631749,73736551678,65959191901,55310260444,42426134429,27615894788,11587914251,
    4499635907,19596787642,32243902171,40592296552,43581452325,39575072004,27462131975,
    6602256626,23413180088,62151036215,108582460816,161665328535,219082860582,278902439233,
    339102951114,397464966299,452760606150,504517862471,552572306048,598661870983,644823635390,
    693619331397,748131655122,810784115745,882559607442,962934864021,1048571087528,1134005095803,
    1211205589562,1270300314953,1300786136548,1293380230797,1240246174984,1137588400689,
    986217384730,791215545281,562924723248,314957916671,63042920652,176041049014,386704359673,
    555543014840,670997874799,725045585392,712256509935,629733785942,478008869699,261824196106,
    8966039244,317022766759,637492072626,938308728433,1182106832302,1330416086071,1350183859908,
    1218877341083,931913011026,506161463207,19146252877,583401046008,1111111970427,1521465242246,
    1739485308003,1709401151272,1408634743503,857118517938,122774933831,681252505129,
    1410870532512,1915466723261,2068923258406,1805631636863,1146266521036,207404599473,
    812339416357,1672815710944,2152467354283,2111546672518,1540022821953,573803705538,
    534007362426,1480696617831,2001648215008,1952787968477,1359545821006,410454696733,
    600880986967,1369741393692,1678221603013,1463849746022,832023198331,13109562210,720804751578,
    1149454929715,1172690174424,832186709539,282813072722,270683698210,649760254537,759603523396,
    610694663983,300745144022,32435609742,268691879961,350724618956,296404153213,178700715220,
    80886153139,48379792206,62312143521,54633970218],
   [41175786796,231913624153,435746300526,510773419163,335751218610,93217531284,616226373437,
    958400250424,869619708157,289084537966,567615520434,1272656715457,1398254740976,773859838333,
    363139516481,1439262420910,1833717333453,1240980082058,105368663818,1505398957437,
    2156724843562,1621100695223,120849132232,1536124667690,2389954226701,1891888056302,
    261996783787,1591389216693,2574098954680,2056603542661,283417078692,1724023833270,
    2748334254465,2115975257362,148344193075,1979067925901,2927352354864,2038911855087,
    194911459309,2377989326678,3070359258987,1744668646120,796847679428,2880262915805,
    3056075343186,1122711423371,1652059880733,3339986790200,2696574990003,101052510840,
    2629278866622,3500250839885,1812218598652,1253310481294,3435961478207,3063737098912,
    357777075177,2660179788763,3665013106378,1832619933043,1456343043595,3630120380510,
    2937259020853,117084650351,3103391152164,3586850806237,1130067539182,2278908051596,
    3810323916629,2149803762144,1339337647370,3701738708157,2891784400946,424070651904,
    3377179544289,3368537589802,381091362389,2945086150621,3628840118620,1037521488723,
    2491775834483,3736547523238,1540621515001,2079581120679,3757244868940,1905722794157,
    1751819338515,3749610565876,2152740043415,1541223138091,3760795458004,2293870438377,
    1477578338869,3820245312242,2321299046085,1589252680011,3930412156990,2201474289625,
    1896394198397,4054397685786,1877394297793,2391791325495,4106929000568,1287378607807,
    3015056426079,3959306146422,402745942563,3630226161329,3470176641898,721793952030,
    4028174640525,2549573809156,1907130261954,3977514219329,1244101961974,2855421568430,
    3334328701993,199918538215,3246964431236,2179806258011,1372885004791,2933651936542,
    888302368843,1904689329209,2136253432286,17592160042,1786970681441,1431273754884,
    276268783020,1558989771417,1327807338330,320146772736,1974877146439,1569319586632,
    1163194631474,3064830281449,876369753990,3305003460534,3351635949243,1959945768905],
   [5283823739124,692257631057,5889979947621,3927927008784,4825519794274,6863968361191,
    2235494552755,8738928690490,1356955241269,9098189798149,5245787445960,7853356532462,
    8742553792897,5231760412649,11322875065986,1663169121976,12698536337699,2350933645470,
    12818024174092,6347339475235,11818710172525,9972416023446,9956695611456,13011595456079,
    7537388352149,15385982799080,4859607155984,17126288577681,2182108409001,18339855862412,
    292411099255,19174793124687,2415244058910,19790618520168,4080942000705,20334339803413,
    5211458871804,20923600035760,5741807112401,21633559244185,5607293663114,22489556113382,
    4736158428187,23460514746247,3043479939710,24450389904168,426680241097,25278255335103,
    3231152779157,25636707694550,8029057456190,25030879766839,13949480783397,22734062800518,
    20664551539884,17849564885491,27275176058985,9587139324012,32126985381402,2210486695370,
    32931063945381,16452140175961,27343276352282,30409823682466,13893570059839,39759198932195,
    6929652565951,39028603144092,31264728437286,22920614802459,50020849581327,9739907990039,
    48937310428914,48916237798134,16002897438817,69432806168999,42623111918875,41598697757144,
    89649811699692,39837790195952,66151938849405,119948488029407,54172120758465,86251687319502,
    177763989249150,125232844881998,52652787176233,229883533912273,261468533480467,
    81738245134821,257066561415716,623039062741690,882763754870120,965282992334164,
    879691476236348,689860924634328,472410355802304,284035853151228,149778372331540,
    68762953843982,27066881095006,8879088676638,2294447973366,403839400546]]
private def rkmC_w64_s6b_9 : List ℤ := pzigCat
  [
   [512667096,1482695027,3101409828,5312906171,7791729632,10992236537,14522695042,18527277649,
    23116111976,28008037745,33310832394,39086866445,44903972912,51099190459,57229851738,
    63131163031,68764683666,73645464663,77526252160,80304234761,81218600638,80297028065,
    77060532226,71226287479,62963858688,52218954699,39185322614,24674385139,9032113736,
    6434381948,20539173735,32103554764,39486216451,41278190346,36355889667,23298795092,
    1850487637,28323604641,67044047612,113267190189,165710655058,222647872977,281770451042,
    341494733267,399721937276,455029342537,506967275366,555568968903,601857805230,647931225863,
    695881139246,748648735323,808314699828,875955460435,951436490674,1032141614805,1113045680916,
    1187499320131,1246223396942,1279724216199,1278917604298,1235788439363,1145670484360,
    1008224504483,826954435732,610459325659,370845478936,122997031895,116798146711,332770026410,
    510896833357,639129493908,708942844203,714670722798,653502841381,525826765074,335897365399,
    91633501912,192880071172,497642260877,796222361028,1056038453515,1242453612954,1322342795773,
    1269264474412,1070081234011,729505115506,272438954833,254887041701,789485633532,
    1258137676917,1586700656392,1711817743937,1593225222718,1223549114393,636390056104,
    92303318638,850399852543,1503750260098,1918769976881,1992089541398,1676966818493,
    1005230426974,93314920735,873439540493,1676684537332,2116475683653,2067044744266,
    1519149324609,593631575694,479696403836,1419751996801,1972890981356,1987986203083,
    1465431603390,562650054031,452685733863,1283570196428,1695912279267,1590931160836,
    1033090485475,222472881868,575705161272,1119563287373,1268137576828,1018754462455,
    494781778456,106668552880,587065081425,813303924366,753398241995,474095921430,104742738569,
    216251544229,393772555048,403664879273,290383755048,136920353565,20602842744,25291907732],
   [24142732645,34669230192,108017829933,242890909394,368808895759,375274365000,181180297569,
    194863764175,608670470600,837376340417,693491415262,151171708553,591256197867,1171768969092,
    1238991511383,660432515980,356484010230,1321000480637,1694018578434,1192890391825,8639396989,
    1318325547866,2016148443781,1655592500644,350759445937,1234580322723,2222521552142,
    2012509475869,652715456840,1141392723708,2359284225053,2268260883558,860703024293,
    1098784817885,2481475414578,2445015279725,952904170122,1158761972682,2637673636155,
    2556174648364,899847817663,1368437288481,2852615303846,2580255290659,650620007430,
    1760838342826,3102012203813,2444441626190,142844363183,2323321200655,3288202648910,
    2033721546113,655944810161,2957504567490,3240300820095,1238164916080,1688716715334,
    3459691877191,2757908590726,31872026697,2760384230257,3548607333508,1699735495361,
    1449805420881,3537745618908,2949590207007,89295192434,2866864289658,3613436794209,
    1527160076048,1784077626520,3696580917335,2652038590824,545836587134,3316989157089,
    3377121633724,642451778099,2638596917617,3714660395222,1652282892957,1820808554895,
    3736670012788,2428360933089,989233806029,3539202973414,2971489184591,227075928075,
    3218200860386,3318049005759,422122927192,2855878344186,3521527227785,943109836274,
    2517895948518,3638916931563,1335964481526,2255507815344,3720221455813,1602970687838,
    2109392188688,3800844224129,1737651991982,2111414586332,3892584833307,1718394355182,
    2280020351876,3975997307757,1509099495330,2610466338900,3994773525377,1071101385754,
    3058470121232,3860276294965,386786239100,3526717525526,3470814345603,507842746073,
    3865038358274,2752438375755,1493371422029,3899009717776,1715808832341,2362362037629,
    3496410876016,506847778061,2868126930747,2662565395990,593088423422,2843703296493,
    1614051274916,1270206034586,2356066908657,740599467852,1394490819066,1779993439471,
    374560986706,1238268418006,1625531930839,423498392454,1448309400628],
   [2057646654523,164815191408,2535686646726,2384825906363,1347551176039,4026506375126,
    1183706451729,4134861109283,4099780102468,2389650197270,6250022655433,809455239920,
    6747757301332,4548335695227,5257286654857,7753166424840,2043721447796,9537715755707,
    2178754535126,9425722356566,6501796215517,7411885726315,10078760224382,3882447464190,
    12307206768745,544114307384,12908643085044,5192585776439,11913927733265,9473484403660,
    9586865953484,12970506412145,6320451936949,15467886167936,2540545811796,16935159926953,
    1369126839116,17483167857000,5109649143239,17312231766807,8481867732576,16663403114118,
    11378906485049,15781709148207,13767006768664,14890673317708,15659165239395,14180209246103,
    17090350983790,13802596565654,18095638567635,13874808531697,18692184727904,14484721095832,
    18863119387945,15697530550303,18538515994362,17556513893010,17570488233057,20064715471847,
    15703731123894,23132836134198,12562402979343,26480441127381,7691837721806,29507712556080,
    706487881733,31199271387419,8438439109721,30168390788718,19109858105630,24927157965917,
    29737990031163,14359503887740,37761117033596,1709968146078,39747467474789,21814204655939,
    31729531274376,41699863451812,10457518578147,52970147048871,23027104516597,43908896957572,
    57912867491350,6326422979965,71629786020253,51841203312123,39068123267930,96440601969468,
    44151460108830,73086275551423,129530558065619,49529897768169,107126846994704,193130741534042,
    108840170586506,101393108054105,275498176417493,254687361465667,2922588224134,
    399140673681192,766191471075212,967837668643432,961733523079302,796149835994994,
    562103444075070,341244316729354,177783443392076,78548629411096,28676474837244,8194129686636,
    1590847968508]]
private def rkmC_w64_s6b_10 : List ℤ := pzigCat
  [
   [264412744,963579405,2429620436,4184786197,6568628056,9504450215,12804634060,16629418413,
    20849235174,25368488345,30566195094,35959546503,41630053556,47557829407,53534973172,
    59475162311,65150579382,70275948875,74777396536,78010329681,80014785658,80314883455,
    78456828466,74580871441,68072457638,59177225203,48072914432,34897643765,20422354708,
    5418939543,9402338627,22410735764,32627491657,38526874390,38643463295,32030353202,
    17632742427,5275971737,36451370278,75898994273,122466170444,174810222629,231466134532,
    290326798087,349404221606,407241880615,462208457826,514039222947,562748553274,609096411493,
    655007803800,702657565855,754204575234,811966524677,876690751504,948298988935,1024647240136,
    1101140022451,1171536931934,1227889255475,1260859269838,1261951994865,1223450168412,
    1140458297957,1011778575100,840074519915,632558421478,400548343919,157646087538,80232325422,
    297575041373,480141274366,615443652081,694455372674,711681835201,663942794110,552032064687,
    379831924286,154770517943,110970462473,400180999386,690333684975,953256373700,1158134183829,
    1273661919616,1272706664271,1137890260618,866272008915,472454187492,9150864416,526731744243,
    1015626147194,1405905496799,1632521854130,1646551185797,1423978630054,975489527699,
    349480162360,369818453806,1069843114273,1626390192250,1925348560511,1886706723946,
    1487916664537,778864813016,118356944228,1025497868845,1743072878454,2096603200809,
    1983657830464,1408640716839,493714894462,544058094884,1443828305787,1970003438744,
    1981161343081,1475383294066,594900118417,410249176909,1255932284578,1709020673409,
    1657390643098,1142471344663,343064138628,486042974266,1097460260959,1327706796090,
    1144474724321,646655866692,20575567573,527606068737,840205160274,854814007037,612086467268,
    229313075913,149084992151,404038863382,480428628415,395806561272,221405373071],
   [45471978792,67707039028,103452820473,95029223712,97008964925,146694793306,232068461285,
    288840895648,234052447601,22978703658,302988196232,607439719085,711049021468,488120722439,
    39485845489,672487232564,1100820189605,1052224168498,456794180031,469244172781,1288274551728,
    1547752659473,1030550663608,86021018618,1272069023155,1894531659762,1559422478659,
    361375588444,1117999298074,2089216927987,1981425575386,783004445007,907213107803,
    2175136039318,2289065628289,1128170330496,710508159490,2213224970987,2508225887488,
    1377282434189,583043976413,2265775045814,2675250411513,1520976222232,571806776866,
    2385596962771,2813142283240,1538435815981,722243130525,2603951080654,2910739799021,
    1384382637742,1072676762380,2910759996869,2907480755348,993988641847,1630414181155,
    3233479000508,2696119038285,312499505480,2339015282966,3430381534897,2154127974126,
    657560610416,3052777743393,3311934487958,1198818524077,1809437572259,3539002292852,
    2695199414635,147196382489,2908771381366,3518971565811,1481681106148,1697429344232,
    3603191778167,2747896008536,244793821302,3065585246941,3490605323064,1151275184595,
    2118776970775,3700133021390,2291952701843,989697248281,3467833359802,3085134667235,
    135179933376,2930400523682,3526831905609,1131576314362,2227580469816,3669924467245,
    1939017943872,1475401850820,3594859103367,2547430969322,756857298588,3387732961283,
    2980536285670,123140474698,3127796977381,3279056072054,397592173121,2881954929093,
    3486954918778,789887193443,2703560369287,3640330992674,1041190455019,2631889523503,
    3758349236330,1134369408197,2689676751077,3836333238152,1047196557497,2877631915191,
    3842784996482,757859812341,3165665127851,3721458534582,259580798241,3485763807207,
    3404976128444,420027540918,3732142568177,2840257580560,1198329477876,3777974198715,
    2025556736662,1930993915242,3515672032011,1047666333318,2435935263706,2919567365981,
    94961996770,2562871738800,2108063850325,589997344247,2301372766804],
   [1351602671049,841521797217,1871582215868,961638006153,752381690677,1689358779984,
    1040469179073,772145413931,2104433636554,1209370059177,1522698327731,2952342221880,
    603636303025,3228395213397,3248415357566,1556963364728,5030873058217,1569887016306,
    4902811531700,4951222513715,2608423349453,7225088516242,1247801821767,7417488452415,
    5485354922966,5268265075350,8804022744035,1255353564507,10211585857504,3630529002349,
    9280788932429,8229763598200,6189516126048,11541571146859,1583412210701,12939781779908,
    3654370905163,12247103546941,8640920849364,9682332055566,12671847150013,5733441027485,
    15316958518050,1004882538560,16432807928603,3916176096768,16116597689972,8553000502147,
    14628697331685,12584164892510,12311802580478,15849653148679,9521068186457,18327633226002,
    6576763957908,20098044036791,3738821193037,21303336018750,1199983780142,22113683249741,
    907368198340,22700922016164,2496255483455,23221162679567,3504664169596,23804954127810,
    3873051429833,24548017404815,3519212863780,25496801320976,2316148202153,26618547768341,
    81358975414,27752673896026,3401919506426,28547700351735,8312160888117,28412346810462,
    14654777403652,26527644900841,22084416514349,21960182601542,29746672322540,13882282689113,
    36196008108497,1848901623680,39384602160842,13871772039486,36661440881147,31728257627833,
    24957778442556,47811653172144,1932361494761,54724676644039,30903456856111,42476341355444,
    63767844591044,4067193692713,76892682371883,54507931661755,46711672302076,104499350867224,
    36418866737850,93632589773111,136930822229015,24184938212887,147930406622482,203102977996608,
    58356681402324,185897373481599,320670208336481,194661133324037,172606147643536,
    612764097099806,929092707519802,1013265129585160,882731464547536,637181333825346,
    385367902746982,194361003639968,79995760663520,25525969214638,5497341710012]]
private def rkmC_w64_s6b_11 : List ℤ := pzigCat
  [
   [712271265,1865791986,3452494803,5669397312,8315726421,11432738592,15145974627,19032794326,
    23491770383,28344018306,33452148713,38928713650,44670647405,50541681206,56433374189,
    61969148266,67341144107,72022958460,75800709897,78509848620,79496504057,78934505056,
    76289628491,71283130564,64079307897,54563047828,42840920785,29605362486,15200404273,
    685976830,13069810774,24863348373,33324490910,37273332033,35357957744,26374918749,9876199242,
    15007666982,47962399247,88549271952,136126163587,188885062896,245487739693,304035011874,
    362570720163,419750612518,474325045247,525536838046,573996544469,620255982764,666086677321,
    713523328686,764433208129,820780183596,883599524535,952126752756,1024599474197,1096665379140,
    1162433766637,1214561818378,1244402488281,1243656307602,1205484966395,1124682887726,
    1000017150301,833747827038,632291894965,406132314740,168350335499,66213447215,281790070678,
    464425601527,601767961194,684457426245,706708552584,665816150451,562454766706,400987569315,
    188500486596,63536691804,339615115895,619658456660,878829810639,1089441751654,1223169854813,
    1253470316220,1161763917111,940841008888,598491825833,160499822530,330281059744,817630884243,
    1236977021552,1525137646115,1629153790934,1516052596401,1181653495508,655195395501,517363411,
    692915913238,1311759104663,1745273855166,1900618155199,1725255439702,1224320572957,
    468173042100,411353111442,1241522463461,1842648179430,2068985835169,1848403132448,
    1209994204295,285746571224,712066785790,1540300410207,1988463149458,1937592150893,
    1398392928344,514534599333,474112105341,1298106964964,1735905832515,1680176584824,
    1168362022645,368994109570,472236108260,1109844176479,1374807383088,1221465773545,
    734073604994,91269817215,498680537903,866327100088,929770533745,712445047400,322045095027,
    95136860915,407014361416,537042010265,482587944398],
   [303216107029,88386192360,80605768598,162483280591,166375376232,136956596935,123868713334,
    149533616111,190741471552,189019566941,86693249140,127621764886,391635922461,578527477152,
    553093625879,251947824754,255404456434,765336203773,1016230873840,819463673653,182194350764,
    653194420926,1292550816527,1374596431102,773242631591,293015956133,1327208318722,
    1784685013811,1363858963784,199192128659,1161168839775,2010836458224,1856716490479,
    709487796492,879497967270,2079542840723,2217908040262,1163467899089,566089282679,
    2051850265344,2463293758319,1527835487424,286646813700,1996734674211,2634276963266,
    1797759454495,88897666391,1978810417806,2776236599333,1974704975114,13346429298,
    2051473025557,2919343077418,2046972601655,100460278337,2248781048462,3061654976281,
    1977539508932,388503851646,2571222492309,3156036067868,1705820214011,897353491617,
    2969157299048,3110775827917,1168447281104,1602303055450,3333435872127,2807816146288,
    333469272945,2409903591751,3502757357834,2138167067243,761460614055,3148336868532,
    3292499282403,1050921160910,1977504438392,3577734793763,2543094010592,393622112608,
    3055045098323,3426133482822,1193760736379,1965469723777,3625489360340,2478530668107,
    611207480525,3231740040410,3300087368571,736273115332,2424502004660,3631224280161,
    1885711467554,1404026582526,3537586173523,2739176603400,341898823862,3133073662987,
    3277775109172,640612291379,2540934803139,3537932343878,1476806058273,1870656115323,
    3585960949020,2144909674225,1206762927805,3498555220562,2654420849045,608718329057,
    3349591752088,3030994451765,115732777159,3202164571166,3303329188081,245577723580,
    3104863044530,3492603097949,454865476814,3088790291208,3605149137289,495186232744,
    3163526624214,3628818180717,354820520604,3313640999200,3533790955887,34007395704,
    3494900137354,3281106394847,443063086383,3635953416790,2838583326393,1016576864829,
    3647905448362,2204554944757,1584785116085,3449950786704,1433729369351],
   [2015589278511,3009476289920,652548147405,2186250174595,2388466207078,40861913643,
    2054178606801,1767664631576,242209613882,1735784072887,1403506339514,185977995736,
    1533070469113,1481909212536,52971659298,1823168332509,1892103082268,374450871582,
    2767914460809,2060037171554,1676606982814,3941733977357,1084522469196,3930219926358,
    4196772840885,1637104836485,6035099329914,2175720877933,5485221493409,5979539710524,
    2447238488236,8178552780421,2156553492100,7766626858300,6796864551513,4673848209277,
    9935039448020,279593475539,10542678555559,5732805634576,8370051289428,10252218575667,
    3926512696217,12741469723186,1761647181293,12675488720689,7486121362424,10134521591984,
    12169749413787,5677178882045,15075801404636,129087179226,15889127976285,5637478342450,
    14683309369296,10875998206361,11817342426105,15067796918352,7803523659542,17951253098237,
    3185244507117,19496361988002,1554178003061,19847758541001,6044634566492,19257311863550,
    10047039467537,18022774868765,13445525900906,16440770795370,16223503998595,14778795862407,
    18434565001704,13263221940152,20172107553249,12081854121973,21541455092182,11394997244182,
    22631652419693,11351357607249,23486415363522,12098591646502,24070026744289,13779403099893,
    24230062044526,16504001384866,23669510658647,20289664990235,21942555485956,24977420325542,
    18495531575021,30144857457027,12754269033938,35041924858290,4241045496933,38541773308901,
    7295478841333,39058115253066,21653592518446,34406494316967,37628318876257,21865063172958,
    51959609070442,861008903928,58248045193163,33027854483899,47436176292384,67107717600878,
    11729373913727,86392741599371,47709028611551,67203147636558,110477282700850,9887495602252,
    127742645315845,130951554389067,33150885363584,203005092483510,183139654509796,
    47907702132011,296884343086759,319111123580565,25116489192487,452583065223200,
    869814110050636,1043654852687574,948776542067854,690137487077472,406988458154174,
    192153387451840,69368029668888,16729835822764]]
private def rkmC_w64_s6b_12 : List ℤ := pzigCat
  [
   [505836081,1432483438,2950069885,5026105504,7409656681,10512538232,13895370455,17680437038,
    22003033425,26638658978,31576182855,36850661130,42323390477,48139118656,53798755887,
    59444247552,64851614765,69573436618,73756477919,76729776542,78481646255,78776146294,
    77026795153,73196468072,67329276103,59099102210,48874381767,36701405216,23230606329,
    9170940206,4715852476,17279025963,27368052328,33845351951,35191375872,30691717229,
    19026684340,464209546,27711459761,63002667226,105479457793,154138854870,207733096539,
    264513386082,322718974711,380765966492,437018130215,490781954650,541385299891,589232008106,
    635303363415,680932956936,728190935469,778966672320,834437170533,895714347118,961771354495,
    1030582312422,1098291277931,1158728737542,1205127206169,1229510852486,1224031809659,
    1182286469228,1099672733921,974708740560,810153552023,611804637672,389692105397,156532220962,
    73361455386,284851965341,463863343758,598668184225,679643675634,701280713243,661250299018,
    560499318269,403578360488,198103754301,45029221707,310676176596,580645145171,832538989092,
    1041094614509,1180419364212,1226219390993,1159699836750,972213891805,667567986876,
    265708670619,197423343777,672301901536,1100271131325,1421018503112,1581480863289,
    1543875949002,1295246494613,851936158656,261311680083,400073240459,1035160443842,
    1540054409293,1819457007610,1806591306025,1479541953886,872414521789,77913054510,
    763468058090,1487133376611,1935968332130,1998258601813,1638951606916,916688856435,
    19987719229,960891217990,1682933472203,2005835710138,1843399545529,1232105290056,
    327081916133,635828956891,1402708952516,1773971507235,1661158751142,1112503694007,
    298584075562,540268949680,1167767114835,1420544091408,1255395483047,755039080430,94824633751,
    517369917649,908100237666,989391182485,776816661352,373357540057,72872880889,422279825170],
   [587034139383,551802411360,367975635713,125650772606,85495884204,207700802819,231574894512,
    190846097525,137381001376,110495151407,115501483824,119512434455,72475630282,57414453186,
    251750376299,434262262274,495438940101,348817515930,8046495892,464137205199,820479807200,
    873203470649,523553647382,142315612824,857033802803,1274321559004,1135812665771,424036031314,
    585480938248,1423594984575,1644797850804,1066016379653,101532746599,1315928913670,
    1955943042359,1643279968148,466886578739,1021780333443,2063850189494,2083896057425,
    1013682954326,636651344704,2017101083971,2377578654626,1480125980927,242417268207,
    1888379914702,2557686308871,1848103747984,101619869065,1749622699445,2675868713698,
    2124306472245,355232014012,1664871385040,2783364561143,2319012176932,485649493089,
    1685476857243,2914790934202,2429175195445,459379881452,1845208758880,3075277504589,
    2427154053756,241347152721,2151504312271,3231301937804,2261244241003,193506749431,
    2573178415186,3309401362689,1869316750612,841539969728,3031424880857,3205773036336,
    1201470722755,1651575111155,3400049710058,2808144954089,248606412716,2509994483424,
    3516713331563,2026695515298,927894785176,3234063195217,3206479575844,833831012429,
    2166661237203,3578537230846,2328373323723,676392182307,3183469628924,3278591086061,
    862782256880,2225954226206,3596055147947,2161323063912,974244584528,3343415138353,
    3054717944018,321385388495,2670388983229,3497980714278,1475754781627,1753360664751,
    3534479902504,2384642001707,752453140999,3257614699416,3015231011397,212808981318,
    2777334777274,3388530179835,1068074054322,2197600414754,3556876817291,1779619405150,
    1604236375462,3585946877197,2342083648076,1062195022900,3540553126763,2766033180206,
    617631705376,3476253296603,3066593024532,302044323998,3433313655251,3254364551278,
    135550182022,3432931100159,3330128250966,128040957230,3474839959961,3284197876552,
    276992368768,3536175248961,3099944101130,561603130728],
   [3572734310829,2763896757212,936861150896,3526432198707,2279856131906,1329594536576,
    3340679768383,1687279045808,1643924749758,2987031330945,1073842058332,1783599975806,
    2497612118435,571628515702,1696850172638,1991172943827,318347440176,1435866341232,
    1665180048715,375902003880,1201352338082,1721612590739,623961982140,1318771707622,
    2215253316769,691948989468,2088011216980,2870657836105,33389368220,3504795247458,
    3003126410241,1767760001067,4971913521788,1731752522263,4506239423141,5278029324298,
    1415056514392,6977024121267,3137773496608,5724604216340,7213030959835,1722332246567,
    8999074943856,3646145402037,7580593727159,8434706279894,3255659736062,10912601730479,
    2653847166546,10167205992538,8343636000921,6332612984577,12153643138554,437077959830,
    13049328932083,6004343552902,10829145748812,11466291582075,6056056143593,14799936782482,
    204643882941,15439517597659,6716703755078,13419613252124,12371027362195,9247410950821,
    16382137322538,3701662935628,18364914251443,2372920138598,18309262838972,8229134439445,
    16488751223341,13316146937138,13343455256800,17314869660459,9367841734125,20122611069512,
    5025082931972,21808953031571,693047836959,22559814192032,3358069757557,22625293467505,
    6964557198976,22277652740932,10049928790263,21784701889177,12596514703532,21395707349234,
    14612533363373,21334013082931,16095683165730,21792825978426,17000084124193,22923266529197,
    17207639822138,24812689072134,16512973238051,27451025521515,14626103076302,30693959347730,
    11196633254203,34226813820587,5844908578018,37528830929966,1809083401776,39800640511005,
    12100150159977,39801557390790,25140798277334,35607607611075,40301433299879,24540405585658,
    55214359249414,3829122481289,64638359204739,27424501972335,60237666866702,65122369833740,
    32512779474193,96922180434959,24274024865287,100148558109182,102513364355564,44516975700227,
    164701202120277,87377288995941,130001030834208,242954971892172,88444591108584,
    219147066756775,378361352323741,178977578529743,311575353813480,814731743296966,
    1067488595932914,995520313128648,712480250774474,395398226077224],
   [164290083625778,44932912352272]]
private theorem rkmWC_w64_s6b_0 : bWinChk 580 9 100000000 1024 rkmPhb_w64_s6b
    724 rkmXsWin_w64_s6b_in 713 rkmC_w64_s6b_1 978760748 = true := by decide +kernel
private theorem rkmWC_w64_s6b_1 : bWinChk 580 9 100000000 1024 rkmPhb_w64_s6b
    713 rkmC_w64_s6b_1 702 rkmC_w64_s6b_2 987140685 = true := by decide +kernel
private theorem rkmWC_w64_s6b_2 : bWinChk 580 8 100000000 1024 rkmPhb_w64_s6b
    702 rkmC_w64_s6b_2 691 rkmC_w64_s6b_3 795493112 = true := by decide +kernel
private theorem rkmWC_w64_s6b_3 : bWinChk 580 8 100000000 1024 rkmPhb_w64_s6b
    691 rkmC_w64_s6b_3 681 rkmC_w64_s6b_4 730179094 = true := by decide +kernel
private theorem rkmWC_w64_s6b_4 : bWinChk 580 8 100000000 1024 rkmPhb_w64_s6b
    681 rkmC_w64_s6b_4 671 rkmC_w64_s6b_5 732513841 = true := by decide +kernel
private theorem rkmWC_w64_s6b_5 : bWinChk 580 8 100000000 1024 rkmPhb_w64_s6b
    671 rkmC_w64_s6b_5 660 rkmC_w64_s6b_6 489555683 = true := by decide +kernel
private theorem rkmWC_w64_s6b_6 : bWinChk 580 7 100000000 1024 rkmPhb_w64_s6b
    660 rkmC_w64_s6b_6 651 rkmC_w64_s6b_7 485251167 = true := by decide +kernel
private theorem rkmWC_w64_s6b_7 : bWinChk 580 7 100000000 1024 rkmPhb_w64_s6b
    651 rkmC_w64_s6b_7 641 rkmC_w64_s6b_8 433968155 = true := by decide +kernel
private theorem rkmWC_w64_s6b_8 : bWinChk 580 7 100000000 1024 rkmPhb_w64_s6b
    641 rkmC_w64_s6b_8 632 rkmC_w64_s6b_9 522769720 = true := by decide +kernel
private theorem rkmWC_w64_s6b_9 : bWinChk 580 7 100000000 1024 rkmPhb_w64_s6b
    632 rkmC_w64_s6b_9 622 rkmC_w64_s6b_10 431511585 = true := by decide +kernel
private theorem rkmWC_w64_s6b_10 : bWinChk 580 7 100000000 1024 rkmPhb_w64_s6b
    622 rkmC_w64_s6b_10 613 rkmC_w64_s6b_11 488774403 = true := by decide +kernel
private theorem rkmWC_w64_s6b_11 : bWinChk 580 7 100000000 1024 rkmPhb_w64_s6b
    613 rkmC_w64_s6b_11 603 rkmC_w64_s6b_12 434255830 = true := by decide +kernel
private theorem rkmWC_w64_s6b_12 : bWinChk 580 6 100000000 1024 rkmPhb_w64_s6b
    603 rkmC_w64_s6b_12 594 rkmXsWin_w64_s6b_out 342870180 = true := by decide +kernel
private theorem rkmWinIterSnd_w64_s6b :
    RkmWinIterSound 98 1024 rkmHbWin_w64_s6a 724 rkmXsWin_w64_s6b_in
      594 rkmXsWin_w64_s6b_out 7853044203 :=
  rkmChS 98 7853044203 (rkmChS 92 7510174023 (rkmChS 85 7075918193 (rkmChS 78 6587143790
    (rkmChS 71 6155632205 (rkmChS 64 5632862485 (rkmChS 57 5198894330 (rkmChS 50 4713643163
    (rkmChS 42 4224087480 (rkmChS 34 3491573639 (rkmChS 26 2761394545 (rkmChS 18 1965901433
    (bWinChk_sound rkmHhb_w64_s6b rkmWC_w64_s6b_0) rkmHhb_w64_s6b rkmWC_w64_s6b_1 rfl rfl)
    rkmHhb_w64_s6b rkmWC_w64_s6b_2 rfl rfl) rkmHhb_w64_s6b rkmWC_w64_s6b_3 rfl rfl)
    rkmHhb_w64_s6b rkmWC_w64_s6b_4 rfl rfl) rkmHhb_w64_s6b rkmWC_w64_s6b_5 rfl rfl)
    rkmHhb_w64_s6b rkmWC_w64_s6b_6 rfl rfl) rkmHhb_w64_s6b rkmWC_w64_s6b_7 rfl rfl)
    rkmHhb_w64_s6b rkmWC_w64_s6b_8 rfl rfl) rkmHhb_w64_s6b rkmWC_w64_s6b_9 rfl rfl)
    rkmHhb_w64_s6b rkmWC_w64_s6b_10 rfl rfl) rkmHhb_w64_s6b rkmWC_w64_s6b_11 rfl rfl)
    rkmHhb_w64_s6b rkmWC_w64_s6b_12 rfl rfl
private def rkmC_w64_s7_1 : List ℤ := pzigCat
  [
   [439967584,1252317033,2627104438,4591858699,6911634756,9807528185,13026940538,16788520773,
    20894567180,25218522509,30126565674,35115237761,40392206850,45910329927,51422390468,
    56886369253,62148507738,66990631289,71306198226,74531395599,76809916486,77653286915,
    76742318178,74232125623,69564797808,62842764311,54057239706,43446006225,31388339868,
    18243985197,4846882160,7766926638,19020314749,27381543224,31838076587,31287281964,
    24566358355,11183497512,9737089042,38282349085,74266106182,117108966771,165684465448,
    218841620611,275105179178,332449052541,389860842880,445702385357,499020302944,549652687027,
    597395065228,643294369151,688546286356,734601453321,783161999900,835528481757,892229782358,
    952992442513,1015753179288,1077491810637,1133116577182,1176486838897,1200936904158,
    1199155693595,1164792957028,1093525004239,982746720674,833866171521,651272520102,
    442797567525,219614831702,5372091378,217853312899,403963405680,551322475163,649749260594,
    692315976419,675723893686,599828472067,468618952942,288594540755,69497789064,175709192174,
    431636868933,679797759858,899202853039,1068175580732,1164311452317,1168725647184,
    1068196999773,858072300078,546070268075,153085902192,286496503588,726585392503,1114606055306,
    1397512597883,1528685228860,1477170453555,1233096836304,812791656579,260054683348,
    357288357786,954090376693,1438418530536,1726685891055,1757300642002,1505289534283,
    991931444668,286903413189,497390888559,1221413834452,1744141913401,1950680868754,
    1780812199839,1248769129900,448159720367,460798591723,1282234031176,1829006444919,
    1967686624738,1656965355021,964008733068,52658683549,853915977297,1529531853640,
    1806530722703,1621066272454,1032887311353,209522709046,621690375690,1238085885627,
    1484507296520,1317041267607,810217711638,130203850573,518827472987,958024987144,
    1085068475587,897780596540],
   [486694008067,2491805713,419104673144,653972780837,668106816128,495602644393,221133357116,
    54378715506,249526981349,326704826594,296950045825,205439740380,107430958705,41208209230,
    12782247339,1851489457,39363117652,122613110675,237938588638,333112127751,336358554174,
    194818587721,85761331877,422059606562,672982498639,696005083668,423383652853,77705875575,
    600587825722,870115199455,684831542594,88133945217,542201844237,666719602982,99610172725,
    538012268263,351260255568,355416537408,166119989571,661585848973,260738841878,340428290598,
    288244099562,333606516071,562386119206,1636232279006,1200093900810,348525095166,345460672750,
    2022250499706,1443122959088,1262452442718,67753228391,1520162867638,2211317131220,
    1568557824448,100872279027,1448165190398,2701479651288,2044218414146,82893703376,
    884718512670,2297358933940,2101239185684,408938059356,875292069810,2354183397044,
    2412597027228,711477369332,948547538252,2433855922534,2637712338674,871384288160,
    946443927196,2803512589514,2447735215388,1106371892998,1104488453436,2926389582384,
    2094950717140,2163772558464,761732357724,1622148650882,2906301260576,4943802258586,
    1348074131836,1876177678647,904807393001,10907603692,2680547318341,3355988245959,
    1499022676623,795768169507,2843993914199,2055826963333,2446778681029,921941604137,
    1266919096037,4684296194907,4420747696235,604495670673,2069359208864,172012020955,
    1378600864128,3204720201470,1783197831170,923655577460,3091449136298,2774062445628,
    2824227758928,792951722884,948430317874,4791676328730,4219430643480,677111260042,
    1673557075659,547141106580,2009390702285,3752244236919,429556453221,1633853458571,
    4186960613993,2194163014259,1046938396281,2791912460569,2316680593109,745520682925,
    2578862883139,1795713429537,4321268745301,1384391241460,3735067814801,4050665282067,
    2426166335327,2607340222191,906570670038,2674315183546,1409590206156,2368641925224,
    1610771493622],
   [1948819312951,1658582984909,937617293507,3399166248287,2568080693503,1227454568151,
    3570778343439,2685269724475,1330550371323,3668510039101,2597574282633,1493768176019,
    3750032719133,2366712965765,1734505730605,3785884796037,2043547487593,2032581409479,
    3739198862621,1663661027891,2424271161511,3277636402565,2018147838543,1418244977165,
    4380137074589,1099791231929,941218485015,3727268181299,3382854566055,346559448301,
    25966340604,1260190068877,801651535323,791628165843,2522044027050,2166881783688,
    2315605498369,11250061074,936717535080,2799459588345,600859913456,2414792906962,
    3300751874179,116474851384,3804301631424,3454356914523,1406681597217,5080090953948,
    2506787073259,4653999445901,7710597622562,2979835510933,4314485076499,7202730454652,
    6484389496339,6180266197312,5815920727511,6713560930222,7773763710411,1820956820298,
    11288588669221,3365957496568,10221353625667,1174320550616,4489690546518,2373723852011,
    8722441927554,11770010235912,14942625764649,3249469872044,2844789027196,5625934101226,
    4710413909855,9332205861205,12573678123550,2634960849081,2733550467824,25893232963370,
    3671642330541,7334667332548,11758786237972,100931997726,3781603668416,4463242316608,
    7452964739541,29875060297373,10428846665420,3545509852538,11122379568082,9467906395635,
    1535668882849,7675240101943,12622388239151,19017462729719,18345374162309,20415532708460,
    14136703571010,638651472188,5542031113974,13486814852493,34302420394347,2214876199987,
    21506110971906,8782677939115,9148168516947,5435892014789,10065203646204,8783482897322,
    24624398637484,6963834458278,19262235536746,34486057703052,10101800822624,12156409806476,
    17831527295721,32069910300875,15102343427499,1049771664051,23938707805374,11412783437632,
    19820884274784,48403309222734,22602807679566,31208275032011,20203621446483,33240739849880,
    25913715283056,32557212973739,33201750620479,30054201036110,42576051593950,24256979335489,
    53643600398285,13162254742164,64880814850758,5488160161370,72920043191845,33346398399283,
    72241232209008,68723573870514],
   [48429875053911,132286663562953,72307087927048,39987217330640,38744808509320,180595845691190,
    45436547949590,164913238041572,221207415378626,71253423446214,311723326005848,
    342387074941788,119895871863348,444902952488588,954383613886458,1144918818820136,
    924938546766430,519426888091932,183518561774478]]
private def rkmC_w64_s7_2 : List ℤ := pzigCat
  [
   [201984247,732481606,1884788445,3455857854,5656102373,8250314682,11221358493,14726905652,
    18524547425,22824220002,27296178783,32147045640,37349563919,42495533026,48003815261,
    53442223748,58711221165,63754613442,68293644473,72143544250,75049169855,76678809112,
    77057813449,75536949914,72282279655,67185463800,59883923307,50803606628,39921186801,
    27768706316,14859216271,1901415166,10101586818,20306357897,27651670102,30647192211,
    28703155050,20599553501,5570584496,16689858158,46467733449,83266393414,126803950065,
    175929651994,229162299189,285208461724,342441668511,399306075550,454820988261,507701827086,
    557912581719,605532517462,651164349793,696145384650,741707657925,789637843632,840890641493,
    895906027650,954472224553,1014644534454,1073196854239,1125860295496,1166333777699,
    1188476582744,1185491946577,1151174773194,1081313604473,973482618258,828542597851,
    650590277322,447035008199,228297362316,6831030219,203786516273,389549050368,538428943973,
    639992929812,687059895539,676202465634,607035197235,482877136138,310596810011,99342435484,
    138261330036,387608780539,631444861412,850299453125,1023811682644,1131352441579,
    1154670133626,1080182347239,901591651994,623125623545,261230220296,155481787034,586322378473,
    983342061138,1295681615843,1476408694804,1490637955139,1321268123224,974216416469,
    481696358358,100730427690,697673243999,1223759563590,1595632957875,1744492422330,
    1630180372169,1251828159042,652755865957,80448246059,828143820736,1456680148221,
    1841318733548,1893832242441,1584774335894,956393725227,121948578858,752394891454,
    1480898365903,1898396537342,1902641241145,1483159028444,729590785691,184150817381,
    1039722244924,1629370050117,1809485911362,1541220004515,901973380630,65629924745,
    744174465411,1316511992826,1512162018381,1299687434786,762148484283,68200422532,580918194624,
    1010767694905],
   [1122937727082,918943437179,490100197408,16764509200,448972743283,695011556968,712805605025,
    533480199138,242558627771,55958849343,274793617038,368734957779,342440923488,238933560389,
    115674106488,19968611947,30001316131,47760000498,65291237611,110757413134,187540828125,
    263998772104,284476352647,197108204612,12255511458,296538879955,550665966912,649816016943,
    507677328990,133593435387,344672868667,717631751922,787103443699,482017445648,62040493498,
    533640442571,614928993820,226858895223,334100432323,571989752616,264951393951,202069882469,
    191999327658,321238962364,556451684913,68545132302,348500358298,46026817766,353574771059,
    303844929685,657681382652,101092260450,159905346991,860340808437,877974224222,73252936928,
    348978194599,738908474211,649009725852,1183054398194,1001786682418,321844231043,698720172518,
    2025464786978,1700447777814,94751982139,584923031674,2197695110176,2041800972464,
    121774877766,427571236570,2171358759936,2570113760444,765069132868,557399762022,
    2002675549374,2312901597156,857070247286,203554616588,2251955432232,2293624422078,
    1089324067382,242449441940,2881519816816,1958715797072,1297098304508,925829016092,
    2501629146484,1950676898372,1978963804578,1372101929256,974168011186,2677246522724,
    3919762476598,604328517610,550128907749,2324808599162,5232681268912,2173961165428,
    1752478179082,1990390867720,360779132452,630005340489,2523193937225,2043548031707,
    1131992747325,955449984685,4048038746385,2945922611955,691871562980,489670756721,
    4719205226545,3281119040703,2812888420253,2610259881405,896784428073,30031621158,
    2342819278016,1350210526612,614777994408,1449035084328,4708707770374,3084336189892,
    1189164588707,2083484047878,4537198657178,2265760847940,3027860776782,3601788480086,
    106661284484,2167357381109,717694351290,2624389148585,835286490335,4240441391071,
    422215595525,2852435874677,4168101002369,30556878341,1631337849737],
   [3190609256529,1934502345069,2297198797009,1303054379265,794886263231,4002227067191,
    4408586965297,2105836078955,2565130510633,617535700743,3240055906278,1866248410026,
    1063579586152,2096768624970,1065811857017,1956864262885,525045668563,2990519425071,
    2745644077303,1241094205341,3495212288447,2560998194849,1563564814889,3784354693225,
    2038002442393,2275884449587,3248402703449,2624187024539,1502773983597,4235072052263,
    1810686730443,1827189358865,4004554483287,2391578091471,1106271218039,3291330057947,
    3989760927169,800670997829,1686764703281,2814133657807,3110525159311,3615529207075,
    150646560876,195650455415,4289195441427,295384468085,2432765287410,1510292430117,
    1567370140846,2659172702968,3923419277099,180967152077,3328229988722,3396197201231,
    2360648404605,6770172810874,4634566993291,3243154633283,9581544357070,9387918111625,
    5777523922706,4798106678765,6199000423064,6911494613877,6102175298734,5812729450213,
    5843936082916,5918612158733,4025996318066,2651439695434,4984162178349,1508235237000,
    658276845687,14981789837581,7629571393804,9111729412853,6140349005511,6457158634114,
    7621519215114,7920782510684,11992357334597,3435314611568,13567977139442,14491481893787,
    8713517939210,831108795357,11540756051427,7845583417496,8035245316930,6979265611796,
    4759175090576,20490619863958,11394456550507,16156866206966,11095070796606,3266472998404,
    20196420060933,11693758118785,2524936689746,2778332440028,6934124880644,8559994432585,
    6686133951678,330868623139,30087339972041,19481176445463,2938856121190,1576651780449,
    10430093126150,28594757850428,16764092631761,26564594446513,10905840513829,10680877104356,
    6257007380073,917786743929,11436234055029,6086652418911,21361484358984,1454363620388,
    14577237441170,19677143700518,20023784577104,34405921976408,13830423809266,2253633223589,
    29893991272129,27179989833075,6128277350364,4653757489110,4493403135889,34066184210932,
    59567860022964,10332731632294,35216152376483,1305412405730,43559973778044,3375567010622,
    46913841847501,8596496713087],
   [51067095464436,17219080831552,54617664006539,30096667766613,55684459688162,48727852306542,
    54098844432011,63936564389009,19109724902360,139110560280612,73125994707535,83724842518235,
    40465368063046,52827964658949,119745701758390,94640003169164,40239843337272,244969341493966,
    94908687291126,123076537406234,396011647059606,194161162716910,139073378247044,
    593031745073924,1091527060523512,1153510014850550,786876530366276,324497850805034]]
private def rkmC_w64_s7_3 : List ℤ := pzigCat
  [
   [455593085,1281138572,2655788789,4598507828,6881921655,9746849382,12932744817,16635886476,
    20638861243,24851066312,29652095049,34532493218,39658242805,44954667152,50269359763,
    55608303680,60728978303,65405361870,69667843593,73010904806,75396298459,76477623704,
    76099974271,74067707174,69999085087,64270473652,56483301575,46856926922,35885419707,
    23626294200,10965525839,1492455215,12717992606,21750414505,27678038444,29221003361,
    25373988734,15548810687,1367757411,25377422046,56613465955,94858833618,139259704959,
    189016267654,242526353757,298580233970,355648117335,412033386900,466816894321,519345143000,
    568995712803,616229903696,661476096001,706141802702,751488793439,798676020482,849052869067,
    902710914844,959262148405,1016919178198,1072350325899,1121335057772,1158371020197,
    1176944480370,1171030710123,1134671103674,1063884350429,956464082410,813081615569,
    637940166222,437776834977,222776043418,5057281047,202363668157,385903728024,533371294829,
    634945954164,682928327107,673952635244,607682391369,487361390258,319616428135,113666434948,
    118252166692,361862911595,600750696558,816597953089,990356214728,1103017380567,1136843737314,
    1078956667151,922333353914,669128629549,332634031522,62566879844,480673594643,877391078746,
    1205170524545,1417885017420,1478862084753,1366405565048,1079520859307,641170409828,
    97350748949,485887608737,1029836036724,1453701035177,1686151543320,1678072175855,
    1413761489936,916543397325,251642201970,480712346748,1158865116609,1658799600974,
    1878511611717,1760525724392,1307914878679,592347011348,255394275118,1067060684559,
    1670580467458,1929562907047,1777285380110,1237420992037,425272298794,475501722836,
    1254834657657,1726980005070,1779969406483,1405551990620,703893846063,140993592145,
    910614221090,1411071109679,1524443992362,1241084356313,658611093084,48971975138,683334071203],
   [1079590178640,1151329727273,909415779218,452645380329,69528899685,505214569944,744588880777,
    748343801636,550988431613,239869549136,77507370616,310517022717,411149173946,381385827327,
    263684299530,118805635209,1083460703,69664588804,92347585331,97188021472,114758606303,
    157753728024,210141496811,230149320964,171761291099,13046930672,221126887022,454698228075,
    582911694316,518785516913,241894172386,172343999744,565665698243,758009086058,637318858007,
    234350984174,262652035234,585515926947,536778935666,134234594849,360307440081,594036211660,
    399476552867,24558757933,248263584844,31359023747,365628248343,417312034192,12080774870,
    409076912675,273690049776,86891115596,36639644670,538404654719,564168206418,101290626771,
    163047449872,717841912003,449847605928,433794550848,190322032327,750367361301,413765568024,
    418143974718,65311421138,675678041853,65803357647,685718256004,469637557202,1119396512303,
    825248604567,796065833462,1181897436530,497537683799,370683955817,1425013615240,
    2001908077846,320186638836,179510702785,1761853357004,2180915754820,995316665468,
    348407862387,1738221356454,2105152778240,1556096872558,154356788349,2338053724846,
    2368930108802,995792145966,224310757846,2196205311626,2044810999420,783263584230,
    1095700002806,1904064305800,1508908320860,2285471935184,978239459556,964028338444,
    2140840364278,3762135831210,480935062520,620618332953,3708721872280,3580116725348,
    1586795263974,144852801934,1440437557956,2113923766932,3107077318180,2461341385882,
    2637710124288,3609660870256,2233098990352,2502384219617,862158013773,1329183874290,
    2395047551391,3382400194953,2806481522827,571017867447,931288695487,1761173573743,
    2592976027569,2913009367461,3212132429743,4904953039837,1310975351385,2345702926614,
    1267861104355,1272821455067,2907886356550,4030071399620,11811594649,3899331901248,
    97625413992,2276350369232,1838972480680,4597413389594],
   [4518870594282,312294480982,2322562210248,1145193993664,2372984095419,618106169739,
    714825200917,2941232556117,2532983753081,2672516651055,2294354018285,555971140485,
    2650165585629,4020859326967,808939678595,1032758502571,2553449780419,977951785343,
    3312636588957,5388213161667,2441157397923,2120947536763,891415792331,2898238618952,
    1662755370380,1007976918580,2125394159314,1219290124369,922165829859,1134398376247,
    2458179553249,2712480899927,1164578333497,3780832758291,2234495129649,1668994128625,
    3826491889395,2369478440995,1652035794347,3475958896927,3395247869901,864874134921,
    3203575261599,4019510795619,1357116528809,2381224211579,2701675016835,3085905180105,
    3910222134063,183904410247,818479219159,6173162916091,2199769862491,483714114300,
    4695600692443,1341917192441,134006823136,4019006680989,499461261185,6006407472984,
    3716508555323,2245371118877,9816945799268,12199992676073,7467973711834,3893159141549,
    3735105421468,6845992152013,7502128658322,5702383523829,4501954086032,4447787901755,
    2954594678106,352789693140,3614042680169,3564445433378,1353547679378,8663132886113,
    11055338332112,7827340370659,1533797859144,7703411917020,6696623519549,617127250489,
    3999407861843,856331909300,7906021618957,18064082899899,19480597093758,124948578556,
    5257052935443,11040639866084,4505004371539,1626774691318,4118850066462,6604879267218,
    18092456718541,11812163183702,8007526670931,3316072459346,11506184256086,12833719297672,
    1149000732729,1863926644472,22504027950584,8695152829902,1731673531606,17094067235133,
    10279062575611,8566769995280,5881893077911,6050303107553,17314433845488,4846254859638,
    24517727105057,5226348351997,22420465653597,16419478325495,10625083947714,32241398462594,
    5356835744441,16390970340257,10628964854725,11742596323207,13407568147632,11909546385897,
    12571202081645,1901887206310,2407769568835,12132769060176,4392736158680,13431889095570,
    22145741574288,29354849847854,36136018044030,2330760385994,32220661900419,13181432599145,
    2416295275290,21284781410563],
   [9103814187573,51930447357396,56742903748756,9348734082617,25937144246721,30660960439262,
    38194196868880,28918000977773,42063996341395,30401521067398,49408818277230,28220676335997,
    63415800242227,33255396528766,55653476331936,17820797215080,137165397082243,37894525241326,
    122094582294704,76240913225715,15014320274398,70535892235813,30339022556833,130546286465188,
    18034428817453,145520538957150,201752988621642,6140637729708,271187889630710,343971391211654,
    91387063717638,218601217354916,809680809842464,1232003616415950,1066664091684734,
    525914082833468]]
private def rkmC_w64_s7_4 : List ℤ := pzigCat
  [
   [232913302,829783909,2083928450,3691208979,5867857716,8415716969,11430071174,15012674847,
    18692416648,22897116467,27401621558,32114706503,37116033708,42260177787,47516575758,
    52840530389,57863602938,62758084863,67178403600,70963661661,73827254704,75503134921,
    76065451110,74863245191,72022576114,67405308455,60773113208,52506465289,42448582094,
    31150021229,19059844724,6657365883,5144385715,15377095538,23168579499,27356252806,
    27077909529,21150132038,9101938255,9803978501,36036226630,69065114705,108873336702,
    154528582705,204973345602,259022510251,315005906266,371791037049,427733937756,481851424599,
    533656547174,582673549565,629227034950,674275384307,718522711040,763494982661,810198118582,
    859751291359,912327336960,966856259369,1021908349514,1074149392307,1119166762664,
    1151709545319,1165721687148,1155304391409,1115219588484,1041292056837,932112099450,
    788287937965,613983375272,416148640713,204197987652,9704800728,212862797515,392344700928,
    536087218657,634342190702,680060509433,669496779854,602749825375,482878058278,316877774329,
    113940378304,113974016890,352541939589,586245360988,797452867761,968079213206,1080583910183,
    1118523547740,1069304625775,926354474752,690547420647,373370561542,3529927920,407802224741,
    798953053526,1132242218243,1363225943858,1454856991887,1383261361856,1142628883261,
    749270866630,241907998569,321457718379,868193012506,1321405914325,1609912187670,
    1679794850517,1505452297342,1096643487087,501540023322,196088002352,887888572747,
    1455571298182,1792491860887,1824537298536,1528174514763,941525431904,162663117113,
    664254315901,1374500255228,1817500459507,1891211761022,1568571956347,910631724338,
    56600608265,803645608197,1472683651602,1794576926763,1694404299708,1199713900205,
    436893755656,401554424794,1105340083161,1502356223720,1504596182733,1130028500544,
    495405156395],
   [218206869551,818546579984,1155477474841,1160614271762,862577633377,370647161586,162115264056,
    586331149455,799650933368,771536262249,543547441676,209129539609,122144982535,359194950722,
    454434850687,411845572280,276284444893,110672541174,28102725288,109563979569,134984880968,
    129311845911,124387698632,139297961697,167348317914,178631054681,133949004416,8993595115,
    183543556501,387455290430,517693766021,493730816698,282914036225,70679456247,447504983980,
    692159480619,682536549556,398642212957,48250851227,448922823878,594065185303,394500606702,
    46499595810,470044594081,612031123366,391079431137,7679020543,253198654376,142960640729,
    190011181815,367540714042,141233843235,306192685331,519886016916,306325620837,15906295136,
    115076482035,512491511232,632742298167,281413104036,3690514885,196753701684,366791303375,
    17605519160,253171294750,230937185104,682034706603,121082778548,506235738866,30634676500,
    619713644005,1149394926,422970097068,365846913934,547273679305,467375657323,435278061890,
    806704879350,605435786765,968027900193,626466792088,1172456633478,253630058575,1592366374425,
    360415178520,807913663776,65868850162,1556576176441,796590347964,1352617993298,1052959810298,
    832891345915,966828890202,2312282494650,1206403612312,289751309443,1339750487204,
    2293683717522,752450509326,79234329182,2397026913420,1677430440558,1371224691152,
    1006469808816,1599396090764,1423218992268,1851644810780,1526292450572,420366566691,
    2800806496888,2940184591950,178413900716,112990765649,3309472468768,3054986047464,
    975156037352,201731393902,1708017091524,2759563329426,3475685852644,969856815414,
    285504662294,3537657304858,715492293268,440484541802,3569942241294,5199097600494,
    2532406814120,442013835502,1399918848626,1126965856310,180552592880,2358963199151,
    3310150181861,416403224175,2295944548293,2202143941999,228152235679,736727548882,
    7561617456859],
   [2732042994347,2261121446187,1817883588173,1890595920907,1543827440805,1333381923828,
    190498671602,2547855100342,4041278449272,263060614675,620302902090,3391423347130,
    2115100103816,3158069446440,4489995672054,2497419108876,1729714542406,822686355450,
    778276193333,517389840494,878070061279,4299840664227,1868998771575,732821630553,
    3211454942281,1778350584039,2183076201261,3871146437273,770795504463,611304999451,
    2515124683393,1067558401139,4372633949869,4708795776297,3042014912209,1898168856099,
    778148413009,2669616545224,1058421894724,1319007496052,1907961142218,1126690806871,
    870232127203,675621566875,2575456009113,2844826429729,960083034571,3098308339693,
    3714412063053,850489082721,2977433873725,3767235912535,1752595090293,2691666381861,
    2437341321807,2751280295887,4482665926733,599902718691,785863456613,6960382639301,
    1877855227513,325224734796,4250802234077,3163222424615,127372181840,5444698327497,
    4488840688887,7877048721548,15777380629795,7089560424964,5083215276071,1898443389530,
    4340280167801,8469149259020,6916104075183,3972521680832,2308981182937,1489223995674,
    742157288697,2454143331767,2759394499554,775464379534,6684359870205,10571940923690,
    9083079501073,2014963020134,5374638980752,8093422706069,5681679981206,1005315045819,
    2383709675071,360776110452,2034443186125,13321278311462,14507406425173,1718116972972,
    13833335432752,17707338374103,5930849212275,3643836585413,1391046474580,6043226536555,
    17592308834948,13397765517999,6027735415490,6497718853142,125988584947,452989526347,
    1983867865912,3382654003797,12617521992647,13339101962920,8768491259068,2737317099016,
    1223262991754,5094450177598,25334147266212,13337753670258,13177482729999,4339613917345,
    7720151053342,23415026001445,3158664958374,10873588096936,3267522616962,3280119326113,
    4354581669584,28419267435873,32616538085523,9469376071320,10249077390452,19690055016678,
    8519561451161,21076474321065,3051767375894,5239794431391,2064001565693,11650105223049,
    7382392541061,1746237343830],
   [72524557274,7918321010200,5584601769508,8329910603976,41758550824270,44502399936192,
    3286317447917,18105967289115,5580391559342,13161655668347,44182541102479,2393471101082,
    65791805854596,34486611979946,25448295567787,3757633621198,53549069671504,6525420745516,
    51356243164771,8881773897899,70040904001388,10455370783813,39915174901561,52258413559481,
    115430877530650,20359660370378,152668660545879,75934555711888,17734533497290,20654633739488,
    21819501284948,139086720314449,60852914799328,15099327530838,17629994918061,234585461650322,
    52290042588788,70470414197886,358291723374518,236872459686980,28405401761250,409506752972260,
    1098290945086098,1288694270680886,783171556387360]]
private def rkmC_w64_s7_5 : List ℤ := pzigCat
  [
   [559223920,1527335255,3034499714,5025440085,7283972228,10269273871,13499798650,17096641709,
    21150579530,25464079647,30065093448,34911661623,39860711900,45116156355,50272286600,
    55385697049,60300892716,64845827261,68926195080,72044764777,74423868266,75539766569,
    75119262840,73262220855,69522775752,64134432365,56873413756,47839829085,37467287690,
    26032800499,13972826994,2098152425,8892121793,17887940498,24176222811,26486045826,
    23892274995,15757049372,1064187589,20273500335,48702937372,84025605107,125472960644,
    172574583895,223948761850,278351007335,334435303046,390812671731,446190614220,499565423793,
    550434261704,598798717549,644632729200,689127719223,733106606648,777655936701,824092588140,
    872807285105,924120918426,976883772287,1029172036550,1077912256977,1118335551150,
    1145632214631,1154059759722,1137791720501,1092044171526,1013378711231,900440971748,
    754535298813,579453804422,382721631161,173629216542,36286469408,234256215103,407964694094,
    545600516995,637795616316,677974343313,662677244902,592167732931,470049775700,303059688231,
    101175404702,124073082106,358387375979,586298388962,791405108407,956307999308,1064491177961,
    1100894511454,1053886272219,917310633180,692095030883,388310425310,26057392913,365292248379,
    747690051140,1079375041613,1318133047310,1427275794807,1382259759730,1174514549783,
    815833657474,339465464821,202518965049,743529175390,1210396616067,1533638786348,
    1657257808513,1550145981374,1212391472189,679914765338,23030710013,661746456919,
    1264055855190,1677635102067,1820331740090,1651248035777,1183566082958,488540255883,
    313745209213,1072615949128,1636213718365,1883421888086,1752431438687,1259773403214,
    502044833685,361267058115,1140344395334,1659726121477,1799768713186,1528658224241,
    913259375184,104203914783,700184282967,1304083819822,1565459520287,1432057029562,
    954410345331],
   [271104654134,432160311750,972927875455,1222275322830,1137839201727,769615222994,240762936849,
    292004966369,686532533126,852873248925,774769022464,506096857615,146884192064,191274127356,
    419644799015,496380201882,430810636221,272160898118,87462849147,64863039325,152437932054,
    175094754721,157717346916,133166653529,123904499128,130583014145,130400395194,90617367947,
    11710807923,171001894610,344425980159,461634526208,452802026905,282140320640,23502428380,
    370702612649,627816578448,677919980379,477202495712,91565980189,317641671995,558766236248,
    504731881107,171407551998,272254959968,584529641327,589081746606,296057746529,87505319021,
    290687530108,181854491985,110775468021,284855169778,126472946295,271052529473,566033848052,
    501914022575,197447180116,42842863671,247065587438,551705254445,526915270728,147749763465,
    129711635159,10330969223,272397817180,209737655025,26690801025,63994103723,371598151130,
    244415893255,270059402389,274135860418,360218854296,516664274413,145707297031,371057640422,
    278604431750,418505087563,285794637209,260978483196,497012586290,136914423161,858398580249,
    337445360734,681015684606,186350763806,1419314292151,416655589930,873248330334,416665307018,
    1768799345427,144971192232,1094154392734,552902815078,1201546885793,383471676243,
    1095223488868,361262344304,1631604312977,475638000343,1276297671664,855143826120,
    1464532961145,924169785004,1712356897766,576897322978,234932298474,1401833178734,
    1816112494366,249237996060,1565823195950,514572220256,1381794320938,2452118158254,
    1051994531876,101366160391,2785748724060,2670545034542,38730062724,25328878766,2997671208522,
    2436993021154,477739636280,878125625680,527625494332,3965995237100,2448793062822,
    603035589305,1194878679962,3208648463190,1816231924562,791204707022,3368389800100,
    2862426374026,8558700133,457002828284,1202853132888,4855906316248,2986626922424],
   [2175902349568,1231902847424,5652407735772,1332882916577,128742275402,1297971202466,
    3206780755325,3298302184265,1646592855041,1285362691922,1117861712209,3825350260245,
    1884235142733,3706730704709,3965343561749,839184036381,2794918279487,3364196488401,
    873973271414,1733656647782,1311301551492,2208884407660,872231876964,988441176458,
    2422303904500,1691690006242,3925712299488,5260703250402,1159750129512,1574372136658,
    3257097188848,89205663113,631158085535,677069500553,3659942675657,785534402917,1530936729995,
    2770429839137,2467231721879,2510227839207,3372263370079,180548587251,912595642471,
    2191807527991,1688507710555,4847679378361,4704269649831,2635232469659,2077030061287,
    630920347535,2378042740510,1390500852406,250940098178,2329543626444,439434605521,
    2132543732209,8797123768,2026481873621,3106174995673,1641722001565,2884146335549,
    2123499908227,2018096631085,5338571913275,321481532069,1073202867539,6315632857561,
    2577080625647,536636997672,3350103058783,7538343911853,6893191728482,15549479370507,
    8453725325952,6561642413687,2326709736957,5860376669895,5021778113932,10141600847523,
    2067359750532,3732654755331,3049692686075,1473866728489,860165638021,1508405028282,
    915039695768,5290877656821,9822059010986,9030792766105,2573331128022,4263643580086,
    9050275782779,7294506951188,1974723359993,2831838398455,4309914457518,4534333552533,
    5956790521354,9131622481161,8339856215878,3361081863090,17506586085625,14216974759818,
    408636521524,5161745559667,3761502377165,16701096704856,13009702313807,6315982488886,
    9682119012255,12129007871253,2891499111208,2169818832506,2248538405199,1603298652475,
    9990801679710,6238848742623,5868393035136,9058347118876,6629748916493,6617729186403,
    4854763915071,8925927898274,11312092275148,6855674863267,6688711015855,33822356076520,
    6338984610290,3391073461414,9841102113640,746400168199,19394386248179,1078722352214,
    2803028042936,10002677322275,23788216858668,2539428061182,16774617635879,27422559739557,
    24581016864563],
   [18682845407498,12061953145076,26355444027,9555307543505,7053350074839,1841935499504,
    7666999818399,8088281308081,6455435984783,9593264851073,5972329638010,7099583349348,
    14111838585881,8405086394310,52932441668562,34319623451420,5251125205351,10461103150894,
    15600688193958,40342961966229,50208619259029,28570878472430,60525590765402,3612893529939,
    15117576260167,41949248595680,53999209120890,57830558823395,9483821441541,17091806900426,
    72662635994248,67916858165031,86353899748047,161135535461246,42530403365343,55013551045563,
    14739111539768,27384392132849,123442472689232,70441608355411,65977626571225,66756474854552,
    112952498863291,109868615474724,167290764440496,26362572032167,196022536607010,
    371873683796212,82142365488912,69633609430634,770319989969008,1378126926504406,
    1075440006610560]]
private def rkmC_w64_s7_6 : List ℤ := pzigCat
  [
   [421147493,1175555278,2437378791,4257500768,6464076445,9231511946,12260901175,15744213802,
    19613301963,23773141486,28324183245,32933796510,37879937613,42946284526,48038339671,
    53145057722,58009542277,62798346770,66895875615,70374325582,73155374315,74672340454,
    75065011981,73853184000,71047272129,66573810484,60225473619,52194967282,42746746239,
    31965833882,20437430901,8593181886,2561290284,12445204963,20150217938,24422517275,
    24629107940,19524594125,8608761710,8683402094,32977707481,63914139788,101436704367,
    144913417436,193415145719,245764919676,300606573135,356628951042,412576072669,467124334302,
    519723272081,569608983500,616990336269,662260039510,706007808095,749695421170,793962998921,
    839859627122,888019420229,937980332794,988770757201,1038075381044,1082715088331,
    1118178486098,1139319629835,1140875434228,1117469334035,1064584942510,979616392071,
    861295126314,711578691877,534863750094,338399811397,131920811664,73596612046,265342271551,
    431309638788,560679363925,644185157166,675869409727,652745714550,575605523075,448588984418,
    278679373119,75906086318,147493937102,377876673097,599576059308,796959302333,953614441120,
    1053846403931,1084094984954,1033696634707,897427965374,676637327373,381013161776,29655830885,
    349768238989,722035578586,1047003367131,1285126668012,1401021767869,1370149367822,
    1183093546315,848825892734,396690497111,125712438063,656395778076,1126166612567,
    1467842565782,1625572428769,1564875335098,1280432110787,799078075830,181232960985,
    486491861553,1101894271272,1561873925075,1781110021046,1708545439531,1340608027482,
    727432386423,31606622679,801790459354,1436568084475,1807225676944,1829989496869,
    1489169507694,844774544889,24652403674,799090846372,1447508411531,1776000674620,
    1709422157369,1263392040666,543115274171,280487489719,1010810513882,1475775726755,
    1570710773086],
   [1285328905291,705703598566,10329664624,675968266701,1125710414704,1259714504525,
    1066326252490,621775344911,63416698168,452454581286,794709921963,892191381530,748408188189,
    432106819082,51321992995,282485555695,487917829034,531732620251,432762061046,247565514841,
    45913593666,113007086732,198152480943,211587424826,179153655131,135663796954,106258254697,
    94788239480,83880249757,45681903724,41261378614,173882074411,317847604524,415092197831,
    405072223154,255264906557,15481368585,331356198798,579517803781,653455994202,503286924691,
    168530120662,223079211110,502672087681,536223519398,295658337793,112801007885,488540375466,
    638071525863,484980752056,125642798339,217749737257,336024660816,180713240859,89482018005,
    216211501964,47734186479,318842233587,600279029798,572624528753,291375883432,57371916587,
    115913757334,380852076591,507246223958,284706224791,83420253753,191590480754,64725851936,
    337034769133,279692990390,25624825617,27142808155,152179995043,172328823696,83853519014,
    162868422529,191800917557,439662457396,72006930747,375433291867,115968914838,412168041322,
    207713584347,401234965827,300614590514,179538149766,130853621432,709170784911,299850250612,
    221006747656,506370610026,1113141515833,126903417778,537018642646,653905752144,1244945273881,
    313197662561,1092181125198,496640494272,1190554347665,530839766739,1009916694430,
    979960630634,1296133751767,674991450225,656387004478,1296017569042,1401985415663,
    690029272871,1697555507886,255182576794,1188879375067,751262107167,1427585640376,
    792318905319,472052907451,540496397238,277182946854,404515227464,1065222627894,111222778321,
    1282836732938,2198824395114,364878399462,368493266829,2140551245984,2768626158592,
    847551308017,1297469340752,2186619996106,2174535541352,1529317720654,416954251779,
    1448145761108,3629102909114,1600706787364,1042154675439,1344892457092,3874219720234],
   [559511590316,1638659898206,1366521571848,2715228342688,165371997919,2274075124168,
    1271753124828,5636201429614,852410210432,1884579687521,3565019179882,1740045030878,
    1255837160412,3110513987056,3970634532852,2690804214306,873302917496,3891974020414,
    2710835976674,2734538892769,1855789339875,983558284025,2165821361815,369819227032,
    145143146467,3783440483699,2710027754579,1868995321651,3394547944477,3001204610113,
    3579125348495,2753240128625,856593863596,210637511440,704823688180,3249070734606,
    180691031738,755076510081,3763874010826,2243911523560,3579470557446,3533526957034,
    2249190108688,2839857953846,3289103000976,216315906309,224695962085,935914014965,
    2583286920571,304995301471,1871142476047,3176701725527,2469329827871,2917740242713,
    2528027260117,37954174344,602092301741,3045560091599,2098099567219,4391186822319,
    5756209176779,1762666373381,1513461112443,1226027706349,2338216618848,1508410507270,
    390446129858,1697675581586,1495891412053,387885329388,907583124865,4629386074681,53433724361,
    1502949505189,2954428166419,8511144011695,9667603718134,15281819738495,6019347825902,
    7143042430915,1828121901665,3568215675663,3169635417420,11805648794251,2363585265916,
    2322096964717,4549659402535,1544387458925,2584501691919,3510225933979,443201628331,
    6837415808517,5338709980576,11604779898979,455824116130,2820936874112,9842208314885,
    7997659093650,2549032428077,2920236401489,6502627169890,6452581160605,5080055753982,
    5890137245823,4935261309988,183111631751,9382163418123,16152725284330,11923691448959,
    1338080815135,5923906605090,6558108656656,18668774474109,14392722723602,2895136419129,
    4190625259499,4142661880196,3854660913585,3928670012060,6085990080090,210281534182,
    15725524545995,1407521454952,3570493316485,7629319732637,6709584197008,1322697438875,
    2155566232295,2423430636874,7622773942940,6272636032448,1033873274031,23598403703487,
    17103662369628,8186187899176,12759922446227,524871237771,17333388298844,3659006987100,
    11334659301122],
   [25424361539684,11343183177197,2967353059834,2627061505769,15911258512393,1352762740318,
    4510941479262,24491733464054,3445212194151,31353360592091,23493837616711,2342162061475,
    13996068899534,1514388587116,5982051142911,257755440119,5841560268915,2919465981029,
    2241847045251,18822158135915,7125488051967,16479099964000,8898287316323,26753643446605,
    21760765015612,49186741943462,12254986949392,9596442519586,42680767196594,3163667315990,
    67772499696327,22850173133533,44224302196182,33866141578184,46003400005445,53816442525288,
    37493755722948,16753848018924,63307942627069,565326595406,139172304585298,133512742520447,
    16012720348873,88456780588258,31070336160827,29914245881728,103308657341577,52769120485262,
    92436419826106,109883237660707,66043456248790,69431462899149,82094828387071,178511294417292,
    36009777732770,4403438030627,336514623983510,270284611078688,66611443443071,349736392051950,
    1285153079815420,1367843150000172]]
private def rkmC_w64_s7_7 : List ℤ := pzigCat
  [
   [231704578,817654755,2042504968,3629090527,5798371848,8311776159,11201359922,14630242465,
    18302611912,22415387859,26648732480,31270217233,36201258504,41020797201,46123586018,
    51117177975,56045283988,60800567067,65066143404,68783763967,71801415080,73766935355,
    74649413614,74032576453,72028995474,68343623297,62812950914,55712711671,46982662982,
    37027566539,25955370584,14484426605,3285898334,7207150218,15709662421,21612942706,
    23785868703,21283988596,13598082655,383992071,20868109174,48010804675,81752209510,
    121704726931,167181812918,217143857857,270322198286,325633498337,381443795428,436801495811,
    490501858220,541896073095,590932339916,637224188303,681659989794,724984890695,768068238156,
    812095769581,857577088070,904924201865,953515154328,1001987057759,1047981016164,
    1087945446613,1117504850634,1131701687449,1125158202398,1093370202395,1032011233362,
    939007805427,814258734874,659603068433,480340673454,283842056321,79900097024,120179940676,
    304469904525,461044022060,579711889045,651934843060,672212526441,638651560990,552432919135,
    418081962274,243476873023,38742450710,183436550274,409594865475,624490011144,812373236725,
    958229109070,1047226305859,1067096173536,1008608848537,867399267372,645950963363,
    354016291172,10229479235,358676474245,719348200046,1033907767453,1264537411024,1378224618243,
    1350913369316,1173538072819,853918360794,418997238311,86710934129,605193869376,1070524363377,
    1418142059724,1593667932985,1561572176698,1313198484657,870404799726,285599626063,
    361957255411,977190585944,1461515350279,1729671833558,1725458102443,1434498305582,
    891946667165,180517621778,579761268162,1250820474095,1702966047188,1840886461105,
    1626101965338,1090867271825,334787668994,490770525788,1213432601723,1677492748890,
    1779620352971,1495738918136,889504405101,99815622678,690059691400,1296965829417],
   [1582633557534,1487613758011,1047662574810,382506872885,335224259393,925775366104,
    1249816553859,1243128118802,930275870401,414251166272,156321168196,630081883101,893985539890,
    902057398983,681032268268,316826012707,76100696483,390517751912,555419769043,551984547740,
    411714944547,198402280188,15036006898,171607835601,244865922472,241016668765,189985852574,
    128362884915,81925118120,56701390079,38017078950,574313323,74110620915,184388823264,
    301036474441,374278558852,353541576759,211419270102,35655131780,321582603749,548940847546,
    623554299827,497051594852,197590721861,169155053211,455582240702,532737004769,354528853686,
    10108429450,398098196125,624130602644,576370648597,282682640438,95622349886,350109634923,
    351538668384,139176985389,97834588081,146920893956,67939649328,413801991221,639276338264,
    576536727785,292040201036,42820301779,45961574120,263259947315,425959573768,308812590161,
    11727941305,210555074604,68001278393,259447317479,397513796902,195888332055,84601763987,
    108922948938,88140283768,174756941945,34231609388,51177051286,119998548734,267445887959,
    50356752622,280960813252,185450300853,223063086423,219172896892,323882686530,594506174031,
    205451118450,53226460118,368075678818,694087898419,307706505166,48224108737,518981384220,
    673610230155,52813620821,271459490704,540105413710,566547668647,616438974821,650304725028,
    826969172594,951944711263,581659699583,562356804472,1163519183782,1110467105557,693843418489,
    563714941800,1163911122100,515545923323,1751814852071,1266270721740,987087702276,
    646194236765,1455062170189,1499459943548,573480998286,1520761030975,85260908449,
    1216963138244,389246277805,83905070844,418828197,403910766847,373428395524,191625513881,
    794251660771,348963329223,2037025900124,1184689590491,751206756087,2374111088164,
    1043270618168,195772637566,369975844944,1345303626366],
   [2191816493370,724912714214,306327520579,929268976278,4703848057702,143172285387,104174727716,
    1235441566682,4185815649406,268534073649,1769083719206,663311840148,1828358349876,
    2493117339772,949668363353,3919688794618,3095007781124,1470268885761,734126329518,
    3366899753050,3306027534566,1058128419042,1851874135774,2820436714900,755615432077,
    826799817846,4608407028132,1688849510902,1207890991206,4177640413286,3186345153810,
    3104097333786,2987399072820,1370273557371,2274117277899,283694586429,778370827593,
    132521523315,1462095575845,3127504965995,806139649745,1805551490143,5361122530801,
    1843683648379,3800552858965,3693997153389,95581981563,1121514886872,607589031160,
    1382221422658,506798542861,902385646538,3462997455648,1596981001288,3210925370984,
    3456466743800,2778050620320,3890161188032,2604820297612,76715406005,110333618193,
    314352828677,1965000816969,315858714397,1554551197487,4556328416869,2169473335977,
    2060931926559,2704792531709,566547246812,563435522423,3952510109073,2351067165697,
    5195643782737,4252717130001,1873963831855,3390759915727,2803272413254,684362138743,
    3499643137360,5346544475021,12772657439682,13717721750795,7035436871664,3076739217319,
    1856946142511,4397418214779,2511186024810,9486182007583,3452784410934,3134401254329,
    7096269769941,35265388041,1057603607199,5503532369353,162599729372,7645372718721,
    3851765032426,9078393191215,207826287748,1190135858438,12265834826035,6298941086592,
    4813079691295,6433023167681,4498692137774,10958011033221,2968991462604,5558782003657,
    1190316368412,354181309574,6416673529291,13099907085730,13743246540821,6435161505828,
    2181187672094,2749016594309,9140600945561,18918298308352,12959909273363,3519706475735,
    10339487035882,5176753412543,661631445946,461845355021,344490468544,1669321733889,
    6225762068086,9686134562861,1301726473359,13244000108860,2729334707367,48089142303,
    1769199306847,7761875652127,6768249355493,2169828358652,5248184107803,7870996225244,
    16128750279941],
   [8303264166508,21102953174486,7574620228009,15301633026305,11216382653996,5235346409360,
    15029235264851,13169945867942,7492254563679,1363406641500,22848785482672,6689792517498,
    14683398214994,1940027483720,3819033880396,9764492879611,19504763208835,7203853357796,
    22860760018250,11382791592432,20194037151519,29507097883951,5814145032449,1823761182070,
    805871544350,4243941897614,7042576440889,4721740169253,9658282271978,12014921777649,
    26070423179933,10178737710092,13937460904660,31857795137879,18613735117519,34476105290590,
    23356743442916,4315796469785,50817973154852,46695172896028,20957777260825,81687693194927,
    45002700915608,5704093497974,6410959628371,3849903094297,50358738155262,87981988824606,
    144396999286771,71120244096694,84354599921032,102801980840625,27041996843790,25698865266021,
    80889626486964,20711771858067,115981546339727,127999914598582,42006273793199,10576140350356,
    55219054779284,163037602320713,32309116433762,139813596932350,82220105536547,136406401901544,
    405259362468430,26894473105840,20042826928839,1007473340115838,1619594837025668]]
private def rkmC_w64_s7_8 : List ℤ := pzigCat
  [
   [421748411,1168646670,2408055731,4191335210,6361113139,9098718912,12101422241,15534297350,
    19314766645,23380803228,27858646343,32409167218,37241594081,42163021700,47172297941,
    52208095020,56906376527,61512513366,65660587505,69238386478,71970351027,73635793750,
    74329607309,73426207480,71125182211,67187396392,61434392913,54260532688,45396051827,
    35338272080,24459660881,13208395018,2240726435,7752670299,15860615504,21030334551,
    22671949162,19586496431,11100295304,3422825732,24397849317,51916074156,86125763043,
    126224610692,171737769389,221647636276,274698893395,329917699344,385491390277,440579825310,
    494219758227,545465504238,594264173113,640505731388,684810503551,727829902302,770471384099,
    813763122678,858370693239,904472334656,951675122107,998414910342,1042800879867,1081167902554,
    1109453854215,1123102594984,1116706586261,1085890498312,1026637526807,936616949168,
    815528278907,665129106974,490179684971,297588212710,96671655757,101701931795,285859183666,
    444096292443,566051635912,643384621081,669841766040,643317580449,564410030162,437234549891,
    269298325508,70228802699,147800024507,371399781628,585780683083,775851127922,927003908947,
    1024822312376,1057124170715,1014785911280,892920191267,692454360172,421227892519,95123450260,
    261852595142,619596371555,942448836432,1194073614977,1340962348026,1356984490087,
    1228861935742,958504097833,566007433404,88808512397,421260115889,902466353382,1291527578669,
    1531506361676,1580428156191,1419667501978,1058523962627,535854348602,81891749270,
    708989948041,1250372888896,1617183441367,1741369227926,1589254421053,1171791996276,
    546331476033,188581586365,907040961084,1477889272791,1789130299052,1771732254957,
    1418016567400,786825291973,2730736915,793589968470,1421929208529,1752941019528,1713250470323,
    1309409169106,629889662545,172277767989,915035760658],
   [1429642037303,1601426384444,1399422257005,882563929934,185708804083,515807766723,
    1051535962780,1299095158639,1214905920242,842062691275,294607998702,275548768964,
    722123799345,943238019264,904714291355,645087781172,257098296037,142727137133,448857740030,
    595373642701,569384263030,407109549963,176712498286,47403306832,207730549561,277814477410,
    265333323707,201176579488,123914841219,62732225490,26437348643,3737596784,27939601484,
    88123751537,178015690652,275366461067,338105333074,320550195985,196083305962,24664150274,
    288068401129,508547892814,599217283447,508430032184,248720963915,95473813335,394127282630,
    521203542389,411526992146,99489924807,285793075029,572572915486,625481968197,417987181532,
    53568468567,282493374873,423341587430,319902876293,77582796896,106092555040,70930363649,
    188418742249,505885630808,658071302579,534859033562,235786861183,124048939,5783824833,
    207778355884,370500139771,291756891574,15942570595,188967399409,101547202418,201104946512,
    400335295709,274921972812,40211452090,198602127935,50193521842,182908124752,204567453643,
    35772367656,41127769606,75219705140,135769977883,51667634633,252459382894,139295847185,
    115623744003,13527721938,445237440952,634147543939,278473399046,6870775572,303766442228,
    697839963033,477813230188,38265585677,156703500918,481819708643,193664717486,271704856740,
    4087605076,430961532475,22327401819,474042648750,305715069658,1042078155763,175692926284,
    671494773682,357090693572,1293064624175,29974760816,1176215774600,105596262739,737659729453,
    779752281091,1720638012098,89929229262,1265991413573,593413876983,1814799351728,244265463198,
    1870798083703,188616738640,1742337936402,1047203790957,677538471341,938612045106,2259743161,
    82127141801,430456037083,82538113790,304747072771,1251145995940,778472539501,751948462355,
    1939543815968,695895081331],
   [1524500894977,649893259454,613366993710,359289560289,1122425258849,722943898394,538501165778,
    2241245759608,1909408892541,1296291472328,2235555485558,2276575953482,2473446057007,
    1883211563472,2999272080480,610589641274,1628992791646,515788288863,3050144479954,
    2576716225698,917846038813,2600851056500,2638027564328,304084796773,209486041618,
    3294500142784,3620820073118,500620546993,331243871434,3145051158758,515247537912,
    1671400279826,4853207167090,1268715936026,195393237339,2273697850262,1373489696228,
    1712748033858,2824312023258,909875938862,2851031878566,4968952496274,3645950764016,
    2522099966546,8731538710,2571885073815,1788767190532,922862765929,2141915010517,1663429954,
    1309324341773,2772606690305,1144203799617,3184063149879,4283798927229,3409987756991,
    4202767675147,131632393999,983890133492,523285033285,452082752156,536914196958,707907392074,
    2433715618526,2406521112988,1571995609924,4190804634138,4063422260658,2448995515248,
    3599476660028,576819546332,1249964324147,1181410489458,517988381899,2461183133707,
    431729838631,4245470359693,3612273121705,758246597003,2863097228225,2063125130192,
    4317658336525,1034059643656,9330675745503,4486979910974,16555156430023,8526625183126,
    6144287613993,811372939517,1872934387482,4918223574934,5747853946619,6327133185320,
    3156700325915,1978075371787,2744855181118,4697244066433,4872104817231,3438290643710,
    6989298045893,1364661614448,8439296156819,1876833534654,2113670097117,8807606934095,
    6412816576518,10227722328555,2563819084163,4289788191394,11944925347383,4513134879824,
    7400404846105,511892557423,1632749718205,5911433762689,4707378654872,15459995627231,
    9436459238374,8991530681081,2251476820167,1231084064746,6348889434980,15777758831299,
    14226950501828,36807797540,13138865572227,10510480002944,223902905795,3428364254663,
    1326598358855,3603370302416,4054443862451,5354684911044,2631848719323,6307844136317,
    11517722624132,3666675520809,7004468569571,1510626572488,3790101215730],
   [263088807831,9661971898692,8912330314813,3875394473364,13716608881093,4301098660169,
    11301116941714,10072006655967,16010571811077,15345492117290,17316322529784,18617633214157,
    9363557229514,209969459181,7355351919845,11801908893950,10161378378427,928997784709,
    1038891556664,12541775490110,14144865211412,6369458683974,16936434870232,5903636977846,
    15357393687317,18416522793115,4910110958928,28519500535094,7056932492776,20445292295105,
    16912429108845,12905897061981,3344121955979,9163367668950,6698247702495,9741829566413,
    15885342223786,507749625385,32958176070603,8765867822,23185056616052,21867499806157,
    36310350588065,26086571476914,9335133414856,2329266881239,19245130819318,103010319208620,
    32260208380163,39372499548047,574324080679,12121545597300,11889655126250,83816879196223,
    154822573900506,532673014194,103228342387227,114493027910642,16383232636091,12812963166090,
    58432957243147,9126235359830,118558068904154,138554341399779,36072087631192,27285224761164,
    49446273545061,119753634286762,84038241876331,117742677727707,145783157517272,26521875686055,
    54427823092903,378964436501038,211325100964102,199846878478549,668727747271408,
    1772231300116020]]
private theorem rkmWC_w64_s7_0 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    594 rkmXsWin_w64_s7_in 586 rkmC_w64_s7_1 395584411 = true := by decide +kernel
private theorem rkmWC_w64_s7_1 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    586 rkmC_w64_s7_1 577 rkmC_w64_s7_2 369663454 = true := by decide +kernel
private theorem rkmWC_w64_s7_2 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    577 rkmC_w64_s7_2 569 rkmC_w64_s7_3 399171697 = true := by decide +kernel
private theorem rkmWC_w64_s7_3 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    569 rkmC_w64_s7_3 560 rkmC_w64_s7_4 355763437 = true := by decide +kernel
private theorem rkmWC_w64_s7_4 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    560 rkmC_w64_s7_4 552 rkmC_w64_s7_5 420025844 = true := by decide +kernel
private theorem rkmWC_w64_s7_5 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    552 rkmC_w64_s7_5 543 rkmC_w64_s7_6 310156381 = true := by decide +kernel
private theorem rkmWC_w64_s7_6 : bWinChk 505 6 100000000 1024 rkmPhb_w64_s7
    543 rkmC_w64_s7_6 534 rkmC_w64_s7_7 398876847 = true := by decide +kernel
private theorem rkmWC_w64_s7_7 : bWinChk 505 5 100000000 1024 rkmPhb_w64_s7
    534 rkmC_w64_s7_7 527 rkmC_w64_s7_8 275285840 = true := by decide +kernel
private theorem rkmWC_w64_s7_8 : bWinChk 505 5 100000000 1024 rkmPhb_w64_s7
    527 rkmC_w64_s7_8 520 rkmXsWin_w64_s7_out 381244683 = true := by decide +kernel
private theorem rkmWinIter_w64_s7 :
    RkmWinIterSound 52 1024 rkmHbWin_w64_s7 594 rkmXsWin_w64_s7_in
      520 rkmXsWin_w64_s7_out 3305772594 :=
  rkmChS 52 3305772594 (rkmChS 47 2924527911 (rkmChS 42 2649242071 (rkmChS 36 2250365224
    (rkmChS 30 1940208843 (rkmChS 24 1520182999 (rkmChS 18 1164419562 (rkmChS 12 765247865
    (bWinChk_sound rkmHhb_w64_s7 rkmWC_w64_s7_0) rkmHhb_w64_s7 rkmWC_w64_s7_1 rfl rfl)
    rkmHhb_w64_s7 rkmWC_w64_s7_2 rfl rfl) rkmHhb_w64_s7 rkmWC_w64_s7_3 rfl rfl) rkmHhb_w64_s7
    rkmWC_w64_s7_4 rfl rfl) rkmHhb_w64_s7 rkmWC_w64_s7_5 rfl rfl) rkmHhb_w64_s7 rkmWC_w64_s7_6
    rfl rfl) rkmHhb_w64_s7 rkmWC_w64_s7_7 rfl rfl) rkmHhb_w64_s7 rkmWC_w64_s7_8 rfl rfl
private def rkmWalksHi_w64_r1024 : List RkmWinSegWalk := [
  ⟨64, rkmHbWin_w64_s0, 0, rkmXsWin_w64_s0_in,
    0, rkmXsWin_w64_s0_out, 665633573⟩,
  ⟨128, rkmHbWin_w64_s1, 0, rkmXsWin_w64_s1_in,
    0, rkmXsWin_w64_s1_out, 1380127811⟩,
  ⟨256, rkmHbWin_w64_s2, 0, rkmXsWin_w64_s2_in,
    58, rkmXsWin_w64_s2_out, 10243149830⟩,
  ⟨512, rkmHbWin_w64_s3, 58, rkmXsWin_w64_s3_in,
    222, rkmXsWin_w64_s3_out, 22153324956⟩,
  ⟨1024, rkmHbWin_w64_s4, 222, rkmXsWin_w64_s4_in,
    580, rkmXsWin_w64_s4_out, 49167225065⟩,
  ⟨1024, rkmHbWin_w64_s5, 580, rkmXsWin_w64_s5_in,
    844, rkmXsWin_w64_s5_out, 47498279950⟩,
  ⟨1024, rkmHbWin_w64_s6a, 844, rkmXsWin_w64_s6a_in,
    594, rkmXsWin_w64_s6b_out, 22664265303⟩,
  ⟨1024, rkmHbWin_w64_s7, 594, rkmXsWin_w64_s7_in,
    520, rkmXsWin_w64_s7_out, 3305772594⟩
  ]
private theorem rkmRowOk_w64 :
    rkmCheckRowFromWinWalks 64 128 1024 [1, 2, 4, 8, 16, 29, 29, 29]
      [4333381, 3920635, 6415160, 6046259, 7528059, 5307913, 4524812, 1017934]
      [12, 21, 66, 117, 254, 271, 231, 52]
      rkmMasksHi_w64_m64_r1024 rkmWalksHi_w64_r1024 rkmRowHi_w64_m64_r1024
      = true := by decide +kernel
private theorem rkmWinChain_w64_s6_full :
    RkmWinIterSound 231 1024 rkmHbWin_w64_s6a 844 rkmXsWin_w64_s6a_in
      594 rkmXsWin_w64_s6b_out 22664265303 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w64_s6a) (hb2 := rkmHbWin_w64_s6a)
    (x1 := rkmXsWin_w64_s6a_out) (x1' := rkmXsWin_w64_s6b_in) rfl rfl
    (muxIntListEq_eq_true.mpr rfl) rfl rkmStatOk_hiw64t12_p.2.2.1
    rkmWinIterSnd_w64_s6a rkmWinIterSnd_w64_s6b
private theorem rkmWinSegWalkSnd_w64_s6 :
    RkmWinSegWalkSound 231 ⟨1024, rkmHbWin_w64_s6a, 844, rkmXsWin_w64_s6a_in,
      594, rkmXsWin_w64_s6b_out, 22664265303⟩ :=
  @rkmSegWalk_mk 231 1024 844 594 22664265303
    rkmHbWin_w64_s6a rkmXsWin_w64_s6a_in rkmXsWin_w64_s6b_out
    (rkmw_buildHbFrom_length 1856 1024 19587930735 1024 0)
    rkmStatOk_hiw64t12_p.2.2.2 rkmWinChain_w64_s6_full
private theorem rkmHbLen_w64_s7 : rkmHbWin_w64_s7.length = 1024 := by
  rw [show rkmHbWin_w64_s7 =
      altBuildHbFrom 1856 1024 19575653846 0 1024 from rfl]
  exact rkmw_buildHbFrom_length 1856 1024 19575653846 1024 0
private theorem rkmInLe_w64_s7 :
    594 + rkmXsWin_w64_s7_in.length ≤ 1024 + 1 := by
  have h3 := @rkmLenApp 87 83 170 rkmXsWin_w64_s7_in_p3 rkmXsWin_w64_s7_in_p4
    (pzig1_len _ 87 rfl) (pzig1_len _ 83 rfl) rfl
  have h2 := @rkmLenApp 87 170 257 rkmXsWin_w64_s7_in_p2 _ (pzig1_len _ 87 rfl) h3 rfl
  have h1 := @rkmLenApp 87 257 344 rkmXsWin_w64_s7_in_p1 _ (pzig1_len _ 87 rfl) h2 rfl
  have h0 : rkmXsWin_w64_s7_in.length = 431 :=
    @rkmLenApp 87 344 431 rkmXsWin_w64_s7_in_p0 _ (pzig1_len _ 87 rfl) h1 rfl
  exact Nat.le_trans (Nat.add_le_add_left (Nat.le_of_eq h0) 594)
    (Nat.le_refl 1025)
private theorem rkmWinSegWalkSnd_w64_s7 :
    RkmWinSegWalkSound 52 ⟨1024, rkmHbWin_w64_s7, 594, rkmXsWin_w64_s7_in,
      520, rkmXsWin_w64_s7_out, 3305772594⟩ :=
  @rkmSegWalk_mkHi 52 1024 594 520 3305772594
    rkmHbWin_w64_s7 rkmXsWin_w64_s7_in rkmXsWin_w64_s7_out
    rkmHbLen_w64_s7 rkmInLe_w64_s7 rkmWinIter_w64_s7
private theorem rkmWalksSndHi_w64_r1024 :
    RkmWinSegWalksSound [12, 21, 66, 117, 254, 271, 231, 52] rkmWalksHi_w64_r1024 :=
  ⟨rkmWinSegWalkSnd_w64_s0, ⟨rkmWinSegWalkSnd_w64_s1,
    ⟨rkmWinSegWalkSnd_w64_s2, ⟨rkmWinSegWalkSnd_w64_s3,
    ⟨rkmWinSegWalkSnd_w64_s4, ⟨rkmWinSegWalkSnd_w64_s5,
    ⟨rkmWinSegWalkSnd_w64_s6, ⟨rkmWinSegWalkSnd_w64_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic `w_hi64_m64_r1024` `r = 1024` hit certificate (`m = 64`). -/
theorem rkmTrajHitHi_w64_m64 :
    RkmAnchorHitSound 64 ⟨1024, [1, 2, 4, 8, 16, 29, 29, 29],
      [4333381, 3920635, 6415160, 6046259, 7528059, 5307913, 4524812, 1017934],
      [12, 21, 66, 117, 254, 271, 231, 52], rkmMasksHi_w64_m64_r1024, rkmRowHi_w64_m64_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 64 128 1024 [1, 2, 4, 8, 16, 29, 29, 29]
    [4333381, 3920635, 6415160, 6046259, 7528059, 5307913, 4524812, 1017934]
    [12, 21, 66, 117, 254, 271, 231, 52] rkmMasksHi_w64_m64_r1024
    rkmWalksHi_w64_r1024 rkmRowHi_w64_m64_r1024 rkmWalksSndHi_w64_r1024 rkmRowOk_w64
/-- Cumulative `w64` part `12` lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T12 :
    @rkmTrajHitHi_w64_m64 = @rkmTrajHitHi_w64_m64 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T10)
    (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T11) rfl)).right.right

end
end QuantumComputation.Specs.DickeSol
