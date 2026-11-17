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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T5

/-
# High-`m` Coupled Walk & Trajectory Part `7` (`FindAllJohnsonRampKickMuxHi128T7`)

Certifies `(m = 128, r = 512)` Part B (`s = 4b..7`) and full trajectory row.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi128T7`). -/
def rkmWordBitsHi128T7 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi128T7 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi128T7`). -/
def rkmUnpackMaskHi128T7 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi128T7 n w ++ rkmUnpackMaskHi128T7 ns ws
/-- Mask segment `4` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s4 : List Bool :=
  rkmUnpackMaskHi128T7 [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 13]
    [1099528409484, 16777216, 17592186044416, 70385940889602, 2101248, 36302405779456, 0,
     79255048290304, 2147488261, 281048795367424, 4110]
/-- Mask segment `5` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s5 : List Bool :=
  rkmUnpackMaskHi128T7 [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 8]
    [141287378452492, 351843720888320, 8796093023244, 549755813888, 20971520, 9071550007808,
     268435456, 1376537052160, 18691697672192, 724389184143368, 205]
/-- Mask segment `6` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s6 : List Bool :=
  rkmUnpackMaskHi128T7 [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 11]
    [8590078021, 35253091565569, 4194308, 0, 128, 131072, 512, 8797267427328, 0, 835628837109760,
     1975]
/-- Prefix-kick masks for `(m = 128, r = 512)`. -/
def rkmMasksHiHiB_m128_r512 : List (List Bool) :=
  [rkmMkHiHiB_m128_r512_s0, rkmMkHiHiB_m128_r512_s1, rkmMkHiHiB_m128_r512_s2,
   rkmMkHiHiB_m128_r512_s3, rkmMkHiHiB_m128_r512_s4, rkmMkHiHiB_m128_r512_s5,
   rkmMkHiHiB_m128_r512_s6, []]
/-- Part `0` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p0 : List ℕ :=
  [32, 11, 1, 3, 21, 19, 97, 0, 11, 2, 52, 85, 949, 2362, 1001, 184, 0, 13, 0, 8, 8, 1, 0, 534, 963,
   509, 897, 1478, 1566, 14, 673, 423, 92, 552, 0, 713, 815, 535, 621, 542, 66, 26, 24, 158, 348,
   777, 2404, 3884, 1440, 177, 2607, 5971, 15520, 26944, 17707, 2148, 157, 0, 2786, 9491, 12796,
   7344, 26, 4310]
/-- Part `1` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p1 : List ℕ :=
  [673, 7087, 10186, 229, 9161, 2401, 1794, 2110, 18, 723, 250, 126, 496, 924, 32, 2977, 104, 1275,
   1151, 862, 1153, 1211, 593, 38, 1998, 8, 0, 26, 0, 20, 495, 0, 180, 15, 1, 47, 0, 2, 642, 16,
   606, 396, 135, 107, 359, 3, 422, 129, 636, 842, 3528, 122, 378, 1011, 3, 565, 74, 249, 6, 86,
   114, 1227, 0, 3326]
/-- Part `2` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p2 : List ℕ :=
  [177, 3899, 128, 6213, 1240, 1616, 24, 3638, 6, 4330, 108, 5407, 6, 5195, 1564, 15408, 12882,
   13224, 57469, 92566, 61669, 35383, 21082, 343, 26729, 54888, 13362, 740, 8303, 13635, 11528,
   2722, 17568, 34376, 834, 12632, 13237, 1759, 118, 14624, 31343, 1833, 58742, 8712, 15000, 11376,
   16, 3794, 9489, 3526, 9133, 21129, 1510, 26851, 1067, 11028, 4504, 113, 2826, 4434, 4, 10276,
   1645, 8842]
/-- Part `3` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p3 : List ℕ :=
  [2744, 3113, 6332, 3609, 2245, 34, 855, 1016, 41, 363, 2762, 79, 4454, 46, 6837, 58, 7571, 777,
   3223, 413, 798, 6, 4, 191, 25, 745, 3647, 6264, 1029, 1971, 9054, 1717, 4658, 127, 3961, 87,
   2987, 2670, 369, 2508, 220, 2096, 935, 3800, 4364, 1208, 6390, 399, 4895, 270, 1143, 829, 9,
   1236, 212, 2071, 1460, 262, 2109, 1314, 2311, 136, 1401, 204]
/-- Part `4` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p4 : List ℕ :=
  [64, 112, 0, 38, 470, 2, 210, 301, 666, 0, 575, 13, 876, 1, 1240, 154, 328, 861, 52, 974, 1347,
   855, 2688, 168, 4153, 27, 4348, 446, 1729, 2540, 362, 4187, 32, 3448, 1018, 1499, 1927, 4, 2658,
   1769, 1434, 7101, 1649, 7678, 400, 3768, 1005, 1182, 2537, 4, 1909, 4458, 1139, 5560, 751, 5186,
   5398, 2074, 8476, 342, 5183, 1284, 2209, 5915]
/-- Part `5` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p5 : List ℕ :=
  [469, 4447, 2788, 6627, 6603, 2122, 10249, 302, 10357, 3385, 5947, 10591, 1290, 6736, 264, 5721,
   4785, 1509, 7279, 219, 4552, 1605, 2846, 2574, 910, 1624, 172, 873, 2197, 321, 2190, 1133, 515,
   1158, 1106, 7643, 760, 1630, 607, 2638, 3841, 99, 1458, 501, 903, 3132, 216, 2068, 698, 1483,
   665, 527, 28, 177, 76, 15, 64, 539, 10, 466, 13, 192, 3, 422]
/-- Part `6` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p6 : List ℕ :=
  [183, 3, 3, 338, 244, 74, 30, 546, 29, 451, 5, 111, 1, 6, 237, 50, 439, 30, 1, 894, 4, 170, 602,
   47, 1876, 49, 3318, 658, 3482, 2386, 2349, 4341, 229, 5381, 476, 6361, 5568, 2680, 6204, 5216,
   20733, 1312, 380, 10100, 55109, 52318, 29977, 36013, 54668, 75606, 59798, 13022, 11479, 82750,
   132559, 110878, 111146, 224880, 550631, 648402, 320989, 215997, 257127, 63016]
/-- Part `7` of `rkmRowHiHiB_m128_r512`. -/
def rkmRowHiHiB_m128_r512_p7 : List ℕ :=
  [85398, 562327, 795925, 939812, 1414062, 2184050, 1992172, 740061, 50822, 203757, 2036115,
   6607715, 12752453, 14422816, 9505127, 3456198, 390908, 339928, 2562113, 4097527, 1979039, 13461,
   2975007, 5969814, 3414791, 13537, 1603994, 697052, 620293, 2622934, 121548, 4629215, 8391322,
   2794017, 8641627, 91202712, 249736586, 181041573, 23979086, 15982916, 115806501, 2862087,
   564593527, 266743711, 138940945, 848938588, 1655327429, 758257764, 665027521, 1894855716,
   479418354, 7703600648, 76287185, 2402787034, 5030372785, 18234695, 3009297138, 2775626677,
   3847540609, 88614258, 11067839699, 10589854009, 4718242764, 940604308025]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 512)`. -/
def rkmRowHiHiB_m128_r512 : List ℕ :=
  rkmRowHiHiB_m128_r512_p0 ++
    (rkmRowHiHiB_m128_r512_p1 ++
    (rkmRowHiHiB_m128_r512_p2 ++
    (rkmRowHiHiB_m128_r512_p3 ++
    (rkmRowHiHiB_m128_r512_p4 ++
    (rkmRowHiHiB_m128_r512_p5 ++
    (rkmRowHiHiB_m128_r512_p6 ++ rkmRowHiHiB_m128_r512_p7))))))
end
public section
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T7`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi128T7 : (0 : ℕ) = 0 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi128T5) rfl).right
/-- Cumulative `m = 128` trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T7`). -/
theorem rkmHiLane_m128_s7 : True :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi128T5) trivial).right
private abbrev fN {α} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private abbrev bZ : ℕ := 100000000000000000
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uCNe (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def u2N : List ℤ → Option (List ℕ)
  | [] => some [] | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs => match u2N xs with | some ns => some (uCN n ns) | none => none
private def uON : List ℕ → List ℤ
  | [] => [] | n :: ns => Int.ofNat n :: uON ns
private theorem u2NS : ∀ (hb : List ℤ) (ns : List ℕ), u2N hb = some ns → hb = uON ns
  | [], _, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [u2N] at h; cases h
  | Int.ofNat n :: xs, _, h => by
    dsimp only [u2N] at h; revert h; cases hxs : u2N xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [uCNe, uON, u2NS xs ms hxs]
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
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
  | [], _, h => by injection h with h'; subst h'; rfl
  | x :: xs, _, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bE1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCNe, bDC, bE1S z x u hx, bES z xs ws hxs]
private def zTd (x : ℤ) (d : ℕ) : ℤ :=
  match x with | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTD : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by dsimp only [muxRawIntTdivNat, zTd]; rw [bNg, ndiv, Nat.add_eq]
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
private theorem bME (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;>
    simp only [muxRawIntMul, bNg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
      Int.negSucc_eq] <;> push_cast <;> ring
private theorem bFA (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a <;> cases b <;>
    simp only [rkmForcedIntAdd, bONF, bNSF, bSE, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFA]; cases a + b <;> cases xs <;> rfl
private abbrev bSV (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem bSVE (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSND]; unfold bSV at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢; have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [bNg]; omega
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
private def bAP : List ℕ → Bool
  | [] => true | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem bAPu {x : ℕ} {xs : List ℕ} (h : bAP (uCN x xs) = true) :
    0 < x ∧ bAP xs = true := by
  rw [uCNe] at h
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => [] | _ :: xs => xs
private theorem bHOe (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [bDN, bZ0]
  | _ :: _ => by unfold bHO; rw [bDC]
private theorem bTNe (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | _ :: _ => by unfold bTN; rw [bDC]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] =>
      uCN (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
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
          dsimp only [bSl, uON] at h ⊢; rw [bDN, rkmUltraSlideLoopAux]; have hp := bAPu h
          have hi := bSlS z d rem b z bR [] [] hp.2; rw [bZ0 z, bDN] at hi
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
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTN vs) (bTN cs)
      dsimp only [mkHbZ] at hrec; rw [← n0m z] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uCNe, uCNe]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
private theorem bSlZ_pfx (z d : ℕ) : ∀ (rem : ℕ) (l t : List ℕ) (p0 q0 : ℕ) (vs cs : List ℕ),
    2 * rem ≤ l.length → bSlZ z d rem p0 q0 (l ++ t) vs cs = bSlZ z d rem p0 q0 l vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, [], _, _, _, _, _, h => by change 2 * (rem + 1) ≤ 0 at h; omega
  | rem + 1, [_], _, _, _, _, _, h => by change 2 * (rem + 1) ≤ 1 at h; omega
  | rem + 1, b :: bz :: l, t, p0, q0, vs, cs, h => by
    change 2 * (rem + 1) ≤ l.length + 2 at h; have hl : 2 * rem ≤ l.length := by omega
    have ha : (b :: bz :: l) ++ t = b :: bz :: (l ++ t) := rfl; rw [ha]; cases vs with
    | nil => cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz [] [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz [] cT hl]
    | cons v vT => cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz vT [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz vT cT hl]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4 | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4P (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) : List ℕ := [b1, z1, b2, z2, b3, z3, b4, z4]
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private theorem hbz4C_app (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) :
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 t = hbz4P b1 z1 b2 z2 b3 z3 b4 z4 ++ t := rfl
private theorem hbz4P_len (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) :
    (hbz4P b1 z1 b2 z2 b3 z3 b4 z4).length = 8 := rfl
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α} (h : HbZ4) (k : HbZ4 → α) : α := match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => k (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r)
private theorem fH4_eq {α} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ => dsimp only [fH4, fL]; rw [rkmb_forceList_eq] | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs => match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t)
  | bs => HbZ4.tail bs
private theorem hbz4L_toH4 : ∀ (xs : List ℕ), hbz4L (toH4 xs) = xs
  | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl | [_, _, _, _, _, _] => rfl | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: bs => by
    dsimp only [toH4]; cases h : toH4 bs with
    | tail _ => have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
private def takeH4 : ℕ → HbZ4 → List ℕ
  | 0, _ => [] | _ + 1, HbZ4.tail l => l
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (takeH4 k r)
private theorem takeH4_spec : ∀ (k : ℕ) (hbz : HbZ4),
    takeH4 k hbz = hbz4L hbz ∨ ∃ t, hbz4L hbz = takeH4 k hbz ++ t ∧ 8 * k ≤ (takeH4 k hbz).length
  | 0, hbz => Or.inr ⟨hbz4L hbz, rfl, Nat.zero_le _⟩ | _ + 1, HbZ4.tail _ => Or.inl rfl
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => by
    dsimp only [takeH4, hbz4L]; rcases takeH4_spec k r with heq | ⟨t, happ, hlen⟩
    · exact Or.inl (congrArg (hbz4C b1 z1 b2 z2 b3 z3 b4 z4) heq)
    · refine Or.inr ⟨t, ?_, ?_⟩
      · rw [hbz4C_app, hbz4C_app, happ, List.append_assoc]
      · rw [hbz4C_app, List.length_append, hbz4P_len]; omega
private theorem bSlZ_takeH4 (z d k : ℕ) (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ)
    (h : rem ≤ 4 * k) :
    bSlZ z d rem p0 q0 (takeH4 k hbz) vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs := by
  rcases takeH4_spec k hbz with heq | ⟨t, happ, hlen⟩
  · rw [heq]
  · rw [happ]; exact (bSlZ_pfx z d rem (takeH4 k hbz) t p0 q0 vs cs (by omega)).symm
private inductive Q4 : Type
  | tail : List ℕ → Q4 | c4 : ℕ → ℕ → ℕ → ℕ → Q4 → Q4
private def q4L : Q4 → List ℕ
  | Q4.tail xs => xs | Q4.c4 x1 x2 x3 x4 r => x1 :: x2 :: x3 :: x4 :: q4L r
private def q4S (x1 x2 x3 x4 : ℕ) (r : Q4) : Q4 :=
  match Nat.add 1 x1 with
  | 0 => r
  | v1 + 1 => match Nat.add 1 x2 with
    | 0 => r
    | v2 + 1 => match Nat.add 1 x3 with
      | 0 => r
      | v3 + 1 => match Nat.add 1 x4 with
        | 0 => r
        | v4 + 1 => match r with
          | Q4.tail xs => Q4.c4 v1 v2 v3 v4 (Q4.tail xs)
          | Q4.c4 y1 y2 y3 y4 yr => Q4.c4 v1 v2 v3 v4 (Q4.c4 y1 y2 y3 y4 yr)
private theorem q4S_eq (x1 x2 x3 x4 : ℕ) (r : Q4) : q4S x1 x2 x3 x4 r = Q4.c4 x1 x2 x3 x4 r := by
  unfold q4S; rw [n1a x1, n1a x2, n1a x3, n1a x4]; cases r <;> rfl
private def toQ4 : List ℕ → Q4
  | x1 :: x2 :: x3 :: x4 :: xs => q4S x1 x2 x3 x4 (toQ4 xs)
  | [] => Q4.tail [] | [x1] => fN x1 fun y1 => Q4.tail [y1]
  | [x1, x2] => fN x1 fun y1 => fN x2 fun y2 => Q4.tail [y1, y2]
  | [x1, x2, x3] => fN x1 fun y1 => fN x2 fun y2 => fN x3 fun y3 => Q4.tail [y1, y2, y3]
private theorem q4L_toQ4 : ∀ (xs : List ℕ), q4L (toQ4 xs) = xs
  | [] => rfl | [_] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq]; rfl
  | [_, _] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | [_, _, _] => by
    dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | x1 :: x2 :: x3 :: x4 :: xs => by
    dsimp only [toQ4]; rw [q4S_eq]; dsimp only [q4L]; rw [q4L_toQ4 xs]
private def q4Hd (z : ℕ) : Q4 → ℕ
  | Q4.c4 x _ _ _ _ => x | Q4.tail xs => bHO z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHO z (q4L w) := by cases w <;> rfl
private def q4AP : Q4 → Bool
  | Q4.tail xs => bAP xs
  | Q4.c4 x1 x2 x3 x4 r =>
    match Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with | 0 => q4AP r | _ + 1 => false
private theorem pos1_false {x : ℕ} (h : (1 - x) = 0) : Nat.ble x 0 = false := by
  cases x with | zero => cases h | succ _ => rfl
private theorem q4AP_pos : ∀ (w : Q4), q4AP w = true → bAP (q4L w) = true
  | Q4.tail _, h => h
  | Q4.c4 x1 x2 x3 x4 r, h => by
    dsimp only [q4AP] at h; revert h
    cases hs : Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | succ _ => intro h; dsimp only at h; cases h
    | zero =>
      intro h; dsimp only at h; simp only [Nat.add_eq, Nat.sub_eq] at hs
      have h1 : 1 - x1 = 0 := by omega
      have h2 : 1 - x2 = 0 := by omega
      have h3 : 1 - x3 = 0 := by omega
      have h4 : 1 - x4 = 0 := by omega
      dsimp only [q4L, bAP]; rw [pos1_false h1, pos1_false h2, pos1_false h3, pos1_false h4]
      exact q4AP_pos r h
private def bChkV (out : Q4) : Option Q4 := match out with
  | Q4.tail xs => cond (bAP xs) (some (Q4.tail xs)) none
  | Q4.c4 x1 x2 x3 x4 r => cond (q4AP (Q4.c4 x1 x2 x3 x4 r)) (some (Q4.c4 x1 x2 x3 x4 r)) none
private theorem bChkV_eq (out : Q4) : bChkV out = cond (q4AP out) (some out) none := by
  cases out <;> rfl
private def bSlQ4 (z d rT : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Q4 → Q4
  | 0, p0, q0, hbz, vs, cs => toQ4 (bSlZ z d rT p0 q0 (takeH4 1 hbz) (q4L vs) (q4L cs))
  | q + 1, p0, q0, hbz, vs, cs => match hbz with
    | HbZ4.tail l =>
      toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0 l (q4L vs) (q4L cs))
    | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR => match vs with
      | Q4.tail vxs =>
        toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
          (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) vxs (q4L cs))
      | Q4.c4 v1 v2 v3 v4 vR => match cs with
        | Q4.tail cxs =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR))
            (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs)
        | Q4.c4 c1 c2 c3 c4 cR => match Nat.add 1 (Nat.mul b4 c4) with
          | 0 => Q4.tail []
          | bc4 + 1 =>
            q4S (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
              (bSlQ4 z d rT q bc4 z4 bR vR cR)
private theorem bSlQ4_eq (z d rT : ℕ) (hr : rT ≤ 4) : ∀ (q p0 q0 : ℕ) (hbz : HbZ4) (vs cs : Q4),
    q4L (bSlQ4 z d rT q p0 q0 hbz vs cs) = bSlZ z d (4 * q + rT) p0 q0 (hbz4L hbz) (q4L vs) (q4L cs)
  | 0, p0, q0, hbz, vs, cs => by
    dsimp only [bSlQ4]; rw [q4L_toQ4]; have h0 : 4 * 0 + rT = rT := by omega
    rw [h0]; exact bSlZ_takeH4 z d 1 hbz rT p0 q0 (q4L vs) (q4L cs) hr
  | q + 1, p0, q0, hbz, vs, cs => by
    have hrem : Nat.add (Nat.mul 4 (Nat.add q 1)) rT = 4 * (q + 1) + rT := by
      simp only [Nat.add_eq, Nat.mul_eq]
    have hq2 : Nat.add q 2 = q + 2 := by rw [Nat.add_eq]
    have hle : 4 * (q + 1) + rT ≤ 4 * (q + 2) := by omega
    cases hbz with
    | tail l => dsimp only [bSlQ4, hbz4L]; rw [q4L_toQ4, hrem]
    | c4 b1 z1 b2 z2 b3 z3 b4 z4 bR => cases vs with
      | tail vxs =>
        dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
        exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
          (4 * (q + 1) + rT) p0 q0 vxs (q4L cs) hle
      | c4 v1 v2 v3 v4 vR => cases cs with
        | tail cxs =>
          dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
          exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
            (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs hle
        | c4 c1 c2 c3 c4 cR =>
          dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq]
          have h4 : 4 * (q + 1) + rT = ((((4 * q + rT) + 1) + 1) + 1) + 1 := by omega
          rw [h4]; dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO, uCNe]
          rw [uCNe, uCNe, uCNe, uCNe, bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bSS (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs = some out) :
    bDec z (q4L out) =
      rkmUltraHornerStage dg mL cL (uON bns) (bDec z (q4L vs)) (bDec z (q4L cs)) := by
  unfold bStg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, bChkV_eq] at h
  have hr : Nat.mod (rkmNextLen mL cL) 4 ≤ 4 := by rw [nmod]; omega
  have hqr : 4 * Nat.div (rkmNextLen mL cL) 4 + Nat.mod (rkmNextLen mL cL) 4 =
      rkmNextLen mL cL := by rw [ndiv, nmod]; omega
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns (q4L vs) (q4L cs)
  rw [← n0m z] at hsl
  have heq : q4L (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4 (mkHbZ z bns)) vs cs) =
      bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns (q4L vs) (q4L cs) := by
    rw [bSlQ4_eq _ _ _ hr, hqr, hbz4L_toH4, hsl]
  revert h
  cases hv : q4AP (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4 (mkHbZ z bns)) vs cs) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'
    have hp := q4AP_pos _ hv; rw [heq] at hp; rw [← h', heq]
    unfold rkmUltraHornerStage; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSlS z _ _ 0 z bns (q4L vs) (q4L cs) hp
private def bBd (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => match bStg z dg mL cL h4 vs cs with
    | none => none | some out => k nL out
private theorem bBS (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBd z dg mL cL (toH4 (mkHbZ z bns)) vs cs kB = some out)
    (hk : ∀ mid, kB (rkmNextLen mL cL) mid = some out →
      bDec z (q4L out) = kU (rkmNextLen mL cL) (bDec z (q4L mid))) :
    bDec z (q4L out) = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uON bns) (bDec z (q4L vs)) (bDec z (q4L cs))) (kU nL)) := by
  unfold bBd at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bSS bns hs]; exact hk mid h
private def bSp (z m c : ℕ) (h4 : HbZ4) (vs : Q4) : Option Q4 :=
  bBd z 16 m c h4 vs vs fun l x => bBd z 15 m l h4 vs x fun l x => bBd z 14 m l h4 vs x fun l x =>
  bBd z 13 m l h4 vs x fun l x => bBd z 12 m l h4 vs x fun l x => bBd z 11 m l h4 vs x fun l x =>
  bBd z 10 m l h4 vs x fun l x => bBd z 9 m l h4 vs x fun l x => bBd z 8 m l h4 vs x fun l x =>
  bBd z 7 m l h4 vs x fun l x => bBd z 6 m l h4 vs x fun l x => bBd z 5 m l h4 vs x fun l x =>
  bBd z 4 m l h4 vs x fun l x => bBd z 3 m l h4 vs x fun l x => bBd z 2 m l h4 vs x fun l x =>
  bStg z 1 m l h4 vs x
private theorem bSpS (bns : List ℕ) {z mL cL : ℕ} {vs out : Q4}
    (h : bSp z mL cL (toH4 (mkHbZ z bns)) vs = some out) :
    bDec z (q4L out) = rkmUltraHornerT16Step mL cL (uON bns) (bDec z (q4L vs)) := by
  unfold bSp at h; unfold rkmUltraHornerT16Step
  refine bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => ?_
  refine bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => ?_
  refine bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => ?_
  refine bBS bns h fun _ h => bBS bns h fun _ h => bBS bns h fun _ h => bSS bns h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Option Q4
  | 0, _, _, _, vs => some vs
  | k + 1, mL, cL, h4, vs => match bSp z mL cL h4 vs with
    | none => none | some vN => fN (rkmNextLen16 mL cL) fun nL => bIt z k mL nL h4 vN
private theorem bItS (bns : List ℕ) (z : ℕ) : ∀ (k mL cL : ℕ) (vs out : Q4),
    bIt z k mL cL (toH4 (mkHbZ z bns)) vs = some out →
      bDec z (q4L out) = muxUltraIterFullT16Rkm k mL cL (uON bns) (bDec z (q4L vs))
  | 0, _, _, _, _, h => by injection h with h'; rw [← h']; rfl
  | k + 1, mL, cL, vs, out, h => by
    unfold bIt at h; revert h; cases hs : bSp z mL cL (toH4 (mkHbZ z bns)) vs with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpS bns hs]
      exact bItS bns z k mL (rkmNextLen16 mL cL) vN out h
private def fQ4 {α} (v : Q4) (k : Q4 → α) : α := match v with
  | Q4.tail xs => k (Q4.tail xs) | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4_eq {α} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by cases v <;> rfl
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  match u2N hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns => match bEnc bZ v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => fH4 (toH4 (mkHbZ bZ bns)) fun h4 => fQ4 (toQ4 vns) fun vs0 =>
      match bIt bZ k mL cL h4 vs0 with
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec bZ (q4L out)
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; cases hh : u2N hb with
  | none => rfl
  | some bns => dsimp only; cases hv : bEnc bZ v with
    | none => rfl
    | some vns =>
      dsimp only; rw [fH4_eq, fQ4_eq]
      cases hi : bIt bZ k mL cL (toH4 (mkHbZ bZ bns)) (toQ4 vns) with
      | none => rfl
      | some out =>
        dsimp only; rw [bItS bns bZ k mL cL (toQ4 vns) out hi,
          q4L_toQ4, ← u2NS hb bns hh, bES bZ v vns hv]
private def bSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem bSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; simp only [rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem pChFull (k1 k2 mL : ℕ) {hb v0 v1 v2 : List ℤ}
    (h1 : muxFastIterFullT16 k1 mL hb v0 = v1) (h2 : bSlideChk k2 mL hb v1 v2 = true) :
    muxFastIterFullT16 (k1 + k2) mL hb v0 = v2 :=
  (muxFastIterFullT16_add k1 k2 mL hb v0).trans
    ((congrArg (muxFastIterFullT16 k2 mL hb) h1).trans (bSlideChk_sound h2))
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def rkmZZ (w : ℕ) : ℤ := match Nat.ble (Nat.mod w 2) 0 with
  | true => Int.ofNat (Nat.div w 2) | false => Int.negSucc (Nat.div w 2)
private def rkmMapZZ : List ℕ → List ℤ
  | [] => [] | w :: ws => rkmZZ w :: rkmMapZZ ws
private def rkmNatZ : List ℕ → List ℤ
  | [] => [] | w :: ws => Int.ofNat w :: rkmNatZ ws
private def pzeros : ℕ → List ℤ
  | 0 => [] | k + 1 => Int.ofNat 0 :: pzeros k
private def pZZZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z | xs :: xss => rkmMapZZ xs ++ pZZZ z xss
private def pNZCat : List (List ℕ) → List ℤ
  | [] => [] | xs :: xss => rkmNatZ xs ++ pNZCat xss
private theorem bDm {a b : ℕ} (h : muxNatListEq [a] [b] = true) : a = b :=
  (List.cons.inj (muxNatListEq_eq_true.mp h)).1
private def phbVec7_4 : List ℤ := pNZCat
  [
   [76614018292616,108182302690187,132292045183811,152522484831973,170262317810632,
    186224884076723,200834600849619,214368425807171,227019028878486,238926905428775,
    250198278865481,260915798814583,271145291087388,280940207055474,290344664192855,
    299395587648211,308124257960851,316557454685671,324718317919301,332627008433497,
    340301221167351,347756590056525,355007011069303,362064902799939,368941418779371,
    375646622016308,382189629677728,388578733931012,394821503584387,400924870132185,
    406895201036744,412738362490078,418459773446589,424064452368219,429557057850103,
    434941924079633,440223091911151,445404336202157,450489189947315,455480965657856,
    460382774361773,465197542541193,469928027274670,474576829812018,479146407775884,
    483639086156482,488057067242488,492402439611550,496677186287193,500883192154914,
    505022250718214,509096070265164,513106279507284,517054432745044,520942014607764,
    524770444410107,528541080162499,532255222268568,535914116939020,539518959348166,
    543070896556466,546571030220009,550020419105662,553420081428700],
   [556770997028032,560074109392653,563330327551597,566540527838495,569705555540803,
    572826226442780,575903328270525,578937622046556,581929843360792,584880703564190,
    587790890890699,590661071512778,593491890535204,596283972931564,599037924427416,
    601754332333807,604433766334521,607076779230170,609683907642000,612255672678045,
    614792580564082,617295123241629,619763778935082,622199012689925,624601276883784,
    626971011712016,629308645649342,631614595888979,633889268760595,636133060128326,
    638346355770000,640529531738673,642682954707440,644806982298494,646901963397286,
    648968238452616,651006139763412,653015991752922,654998111230984,656952807645007,
    658880383320250,660781133689961,662655347515882,664503307099624,666325288485364,
    668121561654300,669892390711265,671638034063890,673358744594683,675054769826346,
    676726352080670,678373728631309,679997131850707,681596789351465,683172924122395,
    684725754659503,686255495092142,687762355304528,689246541052856,690708254078180,
    692147692215269,693565049497591,694960516258611,696334279229541],
   [697686521633713,699017423277700,700327160639331,701615906952724,702883832290455,
    704131103642996,705357884995511,706564337402130,707750619057803,708916885367813,
    710063289015063,711189980025207,712297105829711,713384811326930,714453238941269,
    715502528680507,716532818191347,717544242813263,718536935630702,719511027523708,
    720466647217018,721403921327694,722322974411332,723223929006914,724106905680337,
    724972023066670,725819397911195,726649145109251,727461377744944,728256207128753,
    729033742834064,729794092732683,730537363029345,731263658295268,731973081500769,
    732665734046991,733341715796747,734001125104533,734644058845718,735270612444951,
    735880879903803,736474953827664,737052925451935,737614884667511,738160920045607,
    738691118861919,739205567120164,739704349574998,740187549754345,740655249981149,
    741107531394569,741544473970620,741966156542306,742372656819222,742764051406673,
    743140415824306,743501824524269,743848350908923,744180067348105,744497045195964,
    744799354807375,745087065553951,745360245839658,745618963116040],
   [745863283897079,746093273773680,746308997427811,746510518646288,746697900334231,
    746871204528190,747030492408947,747175824314017,747307259749833,747424857403645,
    747528675155129,747618770087709,747695198499612,747758015914650,747807277092744,
    747843036040191,747865346019681,747874259560075,747869828465941,747852103826860,
    747821136026502,747776974751486,747719669000017,747649267090316,747565816668836,
    747469364718282,747359957565427,747237640888737,747102459725800,746954458480575,
    746793680930455,746620170233145,746433968933377,746235118969439,746023661679544,
    745799637808025,745563087511380,745314050364141,745052565364594,744778670940350,
    744492404953751,744193804707139,743882906947968,743559747873783,743224363137044,
    742876787849822,742517056588346,742145203397426,741761261794732,741365264774944,
    740957244813777,740537233871870,740105263398551,739661364335481,739205567120164,
    738737901689348,738258397482292,737767083443923,737263988027869,736749139199377,
    736222564438116,735684290740858,735134344624056,734572752126299],
   [733999538810657,733414729766920,732818349613716,732210422500529,731590972109597,
    730960021657712,730317593897904,729663711121015,728998395157172,728321667377150,
    727633548693624,726934059562316,726223219983042,725501049500638,724767567205793,
    724022791735765,723266741274999,722499433555629,721720885857880,720931115010355,
    720130137390226,719317968923300,718494625083994,717660120895187,716814470927966,
    715957689301270,715089789681409,714210785281479,713320688860668,712419512723436,
    711507268718594,710583968238259,709649622216693,708704241129027,707747834989867,
    706780413351771,705801985303617,704812559468833,703812144003517,702800746594419,
    701778374456801,700745034332163,699700732485839,698645474704463,697579266293288,
    696502112073379,695414016378660,694314983052815,693205015446050,692084116411702,
    690952288302703,689809532967883,688655851748124,687491245472351,686315714453357,
    685129258483474,683931876830060,682723568230823,681504330888967,680274162468152,
    679033060087280,677781020315082,676518039164519,675244112086982],
   [673959233966293,672663399112498,671356601255444,670038833538151,668710088509943,
    667370358119373,666019633706891,664657905997294,663285165091910,661901400460546,
    660506600933164,659100754691298,657683849259191,656255871494657,654816807579646,
    653366643010520,651905362588011,650432950406878,648949389845225,647454663553500,
    645948753443133,644431640674836,642903305646526,641363727980882,639812886512499,
    638250759274662,636677323485686,635092555534851,633496430967878,631888924471965,
    630270009860350,628639660056390,626997847077135,625344542016400,623679715027284,
    622003335304149,620315371064029,618615789527435,616904556898566,615181638344874,
    613446997975976,611700598821895,609942402810585,608172370744743,606390462277847,
    604596635889430,602790848859530,600973057242299,599143215838742,597301278168549,
    595447196440976,593580921524759,591702402917008,589811588711039,587908425563118,
    585992858658055,584064831673618,582124286743704,580171164420232,578205403633694,
    576226941652312,574235714039744,572231654611280,570214695388454],
   [568184766552020,566141796393205,564085711263182,562016435520663,559933891477554,
    557837999342562,555728677162679,553605840762442,551469403680862,549319277105921,
    547155369806524,544977588061784,542785835587512,540580013459784,538360020035447,
    536125750869400,533877098628513,531613953002003,529336200608095,527043724896786,
    524736406048500,522414120868447,520076742676436,517724141191929,515356182414070,
    512972728496426,510573637616160,508158763837326,505727956967970,503281062410695,
    500817921006315,498338368870219,495842237221026,493329352201083,490799534688326,
    488252600099018,485688358180785,483106612795404,480507161690691,477889796260830,
    475254301294428,472600454709516,469928027274670,467236782315354,464526475404529,
    461796854036485,459047657282784,456278615429096,453489449591632,450679871311760,
    447849582127266,444998273118620,442125624428433,439231304752162,436314970797935,
    433376266713195,430414823475636,427430258245691,424422173677575,421390157185602,
    418333780162194,415252597143637,412146144919283,409013941579441],
   [405855485496736,402670254235193,399457703380680,396217265285694,392948347720716,
    389650332423510,386322573536798,382964395923634,379575093348622,376153926511693,
    372700120919603,369212864578507,365691305488922,362134548922010,358541654453451,
    354911632728049,351243441924611,347535983886529,343788099878640,339998565925353,
    336166087678482,332289294755536,328366734480224,324396864946267,320378047313011,
    316308537226370,312186475240706,308009876095839,303776616677528,299484422458524,
    295130852179285,290713280480951,286228878146103,281674589532139,277047106694237,
    272342839584795,267557881577367,262687969386706,257728436230508,252674156786541,
    247519482118269,242258162241086,236883253334786,231387005711023,225760727422722,
    219994616715336,214077554156134,207996841911979,201737872768268,195283704272233,
    188614502493048,181706803031688,174532510082965,167057510289052,159239703095777,
    151026116084965,142348525130037,133116506912851,123205803139876,112437431135591,
    100536556343706,87040314913658,71045791335652,50220912674478]]
private def pvo7_4 : List ℤ := pZZZ 0
  [
   [89726253490,63912189372,19818878581,20418719355,114688482460,46063280613,109065281253,
    58412651124,44028673668,40536834547,25230554331,43310270321,16566646989,96620007456,
    137250225038,171795830504,288543934708,329317842888,212764246102,45736003656,70492122599,
    21488688283,93681804350,97130539944,11507866073,52096577605,103073722607,91742608549,
    49130935656,148466824028,27216936272,100142482491,40015731497,32307026132,52973957566,
    25369679130,58146852223,85118055437,33312505232,143128936816,34011116352,115524657635,
    59930077633,91885267806,113872995660,35372515757,102212884379,49478985652,128686249536,
    30846576121,147275612229,9916338335,125202242044,18095575098,106452846517,42915190327,
    72407542686,70591753200,47622323499,80518682917,58789516810,86441850434,93590047015,
    123561874403],
   [80529684266,115423115422,81957054947,91658831517,76825534176,44618390810,69339127133,
    7621002801,48522542214,92574988,578774319,32038030108,34572234038,65905945422,96234613072,
    76871041286,139259921152,299773915830,335714859166,285139844572,370533159378,430476608320,
    297605349318,195402968490,149527436352,50673571193,265159489067,281795427057,233577222191,
    201559636005,47796246741,169079079656,245086244718,223595093216,178385530578,14877546651,
    262541217557,273011036265,105344041297,16857355552,123999477420,232276036376,185963399988,
    30290283455,212857779213,203889610693,66551737589,67393277026,180253983818,217923289358,
    43003949546,235069302869,270434073499,7132681453,204665102426,167268067872,54193259176,
    47965692609,193023241821,187563216301,87878867620,267923754524,99084298412,128900456775],
   [151779963331,68559514161,15442016106,129941443780,179815860732,13371800505,273758505291,
    172735027353,202899861206,273382593982,40603958669,213713279045,82756524347,33176962580,
    82953276492,167812338582,37492377188,288363129901,196734895479,283183533854,291091379722,
    185295416699,274660977245,53961498356,154325100126,44038547260,15513185480,71894619795,
    171416683601,29293300806,263797860612,52981408358,269989190291,130118699719,199163512236,
    162726330636,94617305107,144350452899,1834675370,89531600016,50840672982,14953206483,
    55874848539,66302885935,22810003026,140287383192,26790388702,194210735667,75521950611,
    208868162912,102019311978,180290044957,94209968301,119401462974,51339484370,47224341235,
    12259666834,20729733537,76554001111,75621521060,120956046430,113518546859,132676309117,
    129311062254],
   [109839964502,116594125721,58315426457,77950077654,6714732809,24864404533,66524852470,
    28541315467,108758116517,67379758472,122561473592,92423469655,113357416013,103104101666,
    88342655738,97865730709,51092845929,79528918582,7938334982,53165439661,31119345284,
    22162934116,62846786123,2550487160,82010366648,17862961409,92595541221,23697419698,
    101350823882,20472531289,105238669407,17012324766,100448028110,18125771137,78463480417,
    29521536882,38964852164,52235068385,7369436872,77314586548,50528130117,93846112959,
    85720348882,94528804664,112507703881,76951080453,131423225578,44230736396,138489085485,
    2491525685,124237892418,46600404823,90527294395,90728584894,38163411578,125704457077,
    13990713826,135597531974,59389834311,120320655253,90418134600,85038425130,106870366989,
    43024459627],
   [108111958376,6890997702,88926097701,23509602260,51855403136,51038366423,6841889705,
    74061586932,32442965023,82388054923,61841184728,75399588360,73381176273,50195270509,
    71527501968,16778969070,58367103495,17539418070,39974915050,49215557927,26181582893,
    73445300296,20109701124,88392100187,18254060927,94880347734,13492916526,96640177585,
    3014070941,94763138454,12558477383,88369063187,31239469254,77197424402,50685252239,
    61174535149,71082504564,42517883136,91062797887,20712927349,110323930402,3431100061,
    124763612561,28977645554,126610242804,57275157285,113680561423,82601147292,83208289422,
    100908660913,40517235915,102598894152,15867842573,93991778525,75510116956,83483302214,
    119258515971,68227138105,136717217838,41373551098,127507042111,5937871030,107769453976,
    63422954377],
   [84787871791,114430330422,52747987572,151776184783,9060225925,172095269240,43085730361,
    174423389043,92762319784,152342057212,137139472355,109218458067,173223976432,53335769286,
    199679087599,2080667462,209151682582,55733854319,206513595815,100148409460,190960019766,
    135321589173,167658632087,154368335316,132713134482,156519370049,81404641891,148837052100,
    17257945516,140447549347,45171135434,133679121838,86961108849,116736310869,106486344706,
    84680897102,109669996613,39094940159,105976307652,14921579517,110165967315,58663613828,
    120849626014,77754540103,119238499159,84194436800,101087532920,94525085065,81573904249,
    101331587098,60132571774,99940777679,28462216795,101541048938,5385275289,114018546351,
    17495013624,115008639544,18098598565,106626519979,8377979316,88783527252,8405973466,
    58478050783],
   [18861823079,22291001306,8638330940,4323576209,10015510906,18873584362,4542573960,18241996203,
    30357155889,14222697235,26077581580,38335877144,9022256181,48363515231,15472834117,
    30595487956,22144093192,2570197273,10993423949,23943038369,10564970753,43547302326,
    36435226250,48030027097,48535737581,48368164362,37317313686,78578621623,48713645481,
    106732091182,77012070676,131741493937,147627095725,84598846228,163756806184,46583353859,
    151412761099,51471055130,177061373894,33385991009,201977891293,9509113873,195847950692,
    54369465396,139989080485,37358273017,107791262810,9555556183,126686613927,39871619114,
    194686415812,16303305252,198849158513,59846553985,177492608542,48490692924,249694874899,
    153314970505,247485109396,285210664354,137845772857,326595159265,28846538990,301697258796],
   [7025825174,355840597075,164937569067,269133049538,257496209014,104870874783,145603159303,
    211121403712,302622700298,133324644435,440148986887,96427117933,325427023240,8582944746,
    670860295525,595208322703,224352375020,465801512260,374796806111,968924928955,259042862449,
    593312952086,22099648843,1224847485535,751161884819,1009918398256,934127696860,1635623521507,
    2677452531731,482083744254,3489641209146,521364735196,5267609004319,4088423149667,
    4918659028478,8428008014620,2680917465293,15228390872997,7735239080339,15901652843612,
    22878449945462,5525476896551,38187865176759,24639611067799,34006802389108,68033954119490,
    17054372589518,80998939241349,109453440384627,2203876125271,157319139984258,194758875086752,
    20462579229602,255038572626541,391781716309883,218303925258699,224468726483368,
    715240814396920,1016960279942278,1027531567550600,809692471875348,510094970613866,
    254937785314846,96771639928760],
   [24415258682414]]
private def pvm_s4_1 : List ℤ := pZZZ 45
  [
   [1904361278,9857811339,27113020276,69354535613,142006048712,241422537507,330875089226,
    360950042105,286847804316,106012214221,119067102825,267215823066,245302175753,60262035534,
    160342480860,245938378771,120368554144,112078377344,240666268221,138793501058,95957285856,
    234370074709,131691943232,106837906664,222897112203,83966049444,155617917342,222061066889,
    43179707540,165569210790,153914116619,60079337895,207462504182,94565291047,139584396853,
    198454729446,11503802771,182669969403,129369608972,91587533718,178556680701,13262415182,
    170986012712,117194167597,105484013593,173519972110,14009456806,200045418935,125585590398,
    99979406530,136106613649,85049414209,263964943268,159971258711,40312211629,8792961142,
    234112336328,340876449921,166154323904,15149680502,69840698192,263058116695,232796919946,
    2811376492],
   [101315591255,69069896599,214086934458,79572354865,154881085689,152898491708,36382782658,
    58871440533,155439493579,271677664648,86075129423,121031240087,35479676334,164985793074,
    102788699009,169696672383,248235351436,46833405845,77461435025,57824179915,162167005236,
    9549338442,233859536991,172307510794,53448180362,73281197845,109801291249,116213675956,
    150481231336,291133160585,72156776654,164540369172,77206837823,94530042419,432505129,
    192306804588,97622047361,180255259365,223586869408,23189341079,40483473949,110649392477,
    115964815164,116755015388,205844620275,28194786473,200539617124,41294041635,133001439657,
    13913103400,130870598462,26765569848,241410310819,87520542146,261882770000,288583485303,
    10787561390,55172584100,128335871070,98925898263,162006162257,170841880226,150070057282,
    305374717441],
   [58535487290,174051447504,56507427679,73779926835,79773698337,167546777362,77348530914,
    237249957263,6587541153,263330935036,166810197949,11347067189,26741967129,65849808754,
    93065913116,182653815781,5117461071,155874752278,16817819605,135392260559,60102768096,
    34469930550,32969601492,90336406529,1844056511,44801117916,73638646546,117800698217,
    6668328681,74402312376,1474855299,14935678797,97528975403,79134681074,64392384600,51839541927,
    36483396671,15394894647,51167898874,33990410762,54408554819,50096901479,85615469782,
    19892559574,79096156297,19959241966,6896357116,1790783195,26376961314,562944615,35311060385,
    5968901723,108876475976,68610046027,129999061869,164781187116,1970807955,118123196427,
    130391865458,65102086419,112973944457,178956585132,10090366768,148181792201],
   [40812947122,71423094906,51936163139,45735718799,74024500206,3507161652,121488653617,
    90233982938,121965636362,174054306857,30476064189,200732607058,63799425343,131554521147,
    102589464840,6919299548,133539760069,67927005596,124138271902,89874503257,106203759209,
    95122094904,29283376750,90786355103,30672762298,78299613408,109765436627,34884465469,
    113318352850,20663396357,91760317831,48447343472,35982562872,59008490171,46374627078,
    77478383116,35995995099,69591423705,6568326634,47698151804,4067218247,14631528269,45972698714,
    38559534334,81804585533,44013198871,124695199946,12418482216,139319250573,39234058138,
    120065407886,125469423557,123518468651,196484471868,128767925964,185308103639,52293334517,
    181650752834,12737121469,194538600753,15541574672,171580011032,13978837261,130802744983],
   [4652634145,46154554188,35164071053,59418351327,4500319376,61461826462,27831628160,34180987749,
    11279562939,29814514816,28422858597,101121442687,15004314285,121790987666,42907772772,
    98504222545,16096736146,158792781422,4293948867,193959199903,50444431833,155550246762,
    18649865920,218252745675,86723670873,212701160742,179642107180,65095802847,80088450519,
    95338985182,123203431186,23881328791,96955828855,26820271375,7721130417,119001444593,
    193237251593,144091244573,92209135305,128242100389,202842966307,214092799291,124144333311,
    51197530009,137933089725,291497578337,273957704213,69653577057,54770336858,87767166821,
    311361526541,281849393833,26517775181,62231809616,164295457849,362775486143,245944146067,
    24543926915,57687283723,301773710659,377896552015,139488034897,78782597632,69682216079],
   [409872186185,472655492125,168712676493,98554285736,4589955020,294246944133,417528796925,
    253179362779,62519702087,110225675779,310219110753,358598614333,165483626273,25140795746,
    30050302077,277666191317,465148316277,431214529205,243061492127,92096230065,89673449955,
    172458823325,214000295523,190706178725,181939914347,236046665179,315786785825,371391878439,
    397055405617,404961395487,390411548253,334460293319,223723730669,76870131299,40860032718,
    62726865846,4348937958,26136199737,66628616332,260966944572,434463709494,470529237270,
    345731027742,145754262850,17738081034,76461599872,311562203048,578371061384,700700323754,
    600286825042,341720584344,76147677750,48717213615,43381133970,323038173914,663518864544,
    903629928820,938157506482,770557775370,490967331418,211381344424,15258299182,57633303543,
    6473661151],
   [145268098532,379498126110,718174524192,1226971556516,1961233222364,2873423259506,
    3736800485742,4133224663238,3522144391128,1386935077950,2552939029631,8092397803501,
    14315438382825,19479961654629,21085321943801,16144801578001,1626144560795,25017608673644,
    65322148648774,119388428118236,185650592811894,260898069492904,340567002920518,
    419257137846144,491380562409810,551826251743212,596532620275706,622889661729846,
    629929382021324,618299161440748,590043954885370,548248169084302,496603793640888,
    438974619009674,379016303353554,319891980271918,264099423445500,213404987039486,
    168865587989442,130913566034272,99478717682284,74124815809224,54182615161960,38866597618454,
    27367941657058,18920984843304,12844371904524,8560801478922,5600665084432,3595043183820,
    2262827373152,1395596395144,842657955264,497622213972,287101993974,161640090772,88690496944,
    47357912546,24568109636,12357943302,6012071858,2819425554,1268619682,543889890],
   [219685534,81917346,27009904,6967306,612884,865795,870327,578449,325891,166389,79141,35555,
    15197,6201,2413,889,305,93,21,1]]
private def pvm_s4_2 : List ℤ := pZZZ 35
  [
   [77009931398,209788446203,351972846716,381048671553,205806617296,92247354434,291428195147,
    215369415166,60636113532,254536610659,152374543600,123263457120,242911144063,59487317650,
    198520358618,201994294467,55108705485,223211477228,71788854109,192511722791,202642627636,
    53121076532,212085248931,52363712672,181363800860,133588625731,125063027687,198601330204,
    25265538786,211290590537,80400734648,161373191498,143485524403,101195668621,187502675648,
    10274812294,158710033851,4755002806,218394447902,168631094547,49356607241,46652619524,
    213955840142,339381454025,154346131008,17489706900,113214323578,323596755153,237416276580,
    33008885190,78281785989,133493429705,204186947542,17731511084,183538378287,41770097308,
    110595816670,34247197182,266998333857,201987965898,50321431868,78905538895,111661845855,
    128539650258],
   [114171439792,231127961153,54415908718,83096590228,63452919878,199954522127,14779767162,
    248808704338,186846692653,60577642559,69652614598,116855189396,82193640205,181049963371,
    239461317028,148989580,129152807175,22064996623,87893332782,110990957618,211338724115,
    30172583425,269851312472,155766825585,63715916687,7680896594,160937900818,52337304545,
    207366605231,169909514646,113852746408,169878232497,45164604497,100039540836,76242908180,
    85041783229,127258724465,128753632868,153837852188,279157003383,86669190942,35635824084,
    86020145654,101418511569,134323715015,205342091712,90906255184,291289276863,75699527554,
    167103751664,65820324443,69210118209,84086429091,211572527624,18194652630,250129891171,
    46560948180,283072143632,215600756555,69708883107,68889557016,75514915722,56779909164,
    257125593479],
   [86892674298,211496586904,138689963221,157210436719,174725247154,37870563032,37417495389,
    133361155205,55076244896,135782154004,27148560673,171968731207,46207442344,175194464450,
    106460331837,67030750599,18344330566,87230691890,14362301830,130979458825,29001074558,
    90114408084,7383978487,71967118559,20262362351,70061924022,37680152214,70278975743,
    52966949701,96193993368,19435119432,74756327917,79569727,5610809908,54215712210,6553566826,
    90037102893,11130327104,69144803424,27318261914,89989443519,55109931177,139588372770,
    18701806895,80133497519,97089890070,81269160359,38475781925,167777705772,108581922853,
    103975976393,172778166886,9316795473,116593323223,53075422772,31549552110,47567484513,
    15206822466,48409815020,52552321101,56122054271,123962176118,17241669850,179923669895],
   [45699620542,163552671800,113622520709,41146151579,126525559276,66983100403,106027935167,
    152213858034,46954322230,165641572431,4131163203,143402339250,44848025855,109891065513,
    92741219664,40506979398,107187727161,31863792268,100131584230,105372933539,71527211899,
    130858592624,6128049104,101588884335,28622523556,35127900758,49047355311,31328537078,
    82835034466,42418866635,69374010559,17887166982,30029946184,8621121901,24404820607,
    17968813896,13789329880,58171079263,6241404961,85746060238,16373316233,116609292007,
    37071443326,109749119694,85698648295,67838268177,126625963382,19421500985,182366431461,
    61010242552,191812130088,74919578061,135728714825,129459611734,87410732612,172934973363,
    49055788983,186388242662,40756809380,149135706759,25843959329,119913213820,28009612574,
    78901954347],
   [3673060247,72731038030,204644026,86348118183,50239829063,55340237302,69732126726,21731389907,
    24783730777,59804640312,10663209138,93929691285,13832911043,106639580506,14972046672,
    110511494987,2155964867,121109562592,38051414771,194913541731,11975657513,175613417686,
    14416932418,153037541567,8316570368,171991536744,4789688508,205380836053,88227257597,
    144575096902,99825189860,96982047791,81040039425,90080448724,117799096840,3930736671,
    74398225743,40796928331,6390881631,34136081041,60626982869,7688314203,69169695106,59866135766,
    8869545585,10249544325,81442657430,134667828496,34785470302,111850737413,85922085899,
    71374211700,55179698290,195606885165,333897712533,147899867863,75317244634,18056898305,
    304287177057,364384299917,118478352173,45680337492,125797093809,345755346801],
   [248479960917,14424342384,24690309780,228866217839,343342648791,132358202703,94477100724,
    13531975855,338929306933,447368538013,191450264351,78766201066,6223298960,287410596645,
    408905006735,244315631259,58920233009,89706755049,251531240165,299234306701,163626098549,
    33052177771,102818603495,314169851797,421093344879,300475646499,92613318147,7693704059,
    90426989833,227069317665,307231489783,312586737059,284774864249,260749084737,240074288669,
    203470386193,158399284835,142487000223,167792381947,196270807837,201578876713,223009573327,
    313049813263,446368098541,523540998049,468519032909,303239155853,131438712595,59917059973,
    114158104335,204209464725,186574578587,5349238972,282651712534,466466931506,440385070326,
    243266843420,31457363064,34720411207,109200207330,393426309146,650593954236,717692024972,
    547413746338],
   [244495397706,6575152433,62109722985,105203748466,412049309108,720303003898,901077650842,
    887948490398,705306567664,451121412152,233940184212,105794912920,44725492310,646048168,
    33481033355,22984412182,329041126626,1058095794396,2290038825550,3882529432858,5371971704104,
    5977047366142,4761803428248,955631608440,5643896791465,14303246893893,23139783538189,
    29152595890133,28538079120785,17269382911909,8151081404856,49917836424038,108304971428404,
    181357017882382,264968283377310,353339823384342,439722739570558,517305733059516,
    580088744733766,623599178139060,645345862329432,644960537589208,624036707233510,
    585728414012670,534205289003386,474069204002496,409824002689124,345461234376820,
    284191755007458,228323779826358,179266948634354,137630140522282,103376956792310,
    76004996974084,54721251115438,38594247125908,26672336714260,18065267092702,11992003019982,
    7801239215114,4972330403462,3104001039046,1896860948228,1134066535964],
   [662867239098,378493715408,210940935880,114637266538,60688736864,31261755470,15648753000,
    7600606518,3575336972,1625058442,711467418,298739222,119534612,45114814,15774586,4925866,
    1247172,158006,84581,93145,59231,31103,14635,6363,2585,987,347,107,25,3]]
private def pvm_s4_3 : List ℤ := pZZZ 26
  [
   [430435103356,312431896345,149007344095,326802980080,2440495180,284117670989,79638833014,
    236645715152,132605865647,202588914681,190789610922,132257988210,192557607289,112223126875,
    232890431916,46662506216,237364639061,9205544038,215538316804,36209570783,203041192805,
    56486785902,205881775716,104231771007,173037013189,106891299032,193570393590,200189494917,
    59688942629,65016589496,222559035366,306192633611,81738900156,11476923603,249120631620,
    345296115207,91446511766,76328604692,102042483446,230265072011,6345591686,199316663782,
    45056899699,139198023801,35992140431,280533347064,165023915133,78570106643,15140595946,
    169548555238,44724408679,226137308217,179894359872,67326207378,40751465643,174382234049,
    110008070608,179984137772,208909966781,23418030985,53288438870,121947212190,66884680213,
    211107293069],
   [232918143150,43898393594,134630323725,60996909325,87903161084,143271457332,179196283889,
    116087597003,263672972550,67303032831,56037420833,88188790385,109238412578,145717648826,
    226625945737,38814213669,188412681300,7186046812,116577618457,79453885517,165215017624,
    66877448260,167810461249,105194964329,308325657226,124774984409,76392950753,15887164431,
    97465094650,88710772812,196388387085,47466514193,246177468572,64665592741,150383384145,
    65361287922,15873013330,141500728746,170975415215,101518333139,210933496036,72035574426,
    259761751937,56583288132,122926919088,11238824219,24162589463,199118339549,235199596238,
    102999704626,270804154357,19291285383,242959737192,65577088699,85487707219,74088717721,
    132972252020,115224093918,207454724257,70807729387,205109956574,67826868162,238960856683,
    8638155410],
   [161516940460,5421926994,84802078215,105556171693,137725979044,104813760580,159388784615,
    69367956473,127837568054,77613191092,115332152065,89833714545,95663653890,112345391864,
    85887243693,125923986411,87623955922,83901319678,39802193399,62395487693,25802781935,
    108279137410,14867512528,128099423979,22073690316,79493861646,5799848292,61076209577,
    47401180377,89347021060,14337989286,61373169937,19734790684,41754342801,51182788100,
    87139773584,173230611733,621700215,197095467454,106662141175,94780204571,113245394576,
    28725136661,17524339191,70608970540,62503890645,68684507375,104948549950,51854407330,
    106861914055,59434961293,126435278510,13177005682,103665652035,53970782830,44733135894,
    109198105109,47512364858,97155906884,141229448773,18355381707,174998256508,47248713277,
    160056491585],
   [92263074130,103303189948,117927614367,26848415357,108466812542,42652214393,86813416003,
    112723753616,42283776196,173529961413,15724514152,170280617758,55830842407,104566976885,
    77053803492,14991469978,87370648621,58968044202,60875601758,93901058369,15319115471,
    85426051104,4264407015,52497534901,9952239194,32078461938,9076364603,12762176103,12214603058,
    7209704489,35998605615,8033081808,72048056860,9537329541,101281254271,27345967196,89800055858,
    62138091035,39325044807,95730297172,35668440081,143697422901,74084494840,148575540598,
    100631327095,94220600243,144325029012,30506446938,159045521015,38138417998,148851104378,
    96773919277,142270682023,115386776156,121678453490,118847602375,98239537221,98503895430,
    47096564750,97459366515,18498526367,100737516048,25909963858,104414035693],
   [78070049421,57224033162,75854773420,39326608601,53045967245,54929078146,48506361634,
    65992033777,45296812761,83888757608,55528670690,84080795389,42334042845,89714947192,
    15730961638,89952470391,44462628106,142623543650,44313079329,169114268091,13609980932,
    142160145850,28374497329,140161182041,51729787686,175820133888,27643006295,177289315933,
    3783586044,159521911584,17214169430,124703259789,13653700153,121169426562,32517229876,
    132134605035,114541663809,39744593282,91948562574,3047673462,52339523891,5079101329,
    37486524044,3480909944,51367112761,45018551007,10570040006,16811209908,37382749961,
    17334655567,101761211656,121103091586,40127591051,147253293799,26847155773,116195556084,
    21121600724,178992771297,138426636369,129742270236,221224011530,15438769941,190288458659,
    7335467922],
   [276666395294,184732145202,132787730511,208388458493,11201306878,119347164096,84868767333,
    294447583259,194765583181,32871234536,6563558325,286487289003,382164410191,138294147671,
    77963242252,59616854831,347794177235,369918093283,94417610465,109235642450,9108294787,
    269001772035,333925829615,160680127423,22030097035,103428481375,259139299721,257843702705,
    123346293845,74018594981,195382175535,333666560825,314515093687,155125651701,26423243509,
    57236636237,207702117583,328845349595,327460197739,244637299243,170510808913,135090174153,
    121190196289,135257917519,197275517283,278774245679,315209731117,285465266643,236930541713,
    223040945821,241695416651,242042097407,182189563979,86075536377,47015710097,149289804225,
    363576738365,540064410337,539774330923,374607486639,198737055609,160258849119,268776906759,
    395231163463],
   [382196452743,168447150721,155467026176,400403843622,416627449344,217255323610,22909231111,
    101404466751,59931173560,368974760086,640656944528,719223313092,564130765354,267050256432,
    1411393504,74721820115,86998372220,397396185962,692778825324,841370232346,813453505308,
    674007369250,519946520892,411892545912,336887463218,218160011656,23548999147,372756224373,
    637790158553,458710766437,550576677058,2556128955980,5257463387672,7769947414300,
    8732364907338,6665915024098,528757627954,9667399422293,22367198174563,34302623507765,
    40776367852203,36404214546767,16179217877759,23387345830340,83326387953778,161703559445376,
    253669046958752,352059773237524,448427817075196,534282233789298,602296933228702,
    647260694799952,666618085272442,660549859856190,631639837546662,584247514185122,
    523738813435766,455722093828658,385403543133220,317129889727586,254139916541446,
    198508354650208,151240639964026,112465427739170],
   [81671915256642,57947692722634,40186173922942,27246963551372,18064935678134,11712679901078,
    7425908779698,4602949450076,2788600700282,1650535980950,953975140524,538111617458,
    296039772586,158730796608,82883681016,42112039984,20800251718,9977075566,4641855936,
    2091812430,911492766,383218410,155015148,60097058,22204990,7751928,2520002,741854,185244,
    31016,2927,6137,3875,1869,777,283,87,17,1]]
private def pvm_s4_4 : List ℤ := pZZZ 19
  [
   [323183782860,427123101992,137121433066,252672209657,258335860739,57128711904,296394607416,
    49225176260,226654294893,150730383659,160466179322,215649522424,103382017323,242200998421,
    50965246528,214401180518,48476474144,247823700541,29392869465,102734352446,250251606270,
    304092768165,281105407,63270374411,379552321450,263208813655,51970794981,52874493443,
    245628711746,10512843609,213793756609,7039504086,116190542056,153140310030,260788677591,
    6891061099,76970769468,157411954154,110811604049,222692510029,218082665578,69733768496,
    40066333025,178208702073,37717087866,240072858322,127390246883,105948254089,14857182175,
    154144639026,90646084090,292420839405,59646758386,152111970678,1740669608,89924789163,
    119028901915,142937657432,161880920600,245556981753,4190798725,53987686362,128533096574,
    36086831873],
   [246628714681,161657257228,164897886102,154328820363,70554456005,10860139812,170575398598,
    41317727089,138424122571,52255014487,274412980240,109727800131,101053027773,12547607269,
    89982837478,137250353522,205975050457,112146929011,251728863954,35909224148,212213613991,
    33292506932,19763452052,168542718150,122980861703,174378844133,174531763894,134384815684,
    185632832041,63671252141,136412333970,16696009515,84265646406,205351438437,4509875548,
    249612672872,83588913045,207539944753,127618177146,60747208282,33309350510,86518244317,
    155333842437,233079506030,80954423040,225421876095,56104867905,200780524396,42087382548,
    162176505551,41412173285,79696772268,144798429554,108933115701,200297453851,186817540882,
    148295115130,171584412645,115939853819,121227184320,123760060898,88008166711,138243328765,
    60056463606],
   [167392685712,59457124223,171602704841,60849724460,136939136230,8925959573,140193304453,
    43934997277,183966404960,23202542166,174921047811,2789260320,104811893850,42597503794,
    78524212389,99794509891,105890382422,91323079684,88659471935,67373111877,7129922188,
    115503124350,28673949586,172690615355,27447563426,144248483768,94813283729,16535286955,
    41339617706,61809438253,73041989722,47234912438,173988877331,42882295306,161624248402,
    87367296047,109035427379,83526127902,60860116934,63016712275,20776743059,32362673776,
    15562147043,3222643241,67836789078,66191136493,90659528237,145628048186,54368211712,
    177570398469,1176388222,151339511248,58953084273,72009397797,90125693018,28313160395,
    76963703073,102774668258,50146907776,149250943511,16348559879,173858663068,36263163233,
    154148259957],
   [93018830478,98463612856,127164894647,28962811965,124549784060,52979078041,78894544233,
    127076960072,9057589860,150923707389,43317080744,117729881422,62829080355,66647896869,
    56271761552,20280243164,31017989267,21615958380,3074864966,50509997395,545662570,56876219670,
    23083397952,52719164781,44456375521,47137882062,25729204224,50112469403,15928584502,
    45926485360,56817640927,23442011105,92322640500,16110483423,122353907295,58485822034,
    120297917814,101448589245,79060327087,127667653548,9508008292,124415245039,75218695468,
    118372393010,131546560567,104076796979,151500474498,70995108660,146658190523,20025309181,
    123576646778,45456542679,106940046413,92331004624,104954327914,95859510003,104624548675,
    65248049908,80494014612,60088033551,77549389321,51162348216,74506297312,38838887291],
   [55584843593,54352857650,61783608586,70431796067,85803169635,72870831250,100509240860,
    67797591451,92305034747,55235538470,39040757618,83097719549,4916605093,115725599028,973449535,
    128396367493,7361673143,100528605704,34798380445,112843596079,61058790206,125473189196,
    83467496027,142349988125,90827779830,160800415354,63787145033,144299678745,45842229238,
    119434100948,45229528801,108403514377,60060640842,149000966642,6243592253,132702244083,
    32003591785,86992276728,26483496626,73152302875,34135079601,68922752528,70383622336,
    33718216831,89944102249,10571218199,82381032772,48230164614,31072653051,12069129699,
    36341704664,18895203655,95178874567,36410602965,78674570512,45397322170,93553522033,
    77417522427,110199187394,144654584340,88457193419,226548425413,23549366485,191664195124],
   [61198899796,176186690715,91436043349,195769779278,210238076422,91563185825,245886006563,
    28879702149,188587353238,50480539446,204592470973,147614965115,128294912636,180584585708,
    36118101225,117290607211,95396947314,254663269214,81080169102,190145349123,175922030369,
    73546214574,154242213496,89890492627,336373504007,259683853163,3829061711,45471660472,
    174454352677,347876091501,263893713415,82966551271,52184035899,162676295391,219035640553,
    140384552973,54972490609,101693831419,231672669847,271661555795,160958046587,39474832701,
    63617682187,207135907045,313828405425,297336894987,207449553903,128428708273,97123753733,
    118226897363,186348392779,269983805711,313564449529,280927522705,192120922743,114727745295,
    112538972871,183821448727,252027607937,246609134797,196123523199,202022719995,302053046715,
    398058998933],
   [357349929693,171984727861,13924411202,36671056018,137160831463,380100154169,508705038043,
    437346640957,257208330939,161279385483,264463959467,483996641179,605385696161,475848821201,
    139741913049,200877321212,346583483398,241596503846,3146999220,162395352911,98833867687,
    189775794690,535668276852,723361295378,643068950920,363116242390,71634399356,54574890905,
    46777263272,305167409292,574501534034,723756847224,714794855416,623707764738,580395629170,
    651434927654,747932349078,646168782240,141259203292,743242335147,1622631958407,1806521861109,
    572037197501,2417513282714,6708097049770,10867830457372,12690285110810,9841678649798,
    824180301110,14040956903729,31977942094869,47766038627637,54501852916313,44984806881931,
    13395816715391,43161856887572,123666160261646,222991890397658,332594934544890,441900123713586,
    540060289360368,617686388509336,668191752016850,688522524190790],
   [679212840608680,643856072479850,588186081808618,519000918159858,443142124562910,
    366684623607610,294417567345608,229625343822912,174123682259534,128474773233828,
    92297248615994,64596728082002,44063034242526,29303664681798,19003950183210,12019315032588,
    7413413951564,4458610454940,2614074515482,1493572565442,831266335512,450445444788,
    237512047012,121785856574,60684243940,29362666740,13784683528,6273113158,2764453020,
    1178327112,485129308,192605790,73589874,26988300,9467690,3161858,998178,294570,79688,18996,
    3596,322,137,95,31,3]]
private def pvm_s4_5 : List ℤ := pZZZ 12
  [
   [29107665560,94469400562,258165142444,344865153562,375178353634,220384372000,67352816737,
    272354346013,221805610399,45765413511,277428097122,153631735180,84435233910,397234665367,
    32287765338,95059739911,427850090682,104636743075,62445828639,243998291571,44593733572,
    280618495048,4112179756,92911164885,265260448351,157940031566,149023546582,59940775676,
    143251583043,222465220973,211404223824,102457941328,12093379358,146218132549,165958055269,
    234971607884,102332028956,85844392225,138094849849,79798437509,290790192406,638430911,
    172409866683,59435280905,48367286644,174086910580,23361846422,309123385287,89572906332,
    145417787632,27769601316,59549553967,204256431693,131207325688,206222136834,155574778095,
    60591340493,73108065989,173490119536,70293212590,103439390595,213770259301,211256701776,
    121106810398],
   [123898644877,80546919351,50740973735,194246060484,61573513942,217185968209,63919196255,
    222947658560,29995600689,1168747163,144837296269,18063890385,259842636078,59789147641,
    211224517533,21729759206,209208537182,52838937071,36517454647,157982808133,103200415228,
    232040293534,184380217723,196659299299,210352901478,70116514998,84075580891,21853834651,
    119271490217,180029351080,102605710412,237941735447,25613485891,157040616474,43563847476,
    99545548893,70143867395,18856202196,137482378320,34004182682,242545114869,10936425938,
    242519124522,36523298363,163327109079,28239734881,121995940526,108125119716,115208054757,
    160640255185,120658780294,189677454424,133761107269,173632947325,112170334604,150224623692,
    43716835305,177041455561,5855251664,214521132544,18382854881,182363151161,298646949,
    123238932222],
   [77875399766,123385976379,134952062241,159644693050,112508567880,134418412575,97119630027,
    67588161828,134022473474,25536456029,188401781609,59111115182,144798245862,46458843237,
    69699754027,33220760661,32796316548,148195833594,94400769373,177243692145,168292829612,
    106213593530,153580576867,31795471941,68861128758,4430137685,38508181758,14474022225,
    105422572393,41445117242,120293217998,45537898103,130864256085,62090909666,126702969158,
    93492069741,92304188267,106412404654,39156729278,83109854395,31208967934,15299651248,
    82514223297,78894848208,80426103676,144676753525,42856714407,166786091494,699796939,
    161871385803,41025540402,121809227880,72409451777,51322171229,81906003006,31003273865,
    76372241969,112361603362,52641088398,180536069995,2864136487,199635308356,60431614725,
    156741273705],
   [100996486794,75381459192,107869361775,4985917944,83921052084,68422944715,42317259107,
    98601918118,3334086917,91090025017,31779494156,67123769400,31604176863,52463786699,
    15415256698,47265179024,1625209707,27900117015,6156678552,6182023027,25692695363,38998571258,
    44553624182,67156672233,49304179339,94388932050,34323431320,105546571299,3759533712,
    78785599154,64443359469,25441455333,122475908150,27567346913,147099789849,68793655718,
    129635151222,103477488573,83899324813,131898611930,27166070598,140719705805,31133357870,
    117371633814,93045522131,85473956613,134018522914,58366438794,142008098419,38465050453,
    124287941932,19171386692,99263185509,2099122760,74084910252,35286906099,70884726987,
    58334905886,88861676220,49855709153,102143942499,30166977298,110922864924,9963630385],
   [103213035545,13275881212,86917837404,45872282977,84502062469,74730368854,85661206870,
    85448314551,73816267283,93053618224,56511112492,105676599813,53871713355,86543242202,
    12428511278,84726173995,42070532716,109164625270,70301421519,124833620221,79071353232,
    124037843720,73442551725,97508192581,83945164310,72981164982,119541618137,96391891629,
    119719041822,119804499110,94993154687,121829178429,64542991300,96068676836,62323716821,
    92989138647,40393633858,73029364230,42340654085,87840877035,19288924364,105848481414,
    31781504206,86144652099,60756787369,52556078054,54719434666,40523296421,40868467601,
    64509004306,84954642710,26557856115,86878432109,3977103543,60145226322,9738023883,55020328813,
    44737654568,92730345328,56921945879,151688891131,22269025908,189187234780,45564402628],
   [166213769893,66227479979,175998671316,119605183708,172054548317,214520760129,74023229310,
    216246305594,17034015375,209549153535,20948007619,215318917746,73545763798,220767689657,
    183952812855,106260417602,175082233222,43989978421,143299065661,46205599802,190730196336,
    32036846658,180011239573,102097569175,130238798472,116539202228,146149989879,239555452967,
    8122748970,245945473152,150870975238,92612809773,110873561033,98572343202,209470594140,
    64105981158,134538690233,147149860593,22146333393,15174923944,99236498607,199723669895,
    164271187997,95222658033,138718937057,246869842441,256564488331,140912154423,42803323855,
    72094063895,179974579781,246546415633,217296458181,133019931685,70895061763,78342668285,
    147307803361,233748733473,289144472619,276190600159,189513302611,87764344893,70098373163,
    170700431031],
   [294909408021,315272959791,226330630409,149140885463,173817868039,249094576189,255904766335,
    161246079901,67023546657,105373289633,291063343603,478769103499,483810248165,269619080253,
    10307733997,63451772446,107330473955,351053376037,441468319999,319456186023,137882379133,
    106239148509,297668909927,583089936125,731644694053,594123846347,230595666545,123897207224,
    241287961484,84204184340,167452620909,267664099599,97216592527,257947628810,583678571904,
    690486048202,533837740868,236761486652,7978023918,2172459826,211121207212,470575858288,
    591758547062,522588672236,405336538388,468983621176,821449281662,1289808477746,1440892576742,
    817254732286,702832087649,2613801881535,3776995242399,2826487571291,1088593657190,
    7527141846198,14366539093564,18138095845518,15145687424344,3071541060984,17492628741263,
    42205927820549,63261202794423,70860917848367],
   [55549388265843,10757013298339,65185554756392,168157550201272,288738229622642,413926593292436,
    529606953237936,623117305448906,685320456421628,711779525290712,702913471255034,
    663264136911544,600179154054538,522278825650098,438039450079110,354723510938974,
    277759958347168,210561996805070,154689104483272,110222800706534,76227160296472,51192474239984,
    33398885870074,21173894746734,13045774996072,7811657367372,4545416694522,2569609733744,
    1410866221310,752059812642,389003538550,195138590090,94873331620,44673436938,20357331338,
    8969894656,3818034042,1568282722,620915326,236639066,86680402,30461722,10248270,3292000,
    1006312,291460,79508,20262,4774,1024,196,28,2]]
private def pvm_s4_6 : List ℤ := pZZZ 6
  [
   [20124140250,15694313397,2727989805,11243503672,104993201272,34944521942,331014559578,
    135933406906,574546250978,99246061554,397639367684,103213690313,167389797121,237697423853,
    291376310679,148122693722,131972280872,284874767642,29604467670,185353760707,158691974371,
    184074713437,231044182464,218003965472,6330304152,61981227925,288982486007,27280425885,
    250636641480,76882827410,63689149686,231817610569,153770325775,130599769036,160174781056,
    51846156046,45226126357,299578095837,66995288446,246020884102,2646129194,41120572853,
    165342389635,117698514773,317880097794,16433552168,66611453009,179613876181,1594016705,
    149502842124,161761069176,157902698317,208640431597,134480885642,80798382180,85190244562,
    82221408835,180206862643,14511675150,280403245294,62380925485,142282357203,41656734813,
    16117984133],
   [262475760116,44349884815,222886957719,36758768107,228041461142,3215665156,48201560411,
    97831727477,83998928157,214686807338,107841041770,242648773851,81164833209,176630529434,
    20021309620,45432759808,127294638613,176679509179,282771312978,109044156198,245216501339,
    70321375967,116895800806,103203465070,11350012161,126178525937,96365167491,170252512258,
    144291279466,203549037773,100032782845,131717343520,67715145748,613081722,96374537469,
    90833316099,133359112872,135278630798,144913481423,150566569077,124852974236,133495913958,
    52347884747,125870376417,53968615923,163158811594,115368664516,187582702887,122659723611,
    138699464676,140116711422,52286235395,209687990795,22280763796,235057853136,22038207763,
    200007394795,4847400475,126719167826,101200135512,125781384897,153449150181,136634609190,
    149122451770],
   [102449940801,123623648867,10680151412,147470526190,71582543766,216265181891,59222813795,
    222450237532,14842312452,142733914279,12267984443,31672773240,76921659820,49167777208,
    174614962603,50260635823,222068843218,17173275648,197226590971,8077849223,143913303804,
    11691316346,84901399161,20571976239,23215054096,34198775162,37298657000,45078031909,
    102216299467,70421564724,152564377020,115598166971,149998157717,143036405812,98146125592,
    127496899099,30570943723,83684576546,29892586267,23506435097,66676457138,46919174253,
    68292364427,109036917722,46192578892,154374660601,22974732143,179211056440,9240664661,
    173355528087,55137793076,118562894630,96882167373,28764129807,106270408926,64064806559,
    77168974485,139749441310,25543462832,181767457293,33119829668,178443649484,73037223411,
    127093884759],
   [78446226568,56030111446,55144925905,357141398,24961071278,35564685283,10826735763,53314393924,
    9484539150,61658545955,12916705971,62764383104,13964444138,64069498873,10324992879,
    64388377674,6788223229,55862828131,34012713410,23017707002,59680363593,30658083154,
    64144942022,92008212495,50432419295,131974938468,23561856888,134074141481,15532350240,
    100628026396,66705930665,46968853483,115913355876,13296881785,139673370901,75186215262,
    134739937476,119542197241,105896947533,129338579682,56234373496,112858364097,6187255894,
    96473679106,59257504209,88222980537,87145062722,73924661004,98437235555,52127332521,
    102324883570,34721630418,98657162367,30718007257,83790266560,31387826086,65563614409,
    20055759247,64142670686,2777839851,87496016819,19382675034,113981770150,30100432665],
   [134147767069,29326316544,135040232884,24964565499,112840870271,34269715634,78489461504,
    68846407015,58664736269,102186331304,45477973490,121363097947,30233971979,121967114214,
    10413879072,99990317899,28985097578,85528940334,64622139149,78577359489,86742934670,
    67835735480,111367405891,67991324669,130962834382,83430319588,121506875315,81055088325,
    98581091914,42804212460,113449737413,32756893921,123999549178,44575031150,118215754923,
    68922470449,90155422482,86978484496,45205718727,69457366987,32420681834,53775969378,
    46691104701,71187285945,39295605086,86138422530,21252052285,96665788797,7136404787,
    92673834598,27790980094,88521461541,51600243655,58068999718,23437366806,78900571873,
    20942967237,102078103024,39986413794,98405678011,44618818607,87098973370,20696712068,
    115152075981],
   [17017460179,177517550204,95149983100,166863753275,154803776351,131892928112,194733165474,
    84794531057,207877906645,49907425086,218536005220,16667801683,237223255485,46619275967,
    223598720454,117695232834,152319661509,114590485253,137063531710,139197175932,123550674999,
    203343042929,32995765702,184787384314,15936472982,151388353841,22020029227,151694957520,
    29940896906,200579573567,143490328139,124353834116,181030237536,45639692513,178928702227,
    6339905791,202252021180,129241328640,116849829877,189662642089,24356078525,101075224726,
    14077281610,110426461727,59851336759,87947968520,124377776984,42613601878,3898004912,
    54903369672,77032239088,506005378,89342550607,89652176315,25676914263,10374048077,96865595083,
    213891015211,253436717795,195679635999,116921305635,88977954059,118289432053,177794281675],
   [234230744763,236026096607,149635439273,37190153023,26544477471,155665717745,300171048643,
    311027643551,192129552527,88415656317,110193593361,213933233197,267355276893,211335194165,
    134020482593,166014024653,304964452361,386641635917,271868583759,40432054693,64415233660,
    96825095133,391627512327,546116824745,424715795327,156516319211,3670376414,78820494461,
    299657370627,422192192579,309371268041,67855586681,41548368200,143979203503,517654643147,
    787033217607,733621569385,398946031895,36598378823,103633004092,33407920187,280421934217,
    383503637739,197113963989,199383654072,554381088796,637896792680,428042311144,131198659612,
    10542118508,164098047016,440068756106,564621645114,387647254048,57025777150,31737589409,
    476611871860,1530971939184,2497903469570,2396247958802,531647310002,2787828490381,
    5950525425359,6526874760415],
   [2504834826325,6244187478182,17058247116878,24801176186160,23570979890832,9316901801308,
    17625864673587,51189650157999,80161774626663,90745553645389,70370996619489,11531069142135,
    85614071978558,212691264493904,354751378900922,493524195909234,611292531311614,
    694321961243332,735048807003780,732683775766972,692356411456164,623265024859852,
    536438729026726,442669372763462,350992872259366,267874403337520,197053254828174,
    139875073680916,95892524516688,63534796231382,40703892437372,25223140594386,15120785139776,
    8769409231776,4919667424172,2669086724658,1399878601990,709428062474,347183606896,
    163960926744,74662923004,32753785792,13828390114,5612374276,2186963984,817047852,292199762,
    99853824,32540136,10088520,2967600,825588,216396,53190,12188,2576,492,78,8]]
private def pvm_s4_7 : List ℤ := pZZZ 1
  [
   [36504835258,53666414989,158339647530,231618714227,236417864356,212503008179,90400447890,
    63404777356,124133163533,163750836640,558634309,143380420932,257141982772,185450239066,
    400284999366,307276499968,274225784678,268557392766,92168923983,196164562213,162311592759,
    352315945935,10936577285,142583202176,186196864310,228804676100,68675302794,261947258645,
    160008716239,118686369345,30356576208,306971591208,161063318176,181190525733,13703856851,
    278632932399,2712945400,239672709704,152974234530,27618918509,162453073637,144501444355,
    58421473861,281604553838,107595088814,83121375879,152977469593,100585460351,22630974782,
    255695939760,111014276440,300691320903,38210808171,13371067435,125352017288,158461356948,
    60186759611,248112852417,8266934459,178205043796,60746237494,30890871778,141529780599,
    179994721939],
   [137131925958,264546212098,115202508751,190847481761,35435333770,17041214563,169841073454,
    111768130510,291658335419,78326155145,193533213116,71616447048,17182604703,86023882883,
    133044873173,62807946642,247394906708,40782814643,268814778081,19672257854,169883077162,
    55911835442,36941210391,160504269825,53015472149,214885589888,104363889004,196901848905,
    128530930929,126945421306,111641682438,8770853455,87615374101,119778782315,79275976546,
    192670258308,76575977363,162307134473,1812476062,118105961586,97586336150,87694805397,
    174039569059,79535462142,155428051678,2336317905,127141619315,113522524907,129012589160,
    193542780834,125375102437,204190571461,78772649590,167884581158,37865371660,165069080373,
    138654016337,183017924816,155570314460,150979879659,129595886733,57494004692,113947959322,
    65415554768],
   [146545097241,151322627097,204258672820,150436520340,208699382373,109256301409,132679485780,
    82217213726,28207540067,82648416043,72138275237,95478132528,139520882996,107002294403,
    167679982953,96059969118,178660438500,72804980721,178141756103,61440556694,145297156458,
    45491665259,73599058233,5877459614,6575608315,51612868836,72678631154,109703859443,
    109548596861,160648397898,110063357496,182612921587,79115350735,165185454142,43668284538,
    118450282361,12438323369,58916094416,25872388139,7774879352,62574153410,82993655945,
    76799342903,149642166576,57635413530,187558487525,11107913637,192216868388,46902446381,
    162245066537,95473870342,94290880258,111162485343,671237922,86083293622,89048282363,
    37422172391,140836227530,5403772341,149628819315,28483366880,129188652074,36576076837,
    98935414815],
   [30816026568,65849539270,15929867271,36216696795,291406328,7206084724,3291046003,21349073004,
    24964516592,52313945607,45781231241,82506132380,46197277266,98097745381,19360653797,
    92128215654,19231828763,60868701405,57250510680,13984179812,82393969249,39747827720,
    84444383144,95845345715,63544638633,137862740716,21095604200,151079626131,29173850468,
    125181594540,73916817993,68951146973,101939707726,1319576755,116623115109,62399952374,
    120128308442,100756479277,111610001441,110365098340,80438023270,105376462515,36185988563,
    91470846554,8106666437,73232856153,41659759286,56012501188,65257865953,53229870063,
    76509152962,66856435426,70903953975,75163324359,63573797070,67543372746,69198574487,
    52968389327,84133338572,41567713118,92965790733,25040169465,97560344506,3415665701],
   [111177852377,33205735110,131283649456,52450636673,140997844593,58443223708,121938073792,
    63843544629,77614815927,78111411176,28576008432,95568407445,11502353368,109892863556,
    36614728103,117490625703,41846425742,100964048996,50903448959,69287508479,75791112810,
    40780557526,108256190441,25596145767,129893172892,15237012112,141678081183,15089828109,
    134263461938,13194042376,119523631041,9146309153,110349425112,15922918036,91713663795,
    10385507837,84571449520,1085318695,102305155085,13827513919,112576958484,50951247014,
    84955729361,65079656421,49809562770,48837164514,47616725553,45489441481,54336925050,
    47281939130,77054113319,76625401695,77248213572,103079823394,52076282739,91981491715,
    46465342276,74981601792,55674625119,66970672947,64554606030,57948980766,87706264257,
    70494350469],
   [102999187870,93406095144,105677926857,113178023567,99659260158,107570972826,140963101169,
    162708643719,138281660582,223402970698,88041783577,249372479163,18000504124,220724288576,
    10955716674,197655832133,17899537887,211207205958,65587080398,192229433935,99486426945,
    171384926800,135883490900,126939851231,137576087671,102645571654,134316383078,101416078727,
    165232829997,65513204774,185347658420,3024354382,138122827863,2734330888,147603778008,
    11220727776,191464002877,109036611229,148389621094,179562411514,57860929839,186356495421,
    24156092333,140515189954,42807253524,142535385595,121793379941,50699924710,112313422538,
    21298549606,37626694885,13406181210,55397161946,1808676812,71065756041,64367974225,8113497059,
    969754492,41143976757,38321276049,48943245392,127747303312,103637869438,15358313640],
   [31501671247,8719892699,30604313776,41359687350,5820140898,86122769897,198394652431,
    235555691633,152059000983,45914035467,60954805951,201308199269,311820458383,260471179577,
    98151883245,4513220621,80501377425,227615545343,268052794133,172012301007,96928936219,
    167894411599,291973254431,278498584787,113590726869,5927721825,126654856601,379266968823,
    492967840397,326205220273,30618947939,99277725606,71647910687,376055535825,512229055605,
    359031743829,104684071735,39563881665,234345467319,462135500215,449105869059,172227127813,
    111338958050,115168412414,207205801153,619199218385,803283418677,627544677343,256592976939,
    10975324347,85392470435,370829462093,549986314153,387781052987,49565347788,449296528474,
    529228283208,288773533436,14853323392,31152936288,389501976406,767268937362,704619504334,
    51352739098],
   [734236723361,774887336675,539649972982,2813175777356,4494864020878,3676381170256,472536795591,
    6527022413611,10852294941035,9240115701615,461804261080,16107250874768,30865145023556,
    35403682698864,22079551300694,10587786201023,55270875819525,96504196208769,114774670335595,
    92662821342201,20785039310725,98624859310658,251702764382916,416370774056054,567882883957466,
    684644193308026,752609403499122,767263070126900,733072420503026,661044210121778,
    565400148845744,460375327600298,357847248204532,266091336180320,189590530079862,
    129596323720840,85066257115282,53652514806582,32528591654064,18961019453204,10625998986748,
    5723961821524,2962581595776,1472452680044,702238790984,321069921490,140574464980,58863142804,
    23537448520,8972290212,3253945156,1120163316,365054226,112274820,32467900,8789332,2215432,
    516498,110428,21400,3690,544,60,2]]
private def pvm_s4_8 : List ℤ := pZZZ 0
  [
   [220398683556,297904021435,183180721676,77499183378,176747396927,139090615014,31356575844,
    119328118671,72189666928,27087162315,46690377373,75431128566,23247139365,78058290157,
    131263034180,75914894511,2330879505,144977090502,101553751828,42534067832,276997433162,
    263028561350,267095853034,367656374656,409313351398,65379317792,225676954792,66184355869,
    321819151239,167514837907,228869984411,122763519267,80380926012,339113363026,158337490642,
    63387196964,36962104161,245298428807,210387804761,39717424279,209916567222,88559585004,
    233521594586,23039536531,302561340179,129738374175,34289030734,87815879116,182131958798,
    162035662868,195739650603,248275971769,5144158777,106797581840,151662566532,120363742626,
    87326944851,294267394829,11323364735,221420893938,26845092066,78738564426,19187179473,
    306615816957],
   [8853150023,275057978384,76560062550,79109508785,102073397621,128450899265,21866009736,
    253771043448,79223838444,241190225525,110734474847,86589728244,72046977706,113473468752,
    938389089,224681363943,89599146555,208892464104,149974426280,93741816679,149413424007,
    50758204669,65254576994,202475886076,11363059304,257664913423,74209901453,201334212274,
    99598400462,45413306913,134865788755,93426045313,143344933320,143703921470,66350012571,
    139025340093,57897725771,106312024634,167180572856,74200268693,185252331753,17313866910,
    111148841658,91901348986,31751056655,188310074305,19354746989,206041386480,60571233944,
    143733831687,115962342137,31017692922,194279796438,61543391814,253226296121,92499503259,
    224547424800,98475962378,108446696533,118455824297,35572785027,145171270488,151454460538,
    165409918807],
   [208613402039,158494708360,203897426320,104151355455,166953608633,24570849420,129601658150,
    46361679472,82416773073,101458649441,15467674532,149814569984,52305263826,187959764945,
    102831291317,202647423034,126384531710,191170951123,115108009145,150211224014,73298243054,
    76238012715,27938945405,19584321555,5212466009,102455688958,24088949192,162568718207,
    43769104511,196369475760,53552608178,206185280081,44922927493,183435870098,19113609432,
    128687159841,15584224298,54386586480,47318034369,34404221132,67184222486,126161930353,
    59653341281,199145610368,23431166816,223494260707,26759904618,192971353352,64953733409,
    123046366835,83155983656,46300472010,78270497779,20166945886,55137021578,69273881249,
    23651862091,95698568850,4375028857,105428024979,11143622608,105665932834,4686851024,
    100683792375],
   [22685874087,89632448484,21493604042,67845470425,1300083716,33390357780,29849796717,
    11079478214,48785481014,58629517353,52668449969,101075290286,44114992666,124247616833,
    20898976999,115398012660,19942430837,74323555777,66345296200,10210893272,99360804657,
    56184619572,99997732712,111066647019,72805372543,140278788028,28601203112,142447124591,
    18577328132,121363922142,59259704419,81270604805,89915057858,30411532382,104169557125,
    26315306980,106543512508,71738311931,98535668125,93465452266,82993109154,91508662173,
    65592898801,72413637226,43236278336,54002237345,16145284763,47881377714,14464636345,
    58992519223,38292773178,75864156680,53065740125,88928763603,61382375620,94054139072,
    69979118637,95440517013,74870155640,82242104712,84134424509,52514731823,101707187414,
    12861968262],
   [124312954165,20368627876,131916967290,48047081047,118249397605,77053940964,99127662188,
    96545218273,80246527811,95971529456,51781079138,81566193285,4872434639,73885646754,
    46962198783,78049046277,84798825540,82031617832,100740666233,71851795187,99779970806,
    42739454522,95513086901,5905870155,94070982202,28183617587,100345469785,49496149860,
    114983587736,47634123735,122656860923,31680539316,112487334360,24547978385,99813294021,
    23221539794,88144604716,24490839271,79532644949,25563657832,75769660118,26034462783,
    82358785397,17842447314,89513435918,11051653097,104842620771,5834294209,110744541878,
    26157498886,87814376217,10697663351,75534576126,24714476093,95651134615,37809851848,
    121138136444,21703336777,119709507719,10452544314,103601614318,16555892805,89173986251,
    36465026114],
   [79173667126,79303967183,106290861323,95404254726,127631238544,102300981511,138453656661,
    115424995698,158998807870,114361581367,173492788657,109751167012,186277900352,109400775341,
    221047283169,78487967262,247786805764,19249131429,233267314661,27254933621,181683576120,
    7404841502,185038292827,8857091731,195970587994,29384263252,198741572397,69525759187,
    160546597902,72778663130,135968237065,64655508837,138331938470,83982961810,125603347995,
    99359866175,120228369364,138104307096,77007681603,139377652141,54989637214,140428273806,
    53743548289,184871936531,2659619731,205430788836,110102279452,116338107321,125123610315,
    43217847312,93471090676,22693062449,87260385019,5633324835,74922586850,36033078110,
    41219262439,41957372187,2424001459,17895676699,60882467069,33607669319,45803707936,
    64595746284],
   [8381780248,20690659945,16079613340,39923450406,2454742075,65580267801,91084220019,67326689573,
    1914727017,77164422072,102748906388,37213870300,45343956379,26600549591,94192819758,
    170580469378,78335071662,115619704937,209898153585,113945708445,19624771202,18502993833,
    207621363641,315025153827,218458438565,75047571533,87261391457,212619607569,241296885009,
    114643480391,17851612995,121510911237,333088384623,391712658791,193243129227,53516994492,
    47266650076,244886106665,518182602019,468190885569,151523299685,73934019206,32596018357,
    323878988177,457121864685,297820273081,58622633615,42087188519,299164120177,567925824429,
    541775035215,192716520177,172975307232,197345428612,172704052673,616689262747,747027162629,
    488283846361,142515298359,77664683745,357766536467,678225480191,661811294949,233371875649],
   [279006356658,432916437798,116170693774,273833641581,160355367857,593942877454,1368013458874,
    1206852029396,219844645785,1956952771685,2189644351023,281657752574,4561760495666,
    7542001861276,5721809718200,1916903761237,11981386274057,17506903119689,11795241190137,
    6622132083442,30995882662218,47807724451704,42789259615428,8923126057178,47636737433899,
    107084246253673,141734019215359,125854631242359,45466217358003,95907669929228,277665297894734,
    468230397898980,634207806731648,749173747005710,799333331086294,784838201504876,
    717230883730946,614609912961018,496412726707718,379307510256148,274920852767162,
    189379151886962,124152783943670,77529973331386,46141129314252,26174319456446,14149877941992,
    7286283494548,3570979417802,1663838984620,735949393544,308467557160,122244723090,45681108818,
    16043759134,5274788242,1615474426,458063122,119309716,28253486,5997582,1118086,177186,22476],
   [1958]]
private def pvm_s4_9 : List ℤ := pZZZ 0
  [
   [347130404182,175662627238,206232144299,123942875613,168087264944,39776884042,88258911955,
    277378815,119351251002,91839442563,37931544220,73631763746,37003323469,101867350011,
    99316584708,6375473855,40673001005,77496516255,161062484258,43429208361,133962527553,
    145240778960,61222145549,42824410791,61968539924,88915130414,20771789275,29155149234,
    235398283176,91269060522,206285847276,269846379938,416047471118,293261679120,240564087410,
    356355638614,104452308834,96283174993,126778799937,228844588173,347208316819,145042456901,
    114125678384,95331482876,192811169624,273116111092,68022150838,186185977465,233066907231,
    97829643833,96224683489,42544235318,345957013854,151092204830,117955110227,55592034973,
    189129710923,224095362979,158668987106,308365428808,55877491594,94883472931,87134560775,
    163706410327],
   [105388665755,217239694656,236820511290,58130970763,140958341889,97434577183,109298079615,
    102040485068,260269899798,49979060804,233028724937,149713448849,50320262874,99883219552,
    120982270994,75136262810,176130598575,212157585415,99540003576,174723870658,58412058102,
    23143423877,169271682979,138763727637,149016959624,211645514974,13161524361,163190455145,
    156580610715,62864663126,229659456452,33254187916,151863118387,113366773821,7565250889,
    146374321824,146485961250,115385210019,192890694191,30757436020,128907878990,86532308734,
    16309221207,182335705689,71778577439,179369070992,110939927402,70516842789,113567668097,
    83309805169,89262954034,213087814046,50231481269,266965232321,3672016056,221787686072,
    57082580714,105747892821,124561016247,24492114615,163865117888,134994239052,148899955485,
    215808829177],
   [88413718876,250667134614,12777795617,231385891303,57149020189,163660951218,98969959286,
    66001352983,103720411867,46546070061,87575755310,155226320000,72209089993,231525758195,
    58337239354,253688658598,38275274945,229982244497,8614984154,173565800184,19715254634,
    89026641809,32081753969,8626329413,32267166740,102068715702,23961606777,175368871111,
    11129089322,221732629218,4929655309,238389697263,13640016078,212997218880,34831542819,
    138607596747,53060455024,30014085742,54083464433,80492061054,35611045138,166303928135,
    9932823777,207872258636,20702401511,209161746637,43486472398,170330978926,54583101323,
    109005975617,45862441404,42897333872,26719444937,9501337124,14852032772,40412331905,
    17751743667,59784222672,32133519746,76173093573,42984009459,94562995218,44072551340,
    108440423657],
   [35084628999,110757377790,21090266660,90351157769,3123331726,48586408874,33084700099,
    12438251792,61353672546,77221620437,72775864299,123477739734,52966450562,140485602725,
    9898960695,124453783354,36952463449,79647626923,71537410356,15841130518,89769809319,
    52959164582,94444827932,109597353175,84560659579,140196616634,55788712082,140470073499,
    9743044725,117980948310,37576423825,81099234529,70586331498,38514349832,85197286167,273626110,
    86970174440,29868267783,86275542227,46316180332,84107181924,55556893041,83080720089,
    56460869484,76436358832,52694239977,61568986975,47915696644,37396508280,49994130093,
    6967649881,66583187962,20825620729,90824154343,46781002762,115636385066,67074768993,
    125793511493,82261280814,110894194122,96619050351,76145869521,107865048892,31067957718],
   [114062860873,12758475394,110765217674,53745252429,103708150999,84737419920,92665022494,
    100182025861,71508020295,99938828904,32933366938,96274849817,9002218172,85709677800,
    44908939755,63282715097,72927292632,28933448288,102818776551,4909330217,123527158722,
    667399901,119901860167,3486292370,96935130326,18990225725,73011524599,47584148518,63655507186,
    74587807035,66737204893,90199310912,75458119608,89522864225,81492296569,75728232444,
    80510177982,56984982303,72462724611,42966172452,59252864868,45775478523,53900626745,
    60022723508,60995779746,70917851623,67445385415,79081608342,68359146974,88340389627,
    70754469545,88734778214,66633682680,84682393369,54609846217,81459832390,34041221752,
    87453399327,10582822685,106177116342,7343373917,136851807347,1826414771,138601298294],
   [5425242724,110756084433,30607818364,99090313514,79371948863,112316334243,113062681252,
    134040948914,127291626907,151093429813,131547476988,165333950140,125492346955,167497634937,
    126654294576,169979944186,138703835503,195324166219,123451522886,201864450420,111233247873,
    205783559151,92970154212,202726450130,62183319379,168399769437,56963600054,131810881458,
    84387339293,136928990291,94980466526,164784069710,64626685803,166982877073,27202717722,
    131649759392,39788993349,132474990875,44559042010,143597953972,44138013935,171379988091,
    6837496912,162191060346,13091881104,152673687875,29354841453,147547980100,56270883060,
    131503972067,81985211313,117871400032,139169647886,36041777141,128350345175,32918904525,
    60460118620,22538892174,30912264077,9747218386,57282525542,17226642816,35552998315,
    15555208227],
   [14934424608,12462972299,34150685593,11307832340,57026772172,28664643214,32694016543,
    54259729115,35453550021,12136448965,330690877,5064907653,19294551395,7554069805,50050786066,
    98382641652,52011399768,79815487177,160390495811,77301089405,83677513776,111402887230,
    39828271247,148226693845,25427591963,188217214278,207316286434,17489610674,110027875157,
    26193665295,91898894894,28868008244,149686466717,211930998815,109322849197,44741795807,
    168236361171,335673551451,288841380319,36812821043,100751930192,95095420293,413695980747,
    454280951993,150635749375,125604695326,33549593052,313223083681,504657827027,341972648813,
    55737393945,2910446915,236885035565,453529513155,362545411639,50538459375,96225041334,
    155735956805,580341352227,714517723111,378569176751,103647177608,244333683252,88097418527],
   [537546980063,646755396207,344221958541,22944978849,118394695877,605257287977,958163023343,
    691814796115,39882321850,486355004968,86112179024,770190377791,935936836495,294552559036,
    2115036240784,2563746582914,374496397844,3239066570551,4834454860363,1481453189475,
    5937300764126,11951224358744,9869963714958,2443366001599,18787882050701,26703919764567,
    15405134635493,15111267933300,50336288437176,66781421028510,44882780735488,17682742756705,
    100189620945533,164628771819449,170813009062975,93614670178407,65798365284246,279559821859276,
    503001276835446,689850902856526,806208816416390,838372238848028,792946670217256,
    690918663669496,559123494317946,422493462400700,299179360062574,199009801070278,
    124530404205594,73355525332514,40678011600414,21222863891062,10405228152312,4785350691014,
    2059193349294,826328503804,307889806118,105919839512,33395594714,9554981758,2446975732,
    549726714,104922290,16043396],
   [1702204]]
private def pvm_s4_10 : List ℤ := pZZZ 0
  [
   [63801610486,193002259850,353419493806,202669521326,20795923280,222184650295,38380649569,
    75590352338,73608068412,120226207963,57667986330,35209036454,11087158624,32590232823,
    93056414419,202327764176,25594233656,145735678625,40357946990,70196569610,28382879604,
    152059189055,65632281582,42922738232,68934624467,2635898835,20090344216,71179799624,
    59539013209,91521998941,67715488380,51001989186,75248056663,46403799777,113021220548,
    42253585732,78889577263,77279672772,131559273882,54340744404,127019695252,249128368138,
    309084277204,244974759424,270507556694,465876639272,336330752830,60926116844,111067028256,
    26779508298,310306417407,317922361551,139804442687,135226968559,79447071123,213518842884,
    327756851056,128776370074,4965686337,25145287744,186684627669,339483085335,87670389243,
    179401005392],
   [171659717612,150187829562,128333077542,95561859699,282518515687,164814157323,93268927038,
    136514483614,114968766510,156365233108,57774275501,301287204127,129695352017,135956608194,
    143114495216,125146912964,42940088056,200127384255,193554101043,33945263322,142738147318,
    155504197118,40001398178,157981846693,167524514657,13601018411,111769717004,186713687972,
    71634142050,214784181831,202483683857,80385598930,171149253744,109846025058,22687733019,
    212383072911,129217718127,154480087418,180208855750,920849828,107398313417,145635398099,
    30467433623,200832721542,135097377206,140448969679,142655304789,91486288,58559402864,
    131744475458,64723943632,179221267761,173554570305,126644654334,221719472690,15593094983,
    183596555069,94161323361,73484178080,151726619164,59301794290,137375443849,176514240101,
    58969813146],
   [251849279780,42336247110,265945423075,120568029915,207363021194,150352220426,90672850827,
    129065877095,43920251245,63589143664,152852206088,29389303644,211592048283,119650219505,
    218601077910,178777108708,184051914609,196397561269,123299465388,174219922394,60281437165,
    120463607809,6694678754,34005976714,33973867016,74153075166,66585008953,175896793641,
    93230764618,240509572206,107503760415,250251968183,103190476430,202802674718,87750228139,
    117226664779,63155586526,14396497280,28273808049,86132559666,9408294761,158509806907,
    40973512126,191042768866,51355331663,184867117985,37469386704,153206553310,13021650169,
    113242342355,6056628267,72173858672,9229745826,31690833415,3497884818,6953226177,25924350697,
    42441243388,51224484562,75277803615,74520495769,99716058040,79260036624,117609404365],
   [61924585675,116854105760,20097304552,95537660265,25304665906,47585096772,58398314617,
    18577741468,70819943340,85478669047,63882682939,135705680548,45817134614,152731960299,
    16898682021,134067157446,21014060979,85269411209,62918837542,21633175528,93426342451,
    43975984082,103685894066,94152554217,87473706903,125050579516,59132050990,130970688761,
    31640123995,111125672516,5306326850,77591250899,21750648718,43667431842,50256247053,
    19549335419,73426075570,5074848844,84995558047,6069822318,87261630996,16975311557,87930505977,
    25290821358,90283381868,30106167447,89273593483,37873610974,79888862390,52615736347,
    57148955781,74005095208,20571181652,97212416305,24166719452,115772274822,67486487271,
    126010622061,95887854746,118859217090,109480199009,94375162437,109993372080,52058571112],
   [106344039183,1038490583,99896117934,49489300747,88606404469,90670333366,71337993074,
    111358719175,41945146415,114420457274,8057311148,100400375025,23179740318,71708710928,
    50233032645,36579997677,73052183160,4130038216,91723627773,17171671616,98157362770,
    34907658797,95723947989,52857943388,90918882648,65902013801,84586025875,64728112424,
    63675360978,61459653953,32135975375,68811543126,6433298360,90018355207,7403880163,
    104405774142,24687396090,105408903397,41322343811,97704819734,46007990674,89179809101,
    36565155953,84957706804,17384140212,85499575121,7071102832,93125208936,27254891621,
    103502924865,38831816018,110546148488,42866527063,106879309001,48940729920,93374360786,
    64450796579,78889048675,81151891956,58959844530,97247300623,29576856527,119189756110,
    2457901624],
   [139887273729,15138499270,146161401520,30575881315,137877538501,48567404436,115087665842,
    83821698247,97438616747,135008493996,107235787256,175806732547,139866561805,177424753038,
    148633460692,172615313605,135674707245,180660158812,123636854770,188867498097,112352633193,
    194456153462,104262763528,194012535141,101210882927,181562138272,97873230368,153690539085,
    74840555185,137808713144,47964903424,137512070317,31775971863,135767656368,6075928838,
    162644846861,14037386353,175254382116,39576762160,149604090151,35011436277,123788533882,
    2090651042,134310994123,12393232766,161443101748,12942323996,161974917845,46835566603,
    132029492378,52387140632,118772068543,65988172281,100094285428,71749230756,95628220201,
    103545220615,52830340676,102795193246,12623024351,80701077363,20043572763,30436036328,
    13932251692],
   [16061349042,42525252096,17201670282,35920742413,33687774245,4462400942,7610717070,11032643331,
    1671027824,33962215606,38102393064,6865515374,28977596245,40109226939,15880645059,28164275948,
    50789903318,18878502552,39646658343,44313184767,24644382308,54527063066,48226966741,
    159744067213,75369177091,142026913622,192168914260,8638142123,169185568759,64004279587,
    118599681486,81755088208,118284426453,175926101255,9939489929,132474956880,68572434526,
    50345614637,4498417716,161672842466,149637902308,58652820955,164393692015,4402033529,
    151759586506,14799711521,357845799859,430961305087,126449964837,148540369788,21727787928,
    344489782917,478719804749,221590178773,80342116668,36110742212,284268926071,451632861371,
    253140417061,16946309180,47510901711,398864025613,570239829789,289062042851],
   [135683402326,171117390142,279555707543,733111421731,677012260691,169909162551,208584379080,
    24385114458,480011781525,646434606969,220391811527,246105746290,12336845596,845985245307,
    1329519134225,661662992305,564572412556,795661579044,635020801217,2261459575249,1672243582659,
    1611163749286,4665149047820,3446809715922,2621751538259,8433743806987,6791985710073,
    4209331204346,16859547462538,18215563053052,1461362857868,24943983816725,39735248318263,
    23802335127323,22367202047352,72798856547538,88746830812444,43765652373036,54826137823583,
    162858380110961,218026550346171,170294222495045,7087331159009,239848818463906,508120206926724,
    730289062445766,858243504156516,876123892790934,798922724937782,660780438078844,
    500195733231172,348424570041766,224024976631230,133132016624146,73117892730668,37059487448782,
    17285921491718,7387604950524,2874611983314,1009257204544,315593369956,86197609658,19926579682,
    3678391920],
   [469843966]]
private def pvm_s4_11 : List ℤ := pZZZ 0
  [
   [36396255138,63602949711,59700033412,32625467188,206434635500,233412088698,349863855618,
    217209696704,99323965201,39797379759,68346757171,33876559091,140335334642,91615062539,
    71519708489,14703814596,128074572106,65504228352,174861729619,42018086487,114433497370,
    50758355002,15942009237,48866444045,27907515944,78187429812,2562413765,58315459179,
    12063138093,88031205100,20262143582,142017579495,28157342865,122932779956,7590206732,
    70883374327,10693481803,42923171244,36397725252,63594845995,74362025751,90707376060,
    30104586980,126193369365,2713399230,153987984450,25100338407,115756270765,48633132626,
    146476818476,17522556104,8734133533,188254478068,235277811724,124359367914,221542143784,
    443354399530,378324323764,238529781720,310666304168,303927096912,59525599832,177884114993,
    195111059497],
   [175159203871,279799298059,240187659537,41332036152,201931184774,150263647704,215320382722,
    234486127782,85086406845,293486501749,178893651201,105084132767,34439427855,172618306646,
    255574795066,124199113574,30266271275,175333901671,237699464975,72737547409,116251911998,
    176582174770,184357570556,12767278162,229754051283,181700410479,7268968366,80329281706,
    153133293020,159476061250,66436286869,237230354289,117349662325,52289121196,154109822108,
    195051345602,9374875299,257457118849,150244405185,90686991272,155728584204,128932913904,
    2846475227,212438813483,171474908693,124629297862,224393320480,28945526052,116898933143,
    113561312781,63352404373,67814530848,179716639132,61513600418,170368614305,185439834811,
    59881016242,214925417558,66832456570,121648747663,129908634087,45164239387,96723839828,
    196136417362],
   [11023876708,263365421241,138079593883,228292496372,217495946584,122931304799,211112365825,
    2278686811,124209356920,100700396924,8747970274,137836318915,147295168073,99129989826,
    250923615836,11924564147,297550218397,77006259635,276890119934,122975989648,198411562985,
    108834025117,87958573618,45369039370,23180344212,40823192010,114818373101,123772019997,
    177910486840,182555657070,205566797667,200715413137,192379389104,173615946086,139362265073,
    110847558901,61452898492,29262474880,10420433796,47787488128,55736065399,110043087161,
    65106238558,150766332304,46997338983,167742491287,17359661482,164519802214,13028064298,
    145201074993,36435498587,110150739170,37396904098,67843252311,12448746819,20994927310,
    30206948649,30444829276,74608485652,78735800473,97945896081,117509722124,93256889532,
    134478913603],
   [64018715607,122696471464,20083350662,85651556025,25491368110,30866717164,63535129771,
    30323169908,85084857830,86916848673,82285560345,130357751750,55857051296,151874138509,
    17974998627,139840293660,21834876849,97833658725,50207326524,31937584872,72202165135,
    31444112284,84327540460,78657904041,89753506581,100204122764,83997515490,100942075667,
    65066749373,91228424188,38910096450,74949026753,10707633661,55918700950,13802143835,
    35775667293,36757916184,21492986288,60017705779,16465190379,85681711648,22275493842,
    102865209061,21305591367,111913817602,4913206572,112670658363,24681574292,103430492954,
    58004670071,82683554029,83715023404,46649719826,101254194475,567365266,113582767750,
    49072753357,119800146805,89599408692,114481685512,117349808759,93851016487,128645375466,
    58009031260],
   [120040867325,9145764219,95288897796,43464348783,62071457017,87738630046,29951529620,
    111763806369,3254781503,111292787156,19193979437,92491385297,36728831916,60436249858,
    53677891525,25506204909,66437619544,10283455009,75437543185,41492878450,76380629276,
    67471772499,70503486857,85464065634,62340738802,88285788307,47578812685,83291216502,
    30726431974,77118306789,16441306843,73858471456,6548953300,72414860805,4525271838,72739304994,
    25541075275,85138885075,45993266188,106307934904,52815500249,120357442169,45035708958,
    110445356852,41845013537,84030033653,53214066830,55396903168,77431989447,35868360495,
    99926664204,17421061476,119700730399,506378549,129409385896,18233954759,125275881841,
    40012821592,105598777086,66361708927,74898325879,96055358902,42598028768,120930622485],
   [11629040103,136441107796,17875470263,141569086755,48635323090,141964569032,75727809185,
    134623999773,98677741128,111255048350,131191692873,81659343113,175276161086,60219104754,
    217236545211,49740902581,243932291480,47187233476,244356650951,40760337749,217883037660,
    10466001758,194268910705,30982259100,190672684846,54668027625,190424878809,55379382040,
    168943062288,63348629195,145232025509,73387596002,118822004926,85417826307,86283965611,
    109227303708,61934895586,136417019717,52771517457,151708910346,51408360434,148996726193,
    43981346305,142200649720,39793452806,122512375261,22340374355,107098855384,13530409039,
    136269779661,5450788966,155892155218,29705974862,140141202143,51305379335,107557674898,
    43892536346,91024323165,32609890613,90127654070,41193296914,74626159411,53686702381,
    36152967360],
   [42302477836,4212510597,21003910275,23618193717,25912005113,1729855706,35436675138,18764478670,
    29427244139,42405683723,10695013163,18425312346,19803675442,13217455460,15754168134,
    15683306732,3250719956,13463195423,30749500897,35707531695,7921713910,77262527312,61236410264,
    54700349127,94040391169,31732028942,117235257798,8704400789,144463971215,30659025149,
    177160706922,132339899502,124899678557,215106870455,20999830241,142006501724,42079778190,
    114471165095,46661638747,130912772970,107933883504,86897495909,130200080433,32033871010,
    82545974942,99658025275,191162997451,29589583100,261951981098,141668463850,152231128581,
    149757466727,175624220904,336209815696,42943418522,355007871697,351827315055,1374096883,
    159736412314,117209001645,437009076671,345723902313,1503032897,66344777814],
   [248375795445,468344925225,243893051171,113772603636,55933154034,416963759899,702842491945,
    381427528077,185669585276,263395363584,297149091705,796792374547,572118238569,68729607232,
    192667702250,446273951071,923827443905,367149233037,639384160766,575454962062,893795896061,
    2008567381243,939399029499,1421716648656,1834026543448,1255760771337,4672805118581,
    3239907774133,3522285521354,8674639605086,4331456984542,8048249578531,15708978025089,
    6377576696451,16251277941730,30786340717648,16447881020966,23298509809503,55949068891417,
    43934782574555,19644540099484,95065156312722,118210591985374,48304252074592,94199959977793,
    229665637712015,262407728543453,136671088522253,130551389570380,458353212752494,
    743301632254710,906541700106630,921470593481438,812715106115268,634219624970302,
    442315168596376,276936435612698,155763925313216,78489566214126,35210930093256,13910155356564,
    4753746253762,1363648406866,310119027956],
   [48494914202]]
private def pvm_s4_12 : List ℤ := pZZZ 0
  [
   [93187363596,44524139943,19755442452,9369262007,67665218417,62314370726,22622601782,
    86051225651,205606067576,243872509002,251892345748,307098083508,156398316554,42521573280,
    69310915583,103590366115,77168623812,107588629704,66866214827,132968305111,46904847703,
    86095267256,112307418146,224154934,69522409623,55737716253,3364898992,92939467496,27142115560,
    103170664281,13693703027,132607714580,34660309174,64340665467,44353731847,36682465802,
    89254261910,43445038660,108233646141,67632009157,100309705560,37793241668,110788177739,
    45670943663,113987802054,51161608308,106237601589,57896726569,106268666710,71873504860,
    126907516687,88536625629,100210219858,49854789624,89936411969,29187517997,89968331146,
    25067263772,91077557507,27783615585,105264589646,79725821546,57230406563,4513405231],
   [197610149190,161267780362,45786165730,219159939948,388413811910,306705285410,298605163670,
    428848554512,355578317220,141972807884,67413851392,13404197595,191876459303,275309674759,
    278784649981,217633900609,8731580763,166435447262,201016920616,234961932912,190437774626,
    43143061167,219982549923,196723165643,164594330045,88271448371,168111220626,300985388100,
    134759581568,33899670593,130488673571,227541400929,136375013615,101933334394,186419678700,
    133194500880,69227382260,90777569247,255356956855,141322393551,135810639098,213798312938,
    108644768286,14317349135,167862667043,221670348941,11627056161,236953610832,205205429526,
    49071978255,206547984971,123916145487,27554744194,111496699882,147180224612,52809589276,
    170266204549,210144044269,47656884310,227365646726,91836114622,93840785293,118985586837,
    87247616397],
   [11225933238,195181408044,153674380944,172901623673,274806505929,42026428558,278589190534,
    99723408114,172987507207,161170778467,17104515558,105807263536,117189445840,36016289636,
    180539225265,196133305413,162150317098,307384970922,89974997281,333543941881,6162476638,
    264781486864,45311443806,122479777903,40411722227,44128145135,11160275311,179606569710,
    76676391570,250177018549,129648570035,246524571260,152002880236,190336349475,143828102565,
    109142682306,108836509808,27534563595,52249717891,36387218871,18615118153,66700517424,
    88845637278,56855287617,143245744083,14868331402,173549877034,37668725746,178322002511,
    73180412339,161599152894,75342958996,126085512583,45932334459,71588416420,4652066255,
    7920692845,55992605524,55762087441,96638663731,103917287022,116298052624,126106163247,
    105802523449],
   [123955109446,66539469296,102003513435,11664074659,59055771852,46523889005,3052924903,
    89348006660,56779652071,106294692181,106829429666,98290287392,131540606489,68565970431,
    130442100142,30086615986,107331787473,8045474766,70742779028,40627439167,28640798453,
    64801967494,15077819367,82930187313,52280310982,95649248718,72302127257,98927730257,
    71443946710,89625596228,56732446451,69836719999,39976089476,41510880746,36556914179,
    14263939627,42356787294,16892239359,55604727567,48070080918,61640494568,83344425781,
    59100834709,114598963308,47242677798,132196721303,25691237973,131438758908,4824391323,
    112293369487,45147561932,83357760138,86830151229,48769108107,118140154704,7842722706,
    129048184283,43609100876,124992562768,91087014543,104998194995,123027708078,74086623204,
    128085556953],
   [34606818367,107071753308,9715869297,72142142069,49498341678,33069571674,79210278335,
    2441900818,95972536690,29561265927,97346157451,46136254472,79820005628,55037184105,
    45038749771,60080889398,2111048414,61195258829,38584156704,57940435368,68080769381,
    49578549289,84831851466,39693264742,90331096689,30942463491,88750383162,22840932070,
    86351908739,15984408809,82289896222,4034372146,79358187601,12924988598,74753782112,
    37149690953,72424856357,60750994708,69243356192,79963363199,60847953217,99796169830,
    53644710350,115725342733,47580880061,121824718058,37619494278,111027028943,9852668121,
    90297401040,39389030659,75103503927,90441068962,64596840882,124519425947,48923680391,
    134490297338,18878673154,129043657347,18581006880,111620880906,57222494247,85315978193,
    92397080614],
   [50869047822,126706298977,18375592399,150051844824,15666370799,160691478685,51305991076,
    154896790004,91746619913,135944543969,133226833806,106549509578,169162603627,66732617267,
    198466771164,21502727436,221945253869,19476016018,239034830914,42946161983,236514322193,
    54096166992,208710629458,69002921329,167534489089,92713882176,124844480510,123939327637,
    91691706517,152503839036,73399205066,158278981071,53379698559,138996671256,11363913046,
    121103803393,38322025934,114059619604,74809355011,106384230001,97988948202,93152433494,
    118692310417,91161740065,118671618692,82920701936,108179793695,62180877857,103778749534,
    38544985448,108160044127,18927862029,118444794412,6571985184,132081396069,7502408359,
    142457585884,33646685356,114043752453,43840299771,65542061666,15324666520,52633783119,
    3093817995],
   [49205740176,11766751300,35929058727,28527006029,2737836550,24731397268,27721449010,1902889468,
    32705511657,28415782981,16802992602,40628851362,7075040148,34501124211,29904966301,1438419883,
    11440128296,13974403368,5690000452,23430155133,30270605099,7851893874,10769812298,43017775487,
    21076378869,95318817084,95661967852,74352840469,139079988471,31307268022,146822421726,
    1182899827,148807508649,17870803779,176494203942,84159442854,162948035109,154563673229,
    100730345276,185084026336,13875476089,129084389647,14022339318,99297340824,63876472789,
    169407294457,5076343646,159514094668,17763031730,148915547291,7078864115,211774068648,
    86751106068,243082080623,257309694091,96127818710,275995018592,4348957153,292659795751,
    90327750291,337968417286,348744169034,73137125705,293203666485],
   [34963022539,204825021934,18173823361,382593631241,329634847283,36794424940,100399555880,
    300664969233,575070040987,245995765649,264704956378,165717332978,510206047119,824591964791,
    269321862483,377173507226,116107678056,705391957113,790772868919,87633095154,514305598086,
    463095015089,1528492650667,739215199905,1250482277572,1412749587832,1277078772611,
    3334388400853,981284134061,3572101451924,3422336245432,3490201510601,8951862204825,
    3319136713451,9908062002598,14008500788842,1242898477435,21997625014829,20699607944875,
    10826461567420,43061054850720,33757892695518,22941250564389,76873922730465,62535075134681,
    31754684589508,135261765593128,144286564384712,13689088540346,189210648403867,318998480731421,
    250790012355613,32992862471944,430449178956936,784487500689062,971697362412590,
    956829392841136,788785332714716,555974379013292,337368572222636,175755511176828,
    77639241126626,28326423339272,8084547955706],
   [1568850340988]]
private abbrev dP_s4_0 : Prop :=
  bSlideChk 13 513 phbVec7_4 rkmMidHiHiB_m128_r512_s4a pvm_s4_1 = true
private theorem bk_s4_0 : dP_s4_0 := by decide +kernel
private abbrev dP_s4_1 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_1 pvm_s4_2 = true
private theorem bk_s4_1 : dP_s4_1 := by decide +kernel
private abbrev dP_s4_2 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_2 pvm_s4_3 = true
private theorem bk_s4_2 : dP_s4_2 := by decide +kernel
private abbrev dP_s4_3 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_3 pvm_s4_4 = true
private theorem bk_s4_3 : dP_s4_3 := by decide +kernel
private abbrev dP_s4_4 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_4 pvm_s4_5 = true
private theorem bk_s4_4 : dP_s4_4 := by decide +kernel
private abbrev dP_s4_5 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_5 pvm_s4_6 = true
private theorem bk_s4_5 : dP_s4_5 := by decide +kernel
private abbrev dP_s4_6 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_6 pvm_s4_7 = true
private theorem bk_s4_6 : dP_s4_6 := by decide +kernel
private abbrev dP_s4_7 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_7 pvm_s4_8 = true
private theorem bk_s4_7 : dP_s4_7 := by decide +kernel
private abbrev dP_s4_8 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_8 pvm_s4_9 = true
private theorem bk_s4_8 : dP_s4_8 := by decide +kernel
private abbrev dP_s4_9 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_9 pvm_s4_10 = true
private theorem bk_s4_9 : dP_s4_9 := by decide +kernel
private abbrev dP_s4_10 : Prop :=
  bSlideChk 13 513 phbVec7_4 pvm_s4_10 pvm_s4_11 = true
private theorem bk_s4_10 : dP_s4_10 := by decide +kernel
private abbrev dP_s4_11 : Prop :=
  bSlideChk 12 513 phbVec7_4 pvm_s4_11 pvm_s4_12 = true
private theorem bk_s4_11 : dP_s4_11 := by decide +kernel
private abbrev dP_s4_12 : Prop :=
  bSlideChk 12 513 phbVec7_4 pvm_s4_12 pvo7_4 = true
private theorem bk_s4_12 : dP_s4_12 := by decide +kernel
private theorem pwF_s4 : muxFastIterFullT16 167 513
    phbVec7_4 rkmMidHiHiB_m128_r512_s4a = pvo7_4 :=
  pChFull 155 12 513 (pChFull 143 12 513 (pChFull 130 13 513 (pChFull 117 13 513
    (pChFull 104 13 513 (pChFull 91 13 513 (pChFull 78 13 513 (pChFull 65 13 513 (pChFull 52 13 513
    (pChFull 39 13 513 (pChFull 26 13 513 (pChFull 13 13 513 (bSlideChk_sound bk_s4_0) bk_s4_1)
    bk_s4_2) bk_s4_3) bk_s4_4) bk_s4_5) bk_s4_6) bk_s4_7) bk_s4_8) bk_s4_9) bk_s4_10) bk_s4_11)
    bk_s4_12
private def phbVec7_5 : List ℤ := pNZCat
  [
   [76573671532343,108125331322157,132222377053201,152442162871726,170172653633329,
    186126813633193,200728836582511,214255534306650,226899475270158,238801080850051,
    250066518514009,260778394362752,271002499542155,280792257275035,290191761802096,
    299237918826360,307961992414061,316390748017345,324547313546718,332451839156797,
    340122010468097,347573453183080,354820055952082,361874230829432,368747125472352,
    375448797590134,381988359548437,388374099147792,394613581210512,400713733580637,
    406680920367251,412521004673091,418239402598810,423841129963507,429330842908991,
    434712873340169,439991259983372,445169775708169,450251951648670,455241098571654,
    460140325866776,464952558475006,469680552022957,474326906390560,478894077906224,
    483384390335764,487800044808081,492143128800926,496415624293520,500619415178732,
    504756294015563,508827968192457,512836065563218,516782139609784,520667674179633,
    524494087839984,528262737886103,531974924036792,535631891846476,539234835860058,
    542784902533928,546283192944017,549730765299621,553128637279797],
   [556477788207449,559779161074708,563033664431891,566242174151132,569405535074737,
    572524562557357,575600043910252,578632739755169,581623385294649,584572691505032,
    587481346257829,590350015374676,593179343620623,595969955640129,598722456839766,
    601437434221286,604115457168466,606757078190799,609362833626933,611933244310476,
    614468816200613,616970040979794,619437396620573,621871347923526,624272347028049,
    626640833897681,628977236781497,631281972653012,633555447627911,635798057361856,
    638010187429519,640192213685914,642344502611040,644467411638756,646561289470783,
    648626476376631,650663304480232,652672098033985,654653173680890,656606840705391,
    658533401273538,660433150662995,662306377483435,664153363887803,665974385774906,
    667769712983761,669539609480118,671284333535526,673004137899317,674699269963841,
    676369971923280,678016480926331,679639029223066,681237844306221,682813149047174,
    684365161826869,685894096661892,687400163325929,688883567466817,690344510719372,
    691783190814177,693199801682517,694594533557623,695967573072369],
   [697319103353599,698649304113195,699958351736049,701246419365047,702513676983205,
    703760291493051,704986426793391,706192243853541,707377900785140,708543552911632,
    709689352835515,710815450503434,711921993269215,713009125954905,714076990909906,
    715125728068265,716155475004197,717166366985903,718158537027746,719132115940843,
    720087232382144,721024012902029,721942581990502,722843062122012,723725573798963,
    724590235593950,725437164190772,726266474424261,727078279318972,727872690126763,
    728649816363319,729409765843637,730152644716521,730878557498120,731587607104525,
    732279894883478,732955520645202,733614582692396,734257177849415,734883401490653,
    735493347568178,736087108638612,736664775889309,737226439163825,737772186986732,
    738302106587765,738816283925348,739314803709504,739797749424168,740265203348934,
    740717246580227,741153959051949,741575419555584,741981705759807,742372894229580,
    742749060444778,743110278818343,743456622713979,743788164463412,744104975383214,
    744407125791208,744694685022477,744967721444962,745226302474687],
   [745470494590604,745700363349078,745915973398013,746117388490634,746304671498933,
    746477884426790,746637088422770,746782343792609,746913710011405,747031245735502,
    747135008814094,747225056300544,747301444463432,747364228797328,747413464033317,
    747449204149253,747471502379778,747480411226091,747475982465476,747458267160610,
    747427315668631,747383177649990,747325902077090,747255537242706,747172130768198,
    747075729611530,746966380075079,746844127813253,746709017839925,746561094535668,
    746400401654821,746226982332363,746040879090619,745842133845791,745630787914322,
    745406882019092,745170456295447,744921550297079,744660203001739,744386452816799,
    744100337584662,743801894588026,743491160554994,743168171664047,742832963548870,
    742485571303042,742126029484586,741754372120382,741370632710447,740974844232088,
    740567039143916,740147249389739,739715506402323,739271841107034,738816283925348,
    738348864778246,737869613089486,737378557788749,736875727314681,736361149617801,
    735834852163306,735296861933752,734747205431627,734185908681807],
   [733612997233901,733028496164485,732432430079224,731824823114881,731205698941226,
    730575080762824,729932991320720,729279452894020,728614487301353,727938115902241,
    727250359598343,726551238834613,725840773600331,725118983430042,724385887404381,
    723641504150791,722885851844141,722118948207226,721340810511171,720551455575718,
    719750899769412,718939159009676,718116248762776,717282184043679,716436979415801,
    715580648990643,714713206427319,713834664931967,712945037257055,712044335700565,
    711132572105065,710209757856675,709275903883898,708331020656350,707375118183360,
    706408206012459,705430293227734,704441388448077,703441499825287,702430635042068,
    701408801309881,700376005366676,699332253474489,698277551416904,697211904496382,
    696135317531449,695047794853746,693949340304933,692839957233452,691719648491137,
    690588416429681,689446262896941,688293189233093,687129196266623,685954284310162,
    684768453156150,683571702072332,682364029797080,681145434534543,679915913949613,
    678675465162710,677424084744370,676161768709654,674888512512350],
   [673604311038973,672309158602564,671003048936276,669685975186736,668357929907195,
    667018905050443,665668891961493,664307881370025,662935863382580,661552827474511,
    660158762481663,658753656591792,657337497335712,655910271578158,654471965508358,
    653022564630309,651562053752751,650090416978816,648607637695364,647113698561977,
    645608581499613,644092267678905,642564737508092,641025970620584,639475945862124,
    637914641277563,636342034097216,634758100722794,633162816712898,631556156768056,
    629938094715297,628308603492235,626667655130660,625015220739607,623351270487893,
    621675773586106,619988698268013,618290011771392,616579680318237,614857669094344,
    613123942228232,611378462769392,609621192665828,607852092740879,606071122669271,
    604278240952402,602473404892807,600656570567782,598827692802136,596986725140034,
    595133619815900,593268327724346,591390798389075,589500979930741,587598819033700,
    585684260911631,583757249271960,581817726279060,579865632516156,577900906945900,
    575923486869552,573933307884702,571930303841494,569914406797262],
   [567885546969528,565843652687284,563788650340486,561720464327682,559639017001690,
    557544228613237,555436017252473,553314298788265,551178986805155,549029992537896,
    546867224803438,544690589930249,542499991684845,540295331195400,538076506872286,
    535843414325406,533595946278155,531333992477842,529057439602402,526766171163208,
    524460067403787,522139005194223,519802857921039,517451495372307,515084783617738,
    512702584883492,510304757421420,507891155372429,505461628623660,503016022659130,
    500554178403469,498075932058374,495581114931347,493069553256292,490541068005476,
    487995474692367,485432583164785,482852197387795,480254115215725,477638128152616,
    475004021100410,472351572094092,469680552022957,466990724337106,464281844738222,
    461553660853572,458805911892126,456038328281594,453250631285054,450442532595782,
    447613733908743,444763926467090,441892790581878,438999995123038,436085196979483,
    433148040486057,430188156814789,427205163327725,424198662888332,421168243128201,
    418113475665468,415033915271013,411929098978125,408798545130896],
   [405641752366122,402458198522955,399247339473963,396008607870582,392741411795173,
    389445133311093,386119126901187,382762717784052,379375200096212,375955834926932,
    372503848190834,369018428321689,365498723768696,361943840274202,358352837909138,
    354724727839326,351058468792220,347352963189528,343607052906305,339819514611533,
    335989054638661,332114303326874,328193808764895,324226029858449,320209328629935,
    316141961643885,312022070433889,307847670785253,303616640701817,299326706854154,
    294975429268345,290560183968107,286078143225955,281526253008459,276901207112841,
    272199417382102,267416979247120,262549631667794,257592710319458,252541092578996,
    247389132484738,242130583343467,236758504991756,231265151822432,225641836465802,
    219878762329159,213964815835528,207887305838750,201631632816731,195180863239000,
    188515173619748,181611111916861,174440597121069,166969533839447,159155843688976,
    150946582148012,142273561018422,133046404601128,123140920039965,112378218915938,
    100483611407155,86994477418143,71008376935843,50194465149998]]
private def phb7_5 : List ℤ := altBuildHbFrom 896 512 56527592592 0 512
private def pvi7_5 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s4 pvo7_4
private def pvo7_5 : List ℤ := pZZZ 0
  [
   [37576374394,12954720874,8860201547,20057005969,34846593960,85640490624,81578146368,
    43766951366,7799079259,12298976929,19495639706,37434132440,42378304680,65099728034,
    84711859132,51317408962,3147513275,32390896903,47761716979,10797412713,44131022393,8008820461,
    37036467813,74520105961,85244615119,44299521323,37847240332,15095459270,88551457713,
    89022765443,6316817901,32171777992,84116846366,209979739994,303858959588,294332025756,
    215801392892,115805693898,37534271172,10334108202,53003653122,139132686990,169542179446,
    105185985460,2397863394,99005048953,124850062179,7041414285,126079735688,78004586574,
    92464184979,145428167765,4201664283,137515630120,104811371136,26996488173,108067531883,
    76607532915,55914184534,132039308348,512824313,150300559129,43048300517,152752885264],
   [92540377186,125047737433,132603925157,54015162302,96104311880,31830399011,59047885941,
    28689591348,53550691314,27604222658,10356211972,32666799145,41420786303,39993346712,
    69376905164,29978058431,80682195175,8401038118,50852874340,37359509003,54500481195,
    54622508036,66628700420,37056520003,42135841633,27165239204,8379821372,31673276563,2209915216,
    17742413338,27345406677,33239452199,19247201566,31615374072,14736175215,27455638925,
    4909773160,1774341154,31511340575,5119547209,42724840976,46067059178,33615522035,44270047033,
    1942945648,84194325858,2056589413,32699516827,70741705824,141068747674,157976169688,
    129911905114,355987992724,399987313982,386315274624,395258344712,437479265760,386593926164,
    90664879638,145937477237,216372117055,254525142493,291509405625,221286033595],
   [52669492896,295083163708,256036984072,145464755702,83375334224,97631938905,367125976899,
    295029475081,86819986438,326061952856,148743231516,21291596542,3555063639,146531060193,
    298471820543,63131073241,323551312650,254263161236,70397427019,134594964903,124732705869,
    137084637985,23046618320,297442815468,218055185164,204658616225,331291163379,32570469933,
    236606133422,192240654372,10395039407,165769808735,168977028669,21904866947,205412187254,
    223594854680,90167052971,325766279053,95693431095,291829647494,223888124632,146863449705,
    225821913221,1934208293,72289346444,89753431242,81046223918,43946128325,214193158503,
    34186761466,258517261242,3615250253,271213948085,58798084303,179770138790,65045419320,
    81510981061,21613217431,78154271669,45594865855,120212136000,22773181274,189389362135,
    93719880295],
   [161292001358,93385358718,138467710407,83483856843,58744956596,26323678506,16727904102,
    40824034466,62122246059,97211909745,67064953828,118612045402,62495664419,123854784351,
    54974863532,129429313626,27995909377,109174492469,6264023874,58404999136,28233719207,
    40377260009,16457593516,19047459143,36339804137,58381762100,47267751706,96046672393,
    54160726553,106650247400,39446573554,141903501609,14078919041,124689725400,3181437124,
    135395733873,47826111582,63577668992,70494949135,383574329,96062574954,54728498011,
    122986918053,129230595360,114017220870,156608710877,64709638439,151378943132,2071783024,
    122913598105,30312014914,92351781652,45006914425,42460673763,95595238082,30874300655,
    101511376125,50839174326,84751414084,116732535769,62632743869,77001200554,32068356868,
    120936702301],
   [32856867306,80939690112,55698193785,13102589702,33582310682,8593222957,35200183687,
    48615859370,41645278232,82347676595,317050394,74618745992,28848385469,46882910261,32140674994,
    34132825682,29734807661,28402622915,34153092450,13350342562,42066248401,14198424046,
    50493063950,45158077955,58193468895,69359343746,56343470970,93196678441,46852394313,
    115041806134,26926782350,133965870961,6667748693,126061192498,23432877653,85895370289,
    69440676288,35614081900,106311580917,11836308212,100415313878,79712194209,81573522319,
    142369980378,73157136146,136011167697,2221367049,149007692484,32892440075,108105951975,
    77573762952,58386446138,87402116095,30065454036,96968710902,111384868723,97712391327,
    139292199174,39625364394,148979162955,43524703034,142097236408,109170738463,102436503291],
   [136351488182,17507866686,141609963163,84352187370,141188672432,135294895209,62915765881,
    223577457504,41310679624,200907571759,54899317114,195698092732,104065107247,120170293089,
    173653642924,49848170418,203105181105,29734423580,198065937986,103710271645,154804324281,
    155440843552,94214572126,184189896901,23119498943,167256276196,32746720027,121947216959,
    76837343404,63826995298,101737417067,2154636062,99563515014,61362941267,71633825775,
    97396427576,43869138628,125105029127,6835509203,127772667260,42792438829,88228817301,
    69077853732,52311991000,106559929635,4854039549,126227892710,29959780499,135641885937,
    57771782440,111127416488,74171138707,69015844137,84767642556,4088580882,66516387789,
    36066032264,35825798084,19814552233,68862504329,56836922894,33029121238,14166933713,
    72553726767],
   [76930212684,9622389787,10219208637,20577570545,7307667291,36592951824,9106416710,17794349143,
    20898709737,17124237768,10497464094,25670669333,10604208584,25086157664,24051354677,
    22470893041,25430526594,23498015856,18210948447,10519494789,4573943912,7460040771,525899781,
    50652992396,10312753355,78246230577,2673904337,93144118834,6528120976,87430667361,30619371766,
    85004780354,73502351609,84493084937,114876381752,88323725248,147572735615,71165287977,
    210042189230,91264838824,231715665281,115703444965,185497718242,81260464082,130178293327,
    7848061312,129699976600,78722951629,174210358421,56396364552,130642895400,76295267135,
    77995612625,122130916780,32359904062,198786256923,6457609983,252820424578,46104889546,
    337402724275,57894997868,171248396692,214103086058,599359172783],
   [418246838632,127645079527,439201499066,805385663121,392096374224,53429538214,355566438238,
    684383189159,506225432838,331821776767,781684198904,1631072315533,1773025898046,1410571662087,
    1278291256372,1213022826801,609932667304,641324473248,1470386702927,1542383937396,
    2467442276549,3650852935252,3891796390365,2886483019330,280296517805,2748713329233,
    5494426377274,7340108310183,8285782660688,6978895864995,2587174129900,2459256922600,
    6475453425545,2647179650122,3440346490554,12596006508951,19906861565712,21548249240861,
    13501100519336,10298776670829,3111115169686,12268606127306,53962797038585,94526541366508,
    65303935961199,33704067451467,123314164721468,57763492493493,62509708797199,119041517150418,
    60695961487737,71464054074506,108053136287720,161580141544283,24397313057477,137168956085718,
    68044246374833,28931598676293,273485749021158,233445205017886,56822126699237,236235445239288,
    949962049255024,1395722952736498],
   [913269958725168]]
private def pvm_s5_1 : List ℤ := pZZZ 0
  [
   [43452384934,49364124736,106545532874,1820177857,15365526143,76410420302,100639652968,
    21800320692,19702285489,56550217373,69220789593,55773536599,19133419563,37364255451,
    81288582171,40243780885,9665266554,20414771742,28425803892,67956355610,160184357476,
    296110783242,349314977516,238618105826,78381175282,14495074418,20614279058,11027504378,
    78949815466,148600540678,37808874042,107202619695,146386388169,6580613991,29018443664,
    83836938558,53711140864,68921224807,81505685795,37531032522,101030534910,32864023636,
    87254887385,108114427197,29614092244,140977569026,47386660420,128650533995,110765453773,
    80184843372,109985608064,54356411017,97617829565,34271120930,121304570140,53780622116,
    79061937457,90799347807,47770090414,106242578468,37457741521,133170713375,19524360478,
    132125314806],
   [35336049837,137466032237,45232939130,133163630350,20871608093,89811759007,1165502951,
    26613095680,15307721873,11134205797,548831992,12505464347,11578600826,15746579706,43388015583,
    17184544273,64671489866,592553651,79995405485,19089305314,88123004848,1825698083,28118666921,
    55053193634,59093199878,28868760688,124518437524,232201453408,225474436166,257465862790,
    378248017642,407981507028,364337346594,362027243538,278357170148,62234638790,101360402541,
    169859585711,258769421175,324895469801,223219783479,18800242590,207493863544,247858191558,
    215771969056,134658177146,52034255869,253140315547,268836389665,93057900907,68012764496,
    134456930484,206225688422,199574489510,53162897747,311250280007,225167212617,46028650094,
    174360283540,174246845892,123053827672,48991536011,251286121053,210245220055],
   [77559531328,267755581968,126347321968,57200698015,136116130909,89131637199,115085281063,
    80966465880,293106330378,89452133556,236343004287,291596830429,118076153244,207157229238,
    72512669162,15595463005,103414936075,189183870341,34404614185,294796316786,210622401202,
    253844145651,308957977361,110195157940,276972250534,55601059718,116127452141,143509058237,
    126156677737,58197198680,235795288838,56136799158,267805120629,167280160601,139799872216,
    208087353136,103795885549,236113856397,32905755701,143950306000,84234677714,46847330507,
    75629688211,43205941593,3883041581,125999784758,72452771854,158381471699,136171017155,
    160554325122,172594817104,145453933301,171073334675,103865466078,128562406452,45192915087,
    31122846965,25548591961,89203089679,29723174982,141119228268,64406813623,183855125825,
    66931077254],
   [165175266674,60413844769,108628284195,43200239674,19110735960,30711557935,32850137054,
    22984637344,126562135075,21370273716,136710627916,15998469889,146410284053,9818809630,
    134082748328,8413311125,108520050817,44466181658,49739949212,26298199089,17348248013,
    22548233168,7416512739,29677703887,36228052552,38155920900,67334805229,48784436885,
    99509973256,70258586482,109657738429,83012909743,81990105546,33012012738,97918642277,
    19301574507,63293312082,35311061313,45022666057,79169222246,21229039164,104393712393,
    33253616750,152136933040,51397745427,146114804761,85815465630,119356718128,110755341289,
    67604055061,122617022526,6007438788,112759191685,52375890296,82006849452,99872973037,
    34833127275,122342129280,2512344268,146700585131,57485276052,97276981556,50117746157,
    83538287649],
   [64684083554,49910630768,83509064693,2660094969,73525217608,40856515343,43427180097,
    71088103116,3467732191,76801111701,26976025222,82998160460,47767552871,62570744001,
    68885852174,7171305432,59569428349,9409073242,49153194352,16606510573,6542536662,46046016414,
    53295150136,95218706945,7952094082,86464501074,4339635637,72069399783,34921355251,
    116271269260,20794894862,116370884803,4415619311,82414026850,31396894429,72507587985,
    51712415272,54523083328,63119962137,4362284567,96265663678,44648647461,131373257623,
    77178827238,149637192548,67431310637,78738503671,126257755272,67034637986,100716272123,
    15361488560,114814392138,45757236245,71074712439,98221191760,34571390156,128331284797,
    10786497394,143881642072,50919537811,135480709159,80220174298,92354669394,106858464171],
   [24376384749,129880626190,50226823589,139452175303,114718927580,124370251076,159476790749,
    78686503785,188197744662,17292914414,196477746253,46277038492,180379377874,106000653591,
    143992136267,157852888610,95461200000,198267579189,45023194531,218306308906,6543691787,
    217006920247,55572823428,194876158012,97338713639,156041961669,122098885936,98932656622,
    131616879103,33133711475,125167348236,34931940231,113256485385,86781737676,95541790884,
    112513032015,67807838769,113863011158,26206679442,104276165059,24764678884,95608301010,
    69946921013,92529780233,109632879376,82975765190,119934395677,74740531467,116732217486,
    46106558420,112102189455,3995468163,105483727076,25756826869,91081831953,40472801818,
    82434149476,71106148555,68872434679,87929762476,51689192056,67192406131,44833068179,
    46952985292],
   [25775455502,9521002919,22207201563,195052567,17055417038,8481084365,10452505233,23122197226,
    10759214479,2647594388,2066988977,29284658625,35197615114,44263384400,11660874675,59363030979,
    28266433156,24072568189,50375069142,7301843331,41883936406,38993581375,23980560665,
    41375239238,17596238876,52086162165,44227292561,44008404582,39776589000,43922884259,41946573,
    92264868228,24145157439,199101683815,74496384447,190577629064,130891420114,139215134925,
    121386439003,136684956116,90661216886,146418581177,104399353879,158926303014,132406224606,
    125811867515,112850474331,97962513846,64713591956,101919456405,14100737481,156703512906,
    20723060130,201292966723,58210186137,226011690230,116537294844,199797025963,110808916049,
    243991514952,166133470040,277070644953,296066808137,176898816546],
   [321846805096,92057741069,299268127431,61386964108,315099011808,13674484915,347328244661,
    114003047211,250203175708,72321053408,231570534309,189531617517,753165884800,149828067021,
    104502597062,732148767773,699676246954,168785373777,54327724368,590901622743,72180144774,
    773554747905,364522605570,2325024805879,1619254448720,1861850902655,769955395922,
    1272948540879,422814543364,718515712913,4189635413779,2707481546430,4378668055527,
    5130227977886,1248644988309,236843647675,10270246401686,6568519170699,14590630151600,
    2449742974682,1690577972395,19891022924874,16527634154062,7575737411697,21467826392096,
    36952345668724,85193706844170,82508811581985,92346816944711,103744771218698,51856007963609,
    32264824748134,201113437913088,54551387046178,4590450715868,342752773645690,285404492296820,
    94356660021280,294085957231750,769268191084234,1098240163703356,1060796883863722,
    734187179898586,392555218756344],
   [76160022459582]]
private def pvm_s5_2 : List ℤ := pZZZ 0
  [
   [34710437812,12998735333,39227006408,96021187170,77509914294,9690364157,15612712153,
    29130392598,71446672104,73309252664,50824751590,38825233774,15039269363,67601983543,
    55315063273,18899648821,25779894605,52464806779,63823343527,61468065363,32069658997,
    1131968988,10119110164,31518541813,58271403369,96864167320,219580430640,297666261274,
    255391221490,252170967850,183160990398,12658258152,32871971421,61227515236,121921350192,
    125771282716,90570962290,17233377109,118074066951,106333782433,2949005409,87301263436,
    69821170652,31145186417,98757082777,44737527087,102100327422,140483604016,33822110329,
    167152247119,52371237575,116476563844,102187618578,37627532103,101881821873,25245479573,
    77056432912,63864747784,67117259513,133338875707,19930993830,172961698454,41207805736,
    135591869965],
   [24679805565,137000899470,37025180450,113272097397,43125168959,79192433886,34319766954,
    52247808955,38592896339,9417785641,6958903810,47441366486,22428480958,46454621669,5435628477,
    52362401912,25145931609,76151829539,21446769524,65656758470,35293818185,67642075991,
    29363112094,45515021942,34250110913,21864495837,29788480282,18235458045,41130563715,
    34675739484,48321285286,13780727467,11284740523,25895106776,9268514338,3773547066,73565946418,
    139710033940,136550531624,154130682338,274391780190,397166022426,409211650530,370320913730,
    371581499272,353369269932,197111107466,44783232851,190719833091,239304773929,314425679993,
    289779945101,37747986865,226074530800,232505607684,189457064198,143194851520,48421498814,
    233523185361,327889899731,148007905237,74791044418,236822073296,161273299690],
   [158060074206,65222041161,286476648629,253851389261,60605925748,296977438652,141484724848,
    32043118931,42212392051,136828134979,217843532347,13250431806,324363499702,212591645942,
    178757797145,249508097559,37818558165,60472309152,93576068052,199876765996,27436203914,
    297941231473,244391215043,237175947834,315197283134,33503348477,237417541595,131296523775,
    50872591022,152872353922,139813504214,31657067667,256789924423,135038912947,203356223926,
    281135537016,39011544395,295270416365,97485931993,188933869306,122269686220,99449290957,
    108481042957,19179895675,21443553124,71764658224,71858842422,140401686157,224945934071,
    79927521000,231329320900,73394054083,231335188447,34329357282,152679992178,11611375449,
    62879692489,4783526440,68330977221,28200285820,138812838172,2298197774,212580446497,
    14776997325],
   [199363070914,19060232840,123854360071,4625268964,30248543418,6771645787,4568696166,
    21487604628,90838038493,73422998795,123408066966,68447474688,135676352713,65267850547,
    116487036306,57141923412,94152529303,56062211751,51474729614,23180821172,33827351735,
    3960901830,16038102712,38985963827,7187993109,65519655348,10457223265,90368166741,34491891680,
    116182908002,46707745157,120127687995,60606398244,112161447512,62576574097,77601633221,
    61739510446,15800146136,68548080125,55120180326,82154650140,104483216789,59947836663,
    137494748608,17801841502,192891389857,15725729320,136366083636,50388965729,141484497265,
    86189828616,57284703788,100247536987,30214668754,98933025480,52139964445,66519967641,
    94331205984,51290081648,111045792195,22665309245,129505549140,19989731027,106329729003],
   [49314402932,57431965746,51151170611,22751632319,68351156580,34982774211,46175730283,
    60157878900,28913064834,97176680411,42937507914,46702080406,28299083599,56049197739,
    31353637612,59649342624,68876737813,4522481138,38841182698,30031346269,23020775307,
    27163530316,34507800022,40242549353,36050983103,75100883900,30155970328,111888315439,
    37682259153,116517005774,32393030908,100431027239,10757875062,121340758094,8864580491,
    78439475123,55051735918,48866815418,85000321447,2791194946,114297040002,47273945729,
    111558440909,95336235330,84528907406,146564708155,71220864433,143064092628,32008596524,
    104792465943,36713473656,68601667250,97710999353,36842801601,122611249758,7486521509,
    105853078181,95574786054,123757586412,107401461059,49410678413,167009304594,24637399428,
    133266705065],
   [62411634016,107385421892,119692789933,39424370313,175580816684,24957423995,196292912657,
    82603405400,174941625558,133182758799,121647024555,172486856248,51086481548,195243923747,
    21831215044,193324109554,89983690077,163510356245,152307762894,117254692232,195450201087,
    60975657431,209545923434,1186023838,191880370987,53947826212,147960527934,95664844215,
    88989927265,113185046728,23548606918,111897399313,41910216950,91103325602,88196094169,
    72330543533,119712738984,39210746216,123646573991,1357989801,101882363354,42447620227,
    78607928025,88630821894,58671834566,132086643493,30092486435,139937598814,10952806156,
    127078034925,3962714438,113538775968,41969662465,71712321497,69423811528,43803543596,
    94856267067,13142412435,86991861902,8051082461,68051757521,16956347928,49914098468,9248098998],
   [59021451971,17796160231,52481026324,5417411175,2380100535,14044199429,8929398956,18464377333,
    48746549620,54835909857,37397884482,694757876,11261013477,25743261471,17757858972,41703695056,
    26004676179,28281355859,6029611428,4041245576,12759331432,34582629568,6168603962,54029921663,
    27239160389,60787112018,32898134682,57521200979,10511804561,87757332126,1619841954,
    86865475663,13699802990,105840407946,74037020175,163294247807,92045826616,229501322580,
    42963427537,239946364207,13677978843,158696251428,46004200559,147437862709,88840581988,
    158791586476,90936778723,150477795797,75292705046,108647663466,78892219547,49454587677,
    132975300124,30556649708,194070625603,44959225849,244165989262,86105025234,252934845837,
    102025156635,262625557108,105640197460,280056888593,111510628977],
   [342963993802,192475420992,264754819633,310769671541,319914865882,3231293622,107734284864,
    654914738845,713336996748,187964167363,183112895510,614927203991,559653137588,137914377455,
    33877018515,775845447671,1221206371488,972907877895,1560284797378,2017130636613,1718422188986,
    789010277009,176616401006,147343843468,827510178805,1957131118198,4276182483729,4012822508872,
    4053130270217,758741651486,1059891371472,4770838207871,8481742908226,10800364871731,
    4860734777778,1689201057267,6095321566805,6942168844246,130559921913,10524455322277,
    22664788987326,12175692298015,15533657425630,19885039180931,38408430270026,36384391140426,
    114822079501107,118653540238508,80126525113686,75875600011569,40061088007488,2523057204391,
    151537905340817,138922587569114,113734672621418,76735689107427,144644453419740,
    331404134670450,141494427915646,57444592212254,450556811645924,1034484598428164,
    1202506183477566,939572677158932],
   [370407950302522]]
private abbrev dP_s5_0 : Prop :=
  bSlideChk 9 513 phbVec7_5 pvi7_5 pvm_s5_1 = true
private theorem bk_s5_0 : dP_s5_0 := by decide +kernel
private abbrev dP_s5_1 : Prop :=
  bSlideChk 9 513 phbVec7_5 pvm_s5_1 pvm_s5_2 = true
private theorem bk_s5_1 : dP_s5_1 := by decide +kernel
private abbrev dP_s5_2 : Prop :=
  bSlideChk 9 513 phbVec7_5 pvm_s5_2 pvo7_5 = true
private theorem bk_s5_2 : dP_s5_2 := by decide +kernel
private theorem pwF_s5 : muxFastIterFullT16 27 513
    phbVec7_5 pvi7_5 = pvo7_5 :=
  pChFull 18 9 513 (pChFull 9 9 513 (bSlideChk_sound bk_s5_0) bk_s5_1) bk_s5_2
private def phbVec7_6 : List ℤ := pNZCat
  [
   [71897850647123,101522870289529,124148477242118,143133581545013,159781394705434,
    174761345253920,188471724345675,201172440835521,213044304372864,224219161779078,
    234796697613905,244854473798741,254454264072331,263646229473295,272471771714118,
    280965542923537,289156898088975,297070968282802,304729469155085,312151320430817,
    319353127792826,326349562790737,333153665991727,339777091532399,346230306360179,
    352522754030090,358662990479078,364658797429407,370517277772371,376244936316819,
    381847748560010,387331219585825,392700434771366,397960103654590,403114598059149,
    408167985370683,413124057698630,417986357529689,422758200376197,427442694839464,
    432042760440370,436561143514108,441000431420364,445363065282506,449651351438072,
    453867471756681,458013492959619,462091375056909,466102979002101,470050073651847,
    473934342106052,477757387494837,481520738270311,485225853054087,488874125085410,
    492466886309480,496005411140990,499490919933968,502924582185503,506307519497958,
    509640808321615,512925482497368,516162535617038,519352923217110],
   [522497564820056,525597345836047,528653119336557,531665707710309,534635904210973,
    537564474405167,540452157528538,543299667756957,546107695399267,548876908017435,
    551607951479447,554301450949848,556958011822378,559578220598808,562162645717746,
    564711838336836,567226333071551,569706648693478,572153288790799,574566742393440,
    576947484565181,579295976964850,581612668378544,583897995224707,586152382033729,
    588376241903639,590569976933324,592733978634630,594868628324586,596974297498916,
    599051348187933,601100133295804,603120996924143,605114274680816,607080293974755,
    609019374297583,610931827492736,612817958012776,614678063165519,616512433349564,
    618321352279783,620105097203291,621863939106376,623598142912869,625307967674358,
    626993666752669,628655487995003,630293673902063,631908461789540,633500083943257,
    635068767768282,636614735932294,638138206503470,639639393083148,641118504933504,
    642575747100478,644011320532153,645425422192798,646818245172768,648189978794444,
    649540808714380,650870917021829,652180482333801,653469679886803],
   [654738681625395,655987656287707,657216769488034,658426183796633,659616058816838,
    660786551259604,661937815015577,663070001224799,664183258344132,665277732212499,
    666353566114025,667410900839159,668449874743853,669470623806882,670473281685361,
    671457979768538,672424847229931,673374011077853,674305596204404,675219725432979,
    676116519564344,676996097421328,677858575892198,678704069972741,679532692807118,
    680344555727520,681139768292682,681918438325271,682680671948219,683426573620009,
    684156246168964,684869790826570,685567307259865,686248893602923,686914646487466,
    687564661072635,688199031073939,688817848791414,689421205137027,690009189661321,
    690581890579366,691139394795997,691681787930389,692209154339979,692721577143760,
    693219138244953,693701918353101,694169997005575,694623452588529,695062362357313,
    695486802456360,695896847938563,696292572784162,696674049919144,697041351233183,
    697394547597124,697733708880027,698058903965788,698370200769337,698667666252439,
    698951366439099,699221366430588,699477730420092,699720521707009],
   [699949802710885,700165634985014,700368079229702,700557195305208,700733042244372,
    700895678264926,701045160781518,701181546417434,701304891016042,701415249651951,
    701512676641907,701597225555423,701668949225146,701727899756982,701774128539967,
    701807686255906,701828622888772,701836987733878,701832829406834,701816195852272,
    701787134352371,701745691535166,701691913382654,701625845238706,701547531816780,
    701457017207442,701354344885705,701239557718182,701112697970061,700973807311904,
    700822926826275,700660097014201,700485357801465,700298748544739,700100308037557,
    699890074516137,699668085665040,699434378622688,699188989986733,698931955819276,
    698663311651949,698383092490853,698091332821363,697788066612791,697473327322923,
    697147147902417,696809560799076,696460597961997,696100290845585,695728670413452,
    695345767142186,694951611025011,694546231575313,694129657830060,693701918353101,
    693263041238351,692813054112863,692351984139786,691879858021214,691396702000924,
    690902541867002,690397402954370,689881310147193,689354287881188],
   [688816360145829,688267550486438,687707882006184,687137377367968,686556058796210,
    685963948078534,685361066567348,684747435181327,684123074406791,683488004298982,
    682842244483243,682185814156094,681518732086210,680841016615298,680152685658871,
    679453756706924,678744246824513,678024172652226,677293550406560,676552395880192,
    675800724442156,675038551037907,674265890189293,673482755994424,672689162127428,
    671885121838115,671070647951533,670245752867412,669410448559516,668564746574875,
    667708658032914,666842193624482,665965363610753,665078177822038,664180645656466,
    663272776078565,662354577617723,661426058366534,660487225979024,659538087668768,
    658578650206873,657608919919850,656628902687354,655638603939808,654638028655889,
    653627181359887,652606066118941,651574686540128,650533045767423,649481146478520,
    648418990881508,647346580711410,646263917226566,645171001204873,644067832939872,
    642954412236676,641830738407743,640696810268486,639552626132714,638398183807906,
    637233480590319,636058513259903,634873278075050,633677770767155],
   [632471986534977,631255920038820,630029565394510,628792916167162,627545965364748,
    626288705431445,625021128240766,623743225088463,622454986685205,621156403149009,
    619847463997439,618528158139541,617198473867537,615858398848240,614507920114206,
    613147024054602,611775696405792,610393922241620,609001685963395,607598971289556,
    606185761245023,604762038150206,603327783609680,601882978500498,600427602960146,
    598961636374124,597485057363133,595997843769867,594499972645393,592991420235102,
    591472161964223,589942172422883,588401425350695,586849893620863,585287549223789,
    583714363250154,582130305873469,580535346332072,578929452910544,577312592920543,
    575684732681009,574045837497743,572395871642322,570734798330326,569062579698869,
    567379176783378,565684549493625,563978656588960,562261455652725,560532903065820,
    558792953979382,557041562286544,555278680593248,553504260188055,551718251010939,
    549920601620997,548111259163050,546290169333091,544457276342513,542612522881094,
    540755850078669,538887197465436,537006502930849,535113702681028],
   [533208731194624,531291521177078,529362003513201,527420107217995,525465759385649,
    523498885136623,521519407562732,519527247670145,517522324320194,515504554167908,
    513473851598151,511430128659259,509373294994056,507303257768130,505219921595225,
    503123188459621,501012957635346,498889125602075,496751585957531,494600229326237,
    492434943264413,490255612160831,488062117133417,485854335921378,483632142772615,
    481395408326178,479143999489489,476877779310055,474596606841363,472300337002647,
    469988820432161,467661903333623,465319427315412,462961229222117,460587140957983,
    458196989301785,455790595712612,453367776126018,450928340739959,448472093789873,
    445998833312242,443508350895909,441000431420364,438474852780164,435931385594588,
    433369792901548,430789829834708,428191243282678,425573771529061,422937143872016,
    420281080221919,417605290675554,414909475065154,412193322480456,409456510761779,
    406698705961962,403919561774788,401118718927339,398295804533444,395450431405163,
    392582197318928,389690684232660,386775457449802,383836064725819],
   [380872035312266,377882878933021,374868084686727,371827119868843,368759428706021,
    365664430994705,362541520634976,359390064049634,356209398477370,352998830127581,
    349757632182893,346485042633775,343180261927704,339842450413115,336470725555861,
    333064158902981,329621772765193,326142536585668,322625362958085,319069103251735,
    315472542795273,311834395563532,308153298303347,304427804024338,300656374768790,
    296837373560698,292969055417255,289049557285938,285076886746119,281048909284766,
    276963333920177,272817696904028,268609343178459,264335405198597,259992778648441,
    255578094474756,251087686533264,246517553975911,241863317295857,237120166672909,
    232282800904957,227345354740841,222301311804585,217143399459306,211863460812485,
    206452297481109,200899474516957,195193075733792,189319393100663,183262527099889,
    177003864727894,170521385995461,163788724605010,156773867131833,149437304626741,
    141729325521337,133585905395906,124922187165965,115621561568236,105516063653745,
    94347776995173,81682330484731,66672389836648,47129438701949]]
private def phb7_6 : List ℤ := altBuildHbFrom 896 512 53075846153 0 512
private def pvi7_6 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s5 pvo7_5
private def pvo7_6 : List ℤ := pZZZ 0
  [
   [16633238180,27955195146,10438173240,19139060238,14014473658,3597332246,1780762203,4122750796,
    31697285146,66888473846,85056918946,70600020458,12817370220,27388934154,7554993137,
    13311160564,11405972092,9490087045,37569112620,56171983904,85252674086,66311151170,
    43756812402,28552428574,5118250378,33839052051,52688734109,7500522783,44016474002,15927262615,
    87119083953,98409117629,35117427299,4095863165,22897484023,28789045773,28006594923,
    34831104249,82082524295,91261423275,57722500805,9792616269,73539538144,192383121996,
    278902606848,283923430882,229508289472,152365526698,69240107718,465685820,6170794504,
    129408328824,253545890730,196499590266,4399505292,104660971905,64195688151,30398044688,
    101231972930,87567081466,42388257931,169346490221,104255961575,114175170836],
   [186497788716,9893483525,169252817809,42035187155,135055976956,76395081220,77004997885,
    84384957785,5441137108,49832614214,42582246602,15203081678,33166149757,48726874341,
    14320063542,61291631540,31820805399,101030309089,15655246465,103807316954,37950788104,
    65616641333,13941767298,36667484624,19477554172,32368851937,469497800,52798289954,1558184747,
    11572863095,30717596593,2664775737,9510610341,32153040047,30071976184,10191425506,40569431478,
    52861201801,2708457155,21763080314,10168674868,70836626,33304627975,30046507612,10101347251,
    77201998167,2288077076,66276883996,8484761370,81461510309,51447321493,69946744130,45021012708,
    25082799769,5756926965,68146358610,24154560072,30777707733,48010113015,69159256714,
    44959956910,45395262301,98013550981,89752322548],
   [88844976764,43298441080,2778503739,201978623766,343660086818,278113829134,366098509550,
    597198719500,554669363282,249085173886,127861548988,110624230232,140834534967,459157641663,
    388686254249,46269278271,136059964124,173514985008,298536094208,260007068240,114336321061,
    369571496901,225014423957,42545892970,127279985436,155342092354,162557646798,27825598010,
    267798871233,278885004817,21383643722,349262345382,265649494126,25012153299,193102528069,
    167421694213,45497983399,162161150944,291955586376,49224136924,371188017653,235670547733,
    246771203680,290715751568,26681629907,212347352351,74168739095,31966241347,96628079748,
    250411392446,34216242127,321817716091,78676926745,252872368824,146255514188,122104827031,
    118401039363,7482524420,39203963552,70914695788,28227257540,141985026771,97591709851,
    172459050472],
   [161401273088,121265153803,151488736109,57101036344,91323730942,25534937579,48991154319,
    22291347673,19876070011,43818878440,85023492588,33007914063,184265063485,51125570225,
    117835593014,37336551772,145848064607,110258826809,114492630498,18115530168,69576271135,
    333930841,16563810192,16132173533,5742850974,59042450880,54752276061,95664424569,72827177010,
    106456485100,87076337107,92891583399,120711151058,78286742974,140699262463,33173880465,
    136644428372,65889138471,99752134557,63458762920,31669870832,108355113549,61189665428,
    120489383502,92400291573,174757811715,106755987376,85391329760,128774919169,54487241425,
    76825366832,14152473542,87759248081,63569908730,35879730804,112658129959,32952261172,
    86326167676,47795285933,85949649265,97617072644,59870948412,91041498201,21839572899],
   [51723825048,3350915171,45916359165,53517749318,5007412750,35519849979,22135713140,51358732828,
    76856670339,8561345774,42739322384,28571346369,48887003549,27178490611,34279031032,5654568678,
    40266015117,3213747933,31284161762,48128863817,18831140208,64154653054,2758627319,
    105678818543,56446500624,97986060660,86226364697,37348120255,118262539282,8254838842,
    103676484405,64428029628,132995361876,68417588709,86928514045,83071681140,21482913858,
    73616194945,74563695280,86307764692,100797774523,12747384183,168808020892,15139111009,
    164608374905,57008568868,117586547840,96774927183,38238328515,134382483408,18066651537,
    103680086081,67027726090,11476578966,162716735637,44208665566,109452748956,103366910143,
    110320450207,198246622570,38028652486,164194653491,77967694778,105944723118],
   [129200294589,15752387051,175059301082,39849388109,142792829117,117428501020,83656213900,
    202722531671,19679120845,224434484672,53707403547,196309617443,133528939364,127312866520,
    191218177143,42757807447,180559478418,60573725527,129745682255,162631437802,109979730710,
    180728039447,23380452907,152398077868,37548799545,119259003989,114115043970,42715505654,
    83733962237,11811181072,68572952300,46316566135,48350087207,103741347990,5785472407,
    118485007465,57313238230,100393462646,100038927933,56748782487,113725535892,10883861566,
    97821950301,28432354766,84494020920,122632557225,40374908054,86748346496,19675525699,
    166658625815,97566719768,57705237700,16518098197,26934368493,59287272126,29978985284,
    37169622001,45628515728,17071365234,34798640795,11711344371,37263865136,14633606794,
    37272724117],
   [4175376443,23044642610,75174475,14863997975,13621558595,26644015960,32336659036,26817048485,
    47962947847,12430919540,5264454814,31646477895,22624357253,18877978946,7511972025,20030542675,
    28803145464,16982123042,29154422415,11825602755,20390899342,12520443459,14474787683,
    42101527852,8417018197,76220901569,34308957106,99479104978,56487831883,102885418567,
    78972920950,83253260000,103582440761,33742396521,138884116220,29244576585,174792968663,
    83246530776,187136154504,125062881933,166074900435,162814270806,142492933394,177895992359,
    100011043869,143007554734,66151964088,122315810491,92737521018,45859638160,68214095917,
    223195248617,350363142056,208196171095,232926998470,423995856435,640293936590,603512550009,
    190387505060,193359230589,605145371442,626646025573,207917854400,297409348247],
   [896402616252,1189343847797,1105224084580,1119659269295,1534525900886,1826622041929,
    1074655466294,124020462769,339926900769,672056060968,1421540838383,2373377744838,
    2980499947139,2846843721462,2541469765251,2219684752702,1020422770899,1614234658681,
    4705799340752,6885569410909,7384866038686,6779720274255,5122122325386,2068596600239,
    1339970170815,3910814603992,4544480259603,1743453589910,2744504809146,5340378789725,
    3696915677768,891462764408,2884238789077,741300019389,5286365274610,1326215588729,
    6252811500227,1419239118492,6125942293636,5718944487668,15942473151137,18332829852026,
    66358656085727,10363292637053,45551017058372,43898634151833,13605086130349,49925298352075,
    62470753804551,104237831720715,2303506941912,176740224137735,44432222142497,39419630834029,
    172700267958171,36086544014353,142772297552371,131565500111141,21744653240356,105314942394231,
    161075682458949,346779820072349,321168027510213,867734779018550],
   [1689816427373400]]
private def pvm_s6_1 : List ℤ := pZZZ 0
  [
   [28058433090,24019749166,8664054380,17352473396,741495695,9580151190,37229392976,73021071806,
    87187939342,57679164440,12344688066,7303005023,8743576522,14791338300,6829112158,46561881522,
    43994503992,100564816674,64765754670,24560208672,8382924814,27416076511,24631536085,
    43660223249,7307770761,9210844318,34060596939,106159189685,91941352485,519103979,20416549830,
    37311355611,59190504535,57181541687,52141254597,73210362963,23024349323,78756195852,
    182341794264,257628000728,291380110132,268451119112,150163368214,51664130902,17115168258,
    34297615990,94063228956,176452710880,195208905504,78621011576,97174501975,143450547277,
    2004375225,129012427100,78945201448,54797761465,118008437533,80342101153,42586937224,
    152845352802,84700537592,109646955611,145877582139,47381036106],
   [164728375126,7043125274,159925919559,53644256535,125722263152,84389021334,53070353733,
    62954125657,6788454919,8425586886,9979093312,2401065733,42177309159,26838473655,65271312456,
    85632840086,25499738599,77635448419,27175583314,81422743286,16289420295,52661940393,
    28872937548,43558358070,55892344305,45537432433,10974940978,15556995638,14195372564,
    14347693113,34540364478,3469595719,24828667903,8690256653,10476022966,34947691380,35182896881,
    28187722407,11536492677,3365480426,4441156047,31084532753,51413323108,22850980299,25808736593,
    37166256767,86372930194,87407410908,57007967511,25811555761,43974052614,36709901862,
    37452735921,38178692027,58759775678,42360310252,34674163011,24177341104,148872816508,
    212661608954,174089033300,234254468948,427420518330,552983107500],
   [427083051096,345796752886,300808348526,150065032032,203265657367,331377957913,271340588275,
    143475818293,215496652697,80851847658,425363064044,352517276034,18439220367,184686959635,
    164955719711,216331953469,146264842041,173181083456,366313957524,110555486944,192484379889,
    180219976781,73725170303,36359799459,137851249176,319022769162,167293379206,210109100325,
    333671565127,44834452645,242516181976,223147098068,3043287974,153510573187,195099696869,
    55336806755,170223352390,294058768014,29766292923,346726212557,175745690297,271372396060,
    257505367430,100421490747,185617008155,55412485817,5099954163,126440979948,180428603130,
    59258935055,288582799127,38164176871,297883040280,32890001146,181836503383,51031246899,
    79266591310,73354220268,37081522562,31736961735,140073717713,58863356953,165418842628,
    92123711938],
   [169430844871,101986230247,129359182062,72236268816,98690324799,89946292279,40376633165,
    35128794141,35249560460,61719683352,74412561177,136444473205,34609103308,146373808966,
    9429093533,139164932771,5194805249,117041949468,491958727,87339763223,12161394231,60378158634,
    24134583853,11254912272,65590525346,77995025439,36283633649,70603236784,46643672830,
    118206293421,68354251235,123513240666,13844413062,131118595421,10963504208,139825853518,
    41822691093,124491178723,46253166096,10708032560,124607480959,53303577462,121172838468,
    127258080797,100585318611,131234474082,90880355560,148949505527,36939629731,115067195974,
    601944400,96270254819,78196883128,29250794806,68522918727,859225548,86318680008,55072288263,
    107027277451,123600602972,54762216172,96675430565,8509190201,74795775332],
   [4970611041,75565583617,43774854510,3849385722,56286828147,5606985119,22272276580,45293489193,
    30986455009,80449523596,11223480057,66599224367,14813151910,63331557460,22923589907,
    10797737704,14506035545,15240935670,11006830485,1043746019,69691127084,865744335,63477480231,
    43813827776,97514066790,50749586453,42707243097,78619270466,33337850294,143663208109,
    47793678734,150529104212,28925357323,82643899845,75953895638,61396645916,79472275159,
    3592417296,75965646500,80877908829,62514298329,146014285914,50479620112,153523701889,
    3398711867,124412658852,87908570859,137621227131,85275945798,54342886724,106233799169,
    25434725996,105559589304,72304154927,29543253497,146974168900,24399128749,156035598293,
    97166289720,140645755200,125920361105,46869544673,138540339054,30168910275],
   [175260371727,132660583072,69951402302,149982356565,23761962424,159669980010,100841496123,
    154461130309,156471204988,99486814322,202121659605,20990716569,235118960030,31243097849,
    166147669961,121362240172,98186064570,192022523787,18782809677,213124870348,45076321929,
    165644065027,113709667706,114097460326,142237631279,45517129705,143987660058,23188295865,
    98800872091,62899636966,47126030958,100517556909,31409799170,74517646118,47894962183,
    80921821051,95761413646,58217066406,135324391197,2491570719,123299416486,32098753871,
    87184633883,61881423146,17625452024,93471212845,50209593510,152468583414,52975408359,
    106558408435,119225725822,43532751440,48097986045,51823642843,94972959758,56877955817,
    6359011012,250341181,48541975936,59643753143,15477233701,53404178346,7231427585,20135192155],
   [5002151585,33441307308,7136013827,45823861003,26281459897,85147449,19181471234,14080415321,
    37315843201,17165431928,30274790968,14036878155,12604692609,21853671804,9631169451,
    28384587105,4427011820,33888240114,16739978981,18580279559,14918443166,5463474651,11753210045,
    35644990806,21021516154,71958114529,26527418063,103315199684,24175260542,111057634501,
    4387323921,101624884436,42253386387,97244023125,103535946248,103791455722,150395606249,
    91585206317,192592850972,69398121550,222076667775,46395087493,235441071340,51160026302,
    175001368111,8817951763,104741119782,80420239321,78325686917,145324032432,101521835650,
    169027261475,44534979887,91654595746,3910983429,228336629483,238692574922,19714574335,
    147820344294,657831029447,673003056876,203068932979,237931400936,627465404789],
   [577571235048,240312319909,94111871170,626824468609,954970899348,722291093755,821978101548,
    1548648895135,1917332648124,1552642440717,847393950266,450980762659,161390584974,670723391618,
    1855615242047,2436598761748,2605476425039,2906701137802,3303839496617,2598938841196,
    23102980095,3053022211227,5502323440668,7322125318193,7578648224418,6416189028049,
    3823967962444,332530513584,4104092020941,5052109457922,1597551522051,3576520953807,
    5842541188238,1700406862813,4180966581465,56521938084,7834571479546,457410067075,
    11499844040203,16852990227655,20869698461241,21876379121391,3536764149109,37330834792068,
    79980323426825,54929606252387,35127615092453,107429940989557,57801582197379,73782217464437,
    86225419270761,127558201206723,16933752930624,179743083917881,98285584455851,43891006880699,
    164930109642579,775559148338,51284231821943,239524740555505,234611511914139,241967289415655,
    284910120319424,1315334934823172],
   [1373275098967132]]
private abbrev dP_s6_0 : Prop :=
  bSlideChk 7 513 phbVec7_6 pvi7_6 pvm_s6_1 = true
private theorem bk_s6_0 : dP_s6_0 := by decide +kernel
private abbrev dP_s6_1 : Prop :=
  bSlideChk 6 513 phbVec7_6 pvm_s6_1 pvo7_6 = true
private theorem bk_s6_1 : dP_s6_1 := by decide +kernel
private theorem pwF_s6 : muxFastIterFullT16 13 513
    phbVec7_6 pvi7_6 = pvo7_6 :=
  pChFull 7 6 513 (bSlideChk_sound bk_s6_0) bk_s6_1
private def phbVec7_7 : List ℤ := pNZCat
  [
   [73413884059210,103663574942932,126766263975168,146151686955131,163150534823297,
    178446351636748,192445826892136,205414349865524,217536542746851,228947032471008,
    239747605539895,250017459340546,259819670168753,269205456755541,278217093807217,
    286889964125054,295254041673837,303334987438094,311154974962681,318733322912685,
    326086987117283,333230948489444,340178522568897,346941609230615,353530896127396,
    359956025940453,366225735016661,372347969163176,378329981042397,384178412623149,
    389899365401639,395498460541590,400980890650035,406351464569943,411614646308954,
    416774589017340,421835164764712,426799990734412,431672452349457,436455723758921,
    441152786044512,445766443450469,450299337893377,454753961969972,459132670649075,
    463437691807067,467671135743986,471835003798497,475931196164097,479961518995434,
    483927690882149,487831348757861,491674053303519,495457293897138,499182493155717,
    502851011109763,506464149046196,510023153051350,513529217282252,516983486991302,
    520387061326742,523740995928967,527046305340612,530303965246541],
   [533514914558219,536680057355516,539800264697717,542876376314381,545909202185671,
    548899524020896,551848096643176,554755649287449,557622886818365,560450490874059,
    563239120941248,565989415366656,568701992309314,571377450637936,574016370777185,
    576619315506381,579186830713864,581719446110006,584217675901616,586682019430272,
    589112961776921,591510974334896,593876515353370,596210030453077,598511953116029,
    600782705150813,603022697134946,605232328835667,607411989610432,609562058788300,
    611682906033331,613774891691006,615838367118645,617873675000718,619881149649881,
    621861117294537,623813896353631,625739797699394,627639124908654,629512174503337,
    631359236180708,633180593033895,634976521763189,636747292878584,638493170894014,
    640214414513677,641911276810863,643584005399630,645232842599692,646858025594836,
    648459786585177,650038352933552,651593947306308,653126787808767,654637088115596,
    656125057596318,657590901436194,659034820752670,660457012707593,661857670615381,
    663236984047331,664595138932218,665932317653358,667248699142285],
   [668544458969170,669819769430145,671074799631636,672309715571847,673524680219497,
    674719853589938,675895392818745,677051452232888,678188183419581,679305735292898,
    680404254158242,681483883774762,682544765415774,683587037927293,684610837784718,
    685616299147764,686603553913691,687572731768903,688523960238966,689457364737122,
    690373068611333,691271193189919,692151857825845,693015179939692,693861275061371,
    694690256870618,695502237236313,696297326254669,697075632286316,697837261992343,
    698582320369305,699310910783248,700023135002782,700719093231229,701398884137884,
    702062604888406,702710351174382,703342217242083,703958295920437,704558678648247,
    705143455500678,705712715215034,706266545215853,706805031639326,707328259357088,
    707836311999365,708329271977538,708807220506097,709270237624041,709718402215721,
    710151792031147,710570483705774,710974552779782,711364073716871,711739119922578,
    712099763762123,712446076577824,712778128706056,713095989493800,713399727314771,
    713689409585153,713965102778937,714226872442885,714474783211119],
   [714708898819361,714929282118813,715135995089704,715329098854504,715508653690813,
    715674719043940,715827353539174,715966614993757,716092560428565,716205246079508,
    716304727408651,716391059115069,716464295145437,716524488704361,716571692264464,
    716605957576223,716627335677570,716635876903257,716631630893999,716614646605385,
    716584972316584,716542655638825,716487743523679,716420282271136,716340317537478,
    716247894342963,716143057079314,716025849517028,715896314812492,715754495514932,
    715600433573176,715434170342253,715255746589819,715065202502418,714862577691582,
    714647911199775,714421241506172,714182606532295,713932043647489,713669589674260,
    713395280893458,713109153049319,712811241354375,712501580494214,712180204632108,
    711847147413512,711502441970422,711146120925611,710778216396728,710398760000283,
    710007782855493,709605315588015,709191388333552,708766030741345,708329271977538,
    707881140728433,707421665203624,706950873139021,706468791799757,705975447982983,
    705470868020552,704955077781595,704428102674984,703889967651685],
   [703340697207013,702780315382766,702208845769264,701626311507276,701032735289845,
    700428139364008,699812545532408,699185975154811,698548449149508,697899987994626,
    697240611729326,696570339954906,695889191835795,695197186100452,694494341042155,
    693780674519692,693056203957953,692320946348406,691574918249490,690818135786886,
    690050614653696,689272370110515,688483416985399,687683769673727,686873442137961,
    686052447907295,685220800077205,684378511308882,683525593828567,682662059426769,
    681787919457379,680903184836669,680007866042183,679101973111512,678185515640952,
    677258502784059,676320943250069,675372845302216,674414216755920,673445064976860,
    672465396878917,671475218922003,670474537109753,669463356987094,668441683637682,
    667409521681208,666366875270568,665313748088900,664250143346471,663176063777437,
    662091511636448,660996488695110,659890996238297,658775035060308,657648605460874,
    656511707240999,655364339698644,654206501624242,653038191296048,651859406475311,
    650670144401274,649470401785992,648260174808962,647039459111569],
   [645808249791334,644566541395971,643314327917230,642051602784541,640778358858443,
    639494588423791,638200283182743,636895434247516,635580032132902,634254066748549,
    632917527390987,631570402735402,630212680827144,628844349072970,627465394232005,
    626075802406420,624675559031816,623264648867305,621843055985282,620410763760876,
    618967754861071,617514011233486,616049514094812,614574243918874,613088180424343,
    611591302562039,610083588501862,608565015619299,607035560481516,605495198833017,
    603943905580848,602381654779346,600808419614399,599224172387217,597628884497593,
    596022526426628,594405067718915,592776476964151,591136721778171,589485768783365,
    587823583588480,586150130767755,584465373839400,582769275243363,581061796318381,
    579342897278278,577612537187486,575870673935757,574117264212039,572352263477482,
    570575625937541,568787304513145,566987250810887,565175415092202,563351746241502,
    561516191733203,559668697597626,557809208385714,555937667132503,554054015319335,
    552158192834708,550250137933760,548329787196287,546397075483254],
   [544451935891733,542494299708198,540524096360099,538541253365654,536545696281765,
    534537348649988,532516131940456,530481965493678,528434766460103,526374449737353,
    524300927905017,522214111156886,520113907230521,518000221334009,515872956069785,
    513732011355375,511577284340908,509408669323235,507226057656487,505029337658903,
    502818394515721,500593110177943,498353363256753,496099028913377,493829978744114,
    491546080660319,489247198763031,486933193211986,484603920088684,482259231253192,
    479898974194333,477522991872888,475131122557400,472723199652173,470299051516996,
    467858501278112,465401366629909,462927459626770,460436586464496,457928547250647,
    455403135763117,452860139196202,450299337893377,447720505065897,445123406496334,
    442507800226033,439873436225422,437220056046023,434547392452901,431855169036214,
    429143099800388,426410888729325,423658229325941,420884804124139,418090284171200,
    415274328478373,412436583437254,409576682199317,406694244015739,403788873534359,
    400860160050349,397907676706823,394930979641240,391929607073066],
   [388903078327684,385850892791043,382772528788952,379667442384297,376535066084730,
    373374807452559,370186047607683,366968139613333,363720406733259,360442140547634,
    357132598913460,353791003753523,350416538655987,347008346264447,343565525435702,
    340087128139488,336572156071033,333019556943252,329428220420846,325796973653154,
    322124576356348,318409715388219,314650998750134,310846948940567,306995995572528,
    303096467152841,299146581904106,295144437489594,291087999476625,286975088343965,
    282803364802420,278570313153228,274273222354153,269909164395455,265474969503729,
    260967197586100,256382105194212,251715607118387,246963231505789,242120067116668,
    237180700968111,232139144134652,226988742836434,221722071086227,216330799995802,
    210805537225642,205135627796884,199308904259361,193311369535472,187126788851337,
    180736156730795,174116988872568,167242363021033,160079590718489,152588329932606,
    144717820880086,136402689126453,127556288296250,118059550310841,107740968523240,
    96337188097083,83404678803595,68078239521253,48123206987398]]
private def phb7_7 : List ℤ := altBuildHbFrom 896 512 54195000000 0 512
private def pvi7_7 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s6 pvo7_6
private def pvo7_7 : List ℤ := pZZZ 0
  [
   [33190311421,11763286508,7227826802,3161937389,4342052302,9684168676,9343370726,20059215442,
    2651404087,7223291644,4025302907,14826202711,18804477034,61878118466,97463767944,63556501534,
    27495531324,1331345800,7709683609,1476956940,6260682894,6416367793,3138170721,2037489528,
    46516397414,62339127904,45413957842,60171704316,77152420672,79412671332,8103594082,
    52154446703,41407909169,19539333288,47270431382,24730486,53664699263,57371223493,46561744851,
    50125869703,46853615379,16645072267,10720062745,10373602151,25495632333,37589987183,
    56031067383,98320897801,124895315507,76150808013,26970248298,102361644608,154782447170,
    249391305942,328521453820,266369347052,92952676958,25404742439,361490667,105816280202,
    195078612744,226475809020,171630962154,10615521284],
   [131551905399,52159294395,168608203836,202090765518,30567461605,191663591519,98243973341,
    84975309796,92115191572,8992738485,54068864647,31969582571,22789017492,44847877584,
    61062591544,11794864937,109381889465,20721495803,71684288806,68128651364,59006351507,
    68166516633,69864226794,49007309950,12749748346,89662225251,6253430477,2696612674,10675885217,
    1252966325,9500075711,44796791802,2435004257,27135055195,8284826306,3394217192,14105026180,
    2584630828,3810090821,50944767996,8492894778,49502525839,40074885355,23579156820,21045807496,
    38186818013,4458581983,41400361636,23080239986,50734778577,58322937413,119042950614,
    22441035822,39192153315,63861104687,4632878450,47842599724,17557284267,31868516849,5617555089,
    18917071572,21712357455,70316773213,2424310143],
   [115592836536,26960178070,125126638199,22989202589,157887324002,70680279404,80662548173,
    10373505620,120875216736,5658746286,131846455099,21193055638,147307163410,5588605555,
    144400081493,79364214490,248488730340,227229630612,230230237210,479682249992,608718787674,
    496891531368,376435411732,290623320472,37323306626,327209161383,468793387865,231426301183,
    54667915334,182479325804,233770246852,214971001598,104599103818,265319963387,371044093151,
    58035583791,225019708480,230343691666,84129720238,22050309903,242094756493,354308182829,
    85894500158,484965222718,186918685660,245187021385,213551315211,8570090474,123431729310,
    195065178362,119009290032,191370747269,290947645597,77982641162,327956586528,65600585706,
    210269263225,134470499113,21643438462,106562145424,133420328586,4806220827,202976040521,
    81370794121],
   [188304262206,105016095536,111844439519,159387214377,120392800256,95009282470,12216938727,
    58740376111,64028219859,13297546839,38415879326,105358907044,18146104751,133716691213,
    14035882410,165609739288,15633645442,174257102413,56033094489,113790089460,40941098970,
    56756087319,5674396502,4857398804,27974903633,10582641135,54852834406,121021891467,
    158534921829,64414289832,89050029190,190543180693,83126009535,136742553338,22926749766,
    126117306927,19012426050,109550644504,103602129743,38739006947,100416908284,29995924347,
    91816250839,61435535562,123531302458,132370838009,69780209499,160120970132,40241115364,
    140175382133,33173009085,67886874382,57850585989,6725272740,70589455288,29425909533,
    91264628187,76688593284,32672442054,92103431271,72771901545,96408478444,23667294279,
    75127702577],
   [28894821144,16444852956,21549487271,2842117344,12758148266,43647759389,4053718864,29302786614,
    35018508524,51912866173,75712991,48223078286,7775734093,59463771603,3237780818,70683567292,
    25144096861,36521057031,58962080140,14908946297,62688592573,73663080012,58765144726,
    103952001067,26271713891,129139084912,10815503537,132129665313,42550887272,83428341952,
    101040705281,38341331055,129664145160,11777499023,117688987309,64076762110,77697042848,
    88061874691,4906041572,103357697644,84386527121,75987143883,168772861952,81463998908,
    175492162933,40320821812,123015287534,63682964559,69029012399,100989985834,4728530150,
    87636666233,133778922938,67778761802,149367517549,55084273254,144272561958,147186989753,
    91336772727,184373209520,37290745192,144232238423,71930561182,94256865180],
   [154056602973,43608525797,133622566714,105859398819,163059191221,162760292042,92392327012,
    202710987547,35091170626,203772962780,116610650711,154469123333,206063369566,72088419988,
    164390540591,32808839044,151521873202,138587848633,77950396545,170873653330,29908294059,
    135188698075,80380853808,106950197844,101712682835,60600828047,80860282466,26594864051,
    59381654297,93988445946,36140663528,93838884739,67575499786,45672868700,68326442205,
    66772709455,175091689546,55396378339,81002295669,49545621348,102983854856,124202092925,
    20317288266,76629519606,45051456703,60374171977,112185343100,29737208955,91194877839,
    53117376114,77289052076,51853806579,46202696377,11004119752,26909291090,17838231884,
    8286322816,16440035119,46704167865,7111034896,43479786794,7750234949,28011986873,4527741060],
   [41370886754,27416985176,4374398071,4244726330,37078765172,31527951392,17616859005,11535824191,
    47022335374,11314157570,42782469481,5482832357,21421980016,3596240599,5593892770,31130888742,
    14540986405,42180375103,11445077058,3422473991,60085473861,4922613205,26396268902,49334563897,
    14084070087,86877538518,14377368287,115450319559,51592657442,118262935560,97948592639,
    97193727469,132021604224,30578050988,146955384889,43918048470,159755379234,149485864087,
    103785908631,157766420648,144692624304,288214353741,72713632594,39276580156,201229911634,
    469736676809,457690686622,346506761351,379774262294,467851095995,550160238058,489300994305,
    228459298822,214512841297,575554239992,728400205071,666192401330,666997794229,948656558220,
    1484315102699,1610692868354,1133342657559,929734461900,1014379406575],
   [502289662922,584685260764,1499993333695,1784516321402,1939101528753,2378510194384,
    2955929262023,2823109934994,1720760265459,451104771564,903015300784,2854073592415,
    5141317900948,7142338131127,7595699080184,6166299757335,3718393446498,1250677217977,
    1166292362665,3201543786350,4048692656695,2813789731248,232275633848,3449864679383,
    4886863527888,3696053470963,232931251826,2533201407654,1670016970549,1575397424757,
    3239318026268,697502554357,4303345043233,5793778349710,3343285994323,5879551771890,
    19100244570061,31606334796578,26910560388893,9793911469566,7995950421078,21522908141593,
    3383763659160,47522576060202,32664803205427,23574865072891,58273323721381,81371652863142,
    55073183490163,51576477333350,87060103172448,43791470469411,175540538390036,17468729533816,
    98036685560514,141850464204996,8540642885996,109714344186910,105368655424682,124057315710360,
    18827251648577,210407823812518,205814254894884,137379154609384],
   [1939695361193580]]
private abbrev dP_s7_0 : Prop :=
  bSlideChk 10 513 phbVec7_7 pvi7_7 pvo7_7 = true
private theorem bk_s7_0 : dP_s7_0 := by decide +kernel
private theorem pwF_s7 : muxFastIterFullT16 10 513
    phbVec7_7 pvi7_7 = pvo7_7 := bSlideChk_sound bk_s7_0
private def pwalks_r512 : List RkmSegWalk := [
  ⟨rkmHbHiHiB_m128_r512_s0, rkmViHiHiB_m128_r512_s0, rkmVoHiHiB_m128_r512_s0⟩,
  ⟨rkmHbHiHiB_m128_r512_s1, rkmViHiHiB_m128_r512_s1, rkmVoHiHiB_m128_r512_s1⟩,
  ⟨rkmHbHiHiB_m128_r512_s2, rkmViHiHiB_m128_r512_s2, rkmVoHiHiB_m128_r512_s2⟩,
  ⟨rkmHbHiHiB_m128_r512_s3, rkmViHiHiB_m128_r512_s3, rkmVoHiHiB_m128_r512_s3⟩,
  ⟨rkmHbHiHiB_m128_r512_s4, rkmViHiHiB_m128_r512_s4, pvo7_4⟩,
  ⟨phb7_5, pvi7_5, pvo7_5⟩, ⟨phb7_6, pvi7_6, pvo7_6⟩, ⟨phb7_7, pvi7_7, pvo7_7⟩]
private abbrev dP_tail : Prop := rkmAllTrueF [
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 128) 512) 1] [129],
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 2 128) 512) 1] [257],
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 3 128) 512) 1] [385],
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 5 128) 512) 1] [513],
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 7 128) 512) 1] [513],
  muxIntListEq rkmHbHiHiB_m128_r512_s4 phbVec7_4,
  muxIntListEq phb7_5 phbVec7_5, muxIntListEq phb7_6 phbVec7_6, muxIntListEq phb7_7 phbVec7_7,
  rkmCheckRowFromWalks 128 64 512 [1, 2, 3, 5, 7, 7, 7, 7]
    [13240546, 8842920, 5680876, 5000000, 13800000, 1526245, 689986, 541950]
    [49, 61, 55, 71, 244, 27, 13, 10] rkmMasksHiHiB_m128_r512 pwalks_r512
    rkmRowHiHiB_m128_r512] = true
private theorem ptail_r512 : dP_tail := by decide +kernel
private theorem pdim_l1 : Nat.add (highdNatMin (Nat.mul 1 128) 512) 1 = 129 :=
  bDm (rkmHd ptail_r512)
private theorem pdim_l2 : Nat.add (highdNatMin (Nat.mul 2 128) 512) 1 = 257 :=
  bDm (rkmHd (rkmTl ptail_r512))
private theorem pdim_l3 : Nat.add (highdNatMin (Nat.mul 3 128) 512) 1 = 385 :=
  bDm (rkmHd (rkmTl (rkmTl ptail_r512)))
private theorem pdim_l5 : Nat.add (highdNatMin (Nat.mul 5 128) 512) 1 = 513 :=
  bDm (rkmHd (rkmTl (rkmTl (rkmTl ptail_r512))))
private theorem pdim_l7 : Nat.add (highdNatMin (Nat.mul 7 128) 512) 1 = 513 :=
  bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl ptail_r512)))))
private theorem pwalk7_4b :
    muxFastIterFullT16 167 513 rkmHbHiHiB_m128_r512_s4 rkmMidHiHiB_m128_r512_s4a = pvo7_4 :=
  (congrArg (fun h => muxFastIterFullT16 167 513 h rkmMidHiHiB_m128_r512_s4a)
    (muxIntListEq_eq_true.mp
      (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl ptail_r512)))))))).trans pwF_s4
private theorem pwalk7_4 :
    muxFastIterFullT16 244 513 rkmHbHiHiB_m128_r512_s4 rkmViHiHiB_m128_r512_s4 = pvo7_4 :=
  (muxFastIterFullT16_add 77 167 513 rkmHbHiHiB_m128_r512_s4 rkmViHiHiB_m128_r512_s4).trans
    ((congrArg (muxFastIterFullT16 167 513 rkmHbHiHiB_m128_r512_s4)
      rkmWalkHiHiB_m128_r512_s4a).trans pwalk7_4b)
private theorem pwalk7_5 : muxFastIterFullT16 27 513 phb7_5 pvi7_5 = pvo7_5 :=
  (congrArg (fun h => muxFastIterFullT16 27 513 h pvi7_5)
    (muxIntListEq_eq_true.mp
      (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl ptail_r512))))))))).trans
    pwF_s5
private theorem pwalk7_6 : muxFastIterFullT16 13 513 phb7_6 pvi7_6 = pvo7_6 :=
  (congrArg (fun h => muxFastIterFullT16 13 513 h pvi7_6)
    (muxIntListEq_eq_true.mp
      (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl ptail_r512)))))))))).trans
    pwF_s6
private theorem pwalk7_7 : muxFastIterFullT16 10 513 phb7_7 pvi7_7 = pvo7_7 :=
  (congrArg (fun h => muxFastIterFullT16 10 513 h pvi7_7)
    (muxIntListEq_eq_true.mp
      (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl ptail_r512))))))))))).trans
    pwF_s7
private theorem pseg_0 :
    muxFastIterFullT16 49 (Nat.add (highdNatMin (Nat.mul 1 128) 512) 1)
      rkmHbHiHiB_m128_r512_s0 rkmViHiHiB_m128_r512_s0 = rkmVoHiHiB_m128_r512_s0 := by
  rw [pdim_l1]; exact rkmWalkHiHiB_m128_r512_s0
private theorem pseg_1 :
    muxFastIterFullT16 61 (Nat.add (highdNatMin (Nat.mul 2 128) 512) 1)
      rkmHbHiHiB_m128_r512_s1 rkmViHiHiB_m128_r512_s1 = rkmVoHiHiB_m128_r512_s1 := by
  rw [pdim_l2]; exact rkmWalkHiHiB_m128_r512_s1
private theorem pseg_2 :
    muxFastIterFullT16 55 (Nat.add (highdNatMin (Nat.mul 3 128) 512) 1)
      rkmHbHiHiB_m128_r512_s2 rkmViHiHiB_m128_r512_s2 = rkmVoHiHiB_m128_r512_s2 := by
  rw [pdim_l3]; exact rkmWalkHiHiB_m128_r512_s2
private theorem pseg_3 :
    muxFastIterFullT16 71 (Nat.add (highdNatMin (Nat.mul 5 128) 512) 1)
      rkmHbHiHiB_m128_r512_s3 rkmViHiHiB_m128_r512_s3 = rkmVoHiHiB_m128_r512_s3 := by
  rw [pdim_l5]; exact rkmWalkHiHiB_m128_r512_s3
private theorem pseg_4 :
    muxFastIterFullT16 244 (Nat.add (highdNatMin (Nat.mul 7 128) 512) 1)
      rkmHbHiHiB_m128_r512_s4 rkmViHiHiB_m128_r512_s4 = pvo7_4 := by
  rw [pdim_l7]; exact pwalk7_4
private theorem pseg_5 :
    muxFastIterFullT16 27 (Nat.add (highdNatMin (Nat.mul 7 128) 512) 1)
      phb7_5 pvi7_5 = pvo7_5 := by
  rw [pdim_l7]; exact pwalk7_5
private theorem pseg_6 :
    muxFastIterFullT16 13 (Nat.add (highdNatMin (Nat.mul 7 128) 512) 1)
      phb7_6 pvi7_6 = pvo7_6 := by
  rw [pdim_l7]; exact pwalk7_6
private theorem pseg_7 :
    muxFastIterFullT16 10 (Nat.add (highdNatMin (Nat.mul 7 128) 512) 1)
      phb7_7 pvi7_7 = pvo7_7 := by
  rw [pdim_l7]; exact pwalk7_7
private theorem pwalks_snd_r512 :
    RkmSegWalksSound 128 512 [1, 2, 3, 5, 7, 7, 7, 7] [49, 61, 55, 71, 244, 27, 13, 10]
      pwalks_r512 := by
  dsimp only [RkmSegWalksSound, pwalks_r512]
  exact ⟨pseg_0, ⟨pseg_1, ⟨pseg_2, ⟨pseg_3, ⟨pseg_4, ⟨pseg_5, ⟨pseg_6, ⟨pseg_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 512)` (`FindAllJohnsonRampKickMuxHi128T7`). -/
theorem rkmTrajHiHiB_m128_r512 : rkmLo12EqHi 128 64 512 [1, 2, 3, 5, 7, 7, 7, 7]
    [13240546, 8842920, 5680876, 5000000, 13800000, 1526245, 689986, 541950]
    [49, 61, 55, 71, 244, 27, 13, 10] rkmMasksHiHiB_m128_r512 rkmRowHiHiB_m128_r512 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r512
    (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl ptail_r512))))))))))
end
end QuantumComputation.Specs.DickeSol
