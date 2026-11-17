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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T3

/-
# High-`m` Coupled Walk & Trajectory Part `4` (`FindAllJohnsonRampKickMuxHi128T4`)

Certifies `(m = 128, r = 384)` coupled `T_16` walk (`125556` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi128T4`). -/
def rkmWordBitsHi128T4 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi128T4 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi128T4`). -/
def rkmUnpackMaskHi128T4 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi128T4 n w ++ rkmUnpackMaskHi128T4 ns ws
/-- Mask segment `0` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s0 : List Bool := rkmUnpackMaskHi128T4 [50, 10] [1125899906842623, 1023]
/-- Mask segment `1` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s1 : List Bool :=
  rkmUnpackMaskHi128T4 [50, 50, 29]
    [1125899906842623, 1125899906842623, 536870911]
/-- Mask segment `2` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s2 : List Bool :=
  rkmUnpackMaskHi128T4 [50, 50, 50, 50, 15]
    [1125899906842623, 1125899906842623, 1125899906842623, 1125899906842623, 32767]
/-- Mask segment `3` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s3 : List Bool :=
  rkmUnpackMaskHi128T4 [50, 50, 50, 44]
    [1125899906842623, 1125899906842623, 1125899906842623, 17592186044415]
/-- Mask segment `4` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s4 : List Bool :=
  rkmUnpackMaskHi128T4 [50, 50, 50, 50, 50, 50, 45]
    [1125899906842623, 1125899906842623, 1125899906842623, 1125899906842623, 1125899906842623,
     1125899906842623, 35184372088831]
/-- Mask segment `5` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s5 : List Bool := rkmUnpackMaskHi128T4 [20] [1048575]
/-- Mask segment `6` for `(m = 128, r = 384)`. -/
def rkmMkHiHiB_m128_r384_s6 : List Bool :=
  rkmUnpackMaskHi128T4 [50, 50, 50, 50, 50, 50, 47]
    [1125899906842623, 1125899906842623, 1125899906842623, 1125899906842623, 1125899906842623,
     1125899906842623, 140737488355327]
/-- Prefix-kick masks for `(m = 128, r = 384)`. -/
def rkmMasksHiHiB_m128_r384 : List (List Bool) :=
  [rkmMkHiHiB_m128_r384_s0, rkmMkHiHiB_m128_r384_s1, rkmMkHiHiB_m128_r384_s2,
   rkmMkHiHiB_m128_r384_s3, rkmMkHiHiB_m128_r384_s4, rkmMkHiHiB_m128_r384_s5,
   rkmMkHiHiB_m128_r384_s6, []]
/-- Part `0` of `rkmRowHiHiB_m128_r384`. -/
def rkmRowHiHiB_m128_r384_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Part `1` of `rkmRowHiHiB_m128_r384`. -/
def rkmRowHiHiB_m128_r384_p1 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 5, 30, 0, 119, 15, 246, 241, 201, 893, 1,
   1363, 316, 728, 777]
/-- Part `2` of `rkmRowHiHiB_m128_r384`. -/
def rkmRowHiHiB_m128_r384_p2 : List ℕ :=
  [38, 215, 0, 65, 302, 77, 1031, 93, 193, 16, 4, 617, 203, 208, 362, 11, 612, 167, 103, 1220, 700,
   1931, 9, 2971, 1047, 3343, 9, 37, 174, 0, 493, 1048, 1175, 48, 173, 140, 78, 405, 76, 228, 982,
   989, 297, 89, 1995, 4356, 1636, 1313, 11902, 9354, 370, 20668, 19754, 213, 29984, 24047, 1143,
   34091, 16572, 2943, 23154, 8654, 376, 10708]
/-- Part `3` of `rkmRowHiHiB_m128_r384`. -/
def rkmRowHiHiB_m128_r384_p3 : List ℕ :=
  [20724, 3654, 34111, 96187, 655, 256127, 93577, 294941, 512655, 155675, 1214195, 12631, 1942864,
   39387, 2450469, 169986, 2611412, 171433, 2377010, 18104, 1738616, 171532, 848183, 1270089,
   137030, 3400301, 60879, 5799381, 676486, 7014494, 1486193, 5631100, 1301163, 2760556, 132816,
   1010279, 512071, 359980, 2738114, 400400, 2852808, 375918, 454556, 7550, 452904, 2376817,
   1332044, 7277370, 147067, 4576164, 191218, 8141, 46341, 3553579, 3237570, 2209072, 3476762,
   36888, 51921, 195265, 3097448, 2028466, 1391022, 410120]
/-- Part `4` of `rkmRowHiHiB_m128_r384`. -/
def rkmRowHiHiB_m128_r384_p4 : List ℕ :=
  [403101, 901790, 957072, 1886145, 525050, 1247882, 47765, 427629, 2998581, 2369455, 119092,
   1013594, 4201985, 29707, 150275, 2560580, 172350, 1509920, 406790, 1350226, 1203609, 258675,
   2031370, 35635, 1763039, 756317, 828955, 1762420, 71844, 2166008, 188387, 1642900, 1076317,
   668652, 2017324, 36743, 2314183, 215699, 1802224, 1062538, 880235, 2020030, 155087, 2540126,
   38775, 2397883, 564238, 1737665, 1461315, 910920, 2364877, 264109, 3000975, 2280, 3268605,
   164357, 3221738, 676465, 3002807, 1426407, 2780641, 2316150, 2726787, 3267992]
/-- Part `5` of `rkmRowHiHiB_m128_r384`. -/
def rkmRowHiHiB_m128_r384_p5 : List ℕ :=
  [3051161, 4166734, 4124164, 4717209, 6712195, 4264756, 12190795, 2081336, 21782889, 27895,
   32704528, 10273467, 26968654, 71692373, 7600822, 99797571, 142727291, 234242915, 409085389,
   1129219, 79752786, 3079883447, 147048509, 7265265166, 7458248739, 7706345878, 632864307, 867789,
   5212151, 5349729594, 50444368221, 144351286863, 222266922491, 225631684642, 166449768293,
   94198471799, 42270849853, 15367845868, 4592956753, 1139914301, 236596697, 41264650, 6065908,
   752745, 78877, 6970, 517, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 384)`. -/
def rkmRowHiHiB_m128_r384 : List ℕ :=
  rkmRowHiHiB_m128_r384_p0 ++
    (rkmRowHiHiB_m128_r384_p1 ++
    (rkmRowHiHiB_m128_r384_p2 ++
    (rkmRowHiHiB_m128_r384_p3 ++
    (rkmRowHiHiB_m128_r384_p4 ++ rkmRowHiHiB_m128_r384_p5))))
end

public section
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T4`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi128T4 : (0 : ℕ) = 0 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi128T3) rfl).right
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private theorem bNatBle_le : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bNatBle_le h)
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; revert h
  cases h1 : Nat.ble a b with
  | false => exact Bool.noConfusion
  | true =>
    cases h2 : Nat.ble b a with
    | false => exact Bool.noConfusion
    | true => exact fun _ => Nat.le_antisymm (bNatBle_le h1) (bNatBle_le h2)
private def bNLE : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bNatEq x y) (bNLE xs ys) false
  | _, _ => false
private theorem bNLE_true : ∀ {xs ys : List ℕ}, bNLE xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bNLE at h; revert h
    cases hx : bNatEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bNatEq_true hx) (bNLE_true h)
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private abbrev bZ : ℕ := 2000000000000000
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
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
private theorem bDec_len (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | u :: cs => by rw [bDec_cons z u cs, altIntLen, altListLen, bDec_len z cs]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bEnc1 z x with
    | none => none
    | some u =>
      match bEnc z xs with
      | none => none
      | some us => some (uConsNat u us)
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
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
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
private abbrev bStepVal (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢
    have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
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
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  rw [uConsNat_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | _ :: _ => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by unfold bTailN; rw [bDec_cons]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCV z d b0 c0 b v (bHeadOr z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uConsNat (bCV z d b0 c0 b z (bHeadOr z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uConsNat (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSl_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_nil, rkmUltraSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSl_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uConsNat b (uConsNat (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      uConsNat (bStepVal (bHeadOr z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTailN vs) (bTailN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bStepVal v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uConsNat (bStepVal v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uConsNat (bStepVal z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] =>
        uConsNat (bStepVal z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTailN vs) (bTailN cs)
      dsimp only [mkHbZ] at hrec; rw [← n0m z] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uConsNat_eq, uConsNat_eq]; cases vs with
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
    change 2 * (rem + 1) ≤ l.length + 2 at h
    have hl : 2 * rem ≤ l.length := by omega
    have ha : (b :: bz :: l) ++ t = b :: bz :: (l ++ t) := rfl
    rw [ha]; cases vs with
    | nil => cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz [] [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz [] cT hl]
    | cons v vT => cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz vT [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz vT cT hl]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4P (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) : List ℕ := [b1, z1, b2, z2, b3, z3, b4, z4]
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private theorem hbz4C_app (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) :
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 t = hbz4P b1 z1 b2 z2 b3 z3 b4 z4 ++ t := rfl
private theorem hbz4P_len (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) :
    (hbz4P b1 z1 b2 z2 b3 z3 b4 z4).length = 8 := rfl
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => k (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r)
private theorem fH4_eq {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ => dsimp only [fH4, fL]; rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
    match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t)
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
    dsimp only [toH4]; cases h : toH4 bs with
    | tail _ => have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
private def takeH4 : ℕ → HbZ4 → List ℕ
  | 0, _ => []
  | _ + 1, HbZ4.tail l => l
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r =>
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (takeH4 k r)
private theorem takeH4_spec : ∀ (k : ℕ) (hbz : HbZ4),
    takeH4 k hbz = hbz4L hbz ∨
      ∃ t, hbz4L hbz = takeH4 k hbz ++ t ∧ 8 * k ≤ (takeH4 k hbz).length
  | 0, hbz => Or.inr ⟨hbz4L hbz, rfl, Nat.zero_le _⟩
  | _ + 1, HbZ4.tail _ => Or.inl rfl
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => by
    dsimp only [takeH4, hbz4L]
    cases takeH4_spec k r with
    | inl heq => exact Or.inl (congrArg (hbz4C b1 z1 b2 z2 b3 z3 b4 z4) heq)
    | inr hex =>
      cases hex with
      | intro t hp =>
        refine Or.inr ⟨t, ?_, ?_⟩
        · rw [hbz4C_app, hbz4C_app, hp.1, List.append_assoc]
        · rw [hbz4C_app, List.length_append, hbz4P_len]; omega
private theorem bSlZ_takeH4 (z d k : ℕ) (hbz : HbZ4) (rem p0 q0 : ℕ)
    (vs cs : List ℕ) (h : rem ≤ 4 * k) :
    bSlZ z d rem p0 q0 (takeH4 k hbz) vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs := by
  cases takeH4_spec k hbz with
  | inl heq => rw [heq]
  | inr hex =>
    cases hex with
    | intro t hp =>
      rw [hp.1]; exact (bSlZ_pfx z d rem (takeH4 k hbz) t p0 q0 vs cs (by omega)).symm
private inductive Q4 : Type
  | tail : List ℕ → Q4
  | c4 : ℕ → ℕ → ℕ → ℕ → Q4 → Q4
private def q4L : Q4 → List ℕ
  | Q4.tail xs => xs
  | Q4.c4 x1 x2 x3 x4 r => x1 :: x2 :: x3 :: x4 :: q4L r
private def q4S (x1 x2 x3 x4 : ℕ) (r : Q4) : Q4 :=
  match Nat.add 1 x1 with
  | 0 => r
  | v1 + 1 =>
    match Nat.add 1 x2 with
    | 0 => r
    | v2 + 1 =>
      match Nat.add 1 x3 with
      | 0 => r
      | v3 + 1 =>
        match Nat.add 1 x4 with
        | 0 => r
        | v4 + 1 =>
          match r with
          | Q4.tail xs => Q4.c4 v1 v2 v3 v4 (Q4.tail xs)
          | Q4.c4 y1 y2 y3 y4 yr => Q4.c4 v1 v2 v3 v4 (Q4.c4 y1 y2 y3 y4 yr)
private theorem q4S_eq (x1 x2 x3 x4 : ℕ) (r : Q4) : q4S x1 x2 x3 x4 r = Q4.c4 x1 x2 x3 x4 r := by
  unfold q4S; rw [n1a x1, n1a x2, n1a x3, n1a x4]; cases r <;> rfl
private def toQ4 : List ℕ → Q4
  | x1 :: x2 :: x3 :: x4 :: xs => q4S x1 x2 x3 x4 (toQ4 xs)
  | [] => Q4.tail []
  | [x1] => fN x1 fun y1 => Q4.tail [y1]
  | [x1, x2] => fN x1 fun y1 => fN x2 fun y2 => Q4.tail [y1, y2]
  | [x1, x2, x3] => fN x1 fun y1 => fN x2 fun y2 => fN x3 fun y3 => Q4.tail [y1, y2, y3]
private theorem q4L_toQ4 : ∀ (xs : List ℕ), q4L (toQ4 xs) = xs
  | [] => rfl
  | [_] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq]; rfl
  | [_, _] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | [_, _, _] =>
    by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | x1 :: x2 :: x3 :: x4 :: xs => by
    dsimp only [toQ4]; rw [q4S_eq]; dsimp only [q4L]; rw [q4L_toQ4 xs]
private def q4Hd (z : ℕ) : Q4 → ℕ
  | Q4.c4 x _ _ _ _ => x
  | Q4.tail xs => bHeadOr z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHeadOr z (q4L w) := by
  cases w <;> rfl
private def q4AP : Q4 → Bool
  | Q4.tail xs => bAllPos xs
  | Q4.c4 x1 x2 x3 x4 r =>
    match Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | 0 => q4AP r
    | _ + 1 => false
private theorem pos1_false {x : ℕ} (h : (1 - x) = 0) : Nat.ble x 0 = false := by
  cases x with
  | zero => cases h
  | succ _ => rfl
private theorem q4AP_pos : ∀ (w : Q4), q4AP w = true → bAllPos (q4L w) = true
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
      dsimp only [q4L, bAllPos]
      rw [pos1_false h1, pos1_false h2, pos1_false h3, pos1_false h4]
      exact q4AP_pos r h
private def bChkV (out : Q4) : Option Q4 :=
  match out with
  | Q4.tail xs => cond (bAllPos xs) (some (Q4.tail xs)) none
  | Q4.c4 x1 x2 x3 x4 r =>
    cond (q4AP (Q4.c4 x1 x2 x3 x4 r)) (some (Q4.c4 x1 x2 x3 x4 r)) none
private theorem bChkV_eq (out : Q4) : bChkV out = cond (q4AP out) (some out) none := by
  cases out <;> rfl
private def bSlQ4 (z d rT : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Q4 → Q4
  | 0, p0, q0, hbz, vs, cs => toQ4 (bSlZ z d rT p0 q0 (takeH4 1 hbz) (q4L vs) (q4L cs))
  | q + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | HbZ4.tail l =>
      toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0 l (q4L vs) (q4L cs))
    | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      match vs with
      | Q4.tail vxs =>
        toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
          (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) vxs (q4L cs))
      | Q4.c4 v1 v2 v3 v4 vR =>
        match cs with
        | Q4.tail cxs =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR))
            (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs)
        | Q4.c4 c1 c2 c3 c4 cR =>
          match Nat.add 1 (Nat.mul b4 c4) with
          | 0 => Q4.tail []
          | bc4 + 1 =>
            q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bStepVal v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bStepVal v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
              (bSlQ4 z d rT q bc4 z4 bR vR cR)
private theorem bSlQ4_eq (z d rT : ℕ) (hr : rT ≤ 4) :
    ∀ (q p0 q0 : ℕ) (hbz : HbZ4) (vs cs : Q4),
    q4L (bSlQ4 z d rT q p0 q0 hbz vs cs) =
      bSlZ z d (4 * q + rT) p0 q0 (hbz4L hbz) (q4L vs) (q4L cs)
  | 0, p0, q0, hbz, vs, cs => by
    dsimp only [bSlQ4]; rw [q4L_toQ4]
    have h0 : 4 * 0 + rT = rT := by omega
    rw [h0]; exact bSlZ_takeH4 z d 1 hbz rT p0 q0 (q4L vs) (q4L cs) hr
  | q + 1, p0, q0, hbz, vs, cs => by
    have hrem : Nat.add (Nat.mul 4 (Nat.add q 1)) rT = 4 * (q + 1) + rT := by
      simp only [Nat.add_eq, Nat.mul_eq]
    have hq2 : Nat.add q 2 = q + 2 := by rw [Nat.add_eq]
    have hle : 4 * (q + 1) + rT ≤ 4 * (q + 2) := by omega
    cases hbz with
    | tail l => dsimp only [bSlQ4, hbz4L]; rw [q4L_toQ4, hrem]
    | c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      cases vs with
      | tail vxs =>
        dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
        exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
          (4 * (q + 1) + rT) p0 q0 vxs (q4L cs) hle
      | c4 v1 v2 v3 v4 vR =>
        cases cs with
        | tail cxs =>
          dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
          exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
            (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs hle
        | c4 c1 c2 c3 c4 cR =>
          dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq]
          have h4 : 4 * (q + 1) + rT = ((((4 * q + rT) + 1) + 1) + 1) + 1 := by omega
          rw [h4]; dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHeadOr]
          rw [uConsNat_eq, uConsNat_eq, uConsNat_eq, uConsNat_eq]
          rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bStg_sound (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs = some out) :
    bDec z (q4L out) =
      rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z (q4L vs)) (bDec z (q4L cs)) := by
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
    have hp := q4AP_pos _ hv
    rw [heq] at hp; rw [← h', heq]
    unfold rkmUltraHornerStage; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSl_sound z _ _ 0 z bns (q4L vs) (q4L cs) hp
private def bBind (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4)
    (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL h4 vs cs with
    | none => none
    | some out => k nL out
private theorem bBind_sound (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL (toH4 (mkHbZ z bns)) vs cs kB = some out)
    (hk : ∀ (mid : Q4), kB (rkmNextLen mL cL) mid = some out →
      bDec z (q4L out) = kU (rkmNextLen mL cL) (bDec z (q4L mid))) :
    bDec z (q4L out) = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z (q4L vs)) (bDec z (q4L cs)))
        (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound bns hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (h4 : HbZ4) (vs : Q4) : Option Q4 :=
  bBind z 16 mL c h4 vs vs fun l1 c1 => bBind z 15 mL l1 h4 vs c1 fun l2 c2 =>
  bBind z 14 mL l2 h4 vs c2 fun l3 c3 => bBind z 13 mL l3 h4 vs c3 fun l4 c4 =>
  bBind z 12 mL l4 h4 vs c4 fun l5 c5 => bBind z 11 mL l5 h4 vs c5 fun l6 c6 =>
  bBind z 10 mL l6 h4 vs c6 fun l7 c7 => bBind z 9 mL l7 h4 vs c7 fun l8 c8 =>
  bBind z 8 mL l8 h4 vs c8 fun l9 c9 => bBind z 7 mL l9 h4 vs c9 fun la ca =>
  bBind z 6 mL la h4 vs ca fun lb cb => bBind z 5 mL lb h4 vs cb fun lc cc =>
  bBind z 4 mL lc h4 vs cc fun ld cd => bBind z 3 mL ld h4 vs cd fun le ce =>
  bBind z 2 mL le h4 vs ce fun lf cf => bStg z 1 mL lf h4 vs cf
private theorem bStep_sound (bns : List ℕ) {z mL cL : ℕ} {vs out : Q4}
    (h : bStep z mL cL (toH4 (mkHbZ z bns)) vs = some out) :
    bDec z (q4L out) = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z (q4L vs)) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  exact bStg_sound bns h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Option Q4
  | 0, _, _, _, vs => some vs
  | k + 1, mL, cL, h4, vs =>
    match bStep z mL cL h4 vs with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL h4 vNext
private theorem bIter_sound (bns : List ℕ) (z : ℕ) : ∀ (k mL cL : ℕ) (vs out : Q4),
    bIter z k mL cL (toH4 (mkHbZ z bns)) vs = some out →
    bDec z (q4L out) = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z (q4L vs))
  | 0, _, _, _, _, h => by injection h with h'; rw [← h']; rfl
  | k + 1, mL, cL, vs, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL (toH4 (mkHbZ z bns)) vs with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound bns hs]
      exact bIter_sound bns z k mL (rkmNextLen16 mL cL) vNext out h
private def fQ4 {α : Type} (v : Q4) (k : Q4 → α) : α :=
  match v with
  | Q4.tail xs => k (Q4.tail xs)
  | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4_eq {α : Type} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by
  cases v <;> rfl
private def fSp : List ℕ → List ℕ
  | [] => []
  | x :: xs => uConsNat x (fSp xs)
private theorem fSp_eq : ∀ (xs : List ℕ), fSp xs = xs
  | [] => rfl
  | x :: xs => by dsimp only [fSp]; rw [uConsNat_eq, fSp_eq xs]
private def bSlideChk (k mL : ℕ) (bns vns out : List ℕ) : Bool :=
  fL (fSp bns) fun bF => fL (fSp vns) fun vF => fL (fSp out) fun oF =>
    fN (altListLen vF) fun cL =>
      fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        fQ4 (toQ4 vF) fun vs0 =>
          match bIter bZ k mL cL h4 vs0 with
          | none => false
          | some w => bNLE (q4L w) oF
private abbrev pWOk (k mL : ℕ) (bns : List ℕ) (vi : List ℤ) (vo : List ℕ) : Prop :=
  muxFastIterFullT16 k mL (uOfNatHb bns) vi = bDec bZ vo
private def bSlChkZN (k mL : ℕ) (bns : List ℕ) (vi : List ℤ) (out : List ℕ) : Bool :=
  match bEnc bZ vi with
  | none => false
  | some vns => bSlideChk k mL bns vns out
private theorem bSlSndNN {k mL : ℕ} {bns vns out : List ℕ}
    (h : bSlideChk k mL bns vns out = true) : pWOk k mL bns (bDec bZ vns) out := by
  unfold bSlideChk fL fN at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fH4_eq, fQ4_eq,
    fSp_eq bns, fSp_eq vns, fSp_eq out] at h
  revert h
  cases hi : bIter bZ k mL (altListLen vns) (toH4 (mkHbZ bZ bns)) (toQ4 vns) with
  | none => intro h; exact Bool.noConfusion h
  | some w =>
    intro h; change bNLE (q4L w) out = true at h
    have hw := bIter_sound bns bZ k mL (altListLen vns) (toQ4 vns) w hi
    rw [bNLE_true h, q4L_toQ4 vns, ← bDec_len bZ vns] at hw
    have h2 :
        muxUltraIterFullT16HiChk k 0 mL (uOfNatHb bns) (bDec bZ vns) (bDec bZ out) = true := by
      unfold muxUltraIterFullT16HiChk; dsimp only
      rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
      exact muxIntListEq_eq_true.mpr hw.symm
    exact muxUltraIterFullT16HiChk_sound h2
private theorem bSlSndZN {k mL : ℕ} {bns : List ℕ} {vi : List ℤ} {out : List ℕ}
    (h : bSlChkZN k mL bns vi out = true) : pWOk k mL bns vi out := by
  unfold bSlChkZN at h; revert h
  cases hv : bEnc bZ vi with
  | none => intro h; dsimp only at h; cases h
  | some vns =>
    intro h; dsimp only at h; rw [← bEnc_sound bZ vi vns hv]; exact bSlSndNN h
private theorem pChnN {k1 k2 mL : ℕ} {bns : List ℕ} {vi : List ℤ} {vm vo : List ℕ}
    (kS : ℕ) (h1 : pWOk k1 mL bns vi vm) (h2 : bSlideChk k2 mL bns vm vo = true)
    (hk : k1 + k2 = kS) : pWOk kS mL bns vi vo := by
  unfold pWOk at h1 ⊢; rw [← hk, muxFastIterFullT16_add, h1]; exact bSlSndNN h2
private theorem bWalkBridge {k mL : ℕ} {bns : List ℕ} {vZ : List ℤ} {vk : List ℕ}
    {hb vi vo : List ℤ} (hw : pWOk k mL bns vZ vk)
    (hh : muxIntListEq hb (uOfNatHb bns) = true)
    (hi : muxIntListEq vi vZ = true)
    (ho : muxIntListEq (bDec bZ vk) vo = true) :
    muxFastIterFullT16 k mL hb vi = vo := by
  rw [muxIntListEq_eq_true.mp hh, muxIntListEq_eq_true.mp hi,
    ← muxIntListEq_eq_true.mp ho]
  exact hw
private def phbn_0_p0 : List ℕ := [140402937560969,197524896380166,240648510930282,
  276409577646784,307392481147399,334929486215274,359815967956562,382572678084111,403563051785524,
  423052934532703,441243930652345,458293362268174,474326881455781,489446796317282,503737769211665,
  517270836174892,530106316011852,542295962972550,553884590749101,564911318602136,575410542024616,
  585412699045980,594944882530086,604031334763855,612693850922400,620952111167610,628823956257235,
  636325618002933,643471913314928,650276408635824,656751560109629,662908833724350,668758808815680,
  674311267659842,679575273368132,684559237889487,689270981604941,693717785739998,697906438613487,
  701843276573430,705534220333593,708984807312255,712200220482375,715185314165916,717944637141464,
  720482453381159,722802760688322,724909307469555]
private def phbn_0_p1 : List ℕ := [726805607843218,728494955259103,729980434780996,
  731264934163975,732351153841214,733241615920307,733938672276275,734444511817263,734761166989080,
  734890519576119,734834305848489,734594121098378,734171423602473,733567538041733,732783658404649,
  731820850395495,730680053364591,729362081773530,727867626204254,726197253917075,724351408958867,
  722330411818875,720134458625689,717763619874946,715217838673131,712496928478415,709600570314695,
  706528309429838,703279551363419,699853557382977,696249439240732,692466153194823,688502493230082,
  684357083403149,680028369224945,675514607979934,670813857865896,665923965819588,660842553872248,
  655567003853664,650094440233830,644421710855881,638545365271994,632461630343639,626166382707034,
  619655117631576,612922913710142,605964392711667]
private def phbn_0_p2 : List ℕ := [598773673793107,591344321103177,583669283605446,
  575740825691967,567550446835454,559088788117492,550345522944792,541309228586971,531967234285200,
  522305440517777,512308102461712,501957568608763,491233962661171,480114792922141,468574467919952,
  456583689210871,444108681015945,431110199667824,417542240659981,403350322123495,388469161572916,
  372819461017920,356303342376878,338797667774023,320143906055485,300132072336823,278473853066209,
  254754401225418,228337516676434,198153331908613,162118399904257,114862203597529]
private def phbn_0 : List ℕ := pCat phbn_0_p0 (pCat phbn_0_p1 phbn_0_p2)
private def pvi_0 : List ℤ := [rkmP 1000000000000000]
private def pvon_0_p0 : List ℕ := [2000000000005286,2000000000044129,2000000000258943,
  2000000001233198,2000000005055865,2000000018428125,2000000060945085,2000000185468298,
  2000000524730017,2000001391044907,2000003476696668,2000008233393186,2000018550802372,
  2000039903832046,2000082187551921,2000162491340259,2000309055554396,2000566574204297,
  2001002825062950,2001716303813617,2002844114028343,2004568859355749,2007122782433232,
  2010787023609368,2015883784462031,2022759522996250,2031758176120436,2043184802112857,
  2057261834140924,2074082072027638,2093564241911468,2115418008059779,2139125363300042,
  2163944138189991,2188936965501153,2213025688925901,2235067421696570,2253944898754227,
  2268661098314779,2278426878487261,2282730871231471,2281383063828631,2274527018464017,
  2262619925690022,2246383928584367,2226735691723418,2204703489030771,2181341872191662]
private def pvon_0_p1 : List ℕ := [2157653271440255,2134523945863504,2112678990695183,
  2092658144824245,2074811408490921,2059311347295476,2046177629766565,2035308858529458,
  2026517004669236,2019560542901141,2014173474888632,2010088593487136,2007054401737174,
  2004845940711701,2003270348838610,2002168276077672,2001412351381414,2000903812894659,
  2000568222672963,2000350958881266,2000212951987338,2000126935113096,2000074325865224,
  2000042750030528,2000024151708055,2000013401316269,2000007303060586,2000003908284722,
  2000002053778406,2000001059657359,2000000536755149,2000000266892357,2000000130254031,
  2000000062385379,2000000029318914,2000000013518184,2000000006113932,2000000002711910,
  2000000001179501,2000000000502916,2000000000210164,2000000000086053,2000000000034512,
  2000000000013548,2000000000005201,2000000000001950,2000000000000709,2000000000000248]
private def pvon_0_p2 : List ℕ := [2000000000000082,2000000000000024,2000000000000005,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_0 : List ℕ := pCat pvon_0_p0 (pCat pvon_0_p1 pvon_0_p2)
private def pvo_0 : List ℤ := bDec bZ pvon_0
private def phbn_1_p0 : List ℕ := [108806381404631,153374530857686,187231078694461,
  215487219015313,240129680568974,262180787258446,282249834890319,300735096620555,317914099913011,
  333989553179055,349114968243794,363409983029656,376970036420338,389872750286588,402182293894451,
  413952460147333,425228890387593,436050719505955,446451816135826,456461733612982,466106450215388,
  475408953169791,484389704992317,493067019950420,501457370989284,509575642233209,517435338434914,
  525048760036474,532427150515353,539580821208637,546519257694970,553251210967021,559784775977327,
  566127459636740,572286239951231,578267617672864,584077661594843,589722048424022,595206098006209,
  600534804551672,605712864404078,610744700810877,615634486082930,620386161473179,625003455055905,
  629489897847878,633848838378929,638083455891102]
private def phbn_1_p1 : List ℕ := [642196772321483,646191663203472,650070867603912,
  653836997198681,657492544576651,661039890851024,664481312647620,667818988531584,671055004926884,
  674191361576873,677229976588805,680172691100550,683021273603617,685777423953030,688442777091432,
  691018906511964,693507327482046,695909500047971,698226831838284,700460680682205,702612357057804,
  704683126383283,706674211163474,708586793002579,710422014493188,712180980990724,713864762281687,
  715474394153314,717010879871674,718475191574593,719868271585290,721191033652141,722444364119518,
  723629123034295,724746145192220,725796241128052,726780198053043,727698780743082,728552732380581,
  729342775352922,730069612010115,730733925384102,731336379871965,731877621885160,732358280466705,
  732778967878176,733140280158168,733442797653835]
private def phbn_1_p2 : List ℕ := [733687085526943,733873694235841,734003159994602,
  734076005210549,734092738901268,734053857092161,733959843195509,733811168371952,733608291875260,
  733351661381164,733041713301020,732678873080994,732263555487429,731796164879003,731277095466260,
  730706731559047,730085447802363,729413609401101,728691572334109,727919683557996,727098281201070,
  726227694747757,725308245213857,724340245312928,723323999614117,722259804691684,721147949266493,
  719988714339688,718782373318773,717529192136305,716229429361362,714883336303972,713491157112629,
  712053128865059,710569481652328,709040438656421,707466216221360,705847023917966,704183064602302,
  702474534467865,700721623091559,698924513473464,697083382070430,695198398823469,693269727178949,
  691297524103537,689281940092868,687223119173865]
private def phbn_1_p3 : List ℕ := [685121198900630,682976310343842,680788578073518,
  678558120135054,676285048018371,673969466620035,671611474198159,669211162319904,666768615801350,
  664283912639507,661757123936211,659188313813605,656577539320910,653924850332143,651230289434406,
  648493891806370,645715685086498,642895689230560,640033916357923,637130370586079,634185047852810,
  631197935725370,628169013195972,625098250462856,621985608696128,618831039787489,615634486082930,
  612395880097371,609115144210143,605792190340117,602426919599207,599019221922834,595568975675845,
  592076047232245,588540290526949,584961546577626,581339642974520,577674393335956,573965596727027,
  570213037038734,566416482324620,562575684091613,558690376541553,554760275759484,550785078844455,
  546764462978125,542698084426037,538585577465871]
private def phbn_1_p4 : List ℕ := [534426553236439,530220598500520,525967274313914,
  521666114592286,517316624566441,512918279115667,508470520967587,503972758751690,499424364892174,
  494824673324090,490172977014816,485468525270723,480710520806378,475898116550747,471030412161586,
  466106450215388,461125212035878,456085613118961,450986498106144,445826635251551,440604710319676,
  435319319841535,429968963645874,424552036568985,419066819231194,413511467749679,407884002235267,
  402182293894451,396404050526075,390546800163622,384607872567181,378584378211861,372473184348921,
  366270887628679,359973782665684,353577825790594,347078593061490,340471231389108,333750401350734,
  326910209905993,319944130756269,312844909468482,305604449657415,298213675407997,290662363602346,
  282938937721260,275030211753001,266921068658609]
private def phbn_1_p5 : List ℕ := [258594051777009,250028838583564,241201552660002,
  232083848739320,222641672263709,212833539975558,202608094509697,191900519749439,180627093430214,
  168676538820409,155895528053299,142062634853627,126837009570562,109643251399781,89356373854634,
  63064304438872]
private def phbn_1 : List ℕ := pCat phbn_1_p0 (pCat phbn_1_p1 (pCat phbn_1_p2 (pCat phbn_1_p3
  (pCat phbn_1_p4 phbn_1_p5))))
private def pvi_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s0 pvo_0
private def pvm_1_1_p0 : List ℕ := [1999999999999996,1999999999999999,1999999999999996,
  1999999999999998,1999999999999993,1999999999999983,1999999999999949,1999999999999804,
  1999999999999274,1999999999997386,1999999999991065,1999999999971061,1999999999910727,
  1999999999736935,1999999999257491,1999999997987531,1999999994750872,1999999986798642,
  1999999967932497,1999999924649232,1999999828494892,1999999621410631,1999999188594691,
  1999998309802243,1999996575203163,1999993242773932,1999987012819740,1999975648437029,
  1999955498644221,1999920424309014,1999861610934259,1999762796653483,1999608511473675,
  1999350407820566,1998993169981860,1998351264019906,1997653139795717,1996094595414356,
  1995035025026468,1991412769150927,1990250072083746,1982923507211507,1981357391493195,
  1970166288840196,1964819589562741,1953217262495466,1939178411218763,1928077179165113]
private def pvm_1_1_p1 : List ℕ := [1909233515886511,1890878351250264,1874357680466366,
  1851696033430859,1830057540288376,1812600289870564,1792275252614041,1772157203006936,
  1758909156012575,1748686530418518,1737973791094598,1732047751388169,1734169996924535,
  1739829237803754,1745752933713201,1755092613073340,1770904487999445,1790613205300678,
  1809562116286052,1826750345952287,1844756095295508,1865374634655005,1887101459892115,
  1906693263748270,1922137292553831,1933898201125057,1943926308601349,1953932514406851,
  1964407245701381,1974736818645070,1983904617374919,1991138007192964,1996187909548544,
  1999271233422456,2000857299502279,2001459247012631,2001505681399386,2001295856203037,
  2001008954467754,2000735779402609,2000512011853201,2000343854837899,2000224489358117,
  2000143163808765,2000089469435555,2000054907326810,2000033134928178,2000019679320518]
private def pvm_1_1_p2 : List ℕ := [2000011508728297,2000006629341896,2000003761959804,
  2000002103283492,2000001158615268,2000000628844855,2000000336285432,2000000177184504,
  2000000091978545,2000000047041211,2000000023702184,2000000011765264,2000000005753109,
  2000000002771243,2000000001314922,2000000000614551,2000000000282892,2000000000128252,
  2000000000057260,2000000000025169,2000000000010889,2000000000004634,2000000000001937,
  2000000000000792,2000000000000316,2000000000000121,2000000000000044,2000000000000013,
  2000000000000002,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_1_1_p3 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_1_1_p4 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_1_1_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_1_1 : List ℕ := pCat pvm_1_1_p0 (pCat pvm_1_1_p1 (pCat pvm_1_1_p2 (pCat pvm_1_1_p3
  (pCat pvm_1_1_p4 pvm_1_1_p5))))
private def pvon_1_p0 : List ℕ := [2000000000033970,1999999999649455,2000000002492863,
  1999999985906687,2000000067087089,1999999722743726,2000001013439140,1999996684275658,
  2000009786427709,1999973813020335,2000063699723531,1999859038895412,2000283419931779,
  1999484058084315,2000844829907425,1998769450354152,2001563992254207,1998327456699727,
  2001383791279118,1999353036350218,1999653093208181,2001159519630593,1998692789227856,
  2000619186353461,2000501203091029,1998772602123425,2000925442446585,2000202696911006,
  1998866590350949,2000919137694236,2000270089431109,1998843479704723,2000696180208956,
  2000608082172767,1998853743585530,2000187373887472,2001025939057545,1999190296662795,
  1999428164522940,2001110576617845,2000039072354126,1998867959626326,2000416166148448,
  2000985992572118,1999260302243037,1999222013368211,2000940252098962,2000580016617096]
private def pvon_1_p1 : List ℕ := [1998948647830936,1999568216982821,2001107036305250,
  2000350821577254,1998868147102305,1999654783078010,2001132227063525,2000410498675599,
  1998887384479465,1999438728276034,2001020693305144,2000728189403070,1999076190445974,
  1998950913636894,2000509464666797,2001011930513653,1999501703258993,1998281949496575,
  1999044682152525,2000183292338318,1999370594906284,1997063925652389,1995623383365344,
  1995679125342165,1995182043582760,1992254315217137,1987600159195632,1983264325316244,
  1979690923524934,1975032373039063,1967392352323936,1956986528541046,1945640199673383,
  1934476029011850,1922630881086811,1908351308219825,1891050420923754,1872054767488774,
  1853409813273894,1836147742004829,1819757527012649,1803210059044922,1786398715789156,
  1770641993098534,1757906030372424,1749532116941431,1745535109879660,1744921466279585]
private def pvon_1_p2 : List ℕ := [1746632810670792,1750337530782014,1756544213317328,
  1766071963484455,1779328273597711,1795878979186236,1814522788742553,1833750231914462,
  1852284010245869,1869425121774006,1885091149738034,1899605780889677,1913393068816208,
  1926726313475755,1939613883618168,1951824475522633,1963000368487363,1972791862440925,
  1980960994578413,1987430649085879,1992280959268084,1995710272223923,1997981928974129,
  1999374130570821,2000142827723418,2000500540240657,2000609186073706,2000582734396103,
  2000495231439793,2000390621607553,2000292044456551,2000209445259376,2000145176015706,
  2000097756716079,2000064182535772,2000041198841239,2000025908740774,2000015987879123,
  2000009692928318,2000005779056258,2000003390957643,2000001959313847,2000001115312311,
  2000000625674358,2000000345996374,2000000188646680,2000000101424211,2000000053776402]
private def pvon_1_p3 : List ℕ := [2000000028120849,2000000014503410,2000000007377804,
  2000000003701716,2000000001831872,2000000000894125,2000000000430430,2000000000204355,
  2000000000095677,2000000000044173,2000000000020106,2000000000009016,2000000000003981,
  2000000000001730,2000000000000735,2000000000000304,2000000000000120,2000000000000043,
  2000000000000014,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_1_p4 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_1_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_1 : List ℕ := pCat pvon_1_p0 (pCat pvon_1_p1 (pCat pvon_1_p2 (pCat pvon_1_p3
  (pCat pvon_1_p4 pvon_1_p5))))
private def pvo_1 : List ℤ := bDec bZ pvon_1
private def phbn_2_p0 : List ℕ := [98817020717568,139384442842889,170264662511792,196090025486424,
  218659892578711,238899569302522,257360179898392,274401749095401,290274998357856,305162946347227,
  319204111333945,332506382810986,345155777739348,357222215033992,368763463431146,379827923383152,
  390456638442907,400684782167157,410542778746691,420057162059103,429251244190968,438145642725078,
  446758701679613,455106831230663,463204784613600,471065885864894,478702218684986,486124784252519,
  493343634020389,500367982185570,507206301517911,513866405467781,520355518884956,526680339226095,
  532847089772575,538861566100488,544729176822476,550454979443590,556043712030628,561499821278899,
  566827487466359,572030646708062,577113010860583,582078085373664,586929185342856,591669449980574,
  596301855692573,600829227921193]
private def phbn_2_p1 : List ℕ := [605254251895104,609579482406893,613807352724219,
  617940182726897,621980186350854,625929478410039,629790080858923,633563928550854,637252874541222,
  640858694978805,644383093623916,647827706027690,651194103403220,654483796215977,657698237518115,
  660838826048736,663906909119992,666903785306907,669830706957067,672688882534791,675479478812985,
  678203622924669,680862404285062,683456876394116,685988058528517,688456937331358,690864468307010,
  693211577228020,695499161460347,697728091212659,699899210714999,702013339331651,704071272612672,
  706073783288196,708021622209300,709915519238909,711756184095976,713544307155911,715280560210017,
  716965597186491,718600054835345,720184553379457,721719697133782,723206075094622,724644261500711,
  726034816367770,727378285998046,728675203466269]
private def phbn_2_p2 : List ℕ := [729926089083350,731131450839073,732291784824933,
  733407575638200,734479296768241,735507410966040,736492370597800,737434617983483,738334585721052,
  739192696997161,740009365884986,740784997629839,741519988923181,742214728165614,742869595719384,
  743484964150912,744061198463836,744598656323004,745097688269874,745558637929690,745981842210849,
  746367631496796,746716329830803,747028255093950,747303719176608,747543028143729,747746482394204,
  747914376814547,748047000927169,748144639033456,748207570351884,748236069151386,748230404880153,
  748190842290085,748117641557046,748011058397124,747871344179028,747698746032809,747493506955027,
  747255865910528,746986057930946,746684314210070,746350862196201,745985925681605,745589724889179,
  745162476556442,744704394016941,744215687279184]
private def phbn_2_p3 : List ℕ := [743696563103170,743147225074638,742567873677083,
  741958706361648,741319917614959,740651699024970,739954239344910,739227724555369,738472337924629,
  737688260067253,736875669001045,736034740202392,735165646660069,734268558927564,733343645173943,
  732391071233346,731411000653123,730403594740677,729369012609054,728307411221310,727218945433710,
  726103768037790,724962029801311,723793879508161,722599463997216,721378928200207,720132415178623,
  718860066159674,717562020571349,716238416076595,714889388606647,713515072393524,712115600001741,
  710691102359224,709241708787491,707767547031091,706268743286341,704745422229370,703197707043503,
  701625719445991,700029579714114,698409406710678,696765317908910,695097429416787,693405856000795,
  691690711109158,689952106894524,688190154236144]
private def phbn_2_p4 : List ℕ := [686404962761557,684596640867779,682765295742030,
  680911033381992,679033958615630,677134175120575,675211785443079,673266891016568,671299592179790,
  669309988194569,667298177263192,665264256545411,663208322175098,661130469276546,659030791980423,
  656909383439404,654766335843469,652601740434895,650415687522930,648208266498179,645979565846686,
  643729673163741,641458675167405,639166657711762,636853705799909,634519903596691,632165334441184,
  629790080858923,627394224573907,624977846520358,622541026854260,620083844964666,617606379484800,
  615108708302936,612590908573079,610053056725438,607495228476703,604917498840129,602319942135435,
  599702631998515,597065641390969,594409042609462,591732907294910,589037306441494,586322310405518,
  583587988914101,580834411073712,578061645378554]
private def phbn_2_p5 : List ℕ := [575269759718801,572458821388682,569628897094425,
  566780052962062,563912354545097,561025866832036,558120654253791,555196780690953,552254309480937,
  549293303425009,546313824795193,543315935341051,540299696296361,537265168385671,534212411830751,
  531141486356928,528052451199325,524945365108988,521820286358917,518677272749994,515516381616811,
  512337669833415,509141193818941,505927009543170,502695172531986,499445737872751,496178760219590,
  492894293798596,489592392412948,486273109447948,482936497875982,479582610261397,476211498765308,
  472823215150326,469417810785213,465995336649464,462555843337820,459099381064712,455625999668632,
  452135748616446,448628677007630,445104833578455,441564266706095,438007024412683,434433154369304,
  430842703899925,427235719985272,423612249266641]
private def phbn_2_p6 : List ℕ := [419972338049664,416316032308009,412643377687036,
  408954419507385,405249202768528,401527772152260,397790172026141,394036446446886,390266639163717,
  386480793621648,382678952964747,378861160039328,375027457397114,371177887298351,367312491714874,
  363431312333137,359534390557192,355621767511637,351693484044514,347749580730173,343790097872092,
  339815075505660,335824553400927,331818571065303,327797167746240,323760382433857,319708253863545,
  315640820518529,311558120632399,307460192191604,303347072937918,299218800370867,295075411750129,
  290916944097897,286743434201218,282554918614296,278351433660764,274133015435934,269899699809007,
  265651522425261,261388518708215,257110723861753,252818172872229,248510900510549,244188941334213,
  239852329689347,235501099712695,231135285333598]
private def phbn_2_p7 : List ℕ := [226754920275939,222360038060066,217950672004698,
  213526855228793,209088620653407,204636001003525,200169028809861,195687736410651,191192155953413,
  186682319396688,182158258511762,177620004884366,173067589916352,168501044827355,163920400656427,
  159325688263664,154716938331797,150094181367775,145457447704332,140806767501520,136142170748243,
  131463687263759,126771346699169,122065178538891,117345212102112,112611476544226,107864000858255,
  103102813876254,98327944270696,93539420555847,88737271089118,83921524072413,79092207553445,
  74249349427052,69392977436492,64523119174720,59639802085658,54743053465443,49832900463668,
  44909370084604,39972489188410,35022284492330,30058782571877,25082009862001,20091992658250,
  15088757117909,10072329261137,5042734972084]
private def phbn_2 : List ℕ := pCat phbn_2_p0 (pCat phbn_2_p1 (pCat phbn_2_p2 (pCat phbn_2_p3
  (pCat phbn_2_p4 (pCat phbn_2_p5 (pCat phbn_2_p6 phbn_2_p7))))))
private def pvi_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s1 pvo_1
private def pvm_2_1_p0 : List ℕ := [1999764792841483,2000726231149724,1998626077288390,
  2001714883744446,1998774704752166,1999954421326391,2001178422668177,1998900178354935,
  1999849688104450,2001166303838627,1999298102251278,1999343125590119,2001078381152535,
  2000034597431803,1998932884589308,2000469200149135,2000840630806196,1999207404659861,
  1999461598734243,2000956681454913,2000244059574501,1998990946546365,2000003481458529,
  2000996337955304,1999807141458695,1999045490494437,2000326490001975,2000907783632113,
  1999588217423324,1999129338705380,2000456318669332,2000850486092823,1999534353056420,
  1999150528592300,2000442613639566,2000865940361101,1999612409266609,1999105134063875,
  2000299289901086,2000927944265463,1999823939671857,1999046486596344,2000017656952347,
  2000956699588793,2000172562573150,1999079762677439,1999614798587628,2000826431224629]
private def pvm_2_1_p1 : List ℕ := [2000602599753587,1999339365994228,1999202380092275,
  2000416311561029,2000934565282632,1999898830297843,1999026512652973,1999742918091136,
  2000878794467996,2000607798682940,1999368022536027,1999119447146134,2000246261220804,
  2000997439055142,2000221667142777,1999104358898443,1999329918123159,2000557085914651,
  2000968405405584,1999964120790618,1999004954701829,1999468460272058,2000691586858357,
  2000949784963604,1999885302248610,1998970583773943,1999455291719030,2000681074193549,
  2001005749654080,2000000807492227,1998985471907763,1999276265379358,2000498386031722,
  2001100402296020,2000327665455693,1999140500380734,1998994378643252,2000067048428358,
  2001069604429188,2000821040043635,1999602816127735,1998840659189075,1999375608467880,
  2000650388025282,2001182954137886,2000481694045294,1999197243785598,1998840948308415]
private def pvm_2_1_p2 : List ℕ := [1999667256412997,2000950595648054,2001336773479808,
  2000490324306626,1999378515139772,1999102351761871,2000172728036646,2001751725607657,
  2002649494943581,2002555819955203,2002080468197443,2002479142093183,2004534229205596,
  2007821254283663,2011428723875874,2014719210858968,2017834626406056,2021863937240598,
  2027972689517214,2036494558593407,2046973073059337,2058563378466928,2070550567280189,
  2082964772158518,2096541205977966,2111969454733749,2129337861743906,2148055538345130,
  2166974934276147,2184788225210372,2200632738234388,2214345448262761,2226159393468481,
  2236279588953164,2244658430135299,2250896572821520,2254262641297702,2253964163529623,
  2249561210702361,2241194219927311,2229495552839801,2215358217141896,2199739053449205,
  2183500095897390,2167256172680122,2151293406695570,2135635523652619,2120217831451830]
private def pvm_2_1_p3 : List ℕ := [2105041091954181,2090222471755170,2075965303485392,
  2062514282471320,2050128148510772,2039055534391925,2029495238640474,2021549454396361,
  2015196985451669,2010303805389281,2006664008372074,2004048444334565,2002240655864214,
  2001053045761175,2000328268425803,1999934990891458,1999764486993634,1999729731874767,
  1999765510464156,1999827530238131,1999889630765957,1999939485604423,1999973862231644,
  1999994454311694,2000004851361979,2000008725643296,2000009000491004,2000007654112822,
  2000005846856268,2000004156041256,2000002800578191,2000001809482165,2000001129543474,
  2000000684935378,2000000405081818,2000000234374935,2000000132977085,2000000074118831,
  2000000040641912,2000000021947184,2000000011681422,2000000006131833,2000000003175855,
  2000000001623498,2000000000819342,2000000000408298,2000000000200923,2000000000097644]
private def pvm_2_1_p4 : List ℕ := [2000000000046863,2000000000022207,2000000000010386,
  2000000000004792,2000000000002180,2000000000000973,2000000000000424,2000000000000179,
  2000000000000071,2000000000000026,2000000000000008,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_1_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_1_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_1_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_1_p8 : List ℕ := [2000000000000000]
private def pvm_2_1 : List ℕ := pCat pvm_2_1_p0 (pCat pvm_2_1_p1 (pCat pvm_2_1_p2 (pCat pvm_2_1_p3
  (pCat pvm_2_1_p4 (pCat pvm_2_1_p5 (pCat pvm_2_1_p6 (pCat pvm_2_1_p7 pvm_2_1_p8)))))))
private def pvm_2_2_p0 : List ℕ := [1998569937589261,1998237192930954,1999427564846944,
  2001013886186241,2001192559871749,1999839361809626,1998806975416443,1999470803573813,
  2000834278963883,2000948408515647,1999697106940865,1998933102321189,1999753473939204,
  2000910403091048,2000690009702034,1999452212616620,1999058503182572,2000077258859388,
  2000960255829940,2000390400708063,1999245613126425,1999249161169672,2000377940804988,
  2000925089487714,2000079478854000,1999124695539935,1999489782793062,2000613824809974,
  2000811013751733,1999797288443826,1999093442748653,1999742302626098,2000769121156443,
  2000650386530176,1999570990074336,1999130104146091,1999971645353521,2000851119081495,
  2000480297853113,1999408976621596,1999202498543637,2000155859183855,2000880904869187,
  2000331014277434,1999305029525510,1999279307726125,2000286122112010,2000883373668285]
private def pvm_2_2_p1 : List ℕ := [2000222651597851,1999246249159519,1999335891218753,
  2000361607673282,2000879747201397,2000167228933137,1999220414648515,1999356495775613,
  2000381931513854,2000885036782303,2000168943737314,1999227522173664,1999325339425518,
  2000355631959159,2000884426283567,2000256249560275,1999242611783486,1999283731743213,
  2000224399703061,2000922916064869,2000365857805249,1999355690420004,1999173665785255,
  2000048911555510,2000896950850713,2000557056559952,1999535871116283,1999086295877122,
  1999780128942014,2000784277937433,2000777779254261,1999823157125868,1999085731694553,
  1999444457201899,2000517335710923,2000950256851395,2000226452678209,1999253041747853,
  1999140712890377,2000053532099643,2000930444105945,2000693216898369,1999656109472979,
  1999025110173116,1999484812946065,2000550694175347,2001013359841678,2000310049306774]
private def pvm_2_2_p2 : List ℕ := [1999264473923698,1999043534075564,1999852370878115,
  2000836824758517,2000938925454632,2000006036283282,1999055519494344,1999122987112482,
  2000101843023819,2000971685974281,2000864900885444,1999864651487394,1998970563304085,
  1999122382807305,2000168519746475,2001038200102586,2000893986836066,1999897755193805,
  1998980391519376,1999009217558390,1999991960877976,2001007149266219,2001081705345751,
  2000157400116587,1999098210279861,1998836401257100,1999585854567354,2000714757679950,
  2001260525090107,2000729259581836,1999559963565966,1998762496030076,1999016061254186,
  2000104760090863,2001168638574753,2001424619286545,2000736289730531,1999697127357904,
  1999219916659717,1999880013497243,2001481103667247,2003229311597178,2004398031486073,
  2004918405012764,2005439752072350,2006901983427756,2009994796973582,2014836049716365]
private def pvm_2_2_p3 : List ℕ := [2021001995665319,2027873575215549,2035112249517929,
  2042967387600623,2052186820905580,2063577297008514,2077520357380209,2093754762181700,
  2111509797905339,2129843656471296,2147975442468285,2165470611988837,2182234471926821,
  2198336372144396,2213745757241834,2228109899729750,2240697980092364,2250552415024624,
  2256771558190599,2258780751800451,2256473644787086,2250191301801287,2240585480790187,
  2228441474370979,2214520214664963,2199449908925529,2183676846172166,2167474356656180,
  2150999221926383,2134372808778007,2117756052847310,2101390888536507,2085596233617949,
  2070726215589517,2057111773561399,2045008646941022,2034566811851807,2025824880761311,
  2018723943567886,2013131660574026,2008868458803467,2005730937678889,2003510694141545,
  2002008571400507,2001044857471710,2000465838361029,2000146948313505,1999992826630324]
private def pvm_2_2_p4 : List ℕ := [1999934843128952,1999926909670401,1999940500119681,
  1999959709693314,1999976947782126,1999989570156998,1999997502019905,2000001730597519,
  2000003463314321,2000003736795171,2000003294544163,2000002600790745,2000001906553126,
  2000001322290632,2000000877298567,2000000560865909,2000000347275103,2000000209039120,
  2000000122681522,2000000070359771,2000000039506507,2000000021750664,2000000011756654,
  2000000006245378,2000000003263467,2000000001678664,2000000000850504,2000000000424650,
  2000000000209029,2000000000101469,2000000000048583,2000000000022945,2000000000010688,
  2000000000004906,2000000000002217,2000000000000982,2000000000000423,2000000000000176,
  2000000000000069,2000000000000025,2000000000000007,2000000000000001,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_2_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_2_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_2_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_2_p8 : List ℕ := [2000000000000000]
private def pvm_2_2 : List ℕ := pCat pvm_2_2_p0 (pCat pvm_2_2_p1 (pCat pvm_2_2_p2 (pCat pvm_2_2_p3
  (pCat pvm_2_2_p4 (pCat pvm_2_2_p5 (pCat pvm_2_2_p6 (pCat pvm_2_2_p7 pvm_2_2_p8)))))))
private def pvm_2_3_p0 : List ℕ := [1999995438565473,1999977613779762,1999925382275124,
  1999805981876047,1999585540103674,1999256146556536,1998871934927869,1998568854159052,
  1998533970743232,1998909394941312,1999666667060824,2000540315306413,2001110649509577,
  2001041085145234,2000339578512361,1999435229652798,1998944335934666,1999233218447283,
  2000099025786110,2000869727580643,2000916218844351,2000191108272308,1999312267180377,
  1999054957358098,1999655890704664,2000566559999466,2000934209224150,2000405800054426,
  1999489523248158,1999084114765973,1999594034264411,2000509062734305,2000897252072957,
  2000360925213748,1999450427225585,1999126921555643,1999719736885364,2000620189114915,
  2000832274682499,2000170911152175,1999292543847614,1999233417434600,1999967004485893,
  2000786893322070,2000681756379258,1999857535983904,1999171473662752,1999419289738167]
private def pvm_2_3_p1 : List ℕ := [2000339540579998,2000840490522745,2000425959292907,
  1999498932627296,1999153069071541,1999788516232041,2000635643592955,2000785440785340,
  2000014715579357,1999222298473163,1999350275399341,2000198187750898,2000834652589448,
  2000512970457414,1999572865516702,1999152130552220,1999703699567253,2000585263889539,
  2000816335000880,2000084095753145,1999248139019274,1999304344492704,2000145237740545,
  2000821322062836,2000568202657899,1999635181797337,1999124921749243,1999641122295429,
  2000551535596798,2000833352929508,2000174318275941,1999292253213107,1999220788301359,
  2000060779223719,2000816963166356,2000639977962317,1999752092569819,1999128919216274,
  1999483868345494,2000445933829164,2000901478248541,2000326791510631,1999398334952104,
  1999143226662773,1999828310276445,2000719423658063,2000825421504293,1999996924784432]
private def pvm_2_3_p2 : List ℕ := [1999165953809589,1999269331201934,2000168972758086,
  2000876626048011,2000645273892787,1999712170327634,1999067969138432,1999433733302756,
  2000428357242673,2000958060761090,2000455708767751,1999478945841745,1999051784516180,
  1999607822138211,2000584052032113,2000971201488168,2000339754190135,1999336838453016,
  1999022795153584,1999721789695927,2000698195670282,2000965448676803,2000271167192690,
  1999299987754825,1999006491437964,1999701062556104,2000714327729635,2001031276214544,
  2000325163964506,1999298131781854,1998954878863685,1999609902083327,2000630925700071,
  2001068176203043,2000515962891339,1999469303715411,1998890854712888,1999334832959710,
  2000408249643433,2001119717940298,2000813849060785,1999775922283931,1998938443043042,
  1999027496979546,1999954765792200,2000930456359129,2001132057842576,2000377127629412]
private def pvm_2_3_p3 : List ℕ := [1999281552115401,1998763350316340,1999272228581970,
  2000397012361125,2001209721193411,2001048399734362,2000051496910898,1999012253798849,
  1998730386585624,1999411412235231,2000545408561042,2001299638249623,2001119698033694,
  2000126557088491,1999038508402162,1998663538322755,1999319400810724,2000610247891748,
  2001728466920929,2002049912081156,2001580728276268,2000955658795901,2001033907077954,
  2002400079058298,2005089062302270,2008668649203185,2012594021783578,2016616270620378,
  2021019147539019,2026556738676098,2034124218182389,2044340464568081,2057271542248625,
  2072439503740390,2089090312387492,2106548131259731,2124452054608185,2142762546455477,
  2161565552677197,2180802370179164,2200067656263916,2218561833108287,2235204867134600,
  2248856843092665,2258563280992756,2263746861480338,2264292721857779,2260512264802824]
private def pvm_2_3_p4 : List ℕ := [2253010026334745,2242507209518769,2229683508918303,
  2215083321287414,2199101417564172,2182031320964437,2164140369800653,2145734281588047,
  2127187363656434,2108933287343806,2091426655232055,2075092665152406,2060281145393430,
  2047235378841716,2036079301053141,2026821451581571,2019371325088609,2013563086787106,
  2009182108348465,2005990714745472,2003750533825439,2002239804504592,2001264918045368,
  2000666307020908,2000319478335415,2000132424795682,2000040803906975,2000002169350990,
  1999990260669178,1999990002074783,1999993522394960,1999997243239931,1999999913666802,
  2000001390228419,2000001948703092,2000001941123517,2000001655847143,2000001283476867,
  2000000928968373,2000000637432184,2000000418588692,2000000264746990,2000000162012252,
  2000000096254879,2000000055668126,2000000031406258,2000000017314029,2000000009340516]
private def pvm_2_3_p5 : List ℕ := [2000000004936887,2000000002559088,2000000001302094,
  2000000000650792,2000000000319712,2000000000154463,2000000000073416,2000000000034338,
  2000000000015804,2000000000007156,2000000000003184,2000000000001390,2000000000000592,
  2000000000000243,2000000000000095,2000000000000032,2000000000000009,2000000000000002,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_3_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_3_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_3_p8 : List ℕ := [2000000000000000]
private def pvm_2_3 : List ℕ := pCat pvm_2_3_p0 (pCat pvm_2_3_p1 (pCat pvm_2_3_p2 (pCat pvm_2_3_p3
  (pCat pvm_2_3_p4 (pCat pvm_2_3_p5 (pCat pvm_2_3_p6 (pCat pvm_2_3_p7 pvm_2_3_p8)))))))
private def pvm_2_4_p0 : List ℕ := [1999999999938285,1999999999472991,1999999996869376,
  1999999985074419,1999999939459514,1999999784463907,1999999313030954,1999998014864545,
  1999994749094896,1999987211410001,1999971167538668,1999939697601718,1999882632542384,
  1999787629195927,1999642131410317,1999441120149958,1999190816337204,1998926636035420,
  1998698670068817,1998600581240566,1998686976499235,1999042775265807,1999583213051105,
  2000274148351462,2000813671833887,2001123563644961,2000934000851453,2000413269802331,
  1999676903211031,1999113209667995,1999017224741562,1999403265118663,2000160049315552,
  2000783947607052,2000944551323268,2000537797211113,1999754987657240,1999173194284594,
  1999138678090853,1999688162983223,2000487418346451,2000898995354419,2000651721272985,
  1999931266120285,1999235998535426,1999162244950595,1999759101446659,2000523025756414]
private def pvm_2_4_p1 : List ℕ := [2000881646525035,2000501901659006,1999681437424017,
  1999160683849911,1999354955460244,2000096227958459,2000776684207304,2000753192041356,
  2000039783981278,1999315243701525,1999207061441095,1999817529482636,2000620271398729,
  2000832959246188,2000244721798523,1999445323650978,1999172076981137,1999678591240917,
  2000515309777035,2000851932984836,2000335257505144,1999502319404688,1999168600898717,
  1999640751280536,2000479429351852,2000852943623614,2000351259972222,1999492228366354,
  1999164522800752,1999675392765646,2000508124556596,2000840066223979,2000309458171885,
  1999442115403519,1999159253031862,1999755407264729,2000590445950969,2000814231326444,
  2000207360543654,1999373452527373,1999179731015597,1999858181426974,2000691767597260,
  2000786518437293,2000059436917461,1999281110453246,1999245664167462,1999994935629669]
private def pvm_2_4_p2 : List ℕ := [2000767080423994,2000737507776233,1999914665015219,
  1999180567049116,1999321497682688,2000171131786934,2000833440655917,2000631750766043,
  1999770062494367,1999132285312868,1999402061455077,2000317222740399,2000902858216055,
  2000529153733995,1999602269904190,1999099391830014,1999529329452215,2000443807292141,
  2000910248581681,2000438723069265,1999495740241244,1999064037377318,1999613118550885,
  2000571758432023,2000933425518328,2000331389646352,1999396516123618,1999076294274156,
  1999687278652897,2000621875995861,2000942755899758,2000307923858417,1999342992145374,
  1999034248848811,1999708653843057,2000681373287106,2000967957849318,2000291113686720,
  1999331027767727,1999025636838849,1999666951791266,2000640152429157,2001007668020493,
  2000398761682156,1999385124058331,1998951764707615,1999533874301180,2000574315588317]
private def pvm_2_4_p3 : List ℕ := [2001068099493516,2000546069813440,1999511125419369,
  1998933185179847,1999339475373301,2000353898517566,2001056534003764,2000807473095055,
  1999816936521344,1998969582512778,1999039603599654,1999982370652346,2000958347674281,
  2001089752433404,2000255980291397,1999193205493902,1998826501889587,1999463619587220,
  2000556429282720,2001189163127297,2000840281236985,1999793347546037,1998896509631501,
  1998881196376958,1999775851378114,2000875083216855,2001297228073890,2000692145562013,
  1999526579248172,1998712470744348,1998883923801560,1999909038482752,2001010931155459,
  2001371671960614,2000734061371910,1999563189274987,1998689954398986,1998724400221681,
  1999649580790679,2000850520500658,2001536942260876,2001273608682986,2000275471700327,
  1999282134390300,1999099722532556,2000114461828432,2002097041136601,2004419357751008]
private def pvm_2_4_p4 : List ℕ := [2006532739397649,2008396235090966,2010594804010644,
  2014097479447218,2019822523190792,2028265589994138,2039376259787262,2052707924788837,
  2067721319008344,2084064140241254,2101687198876547,2120753267546524,2141395532733429,
  2163446169090868,2186261987906303,2208726943897901,2229433959886711,2246975184885560,
  2260231293665544,2268560581659338,2271838250725989,2270359200975357,2264664955747917,
  2255369746020703,2243042827123087,2228168425418091,2211170114955032,2192466351369147,
  2172521989659173,2151872102526192,2131110817559269,2110851769685041,2091674293034518,
  2074070494370299,2058404910976259,2044893136550085,2033600605221078,2024458755122813,
  2017293402589992,2011859264347998,2007874888969199,2005053441656254,2003126437884315,
  2001859258804312,2001058781236905,2000574505130746,2000295086383615,2000142233934110]
private def pvm_2_4_p5 : List ℕ := [2000063641913263,2000026164648657,2000009950878297,
  2000003834399401,2000001979885810,2000001609641819,2000001567320794,2000001474922809,
  2000001277566647,2000001021969278,2000000763843970,2000000539140584,2000000362364409,
  2000000233393476,2000000144756624,2000000086782185,2000000050437945,2000000028487689,
  2000000015666703,2000000008402731,2000000004401227,2000000002253902,2000000001129610,
  2000000000554517,2000000000266811,2000000000125906,2000000000058296,2000000000026490,
  2000000000011812,2000000000005167,2000000000002214,2000000000000925,2000000000000375,
  2000000000000144,2000000000000050,2000000000000015,2000000000000003,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_4_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_4_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_4_p8 : List ℕ := [2000000000000000]
private def pvm_2_4 : List ℕ := pCat pvm_2_4_p0 (pCat pvm_2_4_p1 (pCat pvm_2_4_p2 (pCat pvm_2_4_p3
  (pCat pvm_2_4_p4 (pCat pvm_2_4_p5 (pCat pvm_2_4_p6 (pCat pvm_2_4_p7 pvm_2_4_p8)))))))
private def pvm_2_5_p0 : List ℕ := [1999999999376901,2000000004159384,1999999980861996,
  2000000069948767,1999999785091480,2000000571653171,1999998660880702,2000002789989305,
  1999994804695620,2000008652003162,1999987164538890,2000016787602687,1999981049636848,
  2000017609626481,1999988149909337,2000002386775130,2000007580360602,1999985580080342,
  2000013061368447,1999992849895522,1999991851756954,2000006593190721,1999975476266567,
  1999978239309590,1999962661147534,1999906072341656,1999869451989482,1999780390919993,
  1999641860272775,1999500056501318,1999291627700378,1999055015993012,1998857957407234,
  1998681303134276,1998607593201231,1998721932252243,1998994666331351,1999441368347996,
  2000029857283493,2000583101607272,2000971405241529,2001101175279062,2000860405537973,
  2000313984554519,1999682734764418,1999167079401585,1998981293201101,1999264596784647]
private def pvm_2_5_p1 : List ℕ := [1999878852065440,2000526324181750,2000929903737226,
  2000860358621822,2000309030419752,1999600065067821,1999135764802358,1999156164359374,
  1999681864032630,2000423105965504,2000882857757794,2000760389008167,2000157545413287,
  1999448595168128,1999099666647118,1999393068303292,2000128988093717,2000751901357017,
  2000821573989160,2000296445876293,1999536731841167,1999120665272713,1999406183221159,
  2000163593949016,2000772250837160,2000762727978683,2000144653668703,1999393777173784,
  1999140215229283,1999628347031311,2000434122011570,2000850953229042,2000536869124614,
  1999766073331511,1999188277626312,1999323220435008,2000080013815345,2000767833838575,
  2000743377694445,2000042766744189,1999315173892710,1999211521202168,1999832318276185,
  2000624494379894,2000835937704102,2000241098206955,1999413395662833,1999159521847020]
private def pvm_2_5_p2 : List ℕ := [1999710490926573,2000529561985120,2000844123974263,
  2000348413717603,1999500295990588,1999131228877522,1999628939678633,2000501284165787,
  2000866676665817,2000368123802863,1999513303957875,1999141972446617,1999617219222532,
  2000482484963597,2000877483737784,2000382385951381,1999486013387959,1999113557677977,
  1999651032834829,2000538751364667,2000872299587600,2000325468205265,1999450746106634,
  1999123927047260,1999686471419807,2000584263191783,2000893316373607,2000275566294088,
  1999365443690008,1999113256790060,1999776683319143,2000663352399226,2000868631289978,
  2000191972759269,1999317335223615,1999128434223970,1999830544867835,2000722372605450,
  2000882699848691,2000127536173202,1999231213832287,1999126168620950,1999920386630629,
  2000792659729772,2000856077329259,2000055575632328,1999198756352038,1999141701093246]
private def pvm_2_5_p3 : List ℕ := [1999947990713530,2000820884004011,2000879393909430,
  2000044867573686,1999148490011963,1999104161121371,1999967590684188,2000868940440989,
  2000901559537183,2000037947749942,1999138748381888,1999084557252660,1999922621265787,
  2000840801766491,2000953350507891,2000143007510970,1999178351425402,1998991296162194,
  1999780165338008,2000798524090720,2001062286846940,2000306354204795,1999249082873542,
  1998898350696257,1999584785868333,2000660674897791,2001126242840558,2000558174125206,
  1999478342762660,1998863061749548,1999266595446793,2000335728346086,2001123985799867,
  2000923990172313,1999895380021737,1998935943698011,1998896874195733,1999828028625707,
  2000926368243103,2001238022670581,2000489623918405,1999317291802992,1998710168817259,
  1999172178405572,2000318102731406,2001213254543906,2001139635223977,2000157356172881]
private def pvm_2_5_p4 : List ℕ := [1999037657455899,1998652427471282,1999305576580514,
  2000508013666698,2001351302087977,2001191392645337,2000131213322406,1998945486593164,
  1998507696861885,1999148003900135,2000415774346802,2001411797696311,2001434062239892,
  2000465798580772,1999172149395953,1998436695481026,1998781709585987,2000065160716493,
  2001631623534902,2002789962430209,2003303335196510,2003603104185101,2004628279323744,
  2007411871251967,2012659791497955,2020544844548482,2030800188311761,2043028426571919,
  2057033406183372,2072982257402509,2091306238196807,2112391134643378,2136215342582774,
  2162114406914934,2188782153467309,2214503883419563,2237517538173244,2256359200331065,
  2270078179467606,2278278534101847,2281017907083212,2278638724839857,2271610065350645,
  2260430446892939,2245602567014956,2227659354831145,2207206430852292,2184949088529375]
private def pvm_2_5_p5 : List ℕ := [2161685678593736,2138265635537886,2115523128757813,
  2094203575026600,2074900099231613,2058012339527654,2043733206776511,2032062524881060,
  2022841426481222,2015798693848257,2010599933066849,2006892033186598,2004337990262440,
  2002640039487018,2001551480047488,2000879221821467,2000479845753503,2000251987468478,
  2000127379874083,2000062195085745,2000029625895351,2000014075836761,2000006937392900,
  2000003723313095,2000002237189359,2000001477798368,2000001024164529,2000000713908204,
  2000000488088710,2000000323513426,2000000207046706,2000000127889756,2000000076324506,
  2000000044081413,2000000024680565,2000000013417458,2000000007093203,2000000003651241,
  2000000001832163,2000000000897113,2000000000429009,2000000000200510,2000000000091650,
  2000000000040986,2000000000017936,2000000000007679,2000000000003212,2000000000001309]
private def pvm_2_5_p6 : List ℕ := [2000000000000516,2000000000000192,2000000000000065,
  2000000000000019,2000000000000004,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_5_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_5_p8 : List ℕ := [2000000000000000]
private def pvm_2_5 : List ℕ := pCat pvm_2_5_p0 (pCat pvm_2_5_p1 (pCat pvm_2_5_p2 (pCat pvm_2_5_p3
  (pCat pvm_2_5_p4 (pCat pvm_2_5_p5 (pCat pvm_2_5_p6 (pCat pvm_2_5_p7 pvm_2_5_p8)))))))
private def pvm_2_6_p0 : List ℕ := [1999998834556752,2000004128758480,1999990475525965,
  2000016128535130,1999979647231862,2000017850387208,1999992761673052,1999993117598817,
  2000015472216617,1999988157678386,1999998578503810,2000012882341257,1999988120136188,
  1999999289298261,2000012190087051,1999989484139313,1999997485051559,2000012431029342,
  1999992042243784,1999994314873406,2000012314075882,1999996052144446,1999990879107509,
  2000010613088667,2000001326923183,1999988602047538,2000006565980083,2000006804977613,
  1999988990243429,2000000420661597,2000010578283841,1999992845504488,1999993682264742,
  2000010353782792,1999998891405228,1999987802696730,2000002823640706,2000000011828100,
  1999976995268777,1999974987556767,1999968664200796,1999923740889927,1999873135106679,
  1999820397765322,1999716395917314,1999568005026232,1999410030501106,1999218547607305]
private def pvm_2_6_p1 : List ℕ := [1998988034053851,1998785871198029,1998654361910157,
  1998600241211972,1998683092520947,1998961676754185,1999398835430662,1999923235669859,
  2000474527997347,2000927270555788,2001118300284643,2000984529513359,2000571310201298,
  1999970573447499,1999361748437014,1999000739953414,1999048530996051,1999472882471925,
  2000112733083545,2000718642675841,2000990616826869,2000761379509105,2000152046859286,
  1999482391333170,1999083091950584,1999176893736695,1999751752028090,2000481043113890,
  2000905662804506,2000769387614681,2000167442756861,1999458357255335,1999087521365131,
  1999330948169951,2000044687133435,2000718701665970,2000873663976146,2000414065819868,
  1999661683817488,1999145317622612,1999264771103131,1999959044794214,2000687416914717,
  2000863929411815,2000358098591935,1999579072232876,1999135665843653,1999387138812901]
private def pvm_2_6_p2 : List ℕ := [2000154271075868,2000805066924232,2000766582521609,
  2000063541608277,1999315207901135,1999168584687483,1999739268625127,2000536682545547,
  2000869985365880,2000425209306185,1999580978927774,1999115353127631,1999474320921340,
  2000320335224660,2000857935708027,2000595308422827,1999782980954241,1999170344618142,
  1999334764110709,2000141932576970,2000826626525566,2000708060816998,1999889341479183,
  1999181576598530,1999284584734464,2000086830786550,2000797062211644,2000725299738803,
  1999938640253548,1999202327733682,1999255224962217,2000066692308067,2000823195338652,
  2000741099055890,1999896676042051,1999160723206008,1999286866244990,2000136977885220,
  2000843050947881,2000692776363924,1999835523467966,1999136238123324,1999318113504701,
  2000214203064846,2000902220565139,2000651160314237,1999712037346892,1999071813280402]
private def pvm_2_6_p3 : List ℕ := [1999404230142557,2000356219963414,2000933288837042,
  2000542705828449,1999591942158395,1999058772280559,1999495977083057,2000464425095386,
  2000964499868149,2000460448914507,1999461326440823,1999015130504026,1999603371709614,
  2000614035908518,2000983929736324,2000326322694766,1999330978138536,1999029534904076,
  1999727379416797,2000706224873550,2000966600767584,2000238580779322,1999255412075751,
  1999021057979878,1999791118562331,2000792212324760,2000994461662453,2000174111050461,
  1999162803918323,1998999226316148,1999856125899478,2000863102616259,2001001851937648,
  2000136493296695,1999134027215304,1998987022821806,1999838048358999,2000854466722125,
  2001045009857507,2000216868837114,1999162897227867,1998904464425147,1999707169516141,
  2000811581278262,2001152353500085,2000386615232250,1999235543405599,1998798006441073]
private def pvm_2_6_p4 : List ℕ := [1999497150907427,2000678046374984,2001234238423209,
  2000648679236865,1999462748729779,1998760029439647,1999174304112732,2000332440284001,
  2001205681109858,2001023653917763,1999940217956587,1998890491031678,1998782880959917,
  1999722803242924,2000922058624717,2001364148615645,2000661978733735,1999386557260895,
  1998593027925580,1998944778068250,2000167328910997,2001277462298461,2001384047878604,
  2000397749752411,1999086780987612,1998461804469127,1998997494714617,2000291053888074,
  2001387080404732,2001489618733088,2000525033231370,1999169174262935,1998355753157001,
  1998634028870235,1999815514880275,2001127787153301,2001752751053097,2001392849262609,
  2000515649512329,2000148647061571,2001378608991156,2004876769532452,2010730550525357,
  2018655049833342,2028421380218774,2040217422979612,2054711426901092,2072771795601796]
private def pvm_2_6_p5 : List ℕ := [2094990333360430,2121252555546543,2150558141769321,
  2181158096182361,2210927049231558,2237803667982938,2260136984260671,2276849324522324,
  2287418586119198,2291748931205060,2290018486766114,2282570701554896,2269873935595937,
  2252534718474871,2231328587028056,2207211692398930,2181290782832277,2154749275026921,
  2128744309503338,2104298815473176,2082212603582654,2063009417194996,2046926351751510,
  2033941807489027,2023830858823569,2016233782430389,2010724240030401,2006867057869337,
  2004260127620542,2002559292748829,2001488290119941,2000837564232120,2000456193702410,
  2000240660139806,2000123206860350,2000061464125231,2000030106258834,2000014662375046,
  2000007230217571,2000003686840585,2000001976482166,2000001117613201,2000000658714982,
  2000000396654119,2000000239326549,2000000142625726,2000000083206114,2000000047288239]
private def pvm_2_6_p6 : List ℕ := [2000000026122118,2000000014015017,2000000007303618,
  2000000003698734,2000000001821502,2000000000872940,2000000000407407,2000000000185288,
  2000000000082164,2000000000035538,2000000000014993,2000000000006166,2000000000002467,
  2000000000000956,2000000000000354,2000000000000124,2000000000000040,2000000000000010,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_6_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_6_p8 : List ℕ := [2000000000000000]
private def pvm_2_6 : List ℕ := pCat pvm_2_6_p0 (pCat pvm_2_6_p1 (pCat pvm_2_6_p2 (pCat pvm_2_6_p3
  (pCat pvm_2_6_p4 (pCat pvm_2_6_p5 (pCat pvm_2_6_p6 (pCat pvm_2_6_p7 pvm_2_6_p8)))))))
private def pvm_2_7_p0 : List ℕ := [1999975212168852,2000014653310374,2000011221952592,
  1999983814558535,1999995634049351,2000015900396817,1999999355382426,1999985385166380,
  2000004553091501,2000012654611054,1999992417505281,1999989775224256,2000009818999070,
  2000007488699765,1999988692884225,1999995408414113,2000012083223560,2000001667514148,
  1999987810361034,2000001159631747,2000011680694796,1999996222254822,1999989375232881,
  2000006089017772,2000009103886744,1999991987410850,1999992788241615,2000009486847285,
  2000005050698987,1999989528919033,1999997272119851,2000010946304105,2000000351201471,
  1999989084836473,2000001974910906,2000010400918815,1999995846482298,1999990554449899,
  2000006098760757,2000008107100727,1999992261137735,1999993543553559,2000009018279275,
  2000004573358410,1999990100168284,1999997455422113,2000010359971061,2000000446209972]
private def pvm_2_7_p1 : List ℕ := [1999989576887631,2000001574660983,2000009955836359,
  1999996218640126,1999990248072365,2000004444862003,2000006346764773,1999989284210863,
  1999985804032782,1999994589813436,1999980645571584,1999947475613413,1999922872557083,
  1999889399379338,1999811370993276,1999699749990752,1999575294345511,1999413975468145,
  1999198390056231,1998969057325238,1998770222899826,1998611962577950,1998529070140601,
  1998598789189923,1998859513022033,1999278961140296,1999810339667160,2000392833776610,
  2000894484921878,2001150787248316,2001077740005172,2000697997895042,2000099839211392,
  1999451455518839,1999003277568407,1998961152808208,1999344377933584,1999990235932498,
  2000640702867219,2001007104027295,2000879437519663,2000293001848124,1999560800991628,
  1999081155298479,1999105039786485,1999627496541232,2000377687986692,2000911123318073]
private def pvm_2_7_p2 : List ℕ := [2000869566972011,2000266087668279,1999501756011123,
  1999077119360853,1999264987894319,1999952550889431,2000686223090528,2000934614360975,
  2000488579456592,1999675181001580,1999119330039416,1999240641223018,1999938468368486,
  2000682931432536,2000896006820905,2000385560619643,1999545188256365,1999080559571576,
  1999400336165899,2000229699923637,2000850545201269,2000735360226918,1999987528471834,
  1999247436816027,1999166375929553,1999839609669770,2000672487190287,2000887382614703,
  2000269531885026,1999401248299505,1999104982313747,1999652843739350,2000522646377841,
  2000896247980185,2000414900899343,1999524511200230,1999086020617415,1999550154277792,
  2000472792303212,2000924569138938,2000440789963748,1999513720582404,1999085589351337,
  1999583400944294,2000498880012489,2000908597349281,2000393804987018,1999467080241878]
private def pvm_2_7_p3 : List ℕ := [1999079293164049,1999651196175406,2000601501106309,
  2000924420574501,2000264661314993,1999321315340931,1999102308573210,1999837448047551,
  2000740287625258,2000855521809283,2000064625365835,1999202267635113,1999183477453164,
  2000040868049716,2000868363308835,2000766932493069,1999826099745586,1999061661299196,
  1999318116562400,2000324582663360,2000979000301104,2000564071173868,1999535829094393,
  1999014519353135,1999561551701784,2000582716405385,2000977149775461,2000316533892625,
  1999305022071520,1999035182332293,1999814397136113,2000811243105978,2000935700173234,
  2000033705194695,1999081271979917,1999126213805190,2000128831863573,2000996732119217,
  2000783402064113,1999721231594429,1998958912977793,1999313991373295,2000403772571405,
  2001067018299452,2000598645842811,1999489343270055,1998908683667624,1999478470102778]
private def pvm_2_7_p4 : List ℕ := [2000612331566882,2001117302849618,2000445755721302,
  1999288168775546,1998862843166590,1999631484414417,2000799795493186,2001144874234950,
  2000299385023973,1999135861231490,1998855066071736,1999745646313531,2000899780374099,
  2001150001454501,2000246086987762,1999090076075610,1998827740473333,1999720740381478,
  2000899920461928,2001216307014609,2000352733056357,1999130027502559,1998722645693936,
  1999535533153475,2000811508880091,2001343063011940,2000614283858696,1999292007788107,
  1998604631990885,1999197790474771,2000538474054790,2001410064440827,2001022750849497,
  1999717427201075,1998645327034282,1998743377910120,1999927416030058,2001187454301052,
  2001461737101110,2000521447541121,1999137945746476,1998433665801120,1998976390246101,
  2000342968768094,2001469317022623,2001482393806964,2000362157468559,1998943495291862]
private def pvm_2_7_p5 : List ℕ := [1998281744809521,1998870848815588,2000287107026046,
  2001499470036621,2001604252362012,2000460305147916,1998803149376891,1997802170528107,
  1998404494314893,2000924340071227,2005134564172717,2010762944640803,2018035727990079,
  2027900013262710,2041772037751602,2060942174863436,2085945598101749,2116197070325522,
  2150027135095930,2185056988635279,2218718318925652,2248709899024461,2273262801968637,
  2291199129812770,2301855034016505,2304967161405425,2300597026785174,2289116963950444,
  2271234573862986,2248009655859920,2220822430586245,2191275732460302,2161042587734826,
  2131691672252710,2104530012063295,2080495195402445,2060113433235863,2043521931020536,
  2030540034616172,2020766587918475,2013681038089389,2008731069289264,2005397096410320,
  2003231230214933,2001873687346404,2001052489156559,2000572939153889,2000302504716926]
private def pvm_2_7_p6 : List ℕ := [2000155148905698,2000077496770369,2000037857466385,
  2000018201472757,2000008689764967,2000004165569472,2000002028327675,2000001012191443,
  2000000519159789,2000000272510958,2000000144994116,2000000077315233,2000000040894510,
  2000000021287736,2000000010847214,2000000005392203,2000000002609961,2000000001228836,
  2000000000562567,2000000000250414,2000000000108387,2000000000045621,2000000000018673,
  2000000000007429,2000000000002866,2000000000001070,2000000000000382,2000000000000127,
  2000000000000036,2000000000000007,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_7_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_7_p8 : List ℕ := [2000000000000000]
private def pvm_2_7 : List ℕ := pCat pvm_2_7_p0 (pCat pvm_2_7_p1 (pCat pvm_2_7_p2 (pCat pvm_2_7_p3
  (pCat pvm_2_7_p4 (pCat pvm_2_7_p5 (pCat pvm_2_7_p6 (pCat pvm_2_7_p7 pvm_2_7_p8)))))))
private def pvm_2_8_p0 : List ℕ := [1999991861233662,1999981827609070,1999977733607262,
  1999987482682338,2000006325876500,2000016999354524,2000007983648373,1999990041775173,
  1999985843397460,2000000730850921,2000013904499883,2000006639293828,1999989895778839,
  1999988941727891,2000005008102438,2000012762348880,1999999999260775,1999987561750527,
  1999995778967309,2000010809280547,2000007409292987,1999991525943601,1999990427888127,
  2000005868379567,2000010842518060,1999996720258653,1999988601365097,2000000879053457,
  2000011419641892,2000001246500839,1999988935477987,1999996934288909,2000010464225982,
  2000004582179344,1999990278893121,1999994180752581,2000008911851954,2000006809833265,
  1999991908266817,1999992410067770,2000007299007046,2000008194711783,1999993441099710,
  1999991343636940,2000005886963710,2000009003094104,1999994708238664,1999990741167724]
private def pvm_2_8_p1 : List ℕ := [2000004776950865,2000009443342141,1999995657152614,
  1999990427433334,2000003987568189,2000009659069662,1999996292149932,1999990287493601,
  2000003499616583,2000009740079966,1999996641640144,1999990253036593,2000003279383078,
  2000009736664705,1999996742011118,1999990288519158,2000003289177778,2000009671627540,
  1999996628954277,1999990375088415,2000003479199578,2000009519655340,1999996261943350,
  1999990332609403,2000003410927349,2000008403211276,1999993844803334,1999986471270242,
  1999995867477493,1999992885691973,1999965294141104,1999937284716062,1999912503229216,
  1999855892712837,1999751630202741,1999620684926111,1999465014810212,1999256829416292,
  1999001665461151,1998754301729282,1998560863054157,1998445998715673,1998463339212601,
  1998686530701250,1999128137371667,1999716024850401,2000346733002676,2000900886505988]
private def pvm_2_8_p2 : List ℕ := [2001219566260399,2001160295592676,2000714600611998,
  2000035914256315,1999358751890931,1998926268645421,1998936262985941,1999429488390802,
  2000194251123827,2000848151451578,2001062001031062,2000730000009985,2000008833884482,
  1999271725944794,1998954468863082,1999280161600647,2000057162011486,2000782726573154,
  2000989553192657,2000546513600395,1999734931805810,1999097439691172,1999102503141796,
  1999776696323292,2000621177882055,2000980330573477,2000576956751882,1999732304957703,
  1999105672569135,1999193524294765,1999943490996190,2000753209427989,2000926858068317,
  2000290890206461,1999397895714286,1999047476742769,1999550511644672,2000448762622934,
  2000935387106565,2000570076608598,1999674684995532,1999073106373151,1999349992896754,
  2000263038989613,2000925880702885,2000674115622928,1999754204300060,1999086792388224]
private def pvm_2_8_p3 : List ℕ := [1999335235284890,2000244811858485,2000905084729830,
  2000651307673600,1999729161027417,1999074793357044,1999379626103826,2000346382751971,
  2000955364574326,2000543275425441,1999545070822670,1999039583486370,1999572319549642,
  2000562194735915,2000939385705498,2000299782803840,1999334119578807,1999089848705513,
  1999844430626148,2000782477011687,2000860963052393,1999971529984919,1999101511464599,
  1999242196340025,2000246276387350,2000973466708502,2000593156317338,1999539842571325,
  1999012608033263,1999606583620619,2000645473340109,2000952969645383,2000177956685759,
  1999193210686787,1999121175454703,2000059803663707,2000944861131319,2000748322030465,
  1999677412879995,1998967050064510,1999453690088653,2000582360206145,2001039700671715,
  2000289621429376,1999202239956798,1999037372865549,1999983219585272,2000948736928256]
private def pvm_2_8_p4 : List ℕ := [2000825840692034,1999754742865712,1998958122728152,
  1999349454244076,2000492396922739,2001086066595375,2000439889034303,1999275542042593,
  1998924761510317,1999806924640579,2000926738686103,2000998222680428,1999924745314041,
  1998924430433418,1999141158246017,2000335640239627,2001158227409897,2000680899017457,
  1999438254433409,1998816591579006,1999505596339140,2000744947857938,2001173364635573,
  2000319281391943,1999107061596176,1998851379468854,1999838903184511,2001017650809208,
  2001119759863708,2000018637617997,1998874742498913,1998909767407251,2000106427661913,
  2001214856274360,2001063919028645,1999794369269167,1998716877793802,1998950215010876,
  2000265926130027,2001328536707864,2001060896727187,1999726238422474,1998648688611034,
  1998890211582075,2000217212441096,2001349282576911,2001203209210398,1999914382265985]
private def pvm_2_8_p5 : List ℕ := [1998687717809544,1998662521078115,1999868935546021,
  2001217494396147,2001493582924921,2000439763041866,1998972120934032,1998369416268876,
  1999165061125918,2000697194896020,2001678598559951,2001279314351806,1999809305543573,
  1998454676193807,1998313170657541,1999524132119564,2001171247618447,2001995191512684,
  2001331153977473,1999561427562226,1997794256178936,1997077415767914,1997769754372200,
  1999528955235864,2001899993125262,2005069616892275,2010262049003828,2019505238202616,
  2034887965949166,2057700118042042,2087865129064765,2123873924166855,2163165082904878,
  2202717692100117,2239599452830813,2271313512036310,2295928471858967,2312076387493866,
  2318926273759728,2316198067394592,2304215362454647,2283946177920440,2256971369737898,
  2225347195785503,2191372369961440,2157307664264317,2125112371242254,2096253680703770]
private def pvm_2_8_p6 : List ℕ := [2071619641930206,2051536023043720,2035863000832149,
  2024135266341125,2015709236610161,2009890001557962,2006023253447695,2003549235216460,
  2002024017528458,2001117448318412,2000597603469666,2000309838867858,2000155937511049,
  2000076329024522,2000036439583715,2000017034464827,2000007839306874,2000003575383464,
  2000001628228308,2000000745664222,2000000345147519,2000000161719955,2000000076515262,
  2000000036351343,2000000017218222,2000000008073932,2000000003725586,2000000001683843,
  2000000000742955,2000000000319296,2000000000133456,2000000000054197,2000000000021367,
  2000000000008169,2000000000003021,2000000000001074,2000000000000363,2000000000000114,
  2000000000000031,2000000000000006,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_8_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_8_p8 : List ℕ := [2000000000000000]
private def pvm_2_8 : List ℕ := pCat pvm_2_8_p0 (pCat pvm_2_8_p1 (pCat pvm_2_8_p2 (pCat pvm_2_8_p3
  (pCat pvm_2_8_p4 (pCat pvm_2_8_p5 (pCat pvm_2_8_p6 (pCat pvm_2_8_p7 pvm_2_8_p8)))))))
private def pvm_2_9_p0 : List ℕ := [1999999956162789,1999999762810045,1999999137646749,
  1999997583324611,1999994511854388,1999989699273033,1999984001659500,1999979820705608,
  1999980483232875,1999988113034720,2000000972170526,2000012720675346,2000015695989146,
  2000007120870055,1999993154266997,1999985492480752,1999991315775923,2000005372278398,
  2000013638055545,2000007298471247,1999993087035929,1999987017400594,1999996268134388,
  2000009843302824,2000011018328941,1999998231601025,1999987932946528,1999993716599893,
  2000007870617322,2000011055682338,1999998808345726,1999988397444548,1999994757843718,
  2000008672989742,2000009653584426,1999996217227006,1999988626114356,1999998474631937,
  2000010587562579,2000006089070317,1999992043390298,1999990750999125,2000004292580572,
  2000010795858050,1999999661258259,1999989158511999,1999996661157723,2000009680726153]
private def pvm_2_9_p1 : List ℕ := [2000006379354920,1999992322019891,1999991393120843,
  2000005189452622,2000009988110852,1999997481148266,1999989414254157,1999999898905791,
  2000010517237678,2000002509979678,1999990077083429,1999995388653888,2000008943960356,
  2000006360032339,1999992291082502,1999992251225681,2000006326819809,2000008796038221,
  1999995115092233,1999990464013016,2000003449285476,2000010010793165,1999997932783317,
  1999989734871392,2000000770154336,2000010342483029,2000000423085021,1999989717084130,
  1999998496650731,2000010121866425,2000002468557277,1999990110295974,1999996678451005,
  2000009611763356,2000004068374462,1999990691325860,1999995283022335,2000008996864348,
  2000005276273030,1999991310998051,1999994244670605,2000008394117210,2000006159017570,
  1999991863219671,1999993440562665,2000007716014490,2000006356617902,1999991200535651]
private def pvm_2_9_p2 : List ℕ := [1999990169936789,2000001047935174,1999993290742332,
  1999963989870838,1999936582797332,1999903443094780,1999825308453699,1999689620240577,
  1999514819363768,1999297556456402,1999017118657294,1998700551072773,1998429848160904,
  1998280723400383,1998305296504389,1998564535995691,1999098122689331,1999836710399851,
  2000591931185321,2001146638517168,2001329076973171,2001044993501421,2000347021392084,
  1999500588625312,1998898436854267,1998836796297185,1999346594879480,2000183293511642,
  2000922178436411,2001136667753913,2000660755803380,1999768894192129,1999041558664577,
  1998962908892176,1999581389059826,2000480178158627,2001038537162520,2000836470259040,
  1999992460582078,1999148603005817,1998991071501536,1999657462496498,2000594227003706,
  2001021466224403,2000584891078366,1999649447339098,1999015869569294,1999257742593300]
private def pvm_2_9_p3 : List ℕ := [2000184030525775,2000947200091217,2000814207273653,
  1999901633442883,1999092742836423,1999173197863136,2000057899617768,2000877946660937,
  2000824603024518,1999941189373120,1999108977011245,1999191134558223,2000126618432473,
  2000937185702384,2000744959077394,1999746775592421,1999027702626815,1999372522056991,
  2000398804651957,2000980141123618,2000480603613409,1999449278108239,1999028093804564,
  1999698794792192,2000721170765173,2000928766046492,2000061789601885,1999112204491618,
  1999196764241205,2000228129588429,2000991240357739,2000581276058537,1999485840272780,
  1999004340575260,1999704142555464,2000753240921570,2000906372230941,1999976781974900,
  1999067625955995,1999274771948287,2000366266836125,2001026678571222,2000436207719181,
  1999299319638004,1999014719531645,1999948004251003,2000952581744384,2000780599099864]
private def pvm_2_9_p4 : List ℕ := [1999641023333683,1998945449135858,1999554097314783,
  2000712700769842,2000991423264445,2000047506507824,1999042038365068,1999214026201904,
  2000359668273709,2001072242279117,2000462579684764,1999267798521611,1998966698057025,
  1999951493421517,2001013388312164,2000823991833295,1999600897946470,1998860954484530,
  1999534625420027,2000794140188593,2001076231302705,2000026697414043,1998939330432973,
  1999153187901309,2000406574790691,2001167719045454,2000509057491721,1999227848825173,
  1998873304887551,1999878313241543,2001041379509903,2000964849900503,1999726549831392,
  1998796139291451,1999292326503154,2000644653167694,2001253598464668,2000381531517839,
  1999039414804772,1998808618127378,1999978118215579,2001193476183604,2001034351530796,
  1999671001272654,1998668914860891,1999182477772747,2000634717493351,2001383709982993]
private def pvm_2_9_p5 : List ℕ := [2000583649824086,1999123541395170,1998620443727223,
  1999630242178098,2001054873155357,2001352949320470,2000199763528726,1998817302040632,
  1998666163363899,1999914093823146,2001274316642102,2001343194121865,2000035403467211,
  1998662456410802,1998606769481773,1999942811945615,2001368911186622,2001488333919495,
  2000165315943799,1998648890980109,1998376697746360,1999622213182664,2001251663140326,
  2001778951535692,2000713197016618,1998979387297797,1998081922721563,1998799979519367,
  2000554675263109,2001936627811000,2001876397671433,2000455256549261,1998733502334608,
  1997817861015051,1997978647628467,1998534587205914,1998597901142446,1998135678112703,
  1998606220391607,2002744643034178,2013617946819227,2033466933092480,2062890490816405,
  2100659552739118,2144093910689525,2189709749393944,2233833966521472,2273024715807791]
private def pvm_2_9_p6 : List ℕ := [2304308298360450,2325335644641917,2334547868236004,
  2331360833992145,2316301898549257,2291007990146874,2258031549827820,2220472212343572,
  2181517164385898,2144002056379085,2110089754367610,2081119065563128,2057622324582139,
  2039469421433188,2026076787931430,2016622615346855,2010226604620778,2006074261186379,
  2003484508520533,2001931319194131,2001034774564285,2000536275855702,2000269053726947,
  2000130821810532,2000061740227362,2000028339585892,2000012686503133,2000005558316098,
  2000002393729650,2000001018312476,2000000430093785,2000000181153751,2000000076312269,
  2000000032173664,2000000013552772,2000000005683310,2000000002361404,2000000000967356,
  2000000000388929,2000000000152880,2000000000058567,2000000000021808,2000000000007872,
  2000000000002744,2000000000000916,2000000000000289,2000000000000083,2000000000000020]
private def pvm_2_9_p7 : List ℕ := [2000000000000002,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_9_p8 : List ℕ := [2000000000000000]
private def pvm_2_9 : List ℕ := pCat pvm_2_9_p0 (pCat pvm_2_9_p1 (pCat pvm_2_9_p2 (pCat pvm_2_9_p3
  (pCat pvm_2_9_p4 (pCat pvm_2_9_p5 (pCat pvm_2_9_p6 (pCat pvm_2_9_p7 pvm_2_9_p8)))))))
private def pvm_2_10_p0 : List ℕ := [1999999999995723,1999999999960802,1999999999752845,
  1999999998763274,1999999994798206,1999999981037848,1999999938975654,1999999824558334,
  1999999545972677,1999998937446332,1999997746386689,1999995668729986,1999992476497022,
  1999988257519741,1999983707094065,1999980286137720,1999979970460141,1999984401716955,
  1999993615517305,2000005062420964,2000013945794074,2000015447575806,2000008061847869,
  1999995762811018,1999986578349321,1999987331483018,1999997874542122,2000009979364589,
  2000013323426212,2000004653811144,1999991757826204,1999987045104107,1999995416702005,
  2000008437014871,2000012277123208,2000002578872736,1999990082790350,1999989183028963,
  2000001079574913,2000011551359428,2000007684320586,1999994200217826,1999988257919291,
  1999997649426701,2000010071402292,2000008859801102,1999995575053856,1999988511112343]
private def pvm_2_10_p1 : List ℕ := [1999997606403205,2000010037603783,2000007950822188,
  1999994307772941,1999989128242099,2000000157423881,2000010885825617,2000005018458911,
  1999991485001047,1999991205361922,2000004667365988,2000010709229457,1999999703180626,
  1999989221211985,1999996189603866,2000009329709757,2000007126748151,1999993167704307,
  1999990614020766,2000003773043320,2000010535936664,1999999425403098,1999989327008446,
  1999997557843908,2000009978308181,2000005065381549,1999991333735477,1999992819009562,
  2000006948216185,2000008752496387,1999994989393428,1999990201204760,2000003004500237,
  2000010373854755,1999998956841174,1999989449805273,1999999204616145,2000010406640258,
  2000002463126330,1999989979970731,1999996064047297,2000009460181507,2000005207586660,
  1999991212661567,1999993715774225,2000008051336284,2000007180106028,1999992708099927]
private def pvm_2_10_p2 : List ℕ := [1999992085962195,2000006539587340,2000008506835251,
  1999994182954578,1999991020493294,2000005140354563,2000009352055305,1999995479683748,
  1999990357261829,2000003963641325,2000009867727349,1999996526033853,1999989958566163,
  2000003050799336,2000010171764569,1999997302437757,1999989741043494,2000002479142334,
  2000010538298194,1999998166148958,1999989971371299,2000001578252464,2000006301334197,
  1999982796763314,1999947050469110,1999901975509680,1999802943401361,1999610051998588,
  1999331230125112,1998986492901463,1998589024745095,1998206025522429,1997988000169227,
  1998085838125451,1998557515382657,1999353199552136,2000311370440134,2001135645198022,
  2001474357410949,2001139884703826,2000276614256447,1999310263111812,1998739113605504,
  1998893768865414,1999722808421769,2000728088334472,2001227594236862,2000856022797769]
private def pvm_2_10_p3 : List ℕ := [1999880180684424,1999019044497811,1998914080308651,
  1999653661643494,2000671786750098,2001134307544799,2000621638433527,1999560123231077,
  1998903455099306,1999257516902248,2000290200466089,2001033103753433,2000788429889690,
  1999787006907641,1998994035025317,1999204499160390,2000231129526968,2001025475781264,
  2000738617741162,1999661407005281,1998955765768893,1999391208026059,2000486020977570,
  2001033751217165,2000432675155936,1999351481505121,1999001827739257,1999791084902713,
  2000829724269808,2000907595959814,1999910511775313,1999011142341572,1999298083945297,
  2000436297655185,2001041894509904,2000373300822089,1999252590828404,1999056549285173,
  2000022181678940,2000956506829455,2000702951703811,1999570791319715,1998970611528806,
  1999668338296828,2000797812329908,2000917397935845,1999852846001185,1998966637984012]
private def pvm_2_10_p4 : List ℕ := [1999419128847896,2000634641547275,2001024417416628,
  2000071388523347,1999024723433251,1999259875909898,2000466088405084,2001057433187289,
  2000258343477875,1999119117706604,1999138064597735,2000295851379204,2001070743780927,
  2000430670383946,1999208385927583,1999027633843381,2000148446951645,2001086848620240,
  2000575084354373,1999280342983691,1998940553098954,2000027142901900,2001087233890555,
  2000690008518318,1999361867611022,1998884976318555,1999901280567912,2001052529727927,
  2000801733218275,1999482044196502,1998846210261723,1999739085136378,2000983595295583,
  2000935662801634,1999649329879154,1998811377518803,1999532370561236,2000881672218750,
  2001089988247729,1999865252332001,1998795851750352,1999289899716331,2000724742213092,
  2001236239474961,2000142191575808,1998845171016541,1999026398430111,2000468344516699]
private def pvm_2_10_p5 : List ℕ := [2001326704387600,2000496298452781,1999024050466968,
  1998773760736637,2000067201113147,2001288581148221,2000914993841806,1999404061700726,
  1998612557900345,1999511608026150,2001014894959720,2001308817188712,2000033395343576,
  1998699682730790,1998888680205405,2000391962791650,2001463490081343,2000851822247763,
  1999242080839760,1998467735708683,1999423159371858,2001053856300365,2001540340012503,
  2000323457079498,1998719682870146,1998476657344427,1999877478601520,2001443805859137,
  2001517054273343,2000001710258581,1998448481086659,1998444772283390,2000009366337058,
  2001601540376273,2001665609515855,2000133091835825,1998444102477921,1998152666689668,
  1999500164988848,2001264950052946,2001933752960013,2001052729564353,1999547050329028,
  1998787579768865,1999275539709341,2000094808701980,1999614227395196,1996939224868918]
private def pvm_2_10_p6 : List ℕ := [1993088287543389,1991116395543949,1995133919038086,
  2008812221098905,2034137645177856,2070879453828111,2116772730392959,2168105060484486,
  2220368414535082,2268809472645361,2308898357333921,2336802350972492,2349885380554432,
  2347140100520926,2329397616980568,2299197661180904,2260315397918587,2217063920722483,
  2173561858504866,2133147909763440,2098054128590375,2069356651568802,2047145270333829,
  2030814000372952,2019375092481921,2011725866189930,2006833879308290,2003837311845855,
  2002077054163377,2001084351946742,2000546343900880,2000265861858947,2000125064241275,
  2000056936635555,2000025122418328,2000010763230623,2000004487855461,2000001826300919,
  2000000727723981,2000000284954614,2000000110038328,2000000042034506,2000000015917045,
  2000000005978657,2000000002225588,2000000000819223,2000000000297213,2000000000105879]
private def pvm_2_10_p7 : List ℕ := [2000000000036890,2000000000012521,2000000000004120,
  2000000000001305,2000000000000394,2000000000000108,2000000000000024,2000000000000004,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_10_p8 : List ℕ := [2000000000000000]
private def pvm_2_10 : List ℕ := pCat pvm_2_10_p0 (pCat pvm_2_10_p1 (pCat pvm_2_10_p2 (pCat
  pvm_2_10_p3 (pCat pvm_2_10_p4 (pCat pvm_2_10_p5 (pCat pvm_2_10_p6 (pCat pvm_2_10_p7
  pvm_2_10_p8)))))))
private def pvm_2_11_p0 : List ℕ := [1999999999999995,2000000000000001,2000000000000003,
  1999999999999993,1999999999999981,1999999999999933,1999999999999651,1999999999998285,
  1999999999992244,1999999999967674,1999999999875430,1999999999554540,1999999998517144,
  1999999995393718,1999999986623087,1999999963636931,1999999907407418,1999999779103851,
  1999999506432364,1999998968086602,1999997984574806,1999996331999219,1999993802080726,
  1999990327759899,1999986167057075,1999982082513175,1999979384662940,1999979674239986,
  1999984191228890,1999992905482016,2000003804488705,2000013036170332,2000016354112252,
  2000011550925807,2000000555499286,1999989400251240,1999985143443119,1999991031737098,
  2000003301387985,2000012897206514,2000012061637929,2000001147355826,1999989362680566,
  1999987360020353,1999997262766828,2000009719915870,2000012294223982,2000002137387443]
private def pvm_2_11_p1 : List ℕ := [1999989808926569,1999988711817762,2000000243564991,
  2000011394427293,2000009119673852,1999995968608065,1999987836461695,1999994876364022,
  2000008343962686,2000010975892226,1999999229354429,1999988586970885,1999993415316953,
  2000007228132807,2000010921473673,1999999227006952,1999988701117524,1999994535582453,
  2000008317247735,2000009744671047,1999996614068314,1999988656229498,1999998031365782,
  2000010396486191,2000006545220159,1999992439187891,1999990359429391,2000003683693966,
  2000011027309622,2000000442006571,1999989168563555,1999995790350784,2000009384575734,
  2000007239277744,1999992904317689,1999990641191549,2000004360461482,2000010556275059,
  1999998490515872,1999989074919264,1999998787378699,2000010615099317,2000003647014235,
  1999990204773973,1999994291263381,2000008628257233,2000007369986119,1999992743538747]
private def pvm_2_11_p2 : List ℕ := [1999991356948265,2000005795241724,2000009565362266,
  1999995667737441,1999989812347480,2000002929822407,2000010565350947,1999998371170277,
  1999989247186525,2000000453265954,2000010799834089,2000000585536243,1999989250158369,
  1999998514846913,2000010639258810,2000002249005228,1999989502397777,1999997116024510,
  2000010348007501,2000003398643770,1999989792041260,1999996197955704,2000010090074578,
  2000004102839212,1999989997129253,1999995691185594,2000009951495151,2000004426758653,
  1999990061793070,1999995537195839,2000009960908468,2000004418353901,1999989983556922,
  1999995722416139,2000010158179939,2000004132413743,1999989628048805,1999995610096990,
  2000009275768515,2000002403612394,1999990650698686,2000005343682479,2000032947580220,
  2000040326773579,2000024443069484,1999972025557571,1999805084919242,1999438771890912]
private def pvm_2_11_p3 : List ℕ := [1998880535040603,1998241766719633,1997707386297454,
  1997532464919112,1997962588555892,1999017058644140,2000339784775255,2001335358259664,
  2001509122369409,2000773085388145,1999568254249180,1998695048586137,1998803033552117,
  1999831111057923,2000958979992723,2001254898242893,2000479596677854,1999310915135081,
  1998782495551415,1999384747590147,2000571447618301,2001193621414285,2000608904935124,
  1999401391985152,1998836523984191,1999515640216829,2000700753431967,2001102974157061,
  2000287981896899,1999161305765676,1998988658379269,1999979350252096,2000998778322324,
  2000837022270812,1999664957680132,1998897917304931,1999488761538649,2000711662025883,
  2001036645134886,2000057364688911,1999016493427281,1999233233206614,2000426151534792,
  2001065891752240,2000324866291077,1999157162233199,1999093126963229,2000235259325860]
private def pvm_2_11_p4 : List ℕ := [2001073410094219,2000468279563499,1999219884233811,
  1999030451061807,2000173348011783,2001079584369251,2000492249313414,1999224112774990,
  1999037935122484,2000190273052039,2001072701007678,2000454975982030,1999201338367851,
  1999067757482905,2000247270242542,2001084388207056,2000388212270361,1999130562974080,
  1999103077422646,2000365219109036,2001117268843405,2000262316897749,1999016605430835,
  1999185864361976,2000540338905210,2001119024037486,2000073549077107,1998916691616264,
  1999330123712517,2000716675130175,2001066179502741,1999871750663259,1998860784386972,
  1999494764028960,2000861396862970,2000990445198263,1999689409267868,1998825899608297,
  1999650107627420,2000990048691373,2000916794863748,1999516733555203,1998793329215192,
  1999802477187630,2001113956042639,2000839197691248,1999349820308789,1998772766141072]
private def pvm_2_11_p5 : List ℕ := [1999950314018120,2001215960015759,2000760112441017,
  1999215207326818,1998767532044904,2000059628595166,2001280220386360,2000714212467082,
  1999144679054048,1998752655921434,2000085923008895,2001312047003661,2000747693227953,
  1999156192996957,1998695876285338,1999995646435637,2001317384418441,2000890873229231,
  1999269488613422,1998591895660705,1999762544771097,2001266791799550,2001144616406912,
  1999532172721331,1998490000838747,1999364494866937,2001069712001257,2001457736629694,
  2000019747859486,1998523852163088,1998823193886473,2000575968690512,2001666684310053,
  2000769751241157,1998932865512831,1998318913934731,1999659541754153,2001421953596125,
  2001594602153155,1999971100607894,1998349090910046,1998509125558249,2000281178696808,
  2001778071448524,2001436294084757,1999628447911609,1998207726972411,1998572413738561]
private def pvm_2_11_p6 : List ℕ := [2000286802900257,2001597375517884,2001234106093971,
  1999683356768723,1998718776934302,1999648036035972,2001874414066688,2003054741910287,
  2000792080932507,1994636367513070,1987041169947641,1982752569499919,1987119744674638,
  2004295302789763,2036073273730841,2081552951345256,2137392829051677,2198349625065422,
  2257969549119789,2309456636095024,2346725823157131,2365490506431387,2364091383805231,
  2343778669037127,2308329000615710,2263116969053720,2213942142974648,2165956875880592,
  2122950442666481,2087084831427376,2059025174545558,2038316534192924,2023841388936485,
  2014229492716851,2008151809650822,2004485416437412,2002371933290677,2001206194110639,
  2000590225433572,2000278095726700,2000126261017546,2000055286125938,2000023371066685,
  2000009549744495,2000003777493587,2000001449075350,2000000540210317,2000000196175854]
private def pvm_2_11_p7 : List ℕ := [2000000069572129,2000000024155476,2000000008228882,
  2000000002754885,2000000000907015,2000000000293580,2000000000093286,2000000000029026,
  2000000000008811,2000000000002594,2000000000000732,2000000000000192,2000000000000045,
  2000000000000007,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_11_p8 : List ℕ := [2000000000000000]
private def pvm_2_11 : List ℕ := pCat pvm_2_11_p0 (pCat pvm_2_11_p1 (pCat pvm_2_11_p2 (pCat
  pvm_2_11_p3 (pCat pvm_2_11_p4 (pCat pvm_2_11_p5 (pCat pvm_2_11_p6 (pCat pvm_2_11_p7
  pvm_2_11_p8)))))))
private def pvm_2_12_p0 : List ℕ := [1999999999999995,1999999999999995,1999999999999997,
  2000000000000004,2000000000000003,2000000000000004,1999999999999999,1999999999999994,
  1999999999999992,1999999999999995,1999999999999989,1999999999999994,1999999999999993,
  1999999999999990,1999999999999985,1999999999999983,1999999999999975,1999999999999933,
  1999999999999744,1999999999998884,1999999999995452,1999999999982426,1999999999935979,
  1999999999779991,1999999999286627,1999999997815937,1999999993683392,1999999982739242,
  1999999955438447,1999999891352025,1999999750001731,1999999457705784,1999998892748152,
  1999997876482151,1999996185583698,1999993607181683,1999990056136826,1999985751323577,
  1999981398407494,1999978260697277,1999977957692415,1999981879526063,1999990298573441,
  2000001566650359,2000012032624843,2000017217524298,2000014144631978,2000003716333947]
private def pvm_2_12_p1 : List ℕ := [1999991341384217,1999984519521576,1999988056543219,
  1999999958497507,2000011716040946,2000014099415217,2000004829071940,1999991522294109,
  1999985991158096,1999993581211122,2000007276613025,2000013553914542,2000005811969451,
  1999991994924258,1999987040604774,1999996622144379,2000009979985092,2000011509950550,
  1999999228476049,1999987999623765,1999991853746025,2000006045846013,2000012287743188,
  2000002273638900,1999989284674193,1999990990523885,2000005150319265,2000011983983350,
  2000001709306416,1999989031822113,1999992467831011,2000007035523560,2000010978989515,
  1999998257440004,1999988273505039,1999996511650116,2000010172421813,2000007679737767,
  1999992932100721,1999989643163282,2000003218680556,2000011457477161,2000000697491037,
  1999988812095142,1999995792817311,2000009884803479,2000007043959932,1999992088594559]
private def pvm_2_12_p2 : List ℕ := [1999990888408112,2000005593297910,2000010433699961,
  1999996812150956,1999988894350033,2000000877190728,2000011256126867,2000001224926835,
  1999988979717813,1999996940130312,2000010523323599,2000004609356140,1999990127809834,
  1999994118044941,2000009152798766,2000006902070134,1999991569291537,1999992298322804,
  2000007753582861,2000008314567346,1999992845651223,1999991227366360,2000006654372617,
  2000009103700075,1999993733714476,1999990669555948,2000005996295194,2000009470051397,
  1999994154049025,1999990465663183,2000005813399156,2000009530144273,1999994105799088,
  1999990540091087,2000006081796864,2000009322310565,1999993632299072,1999990887023249,
  2000006741503013,2000008825188451,1999992809168731,1999991549375104,2000007701607555,
  2000007981003228,1999991742251725,1999992587762487,2000008832156813,2000006737412129]
private def pvm_2_12_p3 : List ℕ := [1999990631655839,1999994131927474,2000009905732689,
  2000004629847089,1999988908936969,1999995951197344,2000012835992546,2000007710687328,
  1999994112782375,1999995201892863,1999986344996151,1999949846778128,1999942966620047,
  2000037667921880,2000224760767293,2000408046016623,2000419984739312,2000029528750677,
  1999094496869298,1997837540078647,1996896928680904,1996947217080747,1998162439895921,
  1999960938407661,2001265275712958,2001230633807574,2000005714107126,1998767761663312,
  1998722867167947,1999913904152321,2001130229810941,2001129930072929,1999936996850164,
  1998843141547816,1999052647851125,2000338365907649,2001219574857719,2000640956630767,
  1999288081421802,1998827259577431,1999837529375624,2001036210243218,2000893025377305,
  1999604880564486,1998850808278829,1999611890342804,2000879281079131,2000963017608461]
private def pvm_2_12_p4 : List ℕ := [1999741849660042,1998871549851065,1999562367597601,
  2000870454908306,2000953646440880,1999677153777197,1998862398119295,1999690600766026,
  2000964430268787,2000827427348651,1999483057556855,1998906355473438,1999941592104977,
  2001056530386364,2000601402518509,1999252164568880,1999020374133075,2000260715753950,
  2001114443433315,2000281117708692,1999010084039597,1999245547782013,2000647138410085,
  2001061682493503,1999831464688704,1998853289842598,1999657142961822,2001000839632439,
  2000784610058600,1999340334925893,1998926838185476,2000193022754578,2001156865506045,
  2000309433854309,1998977278059940,1999245567528073,2000696650881503,2001060683971171,
  1999762100653992,1998828090778155,1999728725953850,2001065778837852,2000739124393400,
  1999242246799369,1998920604704102,2000299329525010,2001225842449633,2000229251807137]
private def pvm_2_12_p5 : List ℕ := [1998855632210754,1999268793621516,2000840912345560,
  2001109051450330,1999636490330142,1998717804797380,1999797380147358,2001203758798433,
  2000747293440266,1999126345108623,1998845804870554,2000344780472318,2001324235004827,
  2000280482986533,1998800158569336,1999134777825200,2000785170889039,2001264241775192,
  1999843665872090,1998641329456540,1999455956377600,2001092614653288,2001131667743113,
  1999497693757433,1998575557079352,1999726275125177,2001298733315024,2001013934189711,
  1999256019655101,1998532518543065,1999895366753782,2001436581525272,2000977340257561,
  1999133204190859,1998460713784649,1999909955266445,2001513772028999,2001081946028028,
  1999174667701133,1998338381107242,1999698604736965,2001482534054323,2001363628141655,
  1999480085364443,1998227701013226,1999193493271810,2001181979765961,2001743806683510]
private def pvm_2_12_p6 : List ℕ := [2000192283588123,1998391990041958,1998477203826791,
  2000337293643556,2001809121951436,2001218920204211,1999268102748685,1998178673054789,
  1999171136276549,2001106875452035,2001731660710220,2000149628238858,1997938014952384,
  1997751142162644,2000712492855813,2004968535232336,2006679796088696,2002689675016948,
  1992946954066636,1981195749953001,1973791703573726,1977556750318266,1997729820467840,
  2036572068803675,2092684968214310,2160966768680701,2233249871949230,2299693813257697,
  2350785834648176,2379457841978891,2382645083835707,2361759462559123,2321964697235001,
  2270590943643978,2215286713889710,2162486526495729,2116540071958458,2079551415114051,
  2051749697925481,2032118693199792,2019038925795817,2010788394397183,2005848647887131,
  2003035708154745,2001509617853045,2000719707966118,2000329154528151,2000144501229480]
private def pvm_2_12_p7 : List ℕ := [2000060933811974,2000024698597359,2000009630828543,
  2000003616049576,2000001308731171,2000000457141800,2000000154329993,2000000050434739,
  2000000015981310,2000000004918337,2000000001472312,2000000000429197,2000000000121909,
  2000000000033726,2000000000009072,2000000000002360,2000000000000585,2000000000000133,
  2000000000000025,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_12_p8 : List ℕ := [2000000000000000]
private def pvm_2_12 : List ℕ := pCat pvm_2_12_p0 (pCat pvm_2_12_p1 (pCat pvm_2_12_p2 (pCat
  pvm_2_12_p3 (pCat pvm_2_12_p4 (pCat pvm_2_12_p5 (pCat pvm_2_12_p6 (pCat pvm_2_12_p7
  pvm_2_12_p8)))))))
private def pvm_2_13_p0 : List ℕ := [1999999999999995,1999999999999995,1999999999999994,
  1999999999999995,1999999999999995,2000000000000004,2000000000000000,2000000000000005,
  2000000000000007,2000000000000004,2000000000000003,1999999999999994,2000000000000001,
  1999999999999989,1999999999999992,1999999999999990,1999999999999996,1999999999999994,
  1999999999999992,1999999999999994,1999999999999999,1999999999999992,1999999999999977,
  1999999999999991,1999999999999982,1999999999999985,1999999999999992,1999999999999995,
  1999999999999989,1999999999999974,1999999999999981,1999999999999983,1999999999999983,
  2000000000000002,2000000000000071,2000000000000350,2000000000001210,2000000000002588,
  1999999999999073,1999999999955506,1999999999712919,1999999998680564,1999999994955218,
  1999999983094750,1999999949136865,1999999860810771,1999999651001756,1999999194963357]
private def pvm_2_13_p1 : List ℕ := [1999998288601561,1999996647320782,1999993958795763,
  1999990026572891,1999985014435837,1999979727006560,1999975751544756,1999975206408431,
  1999979911819650,1999990115524259,2000003406924761,2000014810282354,2000018767793341,
  2000012553996772,1999999101647854,1999986585303024,1999983682325744,1999992941967448,
  2000007549690729,2000015574873911,2000009839582177,1999995223295446,1999985423073812,
  1999990226648509,2000004981941290,2000014217437999,2000007747125038,1999992636199813,
  1999986267297973,1999996313255487,2000010724113856,2000011586258061,1999997670758021,
  1999986942567868,1999993659866153,2000008881457409,2000011724189489,1999998121197360,
  1999987317701668,1999994945236183,2000009925612217,2000010008152244,1999994986228704,
  1999987744674276,1999999534422028,2000011971642876,2000005338349845,1999990185238405]
private def pvm_2_13_p2 : List ℕ := [1999991040396074,2000006571223031,2000011136954126,
  1999997063421245,1999988018251152,1999999419071221,2000011762992860,2000003672364753,
  1999989202742026,1999993804281592,2000009380682316,2000008128324942,1999992244080689,
  1999990478919454,2000006102974955,2000010461994701,1999995456224052,1999988949254355,
  2000003152972033,2000011382937087,1999998029764380,1999988458309594,2000001011502170,
  2000011594183755,1999999721937272,1999988408821110,1999999763284265,2000011568119327,
  2000000542831993,1999988453123179,1999999349122820,2000011537608650,2000000570649403,
  1999988459537302,1999999689193055,2000011547048045,1999999879276318,1999988458299911,
  2000000715806474,2000011502631168,1999998535200641,1999988596914133,2000002355054066,
  2000011212624094,1999996630643783,1999989101359202,2000004484454299,2000010428202432]
private def pvm_2_13_p3 : List ℕ := [1999994330154858,1999990229745638,2000006886994153,
  2000008898268082,1999991910946402,1999992206611340,2000009220555722,2000006447194369,
  1999989784015641,1999995141286360,2000011002548244,2000003016591383,1999988456722547,
  1999999095048474,2000011970987188,1999998766946360,1999987480518779,2000002177192085,
  2000011889391095,1999999320021491,1999995955572328,2000004717510355,1999987115497266,
  1999959407787622,1999992880394413,2000089729551441,2000148319098601,2000059597725174,
  1999796475225052,1999493946057986,1999499322743115,2000141410052287,2001223643980602,
  2001857598013142,2001119676850199,1999043201712565,1996900791529768,1996291753003906,
  1997672639487697,1999731345498938,2000541031779066,1999593888270670,1998406404689760,
  1998711259764304,2000294123673702,2001253966421152,2000455370784830,1999025566009401]
private def pvm_2_13_p4 : List ℕ := [1998898889622974,2000251363681017,2001231182228978,
  2000471907418480,1999042829001819,1999001712220748,2000420445515483,2001209641200035,
  2000188669745700,1998893759451011,1999287195915856,2000760441453024,2001050526672064,
  1999720593838754,1998838519457259,1999772497894681,2001056050650959,2000669595941489,
  1999220890806049,1999014995680598,2000393324814331,2001142510401812,2000034769760086,
  1998861907859397,1999555256623629,2000988777678116,2000788283922040,1999274267935035,
  1998968078696310,2000387781232188,2001157328146659,1999984001604947,1998839957464375,
  1999649566636801,2001047309805199,2000677123869488,1999164443922277,1999063681090129,
  2000547831253091,2001107907090465,1999788585205336,1998820190258397,1999855669978853,
  2001147939614998,2000489840715445,1998984132460452,1999202989967575,2000794286448696]
private def pvm_2_13_p5 : List ℕ := [2001040661278803,1999499685103894,1998800102665131,
  2000156640385064,2001259362887463,2000209531593940,1998789566392610,1999432217812068,
  2001052308831501,2000886110354280,1999207063183496,1998867038733449,2000449645516475,
  2001279699095580,1999950709188429,1998696480695745,1999627675544198,2001190707433279,
  2000772050518835,1999059979220381,1998897692642363,2000565795234227,2001315559078549,
  1999899828475112,1998629569603613,1999593621611047,2001239254256191,2000887206538706,
  1999083623714973,1998734673687275,2000425911506101,2001463676547154,2000173084470236,
  1998580129051667,1999213264592459,2001104238425935,2001294751537888,1999461892797070,
  1998430434513190,1999807041837303,2001506680534355,2000938271937043,1998937099769236,
  1998498584585590,2000293479802134,2001685357879523,2000627105304506,1998638537033256]
private def pvm_2_13_p6 : List ℕ := [1998579583841685,2000547505476722,2001772715374076,
  2000537300071139,1998540364177460,1998512879185984,2000496796989909,2001839355646877,
  2000763154332491,1998679005763804,1998291496815578,2000100131599376,2001797707601126,
  2001213407665669,1999037674626475,1997998895157641,1999547901918516,2002003016300137,
  2002314320949935,1999504391754053,1996078127803170,1995893759336034,2000510761298236,
  2007320452172103,2010978272103864,2006907691993693,1994400950873527,1977649158464410,
  1964617772205897,1964634684023143,1985583116260859,2031308190140155,2099800553149889,
  2182820700112267,2267427761385512,2339198012574631,2386102142105162,2401616045664310,
  2385960591472986,2345210309056546,2288883460137611,2227087764481585,2168213907485704,
  2117715039870220,2077985909018706,2048998025894973,2029239237704571,2016593203702061]
private def pvm_2_13_p7 : List ℕ := [2008964887492850,2004615502442658,2002266253893239,
  2001062003754831,2000475279921647,2000203250153358,2000083100723886,2000032500994929,
  2000012165539562,2000004360559145,2000001497542341,2000000493079289,2000000155761535,
  2000000047244098,2000000013770409,2000000003860510,2000000001041888,2000000000270899,
  2000000000067888,2000000000016392,2000000000003801,2000000000000839,2000000000000171,
  2000000000000028,2000000000000002,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_13_p8 : List ℕ := [2000000000000000]
private def pvm_2_13 : List ℕ := pCat pvm_2_13_p0 (pCat pvm_2_13_p1 (pCat pvm_2_13_p2 (pCat
  pvm_2_13_p3 (pCat pvm_2_13_p4 (pCat pvm_2_13_p5 (pCat pvm_2_13_p6 (pCat pvm_2_13_p7
  pvm_2_13_p8)))))))
private def pvm_2_14_p0 : List ℕ := [1999999999999995,1999999999999995,1999999999999994,
  1999999999999995,1999999999999991,1999999999999991,2000000000000000,1999999999999992,
  2000000000000004,2000000000000002,1999999999999999,2000000000000002,2000000000000006,
  2000000000000010,2000000000000001,2000000000000008,1999999999999998,2000000000000001,
  2000000000000011,1999999999999994,1999999999999986,1999999999999994,2000000000000000,
  1999999999999998,1999999999999985,1999999999999985,2000000000000001,1999999999999996,
  1999999999999990,1999999999999998,2000000000000003,1999999999999996,1999999999999981,
  1999999999999985,1999999999999981,1999999999999981,2000000000000001,1999999999999997,
  1999999999999989,1999999999999987,1999999999999981,1999999999999987,1999999999999982,
  1999999999999977,1999999999999979,1999999999999994,1999999999999995,1999999999999980]
private def pvm_2_14_p1 : List ℕ := [1999999999999971,1999999999999937,2000000000000041,
  2000000000000681,2000000000002526,2000000000004580,1999999999996868,1999999999946247,
  1999999999795265,1999999999560678,1999999999728110,2000000002136341,2000000010916688,
  2000000030873555,2000000056317836,2000000038537678,1999999821899449,1999999059621562,
  1999997169396839,1999993449374282,1999987482535682,1999979817251242,1999972588926255,
  1999969406294409,1999973868992268,1999986895002592,2000004435648254,2000018024076090,
  2000019439551592,2000007327280428,1999990308320446,1999981970382474,1999989670295238,
  2000006610272083,2000016544467337,2000009318347713,1999992403899800,1999984335556631,
  1999994393324107,2000010842281238,2000013714281630,1999999335002584,1999986093130185,
  1999991441004339,2000008250266739,2000013398071032,1999999595330705,1999986579331177]
private def pvm_2_14_p2 : List ℕ := [1999993377727586,2000009941313007,2000011248041021,
  1999995246067616,1999986850081093,1999999367432339,2000012767312472,2000005267151559,
  1999989164926391,1999991272565331,2000008078531081,2000010967802773,1999994931733403,
  1999987844118180,2000002184698342,2000012545873258,2000000359250455,1999987601404517,
  1999997525767237,2000011940383248,2000004150042351,1999988651770757,1999994580373391,
  2000010749869819,2000006333619249,1999989769262044,1999993055792554,2000009842833559,
  2000007296088845,1999990387095827,1999992577684084,2000009548845728,2000007343295930,
  1999990355895670,1999992932242026,2000009880308419,2000006594958850,1999989771437393,
  1999994082271729,2000010649909070,2000005026152289,1999988904520625,1999996088221214,
  2000011506850229,2000002572222989,1999988182911989,1999998984023725,2000011952912581]
private def pvm_2_14_p3 : List ℕ := [1999999267099734,1999988161684228,2000002630658918,
  2000011399820117,1999995389077533,1999989426649631,2000006583606448,2000009312416268,
  1999991563582652,1999992403002271,2000010039541848,2000005442243785,1999988746140251,
  1999997094075875,2000011942323157,2000000093371120,1999988017350445,2000002842789584,
  2000011277709143,1999994283118629,1999990235256167,2000008358591609,2000007458204502,
  1999989299287810,1999995357863606,2000012744477862,2000002312450101,1999986215265588,
  1999997785642884,2000010191879773,2000003598123992,2000005605454853,2000006704776306,
  1999967404456071,1999940426525326,2000022567185024,2000155575301597,2000133951859210,
  1999867233804194,1999573652966030,1999672165189635,2000346260385187,2001068369518559,
  2000824454680915,1999314259876994,1997836504488933,1998248711935396,2000708207905819]
private def pvm_2_14_p4 : List ℕ := [2003001127942100,2002764828367809,2000239715962855,
  1998091680850062,1998211642023115,1999436129370622,1999348007940502,1997838587352557,
  1997268657321176,1998804467902818,2000466860437381,2000088776289780,1998671759077092,
  1998778844785884,2000436157006602,2001105120485919,1999812132413995,1998757607129971,
  1999724088645412,2001119127364897,2000606154867862,1999054400713521,1999120379265317,
  2000705063253986,2001065271434506,1999561553777920,1998827595770932,2000164696673898,
  2001207654980264,2000099594551901,1998818217905631,1999656251397262,2001105927007556,
  2000561044818012,1999009076698883,1999252154759088,2000846607511098,2000902641419966,
  1999318457450339,1998974690651263,2000502942860729,2001116537550724,1999683262416968,
  1998822582080277,2000127714358552,2001209171542221,2000060291900437,1998787019092799]
private def pvm_2_14_p5 : List ℕ := [1999755811496238,2001189902386764,2000421407568009,
  1998859162113777,1999410308544797,2001066550499259,2000746887962536,1999032285025363,
  1999109239186254,2000844999216099,2001018820807229,1999300822488393,1998871816172637,
  2000531279441256,2001215463901777,1999657219829150,1998723287263383,2000135837759998,
  2001307421814630,2000086419322489,1998697390841534,1999680443161145,2001257019886875,
  2000557463689689,1998834523195775,1999208027513750,2001023422669316,2001012521478105,
  1999172303596040,1998794062013091,2000577576489580,2001356462194989,1999723900844442,
  1998553825361091,1999931607449064,2001456034005069,2000440600829289,1998632240836948,
  1999183207201509,2001166775098548,2001163938588406,1999153653199545,1998559859394707,
  2000412794333695,2001597243326504,2000108744957745,1998413369566927,1999330786747283]
private def pvm_2_14_p6 : List ℕ := [2001369067407130,2001193303434639,1999071223512953,
  1998416976415766,2000290400942550,2001730958020307,2000465201983646,1998453503699525,
  1998805674646382,2000994934640797,2001704940057352,1999859033395480,1998195436213258,
  1999173938001901,2001381446119282,2001620289335818,1999514780615826,1998039296245392,
  1999331274887595,2001684165322811,2001813199296884,1999300814617488,1997338428305651,
  1998776809108188,2002399222497579,2003963289166858,2000878190821245,1995368446013379,
  1992816278719871,1996959221918113,2006320687422879,2014641050428865,2014637705648039,
  2002463813262831,1980585445449449,1958075073953826,1948247860709941,1964166817759843,
  2013327377241620,2093623891610680,2192661565923335,2291145612505938,2369070705979548,
  2412024357518831,2414997221022654,2382508876207398,2325643916512227,2257742429658226]
private def pvm_2_14_p7 : List ℕ := [2190577847254883,2132135477053322,2086159786694541,
  2052961099782929,2030747979127994,2016887883096111,2008786296068600,2004334950124805,
  2002030042108637,2000903017532283,2000381793311677,2000153505745962,2000058717649397,
  2000021375257892,2000007407602848,2000002444401734,2000000768221493,2000000229985224,
  2000000065597523,2000000017828671,2000000004618048,2000000001140131,2000000000268300,
  2000000000060167,2000000000012842,2000000000002599,2000000000000492,2000000000000083,
  2000000000000010,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_2_14_p8 : List ℕ := [2000000000000000]
private def pvm_2_14 : List ℕ := pCat pvm_2_14_p0 (pCat pvm_2_14_p1 (pCat pvm_2_14_p2 (pCat
  pvm_2_14_p3 (pCat pvm_2_14_p4 (pCat pvm_2_14_p5 (pCat pvm_2_14_p6 (pCat pvm_2_14_p7
  pvm_2_14_p8)))))))
private def pvon_2_p0 : List ℕ := [1999999999999995,1999999999999995,1999999999999995,
  1999999999999989,2000000000000001,1999999999999999,1999999999999989,1999999999999997,
  1999999999999991,1999999999999999,1999999999999992,1999999999999987,2000000000000004,
  2000000000000000,1999999999999993,2000000000000003,2000000000000004,1999999999999995,
  1999999999999998,2000000000000007,2000000000000006,2000000000000012,1999999999999999,
  1999999999999990,2000000000000001,2000000000000014,2000000000000020,1999999999999997,
  1999999999999985,2000000000000008,2000000000000002,1999999999999993,1999999999999995,
  1999999999999997,1999999999999996,1999999999999988,1999999999999998,1999999999999988,
  1999999999999991,1999999999999995,1999999999999993,2000000000000007,2000000000000019,
  1999999999999995,1999999999999977,1999999999999982,1999999999999986,1999999999999992]
private def pvon_2_p1 : List ℕ := [1999999999999990,1999999999999984,1999999999999996,
  1999999999999992,2000000000000003,1999999999999990,1999999999999981,1999999999999980,
  1999999999999974,1999999999999985,1999999999999996,1999999999999982,1999999999999994,
  2000000000000051,2000000000000079,1999999999999814,1999999999998792,1999999999997700,
  2000000000001498,2000000000019271,2000000000045842,2000000000013903,1999999999769951,
  1999999999267093,1999999999186372,2000000001581461,2000000008585163,2000000016245381,
  2000000004764793,1999999939828369,1999999813898005,1999999739775682,2000000025687881,
  2000001041050166,2000002687432693,2000003635501280,2000001121699758,1999992375054240,
  1999977734401616,1999963229446002,1999958903837597,1999971470325969,1999996085381559,
  2000016402227577,2000017082811181,1999999467314163,1999982958710890,1999986058325700]
private def pvon_2_p2 : List ℕ := [2000005108189472,2000017015571535,2000006932224902,
  1999988161666994,1999985969552171,2000003287653238,2000015433301111,2000004764339279,
  1999987254979507,1999989547292616,2000008018926468,2000013439910605,1999997131767988,
  1999985802965195,1999998249052406,2000013452274339,2000005431286462,1999988112659315,
  1999991880822392,2000010020242540,2000009942852705,1999991806777483,1999988904763643,
  2000006605525036,2000011767240708,1999994643518488,1999987883469411,2000004483193889,
  2000012257367081,1999996012109998,1999987738816548,2000003855107522,2000012161637563,
  1999995939320770,1999988039057480,2000004574761044,2000011636240430,1999994639147309,
  1999988854097543,2000006372398135,2000010436180071,1999992451693718,1999990551209329,
  2000008808641058,2000008129907903,1999989948257297,1999993559297881,2000011154080901]
private def pvon_2_p3 : List ℕ := [2000004369078559,1999988025907558,1999998058363279,
  2000012361020398,1999999234204182,1999987830747759,2000003621292927,2000011277805913,
  1999993563794965,1999990386540020,2000008973270033,2000007174689899,1999989034748555,
  1999995947710428,2000012144495906,2000000441653971,1999987718243770,2000003358445522,
  2000011230199394,1999993035233221,1999991031787371,2000009947852508,2000005633054232,
  1999988113165053,1999998463278357,2000012431021027,1999997153709030,1999988650119497,
  2000006938930948,2000008551694917,1999989784711084,1999995910051517,2000012526290433,
  1999998324681749,1999985399452543,2000007302369154,2000018212828830,1999991681657185,
  1999975819751848,1999994941456375,2000024995104517,2000044691270085,2000007762719158,
  1999896980573360,1999875509711121,2000107483690149,2000343852825328,2000103486137096]
private def pvon_2_p4 : List ℕ := [1999483016929277,1999347164680052,2000236185682811,
  2001268539243241,2000856513078840,1998932791871521,1997762689865388,1999340645765583,
  2002223964142939,2002770667971447,2000040856135851,1997404483730052,1997938615018517,
  2000229577238557,2000956236933276,2000057275883722,2000217402007913,2001813550438987,
  2002040422487276,1999827058935113,1998014758642977,1998705902921671,1999746141945076,
  1998699523004239,1997317991838709,1998297426917470,2000161700609228,1999861856049992,
  1998409164371147,1998940394990282,2000757720581659,2000642859465813,1999000412916273,
  1999097238665411,2000812703420728,2000886031722797,1999211459134854,1999052484997414,
  2000725766490142,2000975939640235,1999312508400426,1998994025691175,2000656779291646,
  2001029638520294,1999362462350915,1998950795360106,2000627785108619,2001064189970725]
private def pvon_2_p5 : List ℕ := [1999373773658365,1998925296250474,2000630974394706,
  2001080983858180,1999359966468454,1998916374858355,2000651435190085,2001083566000232,
  1999336591906941,1998917971718007,2000674482788517,2001080404981113,1999316468257740,
  1998919869622388,2000689743793416,2001082558189985,1999307455214099,1998911133459881,
  2000691482500159,2001099998350474,1999313903855657,1998883364279362,2000675788727849,
  2001139198526320,1999340283936724,1998832147982706,2000636700654535,2001202505790394,
  1999394825986504,1998757213238478,2000563148356505,2001287970923926,1999491780968115,
  1998663137953136,2000437602824645,2001387609717544,1999651775517489,1998562535408792,
  2000236874082273,2001482476611600,1999899529519135,1998482845459167,1999936479627910,
  2001534125735516,2000256451911216,1998476132013832,1999522416208492,2001474634936881]
private def pvon_2_p6 : List ℕ := [2000722838226886,1998627233931616,1999016776345495,
  2001203658419401,2001243034815325,1999046238351323,1998521850328736,2000613988729651,
  2001655091256881,1999815202266476,1998268000693109,1999682694012937,2001663103082431,
  2000853227175250,1998591806741450,1998642127710621,2000946919785634,2001744572528087,
  1999706640273796,1998079912906513,1999500473815133,2001802058176975,2001353507405488,
  1998688929172214,1997828503399679,2000312233775269,2002737051344310,2001401486791108,
  1997597848862349,1996303616666470,1999901064365279,2004831320689534,2005221662673314,
  1999307124401429,1991797928514176,1990072162400405,1997902228171361,2011774042996408,
  2022138445037320,2018706918888693,1997124703210446,1963736383441429,1935467262107560,
  1933705296189134,1974377625821473,2059232488612047,2173284547410992,2290051685715467]
private def pvon_2_p7 : List ℕ := [2381802285414049,2429531173658175,2428181700813512,
  2385728733991507,2317883678607219,2241648621747543,2170456153077273,2112068562693657,
  2068910004626849,2039734888144612,2021531606961961,2010983295054305,2005281152784223,
  2002396243183576,2001026841328805,2000415837202895,2000159218219511,2000057656345383,
  2000019749797007,2000006399734529,2000001961636128,2000000568668960,2000000155872247,
  2000000040381926,2000000009883510,2000000002283969,2000000000497976,2000000000102341,
  2000000000019793,2000000000003588,2000000000000601,2000000000000088,2000000000000008,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_2_p8 : List ℕ := [2000000000000000]
private def pvon_2 : List ℕ := pCat pvon_2_p0 (pCat pvon_2_p1 (pCat pvon_2_p2 (pCat pvon_2_p3
  (pCat pvon_2_p4 (pCat pvon_2_p5 (pCat pvon_2_p6 (pCat pvon_2_p7 pvon_2_p8)))))))
private def pvo_2 : List ℤ := bDec bZ pvon_2
private def phbn_3_p0 : List ℕ := [94655193600000,133514057864894,163093710741950,187831399800000,
  209450703070159,228837955436017,246521069713674,262844907650471,278049631200000,292310550918157,
  305760351170544,318502377522238,330619024200840,342177265381287,353232436782787,363830900400000,
  374011971175001,383809341277412,393252153537568,402365824318990,411172683884746,419692481477186,
  427942788528639,435939324076002,443696220000000,451226239175311,458540956379200,465650909459163,
  472565726536071,479294233737167,485844546988883,492224150666399,498439965334103,504498406375215,
  510405434968278,516166602600000,521787090091184,527271741942468,532625096669855,537851413689409,
  542954697220406,547938717602510,552807030361883,557562993310992,562209781925164,566750403204173,
  571187708197978,575524403351175]
private def phbn_3_p1 : List ℕ := [579763060800000,583906127738115,587955934952461,
  591914704617633,595784557426324,599567519123920,603265526507245,606880432940395,610414013434551,
  613867969333321,617243932640594,620543470023815,623768086522081,626919228985342,629998289268279,
  633006607200000,635945473348582,638816131597614,641619781550184,644357580774323,647030646902545,
  649640059596970,652186862390462,654672064413242,657096642013626,659461540280756,661767674476500,
  664015931383106,666207170572618,668342225603562,670421905149964,672446994067353,674418254400000,
  676336426333351,678202229095263,680016361809388,681779504303800,683492317877714,685155446028933,
  686769515144487,688335135156706,689852900166850,691323389038245,692747165960726,694124780988104,
  695456770550197,696743657940912,697985953783738]
private def phbn_3_p2 : List ℕ := [699184156475910,700338752612462,701450217391248,
  702519015000000,703545598986368,704530412611884,705473889190670,706376452413719,707238516659481,
  708060487291469,708842760943547,709585725793511,710289761825567,710955241082243,711582527906257,
  712171979172837,712723944512944,713238766527836,713716780995389,714158317068557,714563697466332,
  714933238657566,715267251037961,715566039100559,715829901600000,716059131710851,716254017180253,
  716414840475132,716541878924229,716635404855148,716695685726663,716722984256457,716717558544507,
  716679662192289,716609544417971,716507450167773,716373620223635,716208291307353,716011696181325,
  715784063746032,715525619134398,715236583803140,714917175621231,714567608955590,714188094754097,
  713778840626044,713340050920118,712871926800000]
private def phbn_3_p3 : List ℕ := [712374666317684,711848464484589,711293513340547,
  710710002020751,710098116820729,709458041259422,708789956140432,708094039611500,707370467222285,
  706619411980502,705841044406465,705035532586109,704203042222529,703343736686095,702457777063183,
  701545322203577,700606528766585,699641551265909,698650542113308,697633651661103,696591028243558,
  695522818217161,694429165999864,693310214109298,692166103200000,690996972099682,689802957844586,
  688584195713924,687340819263468,686072960358281,684780749204651,683464314381216,682123782869335,
  680759280082709,679370929896286,677958854674462,676523175298606,675064011193926,673581480355695,
  672075699374860,670546783463043,668994846476964,667420000942289,665822358076933,664202027813821,
  662559118823132,660893738534038,659205993155945]
private def phbn_3_p4 : List ℕ := [657495987699263,655763825995706,654009610718140,
  652233443400000,650435424454261,648615653192016,646774227840627,644911245561500,643026802467465,
  641120993639788,639193913144815,637245654050272,635276308441209,633285967435616,631274721199706,
  629242658962889,627189869032428,625116438807792,623022454794721,620908002619000,618773167039951,
  616618031963657,614442680455916,612247194754939,610031656283792,607796145662590,605540742720458,
  603265526507245,600970575305021,598655966639343,596321777290302,593968083303366,591594960000000,
  589202481988097,586790723172207,584359756763564,581909655289937,579440490605285,576952333899240,
  574445255706410,571919325915509,569374613778318,566811187918488,564229116340175,561628466436521,
  559009304997982,556371698220505,553715711713558]
private def phbn_3_p5 : List ℕ := [551041410508017,548348859063913,545638121278043,
  542909260491441,540162339496726,537397420545317,534614565354521,531813835114501,528995290495122,
  526158991652682,523304998236524,520433369395535,517544163784540,514637439570582,511713254439099,
  508771665600000,505812729793628,502836503296644,499843041927791,496832401053580,493804635593872,
  490759800027376,487697948397053,484619134315431,481523410969839,478410831127550,475281447140852,
  472135310952022,468972474098239,465792987716401,462596902547884,459384268943208,456155136866645,
  452909555900746,449647575250800,446369243749224,443074609859885,439763721682359,436436626956115,
  433093373064647,429734007039534,426358575564444,422967124979075,419559701283036,416136350139672,
  412697116879832,409242046505574,405771183693830]
private def phbn_3_p6 : List ℕ := [402284572800000,398782257861501,395264282601269,
  391730690431200,388181524455545,384616827474257,381036641986289,377441010192844,373829974000577,
  370203575024753,366561854592360,362904853745177,359232613242797,355545173565612,351842574917750,
  348124857229978,344392060162554,340644223108051,336881385194137,333103585286309,329310861990605,
  325503253656265,321680798378360,317843534000391,313991498116840,310124728075702,306243260980967,
  302347133695082,298436382841371,294511044806429,290571155742476,286616751569691,282647867978503,
  278664540431861,274666804167471,270654694200000,266628245323258,262587492112348,258532468925786,
  254463209907597,250379748989383,246282119892365,242170356129394,238044491006946,233904557627082,
  229750588889388,225582617492889,221400675937940]
private def phbn_3_p7 : List ℕ := [217204796528091,212995011371933,208771352384914,
  204533851291140,200282539625146,196017448733655,191738609777302,187446053732349,183139811392373,
  178819913369934,174486390098223,170139271832688,165778588652646,161404370462871,157016646995159,
  152615447809886,148200802297533,143772739680205,139331289013125,134876479186111,130408338925039,
  125926896793283,121432181193145,116924220367262,112403042400000,107868675218828,103321146595685,
  98760484148320,94186715341622,89599867488935,84999967753358,80387043149026,75761120542382,
  71122226653431,66470388056982,61805631183872,57127982322179,52437467618424,47734113078755,
  43017944570115,38288987821408,33547268424643,28792811836063,24025643377272,19245788236341,
  14453271468901,9648117999234,4830352621340]
private def phbn_3 : List ℕ := pCat phbn_3_p0 (pCat phbn_3_p1 (pCat phbn_3_p2 (pCat phbn_3_p3
  (pCat phbn_3_p4 (pCat phbn_3_p5 (pCat phbn_3_p6 phbn_3_p7))))))
private def pvi_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s2 pvo_2
private def pvm_3_1_p0 : List ℕ := [2000000000000005,2000000000000005,2000000000000000,
  1999999999999999,2000000000000016,2000000000000002,2000000000000004,2000000000000003,
  1999999999999999,2000000000000008,2000000000000014,2000000000000002,1999999999999995,
  2000000000000007,2000000000000015,2000000000000000,2000000000000001,2000000000000009,
  2000000000000000,2000000000000002,2000000000000001,1999999999999995,2000000000000006,
  2000000000000002,2000000000000005,2000000000000012,1999999999999985,1999999999999977,
  1999999999999991,2000000000000020,2000000000000005,1999999999999987,1999999999999997,
  1999999999999993,1999999999999989,1999999999999999,1999999999999998,1999999999999995,
  2000000000000006,2000000000000007,1999999999999989,2000000000000008,2000000000000007,
  2000000000000012,1999999999999996,1999999999999991,2000000000000017,2000000000000025]
private def pvm_3_1_p1 : List ℕ := [2000000000000015,2000000000000004,1999999999999983,
  1999999999999985,2000000000000009,2000000000000005,2000000000000003,2000000000000015,
  2000000000000010,2000000000000007,2000000000000026,2000000000000022,1999999999999999,
  1999999999999995,2000000000000000,2000000000000006,2000000000000009,2000000000000021,
  2000000000000024,2000000000000032,2000000000000046,2000000000000049,1999999999999783,
  1999999999999248,1999999999999784,2000000000003971,2000000000009804,1999999999999456,
  1999999999947187,1999999999890210,2000000000028308,2000000000587580,2000000001112905,
  1999999999704716,1999999994530039,1999999989752419,2000000000764223,2000000041723297,
  2000000083801538,2000000022103250,1999999754025955,1999999423105145,1999999610159542,
  2000000963184008,2000003050786081,2000003419433741,1999998863612897,1999989576832660]
private def pvm_3_1_p2 : List ℕ := [1999982711075039,1999989210595750,2000012708668791,
  2000040393710890,2000049841113332,2000031165698615,2000001586276065,1999990139964161,
  2000004338864916,2000019926307923,2000012182027758,1999990361823895,1999985227210948,
  2000003421521713,2000016127566156,2000003133572518,1999985567632741,1999992319468179,
  2000011819648461,2000010685406619,1999991031543727,1999987585543815,2000006401796136,
  2000013281297568,1999995665631164,1999986381289125,2000002834961384,2000013670257963,
  1999998105933597,1999986410605867,2000001472175155,2000013455043145,1999998476844254,
  1999986712404239,2000002002643193,2000013062591847,1999997133076280,1999987278161668,
  2000004066333586,2000012183361991,1999994464063119,1999988648006499,2000007185733589,
  2000010132179896,1999991107379099,1999991556017828,2000010496533872,2000006242192364]
private def pvm_3_1_p3 : List ℕ := [1999988196669393,1999996462845205,2000012596756571,
  2000000414331581,1999987339052773,2000002951814450,2000011813226279,1999993704979780,
  1999990055560766,2000009270874541,2000007061011785,1999988509236066,1999996680037807,
  2000012576646801,1999999046133451,1999987767767878,2000005278992260,2000010320238364,
  1999990935527811,1999993070092094,2000011694227875,2000002415658214,1999987359607522,
  2000002611502076,2000011587052549,1999992647803870,1999991463213743,2000010948053540,
  2000003868676763,1999987339731675,2000001677378009,2000012073109419,1999992906678396,
  1999990711259511,2000011231181452,2000005063005997,1999987142927701,1999999229379174,
  2000010462756226,1999997915173870,1999998243566984,2000003409385406,1999983314585978,
  1999992140215539,2000047706648224,2000029695433081,1999914011177799,1999905270287413]
private def pvm_3_1_p4 : List ℕ := [2000101429319590,2000227061213837,1999980263775207,
  1999593969683820,1999735975646133,2000486786138544,2000815961311485,1999770272692068,
  1998633318175625,1999249161234062,2001596623002492,2001922345873676,1999495898436637,
  1997263423497474,1998509622520889,2002183015634979,2002645405715248,1999639194307766,
  1998375367369363,1999363154725153,1999680822259965,1999597712426389,2000285945767928,
  2000914827168956,2001153169982897,2001279463914282,2000130712077716,1997654827978035,
  1997052031056610,1999803039941254,2002149105014157,2001039622064128,1999209847968775,
  1999710399001228,2000389515436615,1998838863669381,1997578866472223,1998989549320726,
  2000344181150330,1999204482311685,1998303582570734,1999875870078886,2000987101530517,
  1999562319879756,1998730128107683,2000356643116569,2001126224790132,1999462093763759]
private def pvm_3_1_p5 : List ℕ := [1998883162481603,2000637627207133,2001041311527504,
  1999236732333351,1999038866432764,2000876385887200,2000859708377405,1999018498746860,
  1999256243917842,2001072966578167,2000615326350162,1998850973543754,1999521890847178,
  2001208537505468,2000335459805372,1998748508210675,1999809585332749,2001278594954295,
  2000045488015320,1998708996720073,2000097312175575,2001290090976838,1999763617971594,
  1998722678701208,2000370378735126,2001254218885875,1999501906638443,1998777580056621,
  2000618374136795,2001183760706717,1999269889336886,1998859636579830,2000832266982018,
  2001094688502905,1999076063641726,1998950463287105,2001004384931607,2001008000365568,
  1998926945858486,1999026626424110,2001129500291566,2000949035544177,1998826739530114,
  1999061682476646,2001203644645091,2000944354217929,1998780537008507,1999030094241063]
private def pvm_3_1_p6 : List ℕ := [2001218706219413,2001017119315620,1998801792182484,
  1998912817289369,2001153335418573,2001179810742891,1998922210319804,1998707492976819,
  2000963637172002,2001419576032829,1999198235510690,1998449053183194,2000582987392978,
  2001671037239719,1999699990887428,1998241873693776,1999950161870022,2001784868867244,
  2000461756405540,1998279763016397,1999077926442617,2001531467783391,2001409589494861,
  1998819027982134,1998103792831036,2000610356675095,2002328620586903,2000285208715945,
  1997449050829534,1998364399872872,2002142542490510,2003360778191453,1999677499640957,
  1995471360376881,1996534764565040,2002696263507136,2007404855553010,2004570447566601,
  1995162572239375,1987213866673229,1989503247316851,2003994404587057,2022416841653288,
  2029799214288112,2013921380214488,1975601367654899,1932782748885311,1914106929097280]
private def pvm_3_1_p7 : List ℕ := [1944383384107447,2030364833981894,2155571098381415,
  2287136698496749,2390219786590173,2441706941664896,2436706885793362,2386414464684212,
  2310495944594067,2228754673379565,2155569591147236,2098144718832642,2057652241471408,
  2031624006174209,2016234324770126,2007812997452490,2003529753013325,2001498474547656,
  2000598202456027,2000224673695762,2000079411009281,2000026416126725,2000008269422919,
  2000002435469654,2000000674533786,2000000175581497,2000000042921566,2000000009844306,
  2000000002115992,2000000000425662,2000000000079997,2000000000014007,2000000000002270,
  2000000000000334,2000000000000039,2000000000000001,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvm_3_1_p8 : List ℕ := [2000000000000000]
private def pvm_3_1 : List ℕ := pCat pvm_3_1_p0 (pCat pvm_3_1_p1 (pCat pvm_3_1_p2 (pCat pvm_3_1_p3
  (pCat pvm_3_1_p4 (pCat pvm_3_1_p5 (pCat pvm_3_1_p6 (pCat pvm_3_1_p7 pvm_3_1_p8)))))))
private def pvon_3_p0 : List ℕ := [2000000000000005,2000000000000003,2000000000000013,
  1999999999999996,1999999999999993,2000000000000005,2000000000000004,2000000000000004,
  2000000000000008,2000000000000008,2000000000000004,1999999999999992,1999999999999991,
  2000000000000018,2000000000000011,1999999999999999,2000000000000005,2000000000000001,
  2000000000000001,2000000000000013,1999999999999997,2000000000000004,2000000000000008,
  2000000000000005,2000000000000003,2000000000000000,2000000000000009,2000000000000010,
  1999999999999983,1999999999999984,2000000000000014,2000000000000029,1999999999999996,
  1999999999999999,1999999999999985,1999999999999986,2000000000000006,2000000000000007,
  1999999999999998,1999999999999998,1999999999999999,2000000000000003,1999999999999995,
  1999999999999977,1999999999999995,2000000000000011,1999999999999994,1999999999999992]
private def pvon_3_p1 : List ℕ := [1999999999999997,1999999999999993,2000000000000010,
  2000000000000027,1999999999999997,1999999999999983,1999999999999991,2000000000000010,
  2000000000000012,2000000000000027,2000000000000019,2000000000000001,1999999999999987,
  1999999999999994,2000000000000013,2000000000000004,1999999999999991,1999999999999993,
  2000000000000019,2000000000000009,2000000000000017,2000000000000024,2000000000000016,
  2000000000000015,1999999999999999,1999999999999985,1999999999999943,1999999999999893,
  2000000000000158,2000000000000900,2000000000000713,1999999999996614,1999999999991204,
  2000000000002484,2000000000045003,2000000000059476,1999999999894576,1999999999579141,
  1999999999779980,2000000001361493,2000000002998561,1999999999494387,1999999988113239,
  1999999983264089,2000000015162730,2000000079679545,2000000074406675,1999999866161322]
private def pvon_3_p2 : List ℕ := [1999999570167954,1999999728004649,2000000777995814,
  2000001903343502,2000000892258784,1999996727656529,1999993099696468,1999996997743275,
  2000009776982533,2000019689910028,2000010169174193,1999981715086118,1999960630458817,
  1999973754846437,2000012848289775,2000038619652378,2000029095275278,2000008780725480,
  2000011814226234,2000029930063125,2000027366456059,2000002036599434,1999991191386391,
  2000008004791663,2000017909776124,2000000066944012,1999985614463059,2000000190155496,
  2000015101301036,2000001274933437,1999985542364492,1999998681123841,2000014298812671,
  2000000982454522,1999985892466862,1999999921313556,2000013930143739,1999998723254640,
  1999986381613194,2000003033476156,2000013032736223,1999994904204004,1999987983268594,
  2000007324315019,2000010428503657,1999990479756684,1999991831495577,2000011425313592]
private def pvon_3_p3 : List ℕ := [2000005214346280,1999987263380277,1999998344720981,
  2000013140918262,1999997718329217,1999987631526876,2000006224756917,2000010261461595,
  1999990319309397,1999993154692941,2000012095510951,2000002384913577,1999987046862430,
  2000002596008488,2000011900256605,1999992647193625,1999991126754403,2000011026274325,
  2000004192146699,1999987187764893,2000001416846271,2000012167103099,1999993099141082,
  1999990999143143,2000011070632387,2000003796034782,1999987122212641,2000002404355313,
  2000011720358574,1999991826213752,1999992315519282,2000012012120404,2000001677996416,
  1999987165511467,2000004906125073,2000009782588761,1999990726262256,1999994820490323,
  2000013833353285,1999991603055263,1999998680736117,1999999820473278,2000025193342544,
  1999943098159952,2000048327101414,1999983328148610,2000051512841131,1999900406129334]
private def pvon_3_p4 : List ℕ := [1999996170600504,2000118339633098,1999998370036092,
  1999978160600096,1999752138392793,2000061867474818,2000523195426619,1999905452308507,
  1999341918417076,1999773558732606,2000702366844774,2001003832137946,1999380899747298,
  1998002918438120,2000187895143429,2002709510270905,2000704474542847,1997433137688306,
  1998310726822728,2001326304707641,2001944482105566,2000424886243599,1999059369118350,
  1998606721635968,1999391676225982,2000867040185434,2001056456840289,1999960909657022,
  2000002336575890,2000853917451613,1999578640162352,1997345093534759,1998554430618442,
  2002265974823980,2002938891737644,2000206097413221,1998897901751138,1999680628362671,
  1999184459192205,1998168440947998,1999753947889796,2001823672127982,2000746753114409,
  1998934969381575,1999745659062836,2000485011153734,1998662639218413,1997731412108337]
private def pvon_3_p5 : List ℕ := [1999553872339023,2000194452490966,1998512582281602,
  1998611781941843,2000647627555508,2000414229245354,1998689823660495,1999514091722869,
  2001186258556808,2000065671738047,1998712446043275,2000185413060602,2001217802352213,
  1999515054856654,1998885161139859,2000741887282002,2000943928629716,1999035053342540,
  1999274099409640,2001137727742908,2000469486540916,1998746168115102,1999811625173233,
  2001308227948952,1999896319466792,1998700561676507,2000392563633397,2001229210976950,
  1999335262188852,1998897430817815,2000908051772629,2000927527822346,1998887400485592,
  1999285464204167,2001271455047257,2000475638858393,1998618843302568,1999776544147628,
  2001441845926287,1999970109283211,1998542965028889,2000273733891437,2001433050575941,
  1999500420835525,1998621741414245,2000701497619917,2001302202842129,1999123825417497]
private def pvon_3_p6 : List ℕ := [1998785211281341,2001022647414643,2001125612472101,
  1998858197200442,1998956507018240,2001235718818796,2000976213853334,1998693066778854,
  1999069559372812,2001357704327186,2000911746515384,1998610684998953,1999075333737858,
  2001401461178888,2000972709806393,1998608236546826,1998941680166643,2001355417391321,
  2001182863664035,1998715122788328,1998653118287385,2001169086891665,2001550774890559,
  1999009072957142,1998204733807012,2000720325640857,2002077909795343,1999699572069759,
  1997625197338182,1999630832925651,2002586696025364,2001422917130554,1997568274863346,
  1997090474405432,2001334247760498,2004426861380509,2001424608139052,1995479821514503,
  1994296825958233,2000613038370986,2008304259853287,2008307472363044,1998050096970781,
  1985419304492265,1983439715974621,1999071732124632,2024504477920667,2039094667863049]
private def pvon_3_p7 : List ℕ := [2023274154708917,1975763186197657,1920597684939831,
  1896572216442268,1934824831899016,2039518856559977,2184250697684572,2325451090213223,
  2423169975232857,2456864830406011,2429293581483604,2359734721958842,2272783074277929,
  2188989564653302,2120438100187485,2070944402563074,2038768700993345,2019708118316010,
  2009339197963623,2004131859530829,2001708592641108,2000660873390167,2000239210133837,
  2000081039506495,2000025694099014,2000007621631344,2000002113960188,2000000547815322,
  2000000132497984,2000000029871746,2000000006267675,2000000001221598,2000000000220662,
  2000000000036831,2000000000005652,2000000000000786,2000000000000092,2000000000000007,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_3_p8 : List ℕ := [2000000000000000]
private def pvon_3 : List ℕ := pCat pvon_3_p0 (pCat pvon_3_p1 (pCat pvon_3_p2 (pCat pvon_3_p3
  (pCat pvon_3_p4 (pCat pvon_3_p5 (pCat pvon_3_p6 (pCat pvon_3_p7 pvon_3_p8)))))))
private def pvo_3 : List ℤ := bDec bZ pvon_3
private def phbn_4_p0 : List ℕ := [90209978181120,127243944983753,155434472509591,179010425453160,
  199614438842363,218091223331408,234943899793121,250501134511096,264991810907040,278583006568781,
  291401174713210,303544807571086,315092429956437,326107870790105,336643867104605,346744603633680,
  356447549003529,365784813125620,374784170219080,383469843039277,391863113171167,399982802389378,
  407845656933253,415466657639252,422859272724000,430035665689597,437006867736390,443782921831452,
  450373003937991,456785525688961,463028221869098,469108225370913,475032131753916,480806055120868,
  486435676700295,491926287268920,497282824344842,502509904920328,507611854372717,512592732086558,
  517456354234211,522206314091922,526846000210549,531378612712325,535807177945292,540134561693923,
  544363481116619,548496515557405]
private def phbn_4_p1 : List ℕ := [552536116359360,556484615790566,560344235179099,
  564117092341363,567805208377672,571410513899969,574934854748851,578379997250375,581747633057303,
  585039383614417,588256804283127,591401388156739,594474569594414,597477727498856,600412188360200,
  603279229086240,606080079637148,608815925481011,611487909884927,614097136054994,616644669137252,
  619131538090523,621558737441077,623927228928169,626237943048657,628491780508225,630689613586037,
  632832287419103,634920621212079,636955409377753,638937422613049,640867408914957,642746094540480,
  644574184914331,646352365487852,648081302552314,649761644009575,651394020102788,652979044109690,
  654517313000800,656009408064691,657455895502325,658857326992335,660214240228967,661527159434298,
  662796595846225,664023048183628,665207003089994]
private def phbn_4_p2 : List ℕ := [666348935556735,667449309327312,668508577283248,
  669527181813000,670505555164627,671444119783128,672343288633242,673203465508506,674025045327248,
  674808414416223,675553950782498,676262024374190,676932997330612,677567224222359,678165052281818,
  678726821624574,679252865462149,679743510306496,680199076166627,680619876737750,681006219583267,
  681358406309957,681676732736662,681961489056760,682212959994720,682431424956989,682617158177469,
  682770428857823,682891501302823,682980635050975,683038085000600,683064101531584,683058930622963,
  683022813966531,682955989076626,682858689396254,682731144399709,682573579691813,682386217103930,
  682169274786872,681922967300829,681647505702424,681343097629026,681009947380413,680648255997891,
  680258221340964,679840038161655,679393898176560]
private def phbn_4_p3 : List ℕ := [678919990136716,678418499895378,677889610473767,
  677333502124871,676750352395374,676140336185764,675503625808709,674840391045743,674150799202327,
  673435015161354,672693201435131,671925518215909,671132123425002,670313172760549,669468819743957,
  668599215765076,667704510126150,666784850084577,665840380894526,664871245847446,663877586311496,
  662859541769942,661817249858555,660750846402024,659660465449440,658546239308863,657408298581010,
  656246772192088,655061787425794,653853469954521,652621943869782,651367331711882,650089754498856,
  648789331754704,647466181536933,646120420463440,644752163738740,643361525179569,641948617239887,
  640513551035271,639056436366755,637577381744097,636076494408512,634553880354876,633009644353423,
  631443889970945,629856719591501,628248234436672]
private def phbn_4_p4 : List ℕ := [626618534585349,624967718993080,623295885510990,
  621603130904280,619889550870312,618155240056311,616400292076669,614624799529879,612828854015100,
  611012546148373,609175965578485,607319201002496,605442340180940,603545469952706,601628676249605,
  599692044110638,597735657695965,595759600300584,593763954367736,591748801502032,589714222482310,
  587660297274239,585587105042666,583494724163715,581383232236645,579252706095475,577103221820379,
  574934854748851,572747679486665,570541769918607,568317199219007,566074039862069,563812363632000,
  561532241632941,559233744298722,556916941402418,554581902065733,552228694768210,549857387356257,
  547468047052023,545060740462094,542635533586037,540192491824786,537731679988871,535253162306505,
  532757002431518,530243263451151,527712007893705]
private def phbn_4_p5 : List ℕ := [525163297736066,522597194411081,520013758814810,
  517413051313656,514795131751359,512160059455873,509507893246127,506838691438658,504152511854143,
  501449411823807,498729448195729,495992677341035,493239155159990,490468937087987,487682078101429,
  484878632723520,482058655029955,479222198654517,476369316794580,473500062216522,470614487261047,
  467712643848424,464794583483638,461860357261456,458910015871412,455943609602715,452961188349071,
  449962801613437,446948498512690,443918327782230,440872337780505,437810576493465,434733091538951,
  431639930171006,428531139284133,425406765417471,422266854758918,419111453149188,415940606085800,
  412754358727015,409552755895706,406335842083174,403103661452903,399856257844260,396593674776138,
  393315955450550,390023142756160,386715279271772]
private def phbn_4_p6 : List ℕ := [383392407269760,380054568719447,376701805290445,
  373334158355930,369951668995885,366554378000282,363142325872231,359715552831074,356274098815437,
  352818003486241,349347306229668,345862046160085,342362262122925,338847992697533,335319276199963,
  331776150685743,328218653952602,324646823543150,321060696747532,317460310606039,313845701911684,
  310216907212741,306573962815255,302916904785511,299245768952474,295560590910194,291861406020177,
  288148249413728,284421155994260,280680160439573,276925297204100,273156600521129,269374104404989,
  265577842653211,261767848848660,257944156361640,254106798351965,250255807771016,246391217363758,
  242513059670738,238621367030055,234716171579308,230797505257511,226865399806994,222919886775274,
  218960997516899,214988763195277,211003214784474]
private def phbn_4_p7 : List ℕ := [207004383070996,202992298655543,198966991954745,
  194928493202872,190876832453531,186812039581332,182734144283539,178643176081701,174539164323261,
  170422138183145,166292126665336,162149158604419,157993262667122,153824467353823,149642801000049,
  145448291777955,141240967697782,137020856609300,132787986203235,128542384012676,124284077414468,
  120013093630588,115729459729502,111433202627512,107124349090080,102802925733140,98468959024400,
  94122475284619,89763500688874,85392061267815,81008182908902,76611891357627,72203212218727,
  67782170957376,63348792900371,58903103237300,54445127021696,49974889172180,45492414473595,
  40997727578117,36490853006363,31971815148485,27440638265245,22897346489090,18341963825202,
  13774514152548,9195021224908,4603508671903]
private def phbn_4 : List ℕ := pCat phbn_4_p0 (pCat phbn_4_p1 (pCat phbn_4_p2 (pCat phbn_4_p3
  (pCat phbn_4_p4 (pCat phbn_4_p5 (pCat phbn_4_p6 phbn_4_p7))))))
private def pvi_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s3 pvo_3
private def pvon_4_p0 : List ℕ := [1999999999999995,2000000000000003,2000000000000000,
  1999999999999987,1999999999999989,2000000000000001,2000000000000004,1999999999999997,
  2000000000000003,1999999999999994,1999999999999994,2000000000000007,1999999999999994,
  1999999999999975,1999999999999994,1999999999999999,2000000000000003,2000000000000008,
  1999999999999995,1999999999999986,1999999999999996,1999999999999997,2000000000000000,
  1999999999999991,2000000000000000,1999999999999993,2000000000000008,2000000000000005,
  1999999999999977,1999999999999986,2000000000000015,2000000000000005,1999999999999988,
  1999999999999985,1999999999999985,2000000000000003,2000000000000016,2000000000000010,
  2000000000000001,1999999999999985,1999999999999977,1999999999999999,2000000000000021,
  1999999999999993,1999999999999995,2000000000000009,2000000000000013,1999999999999992]
private def pvon_4_p1 : List ℕ := [1999999999999997,1999999999999997,1999999999999989,
  2000000000000010,2000000000000021,2000000000000010,1999999999999987,1999999999999994,
  2000000000000008,2000000000000023,2000000000000014,1999999999999994,2000000000000000,
  1999999999999984,1999999999999973,2000000000000012,2000000000000027,2000000000000011,
  1999999999999988,1999999999999976,1999999999999993,1999999999999990,1999999999999991,
  1999999999999989,2000000000000001,2000000000000006,1999999999999996,1999999999999997,
  1999999999999993,2000000000000001,2000000000000026,2000000000000091,1999999999999978,
  1999999999999458,1999999999999429,2000000000001736,2000000000004379,1999999999997125,
  1999999999977936,1999999999987894,2000000000077324,2000000000133826,1999999999845963,
  1999999999319988,1999999999815726,2000000002248841,2000000003152621,1999999995837349]
private def pvon_4_p2 : List ℕ := [1999999984885994,1999999996527867,2000000043420679,
  2000000059106303,1999999938362889,1999999762774390,1999999904940711,2000000525247552,
  2000000828199110,1999999619874909,1999997610732449,1999998238482045,2000003293396934,
  2000007257329317,2000001281954806,1999987684117064,1999984713173830,2000004698944088,
  2000028674066561,2000021901916148,1999983491574914,1999958610589679,1999980212139089,
  2000019296971096,2000026773884950,2000007385226300,2000003956132030,2000018260035294,
  2000010237427548,1999978199802593,1999967642469969,1999986788190582,1999991289882574,
  1999971862130283,1999971859453491,1999997058651757,2000001730694627,1999982876970673,
  1999986344143652,2000009050265762,2000005234059735,1999985811117280,1999995147705777,
  2000013484454514,2000000589434992,1999985977925673,2000002913417814,2000012878191162]
private def pvon_4_p3 : List ℕ := [1999993176237331,1999989325716383,2000010210161368,
  2000007127016545,1999987371919678,1999997486533878,2000013475451254,1999997324160914,
  1999987663666589,2000007655854393,2000009090437006,1999988521276151,1999995940316542,
  2000013229667668,1999998048176475,1999987732074468,2000007694255881,2000008583436376,
  1999988071790189,1999997506882290,2000012815327385,1999996598590783,1999987771910794,
  2000011967886154,2000002069602249,1999993308627556,1999991281623106,2000027380588394,
  1999970065584020,2000022145618799,1999974497577739,2000044661929490,1999941462770118,
  2000047529720866,1999981431068070,1999994644683877,2000013579221832,1999985351229298,
  2000016979809701,1999985593028889,1999998184856457,2000017471880757,2000004423351685,
  1999931937802317,2000090886266999,2000016241599608,1999829760830546,2000148296221688]
private def pvon_4_p4 : List ℕ := [2000080516542379,1999771152800970,2000089698131142,
  2000138606905030,1999847674319493,1999985118165638,2000058507296923,2000061628393183,
  2000092185977704,1999607781983773,1999781398401688,2000973209852753,2000382229777144,
  1998413292012961,1999334868542115,2001927208233968,2000954828659969,1997995126742448,
  1998572745847255,2001489836980885,2001768069151952,1999564512210420,1998331800752522,
  1999126818860750,2000886420621304,2001838217648313,2000368825231836,1998079232010605,
  1998648491886915,2001216501758261,2001285395702221,1999334214094090,1999700852609791,
  2001232857058670,1999691444828342,1997505851616414,1999487121135490,2002606563410996,
  2001670797314519,1999207913317150,1999168876455480,1999296488043465,1998285176549386,
  1999595467158170,2002503278524170,2001975289453334,1999243372621838,1999238382670898]
private def pvon_4_p5 : List ℕ := [2000246437460027,1998924463346425,1998464411969649,
  2000812597993088,2001455112844103,1999431944759744,1999389007460921,2000813809289749,
  1999527311015094,1997782509273288,1999163287691201,2000224984095329,1998547135990148,
  1998337480910850,2000447579537523,2000283641305949,1998557033749687,1999603337446665,
  2001177276119053,1999718493620437,1998749438651910,2000626440584506,2000984613750724,
  1998989932001917,1999341641464187,2001241735596275,2000228945432351,1998661814163905,
  2000228691862978,2001275894450895,1999333027785021,1998933393788856,2001034125977017,
  2000735893056581,1998709279305310,1999676350916653,2001412205242324,1999876830889606,
  1998608411662286,2000557220328532,2001238666621984,1999062865838049,1999023137073344,
  2001232191328054,2000638386220796,1998575217388918,1999741201785463,2001510561804849]
private def pvon_4_p6 : List ℕ := [1999871994483116,1998503323533107,2000493650983098,
  2001398748141576,1999182400420192,1998762638921057,2001087908146804,2001034729962594,
  1998699297271371,1999187982290086,2001458787398174,2000587538723872,1998430158653299,
  1999624126303418,2001644600150638,2000187779141742,1998304684364471,1999969282624781,
  2001734683335731,1999909870708700,1998224663840348,2000170345333652,2001829899972901,
  1999796044085114,1998088634074515,2000179502935234,2002032836734739,1999926765693322,
  1997796071329440,1999838341113350,2002417449925118,2000607487423017,1997385394286196,
  1998617886703829,2002615225380433,2002584709730321,1997978626705108,1995896007758840,
  2000193524784319,2005206547242147,2003394979198580,1995942210630178,1992083101431463,
  1998122307307916,2009086078521818,2012432142389449,2000913145529343,1982527145378940]
private def pvon_4_p7 : List ℕ := [1976505133227554,1995823595821911,2030771042123810,
  2050952015089717,2028514786218874,1964944333562097,1897747025201800,1879114640788538,
  1941940558288828,2078231015867872,2243890728809967,2383746945253903,2458529060590088,
  2458379986670912,2399391292913221,2310049023659313,2217355102246474,2138836262545896,
  2081310438304886,2043858997155897,2021861172174044,2010093436860549,2004324225469403,
  2001721062126628,2000636825662372,2000219141540591,2000070129024592,2000020863306999,
  2000005766114999,2000001478972035,2000000351584354,2000000077331080,2000000015704597,
  2000000002937312,2000000000504427,2000000000079236,2000000000011321,2000000000001454,
  2000000000000160,2000000000000011,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_4_p8 : List ℕ := [2000000000000000]
private def pvon_4 : List ℕ := pCat pvon_4_p0 (pCat pvon_4_p1 (pCat pvon_4_p2 (pCat pvon_4_p3
  (pCat pvon_4_p4 (pCat pvon_4_p5 (pCat pvon_4_p6 (pCat pvon_4_p7 pvon_4_p8)))))))
private def pvo_4 : List ℤ := bDec bZ pvon_4
private def phbn_5_p0 : List ℕ := [97471317332736,137486286885904,167945975599400,193419645332148,
  215682152960238,235646203063479,253855414598899,270664909430735,286321994664912,301007196590326,
  314857147117101,327978266484692,340455400263632,352357515203764,363741593338948,374655375997704,
  385139347796344,395228203293421,404951952359031,414336767528878,423405643422432,432178916849485,
  440674682016930,448909125624887,456896799997200,464650847721829,472183187941769,479504672020143,
  486625214527820,493553904181607,500299098368045,506868504132889,513269247936949,519507936030023,
  525590706944011,531523277330076,537310982145651,542958810022008,548471434502318,553853241726200,
  559108355044026,564240656968311,569253808807069,574151268272361,578936305314323,583612016395158,
  588181337387527,592647055256522]
private def phbn_5_p1 : List ℕ := [597011818663008,601278147608066,605448442222792,
  609524990794568,613509977109644,617405487182151,621213515431315,624935970361393,628574679792616,
  632131395685935,635607798599624,639005501811667,642326055138165,645570948474870,648741615086076,
  651839434662672,654865736168931,657821800495709,660708862935956,663528115496962,666280709062364,
  668967755415735,671590329136490,674149469377880,676646181535943,679081438817536,681456183714843,
  683771329393118,686027760997870,688226336887148,690367889794159,692453227924975,694483135995744,
  696458376213460,698379689204009,700247794890945,702063393328173,703827165489479,705539774017624,
  707201863935520,708814063321836,710376983953169,711891221914835,713357358182102,714775959173648,
  716147577278823,717472751360258,718752007233199]
private def phbn_5_p2 : List ℕ := [719985858122895,721174805101257,722319337503938,
  723419933328900,724477059617467,725491172818819,726462719138776,727392134873726,728279846730457,
  729126272132610,729931819514457,730696888602625,731421870686379,732107148877028,732753098356995,
  733360086619043,733928473696138,734458612382405,734950848445578,735405520831368,735822961860109,
  736203497416039,736547447129567,736855124552823,737126837328816,737362887354464,737563570937785,
  737729178949491,737859996969235,737956305426751,738018379738081,738046490437125,738040903302695,
  738001879481261,737929675605581,737824543909364,737686732338148,737516484656534,737314040551923,
  737079635734904,736813502036420,736515867501832,736186956482020,735826989721615,735436184444492,
  735014754436607,734562910126305,734080858662168]
private def phbn_5_p3 : List ℕ := [733568803988510,733026946918613,732455485205760,
  731854613612180,731224523975951,730565405275960,729877443694965,729160822680853,728415723006129,
  727642322825727,726840797733177,726011320815207,725154062704809,724269191632848,723356873478243,
  722417271816782,721450547968606,720456861044412,719436367990422,718389223632150,717315580717007,
  716215589955792,715089400063093,713937157796638,712759007995632,711555093618105,710325555777317,
  709070533777227,707790165147073,706484585675092,705153929441387,703798328849991,702417914660134,
  701012816016750,699583160480239,698129074055507,696650681220313,695148104952931,693621466759158,
  692070886698682,690496483410834,688898374139728,687276674758825,685631499794928,683962962451620,
  682271174632170,680556246961915,678818288810140]
private def phbn_5_p4 : List ℕ := [677057408311461,675273712386728,673467306763472,
  671638295995884,669786783484368,667912871494658,666016661176519,664098252582044,662157744683551,
  660195235391107,658210821569664,656204599055841,654176662674347,652127106254058,650056022643759,
  647963503727559,645849640439983,643714522780757,641558239829288,639380879758845,637182529850460,
  634963276506538,632723205264201,630462400808360,628180946984530,625878926811388,623556422493085,
  621213515431315,618850286237147,616466814742632,614063180012176,611639460353704,609195733329600,
  606732075767446,604248563770555,601745272728297,599222277326243,596679651556108,594117468725514,
  591535801467572,588934721750281,586314300885762,583674609539312,581015717738307,578337694880928,
  575640609744741,572924530495114,570189524693487]
private def phbn_5_p5 : List ℕ := [567435659305496,564663000708948,561871614701658,
  559061566509143,556232920792193,553385741654290,550520092648917,547636036786732,544733636542611,
  541812953862587,538874050170651,535916986375454,532941822876884,529948619572533,526937435864064,
  523908330663456,520861362399160,517796589022143,514714068011835,511613856381977,508496010686374,
  505360587024550,502207641047321,499037227962262,495849402539097,492644219115003,489421731599817,
  486181993481175,482925057829555,479650977303252,476359804153267,473051590228118,469726386978584,
  466384245462366,463025216348678,459649349922770,456256696090378,452847304382104,449421223957735,
  445978503610490,442519191771201,439043336512443,435550985552582,432042186259780,428516985655931,
  424975430420538,421417566894535,417843441084053]
private def phbn_5_p6 : List ℕ := [414253098664128,410646584982351,407023945062477,
  403385223607966,399730465005479,396059713328329,392373012339871,388670405496853,384951935952711,
  381217646560823,377467579877711,373701778166204,369920283398551,366123137259491,362310381149281,
  358482056186683,354638203211905,350778862789502,346904075211245,343013880498935,339108318407191,
  335187428426197,331251249784407,327299821451217,323333182139598,319351370308699,315354424166406,
  311342381671876,307315280538026,303273158234004,299216051987609,295143998787694,291057035386529,
  286955198302135,282838523820588,278707047998292,274560806664219,270399835422131,266224169652757,
  262033844515955,257828894952838,253609355687881,249375261230989,245126645879552,240863543720464,
  236585988632118,232294014286381,227987654150540]
private def phbn_5_p7 : List ℕ := [223666941489219,219331909366285,214982590646716,
  210619017998452,206241223894226,201849240613369,197443100243588,193022834682733,188588475640532,
  184140054640311,179677603020691,175201151937262,170710732364243,166206375096115,161688110749238,
  157155969763449,152609982403637,148050178761307,143476588756113,138889242137386,134288168485638,
  129673397214042,125044957569908,120402878636130,115747189332624,111077918417740,106395094489672,
  101698745987833,96988901194232,92265588234824,87528835080845,82778669550141,78015119308468,
  73238211870789,68447974602550,63644434720941,58827619296149,53997555252589,49154269370128,
  44297788285288,39428138492443,34545346344998,29649438056558,24740439702077,19818377219008,
  14883276408421,9935162936131,4974062333793]
private def phbn_5 : List ℕ := pCat phbn_5_p0 (pCat phbn_5_p1 (pCat phbn_5_p2 (pCat phbn_5_p3
  (pCat phbn_5_p4 (pCat phbn_5_p5 (pCat phbn_5_p6 phbn_5_p7))))))
private def pvi_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s4 pvo_4
private def pvon_5_p0 : List ℕ := [2000000000000005,2000000000000004,1999999999999997,
  1999999999999994,1999999999999996,2000000000000014,2000000000000009,2000000000000003,
  2000000000000004,2000000000000007,1999999999999990,1999999999999995,2000000000000013,
  2000000000000009,1999999999999993,1999999999999997,1999999999999998,2000000000000012,
  2000000000000011,2000000000000023,2000000000000005,1999999999999990,2000000000000002,
  2000000000000001,1999999999999996,2000000000000012,2000000000000013,1999999999999988,
  1999999999999995,2000000000000022,2000000000000014,1999999999999996,1999999999999988,
  1999999999999997,2000000000000007,2000000000000025,2000000000000000,1999999999999991,
  1999999999999998,2000000000000000,2000000000000003,2000000000000022,2000000000000035,
  1999999999999991,1999999999999972,1999999999999996,2000000000000007,2000000000000002]
private def pvon_5_p1 : List ℕ := [2000000000000005,2000000000000013,1999999999999997,
  2000000000000001,2000000000000008,1999999999999996,1999999999999995,1999999999999982,
  1999999999999988,2000000000000030,2000000000000018,1999999999999992,1999999999999984,
  1999999999999996,1999999999999999,1999999999999996,2000000000000007,2000000000000004,
  1999999999999996,1999999999999969,1999999999999970,2000000000000001,2000000000000022,
  2000000000000024,1999999999999998,1999999999999984,2000000000000002,1999999999999989,
  1999999999999990,2000000000000003,2000000000000022,2000000000000018,2000000000000030,
  1999999999999959,1999999999999917,2000000000000143,2000000000000498,1999999999999721,
  1999999999997683,1999999999999503,2000000000009213,2000000000008825,1999999999970284,
  1999999999943432,2000000000068687,2000000000260731,1999999999954892,1999999999052031]
private def pvon_5_p2 : List ℕ := [1999999999414737,2000000002699907,2000000004027277,
  1999999994639345,1999999983327208,2000000002795625,2000000050913466,2000000032922766,
  1999999886084893,1999999819966139,2000000150323261,2000000574745478,2000000099425412,
  1999998726725313,1999998742212428,2000001774527772,2000004088976113,1999999694974485,
  1999991805381727,1999994025430709,2000009781572913,2000017741332499,1999998236353761,
  1999972121320739,1999981456270173,2000022298149901,2000037744827939,2000002441486678,
  1999967227394857,1999978943190688,2000006939518998,2000006196944590,1999998086603695,
  2000015699161207,2000027695670077,2000000663850002,1999973895721402,1999985311951369,
  1999997966697913,1999983115197808,1999982373110729,2000012780332260,2000024059524015,
  2000006925027674,2000011720529761,2000033045951876,2000022345315014,2000001351442887]
private def pvon_5_p3 : List ℕ := [2000013410321424,2000023286791012,2000001036755812,
  1999993682863700,2000013909823231,2000008882258261,1999988454584934,1999999430769638,
  2000015012449484,1999993463041248,1999991794765517,2000006481953327,2000012299009926,
  1999976834116244,2000015422831952,1999992917053657,2000018275628092,1999958948990019,
  2000050647834713,1999960162456282,2000027006307321,1999972442121525,2000031060569269,
  1999983110386256,1999985858239410,2000036937240397,1999967566234344,2000010447579513,
  2000003959896793,1999999768142841,1999989372207367,2000015785256226,1999984970076799,
  2000010755686817,2000005018822168,1999961982951210,2000065700802486,1999956831009775,
  1999957257224906,2000125814790022,1999898943714975,1999951263259086,2000182178319567,
  1999871816603289,1999916512438977,2000208430763228,1999910281010379,1999884339110808]
private def pvon_5_p4 : List ℕ := [2000155067254180,1999964860306759,1999947113996967,
  2000074948811806,1999882932649970,2000071915312396,2000198437729650,1999641739806287,
  1999910597794107,2000680858609100,1999786431165938,1999038026443598,2000628823160758,
  2001187755168546,1998981799278208,1998613161170146,2001215588347869,2001564836860338,
  1998920618349826,1998347750910160,2000578516530612,2001549772255565,2000184147202453,
  1998772114731636,1998902978665702,2000636133177225,2001986918937893,2000331587240441,
  1997672062715227,1998819527529983,2002107951756293,2001541226420903,1998525606462665,
  1998959401772182,2001034239012589,1999920801077375,1998721371309766,2000977826456113,
  2001977128214856,1999143701565459,1997940130750274,1999978302720714,2000664449925471,
  2000248394741131,2001435073225286,2001049527402075,1997847980693761,1997538955633869]
private def pvon_5_p5 : List ℕ := [2000810675556372,2001660381014793,2000292177726405,
  2000829296058779,2000819447509642,1998247337447478,1997943214980598,2000603249391154,
  2000858029997766,1999522283863174,2000743837372765,2001502266853441,1999245400315344,
  1998682983299427,2000706230089353,2000397245956792,1999041720082875,2000758552900958,
  2002102688594824,2000314495200066,2000046089273792,2001956080282613,2001125148075488,
  1999239771290428,2000570633234892,2001514485228461,1999441960148692,1999203614879011,
  2001238386568205,2000438975224219,1998666121051611,2000223658723065,2001288426091963,
  1999222092318269,1999051195905055,2001209205633307,2000436390329161,1998589671391710,
  2000162970990904,2001357735336825,1999265480567893,1998931916094067,2001181029299096,
  2000601433897973,1998565346692681,1999957556240642,2001467056423313,1999482049163856]
private def pvon_5_p6 : List ℕ := [1998711256385669,2000999708465861,2000941134304454,
  1998654435514569,1999515809862746,2001526341112599,1999983136821106,1998459963968416,
  2000502871333072,2001406342739499,1999071571011892,1998841204851962,2001265420664381,
  2000836615653745,1998497063002752,1999522199412138,2001644664863122,2000114269625217,
  1998294968027639,2000230739220840,2001705272359318,1999456711540405,1998329682378650,
  2000817803694461,2001627140170153,1998945123594537,1998395062187131,2001257613361433,
  2001637265594028,1998574610157244,1998234493993319,2001542393862855,2002040964424750,
  1998443197823953,1997482449644377,2001347138245939,2003216173549646,1999317465700990,
  1995973338807006,1999219139246500,2004510576889255,2003343523184507,1996358379236494,
  1993288564602180,1999804252026092,2008871525358110,2008030107362108,1994957643516136]
private def pvon_5_p7 : List ℕ := [1983271257915028,1990095789697110,2013216847643871,
  2033280533481590,2012484235543037,1981541748307772,1933916654457561,1939468227483136,
  2064631166666712,2108636339105876,2047688428582888,2026721869608610,2115767565634197,
  2269161445303239,2406043767110345,2472475478238388,2458165264190562,2385068870212360,
  2286819791946714,2191973612415585,2116523000926845,2064545774004795,2032776073062806,
  2015306182152708,2006588284563358,2002617737910866,2000960988195724,2000326071266747,
  2000102252173025,2000029619163913,2000007917805532,2000001950630823,2000000442075123,
  2000000091953962,2000000017505175,2000000003039361,2000000000479273,2000000000068275,
  2000000000008720,2000000000000982,2000000000000091,2000000000000004,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_5_p8 : List ℕ := [2000000000000000]
private def pvon_5 : List ℕ := pCat pvon_5_p0 (pCat pvon_5_p1 (pCat pvon_5_p2 (pCat pvon_5_p3
  (pCat pvon_5_p4 (pCat pvon_5_p5 (pCat pvon_5_p6 (pCat pvon_5_p7 pvon_5_p8)))))))
private def pvo_5 : List ℤ := bDec bZ pvon_5
private def phbn_6_p0 : List ℕ := [80090880000000,112970646195691,137998965709032,158930340000000,
  177223145265509,193627338672216,208589604658624,222401742118933,235266960000000,247333594342994,
  258713913764135,269495362353241,279747656582751,289527465510152,298881610511837,307849320000000,
  316463859643307,324753737497276,332743612271465,340454989589005,347906763821685,355115645454573,
  362096502255874,368862634620951,375426000000000,381797397482066,387986620867804,394002586577401,
  399853441281359,405546653056926,411089089057032,416487082058268,421746487778329,426872734484467,
  431870866126380,436745580000000,441501259768616,446142004523936,450671654453980,455093813591110,
  459411870037271,463629014001156,467748253930674,471772430981658,475704232028473,479546201392768,
  483300751441908,486970172187895]
private def phbn_6_p1 : List ℕ := [490556640000000,494062225529462,497488900931954,
  500838546462667,504112956509602,507313845122721,510442851089668,513501542602912,516491421557929,
  519413927517641,522270441374343,525062288737012,527790743068847,530457028597293,533062323016484,
  535607760000000,538094431540041,540523390127520,542895650786160,545212192972437,547473962352068,
  549681872462768,551836806272097,553939617638405,555991132682193,557992151074542,559943447248693,
  561845771540343,563699851261739,565506391714229,567266077143570,568979571641899,570647520000000,
  572270548513180,573849265743842,575384263243557,576876116237273,578325384272056,579732611832614,
  581098328925665,582423051635061,583707282649467,584951511764225,586156216358957,587321861852327,
  588448902135290,589537779984073,590588927454044]
private def phbn_6_p2 : List ℕ := [591602766255536,592579708112650,593520155105957,
  594424500000000,595293126556400,596126409833352,596924716472222,597688404971926,598417825951734,
  599113322403078,599775229930947,600403876985372,600999585083518,601562669022833,602093437085703,
  602592191236025,603059227308081,603494835188092,603899298988788,604272897217335,604615902936913,
  604928583922250,605211202809385,605464017239918,605687280000000,605881239154298,606046138175154,
  606182216067148,606289707487270,606368842860885,606419848493679,606442946679745,606438355805984,
  606406290452964,606346961492395,606260576181348,606147338253362,606007448006554,605841102388860,
  605648495080526,605429816573940,605185254250932,604914992457624,604619212576932,604298093098813,
  603951809688334,603580535251655,603184440000000]
private def phbn_6_p3 : List ℕ := [602763691511690,602318454792316,601848892333111,
  601355164167598,600837427926564,600295838891437,599730550046105,599141712127245,598529473673212,
  597893981071536,597235378605077,596553808496886,595849410953817,595122324208924,594372684562700,
  593600626423186,592806282344988,591989783067241,591151257550561,590290833013005,589408634965080,
  588504787243840,587579412046073,586632629960646,585664560000000,584675319630840,583665024804046,
  582633789983822,581581728176108,580508950956283,579415568496178,578301689590419,577167421682120,
  576012870887949,574838142022583,573643338622571,572428562969625,571193916113351,569939497893440,
  568665406961335,567371740801390,566058595751527,564726067023424,563374248722224,562003233865800,
  560613114403574,559203981234908,557775924227085]
private def phbn_6_p4 : List ℕ := [556329032232872,554863393107707,553379093726488,
  551876220000000,550354856890972,548815088429795,547256997729877,545680667002689,544086177572463,
  542473609890593,540843043549718,539194557297507,537528229050158,535844135905605,534142354156456,
  532422959302655,530686026063887,528931628391727,527159839481533,525370731784104,523564377017096,
  521740846176214,519900209546168,518042536711419,516167896566707,514276357327371,512367986539463,
  510442851089668,508501017215028,506542550512469,504567515948162,502575977866679,500568000000000,
  498543645476320,496502976828716,494446056003627,492372944369190,490283702723407,488178391302175,
  486057069787150,483919797313477,481766632477371,479597633343566,477412857452620,475212361828093,
  472996202983592,470764436929689,468517119180718]
private def phbn_6_p5 : List ℕ := [466254304761449,463976048213638,461682403602470,
  459373424522885,457049164105788,454709675024155,452355009499036,449985219305444,447600355778153,
  445200469817390,442785611894429,440355832057095,437911179935169,435451704745704,432977455298252,
  430488480000000,427984826860825,425466543498265,422933677142399,420386274640657,417824382462544,
  415248046704292,412657313093432,410052226993291,407432833407421,404799176983955,402151302019885,
  399489252465288,396813071927467,394122803675041,391418490641957,388700175431454,385967900319947,
  383221707260868,380461637888434,377687733521363,374900035166532,372098583522576,369283418983435,
  366454581641845,363612111292776,360756047436818,357886429283518,355003295754661,352106685487509,
  349196636837987,346273187883822,343336376427638]
private def phbn_6_p6 : List ℕ := [340386240000000,337422815862420,334446141010316,
  331456252175923,328453185831169,325436978190507,322407665213701,319365282608580,316309865833747,
  313241450101249,310160070379214,307065761394444,303958557634974,300838493352599,297705602565357,
  294559919059986,291401476394338,288230307899768,285046446683485,281849925630869,278640777407761,
  275419034462716,272184729029231,268937893127939,265678558568772,262406756953098,259122519675828,
  255825877927492,252516862696294,249195504770129,245861834738585,242515882994908,239157679737946,
  235787254974072,232404638519068,229009860000000,225602948857057,222183934345373,218752845536823,
  215309711321790,211854560410923,208387421336857,204908322455922,201417291949825,197914357827310,
  194399547925803,190872889913025,187334411288600]
private def phbn_6_p7 : List ℕ := [183784139385625,180222101372239,176648324253154,
  173062834871181,169465659908733,165856825889301,162236359178930,158604285987654,154960632370934,
  151305424231067,147638687318579,143960447233602,140270729427238,136569559202902,132856961717647,
  129132961983481,125397584868660,121650855098970,117892797258992,114123435793356,110342795007971,
  106550899071250,102747772015317,98933437737197,95107920000000,91271242434077,87423428538183,
  83564501680603,79694485100287,75813401907956,71921275087203,68018127495578,64103981865665,
  60178860806141,56242786802828,52295782219727,48337869300050,44369070167230,40389406825924,
  36398901163007,32397574948554,28385449836805,24362547367128,20328888964968,16284495942779,
  12229389500960,8163590728766,4087120605218]
private def phbn_6 : List ℕ := pCat phbn_6_p0 (pCat phbn_6_p1 (pCat phbn_6_p2 (pCat phbn_6_p3
  (pCat phbn_6_p4 (pCat phbn_6_p5 (pCat phbn_6_p6 phbn_6_p7))))))
private def pvi_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s5 pvo_5
private def pvon_6_p0 : List ℕ := [1999999999999995,1999999999999996,1999999999999999,
  2000000000000002,2000000000000012,2000000000000002,1999999999999990,1999999999999990,
  2000000000000000,1999999999999992,1999999999999988,2000000000000004,2000000000000014,
  1999999999999994,1999999999999993,1999999999999990,2000000000000010,1999999999999995,
  2000000000000015,1999999999999991,1999999999999987,1999999999999990,1999999999999985,
  1999999999999994,2000000000000004,1999999999999991,1999999999999987,2000000000000014,
  2000000000000017,1999999999999997,1999999999999985,2000000000000009,2000000000000012,
  2000000000000018,2000000000000005,1999999999999981,1999999999999989,2000000000000014,
  2000000000000015,2000000000000000,2000000000000007,2000000000000005,1999999999999978,
  1999999999999988,2000000000000026,2000000000000037,2000000000000004,1999999999999995]
private def pvon_6_p1 : List ℕ := [1999999999999996,1999999999999985,2000000000000003,
  2000000000000008,2000000000000000,2000000000000012,1999999999999993,2000000000000002,
  2000000000000018,2000000000000006,1999999999999977,1999999999999972,2000000000000010,
  2000000000000016,2000000000000010,1999999999999998,1999999999999995,1999999999999997,
  1999999999999988,1999999999999993,2000000000000015,2000000000000012,2000000000000009,
  1999999999999966,1999999999999962,1999999999999992,2000000000000021,2000000000000002,
  2000000000000013,2000000000000006,1999999999999992,1999999999999988,2000000000000002,
  1999999999999997,1999999999999952,1999999999999960,2000000000000241,2000000000000360,
  1999999999999266,1999999999998110,2000000000001859,2000000000008734,1999999999998065,
  1999999999965251,1999999999985783,2000000000118769,2000000000125906,1999999999663246]
private def pvon_6_p2 : List ℕ := [1999999999352785,2000000000709495,2000000002575104,
  1999999999422769,1999999991614399,1999999996195685,2000000022233890,2000000025838830,
  1999999955135546,1999999899251522,2000000050354409,2000000293566444,2000000075252640,
  1999999340726210,1999999369576245,2000001061969651,2000002116579269,1999999213343781,
  1999995138304219,1999998191270815,2000007911145115,2000008681254007,1999992304447645,
  1999980586073354,1999998914385274,2000027621607850,2000019476027012,1999977458238883,
  1999963460160816,2000001671286587,2000034089422084,2000016275770236,1999988423991089,
  1999992957231570,1999999737939595,1999982560150066,1999981499162262,2000015113823823,
  2000030257212208,2000006438924882,1999995315556683,2000007830173851,1999996249704393,
  1999969872616284,1999980142386890,2000004491795973,1999997273627702,1999991752837075]
private def pvon_6_p3 : List ℕ := [2000019152663843,2000028534797373,2000010001049999,
  2000010461665134,2000033879901442,2000012026835751,2000005015660001,2000004887459193,
  2000032214744112,1999975265719322,2000022546267566,1999984868916362,2000036553717958,
  1999948576783305,2000048095732941,1999974063162414,2000012167279726,1999988504364931,
  2000008102969403,2000012248951463,1999964205437739,2000038006921670,1999984560103332,
  1999992165799568,2000009198615322,2000007295875627,1999980529708918,2000014386264754,
  2000001835860961,1999981385792692,2000032601848532,1999961180275091,2000021377066815,
  2000028838084827,1999916661927985,2000081707551432,2000006314221259,1999879913724072,
  2000138689154220,1999990277630483,1999844381150518,2000170651187684,2000005450570252,
  1999817576292614,2000152363835943,2000040875271844,1999839795662909,2000097417945015]
private def pvon_6_p4 : List ℕ := [2000022683872512,1999913523557858,2000118841558591,
  1999912883267221,1999883269817281,2000316182331750,1999914876759334,1999536361695348,
  2000442176201253,2000445230913698,1999140169537384,1999737055571027,2001249686106744,
  1999995749738960,1998443882586078,2000230456794231,2001746095906421,1999717007580810,
  1998220972384912,2000074253852288,2001592704193270,2000385616191659,1998860182769133,
  1999017157932835,2000449577136981,2001573700960204,2000386576815193,1997972621722062,
  1998724051325356,2002125435302840,2001952013549878,1998276741934880,1998099000446325,
  2001247192828375,2001167134757584,1999028287251951,2000040033021022,2001237958946833,
  1999046214530541,1998257633104031,2000968431160157,2001670714474254,1999749634278031,
  1999621305167381,1999853512870423,1998409507163031,1999376639258843,2002557418724381]
private def pvon_6_p5 : List ℕ := [2001803199366023,1998486867605711,1998534189978636,
  1999835340407043,1999214247558105,2000170393975238,2002479250745889,2001097042523681,
  1998380875886609,1999196717718139,2000146408035695,1998804826681557,1999573776764838,
  2001858422255976,2000748721268848,1998996635719006,2000358040949691,2000654015290122,
  1998667167239396,1999433381657981,2001572207984659,2000487262125142,1999647942729326,
  2001735879445649,2001800462643303,1999655638296554,2000462084128027,2001885368200481,
  1999977134804727,1999143241967923,2001187630446485,2000772215265434,1998739038462167,
  2000044369717558,2001375449152842,1999354485978890,1998962675553352,2001174509120782,
  2000498782516242,1998582189269356,2000165427051229,2001357495702229,1999207576150245,
  1998989878741055,2001256659880634,2000460842650355,1998527130906224,2000173767798923]
private def pvon_6_p6 : List ℕ := [2001414437049985,1999227805847770,1998890419395467,
  2001233913130769,2000627367450180,1998504517130973,1999942561738033,2001535777128303,
  1999489688393246,1998628488652793,2001001660276701,2001046365701142,1998632715636095,
  1999382411193209,2001585136417259,2000143443390271,1998342607297982,2000326323338607,
  2001604150756208,1999243874433653,1998543901481427,2001126537921144,2001247956174176,
  1998566437540502,1998986089963940,2001686298648677,2000785773050994,1998096061931278,
  1999405619273346,2002112330012696,2000474772033164,1997660978416753,1999524293669651,
  2002603216638144,2000672984121093,1997106935948058,1998818780591098,2003117916240036,
  2002144850702983,1996976081399590,1996340552431756,2002088303544538,2005531564888664,
  2000494811965505,1993206585915375,1994634398687821,2005003811912799,2011874561683106]
private def pvon_6_p7 : List ℕ := [2002414839816646,1987538637410598,1978309305531268,
  2007117594171315,2024761372652498,2028507513735445,2011517906427869,1918781515421622,
  1927504983501886,2045226663072477,2095384411316802,2045618281600034,2014044516582566,
  2084037327282418,2232920355874320,2383009108452492,2469352342919205,2470702271181548,
  2404562719467287,2305794548379540,2206509943312974,2125892396588102,2069768731031608,
  2035323378457478,2016394881967746,2006992630148393,2002745001574021,2000992673718083,
  2000330807327919,2000101570474574,2000028713926900,2000007465404137,2000001782140687,
  2000000389787182,2000000077899356,2000000014177738,2000000002340269,2000000000348595,
  2000000000046556,2000000000005520,2000000000000567,2000000000000044,2000000000000001,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_6_p8 : List ℕ := [2000000000000000]
private def pvon_6 : List ℕ := pCat pvon_6_p0 (pCat pvon_6_p1 (pCat pvon_6_p2 (pCat pvon_6_p3
  (pCat pvon_6_p4 (pCat pvon_6_p5 (pCat pvon_6_p6 (pCat pvon_6_p7 pvon_6_p8)))))))
private def pvo_6 : List ℤ := bDec bZ pvon_6
private def phbn_7_p0 : List ℕ := [88225920000000,124445369979820,152015881317921,175073310000000,
  195224163304776,213294573508343,229776595955037,244991668315364,259163640000000,272455913929494,
  284992162136831,296868710636568,308162357185453,318935526865249,329239796821917,339118380000000,
  348607920949073,357739823362356,366541250598986,375035892664438,383244563081226,391185669662058,
  398875590333214,406328976445973,413559000000000,420577556976038,427395435956668,434022459026182,
  440467600333694,446739086508578,452844482218432,458790763476518,464584380781081,470231313762663,
  475737118698118,481106970000000,486345696591736,491457813920491,496447552232220,501318881630270,
  506075534354956,510721024652805,515258666547644,519691589778927,524022754133873,528254962367528,
  532390871877717,536433005278947]
private def phbn_7_p1 : List ℕ := [540383760000000,544245417013576,548020148792354,
  551710026573956,555317027007066,558843038242177,562289865522879,565659236327046,568952805101606,
  572172157629648,575318815064305,578394237660125,581399828229290,584336935347227,587206856329541,
  590010840000000,592750089267306,595425763526626,598038980900294,600590820330740,603082323537418,
  605514496848460,607888312916746,610204712329251,612464605117693,614668872177836,616818366604130,
  618913914945829,620956318390185,622946353877848,624884775155204,626772313767966,628609680000000,
  630397563761066,632136635426842,633827546634336,635470931035598,637067405012352,638617568354041,
  640122004901549,641581283158716,642995956873607,644366565591358,645693635180286,646977678332845,
  648219195042880,649418673060559,650576588326240]
private def phbn_7_p2 : List ℕ := [651693405384479,652769577779268,653805548431553,
  654801750000000,655758605225898,656676527263086,657555919993649,658397178330176,659200688505253,
  659966828348848,660695967554225,661388467932945,662044683659509,662664961506166,663249641068350,
  663799054981220,664313529127719,664793382838568,665238929084571,665650474661595,666028320368560,
  666372761178773,666684086404902,666962579857877,667208520000000,667422180092514,667603828337885,
  667753728017010,667872137621603,667959310981937,668015497390158,668040941719350,668035884538543,
  668000562223813,667935207065662,667840047372804,667715307572524,667561208307742,667377966530913,
  667165795594890,666924905340872,666655502183549,666357789193563,666031966177365,665678229754604,
  665296773433107,664887787681565,664451460000000]
private def phbn_7_p3 : List ℕ := [663987974988101,663497514411509,662980257266117,
  662436379840468,661866055776323,661269456127450,660646749416709,659998101691495,659323676577594,
  658623635331499,657898136891257,657147337925886,656371392883417,655570454037595,654744671533313,
  653894193430787,653019165748539,652119732505222,651196035760317,650248215653751,649276410444465,
  648280756547962,647261388572879,646218439356610,645152040000000,644062319901153,642949406788386,
  641813426752328,640654504277229,639472762271471,638268322097327,637041303599975,635791825135809,
  634520003600042,633225954453654,631909791749670,630571628158825,629211574994596,627829742237653,
  626426238559724,625001171346902,623554646722406,622086769568810,620597643549765,619087371131212,
  617556053602115,616003791094723,614430682604372]
private def phbn_7_p4 : List ℕ := [612836826008839,611222318087267,609587254538665,
  607931730000000,606255838063889,604559671295908,602843321251513,601106878492606,599350432603736,
  597574072207956,595777884982334,593961957673150,592126376110750,590271225224109,588396589055073,
  586502550772314,584589192684991,582656596256132,580704842115739,578734010073629,576744179132008,
  574735427497800,572707832594716,570661471075093,568596418831490,566512751008055,564410542011671,
  562289865522879,560150794506586,557993401222575,555817757235796,553623933426471,551412000000000,
  549182026496677,546934081801226,544668234152148,542384551150900,540083099770899,537763946366358,
  535427156680955,533072795856345,530700928440516,528311618395987,525904929107862,523480923391732,
  521039663501439,518581211136696,516105627450573]
private def phbn_7_p5 : List ℕ := [513612973056847,511103308037226,508576691948437,
  506033183829197,503472842207054,500895725105120,498301890048669,495691394071641,493064293723017,
  490420645073090,487760503719636,485083924793968,482390962966893,479681672454568,476956107024260,
  474214320000000,471456364268154,468682292282898,465892156071592,463086007240083,460263896977905,
  457425876063406,454571994868780,451702303365026,448816851126826,445915687337338,442998860792917,
  440066419907763,437118412718489,434154886888618,431175889713012,428181468122231,425171668686817,
  422146537621521,419106120789457,416050463706193,412979611543782,409893609134724,406792500975879,
  403676331232306,400545143741054,397398982014893,394237889245983,391061908309499,387871081767189,
  384665451870891,381445060565985,378209949494807]
private def phbn_7_p6 : List ℕ := [374960160000000,371695733127824,368416709631419,
  365123129974009,361815034332072,358492462598455,355155454385452,351804049027829,348438285585811,
  345058202848025,341663839334403,338255233299039,334832422733008,331395445367150,327944338674803,
  324479139874512,320999885932690,317506613566243,313999359245165,310478159195092,306943049399818,
  303394065603784,299831243314528,296254617805100,292664224116451,289060097059784,285442271218870,
  281810780952347,278165660395968,274506943464837,270834663855606,267148855048641,263449550310169,
  259736782694385,256010585045541,252270990000000,248518029988268,244751737237001,240972143770977,
  237179281415054,233373181796095,229553876344870,225721396297936,221875772699487,218017036403192,
  214145218073993,210260348189898,206362457043737]
private def phbn_7_p7 : List ℕ := [202451574744903,198527731221071,194590956219895,
  190641279310679,186678729886038,182703337163525,178715130187251,174714137829474,170700388792175,
  166673911608615,162634734644868,158582886101339,154518394014264,150441286257193,146351590542446,
  142249334422566,138134545291743,134007250387226,129867476790717,125715251429748,121550601079045,
  117373552361869,113184131751350,108982365571797,104768280000000,100541901066507,96303254656902,
  92052366513051,87789262234341,83513967278911,79226506964858,74926906471432,70615190840226,
  66291384976339,61955513649536,57607601495390,53247673016412,48875752583171,44491864435394,
  40096032683064,35688281307499,31268634162416,26837114974994,22393747346915,17938554755397,
  13471560554217,8992787974721,4502260126825]
private def phbn_7 : List ℕ := pCat phbn_7_p0 (pCat phbn_7_p1 (pCat phbn_7_p2 (pCat phbn_7_p3
  (pCat phbn_7_p4 (pCat phbn_7_p5 (pCat phbn_7_p6 phbn_7_p7))))))
private def pvi_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r384_s6 pvo_6
private def pvon_7_p0 : List ℕ := [2000000000000005,2000000000000004,2000000000000001,
  2000000000000004,1999999999999993,1999999999999989,1999999999999993,2000000000000012,
  2000000000000006,1999999999999998,2000000000000006,2000000000000020,2000000000000000,
  1999999999999995,1999999999999985,2000000000000016,1999999999999999,2000000000000009,
  2000000000000002,1999999999999987,1999999999999994,2000000000000002,2000000000000004,
  2000000000000015,2000000000000023,1999999999999999,1999999999999998,2000000000000011,
  2000000000000023,1999999999999989,1999999999999984,1999999999999997,2000000000000005,
  2000000000000009,2000000000000000,1999999999999977,1999999999999976,2000000000000007,
  2000000000000018,1999999999999995,1999999999999997,2000000000000001,1999999999999989,
  1999999999999974,2000000000000003,2000000000000033,2000000000000004,1999999999999985]
private def pvon_7_p1 : List ℕ := [1999999999999982,1999999999999972,2000000000000001,
  2000000000000005,2000000000000006,2000000000000013,1999999999999995,1999999999999988,
  1999999999999995,2000000000000016,1999999999999996,1999999999999973,1999999999999987,
  2000000000000013,2000000000000025,2000000000000011,1999999999999987,1999999999999999,
  1999999999999988,1999999999999998,2000000000000001,2000000000000012,2000000000000015,
  2000000000000014,1999999999999968,1999999999999976,2000000000000014,2000000000000028,
  2000000000000020,2000000000000017,1999999999999999,1999999999999991,1999999999999979,
  1999999999999988,2000000000000035,2000000000000043,1999999999999895,1999999999999790,
  2000000000000377,2000000000001147,1999999999998988,1999999999994871,2000000000001370,
  2000000000020240,2000000000005072,1999999999928423,1999999999945037,2000000000222119]
private def pvon_7_p2 : List ℕ := [2000000000304651,1999999999418199,1999999998692779,
  2000000001151566,2000000004703020,1999999999082429,1999999985530428,1999999994566753,
  2000000037766244,2000000036367878,1999999919705288,1999999859106989,2000000121802812,
  2000000417533629,1999999953219296,1999999005154733,1999999518384085,2000001876543025,
  2000002124215771,1999997458238922,1999994340526992,2000001411243322,2000011037992249,
  2000004094766852,1999984241120265,1999984374928487,2000014282153900,2000029947196234,
  1999998274876897,1999963020538762,1999982148958376,2000027048105100,2000027949474193,
  1999993667899469,1999985244808291,1999999189833517,1999991809464942,1999982530763120,
  2000008887484091,2000032165289392,2000009776444428,1999986003222899,1999995824502722,
  1999997642519816,1999975097858933,1999985647399682,2000014497717228,2000019101664675]
private def pvon_7_p3 : List ℕ := [1999996356552540,2000024811417855,2000013003814545,
  2000010281486114,1999965015399159,2000026526811247,1999955998247826,2000003262390216,
  1999945442691453,2000032418150435,1999942124488015,2000003220212133,1999993719821244,
  1999986728547385,1999999856302037,1999977732329076,2000032442991952,1999965667226106,
  2000007067009227,2000013235757033,1999988052824711,1999991025602048,2000020213913028,
  1999991138166943,1999984826726481,2000031397997752,1999968493987643,2000017315910741,
  2000009572657246,1999955273190654,2000066048421612,1999959499617641,1999963698076336,
  2000109144770843,1999903237320439,1999980684930667,2000143809307718,1999859406665250,
  1999985310549333,2000173202859607,1999844884069333,1999966135112028,2000184682113663,
  1999871222153813,1999945693617038,2000152207917199,1999906927520602,1999980536785647]
private def pvon_7_p4 : List ℕ := [2000103526343664,1999855997583004,2000060503082465,
  2000184734897306,1999689817901804,1999974340013035,2000506130824308,1999694054932096,
  1999456873950900,2000716040330192,2000394597923330,1998898054472116,1999887566261482,
  2001393906708731,1999801494211966,1998434562582824,2000412335358549,2001616026627276,
  1999585913501924,1998458204200705,2000134595222735,2001318606069626,2000414205635536,
  1999078991077743,1998872977188997,2000370217209541,2001844030599328,2000246779461864,
  1997591769657298,1999177471987348,2002648529029200,2001219135609767,1997626966086697,
  1998859274500741,2001661532375611,2000364480464761,1998994833108057,2000715632378937,
  2000600023913399,1998345235081158,1999367187708365,2001689065991925,2000613162565163,
  1999325751352459,2000086938000214,1999326977661116,1998458266806553,2001154182444224]
private def pvon_7_p5 : List ℕ := [2002697699986521,1999616465717883,1997860762912780,
  1999562674052318,1999909722164919,1999784686494015,2001885133958629,2001799364845495,
  1998513665139321,1998135352194639,2000192105140329,1999772094814204,1999558070792666,
  2001759996924186,2001424282474418,1998820543794842,1999359553124278,2000634942981895,
  1999050333156050,1999021658899625,2001373410135994,2000724644320721,1998882873062970,
  2000218596195123,2000653974246521,1998268318687900,1998460656488586,2000345138854553,
  1998993185607162,1997950085675450,2000172402616650,2000387695253006,1998399778661926,
  1999584808469630,2001228828198359,1999362157844876,1998837967247302,2001097131707253,
  2000508641991110,1998574698297316,2000188815423144,2001327834888576,1999130294793961,
  1999089489828638,2001327601870089,2000268079271528,1998528223478890,2000434077148190]
private def pvon_7_p6 : List ℕ := [2001281796736808,1998962502658272,1999182247721583,
  2001420365368645,2000191727839320,1998478716022779,2000464474898370,2001342509531947,
  1998969164587623,1999061751332064,2001421317804616,2000393852261096,1998406182731082,
  2000196958215807,2001548550231416,1999248801512469,1998681754691660,2001208888719209,
  2000954461610418,1998462144292971,1999486043421567,2001732372322567,2000047805541715,
  1998192031422695,2000405451343410,2001794960196232,1999177484208916,1998267098892019,
  2001194363231247,2001667565637179,1998478069482854,1998348661290020,2001807799042028,
  2001746797381509,1997958702015625,1997969156275945,2002171953583021,2002590830295538,
  1997934831333360,1996508428208567,2001442723955020,2004667254108643,2000167062801689,
  1994281172884237,1996794735067081,2005193175082459,2008467174640143,1997243001147636]
private def pvon_7_p7 : List ℕ := [1990010086807191,1988053107483808,2015305036125605,
  2020225899120236,1998937312582467,1991069518681683,1944503262681829,1987873604278788,
  2085236564520884,2086361192636936,1912214164887659,1974843165844257,1999068407604461,
  1997716946490966,2073141885401472,2224598277033111,2379935938040915,2471451969881416,
  2475007076092687,2407982598489754,2306917735160429,2205598799047540,2123967155760592,
  2067771396123367,2033762656618341,2015381739801567,2006423796465032,2002462946395896,
  2000867649037682,2000280892907232,2000083538030007,2000022802535130,2000005704488089,
  2000001305346460,2000000272517460,2000000051739091,2000000008897406,2000000001379089,
  2000000000191492,2000000000023627,2000000000002555,2000000000000231,2000000000000013,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvon_7_p8 : List ℕ := [2000000000000000]
private def pvon_7 : List ℕ := pCat pvon_7_p0 (pCat pvon_7_p1 (pCat pvon_7_p2 (pCat pvon_7_p3
  (pCat pvon_7_p4 (pCat pvon_7_p5 (pCat pvon_7_p6 (pCat pvon_7_p7 pvon_7_p8)))))))
private def pvo_7 : List ℤ := bDec bZ pvon_7
private def pwalks : List RkmSegWalk := [
  ⟨uOfNatHb phbn_0, pvi_0, pvo_0⟩,
  ⟨uOfNatHb phbn_1, pvi_1, pvo_1⟩,
  ⟨uOfNatHb phbn_2, pvi_2, pvo_2⟩,
  ⟨uOfNatHb phbn_3, pvi_3, pvo_3⟩,
  ⟨uOfNatHb phbn_4, pvi_4, pvo_4⟩,
  ⟨uOfNatHb phbn_5, pvi_5, pvo_5⟩,
  ⟨uOfNatHb phbn_6, pvi_6, pvo_6⟩,
  ⟨uOfNatHb phbn_7, pvi_7, pvo_7⟩]
private abbrev dP_0 : Prop := rkmAllTrueF [
    bSlChkZN 49 129 phbn_0 pvi_0 pvon_0,
    bSlChkZN 4 385 phbn_7 pvi_7 pvon_7
  ] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [
    bSlChkZN 15 257 phbn_1 pvi_1 pvm_1_1,
    bSlChkZN 5 385 phbn_6 pvi_6 pvon_6
  ] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := bSlideChk 25 257 phbn_1 pvm_1_1 pvon_1 = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := bSlChkZN 25 385 phbn_2 pvi_2 pvm_2_1 = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := bSlideChk 21 385 phbn_2 pvm_2_1 pvm_2_2 = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := bSlideChk 19 385 phbn_2 pvm_2_2 pvm_2_3 = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := bSlideChk 17 385 phbn_2 pvm_2_3 pvm_2_4 = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := bSlideChk 16 385 phbn_2 pvm_2_4 pvm_2_5 = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := bSlideChk 15 385 phbn_2 pvm_2_5 pvm_2_6 = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := bSlideChk 15 385 phbn_2 pvm_2_6 pvm_2_7 = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := bSlideChk 14 385 phbn_2 pvm_2_7 pvm_2_8 = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := bSlideChk 14 385 phbn_2 pvm_2_8 pvm_2_9 = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := bSlideChk 13 385 phbn_2 pvm_2_9 pvm_2_10 = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := bSlideChk 13 385 phbn_2 pvm_2_10 pvm_2_11 = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := bSlideChk 13 385 phbn_2 pvm_2_11 pvm_2_12 = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := bSlideChk 13 385 phbn_2 pvm_2_12 pvm_2_13 = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := bSlideChk 13 385 phbn_2 pvm_2_13 pvm_2_14 = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := bSlideChk 13 385 phbn_2 pvm_2_14 pvon_2 = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := bSlChkZN 10 385 phbn_3 pvi_3 pvm_3_1 = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := bSlideChk 10 385 phbn_3 pvm_3_1 pvon_3 = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := bSlChkZN 11 385 phbn_4 pvi_4 pvon_4 = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := bSlChkZN 9 385 phbn_5 pvi_5 pvon_5 = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := rkmAllTrueF [
    bNatEq (Nat.add (highdNatMin (Nat.mul 1 128) 384) 1) 129,
    bNatEq (Nat.add (highdNatMin (Nat.mul 2 128) 384) 1) 257,
    bNatEq (Nat.add (highdNatMin (Nat.mul 3 128) 384) 1) 385,
    rkmCheckRowFromWalks 128 64 384 [1,2,3,3,3,3,3,3]
      [15515711,6940628,30108311,2464979,1292070,1142242,521425,459510] [49,40,234,20,11,9,5,4]
      rkmMasksHiHiB_m128_r384 pwalks rkmRowHiHiB_m128_r384
  ] = true
private theorem bk_22 : dP_22 := by decide +kernel
private theorem pw_s1_1 : pWOk 40 257 phbn_1 pvi_1 pvon_1 := pChnN 40 (bSlSndZN (rkmHd bk_1)) bk_2
  rfl
private theorem pw_s2_1 : pWOk 46 385 phbn_2 pvi_2 pvm_2_2 := pChnN 46 (bSlSndZN bk_3) bk_4 rfl
private theorem pw_s2_2 : pWOk 65 385 phbn_2 pvi_2 pvm_2_3 := pChnN 65 pw_s2_1 bk_5 rfl
private theorem pw_s2_3 : pWOk 82 385 phbn_2 pvi_2 pvm_2_4 := pChnN 82 pw_s2_2 bk_6 rfl
private theorem pw_s2_4 : pWOk 98 385 phbn_2 pvi_2 pvm_2_5 := pChnN 98 pw_s2_3 bk_7 rfl
private theorem pw_s2_5 : pWOk 113 385 phbn_2 pvi_2 pvm_2_6 := pChnN 113 pw_s2_4 bk_8 rfl
private theorem pw_s2_6 : pWOk 128 385 phbn_2 pvi_2 pvm_2_7 := pChnN 128 pw_s2_5 bk_9 rfl
private theorem pw_s2_7 : pWOk 142 385 phbn_2 pvi_2 pvm_2_8 := pChnN 142 pw_s2_6 bk_10 rfl
private theorem pw_s2_8 : pWOk 156 385 phbn_2 pvi_2 pvm_2_9 := pChnN 156 pw_s2_7 bk_11 rfl
private theorem pw_s2_9 : pWOk 169 385 phbn_2 pvi_2 pvm_2_10 := pChnN 169 pw_s2_8 bk_12 rfl
private theorem pw_s2_10 : pWOk 182 385 phbn_2 pvi_2 pvm_2_11 := pChnN 182 pw_s2_9 bk_13 rfl
private theorem pw_s2_11 : pWOk 195 385 phbn_2 pvi_2 pvm_2_12 := pChnN 195 pw_s2_10 bk_14 rfl
private theorem pw_s2_12 : pWOk 208 385 phbn_2 pvi_2 pvm_2_13 := pChnN 208 pw_s2_11 bk_15 rfl
private theorem pw_s2_13 : pWOk 221 385 phbn_2 pvi_2 pvm_2_14 := pChnN 221 pw_s2_12 bk_16 rfl
private theorem pw_s2_14 : pWOk 234 385 phbn_2 pvi_2 pvon_2 := pChnN 234 pw_s2_13 bk_17 rfl
private theorem pw_s3_1 : pWOk 20 385 phbn_3 pvi_3 pvon_3 := pChnN 20 (bSlSndZN bk_18) bk_19 rfl
private theorem pwalks_snd : RkmSegWalksSound 128 384 [1,2,3,3,3,3,3,3] [49,40,234,20,11,9,5,4]
  pwalks := by
  dsimp only [RkmSegWalksSound, pwalks]
  rw [bNatEq_true (rkmHd bk_22), bNatEq_true (rkmHd (rkmTl bk_22)), bNatEq_true (rkmHd (rkmTl
    (rkmTl bk_22)))]
  exact ⟨(bSlSndZN (rkmHd bk_0)), ⟨pw_s1_1, ⟨pw_s2_14, ⟨pw_s3_1, ⟨(bSlSndZN bk_20), ⟨(bSlSndZN
    bk_21), ⟨(bSlSndZN (rkmHd (rkmTl bk_1))), ⟨(bSlSndZN (rkmHd (rkmTl bk_0))), trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 384)` (`FindAllJohnsonRampKickMuxHi128T4`). -/
theorem rkmTrajHiHiB_m128_r384 : rkmLo12EqHi 128 64 384 [1, 2, 3, 3, 3, 3, 3, 3]
    [15515711, 6940628, 30108311, 2464979, 1292070, 1142242, 521425, 459510]
    [49, 40, 234, 20, 11, 9, 5, 4] rkmMasksHiHiB_m128_r384 rkmRowHiHiB_m128_r384 :=
  rkmCheckRowFromWalks_sound pwalks_snd (rkmHd (rkmTl (rkmTl (rkmTl bk_22))))
end
end QuantumComputation.Specs.DickeSol
