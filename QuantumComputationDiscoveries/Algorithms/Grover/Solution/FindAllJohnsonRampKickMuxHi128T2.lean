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

/-
# High-`m` Coupled Walk & Trajectory Part `2` (`FindAllJohnsonRampKickMuxHi128T2`)

Certifies `(m = 128, r in {128,192})` coupled `T_16` walks (`42657` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi128T2`). -/
def rkmWordBitsHi128T2 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi128T2 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi128T2`). -/
def rkmUnpackMaskHi128T2 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi128T2 n w ++ rkmUnpackMaskHi128T2 ns ws
/-- Mask segment `0` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s0 : List Bool := rkmUnpackMaskHi128T2 [3] [7]
/-- Mask segment `1` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s1 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 6]
    [1124796067274783, 15, 32]
/-- Mask segment `2` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s2 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 25]
    [2199330101436, 528289148496280, 32505856]
/-- Mask segment `3` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s3 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 24]
    [9380747748360, 422212465070342, 14730854]
/-- Mask segment `4` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s4 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 25]
    [301061672011776, 290273221427396, 27176352]
/-- Mask segment `5` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s5 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 27]
    [575044715546881, 9, 103094272]
/-- Mask segment `6` for `(m = 128, r = 128)`. -/
def rkmMkHiHiB_m128_r128_s6 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 25]
    [4675073998918, 274878955524, 22740992]
/-- Prefix-kick masks for `(m = 128, r = 128)`. -/
def rkmMasksHiHiB_m128_r128 : List (List Bool) :=
  [rkmMkHiHiB_m128_r128_s0, rkmMkHiHiB_m128_r128_s1, rkmMkHiHiB_m128_r128_s2,
   rkmMkHiHiB_m128_r128_s3, rkmMkHiHiB_m128_r128_s4, rkmMkHiHiB_m128_r128_s5,
   rkmMkHiHiB_m128_r128_s6, []]
/-- Part `0` of `rkmRowHiHiB_m128_r128`. -/
def rkmRowHiHiB_m128_r128_p0 : List ℕ :=
  [547, 20425, 3, 7938, 19021, 4481, 17735, 25865, 37784, 35785, 1887, 9077, 140278, 19461, 68,
   45672, 8007, 2740, 64252, 1092, 23267, 66825, 248, 67934, 36679, 5145, 224419, 26971, 3159,
   295685, 240847, 15189, 17286, 302, 5759, 10966, 8276, 39024, 12157, 15400, 11065, 219, 14511,
   259280, 0, 39739, 7436, 46294, 2044, 57604, 80251, 17860, 11547, 61338, 122873, 673, 8411, 4882,
   1900, 7895, 98742, 31212, 20641, 38252]
/-- Part `1` of `rkmRowHiHiB_m128_r128`. -/
def rkmRowHiHiB_m128_r128_p1 : List ℕ :=
  [12605, 51674, 30085, 16783, 367118, 229544, 10483, 49852, 14, 209312, 919208, 368061, 255870,
   64680, 1213, 86747, 584114, 785800, 435037, 9741, 7250, 10004, 318066, 288279, 15516, 2789,
   54830, 3498, 136580, 234898, 119764, 215124, 564045, 145132, 139321, 77899, 30896, 525936,
   288279, 1454663, 6083072, 3034863, 21618, 1604085, 1737, 4884242, 29196673, 119824272, 28695484,
   36626, 29227612, 333571471, 1076468908, 1629774, 2150293152, 108034892, 1827289438, 1917454505,
   938557213, 232978196, 4659404950, 1480683278, 4745460696, 980293899721]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 128)`. -/
def rkmRowHiHiB_m128_r128 : List ℕ := rkmRowHiHiB_m128_r128_p0 ++ rkmRowHiHiB_m128_r128_p1
/-- Mask segment `0` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s0 : List Bool := rkmUnpackMaskHi128T2 [43] [8796093022207]
/-- Mask segment `1` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s1 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 37]
    [1125899906842623, 137438953471]
/-- Mask segment `2` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s2 : List Bool := rkmUnpackMaskHi128T2 [50, 12] [1125899906842623, 4095]
/-- Mask segment `3` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s3 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 44]
    [1125899906842623, 1125899906842623, 17592186044415]
/-- Mask segment `4` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s4 : List Bool := rkmUnpackMaskHi128T2 [47] [140737488355327]
/-- Mask segment `5` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s5 : List Bool :=
  rkmUnpackMaskHi128T2 [50, 50, 44]
    [1125899906842623, 1125899906842623, 17592186044415]
/-- Mask segment `6` for `(m = 128, r = 192)`. -/
def rkmMkHiHiB_m128_r192_s6 : List Bool := rkmUnpackMaskHi128T2 [22] [4194303]
/-- Prefix-kick masks for `(m = 128, r = 192)`. -/
def rkmMasksHiHiB_m128_r192 : List (List Bool) :=
  [rkmMkHiHiB_m128_r192_s0, rkmMkHiHiB_m128_r192_s1, rkmMkHiHiB_m128_r192_s2,
   rkmMkHiHiB_m128_r192_s3, rkmMkHiHiB_m128_r192_s4, rkmMkHiHiB_m128_r192_s5,
   rkmMkHiHiB_m128_r192_s6, []]
/-- Part `0` of `rkmRowHiHiB_m128_r192`. -/
def rkmRowHiHiB_m128_r192_p0 : List ℕ :=
  [149544, 8590, 136113, 11345, 77375, 47363, 32973, 103536, 410, 57248, 5371, 47362, 20098, 39636,
   69055, 6797, 114431, 19281, 32618, 15261, 9196, 13361, 79930, 139345, 8812, 11515, 33906, 512,
   21895, 1828, 7733, 2948, 2011, 2790, 225, 1179, 2619, 602, 10280, 2358, 3424, 4526, 83, 251,
   2494, 6502, 2820, 39250, 1130, 95989, 334, 135179, 85, 98848, 5230, 44925, 69500, 71601, 54287,
   18178, 83128, 4150, 71517, 612]
/-- Part `1` of `rkmRowHiHiB_m128_r192`. -/
def rkmRowHiHiB_m128_r192_p1 : List ℕ :=
  [48938, 9532, 20769, 23112, 2404, 32998, 2863, 35013, 22655, 29348, 52717, 19240, 78682, 8753,
   88041, 1497, 76774, 611, 51542, 9244, 25168, 29726, 7807, 59952, 988, 88990, 30, 99617, 959,
   82996, 4253, 51506, 15991, 27021, 44082, 18004, 78795, 19384, 89362, 19131, 71740, 7283, 61401,
   6, 83695, 2049, 120440, 157, 108475, 0, 72703, 5507, 90986, 10046, 138377, 327, 97645, 537,
   102402, 12339, 106293, 54330, 361408, 222246]
/-- Part `2` of `rkmRowHiHiB_m128_r192`. -/
def rkmRowHiHiB_m128_r192_p2 : List ℕ :=
  [123158, 1187409, 1768957, 312644, 38907, 143189, 636018, 887936, 125701, 2589740, 215299,
   2696615, 2509798, 6016, 330221, 4052, 403230, 36237, 5703079, 13381274, 1652997, 7450440,
   21675509, 6209587, 9203776, 77922837, 91585012, 3314862, 1031831303, 7124328594, 24121551130,
   55196539831, 95864558392, 134034304535, 156239899824, 155262799478, 133439550720, 100084219303,
   65861556419, 38134301410, 19450417139, 8740137433, 3458018908, 1203330043, 367737535, 98502755,
   23070522, 4710081, 834954, 127873, 16809, 1879, 175, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 192)`. -/
def rkmRowHiHiB_m128_r192 : List ℕ :=
  rkmRowHiHiB_m128_r192_p0 ++ (rkmRowHiHiB_m128_r192_p1 ++ rkmRowHiHiB_m128_r192_p2)
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T2`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi128T2 : (0 : ℕ) = 0 := rfl
end
public section
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
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs =>
    match uToNatHb xs with
    | some ns => some (uConsNat n ns)
    | none => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
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
    rcases takeH4_spec k r with heq | ⟨t, happ, hlen⟩
    · exact Or.inl (congrArg (hbz4C b1 z1 b2 z2 b3 z3 b4 z4) heq)
    · refine Or.inr ⟨t, ?_, ?_⟩
      · rw [hbz4C_app, hbz4C_app, happ, List.append_assoc]
      · rw [hbz4C_app, List.length_append, hbz4P_len]; omega
private theorem bSlZ_takeH4 (z d k : ℕ) (hbz : HbZ4) (rem p0 q0 : ℕ)
    (vs cs : List ℕ) (h : rem ≤ 4 * k) :
    bSlZ z d rem p0 q0 (takeH4 k hbz) vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs := by
  rcases takeH4_spec k hbz with heq | ⟨t, happ, hlen⟩
  · rw [heq]
  · rw [happ]; exact (bSlZ_pfx z d rem (takeH4 k hbz) t p0 q0 vs cs (by omega)).symm
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
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns =>
    match bEnc bZ v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns =>
      fH4 (toH4 (mkHbZ bZ bns)) fun h4 =>
        fQ4 (toQ4 vns) fun vs0 =>
          match bIter bZ k mL cL h4 vs0 with
          | none => muxUltraIterFullT16Rkm k mL cL hb v
          | some out => bDec bZ (q4L out)
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only; cases hv : bEnc bZ v with
    | none => rfl
    | some vns =>
      dsimp only; rw [fH4_eq, fQ4_eq]
      cases hi : bIter bZ k mL cL (toH4 (mkHbZ bZ bns)) (toQ4 vns) with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound bns bZ k mL cL (toQ4 vns) out hi,
          q4L_toQ4, ← uToNatHb_sound hb bns hh, bEnc_sound bZ v vns hv]
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
private theorem bCh (c : ℕ) {a b m : ℕ} {hb vi vm vo : List ℤ}
    (h1 : muxFastIterFullT16 a m hb vi = vm) (h2 : bSlideChk b m hb vm vo = true)
    (hc : a + b = c) : muxFastIterFullT16 c m hb vi = vo :=
  Eq.mp (congrArg (fun k => muxFastIterFullT16 k m hb vi = vo) hc)
    ((muxFastIterFullT16_add a b m hb vi).trans
      ((congrArg (muxFastIterFullT16 b m hb) h1).trans (bSlideChk_sound h2)))
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pzeros : ℕ → List ℤ
  | 0 => []
  | k + 1 => Int.ofNat 0 :: pzeros k
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCatZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z
  | ws :: wss => pzig ws ++ pzigCatZ z wss
private def pvi0 : List ℤ := [rkmP 1000000000000000]
private theorem bDm {a b : ℕ} (h : muxNatListEq [a] [b] = true) : a = b :=
  (List.cons.inj (muxNatListEq_eq_true.mp h)).1
private theorem rkmTl4 {a b c d : Bool} {bs : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: bs) = true) : rkmAllTrueF bs = true :=
  rkmTl (rkmTl (rkmTl (rkmTl h)))
private def phbv_g0 : List ℤ := pzigCatZ 0
 [
 [329806250666496,462772593955416,562315539326790,644152833333000,714423283522912,776300112952680,
  831682883218576,881818643600084,927580079999520,969607294541560,1008387056742270,
  1044300287321182,1077652096395338,1108691635243820,1137625697335430,1164628322666064,
  1189847756551034,1213411604623258,1235430726065334,1256002224258024,1275211778919298,
  1293135489313606,1309841348706152,1325390436748480,1339837893332640,1353233721163230,
  1365623452650776,1377048708279938,1387547667392338,1397155467697504,1405904546341804,
  1413824932714186,1420944501130132,1427289189955348,1432883192494894,1437749123999256,
  1441908168365092,1445380207489430,1448183935737806,1450336961583174,1451855898143402,
  1452756444075616,1453053456063618,1452761013950730,1451892479417532,1450460548976192,
  1448477301945844,1445954243983174,1442902346665920,1439332083562122,1435253463162700,
  1430676059007604,1425609037295314,1420061182230514,1414040919334682,1407556336918240,
  1400615205890314,1393224998062432,1385392903085320,1377125844142888,1368430492514368,
  1359313281103924,1349780417026870,1339837893332640],
 [1329491499936624,1318746833825994,1307609308598276,1296084163385948,1284176471215244,
  1271891146842994,1259232954111304,1246206512856318,1232816305404106,1219066682683864,
  1204961869985978,1190505972390232,1175702979887240,1160556772214376,1145071123425676,
  1129249706213636,1113096095999424,1096613774806718,1079806134933214,1062676482432748,
  1045228040420038,1027463952209132,1009387284295828,991001029193604,972308108131890,
  953311373624896,934013611918620,914417545323162,894525834436926,874341080268890,853865826264694,
  833102560241902,812053716239460,790721676286026,769108772091562,747217286666280,725049455870796,
  702607469901108,679893474711726,656909573380208,633657827415996,610140258016416,586358847272458,
  562315539326790,538012241486374,513450825291876,488633127545918,463560951302156,438236066817020,
  412660212465846,386835095625070,360762393522008,334443754053724,307880796576366,281075112666264,
  254028266854090,226741797333216,199217216643396,171456012330880,143459647585898,115229561858534,
  86767171453864,58073870107234,29151029540498]]
private def pvo_r128_0 : List ℤ := pzigCatZ 58
 [
 [3990589760,22819952204,91461159136,296651390508,825835682848,2037820733318,4548837908738,
  9315079251696,17679640316278,31343828928472,52226473246092,82194362118454,122681144904750,
  174253087177138,236214933815376,306363638916674,380982312493944,455121031217572,523145429250328,
  579466432141526,619315264542194,639412038070260,638398632240420,616960346454412,577630085661360,
  524334451931420,461786715226882,394848327377170,327968532149884,264778352243292,207872464289978,
  158771876472368,118030433797586,85432885303014,60230987307018,41373222854218,27698240815222,
  18077430555364,11504852949214,7141412015624,4324498536888,2555158210614,1473343950550,
  829203921472,455563525676,244354198256,127973608966,65447214128,32686359692,15943197832,
  7595234228,3534124276,1606239306,713073490,309212342,130971212,54185682,21896328,8642104,
  3331250,1254028,460984,165460,57974],
 [19820,6610,2144,672,202,54,10]]
private def pvm_r128_0_1 : List ℤ := pzigCatZ 71
 [
 [2180684537582,8510448580102,23291041512756,51611307393974,98213098560080,165748396252216,
  253175085825330,354954779402306,461481148403920,560730299404296,640679402727634,691776988524244,
  708763170371452,691397099488876,644023890888574,574251985124326,491205433681582,403831345823168,
  319618087421564,243889621081070,179660494582884,127913491137258,88113107788616,58780931949604,
  38008139534008,23839605925614,14514818209094,8584102885108,4934072587610,2757898177616,
  1499781906500,793875624368,409196910282,205463147972,100533267740,47951248632,22301428052,
  10116391966,4476992768,1933361560,814882684,335284536,134691966,52837896,20243414,7575450,
  2769264,988982,345074,117636,39178,12744,4046,1250,372,104,26,4]]
private def phbv_g1 : List ℤ := pzigCatZ 0
 [
 [336646114742784,472370051961410,573977422172270,657511942857000,729239734522118,792399829814544,
  848931185409012,900106713186310,946817197714080,989716016218724,1029300033347374,
  1065958069748502,1100001563229198,1131684832226170,1161218958905644,1188781592685456,
  1214524053346012,1238576592938188,1261052369757290,1282050501014694,1301658443343222,
  1319953874232798,1337006197063472,1352877758219954,1367624841142560,1381298485543836,
  1393945168132656,1405607372562462,1416324069977658,1426131126810032,1435061652921138,
  1443146300480532,1450413521890164,1456889793452466,1462599810218350,1467566656456824,
  1471811955398164,1475356001270798,1478217876143402,1480415553671706,1481965991513644,
  1482885213901378,1483188385632026,1482889878551302,1482003331448178,1480541704148256,
  1478517326484120,1475941942728696,1472826751999680,1469182445076830,1465019238017530,
  1460346902907730,1455174796044040,1449511883807094,1443366766455570,1436747700043660,
  1429662616641662,1422119143019284,1414124617933684,1405686108148938,1396810423300188,
  1387504129703836,1377773563204790,1367624841142560],
 [1357063873509806,1346096373369822,1334727866592938,1322963700966192,1310809054725498,
  1298268944555012,1285348233094338,1272051635990572,1258383728528912,1244348951872632,
  1229951618940580,1215195919947934,1200085927633876,1184625602197798,1168818795963982,
  1152669257793028,1136180637256896,1119356488593084,1102200274452278,1084715369452684,
  1066905063553318,1048772565257534,1030321004657298,1011553436327938,992472842082370,
  973082133593200,953384154890488,933381684742424,913077438925660,892474072391594,871574181334482,
  850380305166828,828894928407202,807120482485246,785059347468336,762713853714120,740086283452812,
  717178872302962,693993810724114,670533245409628,646799280622666,622793979478244,598519365174008,
  573977422172270,549170097335708,524099301018936,498766908118092,473174759080432,447324660875798,
  421218387931758,394857683034090,368244258194190,341379795484924,314265947846318,286904339862472,
  259296568510914,231444203885664,203348789895096,175011844935736,146434862542972,117619312019696,
  88566639043786,59278266255320,29755593824340]]
private def pvi_r128_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s0 pvo_r128_0
private def pvo_r128_1 : List ℤ := pzigCatZ 17
 [
 [28387,193033,917095,3513181,11505907,33260981,86583147,205748739,450713249,916820919,1741351561,
  3101227359,5195213689,8205274747,12236378535,17241939463,22951588133,28825786101,34063884011,
  37685270243,38686593179,36254783361,29992461389,20097719933,7441265497,6496914032,19835455498,
  30609184818,37129156766,38303043484,33841387020,24303447884,10976595774,4376651937,19841104315,
  33667772397,44525098815,51642037769,54832183493,54415233045,51069875455,45657377555,39047133681,
  31954353589,24763246121,17247182163,7990881883,6861930678,36204962296,99008495688,233444000208,
  512278500798,1066992060486,2122617754228,4043544050052,7386919478232,12954701610014,
  21828441077022,35364380376988,55123327963040,82713558983312,119538501819092,166464576098004,
  223454714035254],
 [289241973965134,361134533578462,435038028185746,505748372558164,567511142469708,614775151394650,
  643007676016184,649407056430236,633358366853830,596530096724568,542590943809014,476612688047288,
  404292604447698,331158729442636,261907995393820,199978909334212,147394751925406,104850457918254,
  71972341626976,47662034138810,30442732148726,18749025628130,11130756828896,6367587918290,
  3508881168752,1861787758784,950754049926,467062362626,220609828900,100132273082,43647409606,
  18259654774,7326014108,2816764132,1037003214,365229982,122938224,39507866,12107618,3534028,
  981120,258670,64652,15280,3400,702,130,18]]
private def pvm_r128_1_1 : List ℤ := pzigCatZ 28
 [
 [1518465725,5072396249,11659313117,21189341453,32061781599,41245285747,45147129251,41002706619,
  28181643713,8782186271,12807039338,31228816892,41830346222,42039731606,31975175356,14165059270,
  7401150395,28477018421,45602947845,56720133579,61284435619,59974228705,54165309717,45333679661,
  34466665771,21444903767,4223061061,22508713722,69662533078,157749248356,323372131110,
  629179351884,1178201774418,2133162268852,3740530239258,6357677315342,10479450493462,
  16758013504128,26007402196546,39182682953050,57323879580484,81457881133180,112457887673708,
  150869317680742,196722136893322,249359849123924,307321818155296,368315184531034,429303540403542,
  486721899143748,536803996251548,575983434525166,601310614359282,610818244858140,603772800016978,
  580767486535234,543640461989130,495233819594084,439036910824308,378775655897816,318014091533726,
  259825566594174,206572014314112,159805955808338],
 [120287084605368,88088078327036,62755197790604,43488432455798,29311698112956,19213107086146,
  12245718379786,7588149783730,4570687595792,2675741845470,1522091259556,841165246734,
  451512480456,235343784200,119088478468,58486115142,27869290576,12881160872,5772942308,
  2507844460,1055610166,430362428,169867534,64883994,23972294,8562620,2955246,984952,316808,98268,
  29364,8442,2328,606,146,30,4]]
private def phbv_g2 : List ℤ := pzigCatZ 0
 [
 [293192954316268,412207140543534,501870097630146,576068097652966,640213278183054,697097626098818,
  748389183191352,795180853208684,838235945197048,878113227996294,915236774570882,949937775323768,
  982480967599226,1013082088372900,1041919821954212,1069144230038290,1094882854758164,
  1119245236117136,1142326320951632,1164209079452448,1184966543884230,1204663418556120,
  1223357366618122,1241100049799222,1257937976848574,1273913202125546,1289063905552950,
  1303424877727534,1317027928527242,1329902233495666,1342074629228646,1353569866663800,
  1364410829388304,1374618722696166,1384213238044160,1393212696702776,1401634175721458,
  1409493618786022,1416805934110392,1423585081151896,1429844147651820,1435595418267390,
  1440850435867270,1445620056402118,1449914498128068,1453743385849366,1457115790752630,
  1460040266326168,1462524880790858,1464577246412222,1466204546014720,1467413556977702,
  1468210672956620,1468601923542160,1468592992043108,1468189231555344,1467395679458930,
  1466217070467154,1464657848335534,1462722176324566,1460413946497312,1457736787921460,
  1454694073835114,1451288927825982],
 [1447524229064790,1443402616625430,1438926492916516,1434098026241384,1428919152496226,
  1423391576008686,1417516769511906,1411295973241486,1404730193135016,1397820198105666,
  1390566516352550,1382969430661216,1375028972637288,1366744915804948,1358116767489354,
  1349143759387890,1339824836719154,1330158645820322,1320143520042648,1309777463770770,
  1299058134363630,1287982821782310,1276548425632172,1264751429301998,1252587870830186,
  1240053310065538,1227142791615712,1213850802987244,1200171227213764,1186097289139306,
  1171621494365990,1156735559682638,1141430333554140,1125695704958576,1109520498494948,
  1092892353228148,1075797582162458,1058221008503772,1040145773934200,1021553112912908,
  1002422085439832,982729258642382,962448324782692,941549639565180,919999659559120,
  897760250556854,874787828887960,851032283754780,826435608428856,800930138252742,774436248229766,
  746859293068818,718085461283612,687976032209908,656359213647978,623018185268272,587672941805724,
  549951488351128,509341592974912,465104163652138,416102696228692,360421018744860,294318184982866,
  208126989399562]]
private def pvi_r128_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s1 pvo_r128_1
private def pvo_r128_2 : List ℤ := pzigCatZ 0
 [
 [29890405701,8616293025,17514128060,5895346062,13652059123,5595682260,14327856239,27018673582,
  212488462,58441613561,111196297514,181476714777,299410660388,426871415377,528770067680,
  591482701009,534886907618,286222153687,76048256451,384967625948,492676596463,299990043172,
  107306068006,413353518687,380130075828,62620523129,310060585409,422352099696,99314817747,
  338366034455,394600926996,17331585021,394345823253,336676634202,182837531812,443668779915,
  91549368094,351985423324,321719431487,179411207491,435745325240,8082363582,416165008007,
  161623392932,338966571758,311010160643,279606969291,384763430246,213103862228,419543486861,
  149519884405,453945985056,130268984768,467376642827,141216703949,470970529734,192766264758,
  442775989983,260706017053,381964273840,311661143222,351023382811,453947645655,186545069430],
 [514922672726,3481565287,555305332957,289350900715,400645070348,505303371672,137505810693,
  659327867243,372831418879,353417571776,622452968390,125004008396,545299773367,626842715299,
  22787092663,655825792222,753870774620,186824158350,545835100861,843876346863,486582638147,
  261225483356,904167461334,1063727822520,671231474376,58516589263,786481315847,1228071181607,
  1296045361225,1195989428091,1426382519589,2547877849707,4562226665529,5900233204617,
  2367640051741,13242252944360,50099073585260,116547615764182,216200101744024,344441953029290,
  487184208231790,623019425096994,728488108475194,784662400111134,782532675739956,725158998770648,
  625966606929594,504162689406062,379239891690510,266533726045218,174995558136424,107265051978246,
  61310846965928,32621822808220,16118798745766,7372842114582,3108978078056,1202078940434,
  423136214702,134299362786,37919719610,9337605048,1942658268,322090190],
 [36871898]]
private def pvm_r128_2_1 : List ℤ := pzigCatZ 0
 [
 [8855194845,18736322192,22962840391,16026662238,667129049,12273283297,11433751304,1583924624,
  8310154651,2779564407,12602571330,1859638136,24870201007,25985963522,14482298497,17257791260,
  18558466709,11796347381,50314503942,68443519719,109459901710,200418138203,295462752358,
  414096843951,585023256898,668704522669,574681838156,354287941711,6950639321,372385882196,
  498253538269,388164301574,25120383645,422918236809,483462275990,139533515477,337332659169,
  505477603984,93681939715,405155811389,419707290804,79075952152,478775968285,235379509638,
  349781283760,430735161053,163820860497,490382207466,46921601375,555788190087,113683490240,
  512670175864,190850652815,526494572261,171595012012,510914645610,161308318079,591137764657,
  7813976285,555275672912,132953311570,587669196267,460003279261,344724640784],
 [679750158610,99230784380,606658032909,532854382875,229134530132,800329090232,562809968024,
  233709001111,823850011285,688829872051,46830851768,819947907058,1109178644518,761109102698,
  9413783625,835232421923,1426808496551,1687709307305,1699029357443,1611970588113,1477633921493,
  1011805038179,709441492446,5577061960044,16666904670818,38145225057130,74669100784914,
  130222894955478,206573677143442,301788801708924,409402630079790,518733169220134,616514513665012,
  689536172834946,727564605467526,725659486057122,685174321171618,613179124328508,520570900621922,
  419529048335114,321088875231302,233441443687076,161232028313482,105779761762526,65904676780492,
  38976522721752,21867416214090,11629263221432,5856406499088,2789326018044,1254608315148,
  531959073508,212165008488,79390688686,27784631576,9059764040,2739360906,763504144,194656332,
  44936832,9262482,1670248,255098,31098],
 [2610]]
private def pvi_r128_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s2 pvo_r128_2
private def pvo_r128_3 : List ℤ := pzigCatZ 0
 [
 [293620403038,399542213376,201199902068,257193232559,340235883721,390585227,329916484640,
  283739560564,131235310783,403315798979,180016740213,387727078780,178598266934,7177325530,
  406151970051,274494985968,183082673211,59661831717,177787320003,506591767932,254096956182,
  306505842087,790338308629,319889435202,506698150430,59462190370,201505460015,463402362655,
  485232004564,130897537041,197057181375,91208022906,141270783492,78154291812,414032159633,
  124119205795,1043242437758,511952035665,78149842057,364069674103,104462278604,160526919268,
  498780445513,251542539006,694473683586,119798161399,203717415781,198816263014,485697487283,
  245452300342,550609317297,50087891167,206997094178,301670516942,450868853499,755924841822,
  770632771837,856337755116,298006547221,251375935665,176759543661,214700292580,132090431483,
  702003675289],
 [553783486088,434735545875,155185775674,153816844666,377208598123,475469836426,250816898613,
  32316518173,364076163160,4517429357,91732365795,352654995077,484751068160,130749646986,
  687393531779,712706526310,32996878034,959440560941,708976625962,255080160550,701683140129,
  857098415612,280798981611,768532168377,529210077326,526416752648,1556727083327,1565367398036,
  393252596177,461599883403,532274904591,2916869778984,1329773688869,491451253978,1591945105936,
  260235114901,1052056484301,194224293322,2878971308940,2593899888155,2370475463223,2078002649314,
  1374956882568,1182507998031,4140475623879,1170236126594,5162451512108,1242881543233,
  6129313549807,4496126924009,7304346424122,14458453766630,8105942927909,33764665880863,
  10259827708463,57208750985236,73304380330802,57429325626303,232832331754339,158214319336823,
  313802459292936,936320162526866,1257025098630326,1044999767654502],
 [509673328475000]]
private def pvm_r128_3_1 : List ℤ := pzigCatZ 0
 [
 [291628773892,414773491815,183233318716,291907433240,357621874335,199998156485,410721040038,
  116256653606,374111770781,191065508659,310635243400,167552059358,193509387037,48819407777,
  3843185835,217127575555,120798710634,459582062744,157183829091,619890220587,7410760057,
  675134591218,92921513809,328607113169,137152958693,603366750882,289306977009,100177952025,
  15377590159,35981498150,413094646901,106173775618,403234768270,536898045084,539527128019,
  87236815835,204425610588,350226223581,351759555123,236854743555,741501870552,162178158819,
  189721434929,417791438494,58797221610,28850315931,281255458011,205090784229,562301351862,
  858212321541,135699920988,165802003763,72876313945,219058671998,185566576371,172705601613,
  426674259454,29091040115,99329885621,177254233390,386383692859,640748565112,111179617565,
  358764866239],
 [151379046294,368561684658,762261352481,753335421342,406632846557,413792186388,636453133491,
  405196990812,266593580495,341220643682,194245670730,705111747093,661022050146,380677403455,
  394478658249,260408006164,255488328192,224210046742,515744208353,471756248552,616184672080,
  395839030817,1074165442504,1024839564392,483968060303,636608655848,359612168038,1295446609085,
  334777247622,1136964798404,1280015562521,914831452497,895658884552,439221041981,2013235969217,
  1261476516824,1200475221112,1005858956757,3658927617529,2376430421764,1774637151416,
  181518731736,5388453978115,1548801921319,4439420234106,3863937087226,1266823406085,
  11969399613829,9711601204765,8412846327528,25607864020040,19953126250828,31370029210505,
  97373762401681,90200730101385,64307912858912,371159910852100,734869075383402,994324328124090,
  1036968402929850,871352292814420,594686509271160,321491208179782,129052313626834],
 [32958784098134]]
private def phbv_g3 : List ℤ := pzigCatZ 0
 [
 [291114137605326,409284481320258,498311703984196,571983620279236,635673994268956,692155016895700,
  743082903086718,789542807609234,832292627443546,871887169608514,908747500277492,943202461624622,
  975514913935378,1005899064552364,1034532330865304,1061563710591650,1087119841556484,
  1111309487095098,1134226920845370,1155954524717182,1176564813156832,1196122031702550,
  1214683434657130,1232300317454042,1249018859082934,1264880815726474,1279924096601584,
  1294183245630342,1307689847150130,1320472869842100,1332558960023430,1343972693140950,
  1354736790531064,1364872307136554,1374398794796484,1383334444878620,1391696213351544,
  1399499930856060,1406760399902858,1413491480972964,1419706169012072,1425416661575888,
  1430634419691042,1435370222336590,1439634215318486,1443435955198536,1446784448846206,
  1449688189103280,1452155186984782,1454193000783234,1455808762394938,1457009201145810,
  1457800665358568,1458189141872482,1458180273700154,1457779375982580,1456991450383444,
  1455821198045644,1454273031217282,1452351083640222,1450059219781750,1447401042978492,
  1444379902551390,1440998899941078],
 [1437260893904186,1433168504802866,1428724118012010,1423929886461102,1418787732320310,
  1413299347833138,1407466195290654,1401289506134854,1394770279170966,1387909277860354,
  1380707026657058,1373163806341604,1365279648295522,1357054327648770,1348487355219700,
  1339577968153168,1330325119146458,1320727464134578,1310783348285766,1300490790134110,
  1289847463648504,1278850678004936,1267497354791396,1255784002330386,1243706686751670,
  1231260999385916,1218442019975842,1205244275113046,1191661691202084,1177687541124666,
  1163314383620206,1148533994207716,1133337286238922,1117714220381764,1101653700471836,
  1085143453216374,1068169888664136,1050717937628556,1032770861321740,1014310027255574,
  995314643900214,975761444528422,955624307931252,934873799999132,913476615133260,891394889507744,
  868585348472074,844998236527598,820575958229118,795251328679774,768945287445478,741563860295628,
  712994042697912,683098097554820,651705450719414,618600819176452,583506182973322,546052184744538,
  505730224422334,461806450342538,413152416470414,357865537019560,292231390084592,206651313203416]]
private def pvi_r128_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s3 pvo_r128_3
private def pvo_r128_4 : List ℤ := pzigCatZ 0
 [
 [15180364798,359704000070,69635267176,337035472840,445479592000,147633246206,60653045783,
  290025265723,24188289589,543652058176,106464425656,122697421106,402157339289,106292892281,
  28221854396,698072224756,182622837007,113590097662,314947880451,205453628538,438681549068,
  503873269219,38927035929,245506467188,620467749498,298868488248,527369611413,68867219681,
  459006758776,223911417738,177980209676,626743404237,456965225796,204595111552,692296355891,
  344498564312,496780409928,212077664527,121670041627,298544472345,242494125104,763350756930,
  716833607861,333053285334,119074806066,569383412116,300309529425,200843324360,655830251265,
  785634727570,582773277863,375253053086,107825793056,329097473511,247917162286,230118047153,
  247877737369,548817809345,760272275712,556227407547,377276374741,495313046704,181601698899,
  504004102484],
 [22889074829,23597836676,380242173488,285342792435,35366792652,59310150779,47499379395,
  95946378841,227090458539,583394908986,375595998673,508716568725,960257715394,211691340243,
  574266687401,1053414504646,629839900929,239881078197,593164171708,21724494946,793224645583,
  1506794352482,1643990835583,592594784784,199183189804,474394468256,1517975788709,2043421302946,
  1272472152517,429302296641,481281107536,1010458391908,1448177135851,26023027145,72358586360,
  1103665222722,806636412842,700577369863,1380356764671,594108923464,1782184482919,1364110778550,
  4049683546449,971974389643,3767429638221,1038451198357,885304210389,5179059062745,2744614156836,
  10132428100725,3320528904124,3649261125283,14246248718789,3026393719232,15304394882396,
  93456249667909,40590320335214,16503154784865,12090836933059,217943146365470,37729718539328,
  51283791764796,741265639083966,1415185027043986],
 [1176749940127838]]
private def phbv_g4 : List ℤ := pzigCatZ 0
 [
 [281251190472648,395417922881384,481428903195408,552604814928258,614137359014256,668704804565186,
  717907253945704,762793096878962,804094552795172,842347631851106,877959134497948,911246761736814,
  942464468146564,971819203724928,999482374960372,1025597931527606,1050288220762128,
  1073658321097378,1095799312180336,1116790784821730,1136702796678382,1155597416649652,
  1173529959262530,1190549982061168,1206702099491022,1222026653035274,1236560267546552,
  1250336316598840,1263385314452148,1275735248328702,1287411861768436,1298438897602030,
  1308838307366998,1318630432664650,1327834162917734,1336467073170464,1344545544923198,
  1352084872474626,1359099356826360,1365602388866328,1371606523271456,1377123544344256,
  1382164524811770,1386739878461236,1390859407358700,1394532344289646,1397767390970802,
  1400572752506462,1402956168498464,1404924941164370,1406485960771834,1407645728657206,
  1408410378062026,1408785692991448,1408777125272802,1408389809970108,1407628579290676,
  1406497975102686,1405002260167272,1403145428175116,1400931212665356,1398363094893568,
  1395444310705698,1392177856465572],
 [1388566494075144,1384612755118694,1380318944154612,1375687141171130,1370719203215288,
  1365416765197380,1359781239866052,1353813816942048,1347515461391068,1340886910808408,
  1333928671879606,1326641015872344,1319023973104942,1311077326325956,1302800602927216,
  1294193065899108,1285253703421532,1275981216966418,1266374007767708,1256430161491556,
  1246147430912788,1235523216372514,1224554543755324,1213238039681752,1201569903561092,
  1189545876089728,1177161203708698,1164410598448682,1151288192487650,1137787486622086,
  1123901291701312,1109621661889764,1094939818394816,1079846062016980,1064329672529908,
  1048378792460004,1031980292283578,1015119613358112,997780584005854,979945203007402,
  961593383249948,942702646282988,923247755884148,903200275171504,882528026939958,861194430190058,
  839157676416478,816369695836882,792774844339790,768308213252680,742893420709010,716439676325164,
  688837804162438,659954733656262,629625669711880,597642623102720,563736993192310,527551936442892,
  488596084157266,446160447566016,399154812386652,345741052440196,282330590437340,199649966605174]]
private def pvi_r128_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s4 pvo_r128_4
private def pvo_r128_5 : List ℤ := pzigCatZ 0
 [
 [188767323899,168914961208,214282819784,16737608218,123955425850,305412361030,209711594602,
  587798289164,145321209554,83034908879,468220559153,256422956886,842040443,399560931974,
  424542455158,560205376665,115968670075,327909286651,286835978372,169386879366,119447858412,
  202047954771,266088328210,469991553316,634094854692,583097302841,143770221429,292815131708,
  262539710978,683217133894,903649561671,35606075089,362325381164,126045811414,625002195057,
  482097365068,867953813607,441789417580,184799787487,133621883156,291580538653,21220402724,
  455496595521,121143188345,234466805713,768740481570,181664173987,500102248059,707819605328,
  74106645481,103622277771,134581066093,239522108778,219030781862,518329776724,638140734644,
  470001246345,618180881714,225940200820,646702593623,132300467067,96626641077,693789192226,
  433416127520],
 [5870777929,1600267677,6122045543,67139450062,5613075113,169215551940,539286275696,355759108925,
  132463795310,1004333149758,1366160419207,300640971128,363218338604,75444453603,333533938407,
  1198044024808,1577599218279,1425719782080,519266324779,62271269140,378918642443,1398414644794,
  1808676532127,1736295605558,129156427199,295410786413,177491351569,841435160618,1105917459483,
  494921396314,455717409226,340605648305,454157194003,498171835700,240868258466,1607834851968,
  1936716234665,168268581914,80992831533,1286907793406,632407135574,2196431752373,1745519865950,
  1820628645102,6369015432821,704231423562,3512974934787,3925303707290,4889319738713,
  8844409554246,13815775694427,30831332240432,32848328074479,62908437675336,35299072487481,
  46952716708503,82147065894332,62721230080127,106254377248626,44151341477867,34560483044969,
  225484142023921,250383709551083,828276730954448],
 [1779172769800482]]
private def phbv_g5 : List ℤ := pzigCatZ 0
 [
 [250687885785152,352448225808772,429112473071142,492553764825866,547399624706416,596037276816866,
  639892941889518,679901082113612,716714347316448,750810499930732,782552133781834,812222425599236,
  840047732954452,866212516781874,890869556986654,914147160366536,936154378886126,956984872203454,
  976719822425164,995430171302780,1013178363392862,1030019722625340,1046003552549116,
  1061174025336218,1075570907221906,1089230155817988,1102184415988498,1114463434632250,
  1126094410053058,1137102288127802,1147510014869930,1157338752998844,1166608068598938,
  1175336092768672,1183539662234832,1191234442177960,1198435033936042,1205155069790584,
  1211407296666688,1217203650276972,1222555320993324,1227472812529086,1231965994348376,
  1236044148581880,1239716012114264,1242989814412820,1245873311586832,1248373817099558,
  1250498229497520,1252253057473102,1253644442534998,1254678179525398,1255359735192198,
  1255694264998108,1255686628325462,1255341402215656,1254662893764542,1253655151279718,
  1252321974292034,1250666922501536,1248693323727138,1246404280919622,1243802678288570,
  1240891186585746],
 [1237672267579788,1234148177750076,1230320971220788,1226192501949774,1221764425180504,
  1217038198159092,1212015080112106,1206696131474446,1201082212349892,1195173980179944,
  1188971886589094,1182476173366618,1175686867536174,1168603775454832,1161226475872304,
  1153554311869132,1145586381578758,1137321527582950,1128758324852064,1119895067081130,
  1110729751248840,1101260060198808,1091483343009978,1081396592884884,1070996422239470,
  1060279034624670,1049240193046350,1037875184173878,1026178777835982,1014145181091528,
  1001767986028142,989040110276804,975953729028100,962500197085508,948669959179684,
  934452446377634,919835955928768,904807511264678,889352698068762,873455471297344,857097926685444,
  840260028494820,822919282899856,805050343228078,786624528941272,767609234263094,747967193979522,
  727655562006652,706624741026730,684816875932164,662163885202654,638584844560932,613982442115782,
  588238067956836,561204835118666,532697356370064,502476219655332,470223359291318,435500803159092,
  397676607637892,355779031015016,308169694569860,251649988361892,177954190847040]]
private def pvi_r128_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s5 pvo_r128_5
private def pvo_r128_6 : List ℤ := pzigCatZ 0
 [
 [151027476140,128630408412,247026114102,91271705976,9161211803,277723731880,23877941833,
  605063433066,239102766134,214110753726,152318949667,341889574219,334345817893,358255391155,
  687298172924,105426944510,76162691044,418529299849,226229645551,95191887505,354258242976,
  20477441554,60374012500,396366574845,757349590850,459402239652,93959028752,64604505900,
  975968246887,462893340144,459495457408,164894020719,728023694399,791905517098,567836694811,
  472095346852,296506025455,252046105173,57970815187,106361594313,224001239267,575219531052,
  178298002631,271894720400,422798070445,467743874689,843043750354,133804532023,152598086117,
  49459471469,484861612410,62402803811,180474351372,281303818768,678339762653,582156425116,
  471416957298,269383755883,584384215254,279891786704,163479650872,413066472281,470652442009,
  225866007120],
 [467016560246,359813107158,106964128936,19710440533,250380184980,344216410929,38084389368,
  1007653328458,1062078899491,815813375946,502386848176,331320175467,652879006659,1177823966742,
  1499328109679,1459903740784,612216662707,144989827166,249635542007,1240827889814,1812414391133,
  1628497550238,574128780283,271213336695,381370401224,923630754220,987207967411,715709998322,
  79874052996,568411781339,58966980294,707893657944,568821246417,435038494180,1414778097833,
  1930105519658,230517405106,195544353135,691562013873,783622093191,2440051389200,143881000801,
  3066531965837,5278109765026,2553956931303,1834566147671,165266870463,4071004587767,
  9222749299183,19046395387500,15167101115271,6035105607664,10621855699064,37212559839076,
  94138208248686,38966779685675,31080482315250,32160344755178,132617432539850,38929375178656,
  101792570935479,141514698140456,132460470670600,547194948367458],
 [1902324764427580]]
private def phbv_g6 : List ℤ := pzigCatZ 0
 [
 [211715629542940,297656178218150,362402104499162,415980732683772,462300185720230,503376566829766,
  540414374663202,574202798734262,605293027101458,634088548644576,660895587893640,685953298565098,
  709452848395696,731550021789330,752373847293584,772032684968918,790618633423392,808210791865972,
  824877721730182,840679336072996,855668371741122,869891551936268,883390515415182,896202567288076,
  908361291680908,919897056189614,930837430666318,941207537519264,951030346769512,960326926176318,
  969116654536822,977417404587262,985245700643770,992616855121274,999545087287688,
  1006043626994748,1012124805637942,1017800136207026,1023080383973982,1027975629110424,
  1032495322318854,1036648334392036,1040443000474692,1043887159685718,1046988190662622,
  1049753043509288,1052188268560428,1054300042319038,1056094190874858,1057576211070714,
  1058751289648578,1059624320577132,1060199920736722,1060482444115294,1060475994649448,
  1060184437827932,1059611411160020,1058760333598280,1057634413993686,1056236658650806,
  1054569878041612,1052636692728224,1050439538537352,1047980671022306],
 [1045262169242056,1042285938880838,1039053714726084,1035567062517008,1031827380170832,
  1027835898388348,1023593680635164,1019101622489626,1014360450342692,1009370719429176,
  1004132811163450,998646929745928,992913097999134,986931152384108,980700737138674,
  974221297468900,967492071713544,960512082388082,953280125999784,945794761508006,938054297283676,
  930056776398472,921799960046880,913281308871982,904497961927826,895446712966128,886123983681228,
  876525793482846,866647725288756,856484886735794,846031866093758,835282682027688,824230726182948,
  812868697356222,801188525752440,789181285498316,776837093167688,764144989545912,751092801184300,
  737666977421992,723852397413712,709632140202468,694987208881262,679896197203428,664334883343548,
  648275730460568,631687266637836,614533306697920,596771963784904,578354377019502,559223048920788,
  539309635802136,518531954002198,496789832857494,473959220636290,449883550641152,424360630117796,
  397121840277030,367797296700262,335853298522428,300469172228276,260261243528258,212528162434512,
  150289206943470]]
private def pvi_r128_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r128_s6 pvo_r128_6
private def pvo_r128_7 : List ℤ := pzigCatZ 0
 [
 [164581362300,46837800894,285849777881,4335488373,178214465113,275852490350,133908821513,
  266365945984,321668406366,388780364274,378357891378,86927525169,190567191330,749085987681,
  279022498349,16629458307,427437327512,178990113860,104729034948,506975653283,66132059731,
  305092686217,517024109446,31612210186,521298989585,383051638380,143489970799,947468999686,
  328474992048,112442499653,1087550384091,981535012312,246511973757,262976645562,34878314877,
  151798848205,209458000170,181967410254,395105839027,220544842462,248217627781,210407773283,
  29684859541,240943792745,1018402708130,1927394822,398709939721,172489596007,430338082340,
  90460976228,480031255775,566587321842,267305235329,214933059596,495346505334,701078105171,
  51932400506,183444293784,139776574842,87226038062,177738435798,628478448768,353355328092,
  287359596259],
 [391179409559,224564894971,454654052046,346919090410,259115699449,1211816748572,958227299545,
  204792194540,446565992026,7861196961,915024023887,1917517362814,1213372458583,1011683224914,
  508660852413,69700578298,589072509731,1528557852200,1772917659387,1319158868728,197414521733,
  170320938215,200067613795,1127959368962,1073844514117,249145732250,105666499628,468331129313,
  118314533494,739148793344,969338200685,692152203500,927641217327,1502070186614,761938235935,
  746527277989,558222832472,351564869202,1450440425948,1073844628443,2412198702791,4932786617044,
  3484181612105,294080018864,2533059949920,83400663469,4420074118699,10806798601136,
  21892864079645,10713642614866,382774409439,10812522897863,36527887495408,65619180490019,
  2553262609635,92742516275472,20787976233531,85493621608166,87577506485295,61271771531811,
  30527255867908,136519677411402,76959304427378,137774617867966],
 [1980195857836090]]
private abbrev pl_r128 : List ℕ := [1, 1, 2, 2, 2, 2, 2, 2]
private abbrev ptau_r128 : List ℕ :=
  [19324585, 23012918, 12552501, 12552501, 2010242, 1942135, 692434, 877181]
private abbrev pnsub_r128 : List ℕ := [30, 35, 31, 31, 5, 5, 2, 3]
private def pwalks_r128 : List RkmSegWalk := [ ⟨phbv_g0, pvi0, pvo_r128_0⟩,
  ⟨phbv_g1, pvi_r128_1, pvo_r128_1⟩, ⟨phbv_g2, pvi_r128_2, pvo_r128_2⟩,
  ⟨phbv_g2, pvi_r128_3, pvo_r128_3⟩, ⟨phbv_g3, pvi_r128_4, pvo_r128_4⟩,
  ⟨phbv_g4, pvi_r128_5, pvo_r128_5⟩, ⟨phbv_g5, pvi_r128_6, pvo_r128_6⟩,
  ⟨phbv_g6, pvi_r128_7, pvo_r128_7⟩]
private def phbv_g7 : List ℤ := pzigCatZ 0
 [
 [308809794590332,433879378366432,527907907983976,605551900631086,672527792891274,731786597973580,
  785092583551394,833602503375580,878124828105612,919251808349430,957433254065500,993020715971042,
  1026295419617144,1057486716716000,1086784719970088,1114349220405360,1140316144981452,
  1164802337791398,1187909169076800,1209725306077586,1230328872614756,1249789154999178,
  1268167965909310,1285520746742876,1301897467429302,1317343367553742,1331899571824104,
  1345603605064614,1358489826149856,1370589795998946,1381932591516696,1392545074909024,
  1402452125910290,1411676842995112,1420240718501730,1428163791690974,1435464783047988,
  1442161212560432,1448269504245430,1453805078823658,1458782436134364,1463215228635594,
  1467116327128266,1470497879672608,1473371364523856,1475747637795824,1477636976461638,
  1479049117217196,1479993291662042,1480478258192126,1480512330947524,1480103406114160,
  1479258985840772,1477986199999624,1476291825991246,1474182306768826,1471663767236344,
  1468742029155716,1465422624681590,1461710808627622,1457611569555046,1453129639762490,
  1448269504245430,1443035408683968],
 [1437431366508794,1431461165086940,1425128371061266,1418436334870278,1411388194467918,
  1403986878256038,1396235107235622,1388135396375900,1379690055193640,1370901187527672,
  1361770690486176,1352300252536154,1342491350695822,1332345246781140,1321862982647150,
  1311045374353052,1299893005166694,1288406217309190,1276585102323160,1264429489928376,
  1251938935205764,1239112703924110,1225949755792760,1212448725387032,1198607900449898,
  1184425197222270,1169898132393076,1155023791187070,1139798791020116,1124219240044826,
  1108280689779516,1091978080854358,1075305680712906,1058257011864918,1040824768984522,
  1023000722769330,1004775607998020,986138992615750,967079123896632,947582746723510,
  927634887708118,907218597138576,886314638428380,864901111624998,842952993285584,820441569151150,
  797333727806774,773591071763452,749168785344600,724014173526904,698064747722884,671245675347910,
  643466315784506,614615410434296,584554230467312,553106516407910,520043166720000,485057894211516,
  447726364031644,407432677003556,363224325400486,313486446226822,255049392487026,179678920813598]]
private def pvo_r192_0 : List ℤ := pzigCatZ 66
 [
 [899994953094,3720850389532,10802921666874,25432391305278,51491648917400,92594359595010,
  150929671021132,226153782821794,314723297604116,409966512208370,502965806418242,584063171751012,
  644603249485994,678464786839800,683015045285288,659309007437178,611571624007146,546174335101322,
  470402219121226,391298502101496,314793025277018,245210032390982,185146153771720,135636730463242,
  96496204794636,66721159444414,44870139531208,29368722424188,18720434268402,11627812198866,
  7041415923672,4159231316628,2397466448954,1349146782238,741482012742,398136665182,208928666718,
  107184503772,53772259258,26387129924,12668948478,5952545192,2737602766,1232618784,543445898,
  234652664,99243706,41119692,16692524,6640032,2588444,988936,370334,135932,48900,17242,5956,2008,
  656,206,58,14,2]]
private def pvm_r192_0_1 : List ℤ := pzigCatZ 72
 [
 [5366484136670,19209435869552,48291878744190,98450593253352,172625102882548,268859501252352,
  379600549382630,492725466773934,594041161584094,670440155536928,712707834973648,717185879684208,
  685962830287156,625761574288974,546037647834770,456908531025906,367428364776110,284497754957784,
  212459510271238,153253805783182,106920606585098,72234503188196,47307299546096,30063158115052,
  18554451302276,11130605329416,6494812373678,3688797889926,2040529704614,1099990004988,
  578163859424,296442636592,148338257024,72471828646,34582494704,16123889174,7347740284,
  3273723956,1426457170,608021682,253588728,103511948,41361132,16181576,6199460,2326278,855088,
  307934,108650,37562,12722,4212,1362,428,126,32,6]]
private def phbv_g8 : List ℤ := pzigCatZ 0
 [
 [311247765068712,437304739654076,532075599286242,610332570424360,677837219385126,737563856835142,
  791290678867744,840183571494322,885057388033300,926509054752272,964991932738654,
  1000860348108258,1034397746612448,1065835290633652,1095364593763134,1123146708534122,
  1149318635013132,1173998139745966,1197287393265084,1219275762814488,1240041988981782,
  1259655905074672,1278179811766128,1295669588148836,1312175598651406,1327743440013382,
  1342414561611204,1356226784517524,1369214738861018,1381410234725792,1392842578571020,
  1403538844672530,1413524109183510,1422821652934838,1431453137940996,1439438761667406,
  1446797392392416,1453546688419290,1459703203428360,1465282479882756,1470299132094066,
  1474766920302828,1478698816921484,1482107065915934,1485003236159160,1487398269471084,
  1489302523958780,1490725813186742,1491677441635520,1492166236846248,1492200578596908,
  1491788425411696,1490937338666798,1489654504522906,1487946753886312,1485820580575590,
  1483282157849190,1480337353430284,1476991743148390,1473250623302512,1469119021837232,
  1464601708411412,1459703203428360,1454427786086686],
 [1448779501502034,1442762166941686,1436379377206192,1429634509184868,1422530725604962,
  1415070977987272,1407258008814356,1399094352910450,1390582338025338,1381724084607092,
  1372521504741056,1362976300224222,1353089959735470,1342863755052456,1332298736255394,
  1321395725846046,1310155311697006,1298577838731134,1286663399213750,1274411821520312,
  1261822657219228,1248895166282728,1235628300207340,1222020682788722,1208070588252034,
  1193775916387470,1179134164278884,1164142394139662,1148797196681072,1133094649330636,
  1117030268487100,1100598954838268,1083794930570702,1066611667056110,1049041801295034,
  1031077039016946,1012708041854094,993924295393356,974713954124232,955063658283970,
  934958316273420,914380844567272,893311854711340,871729273858832,849607881013542,826918735225106,
  803628463672870,779698365729952,755083271912026,729730071182704,703575781623878,676544979867734,
  648546309713440,619467634205838,589169129288064,557473143963202,524148768000000,488887296151186,
  451261043556138,410649248679268,366091884000854,315961337615184,257062939014064,181097437687754]]
private def pvi_r192_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s0 pvo_r192_0
private def pvo_r192_1 : List ℤ := pzigCatZ 14
 [
 [76498429,214019694,361868335,388526964,198946713,120288831,310216010,181277127,137226255,
  283422768,77837301,220921277,217547040,85321220,260872001,52891656,230893158,157993635,
  160572347,220579526,77158230,245732553,1980574,244026564,68423233,226846115,118456206,199570794,
  163392225,197028761,130411030,29292546,508315007,880651085,1491882031,3656029795,8440697117,
  17506173979,35422832715,70950740569,138256600807,261093217313,479946158497,860219900841,
  1502178303929,2555092351849,4235150015411,6843636923149,10782585544249,16566083558251,
  24822928061839,36283164260065,51741841432925,71997161882827,97763342934441,129561060394523,
  167593424829871,211623028667727,260871425102359,313963161928943,368932883680609,423307798867315,
  474268677547307,518879700520289],
 [554362986778623,578382187149729,589294977626565,586337302184535,569711412368947,540563594256313,
  500854379601243,453141253220149,400307461586307,345277111833737,290755257599105,239023535641981,
  191809870043603,150237535889471,114846726470439,85672493640331,62357786735725,44279693935195,
  30670218876449,20718510707805,13647685786703,8764861488801,5487017126349,3347627273073,
  1989869711765,1151954520395,649158786605,355866528383,189620898609,98110312289,49234072749,
  23931238913,11250653741,5107550597,2235240973,941252885,380605649,147448661,54582797,19245677,
  6437391,2031459,600051,163841,40453,8623,1397,77,54,26,4]]
private def pvm_r192_1_1 : List ℤ := pzigCatZ 31
 [
 [137,897,9299,34137,246853,708669,3949157,9995485,44100213,105054315,372549557,861344127,
  2512718745,5662744105,14058561815,30502417845,66904538013,137411970977,274627505355,
  528005465765,979675377645,1759360579067,3056117091279,5143698948837,8395867014847,
  13297988704335,20456211186609,30582936653755,44462654506077,62898256477307,86625191888215,
  116203216734063,151900954860873,193579063553315,240591285322267,291730664737313,345234089385819,
  398851776604547,449988484401583,495908231699259,533976128634363,561907395406269,577994717372245,
  581282091965743,571657358088319,549851631050407,517350350041159,476230329796281,428944896864425,
  378087217729959,326164495857517,275409461533753,227645083683275,184209221857045,145938512964137,
  113203538245805,85981087763605,63946649409153,46571791448791,33214999116093,23198533041215,
  15867197536523,10627812551759,6970816934291],
 [4477398294467,2816409038355,1735112376041,1046958532955,618628014513,357778268601,202335855793,
  111730256093,60123815085,31451179987,15948112789,7814138987,3686429463,1667631321,719736763,
  294367327,112943821,39964195,12605905,3250671,463819,167586,202956,128698,66268,30382,12846,
  5094,1910,674,220,68,16,2]]
private def phbv_g9 : List ℤ := pzigCatZ 0
 [
 [256835386085172,361564709097736,440796917247674,506646936251176,563830363172032,614776915488762,
  660936534365470,703258182074696,742403941734284,778857997903756,812987470715238,845078815805578,
  875360820088300,904019779155130,931209882085808,957060535083442,981681660906592,
  1005167619568724,1027600165588934,1049050716754912,1069582121084234,1089250051582458,
  1108104120563056,1126188779667594,1143544054022530,1160206146522652,1176207939338100,
  1191579413294060,1206348001033894,1220538886351256,1234175259424008,1247278535665368,
  1259868544358524,1271963692040268,1283581104660816,1294736751807724,1305445555694882,
  1315721487148712,1325577650446148,1335026358553596,1344079200067196,1352747098951000,
  1361040368001960,1368968756831866,1376541495041028,1383767331162194,1390654567872434,
  1397211093902700,1403444413017310,1409361670386794,1414969676636024,1420274929814054,
  1425283635501674,1430001725246488,1434434873492804,1438588513154072,1442467849958654,
  1446077875684994,1449423380389424,1452508963718578,1455339045388518,1457917874904132,
  1460249540584580,1462337977954026],
 [1464186977550814,1465800192203034,1467181143813766,1468333229695108,1469259728486378,
  1469963805688590,1470448518844348,1470716822389630,1470771572201558,1470615529864120,
  1470251366671880,1469681667389940,1468908933786900,1467935587956106,1466763975439164,
  1465396368164594,1463834967213344,1462081905422010,1460139249833622,1458009004005128,
  1455693110179912,1453193451333042,1450511853096264,1447650085569248,1444609865022988,
  1441392855500826,1438000670322078,1434434873492804,1430696981027902,1426788462188308,
  1422710740636728,1418465195515020,1414053162446012,1409475934462250,1404734762863896,
  1399830858007690,1394765390028670,1389539489496052,1384154248004440,1378610718701262,
  1372909916751124,1367052819737508,1361040368001960,1354873464920730,1348552977118540,
  1342079734618870,1335454530929918,1328678123065132,1321751231496824,1314674540041200,
  1307448695672686,1300074308265182,1292551950257440,1284882156239390,1277065422455810,
  1269102206223234,1260992925255546,1252737956893074,1244337637229454,1235792260129832,
  1227102076133240,1218267291231170,1209288065513462,1200164511671628],
 [1190896693348618,1181484623322766,1171928261512290,1162227512785136,1152382224557232,
  1142392184160194,1132257115957330,1121976678184278,1111550459487724,1100977975132410,
  1090258662842958,1079391878242818,1068376889847774,1057212873565998,1045898906650154,
  1034433961039836,1022816896024028,1011046450143508,999121232241650,987039711558708,
  974800206749100,962400873682820,949839691870592,937114449326766,924222725653744,911161873095620,
  897928995265596,884520923199866,870934188328210,857164991875680,843209170117418,829062154795616,
  814718927868250,800173969586768,785421198684844,770453903190504,755264660033090,739845241182646,
  724186503502676,708278258777004,692109119431098,675666314228234,658935466568794,641900325794364,
  624542438860338,606840745539696,588771074425704,570305508595270,551411577594386,532051214349028,
  512179388287316,491742283610254,470674824160666,448897235354066,426310144397948,402787383516064,
  378165032115214,352223987113834,324660692673960,295034453274574,262663433217606,226390965491676,
  183944967954084,129417067593902]]
private def pvi_r192_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s1 pvo_r192_1
private def pvo_r192_2 : List ℤ := pzigCatZ 30
 [
 [33016,225200,1045466,3802792,11453510,29367318,65042846,125213088,209353810,301324402,365249272,
  354366170,237047454,30293160,184944371,293321213,219024945,1327044,216530784,258451914,87571870,
  161528081,246851183,134396231,207233606,82616434,495076912,1100143163,1879873860,4608256097,
  9628135404,18472798739,35337007814,64126322117,109798262720,179498821767,277783390992,
  403626276397,548676226792,691085173131,793264272524,809517486547,698635763882,443098667863,
  73728331512,319121426204,603907429557,655582104946,423204023957,12760867013,444719530734,
  630306810945,438240560002,37284604108,491688088637,594289039714,244738953399,303766892741,
  602718503948,375950967749,197771901189,589345263854,401111251589,201459693671],
 [596418979104,339689421083,306556596879,601628868032,172554378491,477742802025,524447035496,
  119593601424,610962801429,260799596954,466244932680,523854158899,201484620585,630461630432,
  78101619607,609496834679,309788297866,514768265702,473377206639,396330370055,575764864346,
  289313059218,635094751643,215181806431,667665192520,184392484332,678608212825,170849353301,
  783169950416,510948725594,108447974931,837869702320,3121895799826,5389310190384,8345187161738,
  14567067433980,25563700533600,41085111549352,61503360203642,89132690167000,126340247538560,
  173215027801646,227837577464162,288218031081436,352927095941572,419710714102784,484224373669442,
  540746124468460,584238144135718,611756477876544,622249196892760,615567560281710,592015177935846,
  552806876653920,500721650524686,440087788513180,375926403075054,312784878869116,253929599600570,
  201194149933630,155322371561456,116442514133106,84395914427222,58852064840734],
 [39295858763570,25006112856888,15092699520636,8591469044750,4577396910362,2254894485398,
  1004135904950,384308191812,107837684612,2340515340,26918194139,27263553875,19742500555,
  12259286733,6904775355,3616946051,1786119371,838313155,375968551,161713735,66886089,26653425,
  10247413,3805161,1365709,474013,159153,51693,16233,4921,1437,397,97,19,1]]
private def pvm_r192_2_1 : List ℤ := pzigCatZ 54
 [
 [358103904,411437474,75525538,290569123,230011631,147531880,280048688,19825641,273095979,
  83128721,232830704,159553436,173504023,210336009,104563846,237351962,32723143,242844577,
  36951233,229220608,100420634,199030497,154323945,155033474,195800660,100298071,222442071,
  38306226,232347040,26966118,224268023,91019645,197834288,148886186,153831923,195302519,94508682,
  225040616,23849705,233422483,52252973,217029674,126043880,174578257,188282069,107860764,
  229147434,22682003,238866963,71681575,218794618,151916102,92927109,286446743,488143234,
  236028123,2990504176,3300911325,16326741618,15346859579,77292509660,58232161139,293122317944,
  140614440531],
 [896999527866,64158999051,2204543987600,1125573451224,4636110539070,5644221606702,9783850822688,
  16222467702940,22761220284444,35607400289652,51021874555656,70538631015874,98499345718386,
  130945395690002,169248170555466,216302482550278,267470779607290,321013196987654,378389201159736,
  434983348287312,485294112676716,528981035090238,564582652111752,586898929186420,593546190156912,
  586685069894188,567678383172138,535647127629536,491627659919936,440196991993340,386145125785610,
  331677071000884,277524528204176,225345625784132,178003129100120,137857725172558,105391459477992,
  79438952599202,58394143789380,41167439323174,27348524718118,16835088808692,9427782456830,
  4670580650644,1924512222496,530353359434,61598466219,238754122111,236403265831,177622404969,
  116176689783,69420166407,38790911733,20541423297,10394576957,5054090465,2369969071,1074442919,
  471709771,200754809,82874201,33194491,12901607,4865477],
 [1780065,631641,217315,72463,23403,7315,2205,637,173,41,5]]
private def pvm_r192_2_2 : List ℤ := pzigCatZ 35
 [
 [757894,4102074,14929014,41924062,95555532,180429298,282952444,362631340,361076698,236801982,
  11534792,211497683,295010807,170579639,80208488,259237674,208751142,32174739,237784133,
  202287569,42172972,238143404,169755006,89477713,242349143,108946829,157233958,220479378,
  32747602,258381697,53948005,187907955,903043736,1468496237,3168678110,7267763549,14390564920,
  27490130571,51367239822,90703807063,151675613548,241263243213,361828388248,507440011301,
  661013236044,789262098809,843951672714,775551893803,554136911334,193647548923,227776723413,
  573334471688,695004534475,510448540356,74124393493,406644829137,655127064036,494355080679,
  590785067,500510783746,625087285675,247048497012,345938834982,637105325007],
 [335348073310,298434778096,636062063301,301892989702,371426873032,628386304917,140802351510,
  527992198020,534490702683,162089139173,650281085980,237340938863,525009654071,523221110536,
  276323426022,658766433207,10782121183,676426704932,209279743911,623104887169,389660496446,
  619933841744,343205474147,233612882719,1149021914090,1794454335260,1934327047020,3993322258500,
  8544260556544,14301675583266,21878459677778,34205651392480,53109650522452,78150217487952,
  109256206066584,148227379955642,196520217039426,252807489259466,313749629690672,376385554400374,
  438634476722844,497658185315834,548859136722856,587164718604546,609218346243362,614228311221198,
  603048012847068,576919656299358,537221450923436,486134049291800,427174574005428,364844238328588,
  303569409264094,246681290660394,196013309014714,152153850074316,114996118253962,84197273776236,
  59374233327588,40088605343988,25767725726338,15675548696256,8964131339816,4773600024770],
 [2330746560490,1012001137480,362033566422,77909461704,24469457973,47066241545,40839983521,
  28190446697,17192036809,9634193929,5057470271,2514572639,1192403271,541801807,236671047,
  99625959,40484143,15901827,6043303,2223655,792563,273715,91603,29703,9321,2827,823,223,55,9]]
private def phbv_g10 : List ℤ := pzigCatZ 0
 [
 [258906134416132,364479842908970,444350864756996,510731802879642,568376274081272,619733585560850,
  666265368706678,708928236847766,748389611180686,785137580027536,819542223445132,851892306633430,
  882418461112052,911308484490382,938717809005440,964776884204410,989596519103674,
  1013271834499088,1035885244059710,1057508741382768,1078205681201164,1098032185386890,
  1117038266255214,1135268733841314,1152763935976264,1169560367442526,1185691175524406,
  1201186582769014,1216074242996790,1230379543047004,1244125860069502,1257334782140358,
  1270026298417364,1282218963840942,1293930042440160,1305175632558174,1315970776719988,
  1326329558392518,1336265187506596,1345790076302546,1354915906810148,1363653691068472,
  1372013825021918,1380006136889014,1387639930684194,1394924025475694,1401866790881336,
  1408476179235370,1414759754801590,1420724720358830,1426377941442968,1431725968493912,
  1436775057125258,1441531186708012,1446000077436982,1450187206028756,1454097820183144,
  1457736951925058,1461109429930904,1464219890932196,1467072790279188,1469672411738608,
  1472022876591902,1474128152093598],
 [1475992059343446,1477618280620644,1479010366223802,1480171740856014,1481105709590796,
  1481815463451172,1482304084631340,1482574551387568,1482629742622632,1482472442185934,
  1482105342909480,1481531050398174,1480752086591254,1479770893110316,1478589834408016,
  1477211200730406,1475637210904770,1473870014963802,1471911696616170,1469764275572604,
  1467429709735924,1464909897262780,1462206678504168,1459321837831272,1456257105352610,
  1453014158527960,1449594623684104,1446000077436982,1442232048024438,1438292016553400,
  1434181418164924,1429901643120274,1425454037810800,1420839905694192,1416060508159282,
  1411117065321370,1406010756749770,1400742722128972,1395314061854610,1389725837565172,
  1383979072610080,1378074752454628,1372013825021918,1365797200971714,1359425753915948,
  1352900320570200,1346221700840376,1339390657843374,1332407917860360,1325274170220836,
  1317990067115494,1310556223335374,1302973215934544,1295241583813094,1287361827216798,
  1279334407149330,1271159744692412,1262838220228698,1254370172561596,1245755897925556,
  1236995648879592,1228089633076014,1219038011895390,1209840898937820],
 [1200498358359374,1191010403041414,1181376992578994,1171598031073056,1161673364709310,
  1151602779104722,1141385996400266,1131022672076086,1120512391462312,1109854665915484,
  1099048928626852,1088094530024540,1076990732726712,1065736705997252,1054331519649132,
  1042774137333152,1031063409141256,1019198063443646,1007176697867424,994997769311016,
  982659582872902,970160279554690,957497822576806,944669982119350,931674318270146,918508161925626,
  905168593346720,891652418019696,877956139408810,864075928111296,850007586832052,835746510481464,
  821287640559288,806625412813718,791753696947908,776665726874272,761354019673270,745810280976034,
  730025293929066,713988788173182,697689284320952,681113908166908,664248167199366,647075679738158,
  629577843960066,611733429838924,593518071084804,574903625693004,555857361414834,536340904258554,
  516308860591014,495706980720610,474469663810342,452516492089094,429747291566176,406034877231246,
  381214006873000,355063810880168,327278285980436,297413183522794,264781170474260,228216254136992,
  185428033590736,130460499267406]]
private def pvi_r192_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s2 pvo_r192_2
private def pvo_r192_3 : List ℤ := pzigCatZ 3
 [
 [18035429657,72347570850,193431836761,393041454828,631376560881,800656119040,761862290655,
  440542554700,73708119044,521411507597,617842556856,278449978511,259884297961,574997839110,
  397795459445,126357227369,528996925728,438343895069,46497284495,423047612768,282735759429,
  244472579055,590614930410,343050091197,284230140625,644496112482,351618654393,282850040529,
  582463735272,255613794241,293361633413,452543322044,106021733839,283890158847,278932788376,
  27214993204,210882520487,97891139522,74383468326,69841446399,18089352367,4681378135,70524787696,
  15371674144,163973787171,77024960676,206556052868,236200479459,142683445179,385151725220,
  28245082431,455727624975,255264373864,409324962168,472558135379,254292275553,619557517584,
  32293853948,660520202775,200111426476,591518088702,388549255601,435106849217,493714141198],
 [228669954512,498008766197,11998168025,405921209556,182330855163,239987313483,333923251652,
  34669835956,434377676221,170338753186,482661608596,337290017331,478254185189,438864185838,
  416042111122,467951476219,288223331425,445112582258,96741680856,414962080229,128215772508,
  421971154212,321686422833,469534145263,414019513340,495466260584,397781846375,414939674263,
  369621018406,231513775320,451323217191,91212411447,612691789704,121723363026,653217315529,
  192416507111,523939401066,72505577772,513456120459,70515330748,695437107600,73814772856,
  640026514167,129662912551,509577521884,44310168379,753327201777,243371805355,546585749804,
  153349971396,655038764221,336212450065,558553838202,411493107888,508426525071,543618926259,
  384369522288,651301477244,215484728081,731269002399,10397266059,745412186822,276048097124,
  660481293929],
 [545944610883,452502696190,767476749948,111648003203,874965824479,385847938261,676835487556,
  894526050288,150184716352,386593880255,237000942281,659386540263,3121462046957,6815697581087,
  7801623216491,257286951285,21782517947090,63494128801008,128660849271480,218259346080124,
  328332310432674,448749927496694,564427228499512,658971170306304,719097012163884,737808290434634,
  715290646740544,657757924688572,575214138557530,479071718342950,380166967328174,287358535001038,
  206735575221732,141417084616234,91873918573104,56621509546870,33064101373898,18271764489634,
  9542354356124,4701893925590,2181406816198,950284721944,387218645052,146755533878,51279824678,
  16275637950,4559992000,1054440260,157598246,14997545,24885757,13075073,5164537,1732109,513523,
  136809,32949,7169,1395,235,31,1]]
private def pvm_r192_3_1 : List ℤ := pzigCatZ 16
 [
 [359,3704,25983,146184,701405,2961762,11225853,38699972,122491907,358403240,974344035,2470151314,
  5855826327,13002677576,27072744163,52855107076,96723408771,165591429654,264623816287,
  392808536796,538536468669,674233507402,759076605663,743556792366,593287125617,304616565048,
  66155947612,414077065779,606255819372,547931334965,243061910782,180763473676,507403286537,
  547934641294,261887383585,188818396699,511383063428,474716137883,88809573858,371003754536,
  543357893963,266985172816,261965768500,627085249519,534915889340,79013701595,336220099775,
  378118951590,101647706213,144432217161,127832340680,13926291238,6379703401,128195558409,
  78546242484,219716337654,325015267597,87995263069,526545984860,228591454893,524339570499,
  553877462560,320435017036,725976063395],
 [30655735411,675588697672,213129454471,423422293561,340417723854,46147574816,369520079419,
  340595162424,368954718838,583973870509,347436314661,566608278282,170728538812,409142569711,
  228477188608,462382125944,453711468235,585960210339,279172483794,179626253344,617827568927,
  273800380681,530241964270,100112921686,604896014131,56925258961,606649459942,5549564974,
  620548297691,11783101692,631407605968,2032112591,643734276003,38647461767,653265965590,
  112097506504,651655726579,218873972299,625211001316,355129102322,555595879755,508675041711,
  422216444308,653839768420,207923128727,743096346845,77072580351,725968368020,378192464238,
  645701257471,873844064253,297466706,884672519578,1293391977574,2749932310228,7841604481922,
  18468988171818,35646799833426,60829974150506,96654045011050,145767912454102,208764569770394,
  283157029949542,364083990346166],
 [445730399420242,522167278417986,587403465806150,635455337133000,661150399066484,661490664961036,
  636721867184510,590381868892216,528293718269430,457077301645840,382865846511718,310597860816956,
  243851136884772,184968564406120,135244266723216,95074238324070,64089732120672,41322744306072,
  25420627691164,14882242117752,8267547082196,4342284614934,2145121531710,988791876104,
  419506341308,159529547404,51077476070,11026849368,1060570559,3180215763,2512202693,1507737817,
  785690751,372068933,163531575,67478323,26320379,9747215,3436955,1156097,371417,114041,33463,
  9375,2499,625,141,25,1]]
private def pvm_r192_3_2 : List ℤ := pzigCatZ 6
 [
 [879620257,4691734948,17087382935,48864985320,115768319917,233047675068,402945202657,
  598332824328,753423502075,776863644516,595358899119,214259811800,244226147804,570795129147,
  578988857860,242559311485,242676753363,552902218972,458041311149,17280804810,430121963904,
  518069135865,170612678784,300659345486,449415094423,108214398670,421609263186,624983413779,
  269960492518,336927645486,626573714155,331380957568,238152347974,513778307393,261446051820,
  195528813082,364746432061,131512071084,167335216550,197033648521,12026427758,93926882788,
  27321149659,26241480795,50303742373,81854413914,75599442578,208714089233,25007884364,
  291520543350,222325316817,246416275319,425290097502,65181375074,541695381889,195136777466,
  522241307314,449675250415,373654202595,623426116666,145810969388,674214965661,93388761902,
  597809230204],
 [282462791521,419589913017,382616762168,180256739632,383996439267,77421057198,303512947186,
  316260795117,176626324037,505595646168,44575354180,618284935827,61964729710,630465356502,
  139232578053,531863408397,216413897746,347415371304,335595979415,151833190709,501457114384,
  40018727910,638470326913,38217585893,635447065396,35108867390,498223530997,112347838122,
  423240402734,326282169795,539153778365,339584117942,601903214414,215729823205,418343462389,
  350101583092,418384059808,472773945317,626558417641,225745963190,401142966504,427183062385,
  616283014479,248240832508,560780660666,246176531727,644676906699,126717668254,667386580902,
  6423905473,686703779003,155287934013,661919483030,339039186292,578066182721,528902454377,
  414437435732,690077596344,162342755897,771608274947,160638222205,716678752472,492705204774,
  506693547627],
 [771192029573,150139671180,1012993924050,634726477190,596293504221,1502672766987,1854166086815,
  2417639895141,2978971652077,588153789269,10046179013408,34513271599836,76903375705568,
  139197566898004,221121135137330,319467887195474,427109919664084,532958986581182,623794375147324,
  687501452553352,716209923457254,707926024737198,666239743160728,598675239672100,514621125975772,
  423541632797110,333730185426652,251571696050894,181209177268320,124549860619666,81567649448098,
  50825049575140,30088701589160,16898859502018,8989525290872,4520661590130,2143738733788,
  955343794074,398103546006,153924877572,54503613116,17244862732,4611392426,869305418,14207393,
  121827611,79596977,37619741,15072889,5381453,1749229,523105,144651,37053,8783,1911,375,61,5]]
private def phbv_g11 : List ℤ := pzigCatZ 0
 [
 [226787471986082,319264208820768,389226811949920,447372846916798,497866219456130,542852387376490,
  583611659034710,620981974864470,655547958966164,687737149748356,717873716897894,746210602778790,
  772949827862334,798255892480562,822264946687154,845091257079518,866831886235004,887570154716388,
  907378252345302,926319241536048,944448617534988,961815540001860,978463816962198,994432699531548,
  1009757530181152,1024470276324504,1038599973151628,1052173093944320,1065213861921716,
  1077744514552666,1089785528929098,1101355815013150,1112472882202860,1123152983601080,
  1133411241543622,1143261757289830,1152717707260672,1161791427795208,1170494490063140,
  1178837766501350,1186831489922620,1194485306264876,1201808321801154,1208809145507980,
  1215495927188052,1221876391857986,1227957870840664,1233747329941606,1239251395038058,
  1244476375366396,1249428284756806,1254112861032806,1258535583766352,1262701690556148,
  1266616191976868,1270283885329714,1273709367309842,1276897045693106,1279851150133310,
  1282575742151128,1285074724387272,1287351849184768,1289410726558504,1291254831604298],
 [1292887511394456,1294311991402154,1295531381492852,1296548681517290,1297366786537290,
  1297988491712760,1298416496875554,1298653410813648,1298701755286846,1298563968793444,
  1298242410105534,1297739361589076,1297057032323538,1296197561034558,1295163018852056,
  1293955411905064,1292576683763714,1291028717737878,1289313339041252,1287432316828866,
  1285387366115436,1283180149581336,1280812279272376,1278285318199152,1275600781841152,
  1272760139560480,1269764815929562,1266616191976868,1263315606354334,1259864356429810,
  1256263699307588,1252514852779736,1248618996210706,1244577271357430,1240390783126846,
  1236060600272562,1231587756032136,1226973248706228,1222218042180628,1217323066392004,
  1212289217737924,1207117359431550,1201808321801154,1196362902534390,1190781866867046,
  1185065947715754,1179215845753902,1173232229429740,1167115734925448,1160866966055590,
  1154486494103190,1147974857591238,1141332561987218,1134560079337842,1127657847830776,
  1120626271279774,1113465718529162,1106176522773132,1098758980784756,1091213352049048,
  1083539857793754,1075738679910826,1067809959760726,1059753796850868],
 [1051570247378428,1043259322626762,1034820987203372,1026255157105982,1017561697601768,
  1008740420903034,999791083620624,990713383974178,981506958735790,972171379880784,
  962706150916004,953110702852370,943384389784126,933526484032322,923536170804504,913412542316024,
  903154591310940,892761203911796,882231151717398,871563083056004,860755513287514,849806814032020,
  838715201183128,827478721541778,816095237879686,804562412209560,792877687001264,781038264037226,
  769041080545284,756882782180144,744559692343158,732067777230200,719402605874484,706559304298796,
  693532502701730,680316274364314,666904064662378,653288608186974,639461831483564,625414738284830,
  611137273281498,596618159380734,581844701942862,566802551520962,551475413945446,535844692886120,
  519889044818984,503583818902460,486900343494794,469805005098976,452258041399868,434211932664334,
  415609216182902,396379450430284,376434888524164,355664123421080,333922412071770,311016284897422,
  286677699934856,260517519905718,231933679040830,199904832145364,162424714533042,114276190827302]]
private def pvi_r192_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s3 pvo_r192_3
private def pvo_r192_4 : List ℤ := pzigCatZ 2
 [
 [127698426056,370075865525,676478371082,854217567511,690861125160,166703705953,427423346613,
  655811123324,321404587225,286106332873,596009155210,300199471419,303087357173,585931869418,
  260293327255,284561895015,405250183446,45228146600,516364721827,397458186524,228328459890,
  640872167283,334687937528,350503770422,617951621537,173414550948,426905652526,475647522241,
  24458538093,418511986654,259457354121,168715089973,302859806044,48339853801,187051794047,
  121914178792,58384278906,76387100511,13031302389,3092365028,60481714266,15394161982,
  147499752349,53348769632,203506407796,188537251591,178189772367,337005472688,59194209364,
  440758657895,129387617408,459056504746,340659266657,379189190359,523479713838,218213288380,
  634534516011,9814460407,654802519690,198271769509,581787902467,365178639002,433395828078,
  460990552407],
 [239236652789,470976627898,31556291372,396998241391,161568483302,255672944688,319999889533,
  74241193769,432197639368,114689777421,493092347519,279006496594,500295830996,393589732651,
  450807180473,447209560780,341117459064,448027070269,173014779401,423510790808,35925200989,
  409428088117,244488317616,426629597542,395648894489,456461308931,449084083252,440299997692,
  424577308721,325881794597,409909822772,140073072244,488215195507,2787043297,624407433642,
  6755766926,667140628253,62387157883,558312346818,18907366843,490451258969,190134264520,
  619082784106,170032072083,694681907117,28035176562,541561112642,135212288475,585704083831,
  179432001004,763403156276,84125930962,547600533089,64822778026,747084614912,181420173116,
  629590380977,222121830541,648966475994,392393926256,557210294649,527635400685,437290330864,
  666828783084],
 [245739567033,762436803663,7675608587,782246417592,312465427912,688371652261,603428093623,
  316989564636,1126495077962,661295166797,949373116330,3349269557051,3501340053366,755108012173,
  5138343172513,2297293232812,8730130864416,4829180796762,3603940307173,5668055182795,
  7596751801696,43267772403074,107066346441134,201160167745668,320859555270890,453315748256004,
  579859690981244,681071943732374,742095181454570,755964645663876,724168215755264,654998710980722,
  560808652540592,455129650912990,350245045883476,255519234786474,176613741264002,115563825549684,
  71518669911268,41820829446164,23082517626566,12010917063782,5883877471632,2708895756222,
  1169471749222,472012917988,177368308680,61678270490,19664852872,5660169344,1428429362,295312380,
  39169920,3221685,4677177,2103711,699637,193743,46295,9629,1731,259,25]]
private def phbv_g12 : List ℤ := pzigCatZ 0
 [
 [226772396215854,319242985629678,389200937972258,447343107662738,497833123638872,542816301089232,
  583572863261744,620940694887726,655504381204496,687691432199864,717825996011398,746160998188680,
  772898445773626,798202828163060,822210286360042,845035079366072,866774263306234,887511153204542,
  907317934083788,926257664166180,944385835009012,961751603004120,978398773264886,994366594297626,
  1009690406224178,1024402174332992,1038530931883968,1052103150399086,1065143051487230,
  1077672871139012,1089713085085136,1101282602030696,1112398930209784,1123078321644824,
  1133335897666366,1143185758596368,1152641079979892,1161714197335932,1170416681064998,
  1178759402881218,1186752594917150,1194405902469502,1201728431205962,1208728789530780,
  1215415126704884,1221795167231374,1227876241945780,1233665316190564,1239169015402516,
  1244393648398604,1249345228609244,1254029493476528,1258451922208154,1262617752054660,
  1266531993257638,1270199442799388,1273624697069496,1276812163550814,1279766071615974,
  1282490482515660,1284989298631156,1287266272056048,1289325012565246,1291168995023564],
 [1292801566280808,1294225951595738,1295445260627088,1296462493026178,1297280543662386,
  1297902207509802,1298330184220816,1298567082409980,1298615423669462,1298477646335462,
  1298156109023270,1297653093947124,1296970810039642,1296111395884294,1295076922473318,
  1293869395802386,1292490759312432,1290942896188138,1289227631521862,1287346734351032,
  1285301919576360,1283094849767690,1280727136863672,1278200343770998,1275515985868418,
  1272675532420356,1269680407904542,1266531993257638,1263231627042596,1259780606541022,
  1256180188773642,1252431591451570,1248535993860860,1244494537682544,1240308327750114,
  1235978432746130,1231505885839466,1226891685264416,1222136794842702,1217242144449170,
  1212208630421800,1207037115916374,1201728431205962,1196283373925198,1190702709258996,
  1184987170075272,1179137457000832,1173154238439492,1167038150531140,1160789797050206,
  1154409749241734,1147898545592914,1141256691537634,1134484659091224,1127582886412220,
  1120551777287532,1113391700536970,1106102989332576,1098685940427692,1091140813290084,
  1083467829132792,1075667169835674,1067738976749802,1059683349375968],
 [1051500343907612,1043189971627346,1034752197145020,1026186936463944,1017494054860250,
  1008673364558726,999724622186394,990647525982954,981441712744648,972106754475252,
  962642154714616,953047344511484,943321678003032,933464427558688,923474778440158,913351822923142,
  903094553818654,892701857323284,882172505117496,871505145619402,860698294287592,849750322850408,
  838659447320050,827423714627304,816040987685954,804508928664128,792824980201702,780986344267118,
  768989958291812,756832468153472,744510197497850,732019112788972,719354783354602,706512335541520,
  693486399905286,680271050120904,666859731999928,653245180616376,639419323052400,625373163638710,
  611096647734462,596578498996470,581806023628938,566764873138832,551438754439720,535809072437612,
  519854485027318,503550343005936,486867976637672,469773774659978,452227977400932,434183068286288,
  415581588426424,396353100978676,376409864893732,355640480533946,333900214471900,310995609989730,
  286658642942438,260500201919692,231918261174830,199891543407274,162413917297840,114268594280718]]
private def pvi_r192_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s4 pvo_r192_4
private def pvo_r192_5 : List ℤ := pzigCatZ 0
 [
 [483920468709,872502361692,798200540121,158405536500,542203775142,626877375093,24067383182,
  564507028180,442013624631,233710885357,624865852006,266719723251,333780529063,369674894278,
  180482933572,516710351197,116226217722,516992891938,510958137919,172559727645,649296518372,
  293165606569,418044973559,554371385608,18098145614,502781483723,290260386722,255432609568,
  384175412663,2441235112,298803650806,148446729753,146309225327,161707014400,29744457224,
  93630196257,450937952,23430933724,32671311284,33555108724,186468309673,148145655264,80386139700,
  164218076669,43521875636,17362877777,24095666066,230768846550,220373162643,453936119283,
  374471382580,617218129240,282976054663,278766415473,588669905240,202109849570,638524144079,
  912357324,649374815216,185862109629,575712638745,337742756196,438070839632,427658391731],
 [255049500523,445621861166,54762744250,390264031987,138082714980,272768887644,303638775581,
  114123399215,427978040434,58889489971,502477049507,218626488804,522181207514,341884819433,
  484085889317,415210063882,386916645888,439146125247,233839074739,429226031612,38053237640,
  410792522243,171771593144,406077509806,352643019937,416959970471,461745259302,414680226842,
  483664080199,352238615515,453627545606,204932772226,446567575913,13958920093,515852925206,
  121866950741,622083398349,137672264776,648176288216,102708716743,543290434865,167071581296,
  439963826940,336933436305,498686585977,403616170698,608365979700,292188518995,528981307277,
  285067849792,425070985844,445075488189,588276148999,355833516052,638693270954,208824435839,
  490618145031,377461322650,756344392758,97538869325,627470753843,121349980894,754217008604,
  69552640776],
 [688312728083,286740666253,858421484136,44044036912,156328191312,1922512694311,2396469445122,
  1618474834103,1790205649150,1082145478259,2162180736239,3297502811902,414676320524,
  3522822694669,1205612490552,3828564143150,1842152920061,5898983874031,1213216965191,
  6513455796374,8283450482326,1813513352122,8017615816321,12872425936923,2881869367245,
  32620256599906,102514164539122,209185595225790,344694044221240,490976175895512,624557083756496,
  723421511717724,772870431247330,768363323390618,715133101828432,625537690548756,515410458375182,
  400468625138776,293521291458086,202903676251764,132224502838644,81174210529838,46909680619574,
  25494205001010,13016014867026,6234384007404,2796836001176,1172676124868,458274354748,
  166304244412,55756924032,17144972996,4781747544,1187494380,253527602,42759448,4017544,663751,
  483757,159255,38693,7493,1153,125],
 [5]]
private def phbv_g13 : List ℤ := pzigCatZ 0
 [
 [185036899956674,260489077945806,317571874815256,365013481535506,406211247184610,442915660263586,
  476171330015008,506661935739316,534864474821908,561127777738464,585716335968122,608836526302748,
  630653178137054,651300508018430,670889601376956,689513688834094,707251964175360,724172409015894,
  740333923349976,755787960079940,770579798022376,784749546760766,798332949456618,811362031268448,
  823865628274626,835869822828998,847398304871336,858472674069170,869112694253970,879336509074778,
  889160825881332,898601073395252,907671537611724,916385479509144,924755237468086,932792316768324,
  940507468109918,947910756766388,955011623706192,961818939798602,968341054040758,974585836596012,
  980560717312750,986272720292940,991728494996596,996934344298888,1001896249858538,
  1006619895107028,1011110686126868,1015373770651878,1019414055392670,1023236221864788,
  1026844740875192,1030243885803796,1033437744800604,1036430232004852,1039225097880420,
  1041825938751094,1044236205610090,1046459212270064,1048498142912808,1050356059091568,
  1052035906233434,1053540519684434],
 [1054872630335640,1056034869864862,1057029775625066,1057859795207712,1058527290706536,
  1059034542704842,1059383754007368,1059577053135744,1059616497604930,1059504076996456,
  1059241715842888,1058831276336694,1058274560875564,1057573314455196,1056729226919636,
  1055743935078422,1054619024699006,1053356032382234,1051956447328016,1050421712997758,
  1048753228679538,1046952350961618,1045020395119296,1042958636419814,1040768311349584,
  1038450618767634,1036006720988898,1033437744800604,1030744782414776,1027928892359576,
  1024991100311946,1021932399873812,1018753753293838,1015456092136552,1012040317900398,
  1008507302586168,1004857889216950,1001092892310656,997213098305964,993219265942308,
  989112126594420,984892384561734,980560717312750,976117775684350,971564184035794,966900540357000,
  962127416330474,957245357346102,952254882467726,947156484350326,941950629106236,936637756118744,
  931218277801004,925692579298012,920061018129020,914323923767452,908481597155024,902534310146348,
  896482304879886,890325793070606,884064955219200,877699939732116,871230861945986,864657803049338],
 [857980808893702,851199888685218,844315013546990,837326114941188,830233082938710,823035764322742,
  815733960510998,808327425279548,800815862269142,793198922252554,785476200138828,777647231687260,
  769711489900490,761668381062050,753517240379178,745257327186368,736887819659054,728407808979696,
  719816292890338,711112168556036,702294224652372,693361132576990,684311436669606,675143543306478,
  665855708713612,656446025316850,646912406416062,637252568933170,627464013938842,617544004607940,
  607489541187388,597297332478586,586963763236166,576484856760592,565856231807184,555073052739756,
  544129971611504,533021060543178,521739732367566,510278646990436,498629600240540,486783391088034,
  474729661920342,462456704960352,449951225723134,437198051380760,424179767657734,410876261823548,
  397264140559076,383315978463654,368999333288764,354275433474276,339097394941756,323407744139636,
  307134887999112,290187929021418,272448770713434,253759560391378,233901601433744,212557395016570,
  189235713019876,163103235388626,132523041905004,93238448774802]]
private def pvi_r192_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s5 pvo_r192_5
private def pvo_r192_6 : List ℤ := pzigCatZ 0
 [
 [653602983480,944929790525,536971309960,295414334590,705975238923,258027794784,467222878112,
  544270491601,112340193273,629471476266,344333972859,302644717459,397425642638,155762338050,
  504742629917,85456965066,536905953342,454065049793,270862326075,653961936172,164762041677,
  525452254787,487062385896,182578701816,544302833339,153383775788,380404178178,332214786957,
  138976173817,332348790150,49909234193,222801817931,127131430052,96472255148,102289408643,
  28051495535,44623606386,558240279,81578142672,176879933041,53946409454,163007578142,
  158975844571,10460859109,59291109490,56064138787,150171741558,1948941608,398054122605,
  105212290394,631621083140,145564371185,690232672967,136542494846,382555685416,528538016207,
  414403136433,566290060684,210470929270,635650688927,36132672721,606884100146,134635857959,
  507596730225],
 [265987363596,346450967636,344649463887,147890769331,361544734318,64707539689,320707946025,
  267241445868,235441232674,437503096041,124636766349,556590269214,7880722146,610103150859,
  99588561308,589639181814,191059164863,495388867627,269890759286,339706143334,346422122357,
  149686531345,429340110720,35225804639,513895612917,174761140148,574337121756,248226228335,
  571124046925,273638994684,478295290226,305665247957,318217542749,396953520740,168507585828,
  539237029235,108550387137,645041382986,130073532722,627590405039,117205709815,528481149174,
  19094568979,510160747429,177998193746,627889289666,173875909155,687711622139,74546186674,
  566308498286,146043539693,530688051291,275877976768,705977359736,130176340985,672929520641,
  51458146530,561743188354,192060176371,804370084503,109044374219,634340611104,26207747842,
  682982168487],
 [408638524489,963168155052,226354720753,462791339828,2203434964829,2606301867598,1431757723549,
  939042845076,212143480005,2233606032123,2775825260038,944749523156,3518289037245,681393656722,
  3128685213986,2058154591379,452458602281,3385004977495,6499414788377,2362241078043,
  5526618215872,8813356684054,3808852661846,6483736196253,14778371710287,11094566323789,
  16435926230014,78738194279298,180509822076984,315544664149820,466227871996440,608070699128284,
  717006409234158,776015114356686,778709351474142,729396223866384,640491350459398,528617499705256,
  410606405581770,300316674257232,206815693352962,134052299169344,81732645343660,46840468184326,
  25209053180812,12726931899812,6019149785070,2662283148770,1098856762024,422060761586,
  150292847776,49366315004,14850730880,4048298164,983047582,206126364,34804316,3713534,218219,
  250055,81005,18205,3111,385],
 [23]]
private def phbv_g14 : List ℤ := pzigCatZ 0
 [
 [214084805353062,301381797693782,367425702772530,422314901320060,469980073196776,512446506278236,
  550922797154736,586199952106610,618829849664190,649216081243598,677664659358242,704414358735356,
  729655884412108,753544522839092,776208798125184,797756576644350,818279484370448,837856174971192,
  856554794820710,874434874123962,891548799765074,907942977906140,923658762827172,938733207136756,
  953199673727514,967088339475778,980426613272128,993239485594792,1005549822888320,
  1017378617071484,1028745198287180,1039667417325520,1050161802859974,1060243697635578,
  1069927376966088,1079226152280642,1088152461971420,1096717951402790,1104933543627920,
  1112809502104104,1120355486490726,1127580602443960,1134493446182426,1141102144482476,
  1147414390665564,1153437477059898,1159178324351258,1164643508181170,1169839283302718,
  1174771605563600,1179446151951406,1183868338906558,1188043339082934,1191976096714398,
  1195671341726700,1199133602717850,1202367218916018,1205376351211700,1208164992350184,
  1210736976360998,1213095987292778,1215245567314846,1217189124240376,1218929938520470],
 [1220471169753478,1221815862749552,1222966953186474,1223927272889364,1224699554763806,
  1225286437409094,1225690469435928,1225914113510612,1225959750145844,1225829681256404,
  1225526133496434,1225051261393554,1224407150293764,1223595819129848,1222619223024998,
  1221479255742300,1220177751989950,1218716489591142,1217097191526934,1215321527859636,
  1213391117543726,1211307530130644,1209072287373382,1206686864736238,1204152692814692,
  1201471158669928,1198643607082186,1195671341726700,1192555626275738,1189297685429862,
  1185898705881286,1182359837211932,1178682192728486,1174866850236562,1170914852755800,
  1166827209177502,1162604894866222,1158248852206474,1153759991095534,1149139189383084,
  1144387293258278,1139505117584564,1134493446182426,1129353032059980,1124084597591144,
  1118688834640918,1113166404637044,1107517938587102,1101744037039862,1095845269989442,
  1089822176720542,1083675265592766,1077405013761698,1071011866834088,1064496238454128,
  1057858509817428,1051099029108858,1044218110859962,1037216035221160,1030093047143364,
  1022849355463060,1015485131884194,1008000509849442,1000395583292672],
 [992670405263384,984824986412940,976859293331220,968773246721026,960566719396102,952239534086988,
  943791461037074,935222215369118,926531454200094,917718773479552,908783704523576,899725710212920,
  890544180819858,881238429423710,871807686869620,862251096219162,852567706634136,842756466626834,
  832816216600440,822745680592140,812543457118484,802208009007288,791737652082316,781130542545774,
  770384662878362,759497806046556,748467557770868,737291276565598,725966071208510,714488775235630,
  702855917979470,691063691574616,679107913238598,666983981992118,654686828803462,642210858917034,
  629549884841846,616697048114124,603644727484210,590384430577636,576906665296310,563200786192306,
  549254809669524,535055190012574,520586545709878,505831322036328,490769370946964,475377422326490,
  459628410469778,443490604616296,426926469590832,409891147303436,392330393607086,374177712499608,
  355350271917768,335742904874138,315218975569326,293595850911832,270620502323796,245925588621142,
  218942766535724,188707897769604,153327091178418,107875430046920]]
private def pvi_r192_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r192_s6 pvo_r192_6
private def pvo_r192_7 : List ℤ := pzigCatZ 0
 [
 [940856896875,773435356826,185393833230,737888136309,213056703902,556347110954,435282314371,
  363191364921,643557930238,40595463589,478550416857,146602489004,435275762888,283558578179,
  398195794033,525583609218,164914085022,676571441037,277738891130,361230912216,247094131971,
  191823499335,231208120639,565456338052,746595664764,187775195205,214645181139,368295595880,
  45320383766,295965157329,85569448150,175904264806,108627569787,89744615121,105676962962,
  30140843691,68729075210,102396025991,49137256835,202803693490,97158107655,117073386615,
  134593446810,18390426211,31820557629,99918039218,161299925567,106251338301,396254815360,
  67274726574,619659063161,36634916959,735351654378,18643494688,628818606697,144666676942,
  423931557968,527277648121,535185655211,466012276876,269675351192,576656255399,128875516091,
  534873771882],
 [49543383923,442457649245,195290590946,288252180622,304077003335,98110989131,363331011624,
  107046752723,374256551957,301051738826,342649522572,459224524883,277437032249,561026076644,
  187149238686,593451890323,77437669047,554182613022,49497510239,454078385715,192316461332,
  317312024574,344844500093,176743323603,489721093636,62937653108,596641455861,11185577686,
  631261921760,62007551375,576197871663,130466117328,453918879316,252938483393,328785244071,
  419933835256,268382718822,561425808245,278475466507,597888352346,276651485904,535705394187,
  170713962997,495602080870,5477906443,578619607311,90570661638,694107020746,25191081119,
  658727536917,2161631394,539289762610,148454566697,603296983165,200490759058,743997202628,
  36276108803,624980443735,46403302742,640024161786,222190652327,652070489363,466197038809,
  1202360728870],
 [942874721761,701893621820,2179380446857,2660057419106,1118306668053,394519488565,756823441566,
  1595029205337,1884621399018,709105244968,3218547708067,928022952606,3284288744176,3168482609341,
  155153939293,1149313020362,127354847129,1270023911294,380739179912,4776237864975,7316098231721,
  2571393156669,5459112610694,9311406153132,4983822421470,6067558588255,17654795888855,
  19140025004253,3641366287538,64244275247836,168811488974738,310622299060908,469878890413854,
  619240058311422,732213928679560,790543876099134,788068029164960,730587586844184,632721813925056,
  513270142466252,390560130954736,278929517764798,186977417463004,117609858099330,69378108928576,
  38352981003086,19849724141898,9606370102566,4340558052240,1827531382736,715205285888,
  259320254910,86742503554,26615137922,7431337868,1866361174,413974372,78517200,11875110,1138118,
  42629,48859,12523,1995],
 [185]]
private abbrev pl_r192 : List ℕ := [1, 1, 2, 2, 2, 2, 2, 2]
private abbrev ptau_r192 : List ℕ :=
  [12311628, 18861414, 9846983, 10218327, 1278670, 1278585, 417309, 724230]
private abbrev pnsub_r192 : List ℕ := [25, 38, 34, 35, 5, 5, 2, 3]
private def pwalks_r192 : List RkmSegWalk := [ ⟨phbv_g7, pvi0, pvo_r192_0⟩,
  ⟨phbv_g8, pvi_r192_1, pvo_r192_1⟩, ⟨phbv_g9, pvi_r192_2, pvo_r192_2⟩,
  ⟨phbv_g10, pvi_r192_3, pvo_r192_3⟩, ⟨phbv_g11, pvi_r192_4, pvo_r192_4⟩,
  ⟨phbv_g12, pvi_r192_5, pvo_r192_5⟩, ⟨phbv_g13, pvi_r192_6, pvo_r192_6⟩,
  ⟨phbv_g14, pvi_r192_7, pvo_r192_7⟩]
private abbrev dP_0 : Prop := bSlideChk 15 193 phbv_g9 pvi_r192_2 pvm_r192_2_1 = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := bSlideChk 15 193 phbv_g9 pvm_r192_2_1 pvm_r192_2_2 = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := bSlideChk 15 193 phbv_g10 pvi_r192_3 pvm_r192_3_1 = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := bSlideChk 15 193 phbv_g10 pvm_r192_3_1 pvm_r192_3_2 = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := bSlideChk 22 129 phbv_g0 pvi0 pvm_r128_0_1 = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := bSlideChk 22 129 phbv_g1 pvi_r128_1 pvm_r128_1_1 = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := bSlideChk 22 129 phbv_g2 pvi_r128_2 pvm_r128_2_1 = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := bSlideChk 22 129 phbv_g2 pvi_r128_3 pvm_r128_3_1 = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := bSlideChk 22 129 phbv_g7 pvi0 pvm_r192_0_1 = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := bSlideChk 22 129 phbv_g8 pvi_r192_1 pvm_r192_1_1 = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [ bSlideChk 16 129 phbv_g8 pvm_r192_1_1 pvo_r192_1,
  bSlideChk 5 129 phbv_g3 pvi_r128_4 pvo_r128_4, muxNatListEq [Nat.add (highdNatMin (Nat.mul 2 128)
  128) 1] [129]] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [ bSlideChk 13 129 phbv_g1 pvm_r128_1_1 pvo_r128_1,
  bSlideChk 4 193 phbv_g9 pvm_r192_2_2 pvo_r192_2, bSlideChk 3 129 phbv_g7 pvm_r192_0_1 pvo_r192_0]
  = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := rkmAllTrueF [ rkmCheckRowFromWalks 128 64 192 pl_r192 ptau_r192
  pnsub_r192 rkmMasksHiHiB_m128_r192 pwalks_r192 rkmRowHiHiB_m128_r192, bSlideChk 5 193 phbv_g12
  pvi_r192_5 pvo_r192_5, bSlideChk 2 193 phbv_g13 pvi_r192_6 pvo_r192_6] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := rkmAllTrueF [ bSlideChk 9 129 phbv_g2 pvm_r128_2_1 pvo_r128_2,
  bSlideChk 5 193 phbv_g10 pvm_r192_3_2 pvo_r192_3, bSlideChk 3 193 phbv_g14 pvi_r192_7 pvo_r192_7,
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 128) 128) 1] [129], muxNatListEq [Nat.add
  (highdNatMin (Nat.mul 2 128) 192) 1] [193]] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := rkmAllTrueF [ bSlideChk 9 129 phbv_g2 pvm_r128_3_1 pvo_r128_3,
  bSlideChk 5 193 phbv_g11 pvi_r192_4 pvo_r192_4, bSlideChk 3 129 phbv_g6 pvi_r128_7 pvo_r128_7,
  bSlideChk 2 129 phbv_g5 pvi_r128_6 pvo_r128_6] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := rkmAllTrueF [ bSlideChk 8 129 phbv_g0 pvm_r128_0_1 pvo_r128_0,
  rkmCheckRowFromWalks 128 64 128 pl_r128 ptau_r128 pnsub_r128 rkmMasksHiHiB_m128_r128 pwalks_r128
  rkmRowHiHiB_m128_r128, bSlideChk 5 129 phbv_g4 pvi_r128_5 pvo_r128_5, muxNatListEq [Nat.add
  (highdNatMin (Nat.mul 1 128) 192) 1] [129]] = true
private theorem bk_15 : dP_15 := by decide +kernel
private theorem pacc_r128_0_1 : muxFastIterFullT16 30 129 phbv_g0 pvi0 = pvo_r128_0 := bCh 30
    (bSlideChk_sound bk_4) (rkmHd bk_15) rfl
private theorem pwalk_r128_0 : muxFastIterFullT16 30 129 phbv_g0 pvi0 = pvo_r128_0 := pacc_r128_0_1
private theorem pseg_r128_0 : muxFastIterFullT16 30
    (Nat.add (highdNatMin (Nat.mul 1 128) 128) 1)
    phbv_g0 pvi0 = pvo_r128_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_13))))]; exact pwalk_r128_0
private theorem pacc_r128_1_1 : muxFastIterFullT16 35 129 phbv_g1 pvi_r128_1 = pvo_r128_1 := bCh 35
    (bSlideChk_sound bk_5) (rkmHd bk_11) rfl
private theorem pwalk_r128_1 : muxFastIterFullT16 35 129 phbv_g1 pvi_r128_1 = pvo_r128_1 :=
    pacc_r128_1_1
private theorem pseg_r128_1 : muxFastIterFullT16 35
    (Nat.add (highdNatMin (Nat.mul 1 128) 128) 1)
    phbv_g1 pvi_r128_1 = pvo_r128_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_13))))]; exact pwalk_r128_1
private theorem pacc_r128_2_1 : muxFastIterFullT16 31 129 phbv_g2 pvi_r128_2 = pvo_r128_2 := bCh 31
    (bSlideChk_sound bk_6) (rkmHd bk_13) rfl
private theorem pwalk_r128_2 : muxFastIterFullT16 31 129 phbv_g2 pvi_r128_2 = pvo_r128_2 :=
    pacc_r128_2_1
private theorem pseg_r128_2 : muxFastIterFullT16 31
    (Nat.add (highdNatMin (Nat.mul 2 128) 128) 1)
    phbv_g2 pvi_r128_2 = pvo_r128_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_10)))]; exact pwalk_r128_2
private theorem pacc_r128_3_1 : muxFastIterFullT16 31 129 phbv_g2 pvi_r128_3 = pvo_r128_3 := bCh 31
    (bSlideChk_sound bk_7) (rkmHd bk_14) rfl
private theorem pwalk_r128_3 : muxFastIterFullT16 31 129 phbv_g2 pvi_r128_3 = pvo_r128_3 :=
    pacc_r128_3_1
private theorem pseg_r128_3 : muxFastIterFullT16 31
    (Nat.add (highdNatMin (Nat.mul 2 128) 128) 1)
    phbv_g2 pvi_r128_3 = pvo_r128_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_10)))]; exact pwalk_r128_3
private theorem pwalk_r128_4 : muxFastIterFullT16 5 129 phbv_g3 pvi_r128_4 = pvo_r128_4 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_10)))
private theorem pseg_r128_4 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 2 128) 128) 1)
    phbv_g3 pvi_r128_4 = pvo_r128_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_10)))]; exact pwalk_r128_4
private theorem pwalk_r128_5 : muxFastIterFullT16 5 129 phbv_g4 pvi_r128_5 = pvo_r128_5 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_15))))
private theorem pseg_r128_5 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 2 128) 128) 1)
    phbv_g4 pvi_r128_5 = pvo_r128_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_10)))]; exact pwalk_r128_5
private theorem pwalk_r128_6 : muxFastIterFullT16 2 129 phbv_g5 pvi_r128_6 = pvo_r128_6 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl bk_14)))))
private theorem pseg_r128_6 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 2 128) 128) 1)
    phbv_g5 pvi_r128_6 = pvo_r128_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_10)))]; exact pwalk_r128_6
private theorem pwalk_r128_7 : muxFastIterFullT16 3 129 phbv_g6 pvi_r128_7 = pvo_r128_7 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_14))))
private theorem pseg_r128_7 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 2 128) 128) 1)
    phbv_g6 pvi_r128_7 = pvo_r128_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_10)))]; exact pwalk_r128_7
private theorem pwalks_snd_r128 :
    RkmSegWalksSound 128 128 pl_r128 pnsub_r128 pwalks_r128 := by
  dsimp only [RkmSegWalksSound, pl_r128, pnsub_r128, pwalks_r128]
  exact ⟨pseg_r128_0, ⟨pseg_r128_1, ⟨pseg_r128_2, ⟨pseg_r128_3,
    ⟨pseg_r128_4, ⟨pseg_r128_5, ⟨pseg_r128_6, ⟨pseg_r128_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 128)` (`FindAllJohnsonRampKickMuxHi128T2`). -/
theorem rkmTrajHiHiB_m128_r128 :
    rkmLo12EqHi 128 64 128 [1, 1, 2, 2, 2, 2, 2, 2]
      [19324585, 23012918, 12552501, 12552501, 2010242, 1942135, 692434, 877181]
      [30, 35, 31, 31, 5, 5, 2, 3] rkmMasksHiHiB_m128_r128 rkmRowHiHiB_m128_r128 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r128 (rkmHd (rkmTl bk_15))
private theorem pacc_r192_0_1 : muxFastIterFullT16 25 129 phbv_g7 pvi0 = pvo_r192_0 := bCh 25
    (bSlideChk_sound bk_8) (rkmHd (rkmTl (rkmTl bk_11))) rfl
private theorem pwalk_r192_0 : muxFastIterFullT16 25 129 phbv_g7 pvi0 = pvo_r192_0 := pacc_r192_0_1
private theorem pseg_r192_0 : muxFastIterFullT16 25
    (Nat.add (highdNatMin (Nat.mul 1 128) 192) 1)
    phbv_g7 pvi0 = pvo_r192_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_15))))]; exact pwalk_r192_0
private theorem pacc_r192_1_1 : muxFastIterFullT16 38 129 phbv_g8 pvi_r192_1 = pvo_r192_1 := bCh 38
    (bSlideChk_sound bk_9) (rkmHd bk_10) rfl
private theorem pwalk_r192_1 : muxFastIterFullT16 38 129 phbv_g8 pvi_r192_1 = pvo_r192_1 :=
    pacc_r192_1_1
private theorem pseg_r192_1 : muxFastIterFullT16 38
    (Nat.add (highdNatMin (Nat.mul 1 128) 192) 1)
    phbv_g8 pvi_r192_1 = pvo_r192_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_15))))]; exact pwalk_r192_1
private theorem pacc_r192_2_1 : muxFastIterFullT16 30 193 phbv_g9 pvi_r192_2 = pvm_r192_2_2 := bCh
    30 (bSlideChk_sound bk_0) bk_1 rfl
private theorem pacc_r192_2_2 : muxFastIterFullT16 34 193 phbv_g9 pvi_r192_2 = pvo_r192_2 := bCh 34
    pacc_r192_2_1 (rkmHd (rkmTl bk_11)) rfl
private theorem pwalk_r192_2 : muxFastIterFullT16 34 193 phbv_g9 pvi_r192_2 = pvo_r192_2 :=
    pacc_r192_2_2
private theorem pseg_r192_2 : muxFastIterFullT16 34
    (Nat.add (highdNatMin (Nat.mul 2 128) 192) 1)
    phbv_g9 pvi_r192_2 = pvo_r192_2 := by
  rw [bDm (rkmHd (rkmTl4 bk_13))]; exact pwalk_r192_2
private theorem pacc_r192_3_1 : muxFastIterFullT16 30 193 phbv_g10 pvi_r192_3 = pvm_r192_3_2 := bCh
    30 (bSlideChk_sound bk_2) bk_3 rfl
private theorem pacc_r192_3_2 : muxFastIterFullT16 35 193 phbv_g10 pvi_r192_3 = pvo_r192_3 := bCh
    35 pacc_r192_3_1 (rkmHd (rkmTl bk_13)) rfl
private theorem pwalk_r192_3 : muxFastIterFullT16 35 193 phbv_g10 pvi_r192_3 = pvo_r192_3 :=
    pacc_r192_3_2
private theorem pseg_r192_3 : muxFastIterFullT16 35
    (Nat.add (highdNatMin (Nat.mul 2 128) 192) 1)
    phbv_g10 pvi_r192_3 = pvo_r192_3 := by
  rw [bDm (rkmHd (rkmTl4 bk_13))]; exact pwalk_r192_3
private theorem pwalk_r192_4 : muxFastIterFullT16 5 193 phbv_g11 pvi_r192_4 = pvo_r192_4 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_14)))
private theorem pseg_r192_4 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 2 128) 192) 1)
    phbv_g11 pvi_r192_4 = pvo_r192_4 := by
  rw [bDm (rkmHd (rkmTl4 bk_13))]; exact pwalk_r192_4
private theorem pwalk_r192_5 : muxFastIterFullT16 5 193 phbv_g12 pvi_r192_5 = pvo_r192_5 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_12)))
private theorem pseg_r192_5 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 2 128) 192) 1)
    phbv_g12 pvi_r192_5 = pvo_r192_5 := by
  rw [bDm (rkmHd (rkmTl4 bk_13))]; exact pwalk_r192_5
private theorem pwalk_r192_6 : muxFastIterFullT16 2 193 phbv_g13 pvi_r192_6 = pvo_r192_6 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_12))))
private theorem pseg_r192_6 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 2 128) 192) 1)
    phbv_g13 pvi_r192_6 = pvo_r192_6 := by
  rw [bDm (rkmHd (rkmTl4 bk_13))]; exact pwalk_r192_6
private theorem pwalk_r192_7 : muxFastIterFullT16 3 193 phbv_g14 pvi_r192_7 = pvo_r192_7 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_13))))
private theorem pseg_r192_7 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 2 128) 192) 1)
    phbv_g14 pvi_r192_7 = pvo_r192_7 := by
  rw [bDm (rkmHd (rkmTl4 bk_13))]; exact pwalk_r192_7
private theorem pwalks_snd_r192 :
    RkmSegWalksSound 128 192 pl_r192 pnsub_r192 pwalks_r192 := by
  dsimp only [RkmSegWalksSound, pl_r192, pnsub_r192, pwalks_r192]
  exact ⟨pseg_r192_0, ⟨pseg_r192_1, ⟨pseg_r192_2, ⟨pseg_r192_3,
    ⟨pseg_r192_4, ⟨pseg_r192_5, ⟨pseg_r192_6, ⟨pseg_r192_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 192)` (`FindAllJohnsonRampKickMuxHi128T2`). -/
theorem rkmTrajHiHiB_m128_r192 :
    rkmLo12EqHi 128 64 192 [1, 1, 2, 2, 2, 2, 2, 2]
      [12311628, 18861414, 9846983, 10218327, 1278670, 1278585, 417309, 724230]
      [25, 38, 34, 35, 5, 5, 2, 3] rkmMasksHiHiB_m128_r192 rkmRowHiHiB_m128_r192 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r192 (rkmHd bk_12)
end
end QuantumComputation.Specs.DickeSol
