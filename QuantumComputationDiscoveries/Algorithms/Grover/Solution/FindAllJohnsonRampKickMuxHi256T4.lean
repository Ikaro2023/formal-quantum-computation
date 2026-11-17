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
# High-`m` Coupled Walk & Trajectory Part `4` (`FindAllJohnsonRampKickMuxHi256T4`)

Certifies `(m = 256, r = 192)` coupled `T_16` walk (`29722` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi256T4`). -/
def rkmWordBitsHi256T4 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi256T4 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi256T4`). -/
def rkmUnpackMaskHi256T4 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi256T4 n w ++ rkmUnpackMaskHi256T4 ns ws
/-- Mask segment `0` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s0 : List Bool := rkmUnpackMaskHi256T4 [13] [8191]
/-- Mask segment `1` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s1 : List Bool :=
  rkmUnpackMaskHi256T4 [50, 50, 50, 10]
    [1125899906842623, 1125899906842623, 1125899906842623, 1023]
/-- Mask segment `2` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s2 : List Bool := rkmUnpackMaskHi256T4 [50, 3] [1125899906842623, 7]
/-- Mask segment `3` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s3 : List Bool :=
  rkmUnpackMaskHi256T4 [50, 46]
    [1125899906842623, 70368744177663]
/-- Mask segment `4` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s4 : List Bool :=
  rkmUnpackMaskHi256T4 [50, 50, 28]
    [1125899906842623, 1125899906842623, 268435455]
/-- Mask segment `5` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s5 : List Bool :=
  rkmUnpackMaskHi256T4 [50, 50, 44]
    [1125899906842623, 1125899906842623, 17592186044415]
/-- Mask segment `6` for `(m = 256, r = 192)`. -/
def rkmMkHiHiB_m256_r192_s6 : List Bool := rkmUnpackMaskHi256T4 [50, 15] [1125899906842623, 32767]
/-- Prefix-kick masks for `(m = 256, r = 192)`. -/
def rkmMasksHiHiB_m256_r192 : List (List Bool) :=
  [rkmMkHiHiB_m256_r192_s0, rkmMkHiHiB_m256_r192_s1, rkmMkHiHiB_m256_r192_s2,
   rkmMkHiHiB_m256_r192_s3, rkmMkHiHiB_m256_r192_s4, rkmMkHiHiB_m256_r192_s5,
   rkmMkHiHiB_m256_r192_s6, []]
/-- Part `0` of `rkmRowHiHiB_m256_r192`. -/
def rkmRowHiHiB_m256_r192_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 15,
   32, 52, 53, 26, 0, 15, 41, 15, 3, 37, 13, 8, 38, 0, 35, 11, 24, 23, 18, 28, 22, 25, 37, 11, 62,
   0, 67, 34, 18, 106, 48, 131]
/-- Part `1` of `rkmRowHiHiB_m256_r192`. -/
def rkmRowHiHiB_m256_r192_p1 : List ℕ :=
  [14, 29, 30, 365, 756, 761, 405, 65, 25, 289, 664, 897, 893, 543, 247, 0, 48, 887, 407, 1345, 213,
   28, 5, 902, 711, 320, 407, 1, 819, 682, 239, 252, 38, 500, 1743, 808, 15, 657, 533, 49, 16, 2,
   98, 430, 458, 95, 81, 677, 1066, 635, 41, 237, 965, 1136, 447, 1, 666, 752, 2577, 2, 97, 229,
   3756, 2250]
/-- Part `2` of `rkmRowHiHiB_m256_r192`. -/
def rkmRowHiHiB_m256_r192_p2 : List ℕ :=
  [0, 341, 5, 605, 1831, 2007, 1033, 96, 265, 1668, 3737, 4878, 7166, 3561, 6996, 4099, 442, 0, 6,
   470, 10398, 73586, 214858, 140076, 542001, 17846086, 146777010, 723393543, 2599493504,
   7383312424, 17296579589, 34295414181, 58547130023, 87091843488, 113880482446, 131753114968,
   135539709359, 124453532761, 102287790499, 75410800331, 49943928122, 29742836935, 15934296736,
   7679603609, 3328257363, 1295978602, 452815980, 141718951, 39640371, 9881649, 2187778, 428383,
   73806, 11118, 1452, 162, 14, 0, 0, 0, 0, 0, 0, 0]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 192)`. -/
def rkmRowHiHiB_m256_r192 : List ℕ :=
  rkmRowHiHiB_m256_r192_p0 ++ (rkmRowHiHiB_m256_r192_p1 ++ rkmRowHiHiB_m256_r192_p2)
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T4`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T4 : (0 : ℕ) = 0 := rfl
end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bForceN_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat; rw [n1a]
private theorem bForceL_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl
private theorem bOfNatF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced; rw [n1a]
private theorem bNegSuccF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced; rw [n1a]
private theorem bPrimNegOfNat_eq (x : ℕ) : primNegOfNat x = -(x : ℤ) := by
  cases x with
  | zero => dsimp only [primNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only [primNegOfNat]; rw [bNegSuccF_eq, Int.negSucc_eq]; omega
private theorem bPrimSubNat_eq (u z : ℕ) : primSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold primSubNatNat; simp only [Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [bOfNatF_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [bNegSuccF_eq, Int.negSucc_eq]; omega
private theorem bPrimMul_eq (a b : ℤ) : primIntMul a b = a * b := by
  cases a <;> cases b <;> dsimp only [primIntMul] <;>
    simp only [bOfNatF_eq, bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> push_cast <;> ring
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
  | x :: xs =>
    match x with
    | Int.ofNat n =>
      match uToNatHb xs with
      | some ns => some (uConsNat n ns)
      | none => none
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
private theorem bStrictCons_eq (x : ℤ) (xs : List ℤ) : highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 =>
        match xs with
        | [] => [Int.ofNat 0]
        | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 =>
        match xs with
        | [] => [Int.ofNat v]
        | h :: t => Int.ofNat v :: h :: t) = Int.ofNat n :: xs
    rw [n1a]; cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 =>
        match xs with
        | [] => [Int.negSucc 0]
        | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 =>
        match xs with
        | [] => [Int.negSucc v]
        | h :: t => Int.negSucc v :: h :: t) = Int.negSucc n :: xs
    rw [n1a]; cases xs <;> rfl
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bConsZ (primSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bConsZ_eq, bPrimSubNat_eq]
private theorem bDec_len (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | _ :: cs => by rw [bDec_cons, altIntLen, altListLen, bDec_len z cs]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bPrimMul0 (z : ℕ) :
    primIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bPrimMul_eq, bZero_eq]; rfl
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
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bRawSubNat_eq (m n : ℕ) : muxRawSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold muxRawSubNatNat; simp only [Nat.sub_eq]; cases h : n - m with
  | zero => dsimp only; rw [Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private theorem bRawAdd_eq (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a <;> cases b <;> dsimp only [muxRawIntAdd] <;>
    simp only [bOfNatF_eq, bNegSuccF_eq, bRawSubNat_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bRawNeg_eq (a : ℤ) : muxRawIntNeg a = -a := by
  cases a <;> dsimp only [muxRawIntNeg] <;>
    simp only [bNeg_eq, bOfNatF_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
private theorem bRawSub_eq (a b : ℤ) : muxRawIntSub a b = a - b := by
  unfold muxRawIntSub; rw [bRawAdd_eq, bRawNeg_eq]; omega
private theorem bRawMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;> dsimp only [muxRawIntMul] <;>
    simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;>
    push_cast <;> ring
private def bStepVal (v P Q d : ℕ) : ℕ :=
  fN P fun p => fN Q fun q => match Nat.sub q p with
  | 0 => Nat.add v (Nat.div (Nat.sub p q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bStepVal at hv ⊢; dsimp only [fN] at hv ⊢
  rw [bForceN_eq, bForceN_eq] at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv; cases h : Q - P with
  | zero =>
    intro _; have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [zTdiv]; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv] at hv ⊢; omega
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal z d b0 c0 b v c1) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntSub (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ)))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bRawSub_eq,
    bPrimMul_eq, bRawMul_eq]; refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCellVal at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bPrimMul_eq]
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
    ((bHeadOr z cs : ℤ) - (z : ℤ)) =
      (match bDec z cs with
      | cn :: _ => cn
      | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) =
      (match bDec z xs with
      | _ :: t => t
      | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 c0 bns vs cs) = true → bDec z (bSlide z d rem b0 c0 bns vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uOfNatHb, muxFastSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bPrimMul0 z, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_nil, bDec_cons z c cT]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b c bR [] cT hp.2
          rw [bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_nil]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b v z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_cons z c cT]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def bStg (z dg mL : ℕ) (bns vns cns : List ℕ) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add (altListLen cns) 1)) fun nL =>
    fN (Nat.mul dg wdScale) fun d =>
      fL (bSlide z d nL 0 z bns vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL bns vns cns = some out) :
    bDec z out = muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [bForceN_eq, bForceN_eq, bForceL_eq] at h; revert h
  set nL := highdNatMin mL (Nat.add (altListLen cns) 1); set d := Nat.mul dg wdScale
  cases hp : bAllPos (bSlide z d nL 0 z bns vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold muxFastHornerStage
    rw [bDec_len z cns, bForceN_eq, bForceN_eq, ← bPrimMul0 z]
    exact bSlide_sound z d nL 0 z bns vns cns hp
private def bBind (x : Option (List ℕ)) (k : List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  match x with
  | none => none
  | some out => k out
private theorem bBind_sound {z dg mL : ℕ} {bns vns cns out : List ℕ}
    {kB : List ℕ → Option (List ℕ)} {kU : List ℤ → List ℤ}
    (h : bBind (bStg z dg mL bns vns cns) kB = some out)
    (hk : ∀ (mid : List ℕ), kB mid = some out → bDec z out = kU (bDec z mid)) :
    bDec z out = HighDForce.withForcedList
      (muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns)) kU := by
  unfold bBind at h; revert h; cases hs : bStg z dg mL bns vns cns with
  | none => intro h; cases h
  | some mid =>
    intro h; rw [bForceL_eq, ← bStg_sound z dg mL bns vns cns mid hs]; exact hk mid h
private def bStep (z mL : ℕ) (bns vns : List ℕ) : Option (List ℕ) :=
  bBind (bStg z 16 mL bns vns vns) fun c1 => bBind (bStg z 15 mL bns vns c1) fun c2 =>
  bBind (bStg z 14 mL bns vns c2) fun c3 => bBind (bStg z 13 mL bns vns c3) fun c4 =>
  bBind (bStg z 12 mL bns vns c4) fun c5 => bBind (bStg z 11 mL bns vns c5) fun c6 =>
  bBind (bStg z 10 mL bns vns c6) fun c7 => bBind (bStg z 9 mL bns vns c7) fun c8 =>
  bBind (bStg z 8 mL bns vns c8) fun c9 => bBind (bStg z 7 mL bns vns c9) fun ca =>
  bBind (bStg z 6 mL bns vns ca) fun cb => bBind (bStg z 5 mL bns vns cb) fun cc =>
  bBind (bStg z 4 mL bns vns cc) fun cd => bBind (bStg z 3 mL bns vns cd) fun ce =>
  bBind (bStg z 2 mL bns vns ce) fun cf => bStg z 1 mL bns vns cf
private theorem bStep_sound (z mL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL bns vns = some out) :
    bDec z out = muxFastHornerT16Step mL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h; unfold muxFastHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, vns => some vns
  | k + 1, mL, bns, vns =>
    match bStep z mL bns vns with
    | none => none
    | some vNext => bIter z k mL bns vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL : ℕ) (bns vns out : List ℕ),
    bIter z k mL bns vns = some out →
    bDec z out = muxFastIterFullT16 k mL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, vns, out, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, bns, vns, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL bns vns with
    | none => intro h; cases h
    | some vNext =>
      intro h; unfold muxFastIterFullT16
      rw [bForceL_eq, ← bStep_sound z mL bns vns vNext hs]
      exact bIter_sound z k mL bns vNext out h
private def fIter (k mL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 2000000000000000
  match uToNatHb hb with
  | none => muxFastIterFullT16 k mL hb v
  | some bns =>
    match bEnc z v with
    | none => muxFastIterFullT16 k mL hb v
    | some vns =>
      match bIter z k mL bns vns with
      | none => muxFastIterFullT16 k mL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL : ℕ) (hb v : List ℤ) :
    fIter k mL hb v = muxFastIterFullT16 k mL hb v := by
  unfold fIter; dsimp only; cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only; cases hv : bEnc 2000000000000000 v with
    | none => rfl
    | some vns =>
      dsimp only; cases hi : bIter 2000000000000000 k mL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 2000000000000000 k mL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 2000000000000000 v vns hv]
private def bSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    muxIntListEq (fIter steps maxLen hbF inF) outF
private theorem bSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bSlideChk at h; dsimp only [fL] at h
  rw [bForceL_eq, bForceL_eq, bForceL_eq, fIter_eq] at h
  exact muxIntListEq_eq_true.mp h
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private theorem pdim_r192_l1 :
    Nat.add (highdNatMin (Nat.mul 1 256) 192) 1 = 193 := by
  decide +kernel
private def phb_r192_0 : List ℤ :=
  altBuildHbFrom 256 192 295160800000 0 192
private def pvi_r192_0 : List ℤ := [rkmP 1000000000000000]
private def pvo_r192_0_p0 : List ℤ := pzig
  [204546, 1552814, 8292822, 35974398, 134449358, 447097828, 1350144164, 3754908532, 9716910544,
   23581794970, 54004906588, 117292425456, 242593601502, 479473540768, 908248231592,
   1653102111956, 2897390366758, 4899661687746, 8007909204110, 12668547335714, 19425883841868,
   28907716537404, 41793413976014, 58762605055764, 80425370334042, 107238310160110,
   139414521714750, 176838628470454, 218999807616732, 264955622408684, 313337062331052,
   362400629501700, 410127153550652, 454360226451632, 492970894473066, 524030674400822,
   545972956171292, 557723835987108, 558787263514568, 549275431388556, 529882549357904,
   501807326183328, 466635499225654, 426197754326724, 382419931498650, 337181532582100,
   292195651156620, 248919221610326, 208497736046866, 171744064292652, 139147327775516,
   110905280737698, 86972450396384, 67116273021126, 50974375204194, 38107653052974,
   28045556605590, 20321702527130, 14499407037562, 10187836467860, 7050181540990, 4805604048916,
   3226751723844, 2134476666694, 1391111518330, 893329297414, 565292000728, 352514067628,
   216646351152, 131227508660, 78347039726, 46107177234, 26747623520, 15296553222, 8624088546,
   4793604370, 2626982940, 1419429336, 756215918, 397252032, 205771974, 105103288, 52937738,
   26293070, 12878060, 6220106, 2962698, 1391618, 644600, 294436, 132622, 58898, 25782, 11122,
   4724, 1968, 798, 314, 114, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0]
private def pvo_r192_0_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvo_r192_0 : List ℤ := pvo_r192_0_p0 ++ pvo_r192_0_p1
private def phbv_r192_0_p0 : List ℤ := pzig
  [261751553025370, 368485532963568, 449234349740698, 516344824678140, 574622817566874,
   626544553872206, 673587728538294, 716719468223142, 756614529185874, 793766363915022,
   828549119704678, 861254735329168, 892116376984322, 921323906204402, 949034463450842,
   975379931931602, 1000472338471352, 1024407849258264, 1047269783700412, 1069130926615832,
   1090055329015780, 1110099729560328, 1129314690207856, 1147745513462784, 1165432990585112,
   1182414017440628, 1198722105607440, 1214387809783138, 1229439087707944, 1243901605226432,
   1257798996406954, 1271153086581892, 1283984084592984, 1296310749302330, 1308150534473354,
   1319519715372504, 1330433499844472, 1340906126135656, 1350950949356084, 1360580518158522,
   1369806642960076, 1378640456823832, 1387092469947234, 1395172618562460, 1402890308936502,
   1410254457060526, 1417273524535756, 1423955551093826, 1430308184130968, 1436338705585670,
   1442054056447116, 1447460859145566, 1452565438044778, 1457373838229978, 1461891842761800,
   1466124988546798, 1470078580957818, 1473757707322506, 1477167249385172, 1480311894835730,
   1483196147989422, 1485824339692240, 1488200636519154, 1490329049325432, 1492213441205304,
   1493857534906790, 1495264919746830, 1496439058066540, 1497383291262702, 1498100845428186,
   1498594836630976, 1498868275858842, 1498924073654148, 1498765044461230, 1498393910706740,
   1497813306631582, 1497025781891502, 1496033804941890, 1494839766221104, 1493445981145364,
   1491854692927200, 1490068075228504, 1488088234658228, 1485917213124032, 1483556990046396,
   1481009484443002, 1478276556890590, 1475360011370864, 1472261597006498, 1468983009692818,
   1465525893630188, 1461891842761800, 1458082402121072, 1454099069092524, 1449943294589640,
   1445616484152866, 1441119998970606, 1436455156825748, 1431623232969986, 1426625460927878,
   1421463033232384, 1416137102093304, 1410648779999796, 1404999140257912, 1399189217463848,
   1393220007913316, 1387092469947234, 1380807524233666, 1374366053985668, 1367768905114456,
   1361016886317026, 1354110769097054, 1347051287717640, 1339839139084130, 1332474982554894,
   1324959439677616, 1317293093848284, 1309476489889578, 1301510133545052, 1293394490884884,
   1285129987618550, 1276717008309164, 1268155895483640, 1259446948632090, 1250590423089190,
   1241586528789380, 1232435428886828, 1223137238230114]
private def phbv_r192_0_p1 : List ℤ := pzig
  [1213692021680398, 1204099792260604, 1194360509121732, 1184474075310780, 1174440335323016,
   1164259072419298, 1153930005686888, 1143452786819606, 1132826996590296, 1122052140985226,
   1111127646966334, 1100052857822848, 1088827028068988, 1077449317838722, 1065918786722118,
   1054234386980344, 1042394956067674, 1030399208378898, 1018245726128822, 1005932949256950,
   993459164234530, 980822491632486, 968020872286724, 955052051871276, 941913563658952,
   928602709212320, 915116536703928, 901451816511840, 887605013672842, 873572256698434,
   859349302164594, 844931494371056, 830313719223872, 815490351319246, 800455192987420,
   785201403780454, 769721418540356, 754006851741864, 738048385236824, 721835635793212,
   705356997863348, 688599455752246, 671548357673272, 654187141909048, 636497002199430,
   618456475196970, 600040926822430, 581221905786110, 561966320106824, 542235374056706,
   521983175119530, 501154877391160, 479684159071216, 457489718584790, 434470281013486,
   410497263563954, 385403607987336, 358966017281046, 330875125149304, 300681800579460,
   267691156641802, 230724386197734, 187465916465328, 131894280406748]
private def phbv_r192_0 : List ℤ := phbv_r192_0_p0 ++ phbv_r192_0_p1
private def pvm_r192_0_1 : List ℤ := pzig
  [1313853680930884, 1206734864180490, 780142918320532, 409915187680620, 185668512254946,
   74870684662624, 27432757924310, 9262299689674, 2911572092306, 858826612946, 239188468158,
   63212670558, 15918022524, 3832641058, 884931384, 196437198, 42014308, 8674990, 1732130,
   334954, 62816, 11436, 2020, 344, 56, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_0_2_p0 : List ℤ := pzig
  [370068355268948, 685063732170750, 892618826751820, 945251176340192, 862862131209826,
   701218689020486, 517771649654286, 352292450226268, 223160004163646, 132643877062524,
   74439500181088, 39640346690900, 20113197300030, 9757474837494, 4539257143258, 2030128028754,
   874802578186, 363901537302, 146381715854, 57026830822, 21545295078, 7903853624, 2818514554,
   977989930, 330506942, 108874102, 34986644, 10975474, 3363356, 1007428, 295114, 84586, 23730,
   6516, 1748, 454, 114, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]
private def pvm_r192_0_2_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_0_2 : List ℤ := pvm_r192_0_2_p0 ++ pvm_r192_0_2_p1
private def pvm_r192_0_3_p0 : List ℤ := pzig
  [43810354519714, 123258157462056, 244073588078376, 392782556978292, 544849779668184,
   672820850641418, 754874935600232, 780388837649552, 751061063167664, 678230745622966,
   578236235175144, 467768639920594, 360534471932528, 265677862966488, 187730653528992,
   127522419773386, 83457644400536, 52724582945490, 32208428840298, 19054415927760,
   10931576706672, 6089245294072, 3297003075576, 1736953607612, 891188288266, 445685832754,
   217421399332, 103537924394, 48162212358, 21897182956, 9736234388, 4235881246, 1804097772,
   752557002, 307587336, 123231624, 48413308, 18657374, 7055446, 2618924, 954490, 341656, 120138,
   41506, 14088, 4694, 1534, 488, 148, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_0_3_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_0_3 : List ℤ := pvm_r192_0_3_p0 ++ pvm_r192_0_3_p1
private def pvm_r192_0_4_p0 : List ℤ := pzig
  [2105055490940, 8047459067954, 21651630788428, 47339008199838, 89209540697722, 149648362647854,
   228063609627396, 320236601780240, 418585889991864, 513341916845498, 594326356372870,
   652847508718548, 683217449274800, 683548897995856, 655725461030114, 604667497011444,
   537167870145994, 460618632081648, 381902904626656, 306623037116614, 238719735704422,
   180441338504142, 132565240513550, 94756055743520, 65957986200648, 44748310109860,
   29612204201864, 19127548111358, 12067809644448, 7441204385794, 4486934958000, 2647141247446,
   1528758301876, 864638219752, 479126970578, 260233010802, 138590666582, 72396870124,
   37107790392, 18668386318, 9220913604, 4472892972, 2131403236, 997962518, 459237590, 207746086,
   92404474, 40420864, 17392172, 7362346, 3066668, 1257116, 507232, 201476, 78784, 30330, 11492,
   4280, 1562, 558, 192, 60, 16, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_0_4_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_0_4 : List ℤ := pvm_r192_0_4_p0 ++ pvm_r192_0_4_p1
private def pvm_r192_0_5_p0 : List ℤ := pzig
  [20288671236, 102712451366, 365915226198, 1059219350312, 2642447164362, 5867412940816,
   11834824331166, 21991731895000, 38037085898128, 61718471164692, 94530255957382,
   137355698761668, 190123012618604, 251557860602686, 319105818668456, 389068004846976,
   456948259709618, 517962761785424, 567625645288446, 602306922109592, 619665735548174,
   618889880725610, 600713417204876, 567227337489902, 521533611707402, 467313749828154,
   408387058163590, 348323042244932, 290151896099412, 236192819499848, 187997555930962,
   146389873229458, 111572405903498, 83270093043818, 60882788259160, 43626289773466,
   30648877989472, 21117760372340, 14275569365852, 9470834547500, 6168242500116, 3944890386632,
   2478129378734, 1529457879592, 927638393626, 553025609740, 324137800376, 186818468374,
   105900715820, 59053545242, 32399333364, 17492039236, 9294515502, 4861377032, 2503220860,
   1269124952, 633621740, 311550602, 150886258, 71984752, 33833420, 15667802, 7149362, 3214854,
   1424700, 622280, 267898, 113684, 47546, 19596, 7958, 3178, 1244, 474, 172, 56, 16, 2, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_0_5_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_0_5 : List ℤ := pvm_r192_0_5_p0 ++ pvm_r192_0_5_p1
private def pvm_r192_0_6_p0 : List ℤ := pzig
  [114750506, 717780450, 3159051926, 11295623868, 34803187720, 95430721906, 237669113962,
   545230771676, 1164069371322, 2331193224670, 4406221321300, 7899788712750, 13490183045370,
   22017932530958, 34448480242068, 51796314101892, 75010098915848, 104826740668908,
   141611307517526, 185207165771718, 234824351708300, 288992480730060, 345596934289660,
   402004624144860, 455270577963194, 502401989125428, 540645353052598, 567757274226330,
   582221556518754, 583383809813044, 571488147979626, 547615853431778, 513540168639882,
   471522135805660, 424078090014258, 373749636005844, 322902410658122, 273572137601184,
   227367252982960, 185428483016756, 148438543257636, 116670387732866, 90060347957132,
   68292761493358, 50884676854242, 37262194105700, 26823258585924, 18984720878420,
   13213863438582, 9046226072476, 6092453037096, 4037154787100, 2632599667368, 1689603583786,
   1067423004718, 663893076016, 406560117164, 245170890876, 145606361030, 85173873632,
   49078575644, 27859902502, 15581516008, 8586586930, 4662817382, 2495327160, 1316104042,
   684174942, 350579992, 177083148, 88178548, 43288050, 20951486, 9998250, 4704508, 2182744,
   998622, 450532, 200436, 87928, 38026, 16212, 6812, 2814, 1136, 448, 164, 54, 16, 2, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0]
private def pvm_r192_0_6_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_0_6 : List ℤ := pvm_r192_0_6_p0 ++ pvm_r192_0_6_p1
private theorem dk_r192_0_0 : bSlideChk 7 193 phbv_r192_0
    pvi_r192_0 pvm_r192_0_1 = true := by
  decide +kernel
private theorem dk_r192_0_1 : bSlideChk 7 193 phbv_r192_0
    pvm_r192_0_1 pvm_r192_0_2 = true := by
  decide +kernel
private theorem dk_r192_0_2 : bSlideChk 7 193 phbv_r192_0
    pvm_r192_0_2 pvm_r192_0_3 = true := by
  decide +kernel
private theorem dk_r192_0_3 : bSlideChk 7 193 phbv_r192_0
    pvm_r192_0_3 pvm_r192_0_4 = true := by
  decide +kernel
private theorem dk_r192_0_4 : bSlideChk 8 193 phbv_r192_0
    pvm_r192_0_4 pvm_r192_0_5 = true := by
  decide +kernel
private theorem dk_r192_0_5 : bSlideChk 7 193 phbv_r192_0
    pvm_r192_0_5 pvm_r192_0_6 = true := by
  decide +kernel
private theorem dk_r192_0_6 : bSlideChk 7 193 phbv_r192_0
    pvm_r192_0_6 pvo_r192_0 = true := by
  decide +kernel
private def phb_r192_1 : List ℤ :=
  altBuildHbFrom 256 192 294042740000 0 192
private def pvi_r192_1 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s0 pvo_r192_0
private def pvo_r192_1_p0 : List ℤ := pzig
  [53922133, 273056713, 955747055, 2664184559, 6256473917, 12740393431, 22859933885, 36436772333,
   51688457161, 64939875613, 71180406989, 65663133087, 46202116461, 15220132261, 19689646578,
   47566726454, 58095709874, 46371900222, 16119856620, 20671051957, 48226095081, 53975588389,
   34813118359, 715652624, 35877259448, 53597195622, 44954401956, 13946181054, 24156359781,
   50282126847, 51172554577, 26196477625, 12209716988, 44769238490, 55085797038, 37884473908,
   1602516250, 35897527949, 56220247031, 49423390489, 18692339953, 21416564184, 52076761124,
   59052898384, 39112440508, 1174160858, 38025947119, 61491282227, 59238180077, 32198596603,
   8624807774, 47017985844, 68133846364, 64057719878, 36337075952, 5146239931, 46146350509,
   73135490597, 77625686621, 58402969895, 21254580491, 23349247962, 63597815328, 89565198508,
   95436225700, 80320143622, 47721434178, 4084131388, 43029615091, 86610847679, 121377459103,
   144312144413, 154607832707, 153176520579, 141912200163, 122868741551, 97443492889,
   65571690767, 24854005127, 30529962994, 111321678612, 235330318256, 430471699356, 738929348790,
   1222610919384, 1969958569802, 3103981390998, 4791098522200, 7250013056922, 10759400187836,
   15662737610830, 22368212962066, 31341421146094, 43088638615044, 58128949872886,
   76954483842600, 99979502267212, 127480974944744, 159535365286756, 195958312004584,
   236255332718546, 279592189316946, 324792817814350, 370370580600822, 414595130072820,
   455592735625866, 491473124514298, 520471487459424, 541091096339832, 552230636940728,
   553281258352212, 544181485528194, 525423129451838, 498007410198800, 463356721250622,
   423192821104048, 379395916171974, 333860589638674, 288363727241996, 244456784093412,
   203390533186090, 166075618407298, 133077599093920, 104641383765892, 80737438013748,
   61121070228986, 45396345914438, 33077460433116]
private def pvo_r192_1_p1 : List ℤ := pzig
  [23642311010490, 16575138423720, 11397104939868, 7685292294330, 5081718098408, 3294567772586,
   2093990808558, 1304630702262, 796676782614, 476761081704, 279564995218, 160606926138,
   90381188608, 49814237262, 26885388454, 14206545200, 7348317508, 3719875164, 1842549428,
   892822012, 423121678, 196071610, 88818212, 39319682, 17006496, 7184316, 2963340, 1193030,
   468624, 179512, 67022, 24368, 8614, 2948, 968, 300, 82, 18, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvo_r192_1 : List ℤ := pvo_r192_1_p0 ++ pvo_r192_1_p1
private def phbv_r192_1_p0 : List ℤ := pzig
  [260760046221702, 367089721138334, 447532663889898, 514388926419702, 572446164070174,
   624171222440992, 671036199013474, 714004556999694, 753748496702898, 790759601428816,
   825410601213140, 857992328975134, 888737067684270, 917833959685180, 945439550196082,
   971685222855412, 996682580133688, 1020527423944530, 1043302758084666, 1065081091665486,
   1085926233074992, 1105894706048966, 1125036881018648, 1143397888883970, 1161018366388900,
   1177935069638822, 1194181383271020, 1209787746242836, 1224782010391434, 1239189744339962,
   1253034492631646, 1266337997925188, 1279120392511854, 1291400364195754, 1303195300625996,
   1314521415418820, 1325393858812072, 1335826815118112, 1345833588858222, 1355426681151262,
   1364617857676842, 1373418209326346, 1381838206484914, 1389887747746586, 1397576203747704,
   1404912456705936, 1411904936170220, 1418561651417934, 1424890220877212, 1430897898902780,
   1436591600191572, 1441977922088286, 1447063165000186, 1451853351113900, 1456354241584006,
   1460571352343432, 1464509968668430, 1468175158616008, 1471571785438580, 1474704519069232,
   1477577846761004, 1480196082954774, 1482563378442652, 1484683728886916, 1486560982748510,
   1488198848673802, 1489600902383506, 1490770593103502, 1491711249573464, 1492426085665916,
   1492918205645278, 1493190609093788, 1493246195528766, 1493087768733524, 1492718040822240,
   1492139636057400, 1491355094436726, 1490366875065180, 1489177359326216, 1487788853865320,
   1486203593397810, 1484423743351812, 1482451402356508, 1480288604584872, 1477937321959402,
   1475399466228604, 1472676890921406, 1469771393186086, 1466684715519698, 1463418547393566,
   1459974526779874, 1456354241584006, 1452559230986844, 1448590986700860, 1444450954143522,
   1440140533531130, 1435661080895952, 1431013909029156, 1426200288351818, 1421221447715944,
   1416078575137218, 1410772818460904, 1405305285962082, 1399677046881160, 1393889131895312,
   1387942533526312, 1381838206484914, 1375577067951718, 1369159997794198, 1362587838719284,
   1355861396360652, 1348981439299544, 1341948699017698, 1334763869780604, 1327427608448998,
   1319940534216166, 1312303228268206, 1304516233364030, 1296580053331448, 1288495152475182,
   1280261954892128, 1271880843688692, 1263352160094306, 1254676202464620, 1245853225167112,
   1236883437340994, 1227767001522418, 1218504032124914]
private def phbv_r192_1_p1 : List ℤ := pzig
  [1209094593763952, 1199538699413130, 1189836308378176, 1179987324073346, 1169991591582954,
   1159848894988862, 1149558954442420, 1139121422956820, 1128535882892922, 1117801842108310,
   1106918729735566, 1095885891551522, 1084702584894274, 1073367973079178, 1061881119258544,
   1050240979662342, 1038446396148534, 1026496087981744, 1014388642747304, 1002122506294178,
   989695971584408, 977107166308140, 964354039101324, 951434344177316, 938345624152810,
   925085190811970, 911650103508778, 898037144855004, 884242793277766, 870263191953642,
   856094113532574, 841730919949938, 827168516483822, 812401299039282, 797423093423144,
   782227085098870, 766805737565060, 751150697060556, 735252680734064, 719101344684926,
   702685127326912, 685991062268090, 669004553222342, 651709101207562, 634085971201142,
   616113781158132, 597767990312422, 579020255146922, 559837609031848, 540181403196356,
   520005918963652, 499256518184192, 477867130282532, 455756761651618, 432824520999318,
   408942312599938, 383943711016104, 357606265087390, 329621780387992, 299542827199676,
   266677150802968, 229850409344330, 186755801360060, 131394668943600]
private def phbv_r192_1 : List ℤ := phbv_r192_1_p0 ++ phbv_r192_1_p1
private def pvm_r192_1_1_p0 : List ℤ := pzig
  [1212855, 15830230, 133509953, 830173960, 3977700751, 14852404408, 42796825623, 91762876518,
   133939872791, 98517104616, 41001583374, 129600657899, 16169323429, 137446491636, 75184412172,
   111860496167, 233553853377, 219819440331, 104272264377, 69136993982, 296492480342,
   618327159000, 1111269754320, 1885751799820, 3091855533762, 4929282889586, 7657412848178,
   11602492232958, 17159517683706, 24786463348950, 34988679184604, 48291854105248,
   65203029227374, 86160726360480, 111477166183186, 141277521173430, 175442835162430,
   213564275588924, 254916445158758, 298456368989654, 342852478950768, 386544642577218,
   427832438311642, 464985019003052, 496362643873704, 520537850743476, 536403675486556,
   543257450311412, 540851394494960, 529405061541602, 509579149642358, 482414560409554,
   449244282152090, 411588196673600, 371041993772896, 329170997488466, 287418058334366,
   247032109882954, 209020978774938, 174129032327716, 142837637038474, 115384455739066,
   91796461854962, 71931191952678, 55521079818426, 42216534459116, 31624530886416,
   23340676083830, 16973829342368, 12163283414650, 8589191938808, 5977348467898, 4099608474622,
   2771245384092, 1846401613334, 1212590943758, 784976073886, 500919692904, 315111094920,
   195414241424, 119469601010, 72007514234, 42788466988, 25067570118, 14479090246, 8245549380,
   4629688994, 2562957572, 1398913158, 752837220, 399459296, 208979734, 107793844, 54819958,
   27487430, 13588608, 6622990, 3182460, 1507618, 704084, 324150, 147104, 65792, 28996, 12586,
   5374, 2250, 916, 362, 136, 44, 12, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_1_1_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_1_1 : List ℤ := pvm_r192_1_1_p0 ++ pvm_r192_1_1_p1
private def pvm_r192_1_2_p0 : List ℤ := pzig
  [2356068153, 12131877366, 38032664819, 80067186738, 109414167123, 74927731368, 27361418938,
   93270177753, 20338496634, 86705459588, 28985328087, 89803589223, 7847937560, 95083253350,
   43141654806, 69601492927, 101549242009, 21849718389, 84771729140, 123590954212, 68163088146,
   41390273917, 144729969419, 200883088359, 199332351433, 149550933243, 64590141143, 51137770024,
   207822712168, 432461351976, 770487851660, 1288813970488, 2080851320210, 3273142156760,
   5032728971458, 7574123060520, 11164522528552, 16125738876556, 22831168113126, 31696177283858,
   43160560094236, 57662306857144, 75602846433784, 97305100643070, 122967026189406,
   152614625065204, 186059459607110, 222866283001388, 262336295015066, 303510640296322,
   345197082585060, 386020447090788, 424494689112798, 459111681669908, 488439424106732,
   511220738552288, 526462929587692, 533509473349074, 532086534841588, 522319767974796,
   504720069815200, 480140293852622, 449707923352190, 414740977490916, 376655707647442,
   336874836488082, 296744260512864, 257464480464608, 220040841979706, 185254298703846,
   153652172374940, 125556536610198, 101086558684292, 80190459911854, 62682670089256,
   48282152364704, 36648616046680, 27414256720180, 20209617980492, 14683039379234,
   10513862257582, 7420070780440, 5161346581044, 3538635009578, 2391297837090, 1592806218194,
   1045751873788, 676760074868, 431701926352, 271442670172, 168235530086, 102778504194,
   61891391430, 36736595938, 21493371174, 12394879314, 7045410506, 3947203928, 2179636320,
   1186261902, 636310356, 336386034, 175256880, 89984314, 45530088, 22701476, 11153644, 5399678,
   2575644, 1210452, 560440, 255620, 114836, 50804, 22124, 9474, 3984, 1638, 654, 250, 90, 28, 6,
   0, 0, 0, 0, 0]
private def pvm_r192_1_2_p1 : List ℤ := pzig
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]
private def pvm_r192_1_2 : List ℤ := pvm_r192_1_2_p0 ++ pvm_r192_1_2_p1
private def pvm_r192_1_3_p0 : List ℤ := pzig
  [51927303461, 100674791400, 76682260391, 28337895765, 81882082604, 4279043058, 77764515895,
   6855121987, 74309420066, 26558404664, 63465376245, 55530053671, 32901014472, 76321566578,
   20853583454, 60819065847, 73094661773, 5577202661, 69208291292, 78949856684, 17335947608,
   61136644153, 94468669231, 60179544759, 16426615342, 87166510094, 113248856150, 83480254126,
   12980518626, 70200210377, 139713215625, 179643225531, 185835792621, 162130526017,
   114808328805, 47634575713, 41617768600, 163434426914, 338403715316, 599433078576,
   994877736314, 1592800793412, 2486292215608, 3799522375522, 5693972236752, 8374047371112,
   12091049619808, 17144277145268, 23877900735634, 32672282312308, 43928619515062,
   58046260480078, 75392747073638, 96267581349130, 120861787187082, 149216426447392,
   181184158803360, 216398524028118, 254255707719040, 293913008914814, 334307024523818,
   374192766972146, 412202711167194, 446922390013176, 476976947038768, 501121340899552,
   518325962321514, 527849452427890, 529291548531840, 522620724639200, 508173995845444,
   486629174168548, 458952708157346, 426328637365402, 390075849233594, 351561563691428,
   312118754434152, 272974146899410, 235191723368710, 199634595091366, 166945968025176,
   137548002474526, 111655852654564, 89303189478222, 70375088342696, 54644254001436,
   41807049510532, 31516556927870, 23410779537354, 17134970364482, 12357841378130, 8782010518740,
   6149454237882, 4242956673858, 2884609666338, 1932359363954, 1275457495176, 829497582616,
   531530273110, 335580139720, 208742266274, 127926310256, 77238357068, 45942760326, 26921432138,
   15540365758, 8836701006, 4949571758, 2730707320, 1483860556, 794146384, 418577118, 217267380,
   111053700, 55893986, 27698948, 13514468, 6491442, 3069428, 1428610, 654436, 295034, 130872,
   57104, 24500, 10328, 4272, 1724]
private def pvm_r192_1_3_p1 : List ℤ := pzig
  [674, 252, 86, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]
private def pvm_r192_1_3 : List ℤ := pvm_r192_1_3_p0 ++ pvm_r192_1_3_p1
private def pvm_r192_1_4_p0 : List ℤ := pzig
  [112518695137, 15843562897, 77370413952, 40536346786, 51544076573, 62357243711, 14360414248,
   67912402164, 30140442788, 44951614709, 62673801903, 4907045001, 57812308736, 54917450832,
   7773739613, 62166124145, 53351268407, 7937659350, 62123307846, 60058728636, 5143234318,
   54916145621, 71407697907, 32647510555, 31271608674, 74503794636, 68392001068, 18010806988,
   45022310483, 84279158759, 79162687315, 33358611717, 30511532850, 84081686486, 106130773816,
   89538802346, 41032883950, 24082420057, 88693710369, 139231942811, 168226522211, 174144028249,
   159446571749, 127969371341, 82421071503, 22351570387, 57467183478, 168541794026, 330412031270,
   572994883350, 939752489108, 1491787800278, 2312824116396, 3514857565192, 5244078969304,
   7686443012422, 11072030422972, 15677130797990, 21822812285534, 29868692685656, 40200740235238,
   53212258640072, 69277775799966, 88720351183862, 111773791269948, 138542316683404,
   168961216845912, 202762788678000, 239452212645312, 278297827697364, 318339442455722,
   358416867293560, 397218877855366, 433350533420944, 465414461087056, 492099706404760,
   512270357805268, 525045623230748, 529863505193994, 526521672586806, 515191401645548,
   496403264125004, 471006204511412, 440104373978328, 404978222161096, 366997631231664,
   327535186921700, 287887041319106, 249207388886110, 212460604990772, 178392890144114,
   147523126211256, 120150838870472, 96377849751956, 76139473880252, 59240963444888,
   45395232874306, 34258589028034, 25462080131842, 18637019915482, 13434117116820, 9536360185544,
   6666328096014, 4588912651548, 3110565705508, 2076164312424, 1364463541456, 882925324904,
   562510464666, 352828295028, 217872657674, 132442602058, 79253088218, 46681498520, 27063799950,
   15442659908, 8671962358, 4792320042, 2606016624, 1394375728, 734041370, 380158448, 193676010,
   97054608, 47835014, 23185880, 11051110, 5179014]
private def pvm_r192_1_4_p1 : List ℤ := pzig
  [2386152, 1080698, 481064, 210438, 90440, 38172, 15808, 6414, 2546, 980, 360, 124, 36, 8, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_1_4 : List ℤ := pvm_r192_1_4_p0 ++ pvm_r192_1_4_p1
private def pvm_r192_1_5_p0 : List ℤ := pzig
  [35228971835, 71751693293, 86275950803, 58161262375, 2524951500, 56205343568, 63748837810,
   20430613846, 37632624525, 62504195397, 34480840145, 21752802704, 58692436006, 46141837478,
   4451387137, 50925574245, 55771287829, 15908837497, 36446372718, 60460301320, 38279453342,
   12744919849, 54669097271, 57432904199, 19641355451, 32117296978, 62849126666, 52675294556,
   8611366758, 41558461657, 67507112891, 54359796461, 10036556513, 40833585930, 71325680000,
   66206762232, 28436292822, 23884968727, 67168370141, 83110960497, 65687537529, 22118148483,
   31425082512, 76661205172, 99533781732, 93916673406, 62059100922, 12429827592, 43700180137,
   95579977237, 135281348555, 158639391901, 164974722517, 156008741823, 134426835581,
   102430970753, 60441768253, 5933796207, 67741833256, 172764395002, 328715405950, 565129424526,
   924885917024, 1468524359302, 2279452799032, 3469869449842, 5187023121010, 7619204677248,
   11000603800478, 15613913765318, 21789367830244, 29898802457468, 40343428048282,
   53534303898592, 69865096541628, 89677549537932, 113221159434640, 140609733185972,
   171778640895966, 206447481477676, 244093345064426, 283939708481356, 324965128370742,
   365934290892202, 405451749639628, 442036069938994, 474209433084658, 500595426539428,
   520016133964010, 531579042229890, 534744863234072, 529369111724764, 515712987726674,
   494422427352184, 466477651998742, 433118682074594, 395754662996992, 355866179959066,
   314909886543294, 274233796656730, 235009707862816, 198186769734316, 164467566554698,
   134305616870890, 107921198371182, 85331071924414, 66387068080156, 50818565105952,
   38274496097990, 28361490567042, 20675887737964, 14828478922484, 10461810640090, 7260626352824,
   4956511646670, 3328046972204, 2197804731966, 1427410030860, 911676067504, 572578753248,
   353591595450, 214688246010, 128150474552, 75197277636, 43372713478, 24588074206, 13698876264,
   7499892948]
private def pvm_r192_1_5_p1 : List ℤ := pzig
  [4034503846, 2132275916, 1107046960, 564556068, 282756944, 139068600, 67157808, 31838666,
   14816330, 6766862, 3032662, 1333442, 575112, 243252, 100868, 40988, 16306, 6340, 2404, 878,
   306, 102, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_1_5 : List ℤ := pvm_r192_1_5_p0 ++ pvm_r192_1_5_p1
private def pvm_r192_1_6_p0 : List ℤ := pzig
  [2739248979, 9728278605, 23296414113, 42978645699, 63728607635, 76223106609, 70697923443,
   43164695589, 323013135, 41004507482, 61354083778, 49734404980, 11603942240, 32284211679,
   56863653681, 47598725741, 9888570673, 33508256890, 56086824106, 43976989164, 4692876778,
   37450707311, 56440013549, 40650196151, 146174766, 41033928280, 57307460662, 39304350740,
   2187593803, 42778209431, 58994556131, 41677974839, 680301839, 41256304436, 61363421662,
   49018284514, 10800652716, 33649156879, 62100948791, 60757584151, 30404417665, 14769147030,
   54381977652, 71203000082, 58281274994, 21089747610, 25576078827, 64007515249, 80355624177,
   69180413827, 34480825213, 12573002528, 57870378082, 88826322152, 97649380270, 82678814794,
   47822650730, 683408732, 49814809647, 95560994661, 130681731577, 152098641791, 159318406877,
   153698053699, 137454160853, 112623750559, 80079225271, 38587551793, 16190362442, 92929728572,
   206306765764, 379312411434, 646411511860, 1057697772390, 1684111419292, 2623655587892,
   4008359384556, 6011487196388, 8854193959506, 12810500603416, 18209158720654, 25430754218110,
   34898345938502, 47060129387788, 62363125987986, 81217758198854, 103954358675934,
   130774084965604, 161698202372268, 196521024330848, 234772693631564, 275698189479372,
   318258257919786, 361156306838076, 402892759435072, 441845172748062, 476369005983828,
   504910773452474, 526122963039180, 538968988783644, 542806850219752, 537442130941418,
   523144265228476, 500624184299520, 470975915874972, 435588795174456, 396040062333570,
   353979351000646, 311016734528240, 268624667186878, 228061644398822, 190322172574072,
   156114214634034, 125862158799784, 99730931507870, 77665365934964, 59438397685990,
   44701987366758, 33035654949202, 23988887335672, 17115181785928, 11996889136744, 8261165013038,
   5588143458270, 3712903785346, 2422948694312, 1552822131158, 977252607370]
private def pvm_r192_1_6_p1 : List ℤ := pzig
  [603890584332, 366380687098, 218214822146, 127574987618, 73202582418, 41220611988, 22775858178,
   12346671418, 6565680158, 3424532704, 1751656032, 878523440, 431959264, 208181274, 98326588,
   45503822, 20629348, 9159936, 3982650, 1695198, 706192, 287840, 114742, 44710, 17014, 6312,
   2276, 788, 260, 74, 16, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_1_6 : List ℤ := pvm_r192_1_6_p0 ++ pvm_r192_1_6_p1
private theorem dk_r192_1_0 : bSlideChk 7 193 phbv_r192_1
    pvi_r192_1 pvm_r192_1_1 = true := by
  decide +kernel
private theorem dk_r192_1_1 : bSlideChk 7 193 phbv_r192_1
    pvm_r192_1_1 pvm_r192_1_2 = true := by
  decide +kernel
private theorem dk_r192_1_2 : bSlideChk 7 193 phbv_r192_1
    pvm_r192_1_2 pvm_r192_1_3 = true := by
  decide +kernel
private theorem dk_r192_1_3 : bSlideChk 7 193 phbv_r192_1
    pvm_r192_1_3 pvm_r192_1_4 = true := by
  decide +kernel
private theorem dk_r192_1_4 : bSlideChk 8 193 phbv_r192_1
    pvm_r192_1_4 pvm_r192_1_5 = true := by
  decide +kernel
private theorem dk_r192_1_5 : bSlideChk 7 193 phbv_r192_1
    pvm_r192_1_5 pvm_r192_1_6 = true := by
  decide +kernel
private theorem dk_r192_1_6 : bSlideChk 7 193 phbv_r192_1
    pvm_r192_1_6 pvo_r192_1 = true := by
  decide +kernel
private def phb_r192_2 : List ℤ :=
  altBuildHbFrom 256 192 290173763157 0 192
private def pvi_r192_2 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s1 pvo_r192_1
private def pvo_r192_2_p0 : List ℤ := pzig
  [4, 10, 0, 8, 0, 6, 12, 2, 3, 7, 4, 0, 16, 18, 22, 24, 22, 20, 42, 34, 24, 46, 116, 288, 810,
   2282, 6370, 17314, 45592, 116518, 288732, 694010, 1618356, 3661866, 8041546, 17141118,
   35467836, 71241860, 138906618, 262876568, 482775352, 860182640, 1486405700, 2489937066,
   4041041960, 6349474312, 9650025162, 14170130694, 20075037402, 27390010984, 35906400050,
   45088685986, 54011071142, 61360891442, 65546859596, 64937321882, 58223990954, 44861770052,
   25484561434, 2157359274, 21682051211, 41694111949, 53521728173, 53944321371, 42012396303,
   19783225785, 7698852606, 33367471040, 49943907188, 52155279930, 38668725884, 12998857982,
   17123447777, 41947800695, 52897205859, 45705440113, 22303877185, 9417876620, 38125733082,
   53084870658, 48286803944, 25027222332, 8222590121, 38799011495, 54667616729, 49233053183,
   24172627505, 10962571944, 42353745706, 57366560012, 49670090814, 21915110516, 15175072229,
   46986401065, 60803575625, 50875398839, 20721071265, 18227565736, 51071167642, 65182948262,
   54988810608, 23980894642, 16705720749, 52486594193, 70623280663, 64647336207, 36391781767,
   4920642768, 46004721866, 73946313582, 80193742934, 62876740794, 26911261486, 17881726507,
   59834911075, 88629999955, 97717679769, 85430677083, 54722213145, 11850594487, 35455785122,
   79801242228, 115477791216, 139167992962, 150001231218, 149121859270, 139005318082,
   122764491482]
private def pvo_r192_2_p1 : List ℤ := pzig
  [103636826152, 84716668284, 68729902914, 57106559020, 46640624284, 20586268692, 70623122665,
   344970298435, 1045954211801, 2622138888015, 5821172695669, 11777092378257, 22055236065885,
   38609182962395, 63606302825787, 99098942956725, 146558114270231, 206338733819923,
   277194640641059, 355987784497607, 437722082448867, 515972465253075, 583684106406363,
   634211892621755, 662389756662785, 665392801992897, 643194966858711, 598521618674883,
   536320657343979, 462889237854587, 384862953040791, 308283549492639, 237914088184991,
   176888029370743, 126689675334133, 87393231535855, 58051113022009, 37120548144567,
   22842086531791, 13520459939799, 7694257059875, 4207391478413, 2209251016381, 1113109733947,
   537677976161, 248759065665, 110111605613, 46574268391, 18797729879, 7227914689, 2642830033,
   916963581, 301153993, 93350077, 27215613, 7431211, 1890429, 445083, 96145, 18829, 3281, 489,
   53, 1, 0]
private def pvo_r192_2 : List ℤ := pvo_r192_2_p0 ++ pvo_r192_2_p1
private def phbv_r192_2_p0 : List ℤ := pzig
  [257328998815426, 362259601440812, 441644086218924, 507620662579508, 564913990507066,
   615958457161730, 662206790354048, 704609776170118, 743830770187392, 780354887521212,
   814549953873028, 846702975419672, 877043178780954, 905757217590678, 932999577265054,
   958899912713380, 983568357955108, 1007099454354504, 1029575113554936, 1051066890602162,
   1071637754301556, 1091343484656798, 1110233789331426, 1128353205398748, 1145741834909644,
   1162435950337354, 1178468497048366, 1193869513488106, 1208666485022818, 1222884643846970,
   1236547224707698, 1249675684176568, 1262289889646734, 1274408283030562, 1286048023192692,
   1297225110412674, 1307954495583452, 1318250176382020, 1328125282270466, 1337592149879520,
   1346662390077486, 1355346947823210, 1363656155733848, 1371599782158994, 1379187074437360,
   1386426797915524, 1393327271227496, 1399896398265608, 1406141697215682, 1412070326980576,
   1417689111274520, 1423004560635196, 1428022892569912, 1432750050026134, 1437191718353904,
   1441353340908204, 1445240133422298, 1448857097268350, 1452209031708716, 1455300545230102,
   1458136066042840, 1460719851818948, 1463055998734946, 1465148449878692, 1467001003073578,
   1468617318168072, 1470000923834016, 1471155223912810, 1472083503345000, 1472788933715384,
   1473274578442870, 1473543397641572, 1473598252677334, 1473441910441642, 1473077047363026,
   1472506253174256, 1471732034452092, 1470756817944908, 1469582953702214, 1468212718018952,
   1466648316206340, 1464891885200078, 1462945496015850, 1460811156061248, 1458490811312460,
   1455986348363448, 1453299596354650, 1450432328787690, 1447386265232072, 1444163072929268,
   1440764368299236, 1437191718353904, 1433446642021804, 1429530611387652, 1425445052850292,
   1421191348202162, 1416770835633026, 1412184810660516, 1407434526989666, 1402521197303408,
   1397445993985666, 1392210049778504, 1386814458374458, 1381260274945006, 1375548516605806,
   1369680162819156, 1363656155733848, 1357477400462336, 1351144765294910, 1344659081850272,
   1338021145161670, 1331231713697454, 1324291509314618, 1317201217143596, 1309961485402232,
   1302572925136550, 1295036109885470, 1287351575266356, 1279519818477716, 1271541297715006,
   1263416431494912, 1255145597882974, 1246729133618770, 1238167333132226, 1229460447443884,
   1220608682941132, 1211612200021486, 1202471111593044]
private def phbv_r192_2_p1 : List ℤ := pzig
  [1193185481421070, 1183755322308454, 1174180594096382, 1164461201469968, 1154596991551888,
   1144587751265024, 1134433204442942, 1124133008664444, 1113686751785630, 1103093948139630,
   1092354034370430, 1081466364863044, 1070430206727420, 1059244734287902, 1047909023023724,
   1036422042898650, 1024782651009322, 1012989583472122, 1001041446456754, 988936706261498,
   976673678309388, 964250514926182, 951665191739418, 938915492512224, 925998992195232,
   912913037943806, 899654727804572, 886220886723284, 872608039463468, 858812379949292,
   844829736453630, 830655531938920, 816284738718948, 801711826436742, 786930702138368,
   771934640952094, 756716205540842, 741267152061178, 725578319804380, 709639500973510,
   693439286108222, 676964879426710, 660201876698926, 643133996034266, 625742748923156,
   608007034662864, 589902635391552, 571401580532506, 552471337226652, 533073765238738,
   513163747452486, 492687364640148, 471579415574480, 449759972351972, 427129471195236,
   403561501845786, 378891828670916, 352900927494172, 325284659072670, 295601480911302,
   263168246889836, 226826066994958, 184298492362198, 129665794660098]
private def phbv_r192_2 : List ℤ := phbv_r192_2_p0 ++ phbv_r192_2_p1
private def pvm_r192_2_1_p0 : List ℤ := pzig
  [116888, 804872, 3864450, 14929384, 49186314, 142610222, 371036254, 877578404, 1904077436,
   3813984050, 7084053972, 12235377586, 19678444678, 29470113950, 41025036172, 52881003908,
   62662664262, 67386638098, 64173633378, 51276128134, 29134106572, 1020755112, 27163424107,
   48178155119, 55636235855, 46456843623, 22618978727, 8699757034, 37022421148, 52117554218,
   47977498954, 25595639448, 6828831473, 36680004697, 51836218275, 45766333159, 20583180937,
   13457927978, 42037978642, 52827170988, 40910583636, 11132600592, 23801821681, 48746568891,
   52716233373, 33748048761, 157690788, 34460366534, 54362473348, 51190813922, 26098572764,
   10473560919, 43268850567, 58632330025, 50128582823, 21055255273, 17062524324, 49220636028,
   62884746854, 52743981758, 22502424038, 16788784031, 51007116045, 68093691281, 62145818401,
   35123980537, 4194851580, 43402777030, 70529201594, 77607138130, 62699704562, 29975645394,
   11924732931, 52526978709, 82289190799, 94744424955, 87576988523, 62560154039, 24590565249,
   19770869670, 63815223640, 101912719888, 130256254658, 147083190692, 152456814702,
   147751011822, 134986141054, 116123462380, 92357342254, 63364749534, 26391054214, 25024509791,
   102948119285, 227895189025, 432971525839, 769656241011, 1315492841831, 2183772115493,
   3534968148853, 5589204882989, 8638391025271, 13055917095611, 19301069263731, 27914751044363,
   39502933943821, 54704712427133, 74143104515681, 98358892011039, 127730729344959,
   162388139437347, 202127308627935, 246342081299819, 293983495825695, 343559994552615,
   393186802633603, 440687092104175, 483740140270161, 520063922491657, 547612876756475,
   564767338798131, 570490417272017, 564431279900597, 546960606222863, 519133245417887,
   482583283723121, 439365970208605, 391767664343071, 342108081491677]
private def pvm_r192_2_1_p1 : List ℤ := pzig
  [292558291782069, 244993610642403, 200893763619215, 161294918586559, 126790783551099,
   97574129532059, 73506516912339, 54202856656909, 39118434477097, 27628555574901,
   19094283346101, 12911137953183, 8540543432159, 5525942593645, 3496739022413, 2163655229441,
   1308906412255, 774012643613, 447326845019, 252611375053, 139360683847, 75091360411,
   39509280935, 20293583895, 10173096513, 4975772543, 2373826499, 1104297565, 500744055,
   221252789, 95229123, 39902705, 16268355, 6456821, 2496037, 935573, 335045, 111769, 33579,
   8661, 1747, 193, 38, 26, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def pvm_r192_2_1 : List ℤ := pvm_r192_2_1_p0 ++ pvm_r192_2_1_p1
private def pvm_r192_2_2_p0 : List ℤ := pzig
  [38, 314, 1946, 9836, 42618, 163576, 566388, 1793354, 5243904, 14266188, 36316440, 86892776,
   196101888, 418607844, 847041386, 1627382418, 2972165286, 5163811330, 8536924372, 13426894100,
   20075276078, 28492694130, 38298335290, 48578878928, 57831515150, 64063810050, 65104718524,
   59128129344, 45307209298, 24425858990, 790114789, 25852665163, 45326244593, 54201043935,
   49504125747, 31632065153, 4843916623, 23471994556, 44760030690, 52006298520, 42313655760,
   18341199998, 12119765485, 38532137265, 51282352015, 45338756735, 22448114851, 9145313014,
   37557388962, 51742012400, 45882494100, 21900388158, 11046699791, 40015439725, 53379324733,
   45544029811, 19326211185, 15036686062, 43902409250, 55665381340, 45420718234, 16958476240,
   18711702253, 47693721335, 58643256585, 47151105415, 17381918169, 19596227418, 50054636816,
   62728848406, 52881996708, 23862279152, 14283709803, 48486249155, 67193223373, 64161543347,
   40278757461, 2970054741, 36412641994, 66212272400, 77886678204, 68225133692, 39853837996,
   98398558, 41265473537, 74612871093, 92692184539, 91968695543, 72910488403, 39341072811,
   2811967710, 46968828998, 87190702934, 119076300564, 140170018354, 149917574280, 149286220534,
   140193062238, 124862303238, 105173363072, 81980061350, 54285635072, 18053356708, 35680379083,
   123839700357, 276043038537, 541650413483, 999699346297, 1772094439089, 3039952181583,
   5062220203601, 8194575389741, 12905238103857, 19782929853477, 29531100542287, 42942222437269,
   60846881350159, 84034969673081, 113150598254503, 148568057468343, 190262422394825,
   237693905121963, 289728261318775, 344615034841523, 400040307915251, 453260991902561,
   501314759689271, 541285743437855]
private def pvm_r192_2_2_p1 : List ℤ := pzig
  [570593987307425, 587269206210059, 590168733576041, 579106329625613, 554871781750299,
   519138458155401, 474273725039797, 423081842222569, 368517796659299, 313412098938999,
   260241093077359, 210966531883759, 166954708252161, 128972192408595, 97244633892839,
   71558639085279, 51384817830457, 36002110120265, 24608207686079, 16406791773707,
   10668068795573, 6763741668553, 4180626880617, 2518583470119, 1478536540969, 845592778315,
   471008501563, 255452923601, 134857481515, 69275412261, 34615513977, 16818471983, 7942386455,
   3643986921, 1623538109, 702082689, 294521259, 119785899, 47208291, 18016645, 6650921, 2369487,
   811329, 265291, 82115, 23799, 6379, 1557, 339, 63, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0]
private def pvm_r192_2_2 : List ℤ := pvm_r192_2_2_p0 ++ pvm_r192_2_2_p1
private def pvm_r192_2_3_p0 : List ℤ := pzig
  [4, 10, 0, 8, 6, 38, 94, 314, 1142, 4026, 13350, 41982, 124952, 353158, 950304, 2439940,
   5988856, 14074860, 31714550, 68591272, 142517298, 284684936, 547004162, 1011345846,
   1799561846, 3081656310, 5077547516, 8045921466, 12252609918, 17911989802, 25099482954,
   33642244588, 43008158694, 52227741496, 59894383150, 64288516242, 63653909638, 56615949086,
   42676322694, 22659526842, 1053548005, 24665367779, 43567727229, 53376149165, 51188413997,
   36714551443, 12862398949, 14560338392, 38135945576, 50890097272, 48545035470, 31212380760,
   3822914978, 25063073691, 45866813171, 51249872919, 38884775521, 12638627303, 18444349638,
   43180006952, 52303512286, 42054057890, 15850633536, 16721842775, 43371523665, 53761442911,
   43580681323, 16385152813, 17599339526, 45323821904, 55949311358, 45096259100, 16622979456,
   18786946217, 47687408155, 58999630189, 48221328095, 19111856157, 17747294344, 48910484462,
   63006297744, 54809022636, 26995177362, 10948897133, 46149741729, 66788855011, 65988144505,
   43872223657, 7258794239, 32739308398, 64268518014, 78245081834, 70771584156, 43869920030,
   4518225604, 37527160899, 72371653479, 92323636787, 93385669257, 75666914463, 42808177233,
   739569059, 43813972274, 84696274732, 117289140364, 138977010010, 149135703222, 148766502370,
   139931466212, 125125934374, 106660462738, 86026482080, 63090522162, 34796066586, 7156750797,
   80431626477, 219010287609, 484196920001, 980859332897, 1879655329387, 3444934711477,
   6066178502495, 10288260633001, 16832812028647, 26600225509627, 40640402490365, 60081411100657,
   86009807418791]
private def pvm_r192_2_3_p1 : List ℤ := pzig
  [119304814194091, 160440107113707, 209279573444681, 264903911358735, 325509711833655,
   388418694560077, 450220799033983, 507052215612303, 554982298882061, 590457782965649,
   610735442033809, 614230494573001, 600719690090755, 571363222817495, 528542833608547,
   475546984043585, 416160102756527, 354226029618475, 293253876646989, 236119392047139,
   184891372881695, 140786940765977, 104237395551847, 75031888097133, 52500788683287,
   35703472794097, 23593757178093, 15147222874273, 9445282431367, 5719112882009, 3361618056163,
   1917502745857, 1061061317531, 569372995239, 296159217073, 149255259043, 72844470229,
   34410716073, 15724173621, 6946125957, 2964260227, 1221123679, 485193179, 185776109, 68476739,
   24268431, 8256437, 2690591, 837337, 247863, 69433, 18293, 4495, 1015, 203, 31, 1, 0, 0, 0, 0,
   0, 0, 0, 0]
private def pvm_r192_2_3 : List ℤ := pvm_r192_2_3_p0 ++ pvm_r192_2_3_p1
private def pvm_r192_2_4_p0 : List ℤ := pzig
  [4, 10, 0, 8, 0, 6, 7, 10, 20, 18, 22, 28, 42, 86, 236, 696, 2144, 6384, 18364, 50782, 135320,
   347644, 861504, 2060918, 4762484, 10636752, 22971360, 47987254, 96994324, 189726292,
   359176390, 658085184, 1166807158, 2001501400, 3320410402, 5324497786, 8247237860, 12327517928,
   17760351406, 24623453518, 32784467930, 41803666776, 50858679162, 58727720362, 63870682244,
   64637585066, 59607330230, 48017163508, 30192693134, 7845474006, 15909054447, 36926732899,
   50826181759, 54084555883, 45180318977, 25424651607, 877741030, 27163324122, 46205144780,
   52214904610, 42830010090, 20269774600, 8893742765, 35493006069, 50643200003, 48842374107,
   30173820005, 680672233, 29427334770, 49267717406, 51292313138, 34298412584, 4193277944,
   27944703381, 49914988541, 53071734923, 35803760697, 4378940049, 29287441698, 52155406262,
   55137784618, 36725293712, 3693565854, 31426332973, 55143969251, 58199648707, 39125994661,
   4814447123, 32095195336, 57955947566, 63154311234, 45566902054, 11215105768, 28011498673,
   58619691461, 70165621921, 58665986829, 27688064281, 13081828302, 51130336930, 75062199442,
   77908692744, 58857497610, 23064408692, 20170198781, 60136670213, 87488210311, 96307092821,
   85044064741, 56288270175, 15637765607, 29886645820, 73424742064, 109503772666, 134724513928,
   147893436478, 149716560300, 142235166930, 128183151480, 110389319876, 91240730878,
   72055767048, 51959911490, 25476241146, 22480482699, 126130529005, 355323635805, 841526447425]
private def pvm_r192_2_4_p1 : List ℤ := pzig
  [1814950304887, 3652083646367, 6928668673867, 12467322742471, 21362663403287, 34962067169693,
   54779882105175, 82329707071439, 118874576557279, 165117305331313, 220878364635597,
   284829225975205, 354356908620115, 425624162024429, 493857745368087, 553849618034759,
   600603672027879, 630018399434583, 639476887349091, 628227220992063, 597477382509713,
   550188843739863, 490616286764777, 423690598361405, 354366388386161, 287049717297915,
   225191018353139, 171083215435419, 125858901659437, 89644401798167, 61809063753205,
   41246034629949, 26632280563397, 16634466731153, 10047185930903, 5866203823405, 3309553808485,
   1803361144633, 948583602107, 481395705207, 235553546481, 111054318863, 50408561785,
   22010209297, 9235954849, 3720639163, 1437206099, 531633313, 188038417, 63485067, 20417323,
   6239495, 1806293, 493455, 126601, 30319, 6717, 1353, 239, 33, 1, 0, 0, 0, 0]
private def pvm_r192_2_4 : List ℤ := pvm_r192_2_4_p0 ++ pvm_r192_2_4_p1
private theorem dk_r192_2_0 : bSlideChk 8 193 phbv_r192_2
    pvi_r192_2 pvm_r192_2_1 = true := by
  decide +kernel
private theorem dk_r192_2_1 : bSlideChk 8 193 phbv_r192_2
    pvm_r192_2_1 pvm_r192_2_2 = true := by
  decide +kernel
private theorem dk_r192_2_2 : bSlideChk 8 193 phbv_r192_2
    pvm_r192_2_2 pvm_r192_2_3 = true := by
  decide +kernel
private theorem dk_r192_2_3 : bSlideChk 7 193 phbv_r192_2
    pvm_r192_2_3 pvm_r192_2_4 = true := by
  decide +kernel
private theorem dk_r192_2_4 : bSlideChk 7 193 phbv_r192_2
    pvm_r192_2_4 pvo_r192_2 = true := by
  decide +kernel
private def phb_r192_3 : List ℤ :=
  altBuildHbFrom 256 192 291576000000 0 192
private def pvi_r192_3 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s2 pvo_r192_2
private def pvo_r192_3_p0 : List ℤ := pzig
  [3, 9, 0, 7, 3, 2, 5, 5, 15, 1, 2, 4, 6, 8, 5, 5, 15, 25, 19, 3, 17, 35, 23, 29, 13, 21, 37,
   35, 57, 103, 249, 667, 2111, 4163, 21201, 864, 298165, 748706, 5039741, 17295490, 74276239,
   240749876, 788040473, 2118180348, 5263861247, 10588283310, 18155491807, 22024085572,
   17203475097, 4343643565, 18840648442, 15339453581, 24491239913, 6846869302, 11007158736,
   26660713389, 61613731799, 61897067895, 32858801493, 4653463526, 35515000338, 54528362210,
   61930903556, 59224666868, 47774157276, 29121938652, 5670389754, 18987646943, 40319555645,
   53664232115, 55419930087, 44280687483, 22096648005, 6051887440, 32806085094, 50429490458,
   53203486850, 39560744274, 13124209204, 17937351077, 43286039833, 53896437035, 45463639443,
   20397490233, 12563819020, 41245479350, 54537699492, 46834883154, 20583944508, 14271199193,
   43955506643, 56320279963, 45908045969, 16462382061, 20310062028, 49366663060, 58509711850,
   43545549278, 10203606490, 28068620751, 55570913281, 60812622513, 41272995489, 4479832107,
   35018385798, 61501540666, 64329025852, 42076587386, 2980188612, 38357709763, 66575306389,
   71233563917, 50449799077, 11279876809, 33061076474, 67916234442, 82054640438, 71041274614,
   38164373852, 7094916467, 52266981227, 85577054777, 98956262501, 89630468107, 60092397523,
   16763316373, 32047982984, 78224980516]
private def pvo_r192_3_p1 : List ℤ := pzig
  [115442323072, 140014494624, 150978688786, 149585495860, 138476808478, 120876978450,
   100139109268, 79929609028, 65005839640, 61565210182, 74088649952, 92363709090, 58755334914,
   195997640925, 1056662261863, 3262953296185, 8058288354517, 17293895252911, 33411856749455,
   59228826223881, 97474506833611, 150108738140129, 217534042996551, 297905228537005,
   386774700721093, 477271228018425, 560886962094101, 628772998314219, 673275236854811,
   689343063074933, 675455490716443, 633834342695425, 569910394147599, 491208575813043,
   405956156493779, 321754209906227, 244588051223001, 178321651501693, 124675721020813,
   83575580170697, 53699053669751, 33057640344423, 19488560702265, 10995852889157, 5933461795579,
   3059510739041, 1506033916809, 706908418901, 315985243873, 134303175957, 54182358671,
   20705897549, 7477517951, 2544642089, 813296593, 243149529, 67663659, 17418653, 4115437,
   883115, 169639, 28553, 4061, 451, 27]
private def pvo_r192_3 : List ℤ := pvo_r192_3_p0 ++ pvo_r192_3_p1
private def phb_r192_4 : List ℤ :=
  altBuildHbFrom 256 192 273117166666 0 192
private def pvi_r192_4 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s3 pvo_r192_3
private def pvo_r192_4_p0 : List ℤ := pzig
  [4, 10, 0, 2, 12, 2, 4, 1, 0, 6, 14, 6, 6, 2, 5, 11, 3, 6, 19, 4, 30, 33, 292, 1351, 6264,
   27217, 112086, 435063, 1592294, 5481065, 17703196, 53488401, 150623468, 393528487, 948498878,
   2093631863, 4191425424, 7509173257, 11802188600, 15752437001, 16764976984, 12007211627,
   1139366474, 10832908256, 14675374241, 4944842246, 10511350672, 13810122959, 1525579735,
   15325930986, 4707064323, 14841997273, 7176324448, 15829860694, 5520802395, 18057916961,
   391390553, 20582725298, 15716449736, 7629050719, 20475683647, 6926374335, 23807419008,
   50918301036, 59642368478, 47983199082, 22967323812, 6100056939, 31985417605, 50544944789,
   59919436001, 59529380427, 49635315903, 31461730533, 7525260239, 18233557864, 40796236488,
   54977611888, 56766548962, 44726765178, 21005151988, 8737542455, 36048186963, 53377995697,
   52373737487, 38959566627, 1247330371, 14244057932, 66532413986, 32544433156, 58269734006,
   8597693810, 42746178175, 30755335705, 47572529363, 63586494711, 9310702589, 61142582160,
   69281359880, 24649764372, 13539779455, 13148122761, 13934542536, 38498084960, 40121067452,
   16350075038, 20618097465, 52411322961, 63515505805, 47958295501, 11611214187, 30531603886,
   60839359628, 66506910350, 44851598410, 4307074648, 39141947901, 68444256833, 72147617975,
   48610055119, 6283456167, 39759927118, 73472474010, 83411669546, 66290490140, 27494639108,
   21245984831, 65902130591]
private def pvo_r192_4_p1 : List ℤ := pzig
  [94381142297, 99621549707, 80813228617, 42727735437, 6286748282, 56824277946, 100679554188,
   132334101176, 149485267324, 152694673978, 144389489068, 127581804880, 104927208942,
   79142930204, 55915223326, 49130050698, 84047979702, 186196274062, 334290968122, 350715123130,
   287352312279, 2700866631967, 8856876735147, 21684489697009, 44902446976063, 82437206207777,
   137427717306061, 210990673528369, 301092985532137, 401959724582963, 504368731556301,
   596942095772957, 668212756510835, 708949537592337, 714092685044733, 683748508767675,
   622984153524511, 540537490691219, 446869058732909, 352124655643947, 264518674816567,
   189440570813813, 129328186994667, 84139237486175, 52144086358235, 30765263700629,
   17267975338089, 9211827293155, 4665372513295, 2240159654457, 1018189652455, 437230590419,
   176988373753, 67353941189, 24019442813, 7995473211, 2472391765, 705941139, 184693295,
   43827553, 9302077, 1730197, 273037, 34441, 2989]
private def pvo_r192_4 : List ℤ := pvo_r192_4_p0 ++ pvo_r192_4_p1
private def phb_r192_5 : List ℤ :=
  altBuildHbFrom 256 192 259232500000 0 192
private def pvi_r192_5 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s4 pvo_r192_4
private def pvo_r192_5_p0 : List ℤ := pzig
  [3, 9, 0, 2, 11, 1, 3, 2, 0, 2, 11, 9, 5, 3, 3, 6, 18, 1, 31, 214, 945, 4288, 18379, 74146,
   283041, 1019560, 3461789, 11058286, 33157637, 93056492, 243585677, 592094520, 1329068025,
   2735158418, 5110771049, 8553267002, 12559377827, 15628595976, 15361631877, 9681624092,
   826978766, 11114491883, 13463267818, 4213230797, 9509633655, 13103247318, 633799493,
   13167526743, 8089888234, 10101369988, 11815482151, 8011392691, 13244528564, 8556046740,
   12996823933, 12200217139, 9519316676, 17252219790, 777433975, 19938056679, 16192381583,
   5437715526, 20865112084, 13541371656, 12834880209, 41629734549, 57449139501, 54411593945,
   35764341853, 9082437949, 18172960426, 40707086754, 55455172168, 60891313000, 56508219874,
   42779217542, 21427763668, 4260720727, 29700850705, 49136393503, 58434526405, 52155857895,
   36478368373, 1837460133, 15676109452, 60794116470, 37378707790, 66107490922, 8689983938,
   14428379051, 23820982389, 71009663163, 53182155319, 2961694917, 5334245554, 21315536634,
   66579861770, 72002061706, 11722863788, 52182550405, 62090058825, 26951388887, 7362831020,
   11102937646, 11373681653, 36462097191, 42872455351, 23846648357, 11966926888, 47006463914,
   64034536116, 54160759366, 20692596508, 22470262153, 56998437079, 68084175047, 50731133587,
   11759043799, 33169916292, 66065247038, 73810946140, 53247976160, 11404235832, 33851390129,
   78502515187, 62094663371, 117390107167, 20101058614]
private def pvo_r192_5_p1 : List ℤ := pzig
  [55163813340, 11761567509, 73469382635, 94514326681, 80339508257, 42793927693, 6800618404,
   58001931616, 102198344406, 133742923932, 150412739698, 152987471404, 144079901940,
   126570782098, 102452082504, 73619050368, 46461495278, 40218410096, 92752297030, 246022354046,
   480952950836, 567679744732, 183991982025, 3238780885989, 11105391915765, 27384603241357,
   56406945558227, 102355083620687, 167950746387277, 253017363699321, 353404822111811,
   460774675852923, 563541082301565, 648890934888093, 705404563058183, 725538029224805,
   707231516067299, 654184319934375, 574774304979477, 480021036242199, 381238224013919,
   288021137148861, 207004839936835, 141521827048387, 92010122240635, 56862116848555,
   33382025132189, 18601497483839, 9828363133095, 4917723297005, 2326663035063, 1038946672889,
   436907588523, 172574974995, 63822970059, 22014385873, 7048479991, 2082321285, 563293915,
   138121065, 30274059, 5812309, 946431, 123203, 11081]
private def pvo_r192_5 : List ℤ := pvo_r192_5_p0 ++ pvo_r192_5_p1
private def phb_r192_6 : List ℤ :=
  altBuildHbFrom 256 192 257779000000 0 192
private def pvi_r192_6 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s5 pvo_r192_5
private def pvo_r192_6_p0 : List ℤ := pzig
  [4, 10, 4, 5, 12, 2, 4, 1, 0, 5, 4, 10, 10, 4, 6, 3, 86, 517, 2318, 9943, 40300, 154405,
   558314, 1904589, 6121514, 18506225, 52512716, 139487685, 345680002, 795856787, 1692977318,
   3303808975, 5857384848, 9304382719, 12962589072, 15264750255, 14054318750, 7848969761,
   2191246925, 11162364550, 12496687651, 3674994808, 8778725298, 12482681953, 2020975662,
   11284465742, 9718341355, 6090572155, 12937129488, 1521447364, 13861425871, 789303856,
   14419399170, 452500119, 15192586185, 2878708843, 15152027780, 9384546856, 11265380047,
   16803193873, 448685980, 18957682686, 17352104596, 2275897695, 19931442711, 18608292143,
   2597040942, 31186716132, 52224458434, 57080923414, 45519799406, 22873596800, 3916158235,
   28944898427, 48110061639, 59055014427, 60151517759, 51936761525, 33176207011, 11405961319,
   20432799030, 34271504708, 66420197010, 42627756668, 63623561954, 4040223660, 2869927733,
   32309724973, 71108503655, 40369717923, 29552891213, 19595803429, 39327717462, 66459752324,
   38609253766, 23812042250, 20342531400, 20208852805, 73950278271, 74930876367, 16909952407,
   42387086420, 55471686650, 27864727984, 3173769731, 9418788485, 9699068660, 34900202984,
   44914046864, 29956785830, 4393812115, 41684989055, 63545814925, 58669179955, 28047295589,
   15536081834, 53294821434, 68741455870, 55053948274, 17090868912, 27429561819, 67789524313,
   64901309971, 78343883911, 21894029668, 5697945177, 75782373370, 128758675522]
private def pvo_r192_6_p1 : List ℤ := pzig
  [48922475034, 31943973669, 28968841567, 24743865844, 73883923914, 92292155980, 78264359878,
   40388613382, 9922484751, 61576397621, 105487786331, 136697706727, 149512934879, 161616164869,
   119164843791, 164264645893, 89364672185, 10981201167, 10496226540, 23596605272, 110441849600,
   345001767886, 703281516846, 855787155074, 164201934407, 4340826856589, 14931521998963,
   36360692684655, 73544962075029, 130610021627905, 209230903388167, 307098602723631,
   417141108679219, 527997306873507, 625859009445303, 697293141942817, 732247442433687,
   726319972577497, 681602659965441, 605897995898943, 510647794242545, 408285602391729,
   309804029277121, 223127255399313, 152521551923439, 98924593254743, 60850485292331,
   35474044764623, 19581529723891, 10222740385659, 5040212281241, 2342770959927, 1024443008075,
   420345323291, 161335367217, 57703266729, 19141183417, 5854077579, 1638174351, 415236489,
   94023017, 18637313, 3131681, 420573, 39065]
private def pvo_r192_6 : List ℤ := pvo_r192_6_p0 ++ pvo_r192_6_p1
private def phb_r192_7 : List ℤ :=
  altBuildHbFrom 256 192 153731000000 0 192
private def pvi_r192_7 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r192_s6 pvo_r192_6
private def pvo_r192_7_p0 : List ℤ := pzig
  [3, 9, 3, 6, 11, 1, 3, 2, 0, 6, 1, 9, 9, 3, 9, 48, 329, 1588, 6845, 28072, 108673, 397226,
   1369609, 4450836, 13612203, 39106174, 105283501, 264828464, 620015735, 1344483106, 2683237097,
   4886555350, 8023881553, 11668953906, 14592842981, 14821701700, 10508987833, 1670485034,
   8242584594, 13020534985, 8029357624, 4039976546, 12480528603, 7685774958, 6328648608,
   12624551795, 1615236398, 12154559444, 7116108077, 10097391427, 9959881804, 8920149158,
   10956960313, 9656791985, 10278363756, 12388364628, 6980524949, 15949819401, 571218407,
   16608523148, 11874433886, 8921840349, 20730155451, 14126852997, 23073528552, 7876827309,
   11032187149, 11281506946, 38329962186, 55064582936, 55225885634, 40348901552, 16300868056,
   10330516373, 34085625261, 51615785471, 59951352047, 59827196433, 46701522001, 31566509549,
   2495138674, 14040776068, 59634571184, 40421772330, 73411965198, 29294646518, 10830118306,
   5043726951, 60127300717, 53414193613, 35882445159, 40459565937, 3438706516, 57310685132,
   52313170940, 31043356844, 31861118472, 12588924646, 44821544233, 83545852941, 56913903477,
   8133567700, 51342218296, 46255057078, 14232366982, 8476004847, 3904770365, 19924978478,
   41550960820, 42908856492, 19613963634, 18167707273, 52130977877, 65352824855, 50461360323,
   13054656419, 30922505242, 62205978384, 67472948494, 42373781716, 2939480622, 51693094345,
   54923936183, 101574089945, 3592886497, 19863564279, 30352092052, 122612033692]
private def pvo_r192_7_p1 : List ℤ := pzig
  [94921587070, 1994150196, 37017368505, 5219221875, 49276262338, 85623378116, 89641064258,
   64350579812, 19747862676, 32635820915, 81725675741, 122307083469, 139721756419, 169334825551,
   119394848813, 167319155707, 128086732597, 42158013401, 5658663, 5607888168, 43448393198,
   203974683596, 542555210082, 927075239832, 748555946390, 1472433477125, 8448942541435,
   24230329156177, 53791969311957, 101970473193097, 171852423315021, 263032939159079,
   370380438215899, 483930300917431, 590226561183773, 674923663956007, 725956254844499,
   736314377053455, 705559462020491, 639649265779029, 549220556373253, 446962780683165,
   344922250922099, 252462265141215, 175266711768215, 115382118562429, 71999422217757,
   42558963082233, 23809170461561, 12592136658317, 6287034960431, 2958245331749, 1309038416581,
   543367213731, 210916380383, 76269909101, 25572858771, 7903484677, 2234435941, 572077417,
   130814207, 26180757, 4440997, 601993, 56445]
private def pvo_r192_7 : List ℤ := pvo_r192_7_p0 ++ pvo_r192_7_p1
private def pwalks_r192 : List RkmSegWalk := [
  ⟨phb_r192_0, pvi_r192_0, pvo_r192_0⟩,
  ⟨phb_r192_1, pvi_r192_1, pvo_r192_1⟩,
  ⟨phb_r192_2, pvi_r192_2, pvo_r192_2⟩,
  ⟨phb_r192_3, pvi_r192_3, pvo_r192_3⟩,
  ⟨phb_r192_4, pvi_r192_4, pvo_r192_4⟩,
  ⟨phb_r192_5, pvi_r192_5, pvo_r192_5⟩,
  ⟨phb_r192_6, pvi_r192_6, pvo_r192_6⟩,
  ⟨phb_r192_7, pvi_r192_7, pvo_r192_7⟩
  ]
private theorem ptail_r192 : rkmAllTrueF [
    muxIntListEq phb_r192_0 phbv_r192_0,
    muxIntListEq phb_r192_1 phbv_r192_1,
    muxIntListEq phb_r192_2 phbv_r192_2,
    bSlideChk 5 193 phb_r192_3 pvi_r192_3 pvo_r192_3,
    bSlideChk 6 193 phb_r192_4 pvi_r192_4 pvo_r192_4,
    bSlideChk 2 193 phb_r192_5 pvi_r192_5 pvo_r192_5,
    bSlideChk 2 193 phb_r192_6 pvi_r192_6 pvo_r192_6,
    bSlideChk 1 193 phb_r192_7 pvi_r192_7 pvo_r192_7,
    rkmCheckRowFromWalks 256 32 192 [1, 1, 1, 1, 1, 1, 1, 1]
      [14758040, 14702137, 11026603, 1457880, 1638703, 518465, 515558, 153731]
      [50, 50, 38, 5, 6, 2, 2, 1]
      rkmMasksHiHiB_m256_r192 pwalks_r192 rkmRowHiHiB_m256_r192
  ] = true := by
  decide +kernel
private theorem pw_r192_0_1 :
    muxFastIterFullT16 14 193 phbv_r192_0
      pvi_r192_0 = pvm_r192_0_2 :=
  (muxFastIterFullT16_add 7 7 193 phbv_r192_0 pvi_r192_0).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_0)
      (bSlideChk_sound dk_r192_0_0)).trans
      (bSlideChk_sound dk_r192_0_1))
private theorem pw_r192_0_2 :
    muxFastIterFullT16 21 193 phbv_r192_0
      pvi_r192_0 = pvm_r192_0_3 :=
  (muxFastIterFullT16_add 14 7 193 phbv_r192_0 pvi_r192_0).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_0)
      pw_r192_0_1).trans
      (bSlideChk_sound dk_r192_0_2))
private theorem pw_r192_0_3 :
    muxFastIterFullT16 28 193 phbv_r192_0
      pvi_r192_0 = pvm_r192_0_4 :=
  (muxFastIterFullT16_add 21 7 193 phbv_r192_0 pvi_r192_0).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_0)
      pw_r192_0_2).trans
      (bSlideChk_sound dk_r192_0_3))
private theorem pw_r192_0_4 :
    muxFastIterFullT16 36 193 phbv_r192_0
      pvi_r192_0 = pvm_r192_0_5 :=
  (muxFastIterFullT16_add 28 8 193 phbv_r192_0 pvi_r192_0).trans
    ((congrArg (muxFastIterFullT16 8 193 phbv_r192_0)
      pw_r192_0_3).trans
      (bSlideChk_sound dk_r192_0_4))
private theorem pw_r192_0_5 :
    muxFastIterFullT16 43 193 phbv_r192_0
      pvi_r192_0 = pvm_r192_0_6 :=
  (muxFastIterFullT16_add 36 7 193 phbv_r192_0 pvi_r192_0).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_0)
      pw_r192_0_4).trans
      (bSlideChk_sound dk_r192_0_5))
private theorem pw_r192_0_6 :
    muxFastIterFullT16 50 193 phbv_r192_0
      pvi_r192_0 = pvo_r192_0 :=
  (muxFastIterFullT16_add 43 7 193 phbv_r192_0 pvi_r192_0).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_0)
      pw_r192_0_5).trans
      (bSlideChk_sound dk_r192_0_6))
private theorem pwalk_r192_0 :
    muxFastIterFullT16 50 193 phb_r192_0 pvi_r192_0 = pvo_r192_0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 50 193 h pvi_r192_0)
    (muxIntListEq_eq_true.mp
      (rkmHd ptail_r192))).trans
    pw_r192_0_6
private theorem pseg_r192_0 :
    muxFastIterFullT16 50
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_0 pvi_r192_0 = pvo_r192_0 := by
  rw [pdim_r192_l1]; exact pwalk_r192_0
private theorem pw_r192_1_1 :
    muxFastIterFullT16 14 193 phbv_r192_1
      pvi_r192_1 = pvm_r192_1_2 :=
  (muxFastIterFullT16_add 7 7 193 phbv_r192_1 pvi_r192_1).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_1)
      (bSlideChk_sound dk_r192_1_0)).trans
      (bSlideChk_sound dk_r192_1_1))
private theorem pw_r192_1_2 :
    muxFastIterFullT16 21 193 phbv_r192_1
      pvi_r192_1 = pvm_r192_1_3 :=
  (muxFastIterFullT16_add 14 7 193 phbv_r192_1 pvi_r192_1).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_1)
      pw_r192_1_1).trans
      (bSlideChk_sound dk_r192_1_2))
private theorem pw_r192_1_3 :
    muxFastIterFullT16 28 193 phbv_r192_1
      pvi_r192_1 = pvm_r192_1_4 :=
  (muxFastIterFullT16_add 21 7 193 phbv_r192_1 pvi_r192_1).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_1)
      pw_r192_1_2).trans
      (bSlideChk_sound dk_r192_1_3))
private theorem pw_r192_1_4 :
    muxFastIterFullT16 36 193 phbv_r192_1
      pvi_r192_1 = pvm_r192_1_5 :=
  (muxFastIterFullT16_add 28 8 193 phbv_r192_1 pvi_r192_1).trans
    ((congrArg (muxFastIterFullT16 8 193 phbv_r192_1)
      pw_r192_1_3).trans
      (bSlideChk_sound dk_r192_1_4))
private theorem pw_r192_1_5 :
    muxFastIterFullT16 43 193 phbv_r192_1
      pvi_r192_1 = pvm_r192_1_6 :=
  (muxFastIterFullT16_add 36 7 193 phbv_r192_1 pvi_r192_1).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_1)
      pw_r192_1_4).trans
      (bSlideChk_sound dk_r192_1_5))
private theorem pw_r192_1_6 :
    muxFastIterFullT16 50 193 phbv_r192_1
      pvi_r192_1 = pvo_r192_1 :=
  (muxFastIterFullT16_add 43 7 193 phbv_r192_1 pvi_r192_1).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_1)
      pw_r192_1_5).trans
      (bSlideChk_sound dk_r192_1_6))
private theorem pwalk_r192_1 :
    muxFastIterFullT16 50 193 phb_r192_1 pvi_r192_1 = pvo_r192_1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 50 193 h pvi_r192_1)
    (muxIntListEq_eq_true.mp
      (rkmHd (rkmTl ptail_r192)))).trans
    pw_r192_1_6
private theorem pseg_r192_1 :
    muxFastIterFullT16 50
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_1 pvi_r192_1 = pvo_r192_1 := by
  rw [pdim_r192_l1]; exact pwalk_r192_1
private theorem pw_r192_2_1 :
    muxFastIterFullT16 16 193 phbv_r192_2
      pvi_r192_2 = pvm_r192_2_2 :=
  (muxFastIterFullT16_add 8 8 193 phbv_r192_2 pvi_r192_2).trans
    ((congrArg (muxFastIterFullT16 8 193 phbv_r192_2)
      (bSlideChk_sound dk_r192_2_0)).trans
      (bSlideChk_sound dk_r192_2_1))
private theorem pw_r192_2_2 :
    muxFastIterFullT16 24 193 phbv_r192_2
      pvi_r192_2 = pvm_r192_2_3 :=
  (muxFastIterFullT16_add 16 8 193 phbv_r192_2 pvi_r192_2).trans
    ((congrArg (muxFastIterFullT16 8 193 phbv_r192_2)
      pw_r192_2_1).trans
      (bSlideChk_sound dk_r192_2_2))
private theorem pw_r192_2_3 :
    muxFastIterFullT16 31 193 phbv_r192_2
      pvi_r192_2 = pvm_r192_2_4 :=
  (muxFastIterFullT16_add 24 7 193 phbv_r192_2 pvi_r192_2).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_2)
      pw_r192_2_2).trans
      (bSlideChk_sound dk_r192_2_3))
private theorem pw_r192_2_4 :
    muxFastIterFullT16 38 193 phbv_r192_2
      pvi_r192_2 = pvo_r192_2 :=
  (muxFastIterFullT16_add 31 7 193 phbv_r192_2 pvi_r192_2).trans
    ((congrArg (muxFastIterFullT16 7 193 phbv_r192_2)
      pw_r192_2_3).trans
      (bSlideChk_sound dk_r192_2_4))
private theorem pwalk_r192_2 :
    muxFastIterFullT16 38 193 phb_r192_2 pvi_r192_2 = pvo_r192_2 :=
  (congrArg (fun h ↦ muxFastIterFullT16 38 193 h pvi_r192_2)
    (muxIntListEq_eq_true.mp
      (rkmHd (rkmTl (rkmTl ptail_r192))))).trans
    pw_r192_2_4
private theorem pseg_r192_2 :
    muxFastIterFullT16 38
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_2 pvi_r192_2 = pvo_r192_2 := by
  rw [pdim_r192_l1]; exact pwalk_r192_2
private theorem pwalk_r192_3 :
    muxFastIterFullT16 5 193 phb_r192_3 pvi_r192_3 = pvo_r192_3 :=
  bSlideChk_sound
    (rkmHd (rkmTl (rkmTl (rkmTl ptail_r192))))
private theorem pseg_r192_3 :
    muxFastIterFullT16 5
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_3 pvi_r192_3 = pvo_r192_3 := by
  rw [pdim_r192_l1]; exact pwalk_r192_3
private theorem pwalk_r192_4 :
    muxFastIterFullT16 6 193 phb_r192_4 pvi_r192_4 = pvo_r192_4 :=
  bSlideChk_sound
    (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl ptail_r192)))))
private theorem pseg_r192_4 :
    muxFastIterFullT16 6
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_4 pvi_r192_4 = pvo_r192_4 := by
  rw [pdim_r192_l1]; exact pwalk_r192_4
private theorem pwalk_r192_5 :
    muxFastIterFullT16 2 193 phb_r192_5 pvi_r192_5 = pvo_r192_5 :=
  bSlideChk_sound
    (rkmHd (rkmTl
      (rkmTl (rkmTl (rkmTl (rkmTl ptail_r192))))))
private theorem pseg_r192_5 :
    muxFastIterFullT16 2
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_5 pvi_r192_5 = pvo_r192_5 := by
  rw [pdim_r192_l1]; exact pwalk_r192_5
private theorem pwalk_r192_6 :
    muxFastIterFullT16 2 193 phb_r192_6 pvi_r192_6 = pvo_r192_6 :=
  bSlideChk_sound
    (rkmHd (rkmTl (rkmTl
      (rkmTl (rkmTl (rkmTl (rkmTl ptail_r192)))))))
private theorem pseg_r192_6 :
    muxFastIterFullT16 2
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_6 pvi_r192_6 = pvo_r192_6 := by
  rw [pdim_r192_l1]; exact pwalk_r192_6
private theorem pwalk_r192_7 :
    muxFastIterFullT16 1 193 phb_r192_7 pvi_r192_7 = pvo_r192_7 :=
  bSlideChk_sound
    (rkmHd (rkmTl (rkmTl (rkmTl
      (rkmTl (rkmTl (rkmTl (rkmTl ptail_r192))))))))
private theorem pseg_r192_7 :
    muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 1 256) 192) 1)
      phb_r192_7 pvi_r192_7 = pvo_r192_7 := by
  rw [pdim_r192_l1]; exact pwalk_r192_7
private theorem pwalks_snd_r192 :
    RkmSegWalksSound 256 192 [1, 1, 1, 1, 1, 1, 1, 1] [50, 50, 38, 5, 6, 2, 2, 1] pwalks_r192 := by
  dsimp only [RkmSegWalksSound, pwalks_r192]
  exact ⟨pseg_r192_0,
    ⟨pseg_r192_1,
    ⟨pseg_r192_2,
    ⟨pseg_r192_3,
    ⟨pseg_r192_4,
    ⟨pseg_r192_5,
    ⟨pseg_r192_6,
    ⟨pseg_r192_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 192)` (`FindAllJohnsonRampKickMuxHi256T4`). -/
theorem rkmTrajHiHiB_m256_r192 :
    rkmLo12EqHi 256 32 192 [1, 1, 1, 1, 1, 1, 1, 1]
      [14758040, 14702137, 11026603, 1457880, 1638703, 518465, 515558, 153731]
      [50, 50, 38, 5, 6, 2, 2, 1] rkmMasksHiHiB_m256_r192 rkmRowHiHiB_m256_r192 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r192
    (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl
      (rkmTl (rkmTl (rkmTl (rkmTl ptail_r192)))))))))
end
end QuantumComputation.Specs.DickeSol
