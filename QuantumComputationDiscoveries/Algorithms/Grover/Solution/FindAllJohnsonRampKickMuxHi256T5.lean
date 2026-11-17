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
# High-`m` Coupled Walk & Trajectory Part `5` (`FindAllJohnsonRampKickMuxHi256T5`)

Certifies `(m = 256, r = 128)` coupled `T_16` walk (`18705` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi256T5`). -/
def rkmWordBitsHi256T5 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi256T5 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi256T5`). -/
def rkmUnpackMaskHi256T5 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi256T5 n w ++ rkmUnpackMaskHi256T5 ns ws
/-- Mask segment `0` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s0 : List Bool := rkmUnpackMaskHi256T5 [6] [50]
/-- Mask segment `1` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s1 : List Bool :=
  rkmUnpackMaskHi256T5 [50, 50, 29]
    [855343801860094, 4132401, 536739840]
/-- Mask segment `2` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s2 : List Bool :=
  rkmUnpackMaskHi256T5 [50, 50, 25]
    [897236384874851, 8589934760, 30303656]
/-- Mask segment `3` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s3 : List Bool :=
  rkmUnpackMaskHi256T5 [50, 50, 26]
    [367374322630805, 1099511627860, 61693697]
/-- Mask segment `4` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s4 : List Bool :=
  rkmUnpackMaskHi256T5 [50, 50, 27]
    [70506183131180, 65536, 129048576]
/-- Mask segment `5` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s5 : List Bool :=
  rkmUnpackMaskHi256T5 [50, 43]
    [1125899906842623, 8796093022207]
/-- Mask segment `6` for `(m = 256, r = 128)`. -/
def rkmMkHiHiB_m256_r128_s6 : List Bool :=
  rkmUnpackMaskHi256T5 [50, 36]
    [1125899906842623, 68719476735]
/-- Prefix-kick masks for `(m = 256, r = 128)`. -/
def rkmMasksHiHiB_m256_r128 : List (List Bool) :=
  [rkmMkHiHiB_m256_r128_s0, rkmMkHiHiB_m256_r128_s1, rkmMkHiHiB_m256_r128_s2,
   rkmMkHiHiB_m256_r128_s3, rkmMkHiHiB_m256_r128_s4, rkmMkHiHiB_m256_r128_s5,
   rkmMkHiHiB_m256_r128_s6, []]
/-- Part `0` of `rkmRowHiHiB_m256_r128`. -/
def rkmRowHiHiB_m256_r128_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12, 52, 175, 438, 857, 1214, 1466, 1763, 2248, 2948,
   2913, 2197, 1686, 1064, 171, 28, 304, 1646]
/-- Part `1` of `rkmRowHiHiB_m256_r128`. -/
def rkmRowHiHiB_m256_r128_p1 : List ℕ :=
  [1085, 1824, 1956, 1348, 115, 1, 594, 1261, 1818, 1604, 790, 57, 299, 1453, 2191, 1634, 513, 0,
   515, 1575, 642, 3474, 51, 162, 1066, 1582, 90, 1752, 1417, 2030, 112, 467, 0, 39, 8, 46, 6, 987,
   2413, 796, 288, 1044, 340, 2936, 2819, 5889, 4979, 873, 605, 5484, 169324, 226562, 226100, 438,
   9435658, 51739115, 34353, 40519, 33696381, 289857153, 1138553743, 121138541, 2130943042,
   996223841960]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 128)`. -/
def rkmRowHiHiB_m256_r128 : List ℕ := rkmRowHiHiB_m256_r128_p0 ++ rkmRowHiHiB_m256_r128_p1
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T5`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T5 : (0 : ℕ) = 0 := rfl
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
private def pzeros : ℕ → List ℤ | 0 => [] | k + 1 => Int.ofNat 0 :: pzeros k
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws => (match Nat.mod w 2 with
    | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCatZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z | ws :: wss => pzig ws ++ pzigCatZ z wss
private theorem bDm {a b : ℕ} (h : muxNatListEq [a] [b] = true) : a = b :=
  (List.cons.inj (muxNatListEq_eq_true.mp h)).1
private def phb_0 : List ℤ := altBuildHbFrom 256 128 410791704545 0 128
private def phbv_0 : List ℤ := pzigCatZ 0
  [
   [297444966337484,418185148169636,509148436542444,584422488303216,649497930201122,
    707207239725260,759242649335850,806712912547450,850392408246796,890848008783014,
    928509937211536,963714187002904,996729334837752,1027774246403386,1057030197366960,
    1084649425683722,1110761323158302,1135477018390882,1158892835178292,1181092946981200,
    1202151445209990,1222133972543900,1241099028389064,1259099023695382,1276181141702166,
    1292388046659428,1307758472191864,1322327713444622,1336128041616362,1349189055367124,
    1361537980488760,1373199926867774,1384198109959096,1394554042585152,1404287701776804,
    1413417674507596,1421961285485784,1429934709619466,1437353071327980,1444230532514792,
    1450580370725318,1456415048774234,1461746276929918,1466585068580756,1470941790172488,
    1474826206092468,1478247519081612,1481214406674644,1483735054101302,1485817184023498,
    1487468083434142,1488694628001096,1489503304103390,1489900228775462,1489891167747916,
    1489481551749566,1488676491214756,1487480789521644,1485898954871034,1483935210900838,
    1481593506118512,1478877522222064,1475790681369772,1472336152448972],
   [1468516856385378,1464335470525884,1459794432119878,1454895940916378,1449641960886788,
    1444034221075650,1438074215574328,1431763202604856,1425102202693374,1418091995904162,
    1410733118096506,1403025856157040,1394970242149742,1386566046314342,1377812768831014,
    1368709630254884,1359255560507650,1349449186295078,1339288816797958,1328772427459640,
    1317897641665068,1306661710073156,1295061487325994,1283093405812936,1270753446114282,
    1258037103685826,1244939351269970,1231454596428666,1217576633484628,1203298589025630,
    1188612859966762,1173511042970112,1157983853781016,1142021034743108,1125611248384852,
    1108741954507472,1091399267620474,1073567790829268,1055230421329286,1036368121433646,
    1016959647461272,996981226705844,976406169903214,955204402843302,933341895633932,
    910779961028542,887474383287326,863374324883996,838420937851230,812545576229230,
    785667460264914,757690572079906,728499449644136,697953360505828,665878021059890,
    632053466553848,596195630964228,557927124549506,516728286769394,471849306964254,
    422137198901344,365648001459966,298586515589676,211145337718778]]
private def pvi_0 : List ℤ := [rkmP 1000000000000000]
private def pvm_0_1 : List ℤ := pzigCatZ 86
  [
   [162067878070538,368753314847566,589756315912708,765525249694268,855373740989022,
    849686777025512,765799722462474,635074071820768,489604899657542,353655737200988,
    240828649722458,155378741059482,95370472571938,55881610204550,31349127706816,16880069139376,
    8743031241690,4364334622836,2103167473426,979894452086,441992544946,193242302150,81980680718,
    33780736826,13532018556,5274065850,2001435572,740027248,266769968,93812566,32199734,10792592,
    3534114,1131096,353954,108336,32440,9500,2718,758,202,48,10]]
private def pvm_0_2 : List ℤ := pzigCatZ 58
  [
   [62718274912,304215272634,1036916801658,2867711685958,6825195177766,14437096908210,
    27699813004258,48888365837008,80190957545594,123207734414698,178411261014330,244704469245362,
    319212496636108,397402028236750,473545299055982,541458265337044,595370626828534,
    630751143266658,644924131774636,637366281363752,609649334912018,565071248131708,
    508076326101310,443591979909794,376404743815372,310668275803594,249593264464336,
    195325970306530,148988074744938,110830489786090,80448101842198,57008066164628,39456640572030,
    26684071712838,17640220364010,11403428349106,7210989496398,4461906424418,2702345476066,
    1602418286414,930544344530,529332135904,295016350464,161131484892,86261044432,45271663902,
    23296324508,11756117594,5818582756,2824903388,1345472080,628749436,288306984,129731658,
    57290760,24831424,10563888,4411370,1808300,727660,287438,111458,42420,15842],
   [5800,2076,724,242,74,20,2]]
private def pvo_0 : List ℤ := pzigCatZ 36
  [
   [118982,949830,5325336,24210828,94665936,328773432,1035061876,2995731420,8053165902,
    20265620068,48035511754,107780108672,229864678904,467582148872,909840903410,1697799298888,
    3044866801990,5258251020518,8758663703540,14093166463900,21934863008994,33062762473712,
    48316169608832,68520742795980,94387884089904,126394890191524,164659310323058,208825881698874,
    257986826631996,310655074157156,364804648120840,417983476487080,467492583176038,
    510614088091502,544860994629236,568216441019384,579330201141266,577645896255840,
    563442604696542,537787376945106,502408142455476,459507270388634,411542839947218,
    361006626599132,310225071464598,261203096126478,215522128165990,174294841873776,
    138171407181062,107386516201712,81833572074108,61152075755856,44815915160430,32213207566792,
    22711799507198,15707834951502,10657512912752,7094046228682,4632879640004,2968544707816,
    1866315192964,1151290820822,696867489244,413888723510],
   [241204280472,137927525924,77388172542,42603553992,23011833424,12194780324,6340068366,
    3233609020,1617810342,793932566,382138938,180385942,83499906,37898800,16864410,7356456,
    3145278,1317878,541060,217610,85716,33056,12474,4596,1648,572,188,56,12]]
private def phb_1 : List ℤ := altBuildHbFrom 256 128 409235636363 0 128
private def phbv_1 : List ℤ := pzigCatZ 0
  [
   [296318252621280,416601073817472,507219795644264,582208711275024,647037649109078,
    704528357285228,756366658131604,803657105233586,847171144151036,887473499935518,
    924992765968836,960063662987094,992953750309518,1023881064565942,1053026194756056,
    1080540802161734,1106553788454850,1131175861283370,1154502979572114,1176618997934888,
    1197597727125764,1217504561171234,1236397777883224,1254329589680328,1271347001072986,
    1287492514700156,1302804717464580,1317318770814324,1331066823705596,1344078362679490,
    1356380510397270,1367998281629854,1378954803892636,1389271508518040,1398968296864456,
    1408063685498462,1416574933502774,1424518154515362,1431908415664666,1438759825209228,
    1445085610399474,1450898186841264,1456209220444790,1461029682880010,1465369901324838,
    1469239603179386,1472647956324834,1475603605425630,1478114704706072,1480188947574836,
    1481833593421896,1483055491870262,1483861104728730,1484256525860574,1484247499155962,
    1483839434772252,1483037423785590,1481846251379072,1480270408676550,1478314103316912,
    1475981268850764,1473275573029946,1470200425049686,1466758981793660],
   [1462954153123192,1458788606243452,1454264769171600,1449384833324056,1444150755232754,
    1438564257392660,1432626828235558,1426339721217374,1419703952998518,1412720300688408,
    1405389298116512,1397711231082740,1389686131529614,1381313770567194,1372593650268954,
    1363524994142536,1354106736163070,1344337508238324,1334215625953862,1323739072422010,
    1312905480030258,1301712109851958,1290155828443730,1278233081708946,1265939865453358,
    1253271692195862,1240223553721972,1226789878777654,1212964485192562,1198740525590774,
    1184110425687670,1169065813976956,1153597441372484,1137695089073618,1121347462554870,
    1104542069119406,1087265075874604,1069501144248904,1051233236222718,1032442386223416,
    1013107431040434,993204688017832,972707568989698,951586113666268,929806421059702,
    907329950469712,884112653644554,860103885629154,835245021370740,809467674938610,
    782691372571262,754820460103520,725739912872450,695309531517106,663355692614110,
    629659264631692,593937257581010,555813711262966,514770933597738,470061954188766,
    420538154284860,364262936438962,297455477714902,210345524727992]]
private def pvi_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s0 pvo_0
private def pvm_1_1 : List ℤ := pzigCatZ 16
  [
   [198308362,51697017,163446969,18324025,144996432,124638766,35684109,159395143,137146505,
    1745837,135863594,186034702,130407066,9744494,116838419,205796349,241404875,230164603,
    187950741,127921425,51387083,61236046,265981352,687825786,1586729588,3484636624,7398525770,
    15251307802,30569819438,59627757988,113248665430,209542699168,377896650018,664546713910,
    1140006678104,1908463723334,3118954648110,4977674478274,7760152450550,11821306408694,
    17600660964874,25619451056518,36466139247190,50767271874592,69141763799052,92138705658906,
    120161534895180,153384598938488,191671258332792,234505076480176,280946638779390,
    329627581237178,378790221184216,426375922336938,470158611921340,507912726615090,
    537598564656962,557543820419496,566598941080384,564246309412102,550648896302920,
    526632066521998,493601301400432,453407155881838],
   [408175347968572,360123453747518,311385826619530,263865308710216,219124850796914,
    178325451662450,142210104586164,111127771338584,85087520252236,63831162188712,46912882022348,
    33776066176334,23820171416102,16453446321680,11130080165290,7372556971272,4781465707146,
    3035757601508,1886564231362,1147373756442,682797908872,397514592436,226360943130,126050696504,
    68625528370,36518872574,18990108768,9647069686,4786216798,2318357916,1096004496,505510406,
    227386518,99709112,42603568,17729182,7181860,2830392,1084556,403792,145956,51174,17378,5700,
    1800,540,150,34,6]]
private def pvm_1_2 : List ℤ := pzigCatZ 3
  [
   [4348790,15058868,35563624,65646956,99328726,124885934,128591576,101278958,44632376,26597337,
    88663585,118158465,102515453,46524901,28606186,93538784,122762466,104880512,46816230,29524067,
    96243699,130037365,120115069,70824281,1258856,73912060,126677668,146520332,130281102,83849538,
    19035628,50416469,112357277,158486449,185110417,192654505,184426231,165146865,139631013,
    111780781,83824137,55466385,22257341,28171980,124613986,330583852,782007790,1761964294,
    3843835436,8156363986,16858090102,33957834582,66684375500,127690800496,238469077456,
    434429468604,772134603312,1339120517456,2266524756758,3744309354850,6038164328958,
    9506198987684,14612343985266,21932172534778],
   [32145898185728,46013010478660,64323793428516,87825183005268,117122187454396,152561188489278,
    194107184521192,241232318426284,292836462174098,347220835049596,402131639858570,
    454882325948802,502551181425124,542237422437072,571346447839104,587866321192874,
    590595167596810,579284177812716,554672833995962,518409722156930,472870591056062,
    420901445665934,365525197913940,309653775293514,255843347282556,206119885243484,
    161888258877898,123923614399698,92431703924010,67157059348412,47515132371934,32726294843748,
    21934609187178,14300861506878,9065906950950,5585728358918,3343138988236,1942691862454,
    1095411965134,598966598228,317382247700,162852299902,80850440642,38802511042,17984525440,
    8041333530,3464368382,1436165310,572027748,218538446,79929040,27925246,9296296,2940140,880364,
    248528,65800,16228,3686,754,134,16]]
private def pvo_1 : List ℤ := pzigCatZ 0
  [
   [116,804,3782,14482,47350,136714,355270,842292,1839258,3724768,7031508,12419406,20575928,
    32023964,46842938,64350884,82843116,99517244,110712314,112531958,101808020,77214934,40218204,
    4511563,49514021,85875001,105281349,102305481,76256185,31958761,20921964,69985812,103145420,
    111799406,93218062,51424024,3721251,58988571,101121153,120118915,111591241,77604713,25901351,
    32189512,84508064,120748026,134434974,123829166,91701266,44209076,10725631,65101291,112217823,
    147537413,168969675,176661829,172457673,159212841,140130509,118229827,95998907,75230281,
    56989267,41607345],
   [28453233,14835447,7709472,64294818,225916774,682868192,1918263010,5095331968,12875004654,
    31049449214,71631013162,158375566946,336104892308,685513091358,1345185928450,2542013261426,
    4629656551922,8131930045108,13783815380346,22557823361250,35658737709926,54467363038382,
    80416117342016,114788215976460,158448493151556,211535903563146,273170804797128,
    341247131857054,412382690686618,482084178231548,545146272885554,596252119640006,
    630688121030694,645044996604176,637763942655562,609408904403002,562600543987816,
    501621052346172,431771468853706,358614455040610,287251934807664,221766054220564,
    164902240043470,118011125088472,81209788241968,53685885712044,34056659156676,20706014121476,
    12048540184484,6699198903372,3552788530418,1793336749776,859493733450,390008731082,
    166990827922,67195906314,25286460336,8844526378,2853151842,840237540,222755224,52092494,
    10405520,1673954],
   [187802]]
private def phb_2 : List ℤ := altBuildHbFrom 256 128 409235636363 0 128
private def phbv_2 : List ℤ := pzigCatZ 0
  [
   [296318252621280,416601073817472,507219795644264,582208711275024,647037649109078,
    704528357285228,756366658131604,803657105233586,847171144151036,887473499935518,
    924992765968836,960063662987094,992953750309518,1023881064565942,1053026194756056,
    1080540802161734,1106553788454850,1131175861283370,1154502979572114,1176618997934888,
    1197597727125764,1217504561171234,1236397777883224,1254329589680328,1271347001072986,
    1287492514700156,1302804717464580,1317318770814324,1331066823705596,1344078362679490,
    1356380510397270,1367998281629854,1378954803892636,1389271508518040,1398968296864456,
    1408063685498462,1416574933502774,1424518154515362,1431908415664666,1438759825209228,
    1445085610399474,1450898186841264,1456209220444790,1461029682880010,1465369901324838,
    1469239603179386,1472647956324834,1475603605425630,1478114704706072,1480188947574836,
    1481833593421896,1483055491870262,1483861104728730,1484256525860574,1484247499155962,
    1483839434772252,1483037423785590,1481846251379072,1480270408676550,1478314103316912,
    1475981268850764,1473275573029946,1470200425049686,1466758981793660],
   [1462954153123192,1458788606243452,1454264769171600,1449384833324056,1444150755232754,
    1438564257392660,1432626828235558,1426339721217374,1419703952998518,1412720300688408,
    1405389298116512,1397711231082740,1389686131529614,1381313770567194,1372593650268954,
    1363524994142536,1354106736163070,1344337508238324,1334215625953862,1323739072422010,
    1312905480030258,1301712109851958,1290155828443730,1278233081708946,1265939865453358,
    1253271692195862,1240223553721972,1226789878777654,1212964485192562,1198740525590774,
    1184110425687670,1169065813976956,1153597441372484,1137695089073618,1121347462554870,
    1104542069119406,1087265075874604,1069501144248904,1051233236222718,1032442386223416,
    1013107431040434,993204688017832,972707568989698,951586113666268,929806421059702,
    907329950469712,884112653644554,860103885629154,835245021370740,809467674938610,
    782691372571262,754820460103520,725739912872450,695309531517106,663355692614110,
    629659264631692,593937257581010,555813711262966,514770933597738,470061954188766,
    420538154284860,364262936438962,297455477714902,210345524727992]]
private def pvi_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s1 pvo_1
private def pvm_2_1 : List ℤ := pzigCatZ 0
  [
   [543259,2330606,5795015,8332722,2665337,17183755,41740088,43248611,6448676,34677036,25912889,
    22577697,36370332,235564,10189537,31293401,49972898,20755009,3658665,3775612,5502906,6720877,
    18315818,82183587,60804638,58418746,21268033,2053113,85144291,61359791,73983243,25050481,
    132242856,77903858,73364680,60508968,19413921,131197824,125982419,94596281,106538161,39458089,
    42075590,16374201,97138462,46587707,278649288,438431865,844445226,931628309,1542577322,
    1744614977,1925078608,1458913283,322969318,476396758,1369494101,1644230130,410678937,
    965363623,1569550640,640691879,843239339,1446009790],
   [417780075,1159977421,1481259372,802209180,1619373357,188486923,1602240284,229562635,
    1641156835,312904948,1745449912,86815881,1958354031,733494083,1652954810,1699249676,591589759,
    2252777487,1377221457,1012407220,2592034882,2104474546,58232728,2181355205,3543325643,
    3739256605,3107723165,2421638931,2818622879,6191056103,12653315579,14594808053,33131502538,
    257395064308,1005432333142,2958412861028,7499486506394,16686905462072,33876643357226,
    62668272967178,107791530797592,171675009293880,256266836475188,357368476817462,
    468511246992438,576973725629284,668340555793750,729176967375096,748310807832180,
    722717090550336,656616694110374,559872607559728,447645009391170,335268253435230,
    234170378649782,151836705731798,91328983094734,50855213747558,25845012054038,11622248567696,
    4426505451858,1350696907412,303735685350,41823692586],
   [1273153888]]
private def pvm_2_2 : List ℤ := pzigCatZ 0
  [
   [26470140,24881639,14052677,14769365,62353182,21227807,14172485,27745271,31793774,2991700,
    19196670,10540511,68741421,54067046,41924276,49334005,3815654,20369666,68031725,89766910,
    43585849,11783102,35630528,156098085,243572890,290033875,449477680,727597263,1003999812,
    1272470649,1511342154,1517787367,1216628320,720212825,21590594,731658144,1185421025,
    1159281314,557761977,321309043,974892228,1196232967,524762828,630421086,1079604455,825354224,
    69148402,991487967,922047124,183515387,938239619,1018453608,75143007,970064179,1073382978,
    390263686,1094471579,580705392,681183130,1094779845,58048989,946861998,692027911,612836295],
   [1103790304,100853732,1298984553,333115816,1354592248,474848931,907252469,876485264,1015039252,
    1214409329,504934453,342096866,1900699888,2990950271,2788492812,4635814411,10044399918,
    15443662543,20735703570,31327384897,47003603226,61855603503,78845475826,99978731195,
    117353699310,124706049165,124674829992,110839770803,75237567106,27047027725,25626548811,
    78852333072,111293830585,107023888268,72348226813,7224711916,66933413478,108635362079,
    106892415058,50127734087,37913879975,105094272044,128205269785,21170005696,44449613008,
    3854564501,435047364574,202778537222,1259107061615,4098874707189,6664707628243,588912347278,
    35562613551336,119811113468242,268901190957294,475076312891876,697423474123138,
    872706347652684,940852164136676,874523577128360,696840508062682,469931864600340,
    261035156870226,112619536155986],
   [32501690463372]]
private def pvo_2 : List ℤ := pzigCatZ 0
  [
   [54770468,426312,9123857,30401978,4674381,28581614,28150706,2456306,37092694,302603479,
    546465540,818943521,1034924370,1266104921,1482700246,1320279441,863339864,188481063,653318179,
    1143428002,1051371257,496372880,341019894,958973623,980627032,394845465,520611009,1046252710,
    732996547,107663423,885776686,946287779,110038346,810446674,931947267,207745300,720804312,
    962517761,181968104,796035340,872804079,24740256,806389920,775873107,118152565,920276696,
    652028581,463668221,1080963964,305588449,816009805,664446520,525211702,1388549067,1101327616,
    336913061,993012958,3200590767,5381816238,7111422677,9285852960,13721199377,20911704126,
    29213014921],
   [37959978400,48202851251,61672301642,76995878603,90327204084,100589298551,107772766354,
    111020382487,105626695404,88605119683,62594261250,30042179133,6785939177,45095329268,
    77601135413,95206439856,93591970813,73744766656,38324326805,8881315617,56225399146,
    88436427603,95301358222,75181910313,33397933256,22591494542,74156388403,98969393914,
    87309418031,44980975506,16105355658,75599510687,105131228072,87541611275,31750610346,
    38588326814,96030624563,110763003374,67306368553,11473912477,85189479526,119747843587,
    90694911624,4944056533,82297492609,123619048418,114548823873,31382912452,142828845002,
    212251438985,95479307643,183140088124,772312250490,68126435403,3754697123045,1767108362845,
    12803726980290,18784123070828,27648072543209,109816030247925,58188775995269,331636932734072,
    969114035297472,1358837544579242],
   [1042904863685738]]
private def phb_3 : List ℤ := altBuildHbFrom 256 128 324642500000 0 128
private def phbv_3 : List ℤ := pzigCatZ 0
  [
   [235066279128426,330485427194864,402372344624898,461860294547874,513288436627180,
    558895235182038,600018036050708,637533070444456,672052318339886,704023770420754,
    733787425491148,761608814132754,787700188453096,812234514710022,835355052334346,
    857182112690288,877817952173172,897350394042782,915855561545682,933399975700682,
    950042189834026,965834080366928,980821878499398,995047003816142,1008546744520886,
    1021354817528142,1033501833438410,1045015685473562,1055921877076082,1066243799621422,
    1076002969243022,1085219229906178,1093910928435434,1102095066090498,1109787430418122,
    1117002710423688,1123754597563324,1130055874623400,1135918494204834,1141353648246742,
    1146371829793382,1150982888019578,1155196077374140,1159020101572114,1162463153059512,
    1165532948484662,1168236760635174,1170581447236106,1172573476951300,1174218952884206,
    1175523633835624,1176492953542356,1177132038092102,1177445721685094,1177438560891430,
    1177114847534338,1176478620313144,1175533675265298,1174283575154028,1172731657856792,
    1170881043819592,1168734642632940,1166295158777002,1163565096575740],
   [1160546764392770,1157242278095036,1153653563804044,1149782359948326,1145630218624912,
    1141198506271682,1136488403646540,1131500905103426,1126236817148782,1120696756255664,
    1114881145905602,1108790212820780,1102423982340880,1095782272889820,1088864689467514,
    1081670616090414,1074199207091742,1066449377177746,1058419790119452,1050108845940222,
    1041514666436950,1032635078846768,1023467597440672,1014009402789670,1004257318406886,
    994207784418846,983856827859550,973200029109398,962232483915052,950948760322302,
    939342849727602,927408111099506,915137207231316,902522031651628,889553624527364,
    876222075528212,862516411160066,848424463488920,833932716425790,819026124773330,
    803687899970190,787899254804442,771639097152412,754883659818614,737606049491552,
    719775692222672,701357644978428,682311731627114,662591445506056,642142536746628,
    620901166326040,598791452760472,575722148145738,551582033743800,526233375845240,
    499502339617546,471164431958732,440921407437334,408362586151388,372895404024310,
    333608673393542,288966111049994,235968428317428,166864981794828]]
private def pvi_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s2 pvo_2
private def pvo_3 : List ℤ := pzigCatZ 0
  [
   [51265893,11896967,29274059,363502,24117530,11707769,112635982,414894895,794587080,1149644749,
    1238931420,1453416353,1282869468,827532687,29919535,796778744,1154853225,987872390,168039281,
    684898897,1024427542,765555785,68989203,871128712,995596791,385318028,540619604,959087463,
    512178132,354473598,960113971,498726628,745667328,1023482841,427266720,634909284,858922263,
    284343548,550465004,1290295009,511229880,31861400,219548343,184719152,564624701,869609238,
    483300909,388765010,427810591,547034419,556497983,961381245,155668052,2374490041,3669554272,
    8782149605,15576097744,18195395339,24494874522,33557316019,48289913654,53885773355,
    70184045086,82215605047],
   [96132949228,104439671647,107642049214,105385537505,96646786700,77929230839,49086433984,
    14370659543,21228606291,54057410148,81094220561,95061997412,90438946743,67728169206,
    32283456579,7984829607,47829362326,80910170791,97078054716,82073412003,32617266974,
    20365203472,54340763973,97909124586,90648886057,61007750070,4311724219,51233807421,
    90985490608,99031898251,66900417892,4115907631,60959218943,101221252040,102748642627,
    64906901888,5737410029,35305011203,27109551894,11599110040,12772696147,58018800759,
    60452703538,111337682818,88061040834,3869285900,92509794888,140822007066,68441070730,
    78714280741,640127545586,889048402499,1834038866088,2125456429639,2445982583792,1087410175356,
    6326370809165,28073933425642,34402677337203,77089471863210,54965532771650,47606175542043,
    399378732676572,1264830451193108],
   [1492461713686812]]
private def phb_4 : List ℤ := altBuildHbFrom 256 128 364908000000 0 128
private def phbv_4 : List ℤ := pzigCatZ 0
  [
   [264221615420640,371475627087716,452278698976204,519144955952704,576951744866280,
    628215167391228,674438440743870,716606475337472,755407155196164,791344035413406,
    824799284939970,856071368189794,885398862958616,912976188557582,938964372924744,
    963498649676452,986693958097316,1008649014190574,1029449382790336,1049169835535964,
    1067876188139122,1085626751268040,1102473490191390,1118462961776542,1133637079093550,
    1148033740975256,1161687354663494,1174629272984240,1186888162579080,1198490316062296,
    1209459918219372,1219819274268168,1229589006595002,1238788225130572,1247434675555470,
    1255544868756516,1263134194344972,1270217020559772,1276806782486268,1282916060202906,
    1288556648209162,1293739617275766,1298475369683398,1302773688671314,1306643782796892,
    1310094325806512,1313133492533664,1315768991268960,1318008092986424,1319857657759136,
    1321324158653566,1322413703354410,1323132053739460,1323484643596154,1323476594647252,
    1323112731032014,1322397592370772,1321335445524568,1319930295147142,1318185893113830,
    1316105746900420,1313693126974752,1310951073254420,1307882400675388],
   [1304489703908258,1300775361251542,1296741537724130,1292390187372336,1287723054800218,
    1282741675925324,1277447377955296,1271841278574066,1265924284319298,1259697088125374,
    1253160165998356,1246313772780844,1239157936955408,1231692454425032,1223916881197662,
    1215830524889134,1207432434944388,1198721391460382,1189695892475288,1180354139566922,
    1170694021578118,1160713096257628,1150408569570776,1139777272394012,1128815634259902,
    1117519653762870,1105884865168832,1093906300691536,1081578447801732,1068895200818408,
    1055849805889246,1042434798293810,1028641930789608,1014462091457318,999885209173266,
    984900144426096,969494562676168,953654786797214,937365624295964,920610163915034,
    903369534803120,885622619565150,867345710015454,848512091106650,829091533942302,
    809049672478466,788347229687390,766939046380516,744772847660808,721787655033272,
    697911711503278,673059723985362,647129127072286,619994907534850,591502248513164,
    561455754391862,529603088126776,495609012822236,459011911833266,419145725195262,
    374986250385242,324806658558356,265235658425672,187561292119138]]
private def pvi_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s3 pvo_3
private def pvo_4 : List ℤ := pzigCatZ 0
  [
   [54801238,1328150,11066644,9886332,79286726,252221651,728782366,1575831055,1748481538,
    794192995,933902940,296953658,1008623793,1165598652,677954657,312809661,958523762,995695813,
    190861228,718969494,1001010101,580223444,381662950,981881199,614029148,260712942,853807691,
    500767128,496780464,1059656217,564476052,558731814,872218655,159049547,1143196650,1176432395,
    503200484,262579278,184859437,249844684,236672041,261208370,549763757,741143441,474742508,
    78205163,144312738,703336279,478201382,877754437,2098099692,3049585535,10210245412,
    21625995543,38152237874,55183226039,62030775692,65771873501,81503183430,105869266533,
    91272948472,117487182759,97005396582,92705531591],
   [74294288692,45185157993,15973889178,23248644772,53355557707,78114358366,90405241757,
    89921008068,72285754439,39635076494,906569974,39676516343,70058020540,87397773743,85120206302,
    59079018121,11419942450,42760984088,80834297239,90442097980,76172195175,44885844484,
    9007256984,70084678109,94644143828,85463699447,62878140244,1817173277,50979649365,
    104511540412,100470833957,74793358616,21464894541,25277260011,46419044888,28005789103,
    6346972993,10153983496,19962149060,24723155653,22221308133,112062862194,93221290021,
    31469119525,48369851032,35273183480,383715396,126289133420,258390240017,57256097736,
    157390752097,148598175000,447153387435,635867188337,393832521289,7626287087699,8518358995624,
    9910632315089,238013303638,28767107784113,70684539732505,71613906320579,163355380246943,
    679247586501220],
   [1871030516757216]]
private def phb_5 : List ℤ := altBuildHbFrom 256 128 282217000000 0 128
private def phbv_5 : List ℤ := pzigCatZ 0
  [
   [204346935773310,287296351545632,349788816877042,401502658297720,446209977805164,
    485856708802356,521605427755524,554217856693510,584225999753352,612019302515334,
    637893331464104,662078916648632,684760572274632,706088660720388,726187719736762,
    745162337947480,763101408498444,780081277576324,796168120356200,811419764640548,
    825887111787242,839615258812118,852644395248510,865010527814382,876746071751082,
    887880337720230,898439936014194,908449114663952,917930044226436,926903059204384,
    935386863922184,943398709061296,950954543814390,958069147652762,964756244947324,
    971028605089112,976898130283400,982375932814070,987472403271308,992197270989628,
    996559657742898,1000568125578816,1004230719540102,1007555005907660,1010548106507916,
    1013216729548644,1015567197382280,1017605471540640,1019337175338304,1020767614302262,
    1021901794651620,1022744440022064,1023300006604924,1023572696849002,1023566471854722,
    1023285062573750,1022731979913026,1021910523829586,1020823791491392,1019474684569550,
    1017865915718470,1016000014292460,1013879331340072,1011506043910810],
   [1008882158702678,1006009515073186,1002889787431054,999524487020450,995914963104544,
    992062403549982,987967834808800,983632121289030,979055964099826,974239899151234,
    969184294582630,963889347487288,958355079893410,952581333953954,946567766288928,
    940313841413826,933818824176780,927081771114294,920101520620810,912876681810642,
    905405621931314,897686452164762,889717011626370,881494849340712,873017203936134,
    864280980756782,855282726038760,846018597734944,836484332498222,826675208242540,
    816586001591210,806210939387694,795543643278994,784577066177804,773303419155654,
    761714087001380,749799530278262,737549171203562,724951260021522,711992717697636,
    698658949662744,684933623888262,670798404648380,656232630733900,641212923352172,
    625712704072958,609701596349452,593144674417580,576001509279846,558224940644010,
    539759472210312,520539138971952,500484617643240,479499223968132,457463223795146,
    434225499679940,409590896121418,383300143520156,354996231164700,324164033475372,
    290011440212250,251202935420336,205131188721316,145058439875220]]
private def pvi_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s4 pvo_4
private def pvo_5 : List ℤ := pzigCatZ 0
  [
   [53139094,14390822,873963,33280967,65568478,307142061,1640336980,1759162407,1101202976,
    258843465,41731226,1370293784,1031834287,456518928,523971190,1103240415,756488660,101822312,
    970070125,921008480,170391037,679097401,973219286,260198691,633797507,777966408,64532389,
    870905993,940640038,30722867,806929619,502401904,783591188,1454457915,875858654,128730025,
    160567411,187276350,405729317,163001216,229544593,29716717,577224818,721166923,379029251,
    360553783,792766546,1325810931,1925011550,5055727815,10325998506,21225977017,37654119504,
    52876758919,65595164512,70886572031,77950371470,95675467405,108734222564,103482247849,
    97990454698,101217563111,58812573338,52377104937],
   [1141716419,36946469192,58699309535,60315880032,98931072155,86057300970,74218872363,
    44014076834,3950319769,35504757703,66839488396,84378494597,84914705540,64283110145,
    22795558892,29215966318,73792425939,92601230554,81805687203,50852631184,7268725803,
    45912762251,91519527278,97563491629,66217674322,26599472347,27900506715,86168438802,
    103681829413,96776460872,42215185933,1643600168,41658757896,43379559423,20493675006,
    10064363630,9648885777,16349631041,15665731388,39143572428,98980351867,90355830408,
    23746445016,65765637063,23595819815,68317243618,78861476769,216318937656,110399637721,
    64091573415,171541556989,263951748697,733318908914,746124069955,1683607176874,2189577072181,
    14040727305457,5877516592438,2995331621025,7203379638830,57477198748236,62541334719282,
    66052057802214,424230707622482],
   [1951447846177918]]
private def phb_6 : List ℤ := altBuildHbFrom 256 128 252571500000 0 128
private def phbv_6 : List ℤ := pzigCatZ 0
  [
   [182881300873684,257117290788322,313045231725444,359326789882404,399337826598742,
    434819864598074,466813357438972,496000012018642,522855948070824,547729701843800,
    570885792024882,592530801108084,612829860994420,631917539238030,649905291515018,
    666886719931478,682941379848006,698137597661972,712534597173614,726184131660780,
    739131755545454,751417828625012,763078318721088,774145450224012,784648233314360,
    794612899713714,804063264434846,813021028373012,821506033177794,829536477312990,
    837129100306226,844299340740194,851061472423760,857428722317860,863413373116122,
    869026852848214,874279813451612,879182199919740,883743311362672,887971855096458,
    891875994697734,895463392813438,898741249394342,901716335920964,904395026107088,
    906783323496442,908886886309608,910711049848970,912260846727724,913541025153494,
    914556065466826,915310195108844,915807402170016,916051447652684,916045876563266,
    915794027935404,915299043872632,914563877687824,913591301206760,912383911294352,
    910944135654080,909274237944094,907376322246920,905252336923784],
   [902904077878984,900333191254628,897541175571076,894529383323774,891299022042468,
    887851154814290,884186700267562,880306432008532,876210977498304,871900816352226,
    867376278038448,862637538946576,857684618790854,852517376305294,847135504180274,
    841538523181284,835725775380524,829696416420676,823449406717096,816983501489764,
    810297239498772,803388930337052,796256640110234,788898175305732,781311064620328,
    773492538476462,765439505911050,757148528465016,748615790634776,739837066366062,
    730807680972070,721522467737800,711975718324694,702161125907112,692071719744992,
    681699789612494,671036798143542,660073278699158,648798715777314,637201404231384,
    625268282579516,612984734391954,600334350020192,587298638612866,573856677203864,
    559984679295590,545655459247230,530837760073488,515495399643092,499586171619246,
    483060409313992,465859077018232,447911183965104,429130202101456,409408974756218,
    388612258625144,366565398327282,343036359252282,317705632898142,290112205079514,
    259547172819384,224815309508348,183583171928430,129820768227796]]
private def pvi_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s5 pvo_5
private def pvo_6 : List ℤ := pzigCatZ 0
  [
   [49751157,21630481,21134481,90837140,317243663,1066827924,2064435921,1225820590,318913805,
    336502135,811688524,1509116205,104523756,499771100,1141304931,677313296,321309170,993555185,
    874824046,93550462,824704465,846483266,58459929,796637983,640669052,258369720,978419081,
    750399318,279831288,809396441,101663608,1144510238,1487977709,567506288,250950236,305741287,
    240869650,292827623,228834992,83298322,162706963,660894078,484081015,46914981,288621697,
    1761947186,2141689343,4627716214,9625135903,19059700720,32504159589,49720978308,63671228683,
    72228839290,79003336165,87464855316,103114901853,110601523988,100870197415,89534398240,
    79805177623,48528558858,7416570213,13061095387],
   [69095531536,64129449511,78500991278,88487124223,90302467174,41755805951,23229151200,
    26253189062,58068171753,80171058050,85540489343,72146753022,39560495071,8196014491,
    56863574876,88425115359,90907958332,65527014657,24929407492,21799763476,68476924289,
    98554012076,89893917383,45863187850,2867521772,48020911079,84403861628,57113854587,
    51054904997,110763847080,61163871366,28733171169,48383036600,11037575995,9775328819,
    11712763896,11250356150,8760483121,41750480205,94981746470,81027988575,5860540313,72779817592,
    3826851486,93113004081,97859108772,143872090115,175130159056,24051229272,41600808921,
    35271344944,693977722041,921738095684,1021239684147,877594539358,4205606938424,14990754760915,
    1289036534656,1478715945195,7958511089391,40659674615884,66011790837776,25153466470872,
    175667006762432],
   [1990523696056538]]
private def phb_7 : List ℤ := altBuildHbFrom 256 128 165378000000 0 128
private def phbv_7 : List ℤ := pzigCatZ 0
  [
   [119746462985286,168354479092024,204974806469814,235278904615810,261477209769300,
    284710030892242,305658633007058,324769382086336,342354030363904,358640791346306,
    373802865776584,387975519113014,401266875920424,413765047933384,425543013761134,
    436662061906542,447174283387094,457124416753836,466551240386892,475488641140414,
    483966447000536,492011084632854,499646104938428,506892607705726,513769588132716,
    520294222146420,526482103268602,532347440745578,537903226432424,543161376264018,
    548132850897440,552827759160996,557255447215922,561424575771546,565343187252710,
    569018764469990,572458282066666,575668251795340,578654762499078,581423515527848,
    583979856203576,586328801850964,588475066831916,590423084955892,592177029583852,
    593740831697932,595118196170630,596312616435040,597327387730356,598165619073548,
    598830244088398,599324030805972,599649590536038,599809385896294,599805738075276,
    599640833395300,599316729233378,598835359350746,598198538675074,597407967573686,
    596465235650896,595371825097916,594129113619514,592738376957738],
   [591200791029354,589517433690292,587689286137166,585717233952838,583602067799966,
    581344483763518,578945083340158,576404373069436,573722763798428,570900569568214,
    567938006106952,564835188910494,561592130887268,558208739539564,554684813648116,
    551020039421210,547213986062878,543266100707398,539175702658692,534941976863478,
    530563966535526,526040564835228,521370505493098,516552352247626,511584486946392,
    506465096133808,501192155918454,495763414876530,490176374704184,484428268278434,
    478516034722044,472436290989054,466185299390870,459758930363348,453152619626470,
    446361318701970,439379437519208,432200777541050,424818453459002,417224801012694,
    409411267844690,401368283453488,393085103179256,384549619638472,375748132954908,
    366665068277878,357282625076022,347580336995398,337534512809938,327117516782564,
    316296828310118,305033792170222,293281925244062,280984570955688,268071565585324,
    254454354932796,240018578677994,224612305903174,208026329801378,189958788903894,
    169945509871558,147203885853596,120206031983734,85003648503400]]
private def pvi_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m256_r128_s6 pvo_6
private def pvo_7 : List ℤ := pzigCatZ 0
  [
   [48431126,22265520,34353158,133475297,459839420,1310895049,2061043940,940811227,67912836,
    532899924,999774285,1320352538,295209038,716942269,1121958778,325759655,663220349,1049497194,
    571228953,476168647,933089518,595877787,335215337,883786508,306082579,645332401,1007554802,
    360118583,629743419,635428002,464303506,1474068275,1211364314,87897553,425519891,274909648,
    238903375,273038160,105336301,203465763,322644520,700004963,271153530,14825661,908684106,
    2379643039,3294271054,7417477105,14642763428,26595350275,41952857450,58606819741,69736766066,
    76617234443,84011731650,94861314315,108630284478,107977647987,93786034224,82168937763,
    65285727888,26257760567,10921182093,34955887522],
   [81196800631,65947626224,85469129155,88509813936,73474620685,21557919954,3090375601,
    48807394167,71064369886,85320753153,80157546880,56287661235,15245985258,34679705720,
    76284662955,93650558470,80896277477,45357333768,632846443,45471752161,79428502626,50728394117,
    117916233005,14568475682,25607757544,65361183161,79604119956,19187922903,83768449193,
    75336042450,90152287654,21281396307,43317484330,2356057042,12816972399,6202309530,13734320318,
    5413858968,62900654587,98283430124,56503783197,34044284473,64675706478,36984566292,
    108399902815,106230868048,153514615361,141158242474,59138505732,49253640391,148139884116,
    822994950675,951985411074,951013912361,41934928366,6143514929250,14385992929827,370712839099,
    402605147935,11609728425021,34050394885200,67484935411270,22012602467474,92324288609788],
   [1996220281713152]]
private def pwalks : List RkmSegWalk := [
  ⟨phb_0, pvi_0, pvo_0⟩,
  ⟨phb_1, pvi_1, pvo_1⟩,
  ⟨phb_2, pvi_2, pvo_2⟩,
  ⟨phb_3, pvi_3, pvo_3⟩,
  ⟨phb_4, pvi_4, pvo_4⟩,
  ⟨phb_5, pvi_5, pvo_5⟩,
  ⟨phb_6, pvi_6, pvo_6⟩,
  ⟨phb_7, pvi_7, pvo_7⟩
  ]
private def pls : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private def pcs : List ℕ := [18074835, 18006368, 18006368, 1298570, 1459632, 564434, 505143, 165378]
private def pns : List ℕ := [44, 44, 44, 4, 4, 2, 2, 1]
private abbrev dP_0 : Prop := rkmAllTrueF [ bSlideChk 15 129 phbv_0 pvi_0 pvm_0_1, muxIntListEq
  phb_0 phbv_0] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [ bSlideChk 15 129 phbv_0 pvm_0_1 pvm_0_2, muxIntListEq
  phb_1 phbv_1] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [ bSlideChk 15 129 phbv_1 pvi_1 pvm_1_1, muxIntListEq
  phb_2 phbv_2] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := rkmAllTrueF [ bSlideChk 15 129 phbv_1 pvm_1_1 pvm_1_2, muxIntListEq
  phb_3 phbv_3] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := rkmAllTrueF [ bSlideChk 15 129 phbv_2 pvi_2 pvm_2_1, muxIntListEq
  phb_4 phbv_4] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := rkmAllTrueF [ bSlideChk 15 129 phbv_2 pvm_2_1 pvm_2_2, muxIntListEq
  phb_5 phbv_5] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := rkmAllTrueF [ bSlideChk 14 129 phbv_0 pvm_0_2 pvo_0, bSlideChk 1 129
  phbv_7 pvi_7 pvo_7, muxIntListEq phb_6 phbv_6] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := rkmAllTrueF [ bSlideChk 14 129 phbv_1 pvm_1_2 pvo_1, muxIntListEq
  phb_7 phbv_7, muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 256) 128) 1] [129]] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := bSlideChk 14 129 phbv_2 pvm_2_2 pvo_2 = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [ bSlideChk 4 129 phbv_3 pvi_3 pvo_3, bSlideChk 4 129
  phbv_4 pvi_4 pvo_4, bSlideChk 2 129 phbv_5 pvi_5 pvo_5, bSlideChk 2 129 phbv_6 pvi_6 pvo_6,
  rkmCheckRowFromWalks 256 32 128 pls pcs pns rkmMasksHiHiB_m256_r128 pwalks rkmRowHiHiB_m256_r128]
  = true
private theorem bk_9 : dP_9 := by decide +kernel
private theorem pw_0_s1 : muxFastIterFullT16 30 129 phbv_0 pvi_0 = pvm_0_2 := bCh 30
    (bSlideChk_sound (rkmHd bk_0)) (rkmHd bk_1) rfl
private theorem pw_0_s2 : muxFastIterFullT16 44 129 phbv_0 pvi_0 = pvo_0 := bCh 44 pw_0_s1
    (rkmHd bk_6) rfl
private theorem pwalk_0 : muxFastIterFullT16 44 129 phb_0 pvi_0 = pvo_0 :=
    (congrArg (fun h ↦ muxFastIterFullT16 44 129 h pvi_0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_0)))).trans pw_0_s2
private theorem pseg_0 :
    muxFastIterFullT16 44 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_0 pvi_0 = pvo_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_0
private theorem pw_1_s1 : muxFastIterFullT16 30 129 phbv_1 pvi_1 = pvm_1_2 := bCh 30
    (bSlideChk_sound (rkmHd bk_2)) (rkmHd bk_3) rfl
private theorem pw_1_s2 : muxFastIterFullT16 44 129 phbv_1 pvi_1 = pvo_1 := bCh 44 pw_1_s1
    (rkmHd bk_7) rfl
private theorem pwalk_1 : muxFastIterFullT16 44 129 phb_1 pvi_1 = pvo_1 :=
    (congrArg (fun h ↦ muxFastIterFullT16 44 129 h pvi_1)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_1)))).trans pw_1_s2
private theorem pseg_1 :
    muxFastIterFullT16 44 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_1 pvi_1 = pvo_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_1
private theorem pw_2_s1 : muxFastIterFullT16 30 129 phbv_2 pvi_2 = pvm_2_2 := bCh 30
    (bSlideChk_sound (rkmHd bk_4)) (rkmHd bk_5) rfl
private theorem pw_2_s2 : muxFastIterFullT16 44 129 phbv_2 pvi_2 = pvo_2 := bCh 44 pw_2_s1 bk_8 rfl
private theorem pwalk_2 : muxFastIterFullT16 44 129 phb_2 pvi_2 = pvo_2 :=
    (congrArg (fun h ↦ muxFastIterFullT16 44 129 h pvi_2)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_2)))).trans pw_2_s2
private theorem pseg_2 :
    muxFastIterFullT16 44 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_2 pvi_2 = pvo_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_2
private theorem pwalk_3 : muxFastIterFullT16 4 129 phb_3 pvi_3 = pvo_3 :=
    (congrArg (fun h ↦ muxFastIterFullT16 4 129 h pvi_3)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_3)))).trans (bSlideChk_sound (rkmHd bk_9))
private theorem pseg_3 :
    muxFastIterFullT16 4 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_3 pvi_3 = pvo_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_3
private theorem pwalk_4 : muxFastIterFullT16 4 129 phb_4 pvi_4 = pvo_4 :=
    (congrArg (fun h ↦ muxFastIterFullT16 4 129 h pvi_4)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_4)))).trans (bSlideChk_sound (rkmHd (rkmTl bk_9)))
private theorem pseg_4 :
    muxFastIterFullT16 4 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_4 pvi_4 = pvo_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_4
private theorem pwalk_5 : muxFastIterFullT16 2 129 phb_5 pvi_5 = pvo_5 :=
    (congrArg (fun h ↦ muxFastIterFullT16 2 129 h pvi_5)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_5)))).trans
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_9))))
private theorem pseg_5 :
    muxFastIterFullT16 2 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_5 pvi_5 = pvo_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_5
private theorem pwalk_6 : muxFastIterFullT16 2 129 phb_6 pvi_6 = pvo_6 :=
    (congrArg (fun h ↦ muxFastIterFullT16 2 129 h pvi_6)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl (rkmTl bk_6))))).trans
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl bk_9)))))
private theorem pseg_6 :
    muxFastIterFullT16 2 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_6 pvi_6 = pvo_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_6
private theorem pwalk_7 : muxFastIterFullT16 1 129 phb_7 pvi_7 = pvo_7 :=
    (congrArg (fun h ↦ muxFastIterFullT16 1 129 h pvi_7)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_7)))).trans (bSlideChk_sound (rkmHd (rkmTl bk_6)))
private theorem pseg_7 :
    muxFastIterFullT16 1 (Nat.add (highdNatMin (Nat.mul 1 256) 128) 1)
      phb_7 pvi_7 = pvo_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_7)))]
  exact pwalk_7
private theorem pwalks_snd : RkmSegWalksSound 256 128 pls pns pwalks := by
  dsimp only [RkmSegWalksSound, pls, pns, pwalks]
  exact ⟨pseg_0, ⟨pseg_1, ⟨pseg_2, ⟨pseg_3, ⟨pseg_4, ⟨pseg_5, ⟨pseg_6, ⟨pseg_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 128)` (`FindAllJohnsonRampKickMuxHi256T5`). -/
theorem rkmTrajHiHiB_m256_r128 :
    rkmLo12EqHi 256 32 128 [1, 1, 1, 1, 1, 1, 1, 1]
      [18074835, 18006368, 18006368, 1298570, 1459632, 564434, 505143, 165378]
      [44, 44, 44, 4, 4, 2, 2, 1] rkmMasksHiHiB_m256_r128 rkmRowHiHiB_m256_r128 :=
  rkmCheckRowFromWalks_sound pwalks_snd (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl bk_9)))))
end
end QuantumComputation.Specs.DickeSol
