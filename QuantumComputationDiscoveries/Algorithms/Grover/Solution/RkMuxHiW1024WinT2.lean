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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW1024WinT0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW1024WinT1

/-
# Caustic `r = 1024` Halo-16 Walk `w1024` Part `2` (`RkMuxHiW1024WinT2`)

Certifies part `2` of the `w1024` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Kick mask `w1024` seg `1`. -/
def rkmMkHi_w1024_s1 : List Bool := List.replicate 999 false ++ [
  true, false, false, false, false, true, true, true, true, true, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, true]
/-- Kick mask `w1024` seg `2`. -/
def rkmMkHi_w1024_s2 : List Bool := List.replicate 994 false ++ [
  true, false, true, false, true, false, true, false, true, false, true, false, true, false, false,
  true, true, false, false, false, true, true, false, false, false, false, false, false, false,
  false, true]
/-- Kick mask `w1024` seg `3`. -/
def rkmMkHi_w1024_s3 : List Bool := List.replicate 988 false ++ [
  true, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, true, false, false, false, true, false, true, false, false, false, false, false, true,
  false, false, true]
/-- Kick mask `w1024` seg `4`. -/
def rkmMkHi_w1024_s4 : List Bool := List.replicate 996 false ++ [
  true, false, false, true, false, true, false, false, true, false, false, true, false, false, true,
  false, true, false, true, false, true, true, true, true]
/-- Kick mask `w1024` seg `5`. -/
def rkmMkHi_w1024_s5 : List Bool := List.replicate 989 false ++ [
  true, true, false, false, false, false, false, false, false, false, false, true, false, false,
  false, false, false, false, true, false, true, true, false, true, true, true, true, true, true,
  true, true, false, true, true]
/-- Kick mask `w1024` seg `6`. -/
def rkmMkHi_w1024_s6 : List Bool := List.replicate 992 false ++ [
  true, false, false, false, false, false, false, false, true, false, true, true, true, false,
  false, false, false, true, false, true, false, false, false, false, false, false, true, false,
  true]
/-- Kick-mask schedule for `w1024` `r = 1024`. -/
def rkmMasksHi_w1024_r1024 : List (List Bool) := [
  [], rkmMkHi_w1024_s1, rkmMkHi_w1024_s2, rkmMkHi_w1024_s3, rkmMkHi_w1024_s4, rkmMkHi_w1024_s5,
  rkmMkHi_w1024_s6, []]
/-- Certified `rowLo12` vector for `w1024` `r = 1024`. -/
def rkmRowHi_w1024_r1024 : List ℕ := List.replicate 955 0 ++ [
  256, 2746, 7392, 12512, 15488, 14123, 8451, 1967, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 269, 126, 0, 0, 0, 0, 1758, 34591, 0, 48, 0, 13163, 27700, 0, 3292, 46786, 68518,
  8286709, 40714, 209864, 437604, 1707403, 833609, 126534892, 52613930, 1229034, 376425995,
  50406074, 505538, 44437470, 455854, 72345177, 854458423, 2954728, 479739398, 57248967, 111771362,
  14456671, 533635535, 996844832820]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.ofNat n :: xs => match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
  | Int.negSucc _ :: _ => none
private def uOfNatHb : List ℕ → List ℤ | [] => [] | n :: ns => Int.ofNat n :: uOfNatHb ns
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
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bEnc1 z x with
    | none => none
    | some u => match bEnc z xs with | none => none | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
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
  match x with | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNatTdiv_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    dsimp only; rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
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
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]
      rw [bNeg_eq, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNatTdiv_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bForcedAdd_eq : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]; simp [Int.ofNat_eq_natCast]
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq, Int.negSucc_eq]; omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal z d b0 c0 b v c1) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
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
private def bAllPos : List ℕ → Bool
  | [] => true | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) : List ℕ → ℕ | [] => z | x :: _ => x
private def bTailN : List ℕ → List ℕ | [] => [] | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 c0 bns vs cs) = true → bDec z (bSlide z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR [] [] hp.2
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
private def bStg (z dg mL cL : ℕ) (bns vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlide z d nL 0 z bns vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL cL bns vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h; revert h
  cases hp : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSlide_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns hp
private def bBind (z dg mL cL : ℕ) (bns vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bns vns cns with | none => none | some out => k nL out
private theorem bBind_sound {z dg mL cL : ℕ} {bns vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL bns vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL bns vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z dg mL cL bns vns cns mid hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bns vns : List ℕ) : Option (List ℕ) :=
  bBind z 16 mL c bns vns vns fun l1 c1 => bBind z 15 mL l1 bns vns c1 fun l2 c2 =>
  bBind z 14 mL l2 bns vns c2 fun l3 c3 => bBind z 13 mL l3 bns vns c3 fun l4 c4 =>
  bBind z 12 mL l4 bns vns c4 fun l5 c5 => bBind z 11 mL l5 bns vns c5 fun l6 c6 =>
  bBind z 10 mL l6 bns vns c6 fun l7 c7 => bBind z 9 mL l7 bns vns c7 fun l8 c8 =>
  bBind z 8 mL l8 bns vns c8 fun l9 c9 => bBind z 7 mL l9 bns vns c9 fun la ca =>
  bBind z 6 mL la bns vns ca fun lb cb => bBind z 5 mL lb bns vns cb fun lc cc =>
  bBind z 4 mL lc bns vns cc fun ld cd => bBind z 3 mL ld bns vns cd fun le ce =>
  bBind z 2 mL le bns vns ce fun lf cf => bStg z 1 mL lf bns vns cf
private theorem bStep_sound (z mL cL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL cL bns vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, bns, vns => match bStep z mL cL bns vns with
    | none => none | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bns vns out : List ℕ),
    bIter z k mL cL bns vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, _, vns, out, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bns, vns, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bns vns with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound z mL cL bns vns vNext hs]
      exact bIter_sound z k mL (rkmNextLen16 mL cL) bns vNext out h
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => match bIter z k mL cL bns vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only; cases hh : uToNatHb hb with
  | none => rfl
  | some bns => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 100000000000000000 k mL cL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 100000000000000000 v vns hv]
private def bWinStep (thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ)
    (dropAcc : ℕ) : ℕ × List ℤ × ℕ :=
  fN (Nat.sub off 16) fun sLo => fN (Nat.sub off sLo) fun padL =>
    fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (rkmDropInts sLo hb) fun hbSl =>
      fL (rkmPrependZeros padL xs) fun vecSl => fN (altIntLen vecSl) fun curLen =>
        fL (fIter 1 remMax curLen hbSl vecSl) fun rawSl => rkmTrimWin thr sLo rawSl dropAcc
private theorem bWinStep_eq (thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ) :
    bWinStep thr d hb off xs dropAcc = muxWinStepT16 thr d hb off xs dropAcc := by
  unfold bWinStep muxWinStepT16; dsimp only [fN, fL]
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq, fIter_eq]
private def bWinIter : ℕ → ℕ → ℕ → List ℤ → ℕ → List ℤ → ℕ → ℕ × List ℤ × ℕ
  | 0, _, _, _, off, xs, dropAcc => (off, xs, dropAcc)
  | k + 1, thr, d, hb, off, xs, dropAcc =>
    match bWinStep thr d hb off xs dropAcc with | (o1, x1, d1) => bWinIter k thr d hb o1 x1 d1
private theorem bWinIter_eq :
    ∀ (k thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ),
      bWinIter k thr d hb off xs dropAcc = muxWinIterT16 k thr d hb off xs dropAcc
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, thr, d, hb, off, xs, dropAcc => by
    unfold bWinIter muxWinIterT16; rw [bWinStep_eq]
    rcases muxWinStepT16 thr d hb off xs dropAcc with ⟨o1, x1, d1⟩
    exact bWinIter_eq k thr d hb o1 x1 d1
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_eq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; rw [Bool.and_eq_true, rkmw_nat_ble_eq_true, rkmw_nat_ble_eq_true] at h; omega
private def wSlChk (steps thr d : ℕ) (hb : List ℤ) (offIn : ℕ) (xsIn : List ℤ)
    (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  fL hb fun hbF => fL xsIn fun inF => fL xsOut fun outF =>
    match bWinIter steps thr d hbF offIn inF 0 with
    | (oRes, xRes, dRes) =>
      Bool.and (bNatEq oRes offOut) (Bool.and (muxIntListEq xRes outF) (bNatEq dRes dropExp))
private theorem wSlChk_sound {steps thr d offIn offOut dropExp : ℕ} {hb xsIn xsOut : List ℤ}
    (h : wSlChk steps thr d hb offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d hb offIn xsIn offOut xsOut dropExp := by
  unfold wSlChk at h; dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, bWinIter_eq] at h
  rcases hres : muxWinIterT16 steps thr d hb offIn xsIn 0 with ⟨oRes, xRes, dRes⟩
  rw [hres] at h; simp only [Bool.and_eq_true] at h; rcases h with ⟨ho, hx, hd⟩
  have ho' := bNatEq_eq_true ho; have hd' := bNatEq_eq_true hd; subst ho'; subst hd'
  have h2 : muxWinIterT16HiChk steps thr 0 d hb offIn xsIn oRes xsOut dRes = true := by
    unfold muxWinIterT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, hres]
    simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true]; exact ⟨trivial, hx, trivial⟩
  exact muxWinIterT16HiChk_sound h2
private theorem rkmSubstHb {k d o0 o2 dT : ℕ} {hbF hbW x0 x2 : List ℤ}
    (hhb : muxIntListEq hbF hbW = true) (h : RkmWinIterSound k d hbF o0 x0 o2 x2 dT) :
    RkmWinIterSound k d hbW o0 x0 o2 x2 dT := by rw [← muxIntListEq_eq_true.mp hhb]; exact h
private theorem rkmChS (kT dT : ℕ) {k1 k2 d o0 o1 o2 d1 d2 : ℕ} {hb x0 x1 x2 : List ℤ}
    (h1 : RkmWinIterSound k1 d hb o0 x0 o1 x1 d1)
    (h2 : wSlChk k2 100000000 d hb o1 x1 o2 x2 d2 = true) (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d hb o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (wSlChk_sound h2)
private def pzig : List ℕ → List ℤ
  | [] => [] | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ | [] => [] | ws :: wss => pzig ws ++ pzigCat wss
private theorem rkmWP0 {a : Bool} {s : List Bool} (h : rkmAllTrueF (a :: s) = true) : a = true :=
  (rkmAllTrueF_cons h).1
private theorem rkmSegWalk_mk {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d)
    (hble : Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private theorem rkmWP1 {a b : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: s) = true) : b = true := rkmWP0 (rkmAllTrueF_cons h).2
private theorem rkmWP2 {a b c : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: s) = true) : c = true := rkmWP1 (rkmAllTrueF_cons h).2
private theorem rkmWP3 {a b c d : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: s) = true) : d = true := rkmWP2 (rkmAllTrueF_cons h).2
private theorem rkmWP4 {a b c d e : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: e :: s) = true) : e = true :=
  rkmWP3 (rkmAllTrueF_cons h).2
private theorem rkmWT5 {a b c d e : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: e :: s) = true) : rkmAllTrueF s = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    (rkmAllTrueF_cons h).2).2).2).2).2
private def rkmHbWin_w1024_s1b : List ℤ := altBuildHbFrom 2048 1024 18399339933 0 1024
private def rkmXsWin_w1024_s1b_in : List ℤ := pzigCat
  [
   [316224290,789839826,1473352350,2897405424,5814479076,11033713800,20190931540,35892337888,
    62192250056,104389009738,170871480098,274169987778,431366183172,665616407688,1008712386790,
    1502055828494,2199765783258,3169571397342,4495847658246,6281760082940,8649634008088,
    11741423754132,15718163938382,20758242728406,27053195916786,34801399965828,44201392767232,
    55441738562692,68690592028160,84081910875392,101702828626124,121580314458540,143669068768092,
    167841382282080,193879012659636,221470145322334,250210562456254,279610521438924,
    309104572606316,338069126749422,365843729901578,391755479097998,415145534878980,
    435397961654544,451965922862536,464395855492142,472349628523814,475618316791916,
    474131552379606,467959621925972,457308924929122,442510567450124,424004425791704,
    402316633396670,378036087124716,351788941583772,324212334963294,295930031367556,
    267530991383330,239549838037014,212454384547870,186635112686656,162400462499142,
    139976630925538,119510199334748,101074253397544,84677518903960,70273233651044,57771007443340,
    47046892578496,37953651634522,30330925542446,24011903686096,18831428206492,14630380337146,
    11260130967456,8585215729844,6484273866134,4851706839140,3595968441414,2640067904812,
    1919737932764,1382117159374,984991164854,694213746720,483692169932,332757695578,225707885480,
    150821838370,98885009918,63662077958,39951907900,24316740616,14197986006,7618701950,
    3714001574,1367562758,295460610]]
private def rkmXsWin_w1024_s1b_out : List ℤ := pzigCat
  [
   [246211563,449847853,664225276,1646516488,745125526,1247320507,3020608949,2427494333,
    2713240042,11174330494,10769884184,11898031415,46872749469,45443635113,44797111848,
    192074468292,219697150762,96106705495,729980803095,1119148295107,299655676963,2237629693226,
    5285539726374,5350305839098,1892664263609,17723956081629,35661708173997,39227712045547,
    5389926492867,85877015912710,239599838541998,437857229729832,641454003644952,802097067472116,
    880069172945662,859005053843784,750747971712096,588594801809264,413170427116696,
    258191877545208,142136698479466,67734164757808,27114853032216,8610090623910,1877391169818]]
private def rkmHbF_w1024_s1b : List ℤ := pzigCat
  [
   [106580361510754,150616992196218,184332165220416,212692294992140,237622613570752,
    260111249329568,280745634856952,299908798420380,317866988162322,334814199774966,
    350896991283880,366229306618406,380901825242066,394988123025396,408548880919760,
    421634848276508,434288983709756,446548036466082,458443737312182,470003710728144,
    481252184227286,492210547384060,502897797763522,513330900531824,523525081339742,
    533494067022060,543250285051106,552805030071470,562168603925726,571350434155764,
    580359174892830,589202793235186,597888643587574,606423531952912,614813771788936,
    623065232745092,631183383359188,639173328604950,647039843030290,654787400103554,
    662420198285416,669942184262526,677357073711986,684668369910262,691879380454142,
    698993232322880,706012885478548,712941145174486,719780673118904,726533997621282,
    733203522832716,739791537177312,746300221059582,752731653922542,759087820722182,
    765370617876312,771581858739072,777723278646592,783796539574194,789803234441148,
    795744891095060,801622976004604,807438897686318,813194009888518,818889614553100,
    824526964573866,830107266368270,835631682277770,841101332810590,846517298739340,
    851880623064874,857192312856648,862453340978958,867664647711628,872827142272906,
    877941704251724,883009184955842,888030408681812,893006173912292,897937254445688,
    902824400462784,907668339534588,912469777575320,917229399744170,921947871299128,
    926625838405994,931263928905406,935862753040522,940422904147810,944944959313186,
    949429479995652,953877012620324,958288089142722,962663227585972,967002932552534,
    971307695711878,975577996265506,979814301390594,984017066663426,988186736463770,
    992323744361204,996428513484378,1000501456874148,1004542977821394,1008553470190386,
    1012533318728376,1016482899362208,1020402579482526,1024292718216286,1028153666688094,
    1031985768270968,1035789358827012,1039564766938530,1043312314130006,1047032315081416,
    1050725077833262,1054390903983728,1058030088878342,1061642921792446,1065229686106862,
    1068790659477012,1072326113995822,1075836316350664,1079321527974636,1082782005192370,
    1086217999360680,1089629757004210,1093017519946340],
   [1096381525435526,1099722006267278,1103039190901966,1106333303578614,1109604564424856,
    1112853189563210,1116079391213812,1119283377793786,1122465354013320,1125625520968660,
    1128764076232076,1131881213938962,1134977124872146,1138051996543568,1141106013273368,
    1144139356266528,1147152203687144,1150144730730406,1153117109692400,1156069510037790,
    1159002098465454,1161915038972176,1164808492914438,1167682619068396,1170537573688098,
    1173373510562000,1176190581067876,1178988934226114,1181768716751524,1184530073103660,
    1187273145535730,1189998074142144,1192704996904728,1195394049737664,1198065366531212,
    1200719079194208,1203355317695446,1205974210103914,1208575882627964,1211160459653448,
    1213728063780826,1216278815861312,1218812835032066,1221330238750482,1223831142827572,
    1226315661460508,1228783907264328,1231235991302830,1233672023118694,1236092110762846,
    1238496360823082,1240884878451990,1243257767394178,1245615130012828,1247957067315618,
    1250283678979998,1252595063377860,1254891317599616,1257172537477704,1259438817609538,
    1261690251379896,1263926930982810,1266148947442920,1268356390636348,1270549349311078,
    1272727911106870,1274892162574722,1277042189195886,1279178075400448,1281299904585492,
    1283407759132868,1285501720426538,1287581868869566,1289648283900706,1291701044010650,
    1293740226757892,1295765908784280,1297778165830198,1299777072749446,1301762703523784,
    1303735131277178,1305694428289736,1307640666011346,1309573915075034,1311494245310042,
    1313401725754632,1315296424668614,1317178409545634,1319047747125198,1320904503404446,
    1322748743649696,1324580532407750,1326399933516972,1328207010118138,1330001824665074,
    1331784438935090,1333554914039188,1335313310432088,1337059687922038,1338794105680454,
    1340516622251354,1342227295560614,1343926182925052,1345613341061326,1347288826094674,
    1348952693567476,1350604998447658,1352245795136946,1353875137478944,1355493078767082,
    1357099671752402,1358694968651206,1360279021152562,1361851880425660,1363413597127054,
    1364964221407758,1366503802920208,1368032390825114,1369550033798170,1371056780036662,
    1372552677265938,1374037772745780,1375512113276648,1376975745205830,1378428714433462,
    1379871066418462,1381302846184354,1382724098324982],
   [1384134867010134,1385535195991066,1386925128605936,1388304707785130,1389673976056516,
    1391032975550588,1392381748005546,1393720334772268,1395048776819212,1396367114737232,
    1397675388744308,1398973638690210,1400261904061068,1401540223983880,1402808637230938,
    1404067182224190,1405315897039512,1406554819410936,1407783986734786,1409003436073764,
    1410213204160956,1411413327403786,1412603841887900,1413784783380984,1414956187336536,
    1416118088897558,1417270522900204,1418413523877368,1419547126062212,1420671363391642,
    1421786269509726,1422891877771062,1423988221244098,1425075332714386,1426153244687804,
    1427221989393718,1428281598788094,1429332104556574,1430373538117484,1431405930624826,
    1432429312971196,1433443715790678,1434449169461684,1435445704109752,1436433349610310,
    1437412135591392,1438382091436314,1439343246286312,1440295629043140,1441239268371630,
    1442174192702224,1443100430233448,1444018008934362,1444926956546988,1445827300588676,
    1446719068354450,1447602286919326,1448476983140588,1449343183660024,1450200914906152,
    1451050203096394,1451891074239228,1452723554136310,1453547668384558,1454363442378220,
    1455170901310906,1455970070177580,1456760973776548,1457543636711400,1458318083392926,
    1459084338041022,1459842424686542,1460592367173154,1461334189159146,1462067914119222,
    1462793565346268,1463511165953096,1464220738874160,1464922306867256,1465615892515186,
    1466301518227418,1466979206241706,1467648978625700,1468310857278528,1468964863932354,
    1469611020153932,1470249347346114,1470879866749356,1471502599443202,1472117566347742,
    1472724788225050,1473324285680612,1473916079164732,1474500188973910,1475076635252214,
    1475645437992628,1476206617038384,1476760192084276,1477306182677954,1477844608221214,
    1478375487971246,1478898841041896,1479414686404886,1479923042891034,1480423929191456,
    1480917363858744,1481403365308132,1481881951818666,1482353141534318,1482816952465134,
    1483273402488328,1483722509349382,1484164290663132,1484598763914830,1485025946461200,
    1485445855531482,1485858508228452,1486263921529448,1486662112287360,1487053097231628,
    1487436892969216,1487813515985570,1488182982645580,1488545309194518,1488900511758960,
    1489248606347708,1489589608852696,1489923535049880],
   [1490250400600124,1490570221050068,1490883011832992,1491188788269668,1491487565569192,
    1491779358829818,1492064183039778,1492342053078080,1492612983715324,1492876989614474,
    1493134085331642,1493384285316858,1493627603914834,1493864055365698,1494093653805750,
    1494316413268188,1494532347683826,1494741470881816,1494943796590338,1495139338437314,
    1495328109951076,1495510124561058,1495685395598460,1495853936296906,1496015759793108,
    1496170879127496,1496319307244870,1496461056995018,1496596141133342,1496724572321468,
    1496846363127856,1496961526028396,1497070073406998,1497172017556176,1497267370677620,
    1497356144882774,1497438352193382,1497514004542062,1497583113772834,1497645691641672,
    1497701749817034,1497751299880390,1497794353326740,1497830921565130,1497861015919152,
    1497884647627454,1497901827844228,1497912567639698,1497916878000604,1497914769830670,
    1497906253951084,1497891341100948,1497870041937744,1497842367037784,1497808326896648,
    1497767931929632,1497721192472172,1497668118780280,1497608721030960,1497543009322626,
    1497470993675514,1497392684032084,1497308090257420,1497217222139628,1497120089390222,
    1497016701644502,1496907068461948,1496791199326572,1496669103647304,1496540790758342,
    1496406269919520,1496265550316652,1496118641061882,1495965551194032,1495806289678932,
    1495640865409756,1495469287207356,1495291563820570,1495107703926558,1494917716131106,
    1494721608968938,1494519390904016,1494311070329846,1494096655569774,1493876154877270,
    1493649576436220,1493416928361206,1493178218697780,1492933455422748,1492682646444428,
    1492425799602914,1492162922670348,1491894023351162,1491619109282336,1491338188033648,
    1491051267107910,1490758353941216,1490459455903170,1490154580297114,1489843734360368,
    1489526925264440,1489204160115250,1488875445953342,1488540789754096,1488200198427940,
    1487853678820542,1487501237713018,1487142881822122,1486778617800440,1486408452236574,
    1486032391655332,1485650442517896,1485262611222010,1484868904102144,1484469327429666,
    1484063887413004,1483652590197810,1483235441867116,1482812448441480,1482383615879148,
    1481948950076194,1481508456866660,1481062142022698,1480610011254702,1480152070211442,
    1479688324480192,1479218779586856,1478743440996078],
   [1478262314111374,1477775404275236,1477282716769240,1476784256814164,1476280029570078,
    1475770040136450,1475254293552238,1474732794795986,1474205548785912,1473672560379990,
    1473133834376036,1472589375511780,1472039188464946,1471483277853326,1470921648234838,
    1470354304107598,1469781249909976,1469202490020658,1468618028758694,1468027870383558,
    1467432019095178,1466830479033998,1466223254281006,1465610348857774,1464991766726490,
    1464367511789988,1463737587891774,1463101998816048,1462460748287722,1461813839972440,
    1461161277476584,1460503064347282,1459839204072422,1459169700080642,1458494555741334,
    1457813774364640,1457127359201438,1456435313443332,1455737640222634,1455034342612348,
    1454325423626140,1453610886218320,1452890733283804,1452164967658082,1451433592117182,
    1450696609377626,1449954022096384,1449205832870834,1448452044238698,1447692658677994,
    1446927678606970,1446157106384050,1445380944307758,1444599194616650,1443811859489240,
    1443018941043924,1442220441338894,1441416362372054,1440606706080930,1439791474342576,
    1438970668973476,1438144291729450,1437312344305532,1436474828335884,1435631745393660,
    1434783096990906,1433928884578428,1433069109545680,1432203773220616,1431332876869574,
    1430456421697132,1429574408845966,1428686839396704,1427793714367784,1426895034715288,
    1425990801332794,1425081015051208,1424165676638602,1423244786800038,1422318346177396,
    1421386355349198,1420448814830414,1419505725072282,1418557086462112,1417602899323090,
    1416643163914074,1415677880429390,1414707048998612,1413730669686364,1412748742492078,
    1411761267349786,1410768244127880,1409769672628880,1408765552589192,1407755883678868,
    1406740665501350,1405719897593220,1404693579423938,1403661710395576,1402624289842550,
    1401581317031344,1400532791160226,1399478711358970,1398419076688556,1397353886140876,
    1396283138638434,1395206833034038,1394124968110482,1393037542580234,1391944555085104,
    1390846004195918,1389741888412184,1388632206161740,1387516955800418,1386396135611684,
    1385269743806272,1384137778521828,1383000237822534,1381857119698722,1380708422066498,
    1379554142767346,1378394279567728,1377228830158686,1376057792155420,1374881163096880,
    1373698940445330,1372511121585928,1371317703826280],
   [1370118684395990,1368914060446216,1367703829049202,1366487987197818,1365266531805072,
    1364039459703642,1362806767645370,1361568452300780,1360324510258560,1359074938025052,
    1357819732023726,1356558888594662,1355292403993996,1354020274393384,1352742495879440,
    1351459064453182,1350169976029444,1348875226436312,1347574811414522,1346268726616864,
    1344956967607576,1343639529861724,1342316408764576,1340987599610960,1339653097604632,
    1338312897857600,1336966995389478,1335615385126792,1334258061902306,1332895020454322,
    1331526255425970,1330151761364490,1328771532720510,1327385563847294,1325993849000004,
    1324596382334928,1323193157908712,1321784169677570,1320369411496490,1318948877118426,
    1317522560193468,1316090454268020,1314652552783944,1313208849077704,1311759336379498,
    1310304007812362,1308842856391284,1307375875022282,1305903056501484,1304424393514180,
    1302939878633878,1301449504321328,1299953262923542,1298451146672794,1296943147685604,
    1295429257961716,1293909469383050,1292383773712636,1290852162593546,1289314627547800,
    1287771159975250,1286221751152458,1284666392231556,1283105074239076,1281537788074776,
    1279964524510446,1278385274188682,1276800027621662,1275208775189892,1273611507140922,
    1272008213588072,1270398884509098,1268783509744880,1267162078998052,1265534581831640,
    1263901007667656,1262261345785686,1260615585321448,1258963715265328,1257305724460900,
    1255641601603408,1253971335238242,1252294913759374,1250612325407780,1248923558269832,
    1247228600275668,1245527439197524,1243820062648066,1242106458078662,1240386612777646,
    1238660513868558,1236928148308344,1235189502885522,1233444564218346,1231693318752900,
    1229935752761198,1228171852339234,1226401603404998,1224624991696468,1222842002769570,
    1221052621996090,1219256834561572,1217454625463166,1215645979507444,1213830881308182,
    1212009315284104,1210181265656586,1208346716447322,1206505651475954,1204658054357658,
    1202803908500690,1200943197103896,1199075903154162,1197202009423848,1195321498468148,
    1193434352622430,1191540553999514,1189640084486908,1187732925743994,1185819059199172,
    1183898466046948,1181971127244964,1180037023510992,1178096135319864,1176148442900346,
    1174193926231966,1172232565041778,1170264338801062],
   [1168289226721984,1166307207754180,1164318260581280,1162322363617372,1160319495003400,
    1158309632603506,1156292754001280,1154268836495972,1152237857098610,1150199792528058,
    1148154619206998,1146102313257836,1144042850498530,1141976206438344,1139902356273522,
    1137821274882864,1135732936823250,1133637316325044,1131534387287432,1129424123273662,
    1127306497506196,1125181482861762,1123049051866312,1120909176689890,1118761829141384,
    1116606980663184,1114444602325734,1112274664821980,1110097138461686,1107911993165668,
    1105719198459886,1103518723469430,1101310536912382,1099094607093544,1096870901898052,
    1094639388784852,1092400034780036,1090152806470046,1087897669994744,1085634591040314,
    1083363534832042,1081084466126930,1078797349206146,1076502147867334,1074198825416740,
    1071887344661182,1069567667899838,1067239756915860,1064903572967810,1062559076780900,
    1060206228538044,1057844987870712,1055475313849588,1053097164975000,1050710499167160,
    1048315273756174,1045911445471816,1043498970433088,1041077804137532,1038647901450296,
    1036209216592952,1033761703132052,1031305313967416,1028840001320158,1026365716720410,
    1023882410994776,1021390034253476,1018888535877184,1016377864503554,1013857968013424,
    1011328793516674,1008790287337748,1006242395000826,1003685061214612,1001118229856770,
    998541843957950,995955845685430,993360176326336,990754776270448,988139584992550,
    985514541034354,982879581985932,980234644466694,977579664105844,974914575522346,
    972239312304350,969553806988082,966857991036164,964151794815358,961435147573708,
    958707977417064,955970211284968,953221774925874,950462592871684,947692588411584,
    944911683565144,942119799054658,939316854276714,936502767272944,933677454699938,
    930840831798298,927992812360792,925133308699572,922262231612434,919379490348088,
    916484992570384,913578644321470,910660349983840,907730012241236,904787532038344,
    901832808539254,898865739084650,895886219147638,892894142288208,889889400106244,
    886871882193058,883841476081334,880798067193502,877741538788394,874671771906170,
    871588645311438,868492035434458,865381816310404,862257859516552,859120034107362,
    855968206547318,852802240641454,849621997463470],
   [846427335281334,843218109480248,839994172482876,836755373666722,833501559278506,
    830232572345436,826948252583206,823648436300600,820332956300528,817001641777340,
    813654318210236,810290807252608,806910926617088,803514489956148,800101306737988,
    796671182117512,793223916802156,789759306912292,786277143835956,782777214077622,
    779259299100682,775723175163380,772168613147772,768595378381438,765003230451512,
    761391923010616,757761203574320,754110813309604,750440486813872,746749951883986,
    743038929274762,739307132446332,735554267299744,731780031900124,727984116186680,
    724166201668752,720325961107138,716463058179726,712577147130576,708667872401356,
    704734868244090,700777758314024,696796155241358,692789660180468,688757862335194,
    684700338458586,680616652325422,676506354175672,672368980126924,668204051553616,
    664011074430790,659789538639820,655538917233396,651258665656836,646948220922466,
    642607000733594,638234402554260,633829802620606,629392554889318,624921989918182,
    620417413673326,615878106257176,611303320550614,606692280762144,602044180876164,
    597358182991638,592633415541564,587868971382608,583063905743150,578217234016698,
    573327929386200,568394920263122,563417087523368,558393261519938,553322218849944,
    548202678850808,543033299797376,537812674768204,532539327145086,527211705705296,
    521828179260564,516387030790564,510886451011392,505324531311098,499699255974454,
    494008493607518,488249987659034,482421345919608,476520028860606,470543336652168,
    464488394672722,458352137290100,452131289655410,445822347203742,439421552498510,
    432924868986218,426327951142404,419626110383122,412814275983918,405886950082510,
    398838155632286,391661375908066,384349483825358,376894658894828,369288289060886,
    361520853919178,353581784804706,345459295892636,337140178615276,328609549160436,
    319850535260014,310843883414562,301567460362084,291995611755592,282098324634384,
    271840114919928,261178520821316,250062016782128,238427049797864,226193699630078,
    213259090703444,199486943484268,184690077727194,168599006039870,150800110080826,
    130597099502922,106632288410320,75400486065764]]
private def rkmC_w1024_s1b_1 : List ℤ := pzigCat
  [
   [528991582,1573825418,4157163272,9498057938,19572999728,37356664124,68546245356,121660119276,
    209185609850,349350694662,568095936670,901592128170,1398653461066,2123791560318,
    3159626655020,4611758293576,6609427614198,9306820577062,12884403236034,17547430002500,
    23521072287606,31045342021364,40365320758408,51719355906792,65324982328294,81361925154944,
    99953526233940,121149831640144,144909367905910,171086036641778,199418309034894,
    229523928875936,260902747033836,292945899449652,324951901477770,356151309394434,
    385735516756256,412892232343290,436842717884882,456877844517662,472394284704130,
    482923340082736,488155497249406,487954715765924,482363531543356,471599609336102,
    456041151699228,436206707876456,412726252332194,386309723046152,357712119039068,
    327698795626046,297014250445032,266352337230770,236334670853880,207492804019976,
    180258174149026,154957993420806,131815936845660,110959648392188,92429378221520,
    76191746033526,62153137499930,50173929951268,40082909677996,31688839010836,24792784383222,
    19196189375746,14708705932170,11153425657546,8369658930394,6215662705578,4567910414166,
    3321878769020,2390022185500,1700987480136,1196911852542,832430539284,571578214816,
    387242905538,258474245982,169892299138,109677438590,69195644748,42682936020,25397119214,
    14429392404,7540520824,3548235448,1233636318,248553258]]
private def rkmC_w1024_s1b_2 : List ℤ := pzigCat
  [
   [289959050,63286437,170121645,341117463,577400715,623680199,221634525,1359471156,5093573088,
    13114431724,30109584674,62961250230,123047271010,227942961488,403402351306,688002559782,
    1134977812648,1817621512950,2833201737488,4307216123194,6397489162376,9295021499176,
    13225880359556,18448010817032,25246404977672,33922706513206,44781231775502,58111895630388,
    74167647351030,93141216094364,115138324676266,140154513059268,168053440868758,
    198550592155552,231205792619452,265422988829834,300463266452284,335466483220844,
    369484901560982,401524578639918,430593023587486,455751446515222,476163990412086,
    491144972582994,500196030296130,503033530427408,499602880475318,490078195368164,
    474850286547420,454499787680756,429762847679796,401487225580690,370586544390682,
    337992595637820,304612119891748,271287462714064,238766646161582,207680021184082,
    178528358698148,151678046366982,127365172969044,105705895965652,86710944161082,
    70304316721792,56341180253944,44628383896284,34941188898176,27039992128864,20683157594854,
    15637824748594,11686243207196,8632080500916,6302078835658,4547462525606,3242565325268,
    2284412635798,1589452001778,1091819687090,739813443744,494248450052,325111361570,
    210396201970,133561739882,83041013684,50230418142,29434837680,16389192876,8505376608,
    3997266706,1338276224,252471116]]
private def rkmC_w1024_s1b_3 : List ℤ := pzigCat
  [
   [306074219,519248185,1082017223,1690938247,2314762641,1814891205,1431611330,11926959714,
    37278826106,90089604956,191427009970,374149062946,688408276896,1205655632468,2025964518530,
    3283674432532,5153321830054,7854306271696,11651677917680,16855767603370,23814410692994,
    32901870705526,44498813847128,58968528576478,76626071746184,97704928374526,122320984549522,
    150439908472172,181848071761086,216134377744694,252682381584644,290678198272942,
    329133653576860,366924911899510,402846297636206,435672867204162,464231142542396,
    487467699667526,504514587830554,514741568793140,517794917386456,513616455498842,
    502443589158578,484788538398946,461402148886798,433221488391354,401310895053796,
    366797360909152,330808353466580,294414155263068,258581530625032,224136927693282,
    191744993828032,161898752078746,134922626106238,110983143601530,90109014471474,
    72214305089104,57125073454700,44604573374740,34378093765426,26153757525780,19639640428796,
    14557416160672,10650499885090,7691150906332,5481499944122,3855119278118,2674844379966,
    1830439553746,1234698075550,820492998564,536854499936,345266739038,218123942692,134933482880,
    81513229986,47870804644,26976311324,14511312082,7067303500,2973597064,888899088]]
private def rkmC_w1024_s1b_4 : List ℤ := pzigCat
  [
   [231837768,220246600,353890145,1801708937,3917658061,6736317677,9496795797,9420217331,
    647346171,29048276010,101035421726,252470679316,541705575108,1057398821356,1926467562386,
    3324229435818,5482059521866,8693722137650,13316005523232,19764299016338,28498549265698,
    40001864909142,54746962280916,73156246402424,95553653901416,122115003654278,152819463564974,
    187410081642652,225365333193340,265891391338210,307934776620056,350220368142190,
    391311479975494,429690582551724,463851259471702,492397253859592,514136684131270,
    528164030953902,533921738125072,531235814580058,520322675099514,501765059196128,
    476464815026258,445572068898326,410403243118538,372351052726464,332798738477092,
    293043030256908,254232046636238,217321292712024,183048885917498,151929232587796,
    124261410059172,100152557509774,79546979981000,62261976602416,48024351375420,36503603363312,
    27343005346630,20182975952974,14680731890556,10522403765928,7430972804538,5169930798302,
    3542714746622,2390241891694,1587377935556,1036806019718,665629303546,419627973640,
    259258922094,156702599026,92389810022,52778074682,28958837586,15075081340,7157894342,
    2643935686,679841336]]
private def rkmC_w1024_s1b_5 : List ℤ := pzigCat
  [
   [473896206,798673348,769394166,178444692,1697377167,5252674435,11640625489,20891751795,
    30925687609,34287158189,13959477049,63954592448,258636929604,666935914114,1436662082480,
    2780448729446,4989280971700,8440795060258,13601826217062,21018577787926,31295678987410,
    45057074943728,62895404081564,85307105283472,112620647299758,144924081797470,182000959534656,
    223284297747454,267836821778100,314365934072050,361274162577218,406745911032676,
    448861487590134,485732890762568,515644118146802,537182343282442,549348506062824,
    551630762953904,544039077169990,527093450858718,501770856826150,469416509226320,
    431630668587690,390144033546804,346693899755492,302913058559260,260241380605906,
    219861784782920,182667597104890,149255030568674,119939749648272,94791884460954,
    73680828891524,56326262266186,42348476259442,31313173186132,22770205267116,16283073429770,
    11450010241628,7915986597656,5379833431830,3593124166408,2357307945888,1518533018204,
    959833032984,594559536336,360474215292,213597262976,123310763734,68963959182,37050140590,
    18838583600,8767976970,3444717282,899045654]]
private def rkmC_w1024_s1b_6 : List ℤ := pzigCat
  [
   [266320172,563303088,1101808860,1721437728,2228581754,1520052272,2356090443,12332895259,
    31010433329,59423451977,91546165067,107278840509,60656400023,135708805396,630178563542,
    1655877257448,3550743247182,6775971307498,11920955729408,19692463836866,30882995033812,
    46314677982010,66759435819638,92839492663006,124917569950004,162991292631412,206605541593836,
    254801878810486,306113812023328,358620778568378,410058600777800,457978440279200,
    499941130534620,533722270519902,557506411400500,570046931322926,570770570979868,
    559817488215768,538010564467992,506762016982284,467929777512572,423645093766664,
    376129252426022,327523757626348,279747714550794,234393105603096,192666065345854,
    155369788565616,122924440378408,95416460612962,72664041539014,54289688664110,39792545366566,
    28612264149998,20180600769508,13960235722270,9470125177074,6298296693370,4105305345608,
    2621287111902,1638575967758,1001971960048,598669468082,348938814582,197934509560,
    108841780836,57653772326,28912693336,13634346772,5649584190,1756599686,253016740]]
private def rkmC_w1024_s1b_7 : List ℤ := pzigCat
  [
   [216976075,165627893,515739928,2144509788,5003224672,7870904520,7993543308,627059063,
    25938819947,75736974057,152490224077,241345734215,292192807251,191577711099,271674982672,
    1442339105886,3832961777386,8143569759452,15259652837180,26215586877004,42118504483796,
    64030399270592,92817718238180,128981635040732,172495447267068,222676217117082,
    278117349258722,336706962852726,395738320379854,452109151626018,502591796157670,
    544138749869480,574185823815048,590911279364880,593412878235746,581781521628664,
    557063917742178,521122477487058,476418233073862,425749722500682,371982584940054,
    317804625133366,265532843141770,216986516516254,173430449601914,135582912434130,
    103673964024148,77536775609250,56714643365734,40569348930640,28376841074052,19405685693800,
    12971502812140,8472687656020,5405734537092,3366985177070,2045875721152,1211807642572,
    698580646546,391371945730,212372159970,111190922652,55637042294,26391427520,11394649454,
    4204214300,935053502]]
private def rkmC_w1024_s1b_8 : List ℤ := pzigCat
  [
   [236923808,235254182,367092033,1475721391,1893186357,276964081,4539282948,12722172488,
    22031854282,26292204116,11694447222,42895827831,160121725445,349394025539,576946033775,
    722331055035,521268606573,498413889154,3071189952650,8222678831292,17251884560180,
    31647693916354,52933441643724,82444582724630,121063134788964,168951978446392,225338795189988,
    288400000961354,355285613459328,422301823455484,485240157672982,539815484784710,
    582148314330986,609215924590658,619199669319232,611676988637464,587628164177124,
    549268508572256,499737639674192,442705034558378,381953940268764,321005347542244,
    262829152123592,209665624765854,162960811015514,123405304107350,91043919351718,
    65431740329646,45801346485120,31219825975066,20716547810612,13377726551496,8402472957024,
    5130167109006,3042247658558,1750560211858,975882600306,526006025552,273413003776,
    136286008390,64809382080,28788371238,11542213000,3844197170,741671104]]
private def rkmC_w1024_s1b_9 : List ℤ := pzigCat
  [
   [300844004,912544310,1032624940,113070910,1489711771,3535532597,5306109689,4164633787,
    3893596998,22659789460,50985642664,75086842462,62192328358,40244958183,291444429839,
    719224180271,1253448138513,1630308978971,1280226249685,776029233436,5981891128614,
    16212536194442,33616473038902,60324667354212,98050448121098,147641583891684,208673274674584,
    279181600268052,355624842881510,433120716012572,505947576555866,568245440108420,
    614789745428632,641703000011938,646969431371418,630663158530416,594856203276174,
    543242768191384,480561139994878,411934857019384,342246145802032,275639635213350,
    215209683355550,162887566323844,119501925977492,84965531381350,58529899745898,39049891572496,
    25221214095434,15759824669890,9520162970616,5554337974518,3125817547308,1694086402620,
    882363849660,440324528720,209541066962,94367171712,39609203886,14963282754,4755029962,
    802325014]]
private def rkmC_w1024_s1b_10 : List ℤ := pzigCat
  [
   [570164600,1011054874,1742226050,1826985614,181925028,4765705243,12763852867,18472992363,
    10371736989,25777200482,95651122022,177398579616,203199811622,52841041214,417049937515,
    1293704964317,2458782713777,3387156356223,2936400348303,794964850808,10451429746822,
    29171466246638,60087582486746,105621041639110,166708502226296,242147958884424,
    328267331487108,419062076185974,506845219495368,583318530194714,640858785124096,
    673746140045044,679063281328386,657082050661424,611070947715890,546604916542876,
    470556417036946,390000791795274,311256206637270,239212061197294,177014922542118,
    126091169049228,86422595868770,56962202638702,36077280069738,21935423632836,12787519526588,
    7136549448058,3805236440480,1933809158358,933392977700,425924350250,182362220070,72363368894,
    25946227572,7743313018,1398970490]]
private def rkmC_w1024_s1b_11 : List ℤ := pzigCat
  [
   [553961633,265313459,1795496246,5638445284,7944614896,1519947068,17911311377,44939356339,
    56302192923,13606433019,117738498906,327088870404,503900502904,402121277502,319641209087,
    1927347559621,4292867432573,6475605261517,6341613869109,406010729391,15905641019408,
    47481351685326,98299757561926,170024572162026,260824960308662,364845274021282,
    472617612701006,572445906586824,652486871214216,703018264995526,718305425381856,
    697591904799514,644997786346912,568421851046984,477802627454008,383219675528368,
    293283665463822,214122154821532,149051164006044,98843063919998,62371688824822,37392870101770,
    21256136258596,11427901992292,5791928981456,2755536054334,1223587658812,503189676606,
    189322263094,63586082830,18175844714,3790336994,206870574]]
private def rkmC_w1024_s1b_12 : List ℤ := pzigCat
  [
   [1020931544,1005780738,1246069311,4437846419,3558608465,4747277816,18363834518,25164627214,
    6280289178,51391442247,129776717827,154659160303,7973429131,391519624996,941905472662,
    1220565037822,491278421756,1996943328113,6355873116967,11177106089669,12772938988131,
    5022286230135,19773048078536,68941792745998,146810699611194,252226702284270,377237935921488,
    507666611341458,625691134659954,713792821584254,758880933543598,755302113066472,
    705837232556674,620496434602720,513653876308486,400533153045090,294109704302000,
    203181982266422,131853560752860,80194683945486,45571835242504,24095511605364,11787924761228,
    5295862816290,2162180788820,789963220868,251885530448,66947813668,13292125008,1023459732]]
private def rkmC_w1024_s1b_13 : List ℤ := pzigCat
  [
   [386282984,146956038,1241881845,1459861815,808130784,3592708218,3325060714,2187077901,
    10980429783,14788184291,355312710,39866772656,76915280242,47023741842,106274543223,
    337295534573,421714583171,18005787275,1050754926550,2361373741756,2611671393956,64454150331,
    6886141711411,16512734159417,23270534501955,16771783634921,16065204178998,86583551087904,
    198901522977698,345728447488690,507755620640174,657579466393224,767121727050570,
    815848594576006,796633981448680,717112267114602,596309165090296,458234415691230,
    325079589970368,212377364860002,127254137841956,69507603564638,34303924357170,15100104224048,
    5812589609102,1893950588416,491248379050,86331037862]]
private def rkmHbWin_w1024_s2 : List ℤ := altBuildHbFrom 2048 1024 18254928571 0 1024
private def rkmXsWin_w1024_s2_in : List ℤ := pzigCat
  [
   [246211563,449847853,664225276,1646516488,745125526,1247320507,3020608949,2427494333,
    2713240042,11174330494,10769884184,11898031415,46872749469,45443635113,44797111848,
    192074468292,219697150762,96106705495,729980803095,1119148295108,299655676963,2237629693226,
    5285539726374,5350305839098,1892664263610,17723956081630,35661708173998,39227712045548,
    5389926492868,85877015912710,239599838541998,437857229729832,641454003644952,802097067472116,
    880069172945662,859005053843784,750747971712096,588594801809264,413170427116696,
    258191877545208,142136698479466,67734164757807,27114853032215,8610090623910,1877391169817]]
private def rkmXsWin_w1024_s2_out : List ℤ := pzigCat
  [
   [379220372,2143660473,6148062170,14756395545,32862797534,68699152561,133833445100,
    240657319187,392928184414,568624671075,713500406242,740861454715,597391115454,374641457479,
    352769378628,917234414657,2202672413296,3625517271577,4312867557282,4499645671731,
    5556992037078,7814567949833,9083177008118,5075234648021,6470161099715,15924173335330,
    6005352526751,16312756137743,15127616938406,14918996069776,20442365334887,18939825938879,
    24655669225520,49536930285320,3736508633352,42891166046319,60396480070509,143250459191744,
    369847869987150,792809061050268,987427290020152,998194311270692,926383441869868,
    575367482524188,204165539093532,34272347299420]]
private def rkmC_w1024_s2_1 : List ℤ := pzigCat
  [
   [441349850,191863621,877863175,947454359,923075234,2242564159,14125541398,31718261323,
    86224692138,228954173811,438106870898,702873601911,947205690446,678881424279,124068740297,
    122331333916,1121101656750,2549808316463,3732058424876,2836431624415,1871847703692,
    9511878101451,19934345340244,3903010010699,19805211572649,20936197816998,44472928839454,
    13478463576666,22396392484423,6231943357098,137184827910440,361481540996890,623333016662736,
    847608137462338,944091473830236,938039991023160,710904331752268,596477537833048,
    321917353387408,58482616910336,1609888601691,2662767709101]]
private def rkmHbWin_w1024_s3 : List ℤ := altBuildHbFrom 2048 1024 17386000000 0 1024
private def rkmXsWin_w1024_s3_in : List ℤ := pzigCat
  [
   [379220372,2143660473,6148062170,14756395545,32862797534,68699152561,133833445100,
    240657319187,392928184414,568624671075,713500406242,740861454715,597391115454,374641457479,
    352769378628,917234414658,2202672413296,3625517271578,4312867557282,4499645671732,
    5556992037078,7814567949834,9083177008118,5075234648022,6470161099715,15924173335329,
    6005352526751,16312756137744,15127616938406,14918996069776,20442365334888,18939825938880,
    24655669225520,49536930285320,3736508633352,42891166046320,60396480070510,143250459191744,
    369847869987150,792809061050268,987427290020152,998194311270692,926383441869868,
    575367482524188,204165539093532,34272347299419]]
private def rkmXsWin_w1024_s3_out : List ℤ := pzigCat
  [
   [401800383,2152335192,5681663451,12284678712,24337110767,45204148636,79550898235,133493381464,
    212474228963,317413001508,441618656117,565374868110,655882495213,674082535268,592035040901,
    414920559158,192376278829,2409080688,91819289728,83145293137,21755585820,25134982036,
    19964989177,4168263687,43475171377,69574047984,234915126096,290898498723,662031085561,
    234687218995,1868822865288,1923055626628,6107680137022,2245580417061,4805023895586,
    20133712137518,11863010383618,14256247577181,2154119635352,24768385996289,23783769228060,
    5088717221084,6759891744060,21582620882694,41620545274128,2673161610415,74862645584774,
    7931368475986,90927614817087,203641054299296,597642723595530,1024821736329718,
    1233343282318816,960439311299434,298821149716742]]
private def rkmC_w1024_s3_1 : List ℤ := pzigCat
  [
   [206379575,1277413484,4441492795,10620752476,22327964999,44012656448,82311998171,145330281366,
    240029277469,367029224064,512912725679,643763861048,708362742455,659395997084,488948214643,
    252539777924,46445400119,61672191813,64299550910,21531461092,26216921945,199256367659,
    243491107223,670377928678,2360184732016,3458474519050,3667596070062,3697594293504,
    5839302122996,10930362634440,15019201763292,6883288857077,16925410518667,3364412727523,
    6630384405372,7075418321754,30406405785178,6326403126661,39524782302846,29989644343534,
    23517858090168,23611682494000,45300945160472,10974811730127,235890155536262,678573706868494,
    945920349999472,1131430017892460,992402924305430,556393656669860,83557304294848]]
private def rkmHbWin_w1024_s4 : List ℤ := altBuildHbFrom 2048 1024 17741777777 0 1024
private def rkmXsWin_w1024_s4_in : List ℤ := pzigCat
  [
   [401800383,2152335192,5681663451,12284678712,24337110767,45204148636,79550898235,133493381464,
    212474228963,317413001508,441618656117,565374868110,655882495213,674082535268,592035040901,
    414920559158,192376278829,2409080688,91819289727,83145293137,21755585820,25134982035,
    19964989177,4168263687,43475171377,69574047984,234915126096,290898498723,662031085561,
    234687218995,1868822865288,1923055626628,6107680137022,2245580417062,4805023895586,
    20133712137518,11863010383618,14256247577182,2154119635352,24768385996290,23783769228060,
    5088717221084,6759891744060,21582620882694,41620545274128,2673161610416,74862645584774,
    7931368475986,90927614817088,203641054299296,597642723595530,1024821736329718,
    1233343282318816,960439311299434,298821149716742]]
private def rkmXsWin_w1024_s4_out : List ℤ := pzigCat
  [
   [205589932,1098541725,3324113156,7109495671,13635009392,24262303903,40920494666,66551422139,
    103967080558,156483073765,225796588538,311209496059,407732705800,503613530943,581612635840,
    620126994915,599370608936,510142083259,361571123770,184455841391,26263698792,68456588004,
    82332691271,40676957996,1681793564,4286192615,16011325495,6194175744,31557947214,12595568901,
    83968507717,129295747698,110931224781,213557454182,353953722629,529211619660,1102511211855,
    1231234187522,567242676523,1254779843237,3306688725146,5588159086367,7219057350752,
    4832085257783,576345171082,3348649444149,5889206947528,2785588606698,10203438849685,
    12096747192018,11933968027234,18216296388944,18033514970189,56123424686702,14518090812485,
    37810050199042,4252898667025,25323047785196,9165003843496,58879605479314,41252943281996,
    59282141367173,33062054477708,626710134799872,1494681115539928,1164742189184074]]
private def rkmC_w1024_s4_1 : List ℤ := pzigCat
  [
   [688763962,2405846877,6034738898,12195387563,22914584500,40669681699,68735504048,111428046815,
    172808858068,254872339675,356069322508,466881560205,568870960142,635898122213,640012023024,
    562383161051,407834306864,213453548099,41342259946,48550462204,43546454467,5146357526,
    17698661313,51535280218,20081247862,76702222429,66037672405,29359169709,115803924989,
    125048389552,127428858031,37531606078,522141405225,1463773856604,1357205483497,526911404394,
    307833040885,4175060149283,9178295810006,2625702702445,4069281551228,327399744542,
    19459392812446,16121614016788,690317801878,15774653740306,22744900158258,26433009158268,
    18728215947983,49938736407754,13229559800379,53621250210290,24019896515310,46126515964932,
    6268530918251,118832347391382,554175026021214,1147522294070522,1371870893439434,
    684877348065082]]
private def rkmHbWin_w1024_s5 : List ℤ := altBuildHbFrom 2048 1024 17628615384 0 1024
private def rkmXsWin_w1024_s5_in : List ℤ := pzigCat
  [
   [205589932,1098541725,3324113156,7109495671,13635009392,24262303903,40920494666,66551422139,
    103967080558,156483073765,225796588538,311209496059,407732705800,503613530943,581612635840,
    620126994915,599370608936,510142083259,361571123770,184455841391,26263698792,68456588004,
    82332691271,40676957996,1681793564,4286192615,16011325495,6194175744,31557947214,12595568901,
    83968507717,129295747698,110931224781,213557454182,353953722629,529211619660,1102511211855,
    1231234187521,567242676523,1254779843237,3306688725145,5588159086367,7219057350751,
    4832085257783,576345171082,3348649444150,5889206947528,2785588606698,10203438849686,
    12096747192018,11933968027234,18216296388943,18033514970189,56123424686701,14518090812485,
    37810050199041,4252898667025,25323047785195,9165003843495,58879605479313,41252943281995,
    59282141367173,33062054477708,626710134799872,1494681115539928,1164742189184074]]
private def rkmXsWin_w1024_s5_out : List ℤ := pzigCat
  [
   [205943696,1053288937,3085963108,6469797997,11962857936,20287831959,33209531080,52149078081,
    79401360740,117119746177,167017085842,230218383205,305189901666,387966697881,470293277528,
    540067504221,582670891354,583059975725,531490742054,427429162329,283981534970,127676415611,
    7696863115,91187480776,109282213359,73366528628,16768283151,21697879577,23051637626,
    187328766,17907026219,16317193040,19304121241,64732239208,149785386753,223318377740,
    259966260855,313914634790,417699762781,444842634384,221056714459,190401186109,452293189506,
    210195352505,464303505845,577876483770,414456798924,445309223833,383926819611,1548310989885,
    1533438689726,1811259715723,1506974409425,9950204867495,4445936082825,7915326486325,
    11487070245080,13572490761375,17843992885610,6116395365735,34857969380010,930814607107,
    3271972055333,42721667053217,23399558698137,46252300876959,7166818464963,14507468950509,
    42561447560209,4020954688650,114721461962647,305697948278923,887398646350942,
    1759890751114748]]
private def rkmHbWin_w1024_s6 : List ℤ := altBuildHbFrom 2048 1024 18161428571 0 1024
private def rkmXsWin_w1024_s6_in : List ℤ := pzigCat
  [
   [205943696,1053288937,3085963108,6469797997,11962857936,20287831959,33209531080,52149078081,
    79401360740,117119746177,167017085842,230218383205,305189901666,387966697881,470293277528,
    540067504221,582670891354,583059975725,531490742054,427429162329,283981534970,127676415611,
    7696863115,91187480776,109282213359,73366528628,16768283151,21697879577,23051637626,
    187328766,17907026219,16317193040,19304121241,64732239208,149785386753,223318377740,
    259966260855,313914634790,417699762782,444842634383,221056714459,190401186109,452293189506,
    210195352505,464303505845,577876483770,414456798924,445309223833,383926819611,1548310989886,
    1533438689726,1811259715723,1506974409425,9950204867495,4445936082825,7915326486325,
    11487070245079,13572490761375,17843992885609,6116395365736,34857969380010,930814607108,
    3271972055334,42721667053218,23399558698138,46252300876960,7166818464964,14507468950510,
    42561447560210,4020954688650,114721461962648,305697948278924,887398646350942,
    1759890751114748]]
private def rkmXsWin_w1024_s6_out : List ℤ := pzigCat
  [
   [689047706,2102703931,4747062388,8901061337,15446869388,25102647823,39359872476,59707367339,
    88208136428,126363733221,175699546746,236427620855,307329935408,384097088639,459993671748,
    524444412531,565283457470,570088523009,529566347204,442041501953,315479738044,169514106323,
    31402405496,70727753114,117237171973,106637200748,57167706069,1070331894,31288439630,
    27937526649,749342462,24665359448,34310382641,41518547352,74620323733,143469710696,
    214754291937,229208966220,140725055997,65735591573,334298329144,415904259701,51349177522,
    183304114948,463849394566,158147969925,603137923807,339975552104,142220166942,492174025567,
    245138431767,754569541958,578546892962,2256939800455,2512103050510,1608230523089,
    4335641419492,781764909461,5343898118005,3839006887091,8114751645187,5092893150133,
    8664930828835,35067086949023,1178313156174,29484946251358,8962712261085,21100478999326,
    11958370569270,44903680229170,38650840090636,493073504232,48282536751748,2700850579245,
    30254254496522,80498232805738,470768065980980,1939617500208732]]
private def rkmHbWin_w1024_s7 : List ℤ := altBuildHbFrom 2048 1024 17890666666 0 1024
private def rkmXsWin_w1024_s7_in : List ℤ := pzigCat
  [
   [689047706,2102703931,4747062388,8901061337,15446869388,25102647823,39359872476,59707367339,
    88208136428,126363733221,175699546746,236427620855,307329935408,384097088639,459993671748,
    524444412531,565283457470,570088523009,529566347204,442041501953,315479738044,169514106323,
    31402405496,70727753114,117237171973,106637200748,57167706069,1070331894,31288439630,
    27937526649,749342462,24665359448,34310382641,41518547352,74620323733,143469710696,
    214754291937,229208966220,140725055997,65735591573,334298329144,415904259701,51349177522,
    183304114948,463849394566,158147969926,603137923807,339975552104,142220166942,492174025567,
    245138431767,754569541958,578546892962,2256939800456,2512103050510,1608230523090,
    4335641419491,781764909462,5343898118005,3839006887091,8114751645187,5092893150133,
    8664930828836,35067086949023,1178313156173,29484946251358,8962712261085,21100478999326,
    11958370569270,44903680229170,38650840090636,493073504231,48282536751748,2700850579246,
    30254254496522,80498232805738,470768065980980,1939617500208732]]
private def rkmXsWin_w1024_s7_out : List ℤ := pzigCat
  [
   [687515878,2067158553,4585214728,8443629401,14450591422,23231563369,36061878840,54073258277,
    79066199392,112467536889,155780147766,209333298393,272673806634,343120452659,415882189964,
    483013338837,534775094590,559959750117,548741101790,494920041981,399777123984,272930933873,
    133693569820,6433779509,84730101999,124053135532,111222374605,62168444674,5091596107,
    32334471851,35783652734,10829840999,21666406941,43300481064,53516955231,71338132810,
    115465829397,176333065008,210776851191,166798973724,24014266563,179488830899,343939861362,
    333652437725,99785819852,130815439840,29440880419,108421895927,394934000183,683026628520,
    303697322164,325178747259,8571293482,540517455510,643919623547,52491556910,425831096385,
    743654847950,834573418239,6068376466558,714610202877,1227267669026,1634081893683,
    2924401014911,2137092849502,22808593017713,14818139425806,2528284989071,39114448836625,
    14510494394430,1733073624435,13643334501534,1661388514142,17322240841088,58773288728526,
    3748912230798,44116955352770,15443656734692,21455442421676,7915433195820,46512152545364,
    1997153387209000]]
private def rkmWalksHi_w1024_r1024 : List RkmWinSegWalk := [
  ⟨1024, rkmHbWin_w1024_s0, 0, rkmXsWin_w1024_s0_in, 320, rkmXsWin_w1024_s0_out, 54371008152⟩,
  ⟨1024, rkmHbWin_w1024_s1a, 320, rkmXsWin_w1024_s1a_in, 980, rkmXsWin_w1024_s1b_out, 95908977724⟩,
  ⟨1024, rkmHbWin_w1024_s2, 980, rkmXsWin_w1024_s2_in, 979, rkmXsWin_w1024_s2_out, 1653447271⟩,
  ⟨1024, rkmHbWin_w1024_s3, 979, rkmXsWin_w1024_s3_in, 970, rkmXsWin_w1024_s3_out, 897649597⟩,
  ⟨1024, rkmHbWin_w1024_s4, 970, rkmXsWin_w1024_s4_in, 959, rkmXsWin_w1024_s4_out, 770264023⟩,
  ⟨1024, rkmHbWin_w1024_s5, 959, rkmXsWin_w1024_s5_in, 951, rkmXsWin_w1024_s5_out, 594573674⟩,
  ⟨1024, rkmHbWin_w1024_s6, 951, rkmXsWin_w1024_s6_in, 947, rkmXsWin_w1024_s6_out, 316881225⟩,
  ⟨1024, rkmHbWin_w1024_s7, 947, rkmXsWin_w1024_s7_in, 943, rkmXsWin_w1024_s7_out, 243238417⟩
  ]
private theorem rkmWC_w1024_s1b_0 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1b
    843 rkmXsWin_w1024_s1b_in 862 rkmC_w1024_s1b_1 2576859389 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_1 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1b
    862 rkmC_w1024_s1b_1 873 rkmC_w1024_s1b_2 2608452921 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_2 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    873 rkmC_w1024_s1b_2 890 rkmC_w1024_s1b_3 2701834242 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_3 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    890 rkmC_w1024_s1b_3 903 rkmC_w1024_s1b_4 2464311933 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_4 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    903 rkmC_w1024_s1b_4 915 rkmC_w1024_s1b_5 2170895915 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_5 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    915 rkmC_w1024_s1b_5 926 rkmC_w1024_s1b_6 1926142903 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_6 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    926 rkmC_w1024_s1b_6 937 rkmC_w1024_s1b_7 2138773219 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_7 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    937 rkmC_w1024_s1b_7 945 rkmC_w1024_s1b_8 1898516879 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_8 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    945 rkmC_w1024_s1b_8 953 rkmC_w1024_s1b_9 1893209446 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_9 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    953 rkmC_w1024_s1b_9 962 rkmC_w1024_s1b_10 2019740927 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_10 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    962 rkmC_w1024_s1b_10 970 rkmC_w1024_s1b_11 1954727957 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_11 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    970 rkmC_w1024_s1b_11 975 rkmC_w1024_s1b_12 1626093573 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_12 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    975 rkmC_w1024_s1b_12 977 rkmC_w1024_s1b_13 1068386808 = true := by decide +kernel
private theorem rkmWC_w1024_s1b_13 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1b
    977 rkmC_w1024_s1b_13 980 rkmXsWin_w1024_s1b_out 948086697 = true := by decide +kernel
private theorem rkmWC_w1024_s2_0 : wSlChk 14 100000000 1024 rkmHbWin_w1024_s2
    980 rkmXsWin_w1024_s2_in 983 rkmC_w1024_s2_1 1006500697 = true := by decide +kernel
private theorem rkmWC_w1024_s2_1 : wSlChk 14 100000000 1024 rkmHbWin_w1024_s2
    983 rkmC_w1024_s2_1 979 rkmXsWin_w1024_s2_out 646946574 = true := by decide +kernel
private theorem rkmWC_w1024_s3_0 : wSlChk 9 100000000 1024 rkmHbWin_w1024_s3
    979 rkmXsWin_w1024_s3_in 974 rkmC_w1024_s3_1 503635994 = true := by decide +kernel
private theorem rkmWC_w1024_s3_1 : wSlChk 8 100000000 1024 rkmHbWin_w1024_s3
    974 rkmC_w1024_s3_1 970 rkmXsWin_w1024_s3_out 394013603 = true := by decide +kernel
private theorem rkmWC_w1024_s4_0 : wSlChk 9 100000000 1024 rkmHbWin_w1024_s4
    970 rkmXsWin_w1024_s4_in 965 rkmC_w1024_s4_1 403145061 = true := by decide +kernel
private theorem rkmWC_w1024_s4_1 : wSlChk 9 100000000 1024 rkmHbWin_w1024_s4
    965 rkmC_w1024_s4_1 959 rkmXsWin_w1024_s4_out 367118962 = true := by decide +kernel
private theorem rkmWC_w1024_s5_0 : wSlChk 13 100000000 1024 rkmHbWin_w1024_s5
    959 rkmXsWin_w1024_s5_in 951 rkmXsWin_w1024_s5_out 594573674 = true := by decide +kernel
private theorem rkmWC_w1024_s6_0 : wSlChk 7 100000000 1024 rkmHbWin_w1024_s6
    951 rkmXsWin_w1024_s6_in 947 rkmXsWin_w1024_s6_out 316881225 = true := by decide +kernel
private theorem rkmWC_w1024_s7_0 : wSlChk 6 100000000 1024 rkmHbWin_w1024_s7
    947 rkmXsWin_w1024_s7_in 943 rkmXsWin_w1024_s7_out 243238417 = true := by decide +kernel
private theorem rkmWinSt_w1024_t2 : rkmAllTrueF [
  Nat.ble (Nat.add 980 (altIntLen rkmXsWin_w1024_s2_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 979 (altIntLen rkmXsWin_w1024_s3_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 970 (altIntLen rkmXsWin_w1024_s4_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 959 (altIntLen rkmXsWin_w1024_s5_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 951 (altIntLen rkmXsWin_w1024_s6_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 947 (altIntLen rkmXsWin_w1024_s7_in)) (Nat.add 1024 1),
  muxIntListEq rkmHbWin_w1024_s1a rkmHbWin_w1024_s1b,
  muxIntListEq rkmXsWin_w1024_s1a_out rkmXsWin_w1024_s1b_in,
  Nat.ble (Nat.add 320 (altIntLen rkmXsWin_w1024_s1a_in)) (Nat.add 1024 1),
  rkmCheckRowFromWinWalks 1024 8 1024 [1, 2, 2, 2, 2, 2, 2, 2]
    [11608976, 11150000, 511138, 295562, 319352, 229172, 127130, 107344]
    [392, 606, 28, 17, 18, 13, 7, 6]
    rkmMasksHi_w1024_r1024 rkmWalksHi_w1024_r1024 rkmRowHi_w1024_r1024,
  muxIntListEq rkmHbF_w1024_s1b rkmHbWin_w1024_s1b
  ] = true := by decide +kernel
private theorem rkmWinIterF_w1024_s1b :
    RkmWinIterSound 226 1024 rkmHbF_w1024_s1b 843 rkmXsWin_w1024_s1b_in
      980 rkmXsWin_w1024_s1b_out 27996032809 :=
  rkmChS 226 27996032809 (rkmChS 210 27047946112 (rkmChS 194 25979559304 (rkmChS 178 24353465731
    (rkmChS 162 22398737774 (rkmChS 146 20378996847 (rkmChS 130 18485787401 (rkmChS 114
    16587270522 (rkmChS 98 14448497303 (rkmChS 82 12522354400 (rkmChS 66 10351458485 (rkmChS 50
    7887146552 (rkmChS 34 5185312310 (wSlChk_sound rkmWC_w1024_s1b_0) rkmWC_w1024_s1b_1 rfl rfl)
    rkmWC_w1024_s1b_2 rfl rfl) rkmWC_w1024_s1b_3 rfl rfl) rkmWC_w1024_s1b_4 rfl rfl)
    rkmWC_w1024_s1b_5 rfl rfl) rkmWC_w1024_s1b_6 rfl rfl) rkmWC_w1024_s1b_7 rfl rfl)
    rkmWC_w1024_s1b_8 rfl rfl) rkmWC_w1024_s1b_9 rfl rfl) rkmWC_w1024_s1b_10 rfl rfl)
    rkmWC_w1024_s1b_11 rfl rfl) rkmWC_w1024_s1b_12 rfl rfl) rkmWC_w1024_s1b_13 rfl rfl
private theorem rkmWinIterSnd_w1024_s1b :
    RkmWinIterSound 226 1024 rkmHbWin_w1024_s1b 843 rkmXsWin_w1024_s1b_in
      980 rkmXsWin_w1024_s1b_out 27996032809 :=
  rkmSubstHb (rkmWP0 (rkmWT5 (rkmWT5 rkmWinSt_w1024_t2))) rkmWinIterF_w1024_s1b
private theorem rkmWinIter_w1024_s2 :
    RkmWinIterSound 28 1024 rkmHbWin_w1024_s2 980 rkmXsWin_w1024_s2_in
      979 rkmXsWin_w1024_s2_out 1653447271 :=
  rkmChS 28 1653447271 (wSlChk_sound rkmWC_w1024_s2_0) rkmWC_w1024_s2_1 rfl rfl
private theorem rkmWinIter_w1024_s3 :
    RkmWinIterSound 17 1024 rkmHbWin_w1024_s3 979 rkmXsWin_w1024_s3_in
      970 rkmXsWin_w1024_s3_out 897649597 :=
  rkmChS 17 897649597 (wSlChk_sound rkmWC_w1024_s3_0) rkmWC_w1024_s3_1 rfl rfl
private theorem rkmWinIter_w1024_s4 :
    RkmWinIterSound 18 1024 rkmHbWin_w1024_s4 970 rkmXsWin_w1024_s4_in
      959 rkmXsWin_w1024_s4_out 770264023 :=
  rkmChS 18 770264023 (wSlChk_sound rkmWC_w1024_s4_0) rkmWC_w1024_s4_1 rfl rfl
private theorem rkmWinIter_w1024_s5 :
    RkmWinIterSound 13 1024 rkmHbWin_w1024_s5 959 rkmXsWin_w1024_s5_in
      951 rkmXsWin_w1024_s5_out 594573674 :=
  wSlChk_sound rkmWC_w1024_s5_0
private theorem rkmWinIter_w1024_s6 :
    RkmWinIterSound 7 1024 rkmHbWin_w1024_s6 951 rkmXsWin_w1024_s6_in
      947 rkmXsWin_w1024_s6_out 316881225 :=
  wSlChk_sound rkmWC_w1024_s6_0
private theorem rkmWinIter_w1024_s7 :
    RkmWinIterSound 6 1024 rkmHbWin_w1024_s7 947 rkmXsWin_w1024_s7_in
      943 rkmXsWin_w1024_s7_out 243238417 :=
  wSlChk_sound rkmWC_w1024_s7_0
private theorem rkmWinSegWalkSnd_w1024_s2 :
    RkmWinSegWalkSound 28 ⟨1024, rkmHbWin_w1024_s2, 980, rkmXsWin_w1024_s2_in,
      979, rkmXsWin_w1024_s2_out, 1653447271⟩ :=
  @rkmSegWalk_mk 28 1024 980 979 1653447271
    rkmHbWin_w1024_s2 rkmXsWin_w1024_s2_in rkmXsWin_w1024_s2_out
    (rkmw_buildHbFrom_length 2048 1024 18254928571 1024 0)
    (rkmWP0 rkmWinSt_w1024_t2) rkmWinIter_w1024_s2
private theorem rkmWinSegWalkSnd_w1024_s3 :
    RkmWinSegWalkSound 17 ⟨1024, rkmHbWin_w1024_s3, 979, rkmXsWin_w1024_s3_in,
      970, rkmXsWin_w1024_s3_out, 897649597⟩ :=
  @rkmSegWalk_mk 17 1024 979 970 897649597
    rkmHbWin_w1024_s3 rkmXsWin_w1024_s3_in rkmXsWin_w1024_s3_out
    (rkmw_buildHbFrom_length 2048 1024 17386000000 1024 0)
    (rkmWP1 rkmWinSt_w1024_t2) rkmWinIter_w1024_s3
private theorem rkmWinSegWalkSnd_w1024_s4 :
    RkmWinSegWalkSound 18 ⟨1024, rkmHbWin_w1024_s4, 970, rkmXsWin_w1024_s4_in,
      959, rkmXsWin_w1024_s4_out, 770264023⟩ :=
  @rkmSegWalk_mk 18 1024 970 959 770264023
    rkmHbWin_w1024_s4 rkmXsWin_w1024_s4_in rkmXsWin_w1024_s4_out
    (rkmw_buildHbFrom_length 2048 1024 17741777777 1024 0)
    (rkmWP2 rkmWinSt_w1024_t2) rkmWinIter_w1024_s4
private theorem rkmWinSegWalkSnd_w1024_s5 :
    RkmWinSegWalkSound 13 ⟨1024, rkmHbWin_w1024_s5, 959, rkmXsWin_w1024_s5_in,
      951, rkmXsWin_w1024_s5_out, 594573674⟩ :=
  @rkmSegWalk_mk 13 1024 959 951 594573674
    rkmHbWin_w1024_s5 rkmXsWin_w1024_s5_in rkmXsWin_w1024_s5_out
    (rkmw_buildHbFrom_length 2048 1024 17628615384 1024 0)
    (rkmWP3 rkmWinSt_w1024_t2) rkmWinIter_w1024_s5
private theorem rkmWinSegWalkSnd_w1024_s6 :
    RkmWinSegWalkSound 7 ⟨1024, rkmHbWin_w1024_s6, 951, rkmXsWin_w1024_s6_in,
      947, rkmXsWin_w1024_s6_out, 316881225⟩ :=
  @rkmSegWalk_mk 7 1024 951 947 316881225
    rkmHbWin_w1024_s6 rkmXsWin_w1024_s6_in rkmXsWin_w1024_s6_out
    (rkmw_buildHbFrom_length 2048 1024 18161428571 1024 0)
    (rkmWP4 rkmWinSt_w1024_t2) rkmWinIter_w1024_s6
private theorem rkmWinSegWalkSnd_w1024_s7 :
    RkmWinSegWalkSound 6 ⟨1024, rkmHbWin_w1024_s7, 947, rkmXsWin_w1024_s7_in,
      943, rkmXsWin_w1024_s7_out, 243238417⟩ :=
  @rkmSegWalk_mk 6 1024 947 943 243238417
    rkmHbWin_w1024_s7 rkmXsWin_w1024_s7_in rkmXsWin_w1024_s7_out
    (rkmw_buildHbFrom_length 2048 1024 17890666666 1024 0)
    (rkmWP0 (rkmWT5 rkmWinSt_w1024_t2)) rkmWinIter_w1024_s7
private theorem rkmWinChain_w1024_s1_full :
    RkmWinIterSound 606 1024 rkmHbWin_w1024_s1a 320 rkmXsWin_w1024_s1a_in
      980 rkmXsWin_w1024_s1b_out 95908977724 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w1024_s1a) (hb2 := rkmHbWin_w1024_s1b)
    (x1 := rkmXsWin_w1024_s1a_out) (x1' := rkmXsWin_w1024_s1b_in) rfl rfl
    (rkmWP1 (rkmWT5 rkmWinSt_w1024_t2)) rfl (rkmWP2 (rkmWT5 rkmWinSt_w1024_t2))
    rkmWinIterSnd_w1024_s1a rkmWinIterSnd_w1024_s1b
private theorem rkmWinSegWalkSnd_w1024_s1 :
    RkmWinSegWalkSound 606 ⟨1024, rkmHbWin_w1024_s1a, 320, rkmXsWin_w1024_s1a_in,
      980, rkmXsWin_w1024_s1b_out, 95908977724⟩ :=
  @rkmSegWalk_mk 606 1024 320 980 95908977724
    rkmHbWin_w1024_s1a rkmXsWin_w1024_s1a_in rkmXsWin_w1024_s1b_out
    (rkmw_buildHbFrom_length 2048 1024 18399339933 1024 0)
    (rkmWP3 (rkmWT5 rkmWinSt_w1024_t2)) rkmWinChain_w1024_s1_full
private theorem rkmWalksSndHi_w1024_r1024 :
    RkmWinSegWalksSound [392, 606, 28, 17, 18, 13, 7, 6] rkmWalksHi_w1024_r1024 :=
  ⟨rkmWinSegWalkSnd_w1024_s0,
  ⟨rkmWinSegWalkSnd_w1024_s1,
  ⟨rkmWinSegWalkSnd_w1024_s2,
  ⟨rkmWinSegWalkSnd_w1024_s3,
  ⟨rkmWinSegWalkSnd_w1024_s4,
  ⟨rkmWinSegWalkSnd_w1024_s5,
  ⟨rkmWinSegWalkSnd_w1024_s6,
  ⟨rkmWinSegWalkSnd_w1024_s7,
    trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic `w1024` `r = 1024` hit certificate (`m = 1024`). -/
theorem rkmTrajHitHi_w1024_m1024 :
    RkmAnchorHitSound 1024 ⟨1024, [1, 2, 2, 2, 2, 2, 2, 2],
      [11608976, 11150000, 511138, 295562, 319352, 229172, 127130, 107344],
      [392, 606, 28, 17, 18, 13, 7, 6], rkmMasksHi_w1024_r1024, rkmRowHi_w1024_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 1024 8 1024 [1, 2, 2, 2, 2, 2, 2, 2]
    [11608976, 11150000, 511138, 295562, 319352, 229172, 127130, 107344]
    [392, 606, 28, 17, 18, 13, 7, 6] rkmMasksHi_w1024_r1024
    rkmWalksHi_w1024_r1024 rkmRowHi_w1024_r1024
    rkmWalksSndHi_w1024_r1024 (rkmWP4 (rkmWT5 rkmWinSt_w1024_t2))
/-- Cumulative `w1024` part `2` lane witness. -/
theorem rkmHiLane_w1024_wint2 : @rkmTrajHitHi_w1024_m1024 = @rkmTrajHitHi_w1024_m1024 :=
  (And.intro (Eq.refl rkmHiLane_w1024_wint1) rfl).right

end
end QuantumComputation.Specs.DickeSol
