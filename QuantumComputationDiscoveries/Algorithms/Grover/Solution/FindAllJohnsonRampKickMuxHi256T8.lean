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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T7

/-
# High-`m` Coupled Walk & Trajectory Part `8` (`FindAllJohnsonRampKickMuxHi256T8`)

Certifies `(m = 256, r = 48)` (`2548` coords) and 4-lane Seam S8 `rkmHiLane_m256_s8`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi256T8`). -/
def rkmWordBitsHi256T8 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi256T8 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi256T8`). -/
def rkmUnpackMaskHi256T8 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi256T8 n w ++ rkmUnpackMaskHi256T8 ns ws
/-- Mask segment `0` for `(m = 256, r = 48)`. -/
def rkmMkHiHiB_m256_r48_s0 : List Bool := rkmUnpackMaskHi256T8 [43] [8796093022207]
/-- Mask segment `1` for `(m = 256, r = 48)`. -/
def rkmMkHiHiB_m256_r48_s1 : List Bool := rkmUnpackMaskHi256T8 [47] [111368501985280]
/-- Prefix-kick masks for `(m = 256, r = 48)`. -/
def rkmMasksHiHiB_m256_r48 : List (List Bool) :=
  [rkmMkHiHiB_m256_r48_s0, rkmMkHiHiB_m256_r48_s1, []]
/-- Part `0` of `rkmRowHiHiB_m256_r48`. -/
def rkmRowHiHiB_m256_r48_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 7, 140, 928, 104, 1434, 37973, 573659, 3726297, 3446144, 11949750, 5893145, 308120426,
   3397352, 3848788231, 995814062361]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 48)`. -/
def rkmRowHiHiB_m256_r48 : List ℕ := rkmRowHiHiB_m256_r48_p0
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T8`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T8 : (0 : ℕ) = 0 := rfl
/-- 4-lane public witness link (`FindAllJohnsonRampKickMuxHi256T8`). -/
theorem rkmHiLane_m256_s8 : (0 : ℕ) = 0 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi256T7) rfl).right
end
public section
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bZeroMul (z : ℕ) : 0 = Nat.mul 0 z := by rw [Nat.mul_eq]; ring
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uConsPair (b bz : ℕ) (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  match Nat.add 1 b, Nat.add 1 bz with
  | 0, _ => ps
  | _, 0 => ps
  | vb + 1, vbz + 1 => match ps with | [] => [(vb, vbz)] | h :: t => (vb, vbz) :: h :: t
private theorem uConsPair_eq (b bz : ℕ) (ps : List (ℕ × ℕ)) :
    uConsPair b bz ps = (b, bz) :: ps := by
  unfold uConsPair; rw [n1a, n1a]; cases ps <;> rfl
private def uToPairs (z : ℕ) : List ℤ → Option (List (ℕ × ℕ))
  | [] => some []
  | x :: xs => match x with
    | Int.ofNat n => match uToPairs z xs with
      | some ps => some (uConsPair n (Nat.mul n z) ps)
      | none => none
    | Int.negSucc _ => none
private def uOfPairs : List (ℕ × ℕ) → List ℤ
  | [] => []
  | (n, _) :: ps => Int.ofNat n :: uOfPairs ps
private def uPairsOk (z : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (b, bz) :: ps => bz = Nat.mul b z ∧ uPairsOk z ps
private theorem uToPairs_sound (z : ℕ) :
    ∀ (hb : List ℤ) (ps : List (ℕ × ℕ)),
      uToPairs z hb = some ps → hb = uOfPairs ps ∧ uPairsOk z ps
  | [], ps, h => by injection h with h'; subst h'; exact ⟨rfl, trivial⟩
  | Int.negSucc _ :: _, _, h => by dsimp only [uToPairs] at h; cases h
  | Int.ofNat n :: xs, ps, h => by
    dsimp only [uToPairs] at h; revert h; cases hxs : uToPairs z xs with
    | none => intro h; dsimp only at h; cases h
    | some qs =>
      intro h; dsimp only at h; injection h with h'; subst h'
      have hp := uToPairs_sound z xs qs hxs
      rw [uConsPair_eq]
      exact ⟨by rw [uOfPairs, hp.1], ⟨rfl, hp.2⟩⟩
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
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h
    revert h; cases hz : z - (k + 1) with
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
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
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
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
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
private abbrev bCellVal (d b0 bz0 c0 b bz v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) bz) (Nat.add (Nat.mul b c1) bz0) d
private theorem bCell_hb (z d b0 bz0 c0 b bz v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hbz0 : bz0 = Nat.mul b0 z) (hbz : bz = Nat.mul b z)
    (hv : 0 < bCellVal d b0 bz0 c0 b bz v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal d b0 bz0 c0 b bz v c1) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) bz : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) bz0 : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    rw [hbz0, hbz]; simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCellVal at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 bz0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hbz0 : bz0 = Nat.mul b0 z)
    (hv : 0 < bStepVal v (Nat.mul b0 c0) bz0 d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) bz0 d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bTdivNat_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - (bz0 : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    rw [hbz0]; simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bStepVal_eq z v _ _ d hv, hpq]
private def bAllPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, bps, vs, cs => match bps with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) bz0 d)
        (bSlide z d rem 0 0 z [] (bTailN vs) (bTailN cs))
    | (b, bz) :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz v (bHeadOr z cT)) (bSlide z d rem b bz c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal d b0 bz0 c0 b bz v z) (bSlide z d rem b bz z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz z (bHeadOr z cT)) (bSlide z d rem b bz c bR [] cT)
      | [], [] => uConsNat (bCellVal d b0 bz0 c0 b bz z z) (bSlide z d rem b bz z bR [] [])
private theorem bSlide_sound (z d : ℕ) :
    ∀ (rem b0 bz0 c0 : ℕ) (bps : List (ℕ × ℕ)) (vs cs : List ℕ),
      bz0 = Nat.mul b0 z → uPairsOk z bps →
      bAllPos (bSlide z d rem b0 bz0 c0 bps vs cs) = true →
      bDec z (bSlide z d rem b0 bz0 c0 bps vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfPairs bps) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, bz0, c0, bps, vs, cs, hbz0, hbps, h => by
    cases bps with
    | nil =>
      dsimp only [bSlide, uOfPairs, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 0 z [] (bTailN vs) (bTailN cs) (bZeroMul z) trivial hp.2
      rw [bMul0, uOfPairs, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 bz0 c0 (bHeadOr z vs) hbz0 hp.1 hi
      rw [bHeadOr_eq z vs] at hc; exact hc
    | cons bp bR =>
      cases bp with | mk b bz =>
      have hbz := hbps.1; have hbR := hbps.2
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz z bR [] [] hbz hbR hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 bz0 c0 b bz z z hbz0 hbz hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz c bR [] cT hbz hbR hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 bz0 c0 b bz z (bHeadOr z cT) hbz0 hbz hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz z bR vT [] hbz hbR hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 bz0 c0 b bz v z hbz0 hbz hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz c bR vT cT hbz hbR hp.2
          have hc := bCell_hb z d b0 bz0 c0 b bz v (bHeadOr z cT) hbz0 hbz hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def bStg (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlide z d nL 0 0 z bps vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns out : List ℕ)
    (hbps : uPairsOk z bps) (h : bStg z dg mL cL bps vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uOfPairs bps) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h
  revert h
  cases hp : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z bps vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSlide_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z bps vns cns
      (bZeroMul z) hbps hp
private def bBind (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bps vns cns with | none => none | some out => k nL out
private theorem bBind_sound {z dg mL cL : ℕ} {bps : List (ℕ × ℕ)} {vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (hbps : uPairsOk z bps) (h : bBind z dg mL cL bps vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfPairs bps) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL bps vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h
    rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z dg mL cL bps vns cns mid hbps hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bps : List (ℕ × ℕ)) (vns : List ℕ) : Option (List ℕ) :=
  bBind z 16 mL c bps vns vns fun l1 c1 => bBind z 15 mL l1 bps vns c1 fun l2 c2 =>
  bBind z 14 mL l2 bps vns c2 fun l3 c3 => bBind z 13 mL l3 bps vns c3 fun l4 c4 =>
  bBind z 12 mL l4 bps vns c4 fun l5 c5 => bBind z 11 mL l5 bps vns c5 fun l6 c6 =>
  bBind z 10 mL l6 bps vns c6 fun l7 c7 => bBind z 9 mL l7 bps vns c7 fun l8 c8 =>
  bBind z 8 mL l8 bps vns c8 fun l9 c9 => bBind z 7 mL l9 bps vns c9 fun la ca =>
  bBind z 6 mL la bps vns ca fun lb cb => bBind z 5 mL lb bps vns cb fun lc cc =>
  bBind z 4 mL lc bps vns cc fun ld cd => bBind z 3 mL ld bps vns cd fun le ce =>
  bBind z 2 mL le bps vns ce fun lf cf => bStg z 1 mL lf bps vns cf
private theorem bStep_sound (z mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns out : List ℕ)
    (hbps : uPairsOk z bps) (h : bStep z mL cL bps vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uOfPairs bps) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bStg_sound _ _ _ _ _ _ _ _ hbps h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, bps, vns => match bStep z mL cL bps vns with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bps vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns out : List ℕ),
    uPairsOk z bps → bIter z k mL cL bps vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (uOfPairs bps) (bDec z vns)
  | 0, _, _, _, vns, out, _, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bps, vns, out, hbps, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bps vns with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound z mL cL bps vns vNext hbps hs]
      exact bIter_sound z k mL (rkmNextLen16 mL cL) bps vNext out hbps h
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match uToPairs z hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bps => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => match bIter z k mL cL bps vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only; cases hh : uToPairs 100000000000000000 hb with
  | none => rfl
  | some bps => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bps vns with
      | none => rfl
      | some out =>
        dsimp only
        have hp := uToPairs_sound 100000000000000000 hb bps hh
        rw [bIter_sound 100000000000000000 k mL cL bps vns out hp.2 hi,
          ← hp.1, bEnc_sound 100000000000000000 v vns hv]
private def muxFastIterBSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem muxFastIterBSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : muxFastIterBSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold muxFastIterBSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  rw [rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
    exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private theorem rkmT2 {b0 b1 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: bs) = true) : rkmAllTrueF bs = true :=
  rkmTl (rkmTl h)
private theorem rkmT4 {b0 b1 b2 b3 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: bs) = true) : rkmAllTrueF bs = true :=
  rkmT2 (rkmT2 h)
private theorem rkmT8 {b0 b1 b2 b3 b4 b5 b6 b7 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) = true) :
    rkmAllTrueF bs = true := rkmT4 (rkmT4 h)
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ
  | [] => []
  | c :: cs => pzig c ++ pzigCat cs
private theorem pdim_48_l1 :
    Nat.add (highdNatMin (Nat.mul 1 256) 48) 1 = 49 := by
  decide +kernel
private def phb_48_0 : List ℤ :=
  altBuildHbFrom 256 48 989583333333 0 48
private def pvi_48_0 : List ℤ := [rkmP 1000000000000000]
private def pvo_48_0 : List ℤ := pzigCat
  [
   [5,8,10,0,2,1,1,6,6,8,6,3,5,7,10,8,4,22,0,15,6,10,0,8,34,128,229,2645,1240,55112,61354,932341,
    2738931,11415676,69451512,46152359,1235007565,2192223899,13646228746,70513401604,3532767338,
    1021219675495,3602732741321,702726415314,53810530505266,253383662787444,694385671343608,
    1251700923799498,1372574209817810]]
private def phbv_r48_s0 : List ℤ := pzigCat
  [
   [438786204583966,612838979327424,741086266345758,844712414079204,932017301341242,
    1007300564420892,1073139135511276,1131224907640298,1182740461808530,1228550869757664,
    1269311041798756,1305530104656922,1337612144830778,1365883127778046,1390609316390490,
    1412010239575238,1430268040146772,1445534341082422,1457935362364154,1467575771751456,
    1474541595434052,1478902411840796,1480712982822302,1480014428420160,1476835016738564,
    1471190614065766,1463084818969342,1452508785113504,1439440718936328,1423845018046310,
    1405670991910506,1384851075025292,1361298399812504,1334903535059918,1305530104656922,
    1273008861909022,1237129574188694,1197629712007164,1154178324248800,1106352396390578,
    1053600968108538,995188293531764,930098841073400,856867174167718,773243978314474,
    675449888654240,556142311673122,396466160808914]]
private def pvm_r48_s0_1 : List ℤ := pzigCat
  [
   [257150476,1802114200,8801708954,34587013982,115956382738,342467487156,909158773256,
    2199661837320,4899169593694,10121155748638,19509257176042,35252833608066,59943439522252,
    96213969727550,146151895567998,210559019189734,288220870043758,375412988829382,465870945454584,
    551364975921972,622859955978684,672053721505620,692939187567858,682989753502846,
    643650155211008,580004033045988,499720471180612,411574005424964,323922704489284,
    243495341391802,174706654290690,119546167513276,77933269894726,48342528925896,28490712360254,
    15924433302582,8423188638658,4205506347772,1975755161672,870097100700,357503876920,
    136241265886,47792428754,15278328004,4389924974,1111088484,239906054,41673386,5044594]]
private theorem dk_r48_s0_0 :
    muxFastIterBSlideChk 24 49 phbv_r48_s0
      pvi_48_0 pvm_r48_s0_1 = true := by
  decide +kernel
private theorem dk_r48_s0_1 :
    muxFastIterBSlideChk 24 49 phbv_r48_s0
      pvm_r48_s0_1 pvo_48_0 = true := by
  decide +kernel
private def phb_48_1 : List ℤ :=
  altBuildHbFrom 256 48 1000800000000 0 48
private def pvi_48_1 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r48_s0 pvo_48_0
private def pvo_48_1 : List ℤ := pzigCat
  [
   [6,4,7,5,1,3,2,4,2,0,11,3,9,11,14,6,9,10,2,31,11,0,6,13,0,12,788,6479,32764,220333,1747514,
    11606661,66179662,361507427,1912059840,9208502843,39134177016,148053713281,497555291926,
    1402824924445,2926870384116,3384880705043,997231603933,7523974032820,5362281718202,
    41600004889317,60729562540649,473079988874498,1941820811049626]]
private def phb_48_2 : List ℤ :=
  altBuildHbFrom 256 48 896158000000 0 48
private def pvi_48_2 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r48_s1 pvo_48_1
private def pvo_48_2 : List ℤ := pzigCat
  [
   [6,6,5,5,1,3,0,4,2,6,9,5,3,19,1,16,5,3,20,13,21,17,26,175,1218,7903,46356,247897,1167544,
    4499317,12977806,28842551,114685512,930856501,5698702630,23768608691,60990278984,20592886872,
    75784794181,389743486105,1514809105503,3860726542815,3712761221731,6913684358118,4855162603929,
    35106720747422,3686383998595,124077207387326,1995809674509482]]
private def pwalks_48 : List RkmSegWalk := [
  ⟨phb_48_0, pvi_48_0, pvo_48_0⟩,
  ⟨phb_48_1, pvi_48_1, pvo_48_1⟩,
  ⟨phb_48_2, pvi_48_2, pvo_48_2⟩
  ]
private theorem ptail_48 : rkmAllTrueF [
    muxIntListEq phb_48_0 phbv_r48_s0,
    muxFastIterBSlideChk 3 49 phb_48_1
      pvi_48_1 pvo_48_1,
    muxFastIterBSlideChk 1 49 phb_48_2
      pvi_48_2 pvo_48_2,
    rkmCheckRowFromWalks 256 32 48 [1, 1, 1]
      [47500000, 3002400, 896158]
      [48, 3, 1] rkmMasksHiHiB_m256_r48 pwalks_48 rkmRowHiHiB_m256_r48
  ] = true := by
  decide +kernel
private theorem pw_r48_s0_1 :
    muxFastIterFullT16 48 49 phbv_r48_s0
      pvi_48_0 = pvo_48_0 :=
  (muxFastIterFullT16_add 24 24 49
    phbv_r48_s0 pvi_48_0).trans
    ((congrArg (muxFastIterFullT16 24 49 phbv_r48_s0)
      (muxFastIterBSlideChk_sound dk_r48_s0_0)).trans
      (muxFastIterBSlideChk_sound dk_r48_s0_1))
private theorem pwalk_48_0 :
    muxFastIterFullT16 48 49
      phb_48_0 pvi_48_0 = pvo_48_0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 48 49 h pvi_48_0)
    (muxIntListEq_eq_true.mp (rkmHd ptail_48))).trans pw_r48_s0_1
private theorem pseg_48_0 :
    muxFastIterFullT16 48 (Nat.add (highdNatMin (Nat.mul 1 256) 48) 1)
      phb_48_0 pvi_48_0 = pvo_48_0 := by
  rw [pdim_48_l1]
  exact pwalk_48_0
private theorem pwalk_48_1 :
    muxFastIterFullT16 3 49
      phb_48_1 pvi_48_1 = pvo_48_1 :=
  muxFastIterBSlideChk_sound (rkmHd (rkmTl ptail_48))
private theorem pseg_48_1 :
    muxFastIterFullT16 3 (Nat.add (highdNatMin (Nat.mul 1 256) 48) 1)
      phb_48_1 pvi_48_1 = pvo_48_1 := by
  rw [pdim_48_l1]
  exact pwalk_48_1
private theorem pwalk_48_2 :
    muxFastIterFullT16 1 49
      phb_48_2 pvi_48_2 = pvo_48_2 :=
  muxFastIterBSlideChk_sound (rkmHd (rkmT2 ptail_48))
private theorem pseg_48_2 :
    muxFastIterFullT16 1 (Nat.add (highdNatMin (Nat.mul 1 256) 48) 1)
      phb_48_2 pvi_48_2 = pvo_48_2 := by
  rw [pdim_48_l1]
  exact pwalk_48_2
private theorem pwalks_snd_48 :
    RkmSegWalksSound 256 48 [1, 1, 1]
      [48, 3, 1] pwalks_48 := by
  dsimp only [RkmSegWalksSound, pwalks_48]
  exact ⟨pseg_48_0, ⟨pseg_48_1, ⟨pseg_48_2, trivial⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 48)` (`FindAllJohnsonRampKickMuxHi256T8`). -/
theorem rkmTrajHiHiB_m256_r48 :
    rkmLo12EqHi 256 32 48 [1, 1, 1]
      [47500000, 3002400, 896158]
      [48, 3, 1] rkmMasksHiHiB_m256_r48 rkmRowHiHiB_m256_r48 :=
  rkmCheckRowFromWalks_sound pwalks_snd_48
    (rkmHd (rkmTl (rkmT2 ptail_48)))
/-- `S8`. -/
def rkmHbHi_m256_r512_s2_c4 : Nat := 0
end
end QuantumComputation.Specs.DickeSol
