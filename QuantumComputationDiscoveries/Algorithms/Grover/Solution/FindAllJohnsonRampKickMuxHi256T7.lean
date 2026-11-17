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
# High-`m` Coupled Walk & Trajectory Part `7` (`FindAllJohnsonRampKickMuxHi256T7`)

Certifies `(m = 256, r = 64)` coupled `T_16` walk (`4550` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi256T7`). -/
def rkmWordBitsHi256T7 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi256T7 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi256T7`). -/
def rkmUnpackMaskHi256T7 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi256T7 n w ++ rkmUnpackMaskHi256T7 ns ws
/-- Mask segment `0` for `(m = 256, r = 64)`. -/
def rkmMkHiHiB_m256_r64_s0 : List Bool := rkmUnpackMaskHi256T7 [4] [15]
/-- Mask segment `1` for `(m = 256, r = 64)`. -/
def rkmMkHiHiB_m256_r64_s1 : List Bool := rkmUnpackMaskHi256T7 [50, 12] [0, 3680]
/-- Mask segment `2` for `(m = 256, r = 64)`. -/
def rkmMkHiHiB_m256_r64_s2 : List Bool := rkmUnpackMaskHi256T7 [50, 13] [0, 4096]
/-- Prefix-kick masks for `(m = 256, r = 64)`. -/
def rkmMasksHiHiB_m256_r64 : List (List Bool) :=
  [rkmMkHiHiB_m256_r64_s0, rkmMkHiHiB_m256_r64_s1, rkmMkHiHiB_m256_r64_s2, []]
/-- Part `0` of `rkmRowHiHiB_m256_r64`. -/
def rkmRowHiHiB_m256_r64_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 56, 1581, 20554, 202520, 1450255,
   7255040, 23200493, 29207118, 2491582, 136689116, 29897668, 3132190964, 996637389592]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 64)`. -/
def rkmRowHiHiB_m256_r64 : List ℕ := rkmRowHiHiB_m256_r64_p0
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T7`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T7 : (0 : ℕ) = 0 := rfl
end
public section
private abbrev fN {α} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uCNe (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def u2N : List ℤ → Option (List ℕ)
  | [] => some [] | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs => match u2N xs with | some ns => some (uCN n ns) | none => none
private def uON : List ℕ → List ℤ | [] => [] | n :: ns => Int.ofNat n :: uON ns
private theorem u2NS : ∀ (hb : List ℤ) (ns : List ℕ), u2N hb = some ns → hb = uON ns
  | [], ns, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [u2N] at h; cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [u2N] at h; revert h; cases hxs : u2N xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [uCNe, uON, u2NS xs ms hxs]
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
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
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bE1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCNe, bDC, bE1S z x u hx, bES z xs ws hxs]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTD : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTd]; rw [bNg, ndiv, Nat.add_eq]
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
private theorem bME : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [bNg, Nat.mul_eq, Nat.add_eq]
    rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [bNg, Nat.mul_eq, Nat.add_eq]
    rw [Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bFA : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bONF, Nat.add_eq]; simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSE, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSE, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNSF, Nat.add_eq, Nat.add_eq]; simp [Int.negSucc_eq]; omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFA]; cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ :=
  match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d) | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSVE (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSND]; unfold bSV at hv ⊢
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNg]; omega
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
private def bAP : List ℕ → Bool | [] => true | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem bAP_cons {x : ℕ} {xs : List ℕ} (h : bAP (x :: xs) = true) :
    0 < x ∧ bAP xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAPu {x : ℕ} {xs : List ℕ} (h : bAP (uCN x xs) = true) :
    0 < x ∧ bAP xs = true := by rw [uCNe] at h; exact bAP_cons h
private def bHO (z : ℕ) : List ℕ → ℕ | [] => z | x :: _ => x
private def bTN : List ℕ → List ℕ | [] => [] | _ :: xs => xs
private theorem bHOe (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [bDN, bZ0] | c :: cs => by unfold bHO; rw [bDC]
private theorem bTNe (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | x :: xs => by unfold bTN; rw [bDC]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uCN (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
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
          dsimp only [bSl, uON] at h ⊢; rw [bDN]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b z bR [] [] hp.2; rw [bZ0 z, bDN] at hi
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
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTN vs) (bTN cs)
      have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
      dsimp only [mkHbZ] at hrec; rw [hz0] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uCNe, uCNe]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
private def bStg (z dg mL cL : ℕ) (hbz v c : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ z d nL 0 0 hbz v c) fun out => cond (bAP out) (some out) none
private theorem bSS (z dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bStg z dg mL cL (mkHbZ z b) v c = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uON b) (bDec z v) (bDec z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]; exact bSlS z _ _ 0 z b v c hp
private def bBd (z g m c : ℕ) (hbz v x : List ℕ) (k : ℕ → List ℕ → Option (List ℕ)) :
    Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bStg z g m c hbz v x with | none => none | some o => k n o
private theorem bBS {z g m c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBd z g m c (mkHbZ z b) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some out → bDec z out = kU (rkmNextLen m c) (bDec z m0)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen m c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uON b) (bDec z v) (bDec z x)) (kU nL)) := by
  unfold bBd at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z g m c (mkHbZ z b) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bSS z g m c b v x mid hs]; exact hk mid h
private def bSp (z m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  bBd z 16 m c hbz v v fun l x => bBd z 15 m l hbz v x fun l x => bBd z 14 m l hbz v x fun l x =>
  bBd z 13 m l hbz v x fun l x => bBd z 12 m l hbz v x fun l x => bBd z 11 m l hbz v x fun l x =>
  bBd z 10 m l hbz v x fun l x => bBd z 9 m l hbz v x fun l x => bBd z 8 m l hbz v x fun l x =>
  bBd z 7 m l hbz v x fun l x => bBd z 6 m l hbz v x fun l x => bBd z 5 m l hbz v x fun l x =>
  bBd z 4 m l hbz v x fun l x => bBd z 3 m l hbz v x fun l x => bBd z 2 m l hbz v x fun l x =>
  bStg z 1 m l hbz v x
private theorem bSpS (z mL cL : ℕ) (b v out : List ℕ) (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uON b) (bDec z v) := by
  unfold bSp at h; unfold rkmUltraHornerT16Step
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  exact bSS z 1 mL _ b v _ out h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, v => some v
  | k + 1, m, c, hbz, v => match bSp z m c hbz v with
    | none => none | some vN => fN (rkmNextLen16 m c) fun nL => bIt z k m nL hbz vN
private theorem bItS (z : ℕ) : ∀ (k m c : ℕ) (b v out : List ℕ),
    bIt z k m c (mkHbZ z b) v = some out →
      bDec z out = muxUltraIterFullT16Rkm k m c (uON b) (bDec z v)
  | 0, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, m, c, b, v, out, h => by
    unfold bIt at h; revert h; cases hs : bSp z m c (mkHbZ z b) v with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpS z m c b v vN hs]
      exact bItS z k m _ b vN out h
private def rkmZZ (w : ℕ) : ℤ := match Nat.ble (Nat.mod w 2) 0 with
  | true => Int.ofNat (Nat.div w 2) | false => Int.negSucc (Nat.div w 2)
private def rkmMapZZ : List ℕ → List ℤ | [] => [] | w :: ws => rkmZZ w :: rkmMapZZ ws
private def rkmNatZ : List ℕ → List ℤ | [] => [] | w :: ws => Int.ofNat w :: rkmNatZ ws
private def pzeros : ℕ → List ℤ | 0 => [] | k + 1 => Int.ofNat 0 :: pzeros k
private def pZZZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z | xs :: xss => rkmMapZZ xs ++ pZZZ z xss
private def pNZCat : List (List ℕ) → List ℤ | [] => [] | xs :: xss => rkmNatZ xs ++ pNZCat xss
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match u2N hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some b => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vn => fL (mkHbZ z b) fun hbz => match bIt z k mL cL hbz vn with
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only [fL]; cases hh : u2N hb with
  | none => rfl
  | some b => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vn =>
      dsimp only; rw [rkmb_forceList_eq]
      cases hi : bIt 100000000000000000 k mL cL (mkHbZ 100000000000000000 b) vn with
      | none => rfl
      | some out => dsimp only; rw [bItS _ k mL cL b vn out hi, ← u2NS hb b hh, bES _ v vn hv]
private def pChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem pCS {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : pChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold pChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; simp only [rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem pChFull (k1 k2 mL : ℕ) {hb v0 v1 v2 : List ℤ}
    (h1 : muxFastIterFullT16 k1 mL hb v0 = v1) (h2 : pChk k2 mL hb v1 v2 = true) :
    muxFastIterFullT16 (k1 + k2) mL hb v0 = v2 :=
  (muxFastIterFullT16_add k1 k2 mL hb v0).trans
    ((congrArg (muxFastIterFullT16 k2 mL hb) h1).trans (pCS h2))
private theorem bDm {a b : ℕ} (h : muxNatListEq [a] [b] = true) : a = b :=
  (List.cons.inj (muxNatListEq_eq_true.mp h)).1
private theorem rkmHd {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) : b = true :=
  (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def phbv_0 : List ℤ := pNZCat
  [
   [195252573090816,273427479426157,331558469787144,379002408584245,419418607417294,
    454700349417639,485981589690354,514006831459956,539296876345919,562233368746618,
    583106083266107,602141272736801,619519609191634,635388044527787,649867937713565,
    663060793184148,675052416754352,685915991546417,695714397583486,704501989543504,
    712325978414261,719227518266308,725242569807584,730402592328331,734735101758005,
    738264122760024,741010555758225,742992474655111,744225367189929,744722327003166,
    744494204252476,743549719872083,741895547144820,739536363059467,736474870875381,
    732711794344605,728245843089330,723073647641667,717189661560888,710586026778038,
    703252396788149,695175710396572,686339906264253,676725565256652,666309463249648,
    655064011093909,642956550151312,629948460065952,615994018452065,601038927139977,
    585018381859358,567854503868151,549452859265381,529697639559910,508444818276259,
    485512139345800,460663937467581,433587098507669,403850869563192,370834846143671,
    333587481872418,290509657252578,238491515712423,169533464716257]]
private def pvi_0 : List ℤ := [rkmP 1000000000000000]
private def pvo_0 : List ℤ := pZZZ 0
  [
   [43972,406708,2627356,13684680,60947378,239683878,849363314,2750280886,8220636242,22857802814,
    59483338118,145579877380,336420743188,736508964346,1531785639154,3033696974608,5733017368754,
    10356016502598,17908576436962,29686780354416,47228088671032,72179005643932,106066214746200,
    149979559552820,204204394742750,267870906676626,338708944220798,412998275273270,
    485779259477692,551338470389096,603917805837252,638531658573256,651734840379334,
    642179756690136,610839750010490,560848082475020,496988922360144,424953289173042,
    350518035367570,278808905855654,213772252153260,157918264833212,112331464033128,
    76890105865884,50606633778664,31998612749984,19418009346914,11296079920104,6291100723772,
    3349207934746,1701428963686,823114754258,378314929684,164734107198,67735031884,26194732806,
    9481419568,3192726446,992486254,281933788,72172682,16315306,3153942,491600,53498]]
private def pvm_0_1 : List ℤ := pZZZ 26
  [
   [192278303408102,425854702626582,660302598981566,827534847946524,889012198384040,
    845395474088834,726178763511688,571360232956818,415976430164296,282402846872748,
    179860502478724,107988121721272,61363996980396,33111669035620,17013084113746,8343401463832,
    3913253975800,1758423366322,758148070538,314050101852,125127869934,48001169186,17744718648,
    6326065570,2176352926,722936490,231981894,71939222,21566444,6251822,1752818,475358,124706,
    31644,7764,1838,418,90,16]]
private def pvm_0_2 : List ℤ := pZZZ 7
  [
   [105833916718,519719685074,1785701764462,4956281649708,11784935996532,24789958162370,
    47076354112948,81838980225992,131570295779964,197126774300882,276916437221714,366500658362702,
    458826168304026,545132135597496,616369037192812,664797400407192,685368969585742,
    676553857623092,640439709411874,582132270882442,508661657676528,427693981358074,
    346347002465232,270328651485996,203497616516462,147828360858202,103680188398326,
    70234165944222,45968436025328,29076657404020,17778278874776,10508863734644,6005884641308,
    3318655990496,1772943832678,915657702442,457097393388,220509359304,102769796708,46256464996,
    20098566934,8426114222,3406488148,1327124680,497858506,179681918,62325580,20753318,6625068,
    2024460,591124,164590,43584,10942,2594,572,114,18]]
private theorem pchk_0_0 : pChk 11 65
    phbv_0 pvi_0 pvm_0_1 = true := by
  decide +kernel
private theorem pchk_0_1 : pChk 11 65
    phbv_0 pvm_0_1 pvm_0_2 = true := by
  decide +kernel
private theorem pchk_0_2 : pChk 11 65
    phbv_0 pvm_0_2 pvo_0 = true := by
  decide +kernel
private theorem pwalkF_0 : muxFastIterFullT16 33 65
    phbv_0 pvi_0 = pvo_0 :=
  pChFull 22 11 65 (pChFull 11 11 65 (pCS pchk_0_0) pchk_0_1) pchk_0_2
private def phbv_1 : List ℤ := pNZCat
  [
   [195530604605952,273816828745253,332030595210394,379542092196250,420015842009651,
    455347823738107,486673607191434,514738755735672,540064812590062,563033965598676,
    583936401992509,602998696778568,620401779259221,636292810585016,650793322534368,
    664004964080531,676013663222224,686892707291397,696705065849722,705505170973937,
    713340300878310,720251668235067,726275284958698,731442655136158,735781333878441,
    739315380059082,742065723863249,744050464929928,745285113052260,745782780515531,
    745554332927564,744608503640832,742951975440643,740589431975614,737523580354430,
    733755145359728,729282834776254,724103274338137,718210909706750,711597871623574,
    704253798850652,696165611594736,687317225646099,677689194218162,667258260116620,
    655996794906344,643872093444675,630845480381931,616871168225580,601894781487621,
    585851423619146,568663104982021,550235257205337,530451906891498,509168822477333,
    486203488369183,461319903688539,434204508440010,404425936346571,371362899487637,
    334062496524196,290923330879967,238831117677257,169774873294465]]
private def pvi_1 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r64_s0 pvo_0
private def pvo_1 : List ℤ := pZZZ 0
  [
   [6,6,8,40,156,526,1636,4656,12092,29154,65358,136728,267748,491826,848668,1376480,2098038,
    3001616,4021160,5023112,5809762,6146986,5818238,4695938,2810806,392650,2142143,4266869,
    5473595,5421357,4055617,1654371,1222992,3874838,5643854,6092232,5110452,2928292,30426,2989229,
    5581215,7357113,8183589,8208757,7366929,4949237,4300501,16187919,8996277,129709018,100269718,
    1289487815,1526698759,11824918984,21551527468,97386154171,279257369711,643700721928,
    3252795627570,1804901048005,32242205624007,39970448937113,213643017973208,982899432537796,
    1727892887016346]]
private def pvm_1_1 : List ℤ := pZZZ 0
  [
   [9734738,6464320,2232093,7565901,5525779,1077702,6669964,7629872,3994390,1769455,6918313,
    9851355,10357809,9117897,7054277,4884549,2906783,796459,3126006,14530534,51394162,168223262,
    522420414,1546159768,4367443994,11785541442,30406122182,75051132502,177335260004,401324703824,
    870256753792,1808861761820,3604912644476,6889860242654,12630419019548,22210216537604,
    37464676925444,60618028397552,94067113138152,139972751132264,199663456594590,272927268093604,
    357350021587884,447922227771286,537143919579870,615777971831332,674235824162086,
    704364114019330,701211362834106,664275886736850,597825969721634,510134075606290,
    411799137208614,313620073866438,224613880426114,150691154219010,94249117080130,54626874748632,
    29117256942128,14129412329350,6156002974940,2359913135382,770875499050,202333325054,
    36961854094]]
private def pvm_1_2 : List ℤ := pZZZ 0
  [
   [61814,246830,677934,1473786,2676920,4167364,5617774,6540882,6443988,5045398,2458106,759907,
    3740215,5589037,5713407,4051443,1108745,2212750,4920266,6247078,5865418,3933670,986072,
    2271265,5174955,7260883,8329781,8426637,7764375,6629443,5300215,3995113,2852717,1936903,
    1255699,778123,414863,72394,931646,182893,20955107,126165063,413317647,427879007,4315875262,
    36380635108,181227676034,705764342198,2321884330572,6675323268936,17075034236272,
    39269495054694,81708317783018,154354867132390,265136654482674,414033922933066,586738891191804,
    751926030595682,866575102272902,890681150265822,806413980682400,631120773672768,
    413963010674910,214812006700286,76456161436906]]
private theorem pchk_1_0 : pChk 11 65
    phbv_1 pvi_1 pvm_1_1 = true := by
  decide +kernel
private theorem pchk_1_1 : pChk 11 65
    phbv_1 pvm_1_1 pvm_1_2 = true := by
  decide +kernel
private theorem pchk_1_2 : pChk 11 65
    phbv_1 pvm_1_2 pvo_1 = true := by
  decide +kernel
private theorem pwalkF_1 : muxFastIterFullT16 33 65
    phbv_1 pvi_1 = pvo_1 :=
  pChFull 22 11 65 (pChFull 11 11 65 (pCS pchk_1_0) pchk_1_1) pchk_1_2
private def phbv_2 : List ℤ := pNZCat
  [
   [158239232000000,221594797278121,268706100983417,307156259767324,339910902446099,
    368504409150669,393855775119400,416568370728440,437064271072550,455652773568608,
    472568721271806,487995477063732,502079463617760,514939775678623,526674766623372,
    537366699049691,547085112866956,555889318131239,563830274921645,570952034091681,
    577292857008823,582886096311730,587760895763870,591942751028875,595453961938580,
    598313998885758,600539800274673,602146013801927,603145191250704,603547944146283,
    603363065820228,602597624010046,601257026967897,599345065082308,596863929165301,
    593814205769798,590194849130357,586003128517223,581234548908861,575882741862709,
    569939322224227,563393704763331,556232872832321,548441088513447,539999530197822,
    530885838713770,521073546405923,510531354042922,499222206670286,487102099230709,
    474118512170643,460208329946274,445295020157906,429284727721294,412060728751539,
    393475316819628,373337500863874,351393522691502,327294285706996,300536993309272,
    270350480409563,235438766949563,193281520890875,137395604218347]]
private def pvi_2 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r64_s1 pvo_1
private def pvo_2 : List ℤ := pZZZ 0
  [
   [6,6,4,6,20,64,190,620,1784,4756,11874,27736,60772,125128,242574,443354,764568,1244126,1909236,
    2759416,3747116,4762028,5628092,6122032,6017500,5150980,3493990,1206894,1351851,3678757,
    5238769,5613745,4640825,2491197,345794,3177790,5292652,6152778,5537492,3590868,761052,2356337,
    5171263,7076029,7854571,9175851,10410439,7115366,2862870,41731913,633628793,3398130174,
    5921123507,1737763045,30307044646,157657774417,692568402830,2072970435531,6202245230768,
    10254901621641,16990400593802,26040710568556,67524834872727,498917706685672,1935305219539456]]
private def phbv_3 : List ℤ := pNZCat
  [
   [114560384000000,160427883450443,194535032322471,222371776089942,246085139682753,
    266785967578468,285139584337063,301582811732203,316421219276086,329878728877329,
    342125359754571,353293861048847,363490238315645,372800712522523,381296488518624,
    389037121918950,396072957499704,402446933934897,408195944769558,413351881479835,
    417942444130340,421991779015540,425520985332467,428548521164994,431090530912113,
    433161110545127,434772522952777,435935372621235,436658746659198,436950327487742,
    436816481211073,436262324655863,435291773231942,433907571065146,432111304236649,
    429903397392898,427283093431569,424248415387497,420796109002007,416921563716669,
    412618708935008,407879881272868,402695657073803,397054642564737,390943211474143,
    384345176442790,377241375694394,369609149538826,361421671317738,352647082710033,
    343247361158689,333176812932483,322380030905215,310789066854716,298319416243730,
    284864144116790,270284978762825,254398206979741,236951093465868,217579628797210,
    195725512939193,170450495805164,139929933768654,99470232383116]]
private def pvi_3 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r64_s2 pvo_2
private def pvo_3 : List ℤ := pZZZ 0
  [
   [6,6,4,4,4,22,36,120,382,1084,2910,7334,17412,38910,81960,162936,306128,543896,913888,1451556,
    2177088,3077546,4087788,5077656,5854220,6187154,5860206,4741370,2853638,419742,2144771,
    4304269,5533429,5472489,4057503,1575475,1384472,4078792,5812618,6131228,4940730,2546184,
    528837,3683123,7113251,2350163,26439347,59079538,329472051,1237449234,2872761063,1635156978,
    15134591974,79571076795,286747334874,900050067953,2408534674638,5387039978227,9633381520092,
    10808725395511,3156953291438,23382827396796,10935755529167,111931964027134,1996634561205042]]
private theorem pbatch_a : rkmAllTrueF [
    pChk 2 65 phbv_2 pvi_2 pvo_2, pChk 2 65 phbv_3 pvi_3 pvo_3
  ] = true := by decide +kernel
private abbrev pl_s : List ℕ := [1, 1, 1, 1]
private abbrev ptau_s : List ℕ := [25169277, 25205117, 1236244, 895003]
private abbrev pnsub_s : List ℕ := [33, 33, 2, 2]
private def pwalks : List RkmSegWalk := [
  ⟨phbv_0, pvi_0, pvo_0⟩, ⟨phbv_1, pvi_1, pvo_1⟩,
  ⟨phbv_2, pvi_2, pvo_2⟩, ⟨phbv_3, pvi_3, pvo_3⟩]
private theorem ptail : rkmAllTrueF [
    muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 256) 64) 1] [65],
    rkmCheckRowFromWalks 256 32 64 pl_s ptau_s pnsub_s
      rkmMasksHiHiB_m256_r64 pwalks rkmRowHiHiB_m256_r64
  ] = true := by decide +kernel
private theorem pwalk_0 : muxFastIterFullT16 33 65
    phbv_0 pvi_0 = pvo_0 := pwalkF_0
private theorem pseg_0 :
    muxFastIterFullT16 33 (Nat.add (highdNatMin (Nat.mul 1 256) 64) 1)
      phbv_0 pvi_0 = pvo_0 := by
  rw [bDm (rkmHd ptail)]; exact pwalk_0
private theorem pwalk_1 : muxFastIterFullT16 33 65
    phbv_1 pvi_1 = pvo_1 := pwalkF_1
private theorem pseg_1 :
    muxFastIterFullT16 33 (Nat.add (highdNatMin (Nat.mul 1 256) 64) 1)
      phbv_1 pvi_1 = pvo_1 := by
  rw [bDm (rkmHd ptail)]; exact pwalk_1
private theorem pwalk_2 : muxFastIterFullT16 2 65
    phbv_2 pvi_2 = pvo_2 := pCS (rkmHd pbatch_a)
private theorem pseg_2 :
    muxFastIterFullT16 2 (Nat.add (highdNatMin (Nat.mul 1 256) 64) 1)
      phbv_2 pvi_2 = pvo_2 := by
  rw [bDm (rkmHd ptail)]; exact pwalk_2
private theorem pwalk_3 : muxFastIterFullT16 2 65
    phbv_3 pvi_3 = pvo_3 := pCS (rkmHd (rkmTl pbatch_a))
private theorem pseg_3 :
    muxFastIterFullT16 2 (Nat.add (highdNatMin (Nat.mul 1 256) 64) 1)
      phbv_3 pvi_3 = pvo_3 := by
  rw [bDm (rkmHd ptail)]; exact pwalk_3
private theorem pwalks_snd :
    RkmSegWalksSound 256 64 pl_s pnsub_s pwalks := by
  dsimp only [RkmSegWalksSound, pwalks]
  exact ⟨pseg_0, ⟨pseg_1, ⟨pseg_2, ⟨pseg_3, trivial⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 64)` (`FindAllJohnsonRampKickMuxHi256T7`). -/
theorem rkmTrajHiHiB_m256_r64 :
    rkmLo12EqHi 256 32 64 [1, 1, 1, 1]
      [25169277, 25205117, 1236244, 895003]
      [33, 33, 2, 2] rkmMasksHiHiB_m256_r64 rkmRowHiHiB_m256_r64 :=
  rkmCheckRowFromWalks_sound pwalks_snd (rkmHd (rkmTl ptail))
end
end QuantumComputation.Specs.DickeSol
