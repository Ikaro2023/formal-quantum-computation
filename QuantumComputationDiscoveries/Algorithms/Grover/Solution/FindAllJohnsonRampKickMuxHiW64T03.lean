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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T02

/-
# Caustic `r = 1024` Halo-16 Walk `w_hi64_m4_r1024` (`FindAllJohnsonRampKickMuxHiW64T03`)

Certifies part `1` of `w_hi64_m4_r1024` (`r = 1024`, halo-16).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Kick-mask schedule for `w64_m4` `r = 1024`. -/
def rkmMasksHi_w64_m4_r1024 : List (List Bool) := [
  [], [], [], [], [], [], [], []]
/-- Certified `rowLo12` vector for `w64_m4` `r = 1024`. -/
def rkmRowHi_w64_m4_r1024 : List ℕ := List.replicate 917 0 ++ [
  501, 0, 2613, 0, 1352, 5893, 0, 33060, 0, 55440, 5024, 37842, 88400, 615, 231872, 0, 288622,
  133601, 144548, 582977, 0, 1009249, 133417, 838456, 1193813, 136979, 2686937, 94711, 2821431,
  2355279, 897070, 6465045, 75919, 7523450, 5131109, 2693279, 15283025, 254520, 17351552, 13325483,
  4921590, 36261634, 2400250, 34016578, 39921892, 3847075, 81994864, 20425870, 48175249, 120667788,
  315100, 150753768, 121899054, 24096833, 298040251, 82438923, 144424982, 463564361, 28901020,
  400528241, 636304910, 296159, 825265783, 847606315, 17256146, 1467289274, 1202519060, 61799221,
  2398169117, 1954045793, 57603788, 3625432743, 3676211745, 1778842, 4721291616, 7417744004,
  781474815, 4113612274, 13621018946, 6657777932, 561186183, 16490291266, 24679101963, 6772794552,
  3363879944, 34766150803, 53348408364, 26714476481, 69109323, 31019848315, 108855472775,
  171773836476, 178396536775, 137666727485, 83380622714, 40780293958, 16350626993, 5410610161,
  1477991858, 331033686, 59714861, 8298866, 772923, 22199, 0, 0, 0]

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
private def rkmPhb_w64_m4_p7b : List ℕ := uNatCatN
  [
   [684703885938067,684098017486175,683489407044686,682878054348131,682263959097024,
    681647120957699,681027539562145,680405214507829,679780145357528,679152331639150,
    678521772845555,677888468434374,677252417827817,676613620412492,675972075539205,
    675327782522771,674680740641808,674030949138542,673378407218594,672723114050777,
    672065068766879,671404270461449,670740718191575,670074410976663,669405347798210,
    668733527599570,668058949285721,667381611723031,666701513739006,666018654122054,
    665333031621228,664644644945977,663953492765881,663259573710397,662562886368585,
    661863429288843,661161200978627,660456199904177,659748424490227,659037873119722,
    658324544133523,657608435830109,656889546465276,656167874251831,655443417359277,
    654716173913500,653986141996446,653253319645796,652517704854632,651779295571101,
    651038089698076,650294085092806,649547279566563,648797670884285,648045256764213,
    647290034877521,646532002847941,645771158251383,645007498615546,644241021419528,
    643471724093426,642699604017932,641924658523920,641146884892032,640366280352248,
    639582842083462,638796567213041,638007452816381,637215495916459,636420693483371,
    635623042433869,634822539630891,634019181883077,633212965944286,632403888513098,
    631591946232314,630777135688447,629959453411200,629138895872942,628315459488176,
    627489140612990,626659935544514,625827840520353,624992851718020,624154965254363,
    623314177184970,622470483503581,621623880141477,620774362966870,619921927784270,
    619066570333862,618208286290850,617347071264810,616482920799020,615615830369785,
    614745795385752,613872811187210,612996873045380,612117976161699,611236115667083,
    610351286621184,609463484011636,608572702753286,607678937687413,606782183580932,
    605882435125593,604979686937157,604073933554564,603165169439086,602253388973470,
    601338586461057,600420756124895,599499892106840,598575988466628,597649039180947,
    596719038142484,595785979158961,594849855952152,593910662156882,592968391320016,
    592023036899422,591074592262923,590123050687227,589168405356844,588210649362977,
    587249775702401,586285777276316,585318646889190,584348377247571,583374960958883,
    582398390530206,581418658367025,580435756771964,579449677943497,578460413974635,
    577467956851587,576472298452405,575473430545595,574471344788714,573466032726930],
   [572457485791568,571445695298621,570430652447238,569412348318185,568390773872274,
    567365919948769,566337777263761,565306336408507,564271587847749,563233521917993,
    562192128825763,561147398645813,560099321319318,559047886652020,557993084312347,
    556934903829488,555873334591443,554808365843026,553739986683831,552668186066167,
    551592952792940,550514275515511,549432142731493,548346542782523,547257463851977,
    546164893962650,545068820974381,543969232581643,542866116311071,541759459518952,
    540649249388659,539535472928037,538418116966732,537297168153469,536172612953274,
    535044437644639,533912628316630,532777170865933,531638050993840,530495254203172,
    529348765795144,528198570866151,527044654304498,525887000787058,524725594775857,
    523560420514587,522391462025044,521218703103494,520042127316952,518861717999385,
    517677458247837,516489330918460,515297318622462,514101403721967,512901568325781,
    511697794285066,510490063188909,509278356359806,508062654849029,506842939431894,
    505619190602927,504391388570905,503159513253797,501923544273576,500683460950920,
    499439242299784,498190867021841,496938313500802,495681559796588,494420583639374,
    493155362423484,491885873201141,490612092676063,489333997196907,488051562750550,
    486764764955203,485473579053358,484177979904556,482877941977978,481573439344846,
    480264445670632,478950934207073,477632877783978,476310248800823,474983019218136,
    473651160548647,472314643848217,470973439706524,469627518237500,468276849069520,
    466921401335326,465561143661674,464196044158710,462826070409056,461451189456587,
    460071367794911,458686571355526,457296765495641,455901914985664,454501983996335,
    453096936085487,451686734184438,450271340583987,448850716920006,447424824158611,
    445993622580904,444557071767258,443115130581140,441667757152453,440214908860371,
    438756542315661,437292613342465,435823076959518,434347887360797,432866997895559,
    431380361047757,429887928414816,428389650685720,426885477618413,425375358016469,
    423859239705002,422337069505798,420808793211621,419274355559679,417733700204196,
    416186769688069,414633505413564,413073847612015,411507735312480,409935106309317,
    408355897128622,406770042993499,405177477788091,403578134020333,401971942783364,
    400358833715540,398738734958987,397111573116630,395477273207622,393835758621104],
   [392186951068229,390530770532346,388867135217285,387195961493633,385517163842914,
    383830654799572,382136344890648,380434142573045,378723954168246,377005683794384,
    375279233295501,373544502167882,371801387483291,370049783808964,368289583124188,
    366520674733274,364742945174756,362956278126586,361160554307133,359355651371734,
    357541443804577,355717802805629,353884596172349,352041688175877,350188939431393,
    348326206762293,346453343057831,344570197123831,342676613526059,340772432425803,
    338857489407186,336931615295700,334994635967412,333046372148238,331086639202663,
    329115246911214,327131999235937,325136694073099,323129122992237,321109070960631,
    319076316052195,317030629139692,314971773569091,312899504814797,310813570114339,
    308713708081033,306599648292949,304471110856402,302327805942009,300169433291179,
    297995681690693,295806228412829,293600738618227,291378864718413,289140245694621,
    286884506369176,284611256625358,282320090571214,280010585642329,277682301638012,
    275334779684776,272967541120285,270580086290195,268171893249429,265742416358454,
    263291084763999,260817300752381,258320437962133,255799839440973,253254815530230,
    250684641557618,248088555316734,245465754308667,242815392717722,240136578089251,
    237428367672939,234689764389461,231919712371979,229117092026442,226280714545649,
    223409315801435,220501549526607,217555979683049,214571071894068,211545183796850,
    208476554143929,205363290449569,202203354936410,198994548487585,195734492247132,
    192420606433374,189050085831419,185619871305676,182126616512928,178566648789340,
    174935922914693,171229966101675,167443812085146,163571921549954,159608085269044,
    155545305126766,151375646525401,147090053285455,142678112690199,138127753211274,
    133424849727646,128552699092793,123491309876607,118216418860044,112698093654932,
    106898686340767,100769726714550,94246994678557,87242268099132,79628509240106,71210701993145,
    61660496081362,50337533014494,35588271769886]]
private def rkmXsWin_w64_m4_s7b_out : List ℤ := pzigCat
  [
   [721390497,388215823,1343092592,1199052172,1331286499,1991950731,1101312314,2902458272,
    578450607,3718612627,520542397,4545288862,2138066266,4941711903,4256788933,4910213658,
    6956536908,3895087297,9935153447,1539115206,12947127930,2356612668,15149465465,8031582121,
    15711259354,15545924266,13842668825,23916230469,8316097858,32303421148,1541628922,39001676339,
    16404148835,41414186474,35674523262,36907553071,57757403435,22367879792,79091589184,
    4227384890,94402708633,43179613713,97278274954,92601745838,79393290731,145628203887,
    34070951366,190673839110,41413327800,211782250437,143281444867,191159463002,258406181066,
    112761746545,362241159115,32092359175,419669372388,236205724528,390972325175,470952844989,
    239656482684,681054916416,50914041554,788321601551,459181351311,706468448380,912046098418,
    367063774847,1280464630565,245076079193,1391874198530,1048434043476,1077792633359,
    1844460107431,243213706254,2326628383916,1047930707496,2148745798309,2502635965429,
    1057616498934,3595775962954,932908625572,3676823315727,3386784445903,2211677170192,
    5402690526612,868473806052,5803181588125,4847790575225,3599642765556,8136101948010,
    1326401012432,8648438580393,7618217173195,4754331697674,12360926430214,3415948661134,
    11982146235791,12954154376929,4240192525860,18427602748988,9356397553434,14199078168007,
    22287177783491,1440078123903,24873764789588,22398980558014,10135104931457,34845084177027,
    18476576193005,24352788721078,43378489231356,11069333556584,40343802932673,50767569444221,
    1405812559621,57772278665040,58544757894180,8625503379987,76927823732713,69672112714087,
    16039895822792,98259609380546,88726579887676,15496831598169,120740532577563,121580943017463,
    2984865540871,137740710736676,172570051211098,56227141652824,128592296124623,233735641699379,
    163507815067479,47696136685258,257146457573768,314509073256990,164911379392624,
    116315329584727,373231066749919],
   [462262887044397,327208674897237,16943803087527,352566449558462,660182454726224,
    829229545578154,845057683322094,742386742588516,577831460684640,404200025816770,
    256056539990604,147431099237694,77206718913002,36706061876762,15772477940610,6078950466830,
    2075722247064,615394702394,152662560740,29038842552,3043328762]]
private def rkmWalksHi_w64_m4_r1024 : List RkmWinSegWalk := [
  ⟨16, rkmHbWin_w64_m4_s0, 0, rkmXsWin_w64_m4_s0_in, 0, rkmXsWin_w64_m4_s0_out, 54221171⟩,
  ⟨32, rkmHbWin_w64_m4_s1, 0, rkmXsWin_w64_m4_s1_in, 0, rkmXsWin_w64_m4_s1_out, 311624573⟩,
  ⟨64, rkmHbWin_w64_m4_s2, 0, rkmXsWin_w64_m4_s2_in, 0, rkmXsWin_w64_m4_s2_out, 893769763⟩,
  ⟨128, rkmHbWin_w64_m4_s3, 0, rkmXsWin_w64_m4_s3_in, 18, rkmXsWin_w64_m4_s3_out, 3514053480⟩,
  ⟨256, rkmHbWin_w64_m4_s4, 18, rkmXsWin_w64_m4_s4_in, 89, rkmXsWin_w64_m4_s4_out, 10209690599⟩,
  ⟨512, rkmHbWin_w64_m4_s5, 89, rkmXsWin_w64_m4_s5_in, 252, rkmXsWin_w64_m4_s5_out, 22444009938⟩,
  ⟨1024, rkmHbWin_w64_m4_s6, 252, rkmXsWin_w64_m4_s6_in, 552, rkmXsWin_w64_m4_s6_out, 46621143699⟩,
  ⟨1024, rkmHbWin_w64_m4_p7a, 552, rkmXsWin_w64_m4_s7a_in, 864,
    rkmXsWin_w64_m4_s7b_out, 74141852558⟩
  ]
private abbrev rkmLs_m4 : List ℕ := [4, 8, 16, 32, 64, 128, 256, 448]
private abbrev rkmHs_m4 : List ℕ :=
  [2692575, 3792785, 5155440, 4542060, 5273504, 5943872, 7203425, 9103735]
private abbrev rkmNs_m4 : List ℕ := [2, 6, 15, 25, 55, 115, 243, 454]
private def rkmStL_w64_m4 : List Bool := [
  muxIntListEq (uHb rkmPhb_w64_m4_p7b) (altBuildHbFrom 1792 1024 20052279735 625 399),
  Nat.ble (Nat.add 552 (altIntLen rkmXsWin_w64_m4_s7a_in)) (Nat.add 1024 1),
  rkmCheckRowFromWinWalks 4 2048 1024 rkmLs_m4 rkmHs_m4 rkmNs_m4
    rkmMasksHi_w64_m4_r1024 rkmWalksHi_w64_m4_r1024 rkmRowHi_w64_m4_r1024
  ]
private theorem rkmStatOk_w64_m4 : bAllT rkmStL_w64_m4 = true := by decide +kernel
private theorem rkmHhb_w64_m4_p7b :
    uHb rkmPhb_w64_m4_p7b = rkmDropInts 625 rkmHbWin_w64_m4_p7a :=
  (muxIntListEq_eq_true.mp (bAllT_hd rkmStatOk_w64_m4)).trans (drHb 1792 1024 20052279735 625 1024)
private def rkmC_w64_m4_s7b_1 : List ℤ := pzigCat
  [
   [250124026,17309983,718131121,1386349911,1751871389,933734225,873457038,2870417308,3929924310,
    3058703036,144793217,4238561655,7382107967,7324788277,2750334343,4966337710,12793419912,
    16315151534,11998337802,377794871,16594939953,29570357003,31016369513,16630886137,11054091044,
    42519497402,62687046180,57858777692,22786529078,35029198125,95058921277,128813752361,
    112600128449,38444795533,77713481894,195671157418,263267876406,235509969010,95555574506,
    130145691005,371328711917,532407395729,523217008803,297622283015,117341733896,614277929378,
    1025189380802,1169265172620,917030402012,248608002670,712937029913,1709733529133,
    2405949892333,2481971379547,1741496061859,204038713963,1854386631224,3929307305880,
    5388793909344,5631961768776,4266997990832,1262981332184,2968123751621,7591964802585,
    11484150193203,13455723944355,12528691682049,8206001778701,669131631793,9143805029568,
    19609988850250,28644183876634,34038346331504,33862492135130,26857180848688,12746038898566,
    7590515006011,32113837576579,57802757290023,80985865058677,97776633235325,104551043512269,
    98399119178841,77487605036957,41288926514237,9346531664638,72276736538440,144293949649042,
    221450752950940,299442406182696,373998487479800,441237818861328,497953121857292,
    541807065501960,571426410220446,586401898877486,587206343349876,575051013213888,
    551703192309454,519288503259104,480098967328076,436420440255558,390392384660352,
    343905677357660,298537098641682,255519043214568,215740970224984,179771689630686,
    147898770750814,120176727412018,96479138023746,76548261121740,60040461221462,46566234005116,
    35720793651418,27107239769326,20354057014042,15125298355368,11125390933770,8101111673182,
    5840663347378,4169794777318,2948138192902,2064213428266,1431592850820,983410996404,
    668820677886,450391811304,300332809066,198038833018,128952085688,82904421024,52507699774,
    32511797148,19499047472,11255964764,6141845656,2919824598,916389368]]
private def rkmC_w64_m4_s7b_2 : List ℤ := pzigCat
  [
   [1063746614,1485309638,1120194916,177132125,2242623481,3645996681,3294689013,887951099,
    3138430774,6564415820,7112089432,3590908410,3336972711,10766126449,14060853849,10338258189,
    714816736,15335258782,25919134254,25581016474,11155748472,14218609083,39909869115,52374952789,
    40921209887,4219916501,46499929954,89224181320,100101644682,63907977092,15797030297,
    112582571121,184790928365,190701772871,107688429711,51388241858,235585698542,368541434274,
    375955094764,218298117326,82606734025,438396414895,714222329559,772383049573,528524979789,
    2739854358,689855314390,1306827145936,1597099749240,1362542305014,548556668316,703216021679,
    2060932817811,3075377879413,3306921837461,2472261601957,571113472149,2054547810044,
    4757209979508,6717098275034,7151625592924,5549838343272,1868812774680,3365595218909,
    9093005510391,13897960101065,16305203385747,15132110813501,9819773742789,666504479945,
    11102208160162,23453903457806,33849968212544,39682040903432,38764425385512,29793197487828,
    12687205843312,11254593292213,39411860270359,68111681805033,93064919991475,109905182597083,
    114747151847561,104682881086607,78148788437611,35121234668021,22880630054254,92969644543394,
    171208686173748,253024317562016,333656714127134,408591077743118,473924668283192,
    526637680102696,564751062989470,587369232250748,594621826946080,587525477118382,
    567790138731760,537599218464014,499389372005876,455647668754550,408742571187290,
    360796432316262,313602452750400,268580661095838,226771811989742,188858694251508,
    155206588908736,125916113477228,100880193133422,79840952840100,62441330963326,48268457547602,
    36889822175070,27880795394964,20842721518468,15414644367268,11280221068928,8169347531950,
    5856090102280,4155439935240,2919097908686,2030377040706,1398280679512,953505717242,
    643523735862,429872693894,284303167054,185834551692,119825435492,76263930934,47822999164,
    29239808890,17170946502,9563265098,4949828860,2211854098,657439740]]
private def rkmC_w64_m4_s7b_3 : List ℤ := pzigCat
  [
   [277207539,919948865,1375835309,921483889,636186756,2484186538,3433218670,2516570496,492420295,
    4477485541,6816679289,5697494187,669601895,6533934118,11957021332,11651978108,4225205950,
    8345656607,19861277389,23169383217,13915635403,6430676218,29695710882,43393431256,36799282484,
    7816689362,34634948147,71224028447,80154666363,48778946839,18173127290,96281042704,
    147850030946,139004215498,56793108082,78856460079,216081555475,288110837485,241878600907,
    66408577921,192352617038,437506400326,553003091026,451443000318,118308591618,363453905367,
    825819717757,1066835484591,926542474697,361062501647,512458245424,1426142704964,2031666491356,
    2015308227504,1222506619392,250647883137,2038461566895,3579320146445,4268521586111,
    3654794813061,1622321927947,1505863756780,4984419752762,7795311700228,8905785209462,
    7572115589952,3607016041092,2467486972481,9438390105809,15605999684683,19143890180363,
    18536683106085,12999952488355,2779382020539,10750589125930,25226904199686,37662477839888,
    44974474516460,44581075296542,34950138533370,15996505877878,10747058988557,42222855815639,
    74190594081261,101762180491383,120043653164871,124782938590295,112927168103785,83012785498395,
    35342686685001,28060526351364,103703099849454,187024775054048,272891840864550,356112879066392,
    431913388629528,496320816675020,546426129156554,580511730839780,598052921536950,
    599608900298026,586633943503050,561242055320320,525954643997832,483458952947160,
    436397546286534,387201821703474,337975952795118,290429381203180,245852652949678,
    205130176359036,168779372044666,137005162806636,109762609794230,86821540548130,67826488510014,
    52348090534250,39925428465040,30099072971820,22434337920138,16535751510862,12054971996898,
    8693832143320,6203392172902,4380154157794,3060809960232,2116883089800,1448906990684,
    981638445604,658157727834,436713670452,286673888686,185790004958,118801652478,75056633772,
    46661712836,28142619800,16174458196,8727253086,4324187052],
   [1833387354,518439422]]
private def rkmC_w64_m4_s7b_4 : List ℤ := pzigCat
  [
   [626263628,1203308708,1226037944,142142038,1801894275,3251161615,2901300029,371082631,
    3385490898,6360094584,5855613620,1341561812,5453013403,11000646741,11199531209,4129564143,
    7553424364,18111007422,20719432204,11061782068,8432681669,28784736719,38013990423,27323056195,
    2962630784,40813123398,66334356012,61592078400,20292370186,44935089627,104240356591,
    123349892309,80671691547,18545504662,136850548848,217239301926,207383994354,87414953134,
    112069336409,312330210429,414030134125,340952030045,81244110693,291112134168,630520616458,
    770470380646,594440395990,99172674200,578174720927,1187243183891,1447195174625,1158484913389,
    302087286529,912729097082,2083501837748,2732965470888,2477571219822,1191775464448,
    891300866265,3193739182699,4931210936457,5348329723761,3983814244909,881980120053,
    3326756936016,7521493984358,10354419867242,10624508116004,7663127605368,1620894935072,
    6437753903179,14680196714187,20875221713197,22914039780729,19364696187813,9922752973851,
    4356032536674,21110114682312,37023144570830,48411927016862,51938595301734,45308495022498,
    27816425049428,633778337062,33220103465307,69219173324949,101923809126233,125724116888039,
    135611987732235,127860692121027,100513107162093,53619807187377,10789932401332,88981131537304,
    175974276443076,266114429490920,353667895441678,433369460654122,500863202988242,
    552996794950986,587958738044274,605267849316002,605637948510682,590754056406018,
    562997771598008,525159495725180,480169045504306,430865028251436,379817610114862,
    329210615052290,280778830191502,235793457896148,195086413775574,159101060230632,
    127958325458468,101529455735434,79507142765866,61469260265568,46933097527028,35398936297326,
    26381854910814,19432575857754,14149961594758,10187231016538,7252852176124,5107320480218,
    3557735500396,2451750097214,1671456514786,1127283639414,752180192284,496550136162,
    324191984224,209129382206,133070758748,83332043606,51192988302,30687206704,17768467222,
    9743667692],
   [4867002582,2033974346,556041482]]
private def rkmC_w64_m4_s7b_5 : List ℤ := pzigCat
  [
   [405048939,1202123189,1203831287,144314140,2069017284,3459256186,2859782140,171599755,
    4125604705,6363245875,4980511111,348374444,7318310074,11379026940,8994305984,93303277,
    11978216447,19531120339,16493597379,1759091103,18377908546,32889548800,30805608512,8407709350,
    26008690025,54338170173,57905344703,27159997917,29159954654,84322415960,105793045394,
    71712687348,13737359035,115792630661,181113402277,163283143281,49779326009,123287082730,
    278170844988,327129749782,216288943950,38743349027,344402166381,558338184215,548979972499,
    263133873335,230013675976,745283240642,1042844309312,927486251256,348992148942,544068904331,
    1428536351323,1910468758637,1680498471481,663608734399,901694820184,2497886474792,
    3480607526826,3309243330184,1777897356308,840656771691,3806405804039,6095379765675,
    6715738361827,5062906363835,1199151618955,4049495952936,9233120648164,12637690283928,
    12780137348170,8901734786054,1312169353160,8532854421369,18267631184291,25130092654667,
    26642856080993,21295872149185,9057000360939,8424654508708,27991245784696,45506496478548,
    56642916681044,57766896990806,46739724435838,23472591854880,9874356307251,49089351678129,
    88464483742095,121604561243931,142346913097825,145638706041795,128233646512063,89111330866163,
    29576365825685,46952770840094,135408952511988,229707416299110,323441848382220,410549128186234,
    485863251875018,545506016432344,587092592710962,609756738906256,614021362060622,
    601555303991532,574863857368580,536957968889926,491039505615440,440230932981306,
    387367317063876,334857074202906,284608217728712,238011096843988,195965836037058,
    158941174426754,127051171688692,100137972904116,77851955086736,59723645572356,45224037986192,
    33811660456482,24966405339016,18211545017472,13126119838712,9349944860392,6583203256972,
    4582326808400,3153670947802,2146253371270,1444477554712,961381363470,632655177468,
    411511528220,264419647084,167678147958,104753986618,64273000344,38527024396,22371961848],
   [12419330302,6453260932,3024460452,1181569600,304133704]]
private def rkmC_w64_m4_s7b_6 : List ℤ := pzigCat
  [
   [895097978,1318989612,582518260,1161718715,3109923789,3589113525,1332962675,2761155954,
    6112267734,6206751604,1786044518,5381325075,10731263059,10044417689,2066285499,9860223270,
    18526250854,16916974492,3106264488,16871080287,31177886759,28760810105,6306322687,26953811580,
    51949337214,50220151576,15659632886,39119888743,84713810927,89933918311,40685885935,
    47381092820,131387589360,159445071660,99880797452,35124528879,186754919391,271759141299,
    224129632887,36127454513,223381899356,429135944626,455184429904,241683533988,158369051045,
    581256095227,812694399443,686215094881,177463488599,553689207444,1201566555310,1430533827662,
    1029335693294,35981696934,1229324986357,2251554511231,2511635592947,1714687424101,38131973956,
    2215718189526,3996302999716,4549423156774,3369168991084,535342880308,3210295064451,
    6627853070397,8353129995013,7373797930203,3452798942577,2657153750100,9307206275514,
    14356991087472,15793437137402,12391244332874,4213582874136,7214643398387,19141459718587,
    28198615896249,31249440232129,26261893341049,12979133164903,6795655683628,29392314476054,
    49921807461586,63247441709890,65072696336626,52914371097186,26756369605690,10749895691017,
    54575144496423,98029872859163,133769883532841,154904202371961,156012470004461,133909105285163,
    88049792601283,20545555400393,64184266662780,160036028742168,260005693194388,357006502162626,
    444607717679062,517610478861398,572412354057022,607148199180480,621626818904334,
    617106388787746,595963902550764,561315498230768,516638277450700,465433286864922,
    410955959932392,356026471251532,302920204628476,253329516951910,208382674339438,
    168703680504796,134496847598914,105641732450600,81786983999906,62435132378248,47013725658918,
    34930984248140,25616127002188,18545830696572,13259046621410,9362801844924,6531458550132,
    4501981375082,3066428074452,2064287263514,1373326965276,903049303202,586774310146,
    376508542700,238522514846,148972745380,91393952490,54903342208,32242049664],
   [18407113574,10053800644,5105433268,2307889586,858172800,209295452]]
private def rkmC_w64_m4_s7b_7 : List ℤ := pzigCat
  [
   [203865025,136188055,270419734,670303108,383387836,777136171,1650401557,1019213207,995665794,
    3118833552,3705344916,1274609486,3204105625,6647370075,6293157023,1101102223,6581361672,
    11622870148,9375973434,545234051,12875440187,19377385449,13558570029,3967487618,23664209792,
    32042091102,20081043960,9437235053,40751984971,52604279569,31347483539,17305959722,
    67609499530,86620264274,53344570444,24538241147,107823442807,144062085099,98056445563,
    22591584542,161831338880,237917016204,187742611474,9689255162,221433181491,381563223057,
    358672705983,120098179597,250508883520,574709374780,658950120432,397865987122,149732105539,
    756627823607,1112054869317,968103515457,281085494439,724623875868,1614317760630,1915796197870,
    1343378992712,27219418699,1724119800541,3022668447139,3229947922219,2004501935123,
    425583151502,3256687544840,5349440862076,5648962692628,3637120099720,362461136213,
    5167314103823,9051155287881,10313326076459,7920658492611,1994580803619,6048479473232,
    13790223329508,18483434579556,17919320081138,11224924910420,669647806263,15066806619091,
    28069629889235,35557349911991,34319513192837,23044849684995,2891054921295,22532907804154,
    47792371890020,66730452379836,73803702438300,65350456022348,40512311929656,1613665992254,
    46072764606753,95116519899285,137109616487047,164003525814575,169356476178833,149281357589919,
    102958045389573,32662903569347,56644483966154,158070839676456,263725591126370,365689304023106,
    456872908193898,531670638134988,586349702845978,619171938538266,630276865246126,
    621383210143216,595380399079430,555877446367678,506770216892316,451870925731972,
    394624523852054,337922894567560,284012439879170,234479991484932,190299401659148,
    151917523763330,119360732304992,92345015623282,70381433124874,52865001576980,39147206905546,
    28588843994664,20595867108308,14641030746976,10272542847340,7115076919348,4865819055126,
    3286196686562,2191959518596,1444115159010,939562625782,603744708752],
   [382738389498,239211591878,147344162996,89202446276,52922889946,30713534866,17299066922,
    9259846354,4536954148,2032777074,533777162]]
private def rkmC_w64_m4_s7b_8 : List ℤ := pzigCat
  [
   [217389769,256733744,475669888,146169885,950148747,1045214541,50842211,1419450500,2063862324,
    894396614,1760204895,3799228331,3072952841,579079580,5249253288,7424233250,4114465074,
    3616327607,10695500941,11584205669,3817869303,9256871874,18886543550,16489524980,682715864,
    20027155221,31378242313,22326923441,6081615512,37972896500,50580391664,29731878446,
    18153778453,66139574591,80180417425,41186502801,37285404982,110884813458,128019068756,
    62494757026,62968272673,179679375923,207907229145,107013263437,89763097738,280079151074,
    341315423344,202913146510,97942500381,415450990829,560086679667,402821642559,35277369498,
    563331780690,895309383888,793723585216,214090175906,630233809659,1333007430503,1477114785061,
    856032865585,374990948752,1708336978634,2476448327524,2159872405444,675085257464,
    1502304429857,3463202790193,4217909002817,3145808910179,348627133701,3267139108786,
    6252695371918,7156219298738,5145454655354,463013475246,5494945800077,10555807693795,
    12506963075609,9948120930061,2948082122883,6756371119838,16141952436284,21780624136664,
    20965989423516,12722925155792,1639045725173,18642084869537,33439646570325,41102581954901,
    38045128266613,23189008974191,1468760108306,31060597051618,58800135385426,77460937233160,
    81033417113266,66174128319140,33116881546768,14145697863811,68435763468243,120578401934817,
    160948477582561,181061684572365,174918773263353,139879238083315,76954028405391,9475503805710,
    112410058828572,223283562170394,333117475938922,433595014582034,517913357911264,
    581330160243318,621382084732540,637801960961462,632204889754378,607623303662494,
    567980776205316,517579172668686,460656578441690,401049290934860,341969543597070,
    285896552786678,234562180752344,189006001430892,149678386274472,116565307912030,
    89317883953336,67370640876916,50043851346778,36622293070912,26411925872934,18777971276132,
    13164765656354,9103360283638,6210138560574,4180436567254,2777086221186,1820725839422],
   [1178140284218,752145732254,473639382732,294078072768,179855792330,108108339624,63941668440,
    36881482968,20644736840,11101140414,5513456610,2375435050,814193620]]
private def rkmC_w64_m4_s7b_9 : List ℤ := pzigCat
  [
   [375786098,61662004,574129283,724550657,122937795,893364210,1460379742,651311162,1321004473,
    2678289123,1775940107,1058814690,3823123022,4093686448,558844990,4925904963,7785235043,
    4715062155,3302551694,11217122244,12377748022,3506655012,10836187367,20186993043,15770975281,
    2477481738,23790700658,31865669572,16632137310,15876827157,44685036089,46621542057,
    13173072411,39448214960,76283230214,65430764828,2724403748,78597391049,123487720845,
    90040250415,17308794394,140316973094,195651260494,127495755690,47251658335,234160044545,
    308543908893,192756071135,81743169150,371254199530,489103798582,317812744230,101019514285,
    559272207545,778280640775,565744467023,47956777034,782661136350,1224644918000,1044851954288,
    207427845054,951932236665,1843268194545,1903996233815,915352848809,811911230646,2505127407656,
    3253597731408,2458403214918,197925447486,2689079250877,4886099149493,5160453103207,
    2974059265805,1142779706184,5656818384616,8566125622812,8222090066986,4114910849244,
    2723773013503,9915220296553,14513407124093,14117105339531,7905086281119,2812784625604,
    14788317306832,23768774099778,25897853449222,19127712955842,4156010486932,15463409861929,
    34124719697013,45694603582873,45323667228111,31018877054279,4507991539201,28872802368008,
    61263541043998,84073193131458,90032219102684,75001170268302,39108889522072,13031256726339,
    73048137234039,130297644571679,173760356849137,193953636733363,184490587447991,
    143025052243959,71467565395501,24491415232504,136390599439778,254313975225074,368262219822228,
    469362565711942,550761937181066,608129019893578,639759684397698,646348148385426,
    630519005459440,596227804391320,548137878060930,491053116516272,429462917327584,
    367225174083988,307390708344558,252148997313780,202872202185748,160222869708820,
    124295999054522,94771683113634,71058979993826,52417796587578,38057541801144,27206143119464,
    19155893164708,13288653892000,9084889579522,6122234522206,4067759753888],
   [2664850748216,1721480687072,1096587075962,688555949886,426217237046,259765317854,155894153802,
    91877050718,52992642548,29853042232,16236419916,8217209072,3847189760,1408483146,309972512]]
private def rkmC_w64_m4_s7b_10 : List ℤ := pzigCat
  [
   [212127340,138743530,386165565,464776097,73679560,812402880,1106113192,210057590,1417506509,
    1995573881,601124151,1763282060,3157462142,1940332700,1720956443,4998124653,4444836533,
    540460472,6585796980,8445180814,3083365768,6920297749,13846377353,10548798429,3043966960,
    17820197836,21432715018,7783091838,15947714203,32624289749,26296983581,3664185542,38607747808,
    50809188140,24547540290,28609814465,72788478735,70232462351,11129787343,72235330130,
    120519789270,87640945820,21067670279,141564767925,185566620709,101213745069,79972355282,
    247828769360,276325229002,111880553872,173850753333,406773179479,410648684651,128881688165,
    310778853940,644909583534,623607073434,179566711064,490363035537,999829699017,982755167745,
    331638634497,683936271338,1511124435118,1598097289136,728855827248,783029542871,2179931871037,
    2617543716723,1636338072415,507370914054,2854888881488,4147528624844,3457301444548,
    741232931710,2981634122187,5976211076867,6555515363189,3934645667909,1232391686514,
    6936406066216,10550552395262,9959753392858,4608728781764,4009497161285,12702717121209,
    17705469189543,16183510376855,7535005007503,6057754162582,20109218178532,29249658102350,
    29120685620170,18091571490582,1830523639707,25265593078215,44881213809201,53560577528249,
    46663227295953,23684987596799,11205755187890,49934907454684,82402999733902,98979270880246,
    92956902470146,62347599003756,10593749487534,53941733035665,119542566448333,173367605880125,
    203831302445925,202640361496573,166111523686673,95592568036539,3000814501882,120343832923904,
    245268940301986,366423457975742,473735718331956,559489535402470,618913676793660,
    650283704856088,654618780378780,635097215333366,596328895669274,543617255934004,
    482303979736080,417264068943040,352572813455560,291341267536138,235693831501100,
    186850582573872,145274969466908,110851777005108,83064485758676,61156750659452,44262864386274,
    31505279259402,22062062756550,15204499215698],
   [10315590109382,6891568175792,4534452768288,2939035522516,1876485140922,1180292176380,
    731209090804,446052838020,267886618654,158084149330,91647998982,51899620500,28605009676,
    15070870850,7565978078,3284109382,1081001296,217798012]]
private def rkmC_w64_m4_s7b_11 : List ℤ := pzigCat
  [
   [474593955,343509083,251814032,864576670,611045264,493763955,1507507403,1131063309,721730698,
    2396381434,2117019896,509682645,3363604331,3696750667,318428975,4578245958,6373671352,
    2243314216,5432372307,10070846829,6285985879,4496229038,14358616592,13503157642,189219945,
    17669775913,23863361155,10265125459,16086895332,35181729330,28176868782,5528460321,
    43109101065,52540793867,18910449239,39692436804,79451789416,61967545318,12374867179,
    95466567759,120376313787,52208274843,75530776590,174137639188,157271218422,10564540352,
    180860371345,277552532221,181781049971,77703444522,340891125284,409812145120,187704761238,
    227453424415,574711327063,585243537385,175372753389,456872744350,914617344460,838881444564,
    163703261146,781482063551,1415898648759,1246920172055,211478057933,1200295792454,
    2157035656218,1950705206014,464295684782,1647834407483,3219662218397,3185049804655,
    1230991030603,1886405446636,4593422963798,5255592562260,3083895516516,1285417251259,
    5901483002143,8327820511225,6846050559039,1460056967999,5834608981762,11740805606112,
    13076893724568,8323250650926,1416536996951,12546331656309,20251416836671,20458948697669,
    11702829506613,3911173377638,21112249837842,33187664863020,34442047766978,22496083953214,
    447276369147,27888466457659,50853291263293,60691643617685,51957009834139,24438428391429,
    16320011820610,60191326638114,95007607122892,109749318527774,97505724298916,57428586406858,
    4791828974527,77988669000733,147791434537255,199520847676193,221021791312919,204840997047301,
    149362907301907,58789489105505,57894671276274,188653890780696,320416553989552,440985524571426,
    540538774249136,612546110980352,654068061709066,665509364819636,649980363762478,
    612441589071000,558804592747534,495123246972650,426959835185830,358967659444336,
    294681491470104,236488200755076,185725896882108,142864662192596,107720067788068,
    79666628087610,57825188659738,41213503122410,28856574002038,19856433528600],
   [13432770044768,8936443016772,5848069198494,3765050857382,2385244800788,1486898066962,
    912120530638,550374511178,326637100660,190441911592,108810764018,60944154998,33126944696,
    17307650984,8404989912,3707706082,1228637078,239116498]]
private def rkmC_w64_m4_s7b_12 : List ℤ := pzigCat
  [
   [245385917,128140405,489596610,495468492,360341729,1279454127,1164973137,166742632,1822394512,
    1887964776,234303027,2902315427,3066250319,83530080,4067142434,4937035810,857599384,
    5508164249,7763962277,2584486995,6802170068,11919127900,6429623936,6947229995,17414428753,
    13636473385,4754341642,23429467050,24639305076,2581976384,27651387669,39959073941,18117520357,
    26180054684,57476675766,43766698068,13490705995,72633283579,81055195385,18750687815,
    75955662286,127242903450,79294411648,49729239819,167457548951,170241567791,28774007755,
    171369320190,276369463324,176623338238,92870557257,350933119091,385555872995,118329983911,
    306391881518,588918328068,476868618938,31088556067,633483680143,893332019531,539611487999,
    297814699376,1106967368728,1291467202254,583539599988,702254891763,1780663697187,
    1855185891645,662489191031,1249076262772,2740406803938,2731812035516,920147590008,
    1887812948789,4095716488831,4186596786671,1677506958383,2408760774716,5908451823530,
    6615946270380,3566513766010,2205856465363,7938042537753,10407223546759,7627439845607,
    109121716687,9036704309134,15331235184456,15013415314758,7023986584054,6097815686609,
    18938764549795,25369548443689,21267687107949,6626222657749,13927029866542,32547008504584,
    41063333102056,34264208784436,12284763983758,18875488594713,48988826413505,66885741445261,
    64277745741253,38817388811069,4644261018926,55034110677100,97974233372970,119756480726362,
    111200489688876,70320858260346,3115984148160,77641858120863,155205269030903,212455972378839,
    235413593879161,215867508793675,152650581408733,51443405548413,76669443055104,217433970762608,
    355916911135334,478749884103698,575777495327468,640933963075282,672355970987534,
    671869952207254,644075227583478,595251816247068,532301337398758,461863848320792,
    389690141843506,320286758793954,256803162960384,201107533240154,153980395158334,
    115369413389320,84650745159210,60865447793720,42909839820898],
   [29676249595122,20142531043358,13422624999972,8784388865210,5647619126032,3567581363256,
    2214674046040,1350985618400,809909593264,476946742842,275831039980,156361156964,86749415224,
    46857727550,24345161422,12155028290,5442770782,2039607974,405910426]]
private def rkmC_w64_m4_s7b_13 : List ℤ := pzigCat
  [
   [273239114,254645835,1206315145,990595147,385793974,1722502250,1450810978,787471435,3001088153,
    2494618995,1116063738,4177615538,3277156516,1677468247,6157988331,5226562709,1789668548,
    8879502222,8250274404,1573781749,12377783077,12869510403,15362202,16538744918,20392257256,
    4241842062,20808247331,31135728153,12645823137,23331694642,45213715222,27972100586,
    21227652489,62075805047,52618476165,10212621742,78494957546,88331371544,16317119536,
    88627397401,135818149801,67780705531,79697450076,189857633092,152810652010,31692699793,
    231382847889,272008809925,81266751227,225822536202,407744335728,279543407156,118350755121,
    507953553515,558698449359,154056577775,471089005742,851595898436,625378327824,156169864973,
    989137796099,1226308385993,555569602485,695385382602,1689802573208,1619843551008,316991822662,
    1507123443925,2621371985855,2072077891747,85246520910,2647775786096,3903033236776,
    2721942068288,573908893551,4182304325285,5765631692045,3890343569193,902888713776,
    6121695790772,8569815247242,6204690362200,444503437161,8196684396523,12685621550447,
    10702018953837,2184505461033,9292654598244,17956092029498,18624395107060,9514223569420,
    6384290786081,22189277989229,30026179783489,24706470150187,6504853040663,18318297850704,
    39637059258350,47462296236926,36212682479502,7488042892146,29858406431127,62485031699485,
    77203415137213,65818264146459,28425963677069,26002650665956,81960453948968,121892448736422,
    131392374928634,103514081792872,40970514678568,44307592672267,133982625908637,207600893077727,
    247163172731841,240847513968761,185101463931135,84825912023183,48144002984006,197698707733782,
    346544005422338,479040421043990,583303430744680,652319058227314,684079440396944,
    680923784279118,648379312050318,593806988547018,525117974535632,449737908832986,
    373909096911146,302334391503138,238114856953018,182899781700920,137160790115446,
    100515242118756,72036869165974,50523249218510,34697020514510],
   [23344053227624,15393189910992,9952040760806,6310349057918,3925005471638,2395459033862,
    1434386787206,842753989100,485640942470,274233679598,151666072696,81760616598,42911345090,
    21577757400,10141416486,4268222656,1278419544,217053062]]
private def rkmC_w64_m4_s7b_14 : List ℤ := pzigCat
  [
   [750995723,261870693,1224080022,1991199732,525359460,1972524153,2937843209,821081685,
    2798081244,4021900518,517509574,4653651877,5787195397,458202381,6555875662,7861282592,
    323953714,9885522505,11707747157,670854781,13943978892,16869183234,1758923820,19375611735,
    24682137565,4633239411,25708950374,36554397590,10869657156,32999280441,52671835353,
    22303488687,38967052596,74824064528,42402773208,41276119091,103242556377,75373493345,
    35100359112,136712580666,126357652444,11630824389,170750545551,200904736303,43630560709,
    192583285388,300076857064,148312086534,178176818727,413263215533,319350791599,89456432486,
    509699327864,563834869858,124281841812,524972160293,856229941755,512060886137,352609782124,
    1105470986254,1082301342110,140875307074,1124117001399,1733582136573,1053901646269,
    628276470646,2167653725490,2313486548590,670351592286,1844205568043,3472337460441,
    2802140679243,116504129164,3559847653744,5108107088974,3273661715934,1284539823799,
    5875402879945,7312213631943,4012910332563,2681760093154,8943956855078,10581662030816,
    5682875686716,3831486077745,12842449601621,15708323809701,9591066317061,3469849935006,
    17072281888962,23512344688902,17922520535612,1307019639398,19251015769555,33557399823181,
    33166666786219,15828291255619,12702058816112,40525133175956,54481648559128,45986591283580,
    15268301023390,27894020637165,67366612181649,86605731100993,75057166903741,32566078770637,
    29854628514888,93163392578832,136212694230672,142420005226114,105021343300478,29339428784158,
    68450173926867,165475372212943,237875887478783,266407122302855,240523283398225,
    160106197749817,34737969679771,118972466119584,281114363588492,432284829944120,
    556683718301382,644016883536306,690088368250420,696258932391732,668133598685406,
    613893876788072,542655293220430,463111908254512,382608118066618,306659979329956,
    238859779477786,181061887302094,133727405708800,96328287785952,67732008317382,46521154025748,
    31231470149364],
   [20504215178980,13170330769058,8279680325644,5095841847298,3071178357696,1812718975924,
    1047632055582,592938008536,328297898628,177611844852,93712618942,47872182180,23396499606,
    10742397338,4355891134,1221460860]]
private def rkmC_w64_m4_s7b_15 : List ℤ := pzigCat
  [
   [746489813,882870517,116667926,1544847286,1087936464,1283918931,2803839927,1237257513,
    2442504378,4407111008,1356691200,3668279103,5572828663,1061986959,6211037202,7396296088,
    313378161,9676732237,9890968173,1649835906,14103111932,13042106166,4062983395,21095950437,
    17782218119,6973214274,30004046164,24073197372,10938085149,42365437295,33784453543,
    15011840530,59013224830,48335867648,18656108511,81190343787,69736275413,20285429364,
    109687626254,101971838288,16396315957,145148002041,150249707439,1416926786,186809695808,
    220897633970,34941557940,229510181419,321003893171,109101119099,260194508086,453917419380,
    242309247396,254414450831,613995298407,459461581493,169947140338,776317387982,782355562092,
    56969465454,879171683435,1208513507463,505564680789,806220743062,1675695737682,1241198127780,
    378790191771,2011332105727,2250398010213,614696122751,1884156496922,3324780833764,
    2307524272376,813560383011,3917938625823,4516390520431,1655073907033,3086502010954,
    6400530489138,5489081701382,248402777276,6229680826409,9420656365793,6411545947493,
    1783229357558,10341791617340,13400512641226,7887746589994,4018953390829,15582790792277,
    19230711412083,11255595075663,5348488450630,21836144354364,28225525396142,19027779933772,
    3024910857941,27528619327523,41258847443187,34997133492489,8848148314049,26808710036632,
    55459765398372,61918068176528,39674976985998,5293881861631,56117015758771,91456851687777,
    94128699880199,58369821134029,7160611830764,81791036196676,139686338752722,158561924299216,
    127180903730670,49185333069502,57762222696595,166932076254277,249775541920671,283177072816987,
    254722912129367,164837647635151,25671158872783,142501749461338,316116132800742,
    473062518793384,596322294709964,675946610302592,709335566916006,700157874544322,
    656452145039462,588476424107030,506765455100646,420676507814008,337532462408822,
    262317016005078,197797039333484,144910888704588,103269317604560,71655369997128],
   [48449124436582,31943222850672,20548289776728,12902724764276,7911746154488,4738626083154,
    2772842055204,1585441521244,885522665800,482946216044,257036569074,133187405924,66822497432,
    32171063378,14608912824,5987516718,1951128308,309481960]]
private def rkmC_w64_m4_s7b_16 : List ℤ := pzigCat
  [
   [543675330,444586618,626952307,1019532153,110423998,1590342274,1210877926,953572203,2885226745,
    1566310441,2337094738,4020618318,661003588,4771962041,5418874089,488752704,7214223348,
    6366285650,2859363641,10469055761,6536083003,7222435650,15259437676,6008080828,13356166885,
    20822285677,4297941717,21630032008,27350227902,762128436,33641815207,35904443315,4801889806,
    49500866056,45727767978,13645142049,71089850415,58744344181,25382142702,99624916546,
    75919023770,40969443469,137840318151,99731157597,60180022662,188676401858,134933780988,
    81493539639,256518750195,188389194899,101360749858,346034629460,271115590908,111645677541,
    460419396699,398248939787,96441153602,598556214542,589081535958,29038761459,751032449837,
    866216696441,133869313169,888866549656,1248043313444,456108266536,948011062137,1730458204885,
    1017648885191,811299821932,2256049771088,1893613864718,295394763231,2663582754939,
    3099427691263,838728221713,2627576780992,4482031190388,2805808360540,1625368688167,
    5558006701169,5590876577879,972608901767,5360354827622,8582955564700,5544559680114,
    2485655839963,10136976623687,11447925221329,4294333978317,7464101287816,15961387973628,
    14454176096882,2287245222468,13810075939371,23366205082937,18770077618047,712479030335,
    21202978492334,33503033839898,26843009686748,2256613542926,28254544184097,47556891966465,
    42696519825065,12639012011001,29930862193822,64034612576118,70536791341486,42005699378020,
    12619912691093,70954585634641,106472060372369,100047854210311,48673272934161,32355185480968,
    114590462546168,166728523569168,165945259199460,106073702875922,89921771613,124725551812935,
    233382540946573,294774761631987,288880654964201,211222915839127,72666716187767,
    104522297683212,292718144066652,465196833865588,601080071726792,688103000636522,
    723081866785152,710536680023962,660223108217230,584368361789614,495233976342684,
    403371336684502,316680422855696,240179930428898],
   [176291146191992,125410312346336,86568913496484,58041917327436,37828784583036,23982437168244,
    14797584564094,8889921092082,5201735615588,2965055257630,1646576953276,890657193646,
    468966606946,240048410570,119124613568,56974230698,25933807092,10934033184,4144573436,
    1015349892]]
private def rkmC_w64_m4_s7b_17 : List ℤ := pzigCat
  [
   [347315034,455534896,586841015,1306961197,432630695,1502554098,1719803608,701630789,2836565659,
    1392378135,2605466084,4055267010,366206810,4935324907,4855583013,1769879910,7825426234,
    4476264894,5924611371,11077160943,2580957437,11057640070,13048006010,2115018591,18266203009,
    14091683001,10055346448,27254261906,13048820494,21760235969,36736764605,7834501287,
    38056298930,46464048028,2588253531,60117019847,55733033783,19669137326,87972173744,
    62754736966,46058569137,123332966541,67574977915,82987959870,166972849236,68894955884,
    133897490145,222449651789,67043652789,202137888922,293876138122,63252362344,291607637709,
    388230873489,61333720853,406598646394,516315586556,69875698950,550691979777,693824637143,
    103638845787,725032386088,941841808214,188791694930,924305140513,1288231104423,369498556737,
    1126434288610,1762522496414,714385296214,1278584104125,2383612151701,1319372934617,
    1274656126696,3134500680230,2302622846250,927675686581,3912599602179,3771663183879,
    51858223479,4451222259696,5735022253488,2036481329220,4223403390931,7930964352025,
    5356849160131,2388805884352,9566468101008,9974784832802,2073548725922,9054501949883,
    14879008079555,9784813925283,4064324138876,17324639788740,19668764744140,7471279222416,
    12594149898767,27092034040943,24628676496139,4169379571185,22959630935780,39288765370220,
    32145562372828,2498194723910,34130518352647,55797073965707,46886147925013,8085134447575,
    42411221310376,77572133970444,75654995947100,32320764115500,35700710139525,97452419296105,
    121848267478719,92301931253035,15087229090379,82243316035438,161479621329534,188691347658156,
    147305555342574,44389621820894,91711677080731,220825833779473,303582014677729,312731510052645,
    239773426885663,95560053139889,94343723245440,297342558792920,481899955277114,623866718210628,
    709862830714706,737596482606676,713817848787460,650996166652512,563799273967324,
    466175179339564,369444707679772],
   [281454486154910,206594811476476,146375264994206,100249042704470,66445009737924,42659935618044,
    26550985153366,16028610923836,9390102675394,5339837343210,2948057137802,1580192894322,
    821986752832,414478851968,202367782390,95168633894,42877638138,18134000602,6976108568,
    2005011310,260959252]]
private def rkmC_w64_m4_s7b_18 : List ℤ := pzigCat
  [
   [256246823,266638325,610211034,631715032,654125557,1526440731,102671299,1966248806,1688015860,
    1157261629,3165254879,1076686101,3236787456,3820614976,1369136497,6036639755,3185720831,
    5224119254,8025946924,260447338,9814909755,8325554825,5375047086,14861320320,5473953778,
    13986739303,18534260765,1834141618,24301066458,18141769418,15171979461,35774640725,
    12257272935,33899000590,44958616236,2276827705,57596368593,48160599515,28074611428,
    84599294114,41913097480,65876781143,111785767377,22022918365,116524475512,135097625834,
    16354616875,180887374643,150900947995,77245395832,257748896904,153241429550,165851782031,
    347960001515,138549136885,286657759960,452271971532,102802218048,445919938569,574763896669,
    43515594695,651648473674,723251969458,38795188199,914419142353,912573973623,139515373996,
    1248747581622,1168395682268,245329415207,1672430790371,1531688408809,326099468630,
    2201099201656,2063179292168,323514773289,2839795875037,2847124887721,133703590634,
    3561971629638,3987076345568,418453949332,4268786658153,5581607531621,1601597481407,
    4720394801168,7658331412034,3777602038556,4443813517067,10034936242303,7327339487849,
    2643512879642,12079231902944,12414103185284,1783473414652,12386859823229,18463580409433,
    9904091457569,8563848706886,23316353403746,21718930296416,2364064582844,22375178925745,
    34175502544475,21958947417697,8955648885574,38803315443682,45901793427456,21702508879486,
    21871604607917,58285041745669,62373846847813,26677259041533,32183064167558,81460322903870,
    90358829642448,47998679487154,28933010922073,103255096211127,135464989332067,103631603814779,
    15049230427571,95839573013430,181915414564712,203289709480938,143804065427844,17516322018096,
    136626564336757,268815381107335,335058103201461,310357050865917,194453984648207,9451341152725,
    208556186310272,420227795128572,592548968605288,704867232560844,750639766828374,
    735546569156782,673418247580964],
   [581579116133760,476852704364978,372910594498016,279089286136492,200409028943622,
    138353131910766,91967132894722,58935026394190,36443574757936,21761278100310,12554400768396,
    6999921887146,3772744989288,1965275067916,989090864312,480338293184,224805686296,100920003996,
    43136550498,17038431122,5939400356,1504009776]]
private def rkmC_w64_m4_s7b_19 : List ℤ := pzigCat
  [
   [210532368,268370868,200789253,689657527,129282218,1104590566,654988460,1017065065,1561508691,
    369638586,2568507074,1154487184,2626809443,3420713257,1020581288,4856216374,2218205482,
    4560706969,5984829705,1442694812,8659695182,4384153238,7719100655,11332116203,1155455090,
    14819834048,9506702836,11246617481,20149150725,1186369331,24096754408,19950965442,14789733623,
    35966906333,9615010285,37141344016,40877809022,13783744141,61748335591,32709802685,
    49271834950,80045658454,4921178478,94214143833,83637449343,45936465522,140913956072,
    62363657688,119291795165,177501091519,6392589375,210516399568,189958347956,90529007707,
    310395264003,163947903687,230809472116,405080373106,84368291522,414432199443,480088443407,
    60517965328,636436890194,519047821222,281743882683,892382781831,508415448353,588722866992,
    1179622911628,436629632716,991572621851,1500881793761,297583350785,1503939235370,
    1870259824200,93376668118,2144897291487,2319578992395,160637920002,2941245630974,
    2905669247142,428357063919,3926191166683,3722124791271,635139672304,5130420322932,
    4910174482564,637863631793,6556059743013,6664088439193,180999478048,8121007971728,
    9214831562816,1160039250036,9552836390649,12758536284503,4027318326709,10214572768038,
    17266405740146,9250028602352,8873404126767,22088825062703,17575965359845,3531196843792,
    25298376820092,28896515086364,8323658013508,22937644465549,40669284218295,28301725816475,
    8959109926586,45699298055588,53545578347902,22194532648400,31077048068955,71027761089487,
    67486334240899,16573198102099,54297120169810,101579524970372,91898540821664,23398190656720,
    70876464421467,139761122067327,141444086501715,66458714808589,55940636721270,170846207277316,
    223029531502894,181930525448130,54965643844776,115725315581867,270183961764243,
    352931027265247,331438634366287,204556876617089,442298554112,239169316244638,464466128594762,
    638700818488196],
   [740818080686248,767444733750390,729343475053844,645496676749844,537060955135054,
    422743475728148,316230046535952,225541759078268,153748139356462,100357853793394,
    62812988836878,37735161131566,21774616578486,12074275215502,6435143937838,3296046832866,
    1621852677332,766017086268,346592364478,149713479222,61318254348,23317497542,7694834100,
    1755749264]]
private def rkmC_w64_m4_s7b_20 : List ℤ := pzigCat
  [
   [440960412,244408544,733896701,944564983,619565858,1617767396,13642141,2161033153,1196334159,
    2166835156,2826862092,994821249,4245515577,1177173381,4645041106,4667156854,2999457065,
    7628301741,1082695841,8785330616,6842698282,6584422969,12851626147,183720211,15955622678,
    10726606274,12526514829,21766712811,993665776,27429568604,17001752200,22496748225,36278416779,
    2867290358,46694295098,28981926174,37172803331,61793324745,1588014580,77259275042,53821944458,
    55564669651,106657462873,10838329931,122010619560,103632590474,71076359073,180059560841,
    50164336597,180494448954,199930159070,64025573491,292348387267,151711314243,234243923532,
    369899122114,13085919386,436542220353,370701775719,223275095796,631347400818,255107911000,
    547334193213,769149972647,4939407894,929296398330,795559575456,424570124621,1326810512659,
    661979471831,1001412787426,1690574845472,329041162922,1722725902219,1974909476857,
    230391492802,2573385993442,2146272874224,1033282340631,3546974157755,2190921647817,
    2091387556982,4659172206968,2124194158688,3417001802217,5964519888967,2003499286501,
    5023626185622,7572365566916,1949294155078,6917105743881,9661602010935,2181840382945,
    9063957065760,12490038610356,3079192785508,11317351725595,16372759846347,5259047703409,
    13268396213994,21584391133998,9654385899036,13988840620351,28090357118713,17488303309649,
    11671501718688,34960733238996,29912816660534,3316804211553,39340500456323,46854935700097,
    14991563501073,35142648052906,64486370511800,45951117497760,12685437006825,71335695810307,
    85082690655619,37237436226281,45993409129082,110427833141188,108997888076540,33777416144746,
    76152748813431,156243576653347,154138402715251,60842584052203,82425662834380,204744720794542,
    241231563791036,164838395419926,1128865137481,193978891373621,338706458035577,377560575961003,
    289582731950919,94013837829729,160849354045324,416454297280246,622288983697692],
   [747717181313684,785235884108546,746516525830550,654527472261144,535210130926686,
    411147475341824,298210309318400,204944945858494,133795720793200,83123175573352,49205907889950,
    27775841065174,14956870553282,7683303006758,3763762835040,1756665204848,780064663192,
    328736888298,130707680634,48265256846,16126185266,4303254412,631186326]]
private def rkmC_w64_m4_s7b_21 : List ℤ := pzigCat
  [
   [578682409,125553671,1027540182,656458354,1142138559,1436113567,832489784,2263229376,140759000,
    3005049725,1599643965,2946738626,3487304086,2028266327,5552272921,334653585,6772371428,
    4001203092,6294947231,8353461769,3192207944,12333931152,2782915596,13615534759,10923337881,
    10943200438,19778404378,2559748071,25772705841,11708615739,25028662290,28637354970,
    13957675749,43252572625,8304447329,48221475464,38931596258,35774771497,69664274543,1029531426,
    85925160160,52054373024,72317050117,109204921561,18688725630,144872463388,70932184526,
    129914244549,170939465557,45070929476,236784341022,103379231476,217331356239,272523421977,
    76253267448,381196907388,172370108144,339191798313,446360016471,91727788952,603054281660,
    324553791218,489052805213,748292645311,34367655570,923486401292,652276362248,612839889557,
    1249330668009,228998391009,1315987324378,1304503296014,541268662785,1988565093279,
    953015381619,1597715475114,2442755668592,113803497386,2812352040431,2499092048239,
    1223298494076,4016570197414,2018157334214,3006483983709,5040747950521,916677021701,
    5149411514666,5751293799248,832086279471,7571692756457,6082301024215,3213675636696,
    10243312867216,6059742065754,6195891139669,13229922769155,5826016640037,9742659956098,
    16735588865238,5681811460988,13801468689831,21135635040783,6163762672565,18227463339312,
    26983793985492,8176512877746,22592393294861,34933150577061,13174484394965,25795180985214,
    45433433467174,23299549976304,25391447954447,57920687131965,41153772791567,16714245152674,
    69082391233090,68389012314276,7544573808218,69975579097457,101619527339697,55069428307015,
    43366911715278,124288221801882,124190907344566,32423585689790,97709208852295,181683058408457,
    158109364745811,28960373683545,139299009021868,252921475445266,242844588294672,
    101459914946106,114215460319627,311256090014775,403666509555247,347435494453245,
    153424488125009,123437329766458],
   [409528512725910,639388402324788,773682627226814,804213551432142,747962588197982,
    635500032477466,499296465196464,365553492881286,250669213076468,161541986202014,
    98055033138668,56135115280298,30328304850450,15462916411456,7435228474190,3367321053150,
    1433314759950,571310659006,211862743338,72204629376,21875176514,5278320340,630634378]]
private def rkmC_w64_m4_s7b_22 : List ℤ := pzigCat
  [
   [223450119,338054152,701813950,291105241,1264843209,32281418,1740059598,843682122,2032604879,
    1897179101,1925804044,3070988344,1093535741,4417279341,282290725,5296291474,2694808126,
    5518439153,5739711773,4430711938,9128191974,1478238577,12180432095,3593633493,13485020114,
    10361964330,11962017375,18265744185,6422713342,25312334572,3881190040,29254959955,18497926307,
    27095901250,35865402504,15688871743,51517285263,5896306917,59921582588,36965406372,
    54641801353,72931268167,29503739604,104129963912,18462411094,117115651371,84492398025,
    97015233604,154589804612,33864848067,205714273171,72366668643,208231986234,203798097692,
    136173871857,323027694031,21108786275,376880859842,245314541938,308887662411,478410597859,
    84286387702,624902738850,279196997196,577714078565,692895171297,258143153516,992310065944,
    323755712900,977485260915,1021331850859,497352684620,1547541899572,440620203158,1546624697399,
    1577525423499,755806042588,2400293653468,783600887794,2296613196485,2571856708021,
    867940106860,3682550923636,1684040896304,3108881909145,4331291464925,387485159314,
    5419686462684,3747414207054,3463381160039,7169877194313,1658089395393,7113261951676,
    7780748668390,1937594235137,10786331049495,6855734489779,6816976554018,13970707837096,
    4237289640886,12654980169749,16337450307619,10211543244,19178313159804,17843121514114,
    5663425200901,26314395947849,18802802151111,12400623340672,34306284091180,19967963470970,
    19785638729665,43765279193993,22669063494891,27078941875418,55602773577070,29055751513682,
    32728171447377,70656830682047,42370316110497,33354415745496,88579139693572,66835475588388,
    22173808059285,105164747581133,105865494316037,12345513102047,107248392218984,155669566662256,
    83935444111238,66537972181537,190180225501327,192064979996933,56185006900349,140658111726108,
    276784244695264,261097015389004,87235123449894,164054671047469,370318926581105],
   [429995722967669,307278605165091,40063310735665,285705211799806,576521026408578,
    765685788543646,829033429211478,781172332056586,659738991851408,507402458781836,
    358729057461338,234478483325574,142179674218870,80116602685318,41969525873488,20423866653330,
    9214775597256,3841681626088,1472419120556,514539931600,161750883044,44275917290,9831841726,
    1154691196]]
private theorem rkmWC_w64_m4_s7b_0 : bWinChk 625 18 100000000 1024 rkmPhb_w64_m4_p7b
    641 rkmXsWin_w64_m4_s7a_out 660 rkmC_w64_m4_s7b_1 3251772533 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_1 : bWinChk 625 18 100000000 1024 rkmPhb_w64_m4_p7b
    660 rkmC_w64_m4_s7b_1 680 rkmC_w64_m4_s7b_2 3071017982 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_2 : bWinChk 625 17 100000000 1024 rkmPhb_w64_m4_p7b
    680 rkmC_w64_m4_s7b_2 695 rkmC_w64_m4_s7b_3 3475311197 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_3 : bWinChk 625 17 100000000 1024 rkmPhb_w64_m4_p7b
    695 rkmC_w64_m4_s7b_3 711 rkmC_w64_m4_s7b_4 3537091999 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_4 : bWinChk 625 17 100000000 1024 rkmPhb_w64_m4_p7b
    711 rkmC_w64_m4_s7b_4 726 rkmC_w64_m4_s7b_5 2567988495 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_5 : bWinChk 625 17 100000000 1024 rkmPhb_w64_m4_p7b
    726 rkmC_w64_m4_s7b_5 741 rkmC_w64_m4_s7b_6 2724636864 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_6 : bWinChk 625 17 100000000 1024 rkmPhb_w64_m4_p7b
    741 rkmC_w64_m4_s7b_6 750 rkmC_w64_m4_s7b_7 3284402215 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_7 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    750 rkmC_w64_m4_s7b_7 761 rkmC_w64_m4_s7b_8 2810708930 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_8 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    761 rkmC_w64_m4_s7b_8 772 rkmC_w64_m4_s7b_9 2835199713 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_9 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    772 rkmC_w64_m4_s7b_9 781 rkmC_w64_m4_s7b_10 2714958413 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_10 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    781 rkmC_w64_m4_s7b_10 792 rkmC_w64_m4_s7b_11 2418821209 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_11 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    792 rkmC_w64_m4_s7b_11 801 rkmC_w64_m4_s7b_12 2856318306 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_12 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    801 rkmC_w64_m4_s7b_12 812 rkmC_w64_m4_s7b_13 2455988626 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_13 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    812 rkmC_w64_m4_s7b_13 822 rkmC_w64_m4_s7b_14 2699428308 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_14 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    822 rkmC_w64_m4_s7b_14 829 rkmC_w64_m4_s7b_15 2291089667 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_15 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    829 rkmC_w64_m4_s7b_15 834 rkmC_w64_m4_s7b_16 2111403375 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_16 : bWinChk 625 15 100000000 1024 rkmPhb_w64_m4_p7b
    834 rkmC_w64_m4_s7b_16 840 rkmC_w64_m4_s7b_17 2231772605 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_17 : bWinChk 625 15 100000000 1024 rkmPhb_w64_m4_p7b
    840 rkmC_w64_m4_s7b_17 844 rkmC_w64_m4_s7b_18 2073365354 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_18 : bWinChk 625 15 100000000 1024 rkmPhb_w64_m4_p7b
    844 rkmC_w64_m4_s7b_18 847 rkmC_w64_m4_s7b_19 2066093600 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_19 : bWinChk 625 15 100000000 1024 rkmPhb_w64_m4_p7b
    847 rkmC_w64_m4_s7b_19 853 rkmC_w64_m4_s7b_20 1869774937 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_20 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    853 rkmC_w64_m4_s7b_20 857 rkmC_w64_m4_s7b_21 2127796746 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_21 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    857 rkmC_w64_m4_s7b_21 859 rkmC_w64_m4_s7b_22 1866109828 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7b_22 : bWinChk 625 16 100000000 1024 rkmPhb_w64_m4_p7b
    859 rkmC_w64_m4_s7b_22 864 rkmXsWin_w64_m4_s7b_out 1829906542 = true := by decide +kernel
private theorem rkmWinIterSnd_w64_m4_p7b :
    RkmWinIterSound 373 1024 rkmHbWin_w64_m4_p7a 641 rkmXsWin_w64_m4_s7a_out
      864 rkmXsWin_w64_m4_s7b_out 59170957444 :=
  rkmChS 373 59170957444 (rkmChS 357 57341050902 (rkmChS 341 55474941074 (rkmChS 325
    53347144328 (rkmChS 310 51477369391 (rkmChS 295 49411275791 (rkmChS 280 47337910437 (rkmChS
    265 45106137832 (rkmChS 249 42994734457 (rkmChS 233 40703644790 (rkmChS 217 38004216482
    (rkmChS 201 35548227856 (rkmChS 185 32691909550 (rkmChS 169 30273088341 (rkmChS 153
    27558129928 (rkmChS 137 24722930215 (rkmChS 121 21912221285 (rkmChS 104 18627819070 (rkmChS
    87 15903182206 (rkmChS 70 13335193711 (rkmChS 53 9798101712 (rkmChS 36 6322790515
    (bWinChk_sound rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_0) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_1
    rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_2 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_3
    rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_4 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_5
    rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_6 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_7
    rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_8 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_9
    rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_10 rfl rfl) rkmHhb_w64_m4_p7b
    rkmWC_w64_m4_s7b_11 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_12 rfl rfl)
    rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_13 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_14 rfl
    rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_15 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_16
    rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_17 rfl rfl) rkmHhb_w64_m4_p7b
    rkmWC_w64_m4_s7b_18 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_19 rfl rfl)
    rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_20 rfl rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_21 rfl
    rfl) rkmHhb_w64_m4_p7b rkmWC_w64_m4_s7b_22 rfl rfl
private theorem rkmWinChain_w64_m4_s7_full :
    RkmWinIterSound 454 1024 rkmHbWin_w64_m4_p7a 552 rkmXsWin_w64_m4_s7a_in
      864 rkmXsWin_w64_m4_s7b_out 74141852558 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w64_m4_p7a) (hb2 := rkmHbWin_w64_m4_p7a)
    (x1 := rkmXsWin_w64_m4_s7a_out) (x1' := rkmXsWin_w64_m4_s7a_out)
    rfl rfl (muxIntListEq_eq_true.mpr rfl) rfl (muxIntListEq_eq_true.mpr rfl)
    rkmWinIterSnd_w64_m4_p7a rkmWinIterSnd_w64_m4_p7b
private theorem rkmWinSegWalkSnd_w64_m4_s7 :
    RkmWinSegWalkSound 454 ⟨1024, rkmHbWin_w64_m4_p7a, 552, rkmXsWin_w64_m4_s7a_in,
      864, rkmXsWin_w64_m4_s7b_out, 74141852558⟩ :=
  @rkmSegWalk_mk 454 1024 552 864 74141852558
    rkmHbWin_w64_m4_p7a rkmXsWin_w64_m4_s7a_in rkmXsWin_w64_m4_s7b_out
    (rkmw_buildHbFrom_length 1792 1024 20052279735 1024 0)
    (bAllT_hd (bAllT_tl rkmStatOk_w64_m4)) rkmWinChain_w64_m4_s7_full
private theorem rkmWalksSndHi_w64_m4_r1024 :
    RkmWinSegWalksSound [2, 6, 15, 25, 55, 115, 243, 454] rkmWalksHi_w64_m4_r1024 :=
  ⟨rkmWinSegWalkSnd_w64_m4_s0, ⟨rkmWinSegWalkSnd_w64_m4_s1, ⟨rkmWinSegWalkSnd_w64_m4_s2,
    ⟨rkmWinSegWalkSnd_w64_m4_s3, ⟨rkmWinSegWalkSnd_w64_m4_s4, ⟨rkmWinSegWalkSnd_w64_m4_s5,
    ⟨rkmWinSegWalkSnd_w64_m4_s6, ⟨rkmWinSegWalkSnd_w64_m4_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic w_hi64_m4_r1024 r = 1024 hit certificate (m = 4). -/
theorem rkmTrajHitHi_w64_m4 :
    RkmAnchorHitSound 4 ⟨1024, [4, 8, 16, 32, 64, 128, 256, 448],
      [2692575, 3792785, 5155440, 4542060, 5273504, 5943872, 7203425, 9103735],
      [2, 6, 15, 25, 55, 115, 243, 454],
      rkmMasksHi_w64_m4_r1024, rkmRowHi_w64_m4_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 4 2048 1024 rkmLs_m4 rkmHs_m4 rkmNs_m4
    rkmMasksHi_w64_m4_r1024 rkmWalksHi_w64_m4_r1024 rkmRowHi_w64_m4_r1024
    rkmWalksSndHi_w64_m4_r1024 (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_w64_m4)))
/-- Cumulative FindAllJohnsonRampKickMuxHiW64T03 lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T03 :
    @rkmTrajHitHi_w64_m4 = @rkmTrajHitHi_w64_m4 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T02) rfl).right

end
end QuantumComputation.Specs.DickeSol
