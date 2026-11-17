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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T00

/-
# Caustic `r = 1024` Halo-16 Walk `w_hi64_m2_r1024` (`FindAllJohnsonRampKickMuxHiW64T01`)

Certifies part `1` of `w_hi64_m2_r1024` (`r = 1024`, halo-16).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Kick-mask schedule for `w64_m2` `r = 1024`. -/
def rkmMasksHi_w64_m2_r1024 : List (List Bool) := [
  [], [], [], [], [], [], [], []]
/-- Certified `rowLo12` vector for `w64_m2` `r = 1024`. -/
def rkmRowHi_w64_m2_r1024 : List ℕ := List.replicate 919 0 ++ [
  83, 0, 4103, 0, 6619, 901, 1257, 27159, 0, 68728, 0, 72283, 59796, 18285, 232856, 0, 363642,
  79914, 248600, 556214, 9297, 1138501, 76702, 1076181, 1185166, 242385, 2984981, 72028, 3267168,
  2620609, 1015938, 7387013, 157031, 8235840, 6639253, 2308681, 18081556, 1021331, 17682711,
  19438539, 2579439, 42840722, 8189346, 29290766, 59885992, 23785, 87900373, 52153842, 24687257,
  163504632, 22924062, 116371706, 230370803, 322890, 294788546, 271235035, 22742924, 572888050,
  290747086, 129256257, 980837563, 318747895, 335964494, 1601175318, 420409413, 608375427,
  2603232082, 763248140, 796324218, 4218130758, 1857950059, 580248156, 6388563097, 5082951905,
  6012081, 7505365198, 12557479863, 2594926774, 3581600694, 21006477186, 20004412606, 1779248582,
  10066667093, 43256673531, 48484652301, 15506433676, 1861697277, 49805245477, 129616385106,
  179713971277, 172087829601, 125106941339, 72245328058, 33945451433, 13143686103, 4216059214,
  1119351012, 244036322, 42827156, 5752226, 500728, 9615, 0, 0, 0]

end

public section

private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
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
private abbrev uON : List ℕ → List ℤ := uHb
private abbrev bDec : ℕ → List ℕ → List ℤ := bD
private abbrev bEnc : ℕ → List ℤ → Option (List ℕ) := bE
private theorem uCNe (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := uCN_eq x xs
private theorem bDN (z : ℕ) : bDec z [] = [] := d0 z
private theorem bDC (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := dc z u us
private theorem bES (z : ℕ) (xs : List ℤ) (us : List ℕ)
    (h : bEnc z xs = some us) : bDec z us = xs := eS z xs us h
private theorem bSpS (z mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uON b) (bDec z v) :=
  bSp_sound z mL cL b v out h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, v => some v
  | k + 1, m, c, hbz, v =>
    match bSp z m c hbz v with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bIt z k m nL hbz vN
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
private def bDropN : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | _, [] => []
  | k + 1, _ :: xs => bDropN k xs
private theorem bDropN_uON : ∀ (s : ℕ) (b : List ℕ),
    uON (bDropN s b) = rkmDropInts s (uON b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => bDropN_uON k bs
private def bDrop2 : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, _ :: _ :: xs => bDrop2 k xs
  | _, _ => []
private theorem bDrop2_mkHbZ (z : ℕ) : ∀ (s : ℕ) (b : List ℕ),
    bDrop2 s (mkHbZ z b) = mkHbZ z (bDropN s b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: bs => by
    dsimp only [mkHbZ, bDropN]; rw [uCNe, uCNe]; dsimp only [bDrop2]; exact bDrop2_mkHbZ z k bs
private def bAbsZ (z u : ℕ) : ℕ := Nat.add (Nat.sub u z) (Nat.sub z u)
private theorem bAbsZ_eq (z u : ℕ) : bAbsZ z u = rkmIntAbsNat ((u : ℤ) - (z : ℤ)) := by
  unfold bAbsZ; simp only [Nat.add_eq, Nat.sub_eq]; cases h : z - u with
  | zero =>
    have hm : (u : ℤ) - (z : ℤ) = Int.ofNat (u - z) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; omega
  | succ k =>
    have hm : (u : ℤ) - (z : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; rw [Nat.add_eq]; omega
private def bPrepZ (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, us => us
  | k + 1, us => uCN z (bPrepZ z k us)
private theorem bPrepZ_eq (z : ℕ) : ∀ (k : ℕ) (us : List ℕ),
    bDec z (bPrepZ z k us) = rkmPrependZeros k (bDec z us)
  | 0, _ => rfl
  | k + 1, us => by
    dsimp only [bPrepZ, rkmPrependZeros]
    rw [uCNe, bDC, bZ0 z, rkmw_strictConsInt_eq, bPrepZ_eq z k us]
private def bNatLen : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNatLen us) 1
private theorem bNatLen_eq (z : ℕ) : ∀ (us : List ℕ), bNatLen us = altIntLen (bDec z us)
  | [] => by rw [bDN, rkmw_altIntLen_eq]; rfl
  | u :: us => by
    dsimp only [bNatLen]; rw [Nat.add_eq, bNatLen_eq z us, bDC]
    rw [rkmw_altIntLen_eq, rkmw_altIntLen_eq]; simp only [List.length_cons]
private def bTrimL (z thr : ℕ) : ℕ → List ℕ → ℕ → ℕ × List ℕ × ℕ
  | _, [], acc => (0, [], acc)
  | off, u :: us, acc =>
    fN (bAbsZ z u) fun ax =>
      match Nat.ble ax thr with
      | true =>
        fN (Nat.add off 1) fun off1 =>
          fN (Nat.add acc ax) fun acc1 => bTrimL z thr off1 us acc1
      | false => (off, u :: us, acc)
private theorem bTrimL_eq (z thr : ℕ) : ∀ (us : List ℕ) (off acc : ℕ),
    ((bTrimL z thr off us acc).1, bDec z (bTrimL z thr off us acc).2.1,
      (bTrimL z thr off us acc).2.2) = rkmTrimLeft thr off (bDec z us) acc
  | [], _, _ => by rw [bDN]; rfl
  | u :: us, off, acc => by
    rw [bDC]; dsimp only [bTrimL, rkmTrimLeft, fN]; simp only [rkmb_forceNat_eq]; rw [bAbsZ_eq z u]
    cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
    | false => dsimp only; rw [bDC]
    | true =>
      dsimp only
      exact bTrimL_eq z thr us (Nat.add off 1) (Nat.add acc (rkmIntAbsNat ((u : ℤ) - (z : ℤ))))
private def bTrimR (z thr : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | u :: us =>
    match bTrimR z thr us with
    | ([], dTail) =>
      fN (bAbsZ z u) fun ax =>
        match Nat.ble ax thr with
        | true => fN (Nat.add ax dTail) fun dSum => ([], dSum)
        | false => (uCN u [], dTail)
    | (v :: vs, dTail) => (uCN u (v :: vs), dTail)
private theorem bTrimR_eq (z thr : ℕ) : ∀ (us : List ℕ),
    (bDec z (bTrimR z thr us).1, (bTrimR z thr us).2) = rkmTrimRight thr (bDec z us)
  | [] => by rw [bDN]; rfl
  | u :: us => by
    rw [bDC z u us]; dsimp only [bTrimR, rkmTrimRight]; rw [← bTrimR_eq z thr us]
    rcases bTrimR z thr us with ⟨ws, dTail⟩; cases ws with
    | nil =>
      dsimp only; rw [bDN]; dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [bAbsZ_eq z u]
      cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
      | true => rfl
      | false => dsimp only; rw [uCNe, bDC, bDN, rkmw_strictConsInt_eq]
    | cons v vs =>
      dsimp only; rw [bDC z v vs]; dsimp only; rw [uCNe, bDC, bDC z v vs, rkmw_strictConsInt_eq]
private def bTrimW (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) : ℕ × List ℕ × ℕ :=
  match bTrimL z thr off us dropAcc with
  | (off1, us1, d1) =>
    match bTrimR z thr us1 with
    | ([], d2) => fN (Nat.add d1 d2) fun dOut => (0, [], dOut)
    | (v :: vs, d2) => fN (Nat.add d1 d2) fun dOut => (off1, v :: vs, dOut)
private theorem bTrimW_eq (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) :
    ((bTrimW z thr off us dropAcc).1, bDec z (bTrimW z thr off us dropAcc).2.1,
      (bTrimW z thr off us dropAcc).2.2) = rkmTrimWin thr off (bDec z us) dropAcc := by
  dsimp only [bTrimW, rkmTrimWin]; rw [← bTrimL_eq z thr us off dropAcc]
  rcases bTrimL z thr off us dropAcc with ⟨off1, us1, d1⟩; dsimp only; rw [← bTrimR_eq z thr us1]
  rcases bTrimR z thr us1 with ⟨ws, d2⟩; cases ws with
  | nil => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rfl
  | cons v vs => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [bDC z v vs]
private def bWinStepN (z thr d : ℕ) (hbz : List ℕ)
    (off : ℕ) (us : List ℕ) (dropAcc : ℕ) : Option (ℕ × List ℕ × ℕ) :=
  fN (Nat.sub off 16) fun sLo => fN (Nat.sub off sLo) fun padL =>
    fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (bDrop2 sLo hbz) fun hbzSl =>
      fL (bPrepZ z padL us) fun vns => fN (bNatLen vns) fun curLen =>
        match bIt z 1 remMax curLen hbzSl vns with
        | none => none
        | some out => some (bTrimW z thr sLo out dropAcc)
private theorem bWinStepN_sound (z thr d : ℕ) (b : List ℕ)
    (off : ℕ) (us : List ℕ) (dropAcc o1 : ℕ) (u1 : List ℕ) (d1 : ℕ)
    (h : bWinStepN z thr d (mkHbZ z b) off us dropAcc = some (o1, u1, d1)) :
    (o1, bDec z u1, d1) = muxWinStepT16 thr d (uON b) off (bDec z us) dropAcc := by
  unfold bWinStepN at h; unfold muxWinStepT16; dsimp only [fN, fL] at h
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h ⊢
  set sLo := Nat.sub off 16; set padL := Nat.sub off sLo
  set remMax := Nat.sub (Nat.add d 1) sLo; set vns := bPrepZ z padL us
  rw [bDrop2_mkHbZ] at h; revert h
  cases hi : bIt z 1 remMax (bNatLen vns) (mkHbZ z (bDropN sLo b)) vns with
  | none => intro h; dsimp only at h; cases h
  | some out =>
    intro h; dsimp only at h; injection h with h'
    have ho : o1 = (bTrimW z thr sLo out dropAcc).1 := (congrArg Prod.fst h').symm
    have hu : u1 = (bTrimW z thr sLo out dropAcc).2.1 := (congrArg (fun p => p.2.1) h').symm
    have hd : d1 = (bTrimW z thr sLo out dropAcc).2.2 := (congrArg (fun p => p.2.2) h').symm
    rw [ho, hu, hd, bTrimW_eq z thr sLo out dropAcc]
    rw [bItS z 1 remMax (bNatLen vns) (bDropN sLo b) vns out hi]
    dsimp only [vns]; rw [bNatLen_eq z (bPrepZ z padL us), bDropN_uON sLo b, bPrepZ_eq z padL us]
private def bWinIterN (z : ℕ) :
    ℕ → ℕ → ℕ → List ℕ → ℕ → List ℕ → ℕ → Option (ℕ × List ℕ × ℕ)
  | 0, _, _, _, off, us, dropAcc => some (off, us, dropAcc)
  | k + 1, thr, d, hbz, off, us, dropAcc =>
    match bWinStepN z thr d hbz off us dropAcc with
    | none => none
    | some (off1, us1, drop1) => bWinIterN z k thr d hbz off1 us1 drop1
private theorem bWinIterN_sound (z : ℕ) :
    ∀ (k thr d : ℕ) (b : List ℕ) (off : ℕ) (us : List ℕ) (dropAcc oR : ℕ) (uR : List ℕ) (dR : ℕ),
      bWinIterN z k thr d (mkHbZ z b) off us dropAcc = some (oR, uR, dR) →
        (oR, bDec z uR, dR) = muxWinIterT16 k thr d (uON b) off (bDec z us) dropAcc
  | 0, _, _, _, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWinIterN, muxWinIterT16] at h ⊢; injection h with h'
    rcases Prod.mk.inj h' with ⟨rfl, h2⟩; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩; rfl
  | k + 1, thr, d, b, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWinIterN, muxWinIterT16] at h ⊢; revert h
    cases hs : bWinStepN z thr d (mkHbZ z b) off us dropAcc with
    | none => intro h; dsimp only at h; cases h
    | some res1 =>
      rcases res1 with ⟨o1, u1, d1⟩; intro h; dsimp only at h
      rw [← bWinStepN_sound z thr d b off us dropAcc o1 u1 d1 hs]; dsimp only
      exact bWinIterN_sound z k thr d b o1 u1 d1 oR uR dR h
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; simp only [Bool.and_eq_true, rkmw_nat_ble_eq_true] at h
  exact Nat.le_antisymm h.1 h.2
private def bWinChk (steps thr d : ℕ) (b : List ℕ)
    (offIn : ℕ) (xsIn : List ℤ) (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  let z := 2000000000000000
  fL b fun bF => fL (mkHbZ z bF) fun hbz => fL xsIn fun inF => fL xsOut fun outF =>
    match bEnc z inF with
    | none => false
    | some uIn =>
      match bWinIterN z steps thr d hbz offIn uIn 0 with
      | none => false
      | some (oR, uR, dR) =>
        Bool.and (bNatEq oR offOut) (Bool.and (muxIntListEq (bDec z uR) outF) (bNatEq dR dropExp))
private theorem bWinChk_sound {steps thr d : ℕ} {b : List ℕ}
    {offIn : ℕ} {xsIn : List ℤ} {offOut : ℕ} {xsOut : List ℤ} {dropExp : ℕ}
    (h : bWinChk steps thr d b offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d (uON b) offIn xsIn offOut xsOut dropExp := by
  unfold bWinChk at h; dsimp only [fL] at h; simp only [rkmb_forceList_eq] at h
  set z := 2000000000000000; revert h
  cases he : bEnc z xsIn with
  | none => intro h; dsimp only at h; cases h
  | some uIn =>
    dsimp only; cases hi : bWinIterN z steps thr d (mkHbZ z b) offIn uIn 0 with
    | none => intro h; dsimp only at h; cases h
    | some res =>
      rcases res with ⟨oR, uR, dR⟩; intro h; dsimp only at h
      simp only [Bool.and_eq_true, muxIntListEq_eq_true] at h
      obtain ⟨ho, hx, hd⟩ := h; have ho' := bNatEq_true ho; have hd' := bNatEq_true hd
      subst ho'; subst hx; subst hd'
      have hit := bWinIterN_sound z steps thr d b offIn uIn 0 oR uR dR hi
      rw [bES z xsIn uIn he] at hit
      have h2 : muxWinIterT16HiChk steps thr 0 d (uON b) offIn xsIn oR (bDec z uR) dR = true := by
        unfold muxWinIterT16HiChk; simp only [rkmb_forceList_eq]; rw [← hit]
        simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, muxIntListEq_eq_true]
        exact ⟨trivial, trivial, trivial⟩
      exact muxWinIterT16HiChk_sound h2
private theorem rkmChS (kT dT : ℕ) {k1 k2 d o0 o1 o2 d1 d2 : ℕ}
    {b : List ℕ} {x0 x1 x2 : List ℤ} (h1 : RkmWinIterSound k1 d (uON b) o0 x0 o1 x1 d1)
    (h2 : bWinChk k2 100000000 d b o1 x1 o2 x2 d2 = true) (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d (uON b) o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (bWinChk_sound h2)
private theorem rkmSubHb {s d o0 o1 dr : ℕ} {h1 h2 x0 x1 : List ℤ}
    (heq : muxIntListEq h1 h2 = true) (h : RkmWinIterSound s d h2 o0 x0 o1 x1 dr) :
    RkmWinIterSound s d h1 o0 x0 o1 x1 dr := by
  rw [muxIntListEq_eq_true.mp heq]; exact h
private theorem rkmSegWalk_mk {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d)
    (hble : Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private def bAll5 (a b c d e : Bool) : Bool :=
  match a, b, c, d, e with
  | true, true, true, true, true => true | _, _, _, _, _ => false
private theorem bAll5_elim {a b c d e : Bool} (h : bAll5 a b c d e = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    first | exact ⟨rfl, rfl, rfl, rfl, rfl⟩ | exact Bool.noConfusion h
private def rkmZZ (u : ℕ) : ℤ :=
  match Nat.ble (Nat.mod u 2) 0 with
  | true => Int.ofNat (Nat.div u 2)
  | false => Int.negSucc (Nat.div u 2)
private def rkmMapZZ : List ℕ → List ℤ
  | [] => []
  | u :: us => rkmZZ u :: rkmMapZZ us
private def rkmHbWin_w64_m2_p7b : List ℤ :=
  altBuildHbFrom 1792 1024 20052279735 0 1024
private def rkmXsWin_w64_m2_s7b_in : List ℤ := rkmMapZZ [222999214,699887370,892440612,329395062,
  955273981,2138398039,2718006983,1894648055,584565466,3666737580,5808935580,5587559650,2026005392,
  4165308847,10476990969,13731020437,10665753965,1053874977,12703719472,25169779378,29311089644,
  20357829508,1830053701,31172960859,55968164027,62866140513,42829473611,4435079828,66076326692,
  119291789224,137791172666,101770268570,8914428654,119574818293,241644177027,304544803285,
  263612559479,102217264481,154347821496,436448405986,643842492150,675424095842,464922968662,
  13797958274,590304144223,1182728002607,1555848111243,1517350507469,956827250687,99491658000,
  1462666478176,2798241630524,3691555703086,3748482095022,2710957778724,561174064034,2420681756833,
  5662913103615,8383771804475,9740354098053,9018532572917,5825394207423,242972910467,7096463593752,
  15039084323746,22046305479450,26428356936012,26635646980168,21562205898864,10808655954842,
  5143785604179,24882224915651,46145906070145,66039774017537,81348935389625,88908725017401,
  85982503416087,70595165452567,41777408075117,302975185042,54339127931956,118005034370930,
  188177045563704,261224864580300,333336186832548,400836268345608,460469721590438,509621411837960,
  546458978262218,569993266376258,580063861187684,577257048893200,562777031935604,538287556172982,
  505743038696662,467224094048542,424792662434334,380373693430298,335666759010542,292091718730570,
  250763582671466,212490974560386,177796883054720,146951984190264,120016280159792,96883418050954,
  77326016619742,61035306988452,47655815655614,36815145411328,28145114636454,21297193165686,
  15953781790386,11833174879710,8691612037994,6322719872176,4556052864352,3252227512152,
  2299756741438,1611272844198,1118469043578,768999804632,523702649092,353211730684,235710391460,
  155547857676,101478708392,65376358574,41157769818,25422815494,15271589290,8579616692,4378874254,
  1960743154,610223118]
private def rkmXsWin_w64_m2_s7b_out : List ℤ := rkmMapZZ [418708104,185805963,985321945,87440295,
  1467161676,487621200,1805492739,1423789623,2056229652,2579488270,1861265955,3961328377,1014107932,
  5552528224,586240780,6793470913,3069453541,7352402292,6353323126,6904729051,10156770625,
  4921729592,14426213174,1018910589,18161757819,5487835127,20316658630,14190812064,19876469775,
  24967308375,14904298844,36443472884,4120095343,46347271681,13359601721,51365244350,37076791516,
  47676962721,64994345059,31402890484,92579620074,780332432,112229609113,49068971459,115357338188,
  110243114392,91343598903,174510660351,31917617950,225901332864,65121774432,243019398533,
  192171475373,202929579062,328850063622,86545000581,438550870793,110832068081,473146495586,
  370496220532,381361269489,640024371867,127786642416,834740809620,286444611074,848130133581,
  799487718851,580872012412,1275521245150,13419755122,1516472642101,875803557857,1307614417098,
  1802013137564,503270091055,2444427817553,864323717015,2385199683282,2487723109048,1295071435747,
  3765835914469,847179939403,3925478224768,3548075648216,2326291819743,5746227905639,1102962473923,
  6050046581116,5463765577712,3349285096783,8814898387567,2331635469833,8720578916434,9128247519132,
  3522542584957,13400980527043,6033822601687,11134604636016,15787623702276,618873306993,
  19061455353647,14753939043793,10247670256844,25884201502202,9886231633226,21885559279573,
  30666357543567,1446885729113,34649230104118,33248845083284,9848324161481,48180575320595,
  34413030452635,23048599978218,62947068149412,36017439764594,36969084058985,80339793056715,
  41318191034809,49640950755052,102354172423000,55564307319510,56748849858613,130204691852961,
  86518305137001,48487096869018,160167390272070,142900063143346,5214325030477,173577437125805,
  224430739078117,102191263033829,120003367556808,290182643782546,283184328061030,84672695746514,
  200975978971933,416275190566913,440695030554355,249360078597377,86605195801010,446652192480358,
  720355928210282,848164108686404,829979818544320,707719607769780,537880236262824,368796243869532,
  229602247885840,130172792085630,67223822595598,31553739434572,13398907803064,5107175693510,
  1725659934342,506541753252,124348516696,23206312892,2226669938]
private def hbN_w64_m2_s7b_p0 : List ℕ := [54326625688279,76770497993776,93952067358139,
  108403121287610,121105145409063,132561907160710,143072902087549,152833419577692,161979212754325,
  170609198568271,178798108504692,186604045832368,194073252239511,201243248822281,208144981819019,
  214804333440353,221243213391383,227480365147557,233531973148798,239412127903567,245133187658361,
  250706063440299,256140446435377,261444991355642,266627465784187,271694872912625,276653553247983,
  281509269534651,286267278159514,290932389581772,295509019782641,300001234314998,304412786214525,
  308747148787245,313007544095773,317196967814930,321318211007193,325373879272373,329366409648753,
  333298085580442,337171050214933,340987318253221,344748786540707,348457243558795,352114377953655,
  355721786218993,359280979633312,362793390538290,366260378033268,369683233150949,373063183570990,
  376401397920992,379698989708237,382957020920252,386176505327687,389358411519109,392503665693843,
  395613154236080,398687726090842,401728194960169,404735341335895,407709914383650,410652633691213,
  413564190892969,416445251181062,419296454712758,422118417922626,424911734747289,427676977769779,
  430414699289858,433125432326093,435809691554932,438467974191562,441100760816916,443708516154792,
  446291689802738,448850716920006,451386018875642,453898003859493,456387067458699,458853593202025,
  461297953074218,463720508002359,466121608316084,468501594183346,470860796023317,473199534897862,
  475518122882939,477816863421174,480096051656762,482355974753769,484596912198830,486819136089177,
  489022911406848,491208496279886,493376142231276,495526094416321,497658591849101,499773867618630,
  501872149095272,503953658127960,506018611232707,508067219772870,510099690131622,512116223877022,
  514117017920081,516102264666183,518072152160191,520026864225568,521966580597814,523891477052486,
  525801725528090,527697494244071,529578947814160,531446247355287,533299550592270,535139011958488,
  536964782692720,538777010932326,540575841802940]
private def hbN_w64_m2_s7b_p1 : List ℕ := [542361417504829,544133877396087,545893358072771,
  547639993446152,549373914817186,551095250948324,552804128132799,554500670261468,556184998887340,
  557857233287870,559517490525123,561165885503892,562802531027856,564427537853854,566041014744366,
  567643068518254,569233804099843,570813324566416,572381731194167,573939123502689,575485599298043,
  577021254714471,578546184254806,580060480829613,581564235795129,583057538990042,584540478771137,
  586013142047876,587475614315931,588927979689719,590370320933969,591802719494366,593225255527287,
  594638007928686,596041054362135,597434471286061,598818333980216,600192716571384,601557692058373,
  602913332336311,604259708220253,605596889468152,606924944803192,608243941935511,609553947583338,
  610855027493556,612147246461727,613430668351563,614705356113905,615971371805183,617228776605409,
  618477630835690,619717993975298,620949924678298,622173480789747,623388719361492,624595696667556,
  625794468219152,626985088779311,628167612377150,629342092321795,630508581215948,631667130969140,
  632817792810648,633960617302105,635095654349814,636222953216756,637342562534322,638454530313765,
  639558903957381,640655730269433,641745055466814,642826925189473,643901384510594,644968477946543,
  646028249466591,647080742502415,648125999957386,649164064215646,650194977150988,651218780135531,
  652235514048213,653245219283089,654247935757450,655243702919772,656232559757478,657214544804550,
  658189696148966,659158051439984,660119647895266,661074522307858,662022711053019,662964250094907,
  663899174993129,664827520909152,665749322612581,666664614487312,667573430537555,668475804393739,
  669371769318291,670261358211304,671144603616092,672021537724624,672892192382866,673756599096000,
  674614789033554,675466793034426,676312641611804,677152364958002,677985992949192,678813555150051,
  679635080818314,680450598909246,681260138080023,682063726694032,682861392825090,683653164261587,
  684439068510544,685219132801599,685993384090926]
private def hbN_w64_m2_s7b_p2 : List ℕ := [686761849065066,687524554144705,688281525488366,
  689032788996051,689778370312798,690518294832192,691252587699797,691981273816535,692704377842006,
  693421924197740,694133937070403,694840440414934,695541457957636,696237013199209,696927129417730,
  697611829671585,698291136802341,698965073437577,699633661993667,700296924678505,700954883494195,
  701607560239691,702254976513386,702897153715669,703534113051432,704165875532533,704792461980223,
  705413893027529,706030189121601,706641370526017,707247457323050,707848469415900,708444426530890,
  709035348219622,709621253861104,710202162663834,710778093667864,711349065746814,711915097609868,
  712476207803731,713032414714558,713583736569846,714130191440309,714671797241707,715208571736663,
  715740532536438,716267697102685,716790082749176,717307706643503,717820585808744,718328737125117,
  718832177331599,719330923027524,719824990674152,720314396596226,720799156983489,721279287892191,
  721754805246570,722225724840307,722692062337962,723153833276391,723611053066139,724063736992811,
  724511900218428,724955557782758,725394724604628,725829415483222,726259645099353,726685428016721,
  727106778683153,727523711431822,727936240482448,728344379942490,728748143808309,729147545966324,
  729542600194144,729933320161692,730319719432305,730701811463827,731079609609677,731453127119907,
  731822377142249,732187372723142,732548126808745,732904652245935,733256961783299,733605068072103,
  733948983667249,734288721028227,734624292520043,734955710414140,735282986889309,735606134032580,
  735925163840110,736240088218048,736550918983401,736857667864879,737160346503729,737458966454567,
  737753539186185,738044076082359,738330588442640,738613087483139,738891584337292,739166090056631,
  739436615611527,739703171891938,739965769708137,740224419791435,740479132794898,740729919294044,
  740976789787541,741219754697895,741458824372120,741694009082412,741925319026804,742152764329820,
  742376355043114,742596101146106,742812012546609]
private def hbN_w64_m2_s7b_p3 : List ℕ := [743024099081442,743232370517047,743436836550086,
  743637506808035,743834390849778,744027498166177,744216838180652,744402420249742,744584253663662,
  744762347646858,744936711358548,745107353893259,745274284281358,745437511489575,745597044421522,
  745752891918201,745905062758511,746053565659744,746198409278077,746339602209059,746477152988089,
  746611070090892,746741361933986,746868036875140,746991103213839,747110569191725,747226442993052,
  747338732745116,747447446518696,747552592328482,747654178133495,747752211837511,747846701289469,
  747937654283884,748025078561246,748108981808422,748189371659046,748266255693912,748339641441354,
  748409536377626,748475947927278,748538883463527,748598350308617,748654355734188,748706906961625,
  748756011162416,748801675458496,748843906922595,748882712578572,748918099401755,748950074319272,
  748978644210374,749003815906763,749025596192911,749043991806371,749059009438094,749070655732733,
  749078937288949,749083860659711,749085432352591,749083658830058,749078546509770,749070101764855,
  749058330924196,749043240272709,749024836051620,749003124458735,748978111648710,748949803733313,
  748918206781693,748883326820630,748845169834798,748803741767013,748759048518483,748711095949055,
  748659889877458,748605436081542,748547740298516,748486808225178,748422645518155,748355257794121,
  748284650630027,748210829563325,748133800092183,748053567675705,747970137734144,747883515649110,
  747793706763786,747700716383125,747604549774059,747505212165695,747402708749518,747297044679580,
  747188225072696,747076255008636,746961139530308,746842883643943,746721492319284,746596970489756,
  746469323052653,746338554869307,746204670765262,746067675530447,745927573919340,745784370651136,
  745638070409911,745488677844782,745336197570062,745180634165425,745021992176052,744860276112787,
  744695490452287,744527639637167,744356728076148,744182760144199,744005740182679,743825672499474,
  743642561369135,743456411033014,743267225699396]
private def hbN_w64_m2_s7b_p4 : List ℕ := [743075009543626,742879766708244,742681501303107,
  742480217405513,742275919060327,742068610280099,741858295045181,741644977303848,741428660972409,
  741209349935319,740987048045291,740761759123408,740533486959221,740302235310864,740068007905150,
  739830808437673,739590640572911,739347507944320,739101414154427,738852362774931,738600357346789,
  738345401380305,738087498355223,737826651720811,737562864895943,737296141269185,737026484198875,
  736753897013201,736478383010280,736199945458230,735918587595251,735634312629687,735347123740104,
  735057024075358,734764016754657,734468104867629,734169291474385,733867579605583,733562972262482,
  733255472417006,732945083011797,732631806960270,732315647146668,731996606426109,731674687624642,
  731349893539289,731022226938093,730691690560164,730358287115721,730022019286129,729682889723948,
  729340901052960,728996055868212,728648356736047,728297806194138,727944406751521,727588160888618,
  727229071057273,726867139680770,726502369153863,726134761842795,725764320085323,725391046190731,
  725014942439854,724636011085088,724254254350410,723869674431385,723482273495181,723092053680575,
  722699017097962,722303165829361,721904501928417,721503027420405,721098744302230,720691654542427,
  720281760081155,719869062830196,719453564672947,719035267464410,718614173031187,718190283171462,
  717763599654996,717334124223104,716901858588641,716466804435987,716028963421020,715588337171100,
  715144927285042,714698735333089,714249762856890,713798011369463,713343482355170,712886177269681,
  712426097539942,711963244564135,711497619711641,711029224322999,710558059709866,710084127154972,
  709607427912070,709127963205895,708645734232108,708160742157250,707672988118682,707182473224535,
  706689198553649,706193165155514,705694374050211,705192826228344,704688522650979,704181464249572,
  703671651925905,703159086552007,702643768970088,702125699992456,701604880401446,701081310949333,
  700554992358256,700025925320130,699494110496558]
private def hbN_w64_m2_s7b_p5 : List ℕ := [698959548518749,698422239987419,697882185472704,
  697339385514061,696793840620172,696245551268845,695694517906907,695140740950107,694584220783003,
  694024957758856,693462952199515,692898204395309,692330714604923,691760483055286,691187509941444,
  690611795426440,690033339641187,689452142684337,688868204622151,688281525488366,687692105284055,
  687099943977491,686505041504002,685907397765830,685307012631979,684703885938067,684098017486175,
  683489407044686,682878054348131,682263959097024,681647120957699,681027539562145,680405214507829,
  679780145357528,679152331639150,678521772845555,677888468434374,677252417827817,676613620412492,
  675972075539205,675327782522771,674680740641808,674030949138542,673378407218594,672723114050777,
  672065068766879,671404270461449,670740718191575,670074410976663,669405347798210,668733527599570,
  668058949285721,667381611723031,666701513739006,666018654122054,665333031621228,664644644945977,
  663953492765881,663259573710397,662562886368585,661863429288843,661161200978627,660456199904177,
  659748424490227,659037873119722,658324544133523,657608435830109,656889546465276,656167874251831,
  655443417359277,654716173913500,653986141996446,653253319645796,652517704854632,651779295571101,
  651038089698076,650294085092806,649547279566563,648797670884285,648045256764213,647290034877521,
  646532002847941,645771158251383,645007498615546,644241021419528,643471724093426,642699604017932,
  641924658523920,641146884892032,640366280352248,639582842083462,638796567213041,638007452816381,
  637215495916459,636420693483371,635623042433869,634822539630891,634019181883077,633212965944286,
  632403888513098,631591946232314,630777135688447,629959453411200,629138895872942,628315459488176,
  627489140612990,626659935544514,625827840520353,624992851718020,624154965254363,623314177184970,
  622470483503581,621623880141477,620774362966870,619921927784270,619066570333862,618208286290850,
  617347071264810,616482920799020,615615830369785]
private def hbN_w64_m2_s7b_p6 : List ℕ := [614745795385752,613872811187210,612996873045380,
  612117976161699,611236115667083,610351286621184,609463484011636,608572702753286,607678937687413,
  606782183580932,605882435125593,604979686937157,604073933554564,603165169439086,602253388973470,
  601338586461057,600420756124895,599499892106840,598575988466628,597649039180947,596719038142484,
  595785979158961,594849855952152,593910662156882,592968391320016,592023036899422,591074592262923,
  590123050687227,589168405356844,588210649362977,587249775702401,586285777276316,585318646889190,
  584348377247571,583374960958883,582398390530206,581418658367025,580435756771964,579449677943497,
  578460413974635,577467956851587,576472298452405,575473430545595,574471344788714,573466032726930,
  572457485791568,571445695298621,570430652447238,569412348318185,568390773872274,567365919948769,
  566337777263761,565306336408507,564271587847749,563233521917993,562192128825763,561147398645813,
  560099321319318,559047886652020,557993084312347,556934903829488,555873334591443,554808365843026,
  553739986683831,552668186066167,551592952792940,550514275515511,549432142731493,548346542782523,
  547257463851977,546164893962650,545068820974381,543969232581643,542866116311071,541759459518952,
  540649249388659,539535472928037,538418116966732,537297168153469,536172612953274,535044437644639,
  533912628316630,532777170865933,531638050993840,530495254203172,529348765795144,528198570866151,
  527044654304498,525887000787058,524725594775857,523560420514587,522391462025044,521218703103494,
  520042127316952,518861717999385,517677458247837,516489330918460,515297318622462,514101403721967,
  512901568325781,511697794285066,510490063188909,509278356359806,508062654849029,506842939431894,
  505619190602927,504391388570905,503159513253797,501923544273576,500683460950920,499439242299784,
  498190867021841,496938313500802,495681559796588,494420583639374,493155362423484,491885873201141,
  490612092676063,489333997196907,488051562750550]
private def hbN_w64_m2_s7b_p7 : List ℕ := [486764764955203,485473579053358,484177979904556,
  482877941977978,481573439344846,480264445670632,478950934207073,477632877783978,476310248800823,
  474983019218136,473651160548647,472314643848217,470973439706524,469627518237500,468276849069520,
  466921401335326,465561143661674,464196044158710,462826070409056,461451189456587,460071367794911,
  458686571355526,457296765495641,455901914985664,454501983996335,453096936085487,451686734184438,
  450271340583987,448850716920006,447424824158611,445993622580904,444557071767258,443115130581140,
  441667757152453,440214908860371,438756542315661,437292613342465,435823076959518,434347887360797,
  432866997895559,431380361047757,429887928414816,428389650685720,426885477618413,425375358016469,
  423859239705002,422337069505798,420808793211621,419274355559679,417733700204196,416186769688069,
  414633505413564,413073847612015,411507735312480,409935106309317,408355897128622,406770042993499,
  405177477788091,403578134020333,401971942783364,400358833715540,398738734958987,397111573116630,
  395477273207622,393835758621104,392186951068229,390530770532346,388867135217285,387195961493633,
  385517163842914,383830654799572,382136344890648,380434142573045,378723954168246,377005683794384,
  375279233295501,373544502167882,371801387483291,370049783808964,368289583124188,366520674733274,
  364742945174756,362956278126586,361160554307133,359355651371734,357541443804577,355717802805629,
  353884596172349,352041688175877,350188939431393,348326206762293,346453343057831,344570197123831,
  342676613526059,340772432425803,338857489407186,336931615295700,334994635967412,333046372148238,
  331086639202663,329115246911214,327131999235937,325136694073099,323129122992237,321109070960631,
  319076316052195,317030629139692,314971773569091,312899504814797,310813570114339,308713708081033,
  306599648292949,304471110856402,302327805942009,300169433291179,297995681690693,295806228412829,
  293600738618227,291378864718413,289140245694621]
private def hbN_w64_m2_s7b_p8 : List ℕ := [286884506369176,284611256625358,282320090571214,
  280010585642329,277682301638012,275334779684776,272967541120285,270580086290195,268171893249429,
  265742416358454,263291084763999,260817300752381,258320437962133,255799839440973,253254815530230,
  250684641557618,248088555316734,245465754308667,242815392717722,240136578089251,237428367672939,
  234689764389461,231919712371979,229117092026442,226280714545649,223409315801435,220501549526607,
  217555979683049,214571071894068,211545183796850,208476554143929,205363290449569,202203354936410,
  198994548487585,195734492247132,192420606433374,189050085831419,185619871305676,182126616512928,
  178566648789340,174935922914693,171229966101675,167443812085146,163571921549954,159608085269044,
  155545305126766,151375646525401,147090053285455,142678112690199,138127753211274,133424849727646,
  128552699092793,123491309876607,118216418860044,112698093654932,106898686340767,100769726714550,
  94246994678557,87242268099132,79628509240106,71210701993145,61660496081362,50337533014494,
  35588271769886]
private def hbN_w64_m2_p7b : List ℕ :=
  pCat hbN_w64_m2_s7b_p0 (pCat hbN_w64_m2_s7b_p1 (pCat hbN_w64_m2_s7b_p2 (pCat hbN_w64_m2_s7b_p3
    (pCat hbN_w64_m2_s7b_p4 (pCat hbN_w64_m2_s7b_p5 (pCat hbN_w64_m2_s7b_p6 (pCat
    hbN_w64_m2_s7b_p7 hbN_w64_m2_s7b_p8)))))))
private def rkmC_w64_m2_s7b_1 : List ℤ := rkmMapZZ [291146229,648504297,776273233,247697057,
  1039380732,2044407378,2366268444,1241617624,1327544257,3992529481,5457333503,4209453571,106997318,
  5877694924,10365782548,10790276002,5049805338,5466000247,16826562213,23370603459,19649915729,
  4405609517,18414735320,39887739326,48514548432,35542233422,731935306,46443885921,87143354935,
  99778331875,69613286585,3171604380,98887607412,181347502862,209642886156,154272873338,13171997926,
  179725668669,359034744039,446322802267,377388000015,133120825617,242582341504,642770728668,
  920712136358,935272636706,603566493496,54995232203,899493888667,1686629949617,2128324568371,
  1976469079707,1112490718697,383077954298,2211072819692,3894311030352,4879232021978,4680637834144,
  3033776060940,14732327606,3907804032311,7914308783063,10972202587821,12049293022093,
  10361575084819,5604570682829,1890625335972,11114061442734,20470072656916,28002767982090,
  31719238246422,29957646289722,21737025290728,7024672720074,13129743555977,36619866940051,
  60468912565333,81155484789989,95026534355367,98741792526795,89687324094885,66301116457539,
  28270827703637,23415095127568,86562841750628,157996865040914,233873807216538,310045693463848,
  382428895197522,447336232013316,501741440479770,543459911228502,571232942658768,584723492941362,
  584435342296802,571574573813172,547874746798278,515408032231610,476402211808340,433075981019210,
  387504974896422,341524108526780,296664731790654,254125315737920,214772721269296,179163182954466,
  147579909643462,120079272655544,96541066159414,76716347145634,60271322887796,46826318714476,
  35985573073206,27359920146540,20584201486240,15327466254830,11297811148870,8244518861080,
  5957371207610,4262930730304,3021128165018,2120422038864,1474179125420,1015188143910,692179779084,
  467342006476,312506095740,206689527844,135030275618,87132656536,55413582326,34464178394,
  20766029422,12044850614,6604149020,3153314350,992787352,213617152]
private def rkmC_w64_m2_s7b_2 : List ℤ := rkmMapZZ [589725024,905777284,441678752,493119527,
  1700695933,2208619891,1311571417,791489648,3421153748,4820102970,3626938896,86247229,5305576347,
  9128191129,8884347785,3399856375,5943824416,15335125634,19109072218,13318831064,1735455633,
  21182998799,35748904301,35913574125,17277599093,16753371358,53366126852,74690123612,65075857652,
  19740634720,50380317669,118572432763,151181392651,122092683855,25960568081,113011614264,
  243972511334,305723711364,249856791704,65885185338,204446529701,471056541707,621130439067,
  558356603471,246607548033,260199162342,818128937048,1225114397562,1282755931280,871329555786,
  11733341508,1109448520477,2165650711373,2770607467741,2594621035331,1485400476441,444154340042,
  2792011961646,4930097730340,6145394727404,5830480248004,3680668239032,160206602125,5050523481141,
  9923740498635,13482127915015,14479101380071,12030806420131,5888497977265,3395173793794,
  14452771756106,25261850851618,33455297471034,36735699339156,33321366377584,22339891775132,
  4098521503796,19821275266797,46667322900919,72805493428161,94150035089037,106670559547313,
  106902615290697,92386552084441,61977824817631,15993092370931,43818669345796,114468843569458,
  192045735359798,272111081160512,350123879557492,421838714914590,483639298864784,532778942648378,
  567514711906914,587135002924722,591893220164832,582869724173204,561784870874892,530788462895264,
  492251493711696,448576433348146,402039169208968,354670367346538,308179839531910,263917048173202,
  222866697457150,185670540162868,152667068345270,123942174622152,99383486258342,78734920852962,
  61646167705862,47713935006906,36516414001086,27639802315816,20695676825072,15332071463846,
  11240121411768,8155807151608,5858035367240,4165470525380,2932464017440,2044213273886,
  1411022317324,964469033772,652537501286,437040862514,289861178672,190030283548,122890743780,
  78437654542,49332558396,30265474144,17844827502,9986815048,5199268306,2338180872,698896550]
private def rkmC_w64_m2_s7b_3 : List ℤ := rkmMapZZ [530771405,654983255,298496147,862939334,
  1987796748,2122169376,927057602,1357849051,3651202549,4324539057,2269324735,1870627010,6467765146,
  8645457412,6069223328,1071808285,9982559757,16052127587,14331990599,3690993107,12519370820,
  26991829936,30875974982,18367321310,8555682559,39411024073,58986689061,52734103913,16110721127,
  40487336172,93884579632,115557799700,84594126608,1308174536,108654764367,199154012285,
  220304583931,141563182691,28646093738,237276323022,399503392370,427854791444,271473001392,
  52688185537,450985964965,772837766247,860689424177,613218130669,39480822787,718708508256,
  1410311472576,1747387585088,1505216504632,620047506212,751633663731,2239629847701,3343654031357,
  3577774738673,2635862706699,531430064245,2340329940174,5250264373426,7291875069320,7619128415346,
  5707753487270,1566339704724,4166145261891,10278143309931,15201843186921,17353980576109,
  15526939487681,9242951988501,1015697972288,13763705171954,26684758341026,36996869919260,
  41948397486326,39358224647450,28095544153560,8407537730784,17966032549951,47918348179907,
  77323619274337,101551372911041,116065990354993,117019567267283,101752334841821,69132193202147,
  19694346629753,44425199895440,119739415106016,201800691624618,285668224011558,366391419325620,
  439451228634742,501115902472850,548679958204396,580577400209522,596377334381444,596676977401596,
  582920331486630,557173822128040,521886561487248,479661160449692,433053892963284,384416322783274,
  335784791398084,288815986859126,244763405624924,204488916649854,168499787443984,137000536125898,
  109952696998646,87136804144120,68210166071104,52756533884580,40327204735504,30473311565504,
  22768870582788,16824988485098,12298235918158,8893371785964,6363609567182,4506195644696,
  3158161035046,2190901521988,1504317381834,1022333182586,687868907226,458085313056,301590960224,
  196189958728,126147976726,80053036716,49830324594,30135087270,17534894866,9702354348,4962337392,
  2161791000,620802530]
private def rkmC_w64_m2_s7b_4 : List ℤ := rkmMapZZ [231328613,177315672,578277396,290112626,
  422186647,1520203289,2168999355,1436072747,633492610,3054613100,4339555888,3160958174,777007969,
  5294714141,7816181323,6111994133,280708286,8675429146,14171557972,12790219200,2997832546,
  12022528669,24457909341,26077694301,12554982097,12751769338,38631059688,50116013282,36350414308,
  2336561805,51987836091,88112710451,86538741269,37575394277,46648596100,131692074700,172940580312,
  136387137172,18714541128,143836431325,282559000319,321874647269,214898325071,27676028846,
  328183863270,561605130494,601323197724,376418271028,83585117211,638669707727,1071839161363,
  1163834288775,785572039193,29414514324,1061719199626,1951493915610,2308952140024,1858112017202,
  564370544432,1300524424301,3193228884679,4435751505523,4425352397333,2855252064693,124098360684,
  3864017455036,7329734732566,9350771643066,8952644357360,5682361697324,166256344075,7504216332183,
  14611084201569,19487766781161,20328636676487,16007545018125,6456734388561,7159273131252,
  22529411719600,36543533432788,45843724667108,47475227417194,39511614667364,21532151667164,
  5142078690017,37501148683769,71182304504841,101031854713751,121797597518683,128842387401871,
  118767208061087,89856086375667,42286893050661,21903528512966,99080922090224,184448667055276,
  272583339786990,357995670975336,435646041284832,501360493578800,552111381052250,586149452000634,
  602997278713674,603325149184946,588740373381514,561528194092620,524378661142886,480127811740540,
  431535682485922,381114102499044,331009069256302,282937010869286,238167987503592,197545275133772,
  161531472815492,130271464303758,103661896357276,81419133081382,63141488916530,48363087428150,
  36596940887420,27366532679302,20227384617576,14780595139938,10679632184824,7631541038230,
  5394284640884,3772032122570,2609547665748,1786163494374,1209679320670,810654348346,537494800146,
  352447726566,228359456834,146016799512,91986881840,56945610318,34467224646,20185701974,
  11206077574,5665346026,2392820286,659371898]
private def rkmC_w64_m2_s7b_5 : List ℤ := rkmMapZZ [399353495,832094809,868362529,75133864,
  1380514894,1967854538,1201970786,1001900977,3561652233,4329674109,2428378707,1591545178,
  6008252896,7723217636,4610257302,2601824599,10347153641,13636882573,8945111705,3325597524,
  17245029616,24465941716,18487923502,1112410193,26267274283,42594935945,37906945477,8797551361,
  34705491410,70620831928,75629684532,38048974660,32719628053,106085586715,141274703667,
  107695508643,4754167651,130923152058,235369459944,244146316812,126279155820,91500460233,
  324466291077,458726866857,400242097631,125975888515,287417577716,677775010934,853906078496,
  676757192066,135973108826,616431903467,1298020964575,1590072711693,1266004225147,308433984921,
  1039341167110,2317370932090,2988737572232,2634907504734,1142733275524,1190525510843,3686445409347,
  5458332630511,5688634280603,3928479332005,322146955555,4331050764968,8720643973168,11352834376134,
  10985379025338,7050792216442,60779922277,8956240509163,17469854605841,23133613716625,
  23786134568265,18175709453059,6403499107461,9912744575138,27810553701212,43474036532316,
  52954428340322,52974645866954,41655765647306,19020044927752,12831308317371,49901860086767,
  86811244883415,117542075570141,136292487769739,138292809586435,120460424817589,81801794207391,
  23517542668455,51182325475774,137502727428800,229648865484840,321480483263210,407143398984812,
  481602495715508,541025935299108,582997069465506,606554843940450,612084963927158,601099462565350,
  575948349062804,539505346378756,494864218044808,445074217091098,392932782666184,340842621509906,
  290731559679582,244027919046756,201680656598572,164211458781080,131785789111486,104291624074642,
  81417328412854,62722704323708,47699372501470,35818557935574,26566139114094,19466181340218,
  14094858443952,10086780816432,7135620266682,4990773661812,3451635101542,2360769566942,
  1596905059428,1068288815610,706686531398,462160041880,298686698836,190624322452,119959512136,
  74220970290,44915700506,26358512430,14798519842,7779085328,3687280140,1455412164,377721870]
private def rkmC_w64_m2_s7b_6 : List ℤ := rkmMapZZ [490219504,771560780,121054730,1137232335,
  2209602633,2268263595,602963711,2191515500,4039094448,3387986228,35142097,4835516091,7830193581,
  6157415395,339019706,8508946990,13196151958,10192100726,1019478255,14974679413,22856541737,
  17697763923,853919438,24758512730,39415937748,32772275052,3222134686,37285046829,66274098979,
  62098006967,17989947349,49991073766,107439002956,116805290018,58965115510,50320914485,
  161487550785,211034144431,154002024815,6291941708,208352809022,351693950370,342604471048,
  145954425494,183210275447,506708801633,655028771103,507003195825,61375837021,535913659514,
  1029943833422,1154980991076,758247230508,103654260287,1146278598369,1938104839957,2061101350473,
  1297070134917,236192061756,2067057868584,3495777977964,3834802235658,2687843531946,163467199842,
  3070774758269,5936535710157,7268813049177,6224282902865,2640244133319,2787856024446,8593903453590,
  12897363876260,13944743771562,10685930585304,3211730941088,7093554955149,17758433414735,
  25764276045831,28298147119327,23533753788845,11239431556991,6953715366604,27711394974472,
  46568183786492,58799498839688,60412606287184,49048328366440,24603921779922,10551033890251,
  51807209817341,92949134596353,127069170645403,147595085760539,149253110684323,128812510693885,
  85508055022069,21098975550733,60415460766596,153352180215242,251067061930774,346727475356848,
  434027122295210,507759696149166,564199713573442,601272840634120,618528975073322,616954693705578,
  598674915980020,566597130807930,524047451690948,474438499406440,420996789695100,366564108173072,
  313475469901330,263507221439248,217883092108604,177323166060230,142120238941746,112229335100582,
  87358770479976,67054394124266,50771848809680,37934394188564,27975882456424,20369921563964,
  14647195675398,10403388956160,7300224621608,5061884203430,3468658546112,2349236761052,
  1572660180292,1040609862208,680564260428,439750356378,280680918910,176553189138,109412883488,
  66474481354,39301601258,22592263026,12567770450,6585305406,3082051014,1178485726,292240530]
private def rkmC_w64_m2_s7b_7 : List ℤ := rkmMapZZ [525770799,1051214189,554514137,855652604,
  2111800682,2271363346,531921208,2568749005,4669688037,3940192111,151893911,4963402962,7822423512,
  5447404466,1987389393,10340495793,13637026535,8111921631,4914408526,18245226144,22196871896,
  11445085194,10505307413,31708622177,37175600235,18471044459,18410677144,53496406140,62861070766,
  33286102262,26723806549,86554473925,107302570147,65163259907,30007509824,133224329764,
  182761388486,133502759896,10789122829,188277504867,302478186591,269821394999,70853359185,
  223001277636,469069805964,517209978044,290473488832,156633622399,637704989757,904212227199,
  762303752741,184818376289,639085663084,1352803828448,1573362563546,1072779799528,79835320273,
  1489828850695,2555257358213,2701627504621,1646346068907,418409475492,2816878589598,4586884898224,
  4831310533714,3100959942236,340941329277,4493530198927,7876156174363,9009861941943,6971054920769,
  1823732245943,5238013735788,12120886145984,16401540056128,16081805936416,10303116266516,
  210450845565,13141971861789,25045777023193,32190686891653,31572625740405,21828982411043,
  3803897004681,19401369416928,42931387057406,61135157391214,68771785039758,62196240932984,
  40265361081660,4771181348598,39685167207775,86347478774213,127350630515807,154953919654565,
  162734423180923,146537950621423,105045865685541,39895820230851,44624345272152,142222516218804,
  245457315409942,346656095685318,438761483594042,516002597173414,574329845173156,611593984216244,
  627491185514814,623319631810116,601614135319406,565721367849316,519378463815532,466338276686274,
  410071953539524,353563340864048,299192834803946,248702115874394,203222265968396,163344954946650,
  129219729915370,100660673436086,77249189341878,58425931885084,43566500585966,32039119634484,
  23244213736392,16640871670292,11758854161998,8203183530378,5650775819552,3844054698512,
  2582908697096,1714495236656,1124166619782,727959791994,465433738904,293561420186,182430517770,
  111418905880,66962559128,39258576710,22351413560,12310799744,6358445840,2895283624,1059905706,
  249438848]
private def rkmC_w64_m2_s7b_8 : List ℤ := rkmMapZZ [200393250,235081711,420251741,19238846,
  710840696,1022395684,246333066,1449290075,2690556149,2067097991,542141110,3648068118,4917258100,
  2539132500,2889895721,7670957491,7705714333,1892369543,7013206614,13158620544,10660688668,
  1061585619,15376825107,22363398305,14830644717,5994273488,28338556470,35920175706,19300919644,
  16027011217,50032651259,58126437291,27356760469,31274091664,84624851696,94728535250,43134132576,
  51908878883,138462095861,156947343493,77352293615,74212997904,219080489096,263569254896,
  153909096094,81221760971,328926730739,441377715305,316978400551,29234877986,448849829060,
  716162929358,639916457652,179205654946,501085468197,1077541839657,1210389270725,721696803549,
  276780660900,1381717599538,2046279994480,1828583848496,632881111452,1175291024191,2855336449627,
  3571371615359,2766024050001,470184910885,2601525846446,5242951546754,6193701772118,4669876002642,
  778620164348,4370597017225,8942985298259,10982981755777,9152305007805,3338386208623,5107297029702,
  13628757092528,19184906115326,19225884312110,12622943446046,240944699694,15058235901629,
  29031567952655,37147768432939,35871875112979,23783874115191,2214384647935,24797280899260,
  51240858486402,70405924046310,76393488901238,65516705711526,37273384644930,5319976506157,
  56096637538439,106719040393579,148057096608473,171688660539905,171238471297519,143330888412979,
  88021206266883,8680660283255,88596022291868,195913480282158,304654530615842,406535087496820,
  494487815989346,563279872116304,609822263229752,633183524409536,634358590242130,615867551125868,
  581267003089550,534649975147596,480193204858910,421795926194984,362824660522916,305968525846658,
  253191114474996,205760496586260,164332237957730,129061762008346,99729100408762,75858978532448,
  56825107854022,41936366902626,30500650420850,21869323117494,15462669749512,10783729147044,
  7419869579180,5037820316944,3375883251980,2232999662750,1457967590526,939393647542,597350691690,
  374491308688,231353540696,140744649572,84071310686,49183082594,28088423500,15487364232,7980274366,
  3862069962,1492650622,350026236]
private def rkmC_w64_m2_s7b_9 : List ℤ := rkmMapZZ [265472734,578114492,367389790,727290231,
  1608889847,1037839321,755205420,2522004388,2666059712,195606896,3592415501,5517411423,3338871025,
  2237319960,7642228220,8328053212,2220557004,7591282991,14014367993,10851368577,1957623616,
  16768127472,22292999698,11510869920,11615496337,32278890561,33719007283,9737108011,28202975806,
  55232488468,47998966510,2565566006,57442710991,91636894133,68443976343,10429304578,103349157432,
  148084888980,100495578336,29986663031,174383131605,237719636131,156773440773,50763013964,
  279111518388,383448176806,265265340222,54177826489,421341037313,617310819135,478697430865,
  9615967253,584197695234,976036015746,885525250340,252011737628,685998991923,1463942805837,
  1606085495859,886108956269,498931567568,1951420203286,2711973230322,2224288482622,460721447782,
  1963821261237,3977812572119,4494885448417,2935863480547,405473823054,4343644914100,7187498898294,
  7413262468376,4365093832118,1313868504883,7740036795649,12369801972415,12929226519929,
  8361245887797,574399620888,11316071200282,20184623414000,23554798858166,19143795226224,
  6979658883112,10298766614873,27961236325505,40417139978973,42822410338611,32602222923771,
  10442853893023,19552977949248,50616584778370,74801184851796,84839521549508,75920836222674,
  46963699523324,1095757935884,54750031877007,111012538224963,157180460681727,183612600200499,
  183143161979725,152187598314939,91195840822891,4430750122803,100818029412202,215392192353278,
  329564739089664,434265227604066,522058735286796,587774081731562,628756131713234,644771838896014,
  637648931530202,610746616544286,568362085350310,515156462144006,455668446067046,393950650866858,
  333338952800674,276350072006516,224682597296378,179294265779958,140525453948450,108244037809308,
  81987733866496,61094112324984,44806726873600,32355351064346,23012115601488,16125615245192,
  11136240975724,7581241572908,5088728472982,3368274207152,2198799379220,1415583229428,898562986338,
  562429602922,346795085022,210568000344,125771685138,73639078502,42243574220,23424374264,
  12551854306,6270888608,2696974416,904033528]
private def rkmC_w64_m2_s7b_10 : List ℤ := rkmMapZZ [225635134,172534670,521754441,982689033,
  324925979,1161461132,2099854794,1301698666,1054028311,3243465299,3040087587,254886962,4452626170,
  5827079734,2303465944,4452266207,9520616551,7820611359,1268685690,11780743924,14904903440,
  6157442332,10222477895,22617041075,19513789155,940098946,26195426282,36640674258,19794887980,
  17711273677,51475403033,53315832351,13313811661,47984948336,87926162848,70083025494,6588202729,
  98942704497,140979460419,88238860071,44162690850,178476556866,217124109002,108622208804,
  105868448435,300359576523,333069758433,141736806669,196278157020,485430711472,519106318984,
  213742788686,309489754347,760226268455,829905358779,384883638203,413403015818,1148279986122,
  1351810781730,778554875784,403773430547,1630531353223,2192140436237,1614781331089,25439338556,
  2040455237224,3394359794682,3202596001474,1232143500588,1855621437455,4687493433117,5753038282513,
  4138938176851,83616157687,4941832027338,8726113186106,9228769111816,5544784256324,1505869581473,
  9465559240731,15046448897173,15392827888435,9327291458279,1927617803888,14886989421268,
  24828141557546,27396286116172,20247348228992,4143881541216,16919289281785,36665290651813,
  48318001467121,46688828074275,29935823287485,452182393627,35404492651864,68699099407810,
  90061951330524,92030220587010,70997826113996,28295051507930,29837067670341,93339368528621,
  150210468533965,188728966032853,199542672326589,177225727004609,121049681374431,34902671122255,
  73535663608442,194132601755692,315865314649046,428319272392986,522901003162324,593623509251750,
  637423206320518,654050530872480,645631705078038,616028640211702,570128040903060,513164472944376,
  450158533905544,385509925174070,322754588544488,264474457766418,212324243481480,167143487088728,
  129114055715938,97933347701064,72980644012190,53458890777516,38509062581950,27290338216052,
  19033184684376,13068137185042,8835387173922,5883867041784,3859955254214,2494823229306,
  1588807448076,996750968558,616063721420,374779458924,224361833358,132016560798,76136795020,
  43012840354,23436660750,12232438834,5853877176,2374633462,744409834]
private def rkmC_w64_m2_s7b_11 : List ℤ := rkmMapZZ [507397261,646996075,264039668,1338430846,
  1294828840,277317345,2043504165,2393726183,430247125,2894974634,4451256270,2026132176,3175204135,
  6693754603,4854691909,2152460942,9431710792,10066097018,1430090040,11000124109,16921826515,
  9222756525,8583199272,23695390188,21716253062,137370575,27855679911,38652519893,18857705095,
  22405645126,55616824884,50460152962,1197495342,62415061311,90843353397,51943322179,39456028874,
  122504178730,128366377988,33047248452,113217889637,208417220879,165557431695,15688348366,
  230700372908,325114591948,198996993562,106693898087,409937390217,489097695149,234163152425,
  250930241108,677165139324,732631548042,293536173486,453455950505,1072634252531,1120153790205,
  435331992555,698268008366,1647776422770,1765859778278,793926860978,902062833491,2437529173181,
  2845472508811,1637948731797,819253501690,3362198294134,4549824030972,3424712885364,128058068452,
  3985332083595,6864745808225,6727336407673,3028526877265,3057443017816,8943979772900,
  11677030620058,9301894730382,1942116243774,7941082954881,16314134044487,19132993706257,
  14098988467057,1880677099935,13754677188388,27049275108548,32267779984280,25904103424060,
  8270078703988,16161969095165,39859944658201,54473078707753,53517154935543,34646003858351,
  775178038063,40313835088366,77805074362974,100605556714472,100269014645014,73310291376522,
  22322168912966,44343304617313,114200706778299,173124142911237,208100419759421,209638466907835,
  173362717842401,100555539917147,2346132533540,125079292626832,255361698354734,380795873210848,
  490529950665232,576448728339722,633784438958734,661164330112660,660199076408856,634766726913050,
  590164127271840,532269562754126,466831219001190,398940725127992,332712211161182,271152996532036,
  216185486353708,168777844306750,129131866811324,96891554771876,71341353738678,51574338395356,
  36624704446476,25559054234296,17535218117686,11830720019070,7851863945130,5127251551420,
  3294813392404,2083781291682,1296841293848,794340433524,478623204178,283621016106,165038266638,
  94235668794,52449366424,28365715674,14623307126,7105234390,2936724436,910593148]
private def rkmC_w64_m2_s7b_12 : List ℤ := rkmMapZZ [339618027,495111883,121236717,745837952,
  1121321234,13628660,1647431109,2000711377,248554967,2288745334,3349761746,1092545498,3114162923,
  5413001011,2664670485,3644616552,8075488008,5739045856,2855490609,11309049159,10845465011,
  460142766,14504944144,18551006752,5992755326,15465959787,28227004369,18129451189,11718482458,
  38448316696,36676589820,611587894,45425623759,62560436669,28022213187,40548362080,90967843866,
  74441397232,11506010211,109440983591,138400060971,56767894139,93331250060,202917224154,
  170882292136,10493307403,228601017283,315259043087,169791460667,146503964074,424322537398,
  437347201532,114138582080,375071686155,696348265607,569583740239,12904137768,724306175514,
  1074127511174,728979852006,219226168181,1234168670447,1620600159313,973870090679,489114704420,
  1957940022676,2454581197568,1443253909614,739316128895,2940677994009,3770596642553,2423019571561,
  724856856764,4133201226340,5815070330872,4425383403398,147872685926,5154556109957,8704242811319,
  8187184740513,3080517912405,4787466875668,11823475510166,14239163789742,9924666646836,
  264714046515,12488668642967,21311182112323,21988503948945,12707740086765,4222257730464,
  22829590399260,35524024058470,36006561852132,21932484960132,3723276517281,33196408725939,
  56257681610425,63580207317065,50020508739757,16701239539933,28807516266154,74299591140722,
  106195454967318,113295702800026,89955368223854,37821822278682,34270530933237,112146465883701,
  179326586547061,220462048606475,224355956800361,185945590573353,106936821522147,4888591118876,
  137383460089440,276300653923334,407609419518208,519443614138044,603407327054944,655140176023420,
  674195711950680,663396021892320,627878257484808,574044026389316,508592529151494,437748855747648,
  366746806681254,299564131506666,238875609369244,186163853819420,141929376389300,105938903202384,
  77473224593750,55542584217760,39058423044884,26953818204444,18261038858924,12150097504756,
  7941836315986,5100797361678,3219760861330,1997555103984,1218227881542,730102489534,429947590926,
  248475278368,140862001584,78036747926,42137810664,21834440680,10712655306,4681105466,1722274170,
  342280160]
private def rkmC_w64_m2_s7b_13 : List ℤ := rkmMapZZ [271341231,433719591,43640793,640889814,
  925447928,122941055,1494126239,1699478059,214931268,2425744304,2422553926,350433105,3678277235,
  4034128271,117802623,5300704698,6359324624,822289802,7191494029,9762300901,2895689139,8941147176,
  14856062474,7109005506,10112407577,21738456981,14335853827,9463883342,30232220580,26474238254,
  4211080561,38841798325,44416223029,8247392541,45186280778,68756580264,32743487868,43496935377,
  98359440011,75371225937,23442514040,125338944342,138176474230,28751897130,133788195507,
  216815931449,127953927937,94812671158,289255093430,280501364826,28390435882,308650870495,
  466105774059,271433579091,194670159158,610876083618,627380485610,141334442386,571765810697,
  998057206799,740657460029,151444917688,1132622757266,1476931781966,788389021014,643923585345,
  1926426771357,2095495835123,793743839737,1364608077434,3044841277694,2983537541830,861786756586,
  2311377477313,4636616070873,4412439060141,1268513857953,3371857172640,6883832376908,6862687760598,
  2624731760640,4105946908243,9828413652965,11014151851565,6112992857383,3278151709330,
  12818931004342,17361823365994,13556396299262,1843065164284,13241142039417,24758572427053,
  26422916270905,15673983838343,4660325881844,26976187427084,41678774556874,41077404775190,
  22820396471084,8568225520229,42758775071437,66993642108483,70587970252587,48944945555393,
  5657942943363,48050578938546,96381330021116,123527824154288,118335699470414,77673353458140,
  7591617502378,77946896426287,160299318959687,220376083084339,242762654250761,218761304709317,
  147777211766055,36935614216549,100756425302368,249123171489092,391732064215454,514418017660818,
  607018881194294,664165336405688,685178096994502,673286310634378,634446308877794,576048042579448,
  505735280464386,430491278911930,356048979985350,286621539479242,224893736314176,172198768298524,
  128795604075610,94180722059256,67380153092850,47194180109696,32379591192212,21771352689658,
  14352015588940,9278809072552,5885242483676,3662753869452,2237103538994,1340895849162,788792205432,
  455150806662,257388916298,142570289896,76939726336,40357075142,20254153174,9506637182,4009006362,
  1208107460,206781220]
private def rkmC_w64_m2_s7b_14 : List ℤ := rkmMapZZ [238522825,250661936,785117548,503675060,
  753645717,1630101065,1012685015,1160889290,2573509160,1204089350,2224366883,3994120341,1546193869,
  3350116966,5684874720,2167810796,4970588617,8557484269,3580663027,6907798420,12418472524,
  5640918886,9157355595,18031659953,9799670369,11441883374,25936628368,16458945870,12901739573,
  36409480133,27608155973,12398633602,49522869554,45188991118,6438102485,64732126149,71570617525,
  7878540041,79599089048,109466199876,38201970210,88030523745,159642161227,93987740899,77962811026,
  217035800628,183880923868,30511297565,267657833443,313295478037,81398473275,279469852398,
  472257942744,285999676308,198834840943,620925987403,597243286159,49476314749,666368502368,
  977526359166,533422756842,458256832399,1294245103617,1256052262505,187923766793,1270107023628,
  2040986453010,1374016031472,511714719643,2417501018573,2897472882137,1297507590667,1617150536756,
  3972848346126,3947610243016,1081848069802,3164842379551,6103077431719,5452490869843,951722985385,
  5137329395490,9107023039102,7971894854856,1482686578310,7291802432445,13349635600761,
  12493867234779,3952144069165,8672833330928,18843335392824,20355207365614,10808272734070,
  6580456268163,23937604623715,32208451400431,25594587226271,4821427791265,22431697844446,
  44340776070092,49892624422096,33886038644322,210962329131,40857334465737,72383011480421,
  80805616618811,59310174932487,11321307901253,49969495022548,105462318650118,136052059386892,
  128612480702096,80172270841794,906797678531,96941424138869,185356776996873,244157775636933,
  256925591967647,216140905130815,124223703571385,7657004441630,162422203934970,320702832626856,
  464353102478300,579171304984774,656446863372552,693288936601788,691938757631064,658427210094350,
  600966886136826,528417291919064,449053406748084,369748601899328,295577800469260,229772566706214,
  173927379471026,128341568586744,92407387937106,64973543949112,44643075755308,29992856173586,
  19712531920114,12679856874744,7985214897828,4924609871068,2974845242194,1760424986044,
  1020342746278,579294922946,321785677938,174651376052,92456962798,47415396754,23295564766,
  10778230746,4416256698,1252395322]
private def rkmC_w64_m2_s7b_15 : List ℤ := rkmMapZZ [217473947,299744505,342596828,744188602,
  61864265,1427359249,1272892841,771310246,2414609236,1691421388,1379212017,3795406597,2044326739,
  2691762390,5192841842,2168672222,4676371733,7726729843,2237799111,7122297686,10842005580,
  2534406088,11106280439,15492958397,2963562469,16311068312,21593812664,3669492152,23252946537,
  30815597001,5687912291,32309804636,43906193352,9645893490,43740019325,62608421713,17730186433,
  57281540806,89024782642,33186213924,71549565319,125783305633,60815331397,83721357314,175965195658,
  108756880304,85987525643,239535980481,187287595619,65058505882,311922483054,307561198058,17092426,
  379081506061,478664059895,141413087337,407727031366,696586842480,397808701102,338582372303,
  928822933761,802283904983,79504873156,1086042407372,1348428785234,479137943782,1000425074953,
  1938242650493,1419700651499,416244880864,2300076563854,2678387736638,935050650998,1942113934341,
  3870458727667,3129478174847,228791201842,4117477528146,5662634018936,3239014367756,2113717629771,
  7016796524337,7821244726939,3169950721939,4682788925418,10871810065334,10841965630496,
  3459889633566,7723742362943,16093766600157,15759938251933,5363035685699,10449158199602,
  23011209693984,24246862273842,11452767712610,10463976157289,30763048169485,38018650282089,
  26135451513287,1852840257276,34293372749416,55743574154606,54017237802674,26227299193582,
  19001740964775,64281394364925,90132500164453,82865390034373,40481608429083,25746266523842,
  94608988960166,141933477881184,148652070700594,107184722739458,24116253619516,81472544686175,
  183219301255245,254438950320115,274711199560069,234366272407253,135959372602043,7228524410260,
  174857401226704,344165481879924,494364955568852,609896065336704,682092288896320,709266979513470,
  695569158169296,649125006581082,579991057286018,498336741499746,413103985008290,331233789971416,
  257409326546706,194194159064476,142413922958824,101638109849932,70656661074008,47883314174374,
  31654624293690,20424575324070,12868560758124,7920305916082,4763119240352,2799485867960,
  1608270185836,902804446802,494988218478,264940290620,138151401010,69829774708,33928543948,
  15585987168,6478065292,2143042230,344607746]
private def rkmC_w64_m2_s7b_16 : List ℤ := rkmMapZZ [310593073,334354185,564327580,963162718,
  209463150,1271855497,1375528155,398641798,2381279766,1561973588,1813001677,3759945121,1499373189,
  3324108742,5107810294,979633580,5709579151,6770903393,682679948,9198766780,8340941354,3480183145,
  14018686501,10054692829,7443542856,20272710920,11451582344,13638448707,28819884491,12867391081,
  22475605370,39854006066,13837254218,34997434501,54747219037,15213812197,51717594516,74866456858,
  17200448672,74209921373,102749913951,21493419365,103376200092,141674496208,31119670586,
  140144028325,197023990131,51303213417,184620539272,275658236900,91560633294,232732775581,
  384593742561,166214225271,275736715410,531274252936,296813181614,294382640799,718892273349,
  513371467521,251483790660,935836289934,849466089542,85713570629,1142197327837,1331894611773,
  294514107987,1244701480316,1950668834702,999607268148,1072647283021,2610456486181,2122801152749,
  360732973628,3047986541444,3635138843594,1202646269452,2763930495895,5214904535451,3812250083787,
  1028743027812,6021461758506,7176842598932,2851500387116,4591815445579,9974562982419,8805449478699,
  756006483001,9462387249818,14776356614128,10474048498948,2123251826077,15714127080875,
  21158856036291,13357927523897,4836901180388,23405900660662,30580334911222,19938503637982,
  5013274286703,31718626028161,44817983678433,34576158436353,2929274275931,36300191249382,
  63468052819740,62627773138384,29860455060124,23724926865073,75917700578633,102617414162759,
  88294663364665,33175667290459,45860681410092,120979987705054,163337574020604,153409711056024,
  87965337335688,18566752732165,138416216498275,238642992930663,290288160032231,275691837199793,
  192125048071455,51244127424679,124857549771766,309436477099556,476984791764986,607809704127736,
  690543090994766,722493772494580,708284506253994,657483657421158,581974044632928,493638924261994,
  402704913818506,316845245445406,240957357804978,177429228569872,126683031540464,87806486089752,
  59138060941618,38733257266992,24686709153658,15319329016526,9259699159308,5453403328086,
  3129975312846,1750849745230,954377903256,506665307516,261679391832,131178120990,63485796246,
  29305541236,12579776900,4767777612,1409427222,202107180]
private def rkmC_w64_m2_s7b_17 : List ℤ := rkmMapZZ [367945615,469811784,1168793032,377519942,
  1293490229,1566809721,417864854,2319261484,1707783222,1671623421,3559402307,1051259033,3866350162,
  4802378926,593899731,6713529291,5446322467,3450041704,9835492424,4715807804,8116594897,
  13473714067,2399376331,14934998394,17071257548,2492141947,24001590707,19826257979,10741446206,
  35193644472,20777141912,23577037159,49244196565,19298441197,41984790202,65838009582,13734454280,
  67584343139,85687707097,3711638083,101964215170,109564358188,12578897099,148233495821,
  139633813649,35907352436,209704134390,178834837304,66729467119,291370954931,233240447231,
  103800909726,399503536496,312724200860,142823338161,541227037083,431541965925,174851491616,
  724588153116,612678896900,180398250267,954046718551,888117527581,122528604490,1223009398044,
  1297516436746,60333440864,1501050873483,1882228325701,465883280323,1708715736488,2662760967860,
  1228931127622,1685500400309,3596107864797,2505787599463,1150141484672,4489433639580,4398260040150,
  304127878786,4890620599933,6798389086311,3133876139393,3976681223554,9102674577352,7556472936216,
  598738646105,9868646250141,12942450254281,6248552685353,6686685509078,16930394121512,
  16175744403102,3063346010076,14846597438315,25339085260105,19631832354069,1018165316620,
  24879512354032,36331867591880,25713399009616,3701723971423,36253715482921,52185750148517,
  39152194364659,311768915933,45885094158520,74528850641954,67232654769822,22474805958930,
  42170010847869,97250124703179,114737916961805,81165764762973,4568386832307,87791440575494,
  159776831782106,180316444372106,135273077676476,32837085636972,99095924035423,222003128265847,
  298612475903307,303442038254253,228903566398557,85775761088587,101218169566272,300678037439050,
  482186960229686,622336652756260,707993653548080,736674025905546,714659323609214,653865015879586,
  568478223510546,472131528876596,376018793390774,288019131723302,212658582446380,151625703272890,
  104547804632322,69793201187616,45151783604266,28328779506876,17247717292278,10194996991856,
  5852348551322,3263253676184,1767300875548,929583063128,474495755696,234532616476,111984704758,
  51197307330,22239871744,8774412886,2837012046,596909734]
private def rkmC_w64_m2_s7b_18 : List ℤ := rkmMapZZ [468809411,482752735,522294554,1136892632,
  246588260,1516875275,1482896169,796745308,2893893680,1291993738,2516908611,3603768417,503141138,
  4996918892,3499331360,3487981923,7260789995,1721238455,7938263734,8854318150,2370397405,
  13239886069,8113846191,9563418348,18288450984,3680870614,19774378315,22094408881,5451182226,
  32372318094,22066658974,20717197329,45908257839,15727720983,42643827032,58234609886,643258726,
  71582882009,67140897995,25642276142,106917990166,69035659780,66378607699,148294501797,60439422701,
  123882706992,194228388716,37205812678,201841059999,244671103057,4259619906,303830446052,
  299932225666,68152030035,435885651613,362860750415,157772244106,605840870022,439803392032,
  275460296101,825549294081,542983131615,421482566554,1112864895134,695590030702,589504875667,
  1490094028549,935034079627,760617034000,1982745501460,1319959441938,892231657671,2613516167489,
  1937781478595,897704590752,3382644247798,2904430137588,620806378269,4231901558587,4350499015723,
  199345291799,4973581736092,6363594828414,1939037308700,5193562962515,8864893385487,5049366755271,
  4129900801228,11359642831856,9846357418514,640019202033,12585794590993,16013579903281,
  6534688408343,10203592161954,21721552143240,17814247104218,1040577475117,22618463130201,
  30773221128683,17100229105397,11858624982862,37507836787702,40979083164488,16266190475626,
  24187090750117,55735681807361,56304167483219,20731375390159,34309645583720,78294068193684,
  83551614926054,41359059527198,31643309540105,100438862168925,128534398503589,96185315993767,
  10924771574363,94542295419246,175827429126526,195365103377966,137825072900662,16311428544084,
  132412770459005,260916529654439,326776637785659,305201113669487,194826521359185,15876935694689,
  197470345476806,407203916864324,580729581068182,696932481051320,748212459581686,738990852186484,
  681994911613336,593824800783648,491025754884664,387376858566272,292573206868378,212098137519166,
  147881977897974,99323597222038,64340924737206,40238261278446,24312630288226,14200506971364,
  8020729997572,4381981996654,2315463187942,1183060000626,583947390784,278082951934,127243868332,
  55653108188,22817228550,8504783674,2573437936,314741442]
private def rkmC_w64_m2_s7b_19 : List ℤ := rkmMapZZ [280554346,2626320,546922867,378920095,
  995035206,1401689790,271276063,2172912489,1108815641,2035386096,2929148130,569179461,4042164633,
  2426667067,3468126324,5621111812,178621535,7208609267,4907147473,5515418986,10511185982,
  1065725934,12234328819,10816469979,7087380064,19041649668,5989397300,19050758387,22279994751,
  6256846560,32741038994,18315618808,26014861525,43810725037,3717280939,51228093700,46721295136,
  24435272981,78113311929,35251441613,66435221644,99824029116,3354073636,119840776585,107602339701,
  53406268442,178605739014,91521203896,137667226311,234683315855,42025712589,248735842128,
  277071723756,50506667077,384379600815,294341039071,193587728094,539789746690,274449931456,
  394671162747,711415862099,207141065739,661253045032,897462042054,83088193288,1003454636229,
  1102138721887,104221320420,1436276161460,1339753882746,354966348133,1981798408579,1639857660907,
  661630926318,2672690649586,2056163326898,999815356037,3551515903385,2678245470167,1310637393572,
  4662806246348,3643806730638,1473633932819,6032618514655,5149719454393,1258516671972,7614110173908,
  7440676509226,267619991493,9188532493073,10752905826579,2129834202879,10183535439888,
  15130178872310,6780228250520,9435118031163,20042044032321,14510787236373,4985733325792,
  23718477815728,25383717632008,5720260770832,22353875671051,37127353021499,24489296743391,
  9957570096148,42867426532454,48847367194228,19179449363678,29944982031875,66302412319015,
  62467356695185,14993734630695,50973517055192,95328029980000,86928935268506,23373489010826,
  65352553992607,131742008858643,135925564688709,67399150236401,48083503691568,159636264164340,
  214357961541424,181047807648092,63795548534588,99684174174037,252936995747919,341587708007103,
  331473850919295,217870770169185,23984125533635,208920759248670,434990902645540,615955874378162,
  728699640458966,767205625449962,739823999388000,663898103969136,559907293343424,446727821641836,
  338770393281062,245008516321604,169423412466450,112231852854502,71324380165266,43532154505610,
  25537062897180,14406166372824,7817447880962,4080617801060,2048431574130,988279314098,457412904796,
  202752353432,85554480494,33869988366,12214352902,3674395230,644781452]
private def rkmC_w64_m2_s7b_20 : List ℤ := rkmMapZZ [629681156,207132752,949540889,984840553,
  841611196,1889429660,132791220,2492740011,1819209155,2171370260,3848988992,228378651,4905528967,
  2679506673,4467229726,6416706948,1524379953,8916957243,4061670193,8602820234,10722264922,
  3665042617,15965584491,6033161743,15918128260,18428924696,6939569585,27585113039,10339752273,
  26921752356,31803682302,10807510445,46985904617,20304541355,43533780082,56814965392,12020251381,
  78757781395,43667058887,64199305392,101523126526,2067898435,126122744201,93832987595,82029583066,
  178374172924,38953110368,187325692737,195550220705,72680980762,296417169736,150712121122,
  238342189723,378232896459,22402638509,440628389478,395715935972,200933225157,650242299113,
  312920948357,517314787790,827352966436,98385714588,912434527073,928924526005,269116065550,
  1361833888994,913513288280,802481907323,1839426312725,746973105297,1508990662682,2323860339880,
  405282643712,2396621588713,2808404229721,125066503208,3484104439358,3313663940192,842671865169,
  4810755691031,3901317919107,1725620379262,6444251607276,4693622127914,2715424365793,8484400632327,
  5902151703399,3677350361212,11047326962488,7860720219726,4331358421929,14215640675223,
  11059803194023,4126336055800,17898400790378,16120178403486,2073458393113,21554088274751,
  23630914572671,3421004278721,23688243128222,33624896973844,14492975409392,21169388865071,
  44407014805945,32996054613279,8771099913976,50564744822972,57958304696318,19694313915296,
  40937010806629,80440197728707,65837614265013,75900608764,77424855184618,113792618807680,
  78693006600858,14689239419431,114755849210925,160735235013551,118219157277873,162417791223,
  138204251539486,226948362020152,216102357810746,99660557983866,81810911020953,259210574098133,
  363447224274849,351185577563369,217860440625929,4966987581092,264080205910834,503420366552654,
  679921422931984,771953437495022,779666832817162,719404158028412,615570723290916,493039956106638,
  371960899236696,265469505525816,179797409074142,115817684868098,71068546937314,41587035491676,
  23222240816518,12377648043298,6296788377914,3055932823850,1413509495850,622038902902,259643256486,
  102044475564,37392856356,12243041522,3211855508,289826358]
private def rkmC_w64_m2_s7b_21 : List ℤ := rkmMapZZ [550406747,49595386,1006346288,442324004,
  1483901985,1575971517,1109021716,2674046226,32380979,3558149921,1799774867,3446376246,4290789642,
  2009788221,6533669449,1117916925,7603053128,5591651294,6412093247,10470824587,2276538784,
  14509418988,5389598232,14750499653,15180159047,9660876586,24412355800,2491618646,28799271097,
  20354244223,23321573312,39191140386,4757071333,51161513671,25596722915,47253388658,61076857342,
  19250576911,87277319077,32278624309,86104418866,95582408562,42521192741,144727050257,44023120961,
  147124393438,152687181920,75793411201,237698685935,71429276323,239173061660,253980839010,
  111468808811,387030294897,141840189589,366606956354,438110389586,122786168849,620352998991,
  313360830659,513770070334,766662483144,34793319745,950565072135,695199453821,599919024540,
  1308876281980,319910491548,1315275753937,1447772196007,396030615384,2061091347988,1236832441364,
  1431351660333,2689383066789,582340764007,2712398779884,3051297449938,562501967201,4136931424115,
  3023847110269,2202805019996,5605575467894,2529233321662,4320746469229,7054806501083,1541950421487,
  6903546473788,8493920369794,93855077766,9977362861957,10042467780251,1715604239684,13631073916344,
  11972897143594,3687274042393,18022081275447,14770320819345,5431018255588,23326073129764,
  19193180885730,6198672361777,29583328516723,26312305445905,4583034138230,36305903179760,
  37372640464016,1866074279686,41684260618297,53162580869889,16873369500601,41257976739230,
  72255595382290,44673384484394,26420364363715,87363085985515,86313184759171,15149671566609,
  80189717530540,130148394093360,91280465713138,20491936179271,136881478238327,179997708333039,
  112435224965715,37457614639908,190087959723746,258785990947328,196945958213362,22231898072452,
  192845411530233,355832322332855,394989455347759,286389916120431,57874028955755,227542871697706,
  498024134838702,696799563964860,795498330481426,795111030911292,717851613072776,595389610339460,
  458325357983732,329630199813940,222474776435912,141326484199980,84662243262444,47881331930548,
  25576657636378,12902020891708,6141503480296,2754659036556,1161469890722,458561744210,168608929170,
  56787587352,16895705794,4026864570,289107868]
private def rkmC_w64_m2_s7b_22 : List ℤ := rkmMapZZ [243393633,412571562,640666424,574094605,
  1236551001,447950520,1888248218,257589934,2572912513,1411718633,2672731620,3206099890,1984265947,
  5020560275,212152902,6348647646,2506833502,7013274577,6308198923,5856888956,10406560728,
  2458809709,14117466543,3320366617,15826533580,11560623388,14125045407,21150445551,7335764008,
  29707195162,5604911042,33793142827,23580258701,29885498454,44182048198,14036512927,61408682903,
  14454292073,67549509238,53280027488,54543809359,94320489295,15892838006,123900115710,48611682806,
  124070253455,128002337361,79229649052,200235784756,17911175132,232523751721,156299861321,
  190757357136,301740414482,51628545933,395877655083,176902462183,370417179522,441114782688,
  173373388647,640211639429,195333202815,646440298148,650496032670,355325320303,1014246833471,
  243548534399,1054759239432,1001885511660,583518124359,1600082732053,409475988029,1627698122176,
  1637978533368,777629855563,2515144467931,899817467977,2338964814096,2806302304540,685038539513,
  3859266781943,2134192728783,2941493069906,4831235589148,314649693686,5484771123821,4789487041865,
  2606068598114,7821139932786,3418675177958,6385109024931,9476143144011,597925732623,10682648574626,
  10106142841894,3620802339891,15191128455871,9570785802327,9089612444510,19765962538344,
  7964356610920,15662016396331,24544127627959,5641387376639,23265805345354,30041344599984,
  3279458411008,31905051181943,37249184813821,2071002694805,41482030317136,47676967617972,
  4101870550878,51283507518977,63198457965399,12951367145931,58818836910452,85208844097228,
  34212226134442,57669336373499,112012999028281,74679405365115,34635078189842,132741478574332,
  136691556930952,30551471585268,117467590976315,201141849254871,151424306535459,13455985190466,
  196949354476066,284047367985368,211277078542332,3471494614100,241209260488405,404139934737323,
  404075736559473,229959447239521,62823265637802,383850525471900,646833069011758,798185774720440,
  826341700791810,753846668406600,620604709949790,467254862361222,324334757503490,208582984023730,
  124642675127538,69304314507978,35861917613262,17253108685868,7700743625938,3177965456484,
  1206048946942,417511237962,129885017564,35200094670,7606106008,682120046]
private def rkmWalksHi_w64_m2_r1024 : List RkmWinSegWalk := [
  ⟨16, rkmHbWin_w64_m2_s0,
    0, rkmXsWin_w64_m2_s0_in, 0, rkmXsWin_w64_m2_s0_out, 154322574⟩,
  ⟨32, rkmHbWin_w64_m2_s1,
    0, rkmXsWin_w64_m2_s1_in, 0, rkmXsWin_w64_m2_s1_out, 447062660⟩,
  ⟨64, rkmHbWin_w64_m2_s2,
    0, rkmXsWin_w64_m2_s2_in, 0, rkmXsWin_w64_m2_s2_out, 676656641⟩,
  ⟨128, rkmHbWin_w64_m2_s3,
    0, rkmXsWin_w64_m2_s3_in, 17, rkmXsWin_w64_m2_s3_out, 2962659292⟩,
  ⟨256, rkmHbWin_w64_m2_s4,
    17, rkmXsWin_w64_m2_s4_in, 87, rkmXsWin_w64_m2_s4_out, 9210483343⟩,
  ⟨512, rkmHbWin_w64_m2_s5,
    87, rkmXsWin_w64_m2_s5_in, 250, rkmXsWin_w64_m2_s5_out, 22149627228⟩,
  ⟨1024, rkmHbWin_w64_m2_s6,
    250, rkmXsWin_w64_m2_s6_in, 555, rkmXsWin_w64_m2_s6_out, 47510516360⟩,
  ⟨1024, rkmHbWin_w64_m2_p7a,
    555, rkmXsWin_w64_m2_s7a_in, 866, rkmXsWin_w64_m2_s7b_out, 71587073947⟩
  ]
private theorem rkmWC_w64_m2_s7b_0 : bWinChk 18 100000000 1024
    hbN_w64_m2_p7b 643 rkmXsWin_w64_m2_s7b_in
    661 rkmC_w64_m2_s7b_1 3395845760 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_1 : bWinChk 17 100000000 1024
    hbN_w64_m2_p7b 661 rkmC_w64_m2_s7b_1
    678 rkmC_w64_m2_s7b_2 2856152947 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_2 : bWinChk 17 100000000 1024
    hbN_w64_m2_p7b 678 rkmC_w64_m2_s7b_2
    694 rkmC_w64_m2_s7b_3 3194541852 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_3 : bWinChk 17 100000000 1024
    hbN_w64_m2_p7b 694 rkmC_w64_m2_s7b_3
    708 rkmC_w64_m2_s7b_4 3063833846 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_4 : bWinChk 17 100000000 1024
    hbN_w64_m2_p7b 708 rkmC_w64_m2_s7b_4
    724 rkmC_w64_m2_s7b_5 2574595557 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_5 : bWinChk 17 100000000 1024
    hbN_w64_m2_p7b 724 rkmC_w64_m2_s7b_5
    739 rkmC_w64_m2_s7b_6 2340411368 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_6 : bWinChk 17 100000000 1024
    hbN_w64_m2_p7b 739 rkmC_w64_m2_s7b_6
    753 rkmC_w64_m2_s7b_7 2865980786 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_7 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 753 rkmC_w64_m2_s7b_7
    762 rkmC_w64_m2_s7b_8 2812927446 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_8 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 762 rkmC_w64_m2_s7b_8
    775 rkmC_w64_m2_s7b_9 2701581904 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_9 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 775 rkmC_w64_m2_s7b_9
    785 rkmC_w64_m2_s7b_10 2464924072 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_10 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 785 rkmC_w64_m2_s7b_10
    796 rkmC_w64_m2_s7b_11 2380092958 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_11 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 796 rkmC_w64_m2_s7b_11
    804 rkmC_w64_m2_s7b_12 2200802478 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_12 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 804 rkmC_w64_m2_s7b_12
    812 rkmC_w64_m2_s7b_13 2356929877 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_13 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 812 rkmC_w64_m2_s7b_13
    821 rkmC_w64_m2_s7b_14 2764961131 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_14 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 821 rkmC_w64_m2_s7b_14
    828 rkmC_w64_m2_s7b_15 2326277507 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_15 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 828 rkmC_w64_m2_s7b_15
    835 rkmC_w64_m2_s7b_16 2193119201 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_16 : bWinChk 15 100000000 1024
    hbN_w64_m2_p7b 835 rkmC_w64_m2_s7b_16
    842 rkmC_w64_m2_s7b_17 2025939981 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_17 : bWinChk 15 100000000 1024
    hbN_w64_m2_p7b 842 rkmC_w64_m2_s7b_17
    847 rkmC_w64_m2_s7b_18 2008858658 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_18 : bWinChk 15 100000000 1024
    hbN_w64_m2_p7b 847 rkmC_w64_m2_s7b_18
    851 rkmC_w64_m2_s7b_19 1798496950 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_19 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 851 rkmC_w64_m2_s7b_19
    857 rkmC_w64_m2_s7b_20 2105957909 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_20 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 857 rkmC_w64_m2_s7b_20
    861 rkmC_w64_m2_s7b_21 2109189979 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_21 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 861 rkmC_w64_m2_s7b_21
    863 rkmC_w64_m2_s7b_22 1905672993 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7b_22 : bWinChk 16 100000000 1024
    hbN_w64_m2_p7b 863 rkmC_w64_m2_s7b_22
    866 rkmXsWin_w64_m2_s7b_out 1884138265 = true := by decide +kernel
private abbrev m2B0 : Bool := muxIntListEq rkmHbWin_w64_m2_p7b (uON hbN_w64_m2_p7b)
private abbrev m2B1 : Bool := muxIntListEq rkmXsWin_w64_m2_s7a_out rkmXsWin_w64_m2_s7b_in
private abbrev m2B2 : Bool :=
  Nat.ble (Nat.add 555 (altIntLen rkmXsWin_w64_m2_s7a_in)) (Nat.add 1024 1)
private abbrev m2B3 : Bool :=
  rkmCheckRowFromWinWalks 2 4096 1024 [8, 16, 32, 64, 128, 256, 512, 896]
    [2908422, 3930347, 4690646, 4542060, 5273504, 5943872, 7203425, 9103735]
    [3, 6, 13, 25, 55, 115, 243, 454]
    rkmMasksHi_w64_m2_r1024 rkmWalksHi_w64_m2_r1024 rkmRowHi_w64_m2_r1024
private abbrev m2B4 : Bool :=
  rkmCheckRowFromWinWalks 8 1024 1024 [2, 4, 8, 16, 32, 64, 128, 224]
    [2908422, 3930347, 4690646, 4542060, 5273504, 5943872, 7203425, 9103735]
    [3, 6, 13, 25, 55, 115, 243, 454]
    rkmMasksHi_w64_m2_r1024 rkmWalksHi_w64_m2_r1024 rkmRowHi_w64_m2_r1024
private theorem rkmWinSt_w64_m2_t1 :
    bAll5 m2B0 m2B1 m2B2 m2B3 m2B4 = true := by decide +kernel
private theorem rkmWinSt_m2_p :
    m2B0 = true ∧ m2B1 = true ∧ m2B2 = true ∧ m2B3 = true ∧ m2B4 = true :=
  @bAll5_elim m2B0 m2B1 m2B2 m2B3 m2B4 rkmWinSt_w64_m2_t1
private theorem itB_w64_m2_p7b :
    RkmWinIterSound 373 1024 (uON hbN_w64_m2_p7b) 643 rkmXsWin_w64_m2_s7b_in
      866 rkmXsWin_w64_m2_s7b_out 56331233425 :=
  rkmChS 373 56331233425 (rkmChS 357 54447095160 (rkmChS 341 52541422167 (rkmChS 325 50432232188
    (rkmChS 309 48326274279 (rkmChS 294 46527777329 (rkmChS 279 44518918671 (rkmChS 264
    42492978690 (rkmChS 248 40299859489 (rkmChS 232 37973581982 (rkmChS 216 35208620851 (rkmChS
    200 32851690974 (rkmChS 184 30650888496 (rkmChS 168 28270795538 (rkmChS 152 25805871466
    (rkmChS 136 23104289562 (rkmChS 120 20291362116 (rkmChS 103 17425381330 (rkmChS 86
    15084969962 (rkmChS 69 12510374405 (rkmChS 52 9446540559 (rkmChS 35 6251998707
    (bWinChk_sound rkmWC_w64_m2_s7b_0) rkmWC_w64_m2_s7b_1 rfl rfl) rkmWC_w64_m2_s7b_2 rfl rfl)
    rkmWC_w64_m2_s7b_3 rfl rfl) rkmWC_w64_m2_s7b_4 rfl rfl) rkmWC_w64_m2_s7b_5 rfl rfl)
    rkmWC_w64_m2_s7b_6 rfl rfl) rkmWC_w64_m2_s7b_7 rfl rfl) rkmWC_w64_m2_s7b_8 rfl rfl)
    rkmWC_w64_m2_s7b_9 rfl rfl) rkmWC_w64_m2_s7b_10 rfl rfl) rkmWC_w64_m2_s7b_11 rfl rfl)
    rkmWC_w64_m2_s7b_12 rfl rfl) rkmWC_w64_m2_s7b_13 rfl rfl) rkmWC_w64_m2_s7b_14 rfl rfl)
    rkmWC_w64_m2_s7b_15 rfl rfl) rkmWC_w64_m2_s7b_16 rfl rfl) rkmWC_w64_m2_s7b_17 rfl rfl)
    rkmWC_w64_m2_s7b_18 rfl rfl) rkmWC_w64_m2_s7b_19 rfl rfl) rkmWC_w64_m2_s7b_20 rfl rfl)
    rkmWC_w64_m2_s7b_21 rfl rfl) rkmWC_w64_m2_s7b_22 rfl rfl
private theorem rkmWinIterSnd_w64_m2_p7b :
    RkmWinIterSound 373 1024 rkmHbWin_w64_m2_p7b 643 rkmXsWin_w64_m2_s7b_in
      866 rkmXsWin_w64_m2_s7b_out 56331233425 :=
  @rkmSubHb 373 1024 643 866 56331233425 rkmHbWin_w64_m2_p7b (uON hbN_w64_m2_p7b)
    rkmXsWin_w64_m2_s7b_in rkmXsWin_w64_m2_s7b_out
    rkmWinSt_m2_p.1 itB_w64_m2_p7b
private theorem rkmWinChain_w64_m2_s7_full :
    RkmWinIterSound 454 1024 rkmHbWin_w64_m2_p7a 555 rkmXsWin_w64_m2_s7a_in
      866 rkmXsWin_w64_m2_s7b_out 71587073947 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w64_m2_p7a) (hb2 := rkmHbWin_w64_m2_p7b)
    (x1 := rkmXsWin_w64_m2_s7a_out) (x1' := rkmXsWin_w64_m2_s7b_in)
    rfl rfl (muxIntListEq_eq_true.mpr rfl) rfl rkmWinSt_m2_p.2.1
    rkmWinIterSnd_w64_m2_p7a rkmWinIterSnd_w64_m2_p7b
private theorem rkmWinSegWalkSnd_w64_m2_s7 :
    RkmWinSegWalkSound 454 ⟨1024, rkmHbWin_w64_m2_p7a, 555, rkmXsWin_w64_m2_s7a_in,
      866, rkmXsWin_w64_m2_s7b_out, 71587073947⟩ :=
  @rkmSegWalk_mk 454 1024 555 866 71587073947
    rkmHbWin_w64_m2_p7a rkmXsWin_w64_m2_s7a_in rkmXsWin_w64_m2_s7b_out
    (rkmw_buildHbFrom_length 1792 1024 20052279735 1024 0)
    rkmWinSt_m2_p.2.2.1
    rkmWinChain_w64_m2_s7_full
private theorem rkmWalksSndHi_w64_m2_r1024 :
    RkmWinSegWalksSound [3, 6, 13, 25, 55, 115, 243, 454]
      rkmWalksHi_w64_m2_r1024 :=
  And.intro rkmWinSegWalkSnd_w64_m2_s0 (
  And.intro rkmWinSegWalkSnd_w64_m2_s1 (
  And.intro rkmWinSegWalkSnd_w64_m2_s2 (
  And.intro rkmWinSegWalkSnd_w64_m2_s3 (
  And.intro rkmWinSegWalkSnd_w64_m2_s4 (
  And.intro rkmWinSegWalkSnd_w64_m2_s5 (
  And.intro rkmWinSegWalkSnd_w64_m2_s6 (
  And.intro rkmWinSegWalkSnd_w64_m2_s7 (
    trivial))))))))
/-- Caustic `w_hi64_m2_r1024` `r = 1024` hit certificate (`m = 2`). -/
theorem rkmTrajHitHi_w64_m2 :
    RkmAnchorHitSound 2 ⟨1024, [8, 16, 32, 64, 128, 256, 512, 896],
      [2908422, 3930347, 4690646, 4542060, 5273504, 5943872, 7203425, 9103735],
      [3, 6, 13, 25, 55, 115, 243, 454],
      rkmMasksHi_w64_m2_r1024, rkmRowHi_w64_m2_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 2 4096 1024 [8, 16, 32, 64, 128, 256, 512, 896]
    [2908422, 3930347, 4690646, 4542060, 5273504, 5943872, 7203425, 9103735]
    [3, 6, 13, 25, 55, 115, 243, 454] rkmMasksHi_w64_m2_r1024
    rkmWalksHi_w64_m2_r1024 rkmRowHi_w64_m2_r1024
    rkmWalksSndHi_w64_m2_r1024
    rkmWinSt_m2_p.2.2.2.1
/-- Caustic `w_hi64_m2_r1024` `r = 1024` hit certificate (`m = 8`). -/
theorem rkmTrajHitHi_w64_m8 :
    RkmAnchorHitSound 8 ⟨1024, [2, 4, 8, 16, 32, 64, 128, 224],
      [2908422, 3930347, 4690646, 4542060, 5273504, 5943872, 7203425, 9103735],
      [3, 6, 13, 25, 55, 115, 243, 454],
      rkmMasksHi_w64_m2_r1024, rkmRowHi_w64_m2_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 8 1024 1024 [2, 4, 8, 16, 32, 64, 128, 224]
    [2908422, 3930347, 4690646, 4542060, 5273504, 5943872, 7203425, 9103735]
    [3, 6, 13, 25, 55, 115, 243, 454] rkmMasksHi_w64_m2_r1024
    rkmWalksHi_w64_m2_r1024 rkmRowHi_w64_m2_r1024
    rkmWalksSndHi_w64_m2_r1024
    rkmWinSt_m2_p.2.2.2.2
/-- Cumulative `FindAllJohnsonRampKickMuxHiW64T01` lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T01 :
    @rkmTrajHitHi_w64_m8 = @rkmTrajHitHi_w64_m8 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T00) rfl).right

end
end QuantumComputation.Specs.DickeSol
