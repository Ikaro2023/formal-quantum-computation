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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T9

/-
# Caustic `r = 1024` Halo-16 Walk `w1024` Part `0` (`RkMuxHiW1024WinT0`)

Certifies part `0` of the `w1024` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w1024_s0`. -/
def rkmHbWin_w1024_s0 : List ℤ := altBuildHbFrom 1024 1024 29614734693 0 1024
/-- Entry `rkmXsWin_w1024_s0_in`. -/
def rkmXsWin_w1024_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w1024_s0_out`. -/
def rkmXsWin_w1024_s0_out : List ℤ := let p := rkmP; [p 216399085, p 352741628, p 540374354,
  p 813011731, p 1071670895, p 1480618635, p 1932020500, p 2600069659, p 3475436604, p 4556647861,
  p 6005808848, p 7776122386, p 10147381802, p 13146905180, p 16967862185, p 21852668691,
  p 27962018104, p 35774572575, p 45526341919, p 57765614344, p 73011379679, p 91901708494,
  p 115380423524, p 144279916681, p 179883260557, p 223439707541, p 276553873416, p 341133765598,
  p 419226310834, p 513486535772, p 626682523591, p 762229624397, p 923901830468, p 1115929340419,
  p 1343266816387, p 1611209456988, p 1925959630982, p 2294180597133, p 2723316671304,
  p 3221588924693, p 3797776532728, p 4461648598945, p 5223423910298, p 6094188902794,
  p 7085596242511, p 8209821540571, p 9479732243840, p 10908331785132, p 12509114325589,
  p 14295478202969, p 16280791279573, p 18478209491328, p 20900180603333, p 23558612236783,
  p 26464111590029, p 29626103532526, p 33052347492688, p 36748585542908, p 40718526727144,
  p 44963059553705, p 49480489894572, p 54265808845790, p 59310791188990, p 64603663645318,
  p 70128915196042, p 75867286754623, p 81795637613732, p 87886932581392, p 94110530168943,
  p 100432002619391, p 106813726591055, p 113214899912627, p 119591961914950, p 125899310734077,
  p 132089300391765, p 138113468023071, p 143922582313896, p 149467531918336, p 154700184158929,
  p 159573497065522, p 164043004325205, p 168066810409379, p 171606581578615, p 174628256448213,
  p 177102111507558, p 179003872508366, p 180314581029985, p 181021236970253, p 181116920592806,
  p 180600812446747, p 179478420121739, p 177761107482782, p 175466386298674, p 172617159665909,
  p 169241609481627, p 165372829756240, p 161047868942375, p 156307683681782, p 151196017093216,
  p 145759050947328, p 140044522887977, p 134101140392598, p 127977915862059, p 121723379707476,
  p 115385053655193, p 109009004654693, p 102638920833816, p 96316192232355, p 90079112194382,
  p 83962730823970, p 77998726106266, p 72214794554816, p 66635258232458, p 61280288104137,
  p 56166336993091, p 51306379700307, p 46709511449797, p 42381795967827, p 38325935916954,
  p 34541853506448, p 31026943076106, p 27776130476182, p 24782495558026, p 22037220262103,
  p 19530339772025, p 17250547267602, p 15185697030266, p 13323172781858, p 11649887373129,
  p 10152573039562, p 8818089628377, p 7633273180772, p 6585567174673, p 5662577302690,
  p 4852610366787, p 4144637519253, p 3527939496897, p 2992952412392, p 2530540541380,
  p 2132356021228, p 1790832446277, p 1498870010598, p 1250312894485, p 1039459360705,
  p 861345785981, p 711385688875, p 585530879931, p 480380763586, p 392840845853, p 320153504589,
  p 260132815688, p 210602188773, p 170025901391, p 136828617234, p 109634759747, p 87594625595,
  p 69637993409, p 55091610802, p 43294663782, p 33759163517, p 26133088230, p 19927156215,
  p 15011998448, p 11084823078, p 7987431392, p 5578297343, p 3656728932, p 2230037992,
  p 1262556212, p 500822910, p 138749130]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private abbrev bz0 : ℕ := 100000000000000000
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
private def bSV (v P Q d : ℕ) : ℕ := match Nat.add 1 P with
  | 0 => 0 | pF + 1 => match Nat.add 1 Q with
    | 0 => 0 | qF + 1 => match Nat.sub qF pF with
      | 0 => Nat.add v (Nat.div (Nat.sub pF qF) d) | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem svEq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bSV at hv ⊢; rw [n1a P, n1a Q] at hv ⊢; dsimp only at hv ⊢
  rw [← sntEq]; unfold rkmUltraSubNatTdiv
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
private def tkZ : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | n + 1, xs => match xs with | [] => [] | x :: r => x :: tkZ n r
private def tk4 : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | q + 1, xs =>
    match xs with
    | x1 :: x2 :: x3 :: x4 :: r => x1 :: x2 :: x3 :: x4 :: tk4 q r
    | r => r
private theorem uHb_tk4 : ∀ (q : ℕ) (b : List ℕ), uHb (tk4 q b) = tkZ (4 * q) (uHb b)
  | 0, _ => by have h0 : 4 * 0 = 0 := rfl; rw [h0]; rfl
  | q + 1, [] => by
    have h4 : 4 * (q + 1) = (4 * q + 3) + 1 := by omega
    rw [h4]; rfl
  | q + 1, [x1] => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; rfl
  | q + 1, [x1, x2] => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; rfl
  | q + 1, [x1, x2, x3] => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; rfl
  | q + 1, x1 :: x2 :: x3 :: x4 :: bs => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; dsimp only [tk4, uHb, tkZ]; rw [uHb_tk4 q bs]
private def toH4K : ℕ → List ℕ → HbZ4
  | 0, _ => HbZ4.tail []
  | q + 1, xs =>
    match xs with
    | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
      match toH4K q bs with
      | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
      | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
        HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
    | bs => HbZ4.tail bs
private theorem hbz4L_toH4K (z : ℕ) : ∀ (q : ℕ) (b : List ℕ),
    hbz4L (toH4K q (mkHbZ z b)) = mkHbZ z (tk4 q b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [x1] => by simp only [mkHbZ, tk4, uCN_eq]; rfl
  | _ + 1, [x1, x2] => by simp only [mkHbZ, tk4, uCN_eq]; rfl
  | _ + 1, [x1, x2, x3] => by simp only [mkHbZ, tk4, uCN_eq]; rfl
  | q + 1, x1 :: x2 :: x3 :: x4 :: bs => by
    have ih := hbz4L_toH4K z q bs; simp only [mkHbZ, tk4, uCN_eq]; dsimp only [toH4K]
    cases h : toH4K q (mkHbZ z bs) with
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
private theorem bDg_sound (z q dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bDg z dg mL cL (toH4K q (mkHbZ z b)) v c = some out) :
    bD z out = rkmUltraHornerStage dg mL cL (uHb (tk4 q b)) (bD z v) (bD z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z (tk4 q b) v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bDg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, bChkPe, bSlZ4_eq, hbz4L_toH4K, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z (tk4 q b) v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z]
    exact bSl_sound z _ _ 0 z (tk4 q b) v c hp
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (v x : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bDg z g m c h4 v x with | none => none | some o => k n o
private theorem bBdD_sound {z q g m c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4K q (mkHbZ z b)) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some out → bD z out = kU (rkmNextLen m c) (bD z m0)) :
    bD z out = (HighDForce.withForcedNat (rkmNextLen m c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uHb (tk4 q b)) (bD z v) (bD z x)) (kU nL)) := by
  unfold bBdD at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bDg z g m c (toH4K q (mkHbZ z b)) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bDg_sound z q g m c b v x mid hs]
    exact hk mid h
private def bSp (z q m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  fH4 (toH4K q hbz) fun h4 =>
    bBdD z 16 m c h4 v v fun l x => bBdD z 15 m l h4 v x fun l x =>
    bBdD z 14 m l h4 v x fun l x => bBdD z 13 m l h4 v x fun l x =>
    bBdD z 12 m l h4 v x fun l x => bBdD z 11 m l h4 v x fun l x =>
    bBdD z 10 m l h4 v x fun l x => bBdD z 9 m l h4 v x fun l x =>
    bBdD z 8 m l h4 v x fun l x => bBdD z 7 m l h4 v x fun l x =>
    bBdD z 6 m l h4 v x fun l x => bBdD z 5 m l h4 v x fun l x =>
    bBdD z 4 m l h4 v x fun l x => bBdD z 3 m l h4 v x fun l x =>
    bBdD z 2 m l h4 v x fun l x => bDg z 1 m l h4 v x
private theorem bSp_sound (z q mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z q mL cL (mkHbZ z b) v = some out) :
    bD z out = rkmUltraHornerT16Step mL cL (uHb (tk4 q b)) (bD z v) := by
  unfold bSp at h; rw [fH4e] at h; unfold rkmUltraHornerT16Step
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  exact bDg_sound z q 1 mL _ b v _ out h
private theorem nxt_le (m c : ℕ) : rkmNextLen m c ≤ c + 1 := by
  unfold rkmNextLen; rw [rkmb_natMin_eq, Nat.add_eq]; exact Nat.min_le_right m (c + 1)
private theorem sl_tk : ∀ (d rem : ℕ) (p : ℤ) (n : ℕ) (hb v c : List ℤ),
    rem ≤ n → rkmUltraSlideLoopAux d rem p (tkZ n hb) v c =
      rkmUltraSlideLoopAux d rem p hb v c
  | _, 0, _, _, _, _, _, _ => rfl
  | _, rem + 1, _, 0, _, _, _, h => absurd h (Nat.not_succ_le_zero rem)
  | _, _ + 1, _, _ + 1, [], _, _, _ => rfl
  | d, rem + 1, p, n + 1, b :: hbR, v, c, h => by
    have hn : rem ≤ n := Nat.le_of_succ_le_succ h; dsimp only [tkZ]
    cases v with
    | nil => cases c with
      | nil => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR [] [] hn]
      | cons _ cT => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR [] cT hn]
    | cons _ vT => cases c with
      | nil => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR vT [] hn]
      | cons _ cT => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR vT cT hn]
private theorem stg_tk (dg mL cL n : ℕ) (hb v c : List ℤ) (hc : cL + 1 ≤ n) :
    rkmUltraHornerStage dg mL cL (tkZ n hb) v c = rkmUltraHornerStage dg mL cL hb v c := by
  unfold rkmUltraHornerStage; simp only [rkmb_forceNat_eq]
  exact sl_tk (Nat.mul dg wdScale) (rkmNextLen mL cL) (Int.ofNat 0) n hb v c
    ((nxt_le mL cL).trans hc)
private theorem bd_tk (dg mL cL k n : ℕ) (hb v c : List ℤ)
    {f1 f2 : ℕ → List ℤ → List ℤ} (hc : cL + (k + 1) ≤ n)
    (hf : ∀ l1 c1, l1 ≤ cL + 1 → f1 l1 c1 = f2 l1 c1) :
    (HighDForce.withForcedNat (rkmNextLen mL cL) fun l1 =>
      HighDForce.withForcedList (rkmUltraHornerStage dg mL cL (tkZ n hb) v c) (f1 l1)) =
    (HighDForce.withForcedNat (rkmNextLen mL cL) fun l1 =>
      HighDForce.withForcedList (rkmUltraHornerStage dg mL cL hb v c) (f2 l1)) := by
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq]
  rw [stg_tk dg mL cL n hb v c (by omega)]
  exact hf (rkmNextLen mL cL) _ (nxt_le mL cL)
private theorem step_tk (mL cL n : ℕ) (hb v : List ℤ) (hc : cL + 16 ≤ n) :
    rkmUltraHornerT16Step mL cL (tkZ n hb) v = rkmUltraHornerT16Step mL cL hb v := by
  unfold rkmUltraHornerT16Step
  refine bd_tk 16 mL cL 15 n hb v v hc fun l1 c1 h1 => ?_
  refine bd_tk 15 mL l1 14 n hb v c1 (by omega) fun l2 c2 h2 => ?_
  refine bd_tk 14 mL l2 13 n hb v c2 (by omega) fun l3 c3 h3 => ?_
  refine bd_tk 13 mL l3 12 n hb v c3 (by omega) fun l4 c4 h4 => ?_
  refine bd_tk 12 mL l4 11 n hb v c4 (by omega) fun l5 c5 h5 => ?_
  refine bd_tk 11 mL l5 10 n hb v c5 (by omega) fun l6 c6 h6 => ?_
  refine bd_tk 10 mL l6 9 n hb v c6 (by omega) fun l7 c7 h7 => ?_
  refine bd_tk 9 mL l7 8 n hb v c7 (by omega) fun l8 c8 h8 => ?_
  refine bd_tk 8 mL l8 7 n hb v c8 (by omega) fun l9 c9 h9 => ?_
  refine bd_tk 7 mL l9 6 n hb v c9 (by omega) fun la ca ha => ?_
  refine bd_tk 6 mL la 5 n hb v ca (by omega) fun lb cb hb1 => ?_
  refine bd_tk 5 mL lb 4 n hb v cb (by omega) fun lc cc hc1 => ?_
  refine bd_tk 4 mL lc 3 n hb v cc (by omega) fun ld cd hd1 => ?_
  refine bd_tk 3 mL ld 2 n hb v cd (by omega) fun le ce he1 => ?_
  refine bd_tk 2 mL le 1 n hb v ce (by omega) fun lf cf hf1 => ?_
  exact stg_tk 1 mL lf n hb v cf (by omega)
private theorem it1_eq (mL cL : ℕ) (hb v : List ℤ) :
    muxUltraIterFullT16Rkm 1 mL cL hb v = rkmUltraHornerT16Step mL cL hb v := by
  unfold muxUltraIterFullT16Rkm; dsimp only; rw [rkmb_forceList_eq, rkmb_forceNat_eq]; rfl
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
        fN (Nat.sub (Nat.add d 1) sLo) fun remMax =>
          fL (bPZ z padL us) fun vns => fN (bNL vns) fun curLen =>
            fN (Nat.add (Nat.div curLen 4) 5) fun qH =>
              match bSp z qH remMax curLen (dr2 kD hbz) vns with
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
    set vns := bPZ z padL us; set qH := Nat.add (Nat.div (bNL vns) 4) 5
    rw [d2Eq] at h; revert h
    cases hi : bSp z qH remMax (bNL vns) (mkHbZ z (drN kD b)) vns with
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
      have hq : bNL vns + 16 ≤ 4 * qH := by
        have hdm := Nat.div_add_mod (bNL vns) 4
        have hml := Nat.mod_lt (bNL vns) (Nat.succ_pos 3)
        dsimp only [qH]; rw [Nat.add_eq, ndiv]; omega
      rw [ho, hu, hd, twEq z thr sLo out dropAcc]
      rw [bSp_sound z qH remMax (bNL vns) (drN kD b) vns out hi]
      rw [uHb_tk4 qH (drN kD b), step_tk remMax (bNL vns) (4 * qH) _ _ hq, ← it1_eq, hkd]
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
private def uNatApp : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | n :: ns, acc => n :: uNatApp ns acc
private def uNatCatN : List (List ℕ) → List ℕ
  | [] => []
  | ns :: nss => uNatApp ns (uNatCatN nss)
private def pzigApp : List ℕ → List ℤ → List ℤ
  | [], acc => acc
  | w :: ws, acc =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzigApp ws acc
private def pzigCat : List (List ℕ) → List ℤ
  | [] => []
  | ws :: wss => pzigApp ws (pzigCat wss)
private theorem drHbSub {w0 k0 wc : ℕ} {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb) (hw : w0 + k0 = wc) :
    uHb (drN k0 b) = rkmDropInts wc hb := by
  rw [dnEq k0 b, hhb, ← dr_add w0 k0 hb, hw]
private def rkmPhb_w1024_s0 : List ℕ := uNatCatN
  [
   [60650976651264,85689670632493,104845396188099,120946576486212,135089942214705,
    147838535308395,159527162314739,170374183838213,180531422688528,190109528280919,
    199192113455996,207844200271124,216117547556424,224054161840899,231688696022046,
    239050138441896,246163033295187,253048382190384,259724323162308,266206650834860,
    272509220940748,278644269164035,284622665503245,290454119418457,296147346930000,
    301710207958781,307149820144000,312472653885649,317684612266406,322791098695149,
    327797074503442,332707108262233,337525418229810,342255909066255,346902203734249,
    351467671336524,355955451505759,360368475855351,364709486913104,368981054890060,
    373185592579850,377325368637438,381402519447859,385419059763969,389376892265915,
    393277816173141,397123535021383,400915663701655,404655734845152,408345204626985,
    411985458052190,415577813779448,419123528531068,422623801131851,426079776214374,
    429492547623800,432863161551533,436192619423680,439481880567413,442731864675792,
    445943454089388,449117495911106,452254803968898,455356160639568,458422318545494,
    461454002134972,464451909155789,467416712030743,470349059142975,473249576038259,
    476118866550718,478957513857867,481766081470330,484545114161132,487295138839012,
    490016665369842,492710187349875,495376182834236,498015115023800,500627432913320,
    503213571903456,505773954379137,508308990256505,510819077500486,513304602614929,
    515765941107045,518203457927796,520617507889734,523008436063696,525376578155644,
    527722260864858,530045802224606,532347511926317,534627691628238,536886635249475,
    539124629250243,541341952899134,543538878528104,545715671775896,547872591820500,
    550009891601281,552127818031316,554226612200459,556306509569645,558367740156873,
    560410528715309,562435094903919,564441653450999,566430414310976,568401582814808,
    570355359814303,572291941820657,574211521137483,576114285988620,578000420640939,
    579870105522417,581723517335672,583560829167195,585382210592460,587187827777106,
    588977843574384,590752417619004,592511706417584,594255863435818,595985039182524,
    597699381290706,599399034595757,601084141210923],
   [602754840600151,604411269648431,606053562729730,607681851772622,609296266323718,
    610896933608968,612483978592935,614057524036127,615617690550445,617164596652841,
    618698358817252,620219091524871,621726907312823,623221916821318,624704228839316,
    626173950348792,627631186567617,629076040991149,630508615432541,631929010061843,
    633337323443930,634733652575300,636118092919783,637490738443205,638851681647034,
    640201013601061,641538823975127,642865201069954,644180231847096,645484001958040,
    646776595772494,648058096405892,649328585746125,650588144479548,651836852116265,
    653074787014739,654302026405722,655518646415559,656724722088854,657920327410548,
    659105535327408,660280417768950,661445045667827,662599488979682,663743816702485,
    664878096895390,666002396697095,667116782343752,668221319186415,669316071708063,
    670401103540187,671476477478977,672542255501108,673598498779138,674645267696534,
    675682621862332,676710620125451,677729320588654,678738780622187,679739056877092,
    680730205298203,681712281136844,682685338963226,683649432678564,684604615526904,
    685550940106692,686488458382069,687417221693916,688337280770645,689248685738756,
    690151486133148,691045730907206,691931468442670,692808746559279,693677612524205,
    694538113061291,695390294360073,696234202084624,697069881382199,697897376891695,
    698716732751934,699527992609777,700331199628051,701126396493330,701913625423538,
    702692928175405,703464346051761,704227919908687,704983690162515,705731696796691,
    706471979368491,707204577015610,707929528462616,708646872027269,709356645626728,
    710058886783620,710753632632000,711440919923188,712120785031501,712793263959860,
    713458392345300,714116205464370,714766738238429,715410025238838,716046100692064,
    716674998484673,717296752168239,717911394964159,718518959768375,719119479156011,
    719712985385926,720299510405175,720879085853398,721451743067123,722017513083993,
    722576426646914,723128514208129,723673805933222,724212331705045,724744121127579,
    725269203529724,725787607969027,726299363235332,726804497854383,727303040091351,
    727795017954306,728280459197625,728759391325344],
   [729231841594451,729697837018127,730157404368920,730610570181882,731057360757634,
    731497802165400,731931920245970,732359740614628,732781288664024,733196589567000,
    733605668279371,734008549542657,734405257886774,734795817632677,735180252894963,
    735558587584429,735930845410594,736297049884172,736657224319514,737011391837005,
    737359575365426,737701797644276,738038081226060,738368448478540,738692921586950,
    739011522556174,739324273212898,739631195207720,739932310017231,740227638946066,
    740517203128917,740801023532525,741079120957632,741351516040907,741618229256849,
    741879280919647,742134691185030,742384480052071,742628667364980,742867272814859,
    743100315941437,743327816134780,743549792636967,743766264543756,743977250806210,
    744182770232313,744382841488554,744577483101489,744766713459284,744950550813232,
    745129013279253,745302118839368,745469885343150,745632330509166,745789471926383,
    745941327055565,746087913230650,746229247660098,746365347428234,746496229496563,
    746621910705067,746742407773490,746857737302599,746967915775430,747072959558521,
    747172884903119,747267707946380,747357444712548,747442111114116,747521722952979,
    747596295921563,747665845603942,747730387476945,747789936911237,747844509172401,
    747894119421991,747938782718578,747978514018785,748013328178301,748043239952890,
    748068263999379,748088414876637,748103707046547,748114154874950,748119772632595,
    748120574496063,748116574548690,748107786781465,748094225093931,748075903295064,
    748052835104150,748025034151637,747992513979994,747955288044544,747913369714297,
    747866772272766,747815508918777,747759592767265,747699036850066,747633854116694,
    747564057435107,747489659592474,747410673295920,747327111173269,747238985773776,
    747146309568851,747049094952776,746947354243408,746841099682876,746730343438275,
    746615097602345,746495374194140,746371185159701,746242542372708,746109457635129,
    745971942677865,745830009161382,745683668676340,745532932744210,745377812817888,
    745218320282301,745054466455003,744886262586768,744713719862175,744536849400185,
    744355662254711,744170169415186,743980381807117],
   [743786310292643,743587965671073,743385358679432,743178499992992,742967400225798,
    742752069931193,742532519602330,742308759672686,742080800516562,741848652449586,
    741612325729201,741371830555159,741127177069998,740878375359523,740625435453275,
    740368367325000,740107180893108,739841886021133,739572492518183,739299010139385,
    739021448586330,738739817507509,738454126498745,738164385103623,737870602813909,
    737572789069975,737270953261208,736965104726423,736655252754268,736341406583624,
    736023575404004,735701768355947,735375994531404,735046262974124,734712582680037,
    734374962597626,734033411628306,733687938626789,733338552401451,732985261714692,
    732628075283296,732267001778785,731902049827768,731533228012287,731160544870167,
    730784008895347,730403628538224,730019412205981,729631368262922,729239505030792,
    728843830789107,728444353775469,728041082185886,727634024175084,727223187856818,
    726808581304180,726390212549904,725968089586663,725542220367375,725112612805493,
    724679274775300,724242214112197,723801438612993,723356956036186,722908774102247,
    722456900493897,722001342856385,721542108797759,721079205889137,720612641664980,
    720142423623350,719668559226179,719191055899527,718709921033841,718225161984209,
    717736786070617,717244800578195,716749212757469,716250029824608,715747258961663,
    715240907316813,714730982004604,714217490106183,713700438669536,713179834709721,
    712655685209095,712127997117547,711596777352721,711062032800241,710523770313935,
    709981996716052,709436718797484,708887943317979,708335677006357,707779926560721,
    707220698648670,706657999907502,706091836944428,705522216336771,704949144632172,
    704372628348787,703792673975493,703209287972079,702622476769446,702032246769799,
    701438604346840,700841555845957,700241107584417,699637265851548,699030036908929,
    698419426990572,697805442303102,697188089025945,696567373311498,695943301285315,
    695315879046278,694685112666771,694051008192858,693413571644451,692772809015480,
    692128726274062,691481329362670,690830624198297,690176616672620,689519312652166,
    688858717978470,688194838468236,687527679913497],
   [686857248081772,686183548716224,685506587535810,684826370235439,684142902486125,
    683456189935132,682766238206132,682073052899347,681376639591698,680677003836953,
    679974151165870,679268087086341,678558817083536,677846346620041,677130681136001,
    676411826049257,675689786755488,674964568628340,674236177019571,673504617259178,
    672769894655533,672032014495517,671290982044649,670546802547217,669799481226408,
    669049023284435,668295433902663,667538718241738,666778881441711,666015928622161,
    665249864882318,664480695301186,663708424937665,662933058830671,662154601999251,
    661373059442707,660588436140713,659800737053425,659009967121604,658216131266728,
    657419234391103,656619281377981,655816277091666,655010226377633,654201134062628,
    653389004954786,652573843843737,651755655500711,650934444678649,650110216112306,
    649282974518356,648452724595501,647619471024568,646783218468617,645943971573041,
    645101734965668,644256513256858,643408311039611,642557132889656,641702983365556,
    640845867008805,639985788343921,639122751878545,638256762103536,637387823493065,
    636515940504710,635641117579549,634763359142249,633882669601165,632999053348423,
    632112514760018,631223058195897,630330688000055,629435408500616,628537224009929,
    627636138824648,626732157225822,625825283478981,624915521834222,624002876526290,
    623087351774666,622168951783649,621247680742439,620323542825219,619396542191237,
    618466682984886,617533969335785,616598405358863,615659995154430,614718742808262,
    613774652391680,612827727961622,611877973560724,610925393217399,609969990945905,
    609011770746429,608050736605158,607086892494353,606120242372424,605150790184003,
    604178539860016,603203495317758,602225660460962,601245039179871,600261635351311,
    599275452838758,598286495492410,597294767149256,596300271633144,595303012754851,
    594302994312150,593300220089877,592294693860000,591286419381681,590275400401348,
    589261640652759,588245143857061,587225913722866,586203953946304,585179268211095,
    584151860188608,583121733537926,582088891905909,581053338927252,580015078224554,
    578974113408372,577930448077287,576884085817962],
   [575835030205202,574783284802015,573728853159672,572671738817763,571611945304258,
    570549476135563,569484334816580,568416524840764,567346049690177,566272912835550,
    565197117736334,564118667840759,563037566585886,561953817397669,560867423691001,
    559778388869776,558686716326938,557592409444536,556495471593780,555395906135090,
    554293716418151,553188905781964,552081477554902,550971435054754,549858781588783,
    548743520453774,547625654936087,546505188311704,545382123846280,544256464795195,
    543128214403601,541997375906473,540863952528653,539727947484906,538589363979961,
    537448205208564,536304474355521,535158174595750,534009309094325,532857881006521,
    531703893477864,530547349644176,529388252631619,528226605556743,527062411526527,
    525895673638430,524726394980431,523554578631073,522380227659512,521203345125555,
    520023934079706,518841997563210,517657538608096,516470560237218,515281065464297,
    514089057293968,512894538721814,511697512734416,510497982309390,509295950415425,
    508091420012334,506884394051082,505674875473836,504462867214003,503248372196265,
    502031393336627,500811933542447,499589995712485,498365582736933,497138697497462,
    495909342867251,494677521711036,493443236885139,492206491237511,490967287607768,
    489725628827228,488481517718949,487234957097765,485985949770323,484734498535119,
    483480606182538,482224275494883,480965509246417,479704310203397,478440681124106,
    477174624758894,475906143850208,474635241132631,473361919332912,472086181170003,
    470808029355095,469527466591649,468244495575430,466959118994542,465671339529460,
    464381159853065,463088582630676,461793610520082,460496246171575,459196492227984,
    457894351324706,456589826089738,455282919143708,453973633099909,452661970564328,
    451347934135681,450031526405440,448712749957866,447391607370039,446068101211890,
    444742234046231,443414008428784,442083426908213,440750492026151,439415206317236,
    438077572309131,436737592522562,435395269471345,434050605662411,432703603595841,
    431354265764890,430002594656019,428648592748922,427292262516552,425933606425154,
    424572626934289,423209326496865,421843707559162],
   [420475772560858,419105523935064,417732964108342,416358095500737,414980920525804,
    413601441590633,412219661095878,410835581435779,409449204998194,408060534164622,
    406669571310228,405276318803872,403880779008133,402482954279334,401082846967569,
    399680459416728,398275793964520,396868852942503,395459638676104,394048153484645,
    392634399681369,391218379573465,389800095462090,388379549642395,386956744403548,
    385531682028760,384104364795307,382674794974554,381242974831979,379808906627197,
    378372592613983,376934035040294,375493236148294,374050198174377,372604923349187,
    371157413897646,369707672038970,368255699986698,366801499948709,365345074127250,
    363886424718952,362425553914856,360962463900433,359497156855610,358029634954784,
    356559900366851,355087955255225,353613801777855,352137442087255,350658878330518,
    349178112649339,347695147180036,346209984053574,344722625395579,343233073326365,
    341741329960951,340247397409083,338751277775253,337252973158719,335752485653529,
    334249817348533,332744970327414,331237946668695,329728748445770,328217377726916,
    326703836575318,325188127049083,323670251201263,322150211079874,320628008727912,
    319103646183376,317577125479285,316048448643696,314517617699723,312984634665559,
    311449501554489,309912220374912,308372793130359,306831221819508,305287508436210,
    303741654969496,302193663403606,300643535717997,299091273887370,297536879881679,
    295980355666156,294421703201325,292860924443017,291298021342393,289732995845958,
    288165849895577,286596585428495,285025204377352,283451708670202,281876100230526,
    280298380977252,278718552824773,277136617682959,275552577457176,273966434048304,
    272378189352751,270787845262469,269195403664973,267600866443355,266004235476298,
    264405512638098,262804699798674,261201798823586,259596811574051,257989739906960,
    256380585674889,254769350726120,253156036904653,251540646050223,249923179998312,
    248303640580171,246682029622827,245058348949103,243432600377635,241804785722879,
    240174906795133,238542965400552,236908963341155,235272902414850,233634784415439,
    231994611132640,230352384352098,228708105855398],
   [227061777420082,225413400819663,223762977823637,222110510197500,220455999702758,
    218799448096947,217140857133640,215480228562467,213817564129124,212152865575390,
    210486134639137,208817373054350,207146582551132,205473764855724,203798921690517,
    202122054774063,200443165821090,198762256542517,197079328645462,195394383833260,
    193707423805475,192018450257911,190327464882626,188634469367947,186939465398477,
    185242454655114,183543438815063,181842419551842,180139398535303,178434377431639,
    176727357903400,175018341609501,173307330205239,171594325342303,169879328668786,
    168162341829196,166443366464473,164722404211995,162999456705593,161274525575564,
    159547612448681,157818718948204,156087846693894,154354997302026,152620172385394,
    150883373553331,149144602411715,147403860562983,145661149606140,143916471136775,
    142169826747067,140421218025799,138670646558370,136918113926805,135163621709766,
    133407171482563,131648764817168,129888403282220,128126088443043,126361821861651,
    124595605096762,122827439703808,121057327234948,119285269239073,117511267261824,
    115735322845595,113957437529552,112177612849635,110395850338576,108612151525904,
    106826517937957,105038951097895,103249452525706,101458023738218,99664666249113,
    97869381568930,96072171205080,94273036661856,92471979440442,90669001038921,88864102952289,
    87057286672462,85248553688288,83437905485553,81625343546996,79810869352315,77994484378179,
    76176190098233,74355987983117,72533879500463,70709866114917,68883949288140,67056130478820,
    65226411142682,63394792732499,61561276698095,59725864486363,57888557541268,56049357303857,
    54208265212273,52365282701756,50520411204659,48673652150454,46825006965743,44974477074264,
    43122063896902,41267768851697,39411593353855,37553538815753,35693606646953,33831798254205,
    31968115041460,30102558409876,28235129757830,26365830480922,24494661971988,22621625621105,
    20746722815604,18869954940071,16991323376365,15110829503617,13228474698248,11344260333967,
    9458187781787,7570258410031,5680473584340,3788834667679,1895343020352]]
private def rkmC_w1024_s0_1 : List ℤ := pzigCat
  [
   [386180544668,1610614391618,4745203734026,11403631958194,23710023012648,44048635568646,
    74630669164366,116949428417240,171258715182118,236210813493426,308771530392552,
    384455856500684,457856560143480,523357748623470,575894216318198,611605899908606,
    628278985993918,625510517823888,604603002490368,568238124704428,520015905187040,
    463951318598586,404008008064492,343730592647306,286001061311726,232924258809094,
    185826365462216,145333616465328,111503499107688,83975398267626,62117390400778,45155976968492,
    32276128490548,22694653476916,15705140046154,10700973540404,7181947090986,4749890432114,
    3096488427470,1990562826258,1262289474374,789763881004,487706085538,297354032978,
    179011326386,106303020916,62448042380,36029145262,20356497170,11218464422,5843189694,
    2709375946,1022381240,250528550]]
private def rkmC_w1024_s0_2 : List ℤ := pzigCat
  [
   [430979756,1553217046,5051632486,13789890922,34735098030,81130009878,177000032484,
    363973140894,709105828032,1315550473070,2334607119466,3976451046550,6519781577342,
    10317491413546,15792647749738,23427870948296,33741249570726,47250885366724,64428718054832,
    85647547687238,111124023847330,140866158349206,174631524679560,211900395334876,
    251873103711660,293490277891800,335478892558576,376420071472606,414834086713728,
    449273992870284,478419490358232,501162698897328,516678429043860,524470194360994,
    524393320717730,516650153474738,501761439710840,480517589671884,453915287921538,
    423086642606518,389225839411082,353520261248650,317091303156456,280946532680460,
    245945532667476,212780658346232,181970714595746,153865395094580,128659002092674,
    106410744515836,87068336324706,70492731466048,56482531332596,44796457335078,35172630197164,
    27344289615570,21052061931790,16052859911008,12125592107506,9074183408114,6728579365942,
    4944284900720,3600813386026,2599385529160,1860247163920,1319929273842,928643215612,
    647883961854,448267014116,307629063498,209424692772,141427049142,94704090626,62818582380,
    41199180462,26643718176,16930780810,10524083166,6356490708,3681077082,1977846206,904334434,
    270794610]]
private def rkmC_w1024_s0_3 : List ℤ := pzigCat
  [
   [351669500,929191254,1969988502,4068280884,8487833632,16584931734,31584672852,58515544318,
    105104297026,183345475276,311560430500,515929879660,833994312242,1317001749032,2033956198918,
    3074743407276,4552933774904,6608997922910,9411168939726,13154671386230,18059443366744,
    24364657088070,32320153108322,42174990443290,54163060883426,68486602981590,85298223114778,
    104682283891010,126637660531352,151063429526598,177748255829434,206364962259732,
    236471964622862,267521868844980,298876710774060,329829621801204,359632314173948,
    387526569078322,412777439669042,434706260109898,452721622716518,466346182341350,
    475237356856818,479200797322896,478196175811324,472335152312230,461871772256268,
    447186199156702,428763247319368,407167363930624,383015670819746,356950659607030,
    329614113557160,301623634488346,273552771763988,245915345665550,219154248372538,
    193634759302756,169642150701394,147383093160394,126990180125982,108528824057876,
    92005802196498,77378781836846,64566204602034,53456974562522,43919500012376,35809776405566,
    28978334811952,23275986259850,18558362169532,14689299479690,11543161564328,9006225538578,
    6977294948556,5367705677532,4100881792078,3111574852706,2344895117808,1755222577298,
    1305070646240,963962740100,707368753888,515733645564,373615070672,268933668158,192330287770,
    136621734468,96343947284,67395086502,46697879852,32117155638,21817069800,14940166672,
    10072509322,6244427714,3432773694,1618807462,518351042]]
private def rkmC_w1024_s0_4 : List ℤ := pzigCat
  [
   [418974206,894302264,1609251376,2999285276,5469924896,9621375824,16645194736,28344948196,
    47288584114,77320212676,124112462896,195780403204,303695734654,463422984218,695859713890,
    1028705618434,1498015825502,2149608864434,3040520562092,4240600276454,5833826274860,
    7918922796458,10609328938742,14032600686030,18328896263084,23648110994000,30145648114694,
    37977066893692,47291662381142,58224897251264,70889875265132,85368396047270,101702168656206,
    119884610464140,139853662257390,161486218187234,184594818496956,208927065450150,
    234167977204326,259945365103850,285838249431074,311388163697160,336112927721332,
    359522232038114,381134268797024,400492626525170,417182648741150,430846428257942,
    441195637334256,448021526315244,451201629417002,450702927900386,446581403707480,
    438978089414430,428111901062074,414269731093986,397794403445296,379071210142618,
    358513660092256,336549252279288,313605620379312,290098120279688,266418454166548,
    242926033167282,219940327284598,197736721551752,176543130056892,156539598768744,
    137859299212804,120590587886108,104781215746466,90442512322544,77554302953040,66070738547142,
    55925161781068,47035258224146,39308037513214,32644239629380,26941214714732,22097211766268,
    18013167175380,14594723502358,11753703842028,9408987806904,7487417180676,5923299927900,
    4658318791194,3642096957000,2831392418884,2188571668338,1681970926700,1285158954188,
    976670188898,738177535132,554788557254,414835174630,308463463794,227827442570,167241170824,
    122130738392,88708040538,64002570030,46171480724,33039235282,23319507482,16274629268,
    11000716462,6973944532,4101591758,2139737182,749807662]]
private def rkmC_w1024_s0_5 : List ℤ := pzigCat
  [
   [363305300,792511806,1403213848,2360085966,3958553250,6616882768,10862426816,17446527134,
    27567151308,43037160892,66370464616,100963022046,151490804122,224418980382,328468126858,
    475074676360,679012814062,959225316684,1339726021460,1850440085304,2528000427506,
    3416580204740,4568725137918,6046016527574,7919408306206,10269189535724,13184574949124,
    16762851375546,21107956014742,26328344768230,32534200409482,39833927033972,48330210247594,
    58115322950060,69266377534290,81839770029906,95866418516092,111346302113332,128244683866986,
    146487999524222,165961694727298,186508898393414,207930517640246,229987579716840,
    252404486237426,274874432840482,297066451510400,318632987423864,339219730334748,
    358475069837016,376060559806182,391660786380082,404993360729050,415816838960806,
    423938497617828,429220081258218,431580909731630,431000458544064,427517820721380,
    421229252240146,412284368413342,400880739283316,387256229509640,371681829732296,
    354452340406728,335878064559460,316275774876178,295959972916218,275235824954544,
    254392186648366,233695541919370,213385914001514,193673284878730,174736326034034,
    156720369720806,139738126194924,123871266607214,109172167517420,95665855961210,
    83353047761428,72214389695524,62213353691170,53298507245408,45408227590240,38473240240028,
    32419370988292,27169683333492,22647346834230,18776800248898,15484674197298,12702135060986,
    10364910037832,8413573560166,6794035554138,5458147902662,4362339741740,3468509939952,
    2743912175388,2159722857852,1691374113690,1318125230256,1022318367208,788858466974,
    605827140792,462869183516,351702079318,265976529060,200152648298,149833185530,111717376704,
    83031281882,61266853508,45118077850,32941665172,23653239856,16751734780,11528540034,
    7498209584,4590748344,2538721624,942439002,240613438]]
private def rkmC_w1024_s0_6 : List ℤ := pzigCat
  [
   [585387640,1128735784,1939387500,3136243328,4903185112,7635579696,11794753802,18105640670,
    27334724036,40838275032,60242921170,88102012204,127522060966,182756165208,259330782320,
    364357573478,507174047508,699422025604,955666505996,1294052484158,1736409396102,
    2309548357298,3045096002334,3980471650592,5159067070674,6630666006132,8451517450680,
    10684389622258,13398281711906,16667368793376,20570701897694,25190227585908,30609296306814,
    36910598983500,44173630746266,52471262067548,61867534661816,72413582565376,84144297712314,
    97075508548844,111200303250196,126486263436172,142873618806284,160272939305388,
    178565126721506,197600727782838,217201504425786,237162516113000,257254989220188,
    277230647493294,296826688939858,315771553474208,333791459204008,350616457702864,
    365988160464300,379665786202502,391432914145006,401102885786000,408523779628720,
    413583101295396,416209548322374,416374861856110,414094202554794,409425868293640,
    402467966454116,393355247351838,382255683355646,369365383197958,354902307676922,
    339100149343134,322203766223130,304461918132206,286121651471296,267423465326106,
    248596527417048,229853922641650,211390152419636,193378909944594,175969970499708,
    159289476624034,143439500687634,128498235238366,114520942984218,101542172827040,
    89576602610640,78621383796122,68659222036004,59659565398304,51581781020754,44377306851896,
    37991544243842,32365423876944,27438411086072,23148909289328,19435816351240,16240235736738,
    13505584260128,11178021287342,9208154376468,7549833410762,6161055443552,5004398970938,
    4046014257288,3256080586280,2608458679484,2080259917884,1651436733988,1305296060042,
    1026944145942,804254816500,627128100124,486651132706,375798833816,289114912728,221330330796,
    168785226560,128234460590,96963177602,73077095518,54809573960,40689463096,30094279492,
    21866283036,15565199192,10795877234,7035097500,4235240964,2313146326],
   [872167368,229077172]]
private def rkmC_w1024_s0_7 : List ℤ := pzigCat
  [
   [224582132,666845910,1171623378,1825494644,2886469850,4400902446,6738263564,10074691844,
    14877428512,21780359018,31712114168,45647193342,65221276664,92401316878,129641879658,
    180476936196,249390133242,341615391342,464465083738,626515117830,838465166156,1113624691264,
    1467917492976,1920473519026,2494003116782,3214994849526,4114544540708,5227897632214,
    6595413302830,8262174121588,10278050460084,12697677602884,15579548880140,18986206965282,
    22982517999960,27635061977650,33010484325668,39173954538098,46187228904022,54106398358356,
    62979863125594,72845603927184,83729371031526,95641451224372,108574993641168,122503947063804,
    137381533509632,153138718651578,169683219699616,186900414645880,204653319126316,
    222783569866610,241113048360364,259448035418074,277581494675216,295296146085234,
    312369887789834,328580560547022,343710272563378,357549967615536,369905628679462,
    380601507543100,389484906698236,396430104879086,401340969870306,404152604809796,
    404833741952118,403386782174620,399847107888516,394282181812926,386789724000342,
    377493966829758,366543348078904,354106704156436,340367727929456,325522188126912,
    309772628336188,293323860782120,276379093803840,259136496074768,241784553482272,
    224500023756420,207445199966708,190765546928276,174588852674550,159024690330070,
    144162900857338,130075134478126,116814591032958,104416888970376,92902135733746,
    82275834944988,72530022841838,63646459691338,55596869520262,48345232317838,41849908101114,
    36064595302050,30939986596500,26425563485508,22469693740526,19021857315198,16032514001498,
    13453766030732,11240616062226,9350852307082,7744979465892,6387389600294,5245078277336,
    4288632335404,3491860650168,2831106898224,2285721528034,1837842271166,1471374822594,
    1173151097942,931431381520,736276998890,579634622684,454416817112,354682237014,275920861804,
    213658007614,164854794646,126784351396,97026757472,74005031590,56228720112],
   [42267763880,31658795578,23281041658,16783299826,11869438610,7937199812,5002035016,2722120754,
    1236922276,416722478]]
private def rkmC_w1024_s0_8 : List ℤ := pzigCat
  [
   [494673234,935079400,1627193062,2418113118,3666167270,5388084844,7840365540,11368896506,
    16318941746,23331653134,32965971574,46265565798,64379374094,89080953388,122313518484,
    166764690980,225893134242,303781143804,405831693454,538413939188,709660550832,929155779224,
    1208631257098,1561911690848,2005396069694,2558476527554,3243383617070,4085956122920,
    5115168127212,6364190822374,7869771555616,9672353892064,11815754339730,14347838992454,
    17319335993946,20782709340880,24792220648168,29403660229204,34671731893372,40648971656162,
    47385270477580,54925816187428,63308944025938,72564345125420,82712305563200,93760364639918,
    105702922062386,118519494493572,132172747894512,146607884290896,161752809610016,
    177516728054738,193790975562364,210449936752814,227351936625066,244340667383836,
    261248680907934,277898739455596,294107053070162,309687345335054,324453940473380,
    338225116262512,350828114080426,362101362829340,371898604480870,380092434901950,
    386576319752618,391267163062234,394107854318458,395066864782992,394139997418608,
    391350040406846,386745434576764,380399550421604,372408931880586,362889893737514,
    351976968672974,339818884368084,326575697623496,312415700716610,297511341046192,
    282035974551890,266161556547506,250054195021306,233872711951582,217766092995138,
    201871188356056,186311728491126,171197107740864,156621000575438,142662514802220,
    129384858977418,116836313325558,105051277768276,94050525548996,83842548608320,74425275085176,
    65786073926694,57904555073966,50753377805354,44299003836408,38504430088540,33328787853660,
    28729450699990,24662884216300,21085000449420,17952408816686,15222994117530,12855943677038,
    10813051155186,9057935268932,7557166387828,6279817706218,5197437863394,4284580787986,
    3518248833826,2877389365922,2344204407868,1902302870148,1537502899076,1237902432796,
    992605229554,792895837202,630879910754,499938363776,394676912984,310412637850,243276992864],
   [190048158204,147730005436,114617271248,88544251576,67991322496,52056260900,39465914764,
    29694877330,21959020966,15911894304,11230793402,7456158016,4605913794,2636197904,1051692218,
    292678214]]
private def rkmC_w1024_s0_9 : List ℤ := pzigCat
  [
   [378440958,817981102,1295290458,1968287790,2893036304,4225655904,6073721002,8687265966,
    12310262140,17300761528,24123395642,33419682288,45995332436,62803148378,85559816746,
    115558650842,154997469094,206747416284,274426118332,361767160988,473797165490,617234421350,
    799659851246,1029380298624,1317433983870,1676702097634,2121774398658,2669577121696,
    3340065998336,4155447235330,5141151137214,6325773705342,7740642424216,9419987589746,
    11401919191686,13726658991956,16436857292882,19577680341652,23195540635208,27337361158086,
    32050916319780,37382242458058,43375301526500,50071125378430,57505823007558,65709375549994,
    74704928402852,84505883102286,95115792952638,106526877771516,118718247983586,131655404727812,
    145289767982108,159557122950302,174378817223422,189661114310032,205295869737150,
    221161856741018,237125673322794,253043226391042,268762921730290,284126511403382,
    298972688144568,313140000910028,326469031609416,338805853060002,350005344523744,
    359933220605110,368469654302406,375511342836594,380972733687134,384789539814714,
    386918279728256,387337877117982,386050267218030,383079382621678,378471026302966,
    372291871348422,364626889353764,355578885620114,345265192481244,333815534827238,
    321369487211284,308073424587750,294077879058642,279535093406786,264595619980616,
    249406876775322,234110220664562,218839004842308,203717883256422,188859651676588,
    174365887668592,160325594143506,146814389900714,133895299298550,121618500056616,
    110021266826894,99129618890440,88958026504502,79511144805366,70784482767772,62765189192226,
    55434302691720,48766369125976,42731769833802,37297238233136,32426580963168,28082234378240,
    24225647120670,20817632018362,17820108329816,15195414796522,12907587723054,10922227446596,
    9206708001130,7731356482934,6467765097272,5390202016910,4475385543410,3701814899740,
    3050581363238,2504450304826,2048493887718,1669270990106,1355078973730,1095973841558,
    883113643764],
   [708848393340,567005888126,451744672772,358755701758,283924157376,223759582988,175929058180,
    137771987622,107525536368,83550897442,64610428578,49795176162,37943256086,28661376828,
    21270927762,15432582408,10882025606,7221273218,4475386114,2594367798,1054058900,299109454]]
private def rkmC_w1024_s0_10 : List ℤ := pzigCat
  [
   [267736228,804756748,1137218742,1475465148,2292586628,3606856980,4924363910,6767915108,
    9627089024,13467805468,18414408796,25308893746,34411914126,46583811018,62948911868,
    84340269544,112059019716,148575940012,195833919482,256570672572,334449095314,433555610594,
    558889313042,717004346644,914766356168,1160891155086,1465709071406,1840923740392,
    2300269270910,2859803006742,3537040237084,4352522841398,5329175348562,6492226768046,
    7869870064660,9492601689530,11393329481596,13607739480586,16173451307522,19129394170286,
    22516732893342,26376462895456,30750038188646,35678585597326,41201132230924,47354428692594,
    54171854571698,61681395160096,69906085494428,78861402709424,88554596112484,98984043016894,
    110137527333760,121991526759248,134510949997652,147647901304578,161341962750490,
    175520076895846,190095932165564,204971951602512,220038691785144,235176980930760,
    250259052934338,265149768701194,279709397736732,293795334298850,307263898892540,
    319974084036692,331788887843194,342577988871380,352221053764974,360608346439142,
    367644333053890,373248718907934,377358189298514,379927700198006,380930926831164,
    380361056270224,378230892107774,374571659283230,369433503619406,362883470038948,
    355004035291360,345892453421796,335657306785716,324417569828672,312299779600504,
    299435508885352,285960029705530,272008714623718,257716124588382,243213160460554,
    228625320947748,214071554169914,199662399914588,185498712024552,171671505759340,
    158260678693370,145335215006406,132952342937916,121158318233094,109988929922100,
    99468626373572,89612851505950,80427764028288,71911224734960,64054371251072,56841374470730,
    50251609262588,44259754991864,38837036907988,33952093918698,29571601320028,25661065634310,
    22185546468376,19109983992010,16400526957080,14023551769436,11947156410482,10141257126964,
    8576885450612,7227717719774,6068708012444,5077143435014,4232512003876,3515657747532,
    2909811910172,2399659379572],
   [1971947278534,1614701281246,1317287893016,1070930686974,867473802290,700228659870,
    563219557484,451405000444,360679375370,287109561924,227846112190,180179046924,142029346486,
    111646764552,87364811116,68043141010,52756761626,40422147580,30861831842,23124401846,
    16875956394,12059790404,8200437184,5367951206,3091508640,1504817038,543074796]]
private def rkmC_w1024_s0_11 : List ℤ := pzigCat
  [
   [444073736,647774486,1014631520,1516610528,2123026050,3214542872,4525242584,6156764070,
    8484979220,11747213696,15952564732,21814820452,29380915848,39331188694,52638768262,
    69930309342,92407574296,121732441216,159125329254,207229276178,268693763216,346417279270,
    444516535052,567553515196,721010517448,911724913780,1147352743534,1436753663816,
    1790846752672,2221296217914,2742283793954,3369667458482,4121083442714,5016647520678,
    6078409879770,7330803992042,8800807935696,10517102527750,12510779951086,14815092797958,
    17464245017536,20494769404002,23943369113200,27847394848236,32244392758988,37170466882382,
    42660240345270,48746147982882,55456811814672,62816865300488,70845383684654,79554958751902,
    88951269512534,99031081587296,109782687996294,121184276329918,133203106259104,
    145796402634124,158909237503110,172475845156042,186419318369670,200651964994140,
    215076294077356,229585533344134,244064930817680,258393554504396,272445118592550,
    286090719479180,299200283834150,311644351426226,323297089252698,334037329862212,
    343751617184236,352335669388328,359696233950542,365753538397146,370441287465440,
    373709548799112,375524584184672,375869247209160,374744004681060,372166519866282,
    368170919518924,362807587090814,356141547582810,348251913755142,339229573872018,
    329175689317104,318200366311714,306419669547806,293954924918094,280929472576546,
    267467189391796,253691306363108,239721079773326,225671705695194,211652087522676,
    197763620225030,184099746748840,170744445844748,157772522062546,145248368667128,
    133226393116792,121751034464888,110856644370326,100568657155942,90902940366590,
    81867473776426,73462728258568,65682322923154,58513943570528,51940151356218,45939232852448,
    40486224143934,35552763531810,31109143183770,27124043737802,23565297894696,20401048314040,
    17598942616886,15128149713480,12958480374358,11060799573374,9408030457762,7974154802778,
    6735325282688,5669122130528,4755122445940],
   [3974749854222,3310792386342,2748344976114,2273497887448,1874134145000,1539584334286,
    1260313165868,1028309261106,836013621080,677357394528,546959078454,440161672418,353180232562,
    282343185368,225056432800,178798664876,141595585938,111840361072,87880387436,68809191568,
    53474764508,41256953256,31541274168,23688280020,17526114056,12510365828,8632625328,
    5633999964,3351987856,1825813032,723967598,205365824]]
private def rkmC_w1024_s0_12 : List ℤ := pzigCat
  [
   [336197768,765797388,1112879998,1631556612,2307880194,3131486974,4435015214,6210131900,
    8347043738,11436310022,15333304416,20668378070,27744244546,36806463944,48798564434,
    64313900774,84237064380,110129761170,143203772430,185203054314,238586616658,305687543050,
    390028072020,495499635588,626408679324,788544362118,987908631760,1232361216068,1530428500290,
    1891965589408,2328779355474,2853761004450,3481584631498,4229124241338,5114681908736,
    6158871465540,7384309815808,8815318733990,10478625509682,12402359379564,14616846533728,
    17153864031810,20045918760600,23327169334610,27031475908490,31193129051410,35845531657686,
    41020751506948,46749115963566,53057794166578,59970343458508,67506142484442,75678578576438,
    84495308817714,93956977508242,104055824840922,114776121861632,126092523700514,
    137970312675692,150364684743012,163220606503518,176473577523334,190048300374628,
    203860688534114,217817981907914,231819065169750,245756732760468,259517687372174,
    272985084089662,286039811469546,298561714431606,310432209592704,321535486703352,
    331761145823494,341005094904774,349172112275412,356177297920238,361947249731528,
    366421631068270,369554206805974,371313243431606,371682817526912,370662183126158,
    368266318127956,364525563613334,359484315533512,353201297300800,345747185671380,
    337204305277842,327664790992488,317228202942046,306001493373608,294095686915438,
    281624763008018,268703892691830,255447234049248,241967315658200,228372429571478,
    214766072444932,201245464653312,187900662445084,174814033143120,162058752742764,
    149699710309442,137792338532158,126382739983820,115508188666422,105196762150578,
    95468603443630,86335522541254,77802316463056,69867203896520,62522116462372,55754301270838,
    49546082316086,43876349460922,38720817179518,34052793788686,29844291920172,26065672496884,
    22687156101964,19678661733812,17010544317542,14653984749658,12580646769916,10763889099772,
    9178104641212,7799423219330],
   [6605509655820,5575351801724,4690048182332,3931925214872,3285290610754,2735792690468,
    2270446095796,1877982242550,1548013777284,1271810013770,1041372814288,849818565184,
    691233652374,560337654656,452745334522,364754471032,292792969610,234496676130,187118877464,
    148781039050,118064306200,93159516122,73270160956,57246770340,44448323804,34164096272,
    25730279070,19164932936,13874489794,9829290306,6637676558,4085604326,2296633212,929364200,
    267384910]]
private def rkmC_w1024_s0_13 : List ℤ := pzigCat
  [
   [224804090,547089724,816355572,1323834140,1928882982,2605695506,3707768474,4966109568,
    6703064874,9236912696,12360237176,16608178054,21953674148,29098200122,38423198016,
    50391069592,65957286158,85855979792,111181448132,143502246370,184285658038,235681604246,
    300179516916,380531333006,480557071592,604050491918,756051278228,942573921092,1169907616284,
    1446118724758,1779959657184,2181684320398,2663055137322,3236997538586,3918662890254,
    4724149354980,5671778415130,6781897084224,8075897953152,9577844597658,11313108588766,
    13308865642370,15593639189396,18197307978362,21150757133072,24485461025202,28233167663198,
    32425519522996,37093177575718,42265656645338,47970092954694,54230965351450,61069773419836,
    68502976602478,76542512743282,85194340340158,94457761944000,104325269696856,114780726094614,
    125800354956238,137351241600612,149391203112758,161869372648552,174724884597154,
    187888513876170,201282160088084,214819476405474,228407301689488,241945787305712,
    255330284185412,268451909493080,281199619028272,293461472639474,305125842529738,
    316084113726804,326231329728578,335468672786394,343704619847712,350856229983014,
    356851438225616,361629284349464,365141584050434,367353238508498,368243212227564,
    367805110042352,366046250543792,362988574220798,358667483517828,353131454982144,
    346441185963468,338668072055168,329893809903316,320208003534734,309707362024982,
    298493883250754,286672945914498,274352371057068,261639996160182,248642978621498,
    235465755122606,222208866479156,208968279870490,195833559040354,182887886459240,
    170206544385536,157857058808538,145898628528136,134381767706480,123348526534374,
    112832647579110,102859578161398,93447493337784,84606685697420,76341180719958,68648851379596,
    61521791783202,54947987669414,48910369006874,43389035656638,38361223096152,33801596464552,
    29683927257700,25980207593234,22662327366748,19701915960266,17070890266058,14741952775576,
    12688152704544],
   [10884301022864,9305850046646,7929878578818,6735119242788,5701386900710,4810507949858,
    4045298347094,3390629533508,2832611158190,2358517552390,1957404621086,1619034229018,
    1334855413836,1096909812568,898333643246,733413152862,596752422582,484176303652,391534002638,
    315605952852,253670917008,203182715416,162415846236,129315766854,102617644148,81036623270,
    63532572642,49570417022,38222694194,29251823812,22015520784,16206707790,11661627954,
    7931600446,5170830978,2985865330,1471499976,541428090]]
private def rkmC_w1024_s0_14 : List ℤ := pzigCat
  [
   [372139738,585593968,1047617186,1398795880,1945796640,2786723436,3780579646,5265785874,
    6961138358,9420686674,12581015454,16581886572,21972869708,28978784402,37946823066,
    49577818306,64441435618,83379833582,107460188948,137997108458,176504230126,224590396974,
    284810322040,359625669124,452196139326,566485913926,706533378604,877893862210,1086331142594,
    1338681076404,1643293524804,2008991490068,2446494979770,2967373138984,3584859462650,
    4314006887294,5170731675514,6173377084926,7341693782872,8697112104898,10262823845132,
    12063283511332,14124882153760,16474952255486,19142229122450,22156059975186,25546165007904,
    29342879626338,33575488907146,38272843651650,43462286738558,49168938761670,55415530272004,
    62220953879432,69600444215992,77564087572362,86116490263856,95256257917634,104974805418634,
    115256693444862,126078113099790,137407186202818,149203744995518,161418648538778,
    173994414946160,186864726160986,199955734131678,213185983095074,226466856263960,
    239704234883496,252798686261650,265647517732366,278145184974870,290185323830218,
    301662120936064,312471691197754,322513835891622,331693592143616,339922388929434,
    347120088650170,353215533374268,358148384662936,361869879463952,364343221882512,
    365545293618702,365465577727714,364107436139868,361487531578994,357635116180798,
    352592771554882,346413922768968,339163230327014,330915041179222,321751732046878,
    311763318895064,301044775235366,289695598926176,277817696593870,265514125426424,
    252887742414602,240039184188112,227066854503984,214064486809114,201120924548362,
    188319124157986,175734813546020,163436989026348,151486477776708,139936554861420,
    128832154466818,118210086738124,108099886651474,98522939806290,89494015862048,81020868425176,
    73105164769932,65743161113192,58925679971248,52639865214060,46868574577232,41591794981398,
    36787026858036,32429649124212,28494199188730,24953678550338,21781146114316,18949431581566,
    16431649419062],
   [14201830579222,12234278973032,10504965400296,8990635887562,7669529776152,6521356050902,
    5526875785386,4668935731204,3931289189362,3299499665822,2760309489672,2301595072776,
    1912964175826,1584651097082,1308531497848,1077053602072,883625914114,722710282864,
    589067075334,478747292846,387849077708,313301778430,252425883770,202655392358,162299510260,
    129398085954,102800928536,81301133862,63868575922,49954678894,38606945060,29594986238,
    22294263094,16419343072,11823995064,8053642886,5264466602,3050187702,1508657372,556888660]]
private def rkmC_w1024_s0_15 : List ℤ := pzigCat
  [
   [295696196,548295726,832893020,1321650706,1761370172,2589829690,3532666726,4712065320,
    6359204354,8392296308,11274122450,14897683688,19578972514,25731409004,33590614776,
    43744027240,56601564772,73167914878,94132557510,120449041760,153706291718,195197763312,
    247054857180,311435040978,390970884474,489086696218,609329987160,756234522856,934748066260,
    1151004058154,1412028957790,1725436777898,2100453716114,2547078044170,3076894615182,
    3702848492392,4439096653816,5301791548458,6308115988810,7477313395728,8829821417114,
    10387881460854,12175259277348,14216883215508,16539032358964,19169151317264,22135194356644,
    25465735184268,29189219115782,33334061837718,37927887631720,42996483749316,48564405685380,
    54653226394194,61281665309742,68464566483740,76211848591684,84529167889118,93415647487826,
    102864523068634,112862160855128,123387036329468,134410685469732,145895903538414,
    157797772506318,170063195205172,182630723972018,195431726725846,208389804900500,
    221422300408818,234440315227918,247350123466996,260054264304488,272451997166938,
    284441831352880,295921659231892,306791044866492,316952507282810,326312334531448,
    334783069743084,342283899774364,348742793469818,354096980948800,358294143421482,
    361293855028372,363067095424444,363597907939292,362882726661712,360930775325790,
    357764116635186,353416577602868,347934104394236,341372795547616,333798932942326,
    325287641930900,315921180571714,305788411026914,294982403385266,283600132973082,
    271740283295668,259502005018050,246984094950282,234282763030732,221491575036750,
    208699443230732,195990345830030,183442452925582,171126811695486,159107927102530,
    147442374961998,136179542574946,125360999511984,115020437953526,105184637299994,
    95872711953436,87097571243190,78865447885020,71176806940414,64027183684118,57406947757532,
    51302971283048,45698116207542,40572674816116,35904700117422,31670149949858,27844239294694,
    24400777668974,21313724662642],
   [18556849646958,16104160240998,13930601031874,12011335366074,10323147870390,8843574411880,
    7551636556230,6427830165266,5453573029284,4612250950998,3888067607060,3267049423448,
    2736439075602,2284544751376,1901308183836,1577159867862,1304144469910,1074902162256,
    883055700326,723278702506,590451792272,480693658420,390115174360,315669816930,254733466164,
    204796983124,164242226918,131135504402,104345291754,82660605488,65041451850,50949878474,
    39427902752,30263914420,22830552110,16842849166,12155164444,8298208802,5437693636,3156997408,
    1563861642,577788586]]
private def rkmC_w1024_s0_16 : List ℤ := pzigCat
  [
   [294539334,615777976,1044400116,1444688040,2131386654,2793146184,3796793648,5132039102,
    6878188708,9125049752,11997335968,15806535554,20755116174,27027911432,35162908224,
    45555196416,58808310466,75667486938,96734856732,123374583112,156710605882,198343018670,
    250178733408,314138603360,393218489334,490097472022,608541201324,753011246306,928087015336,
    1139828410150,1394434347750,1699640580436,2064125888288,2497167623040,3010097963146,
    3614958058756,4325485370582,5156684900774,6124922712460,7248534487046,8546873930840,
    10041220006064,11753873515638,13708736023514,15931062927008,18446600020160,21282571162476,
    24466091225978,28024771696494,31986202149616,36376951763884,41222950823330,46547970517744,
    52374037733836,58720153333820,65601838239732,73030992959650,81014242467824,89553604267260,
    98644875829628,108277444970478,118434101536356,129090001452856,140213278465740,
    151763706750752,163693626411920,175947699545658,188462676826686,201168618999706,
    213988286868580,226838823181800,239631896052540,252274819701824,264672025283842,
    276725219710402,288335906056918,299405751096908,309838390568658,319540809848934,
    328424228392316,336406550691114,343412390257158,349375111975290,354237535908434,
    357952706776462,360485354811600,361811339154236,361919170390180,360809330214786,
    358494494227778,354999665227928,350360942410484,344626008262094,337852145647786,
    330106019177216,321462515487926,312003114875806,301815481852902,290990909543672,
    279624071922726,267811121978032,255648403619400,243231699891788,230654001064940,
    218005623325354,205372240174032,192834514587948,180467421280730,168338993138480,
    156510992191860,145037423680772,133965272451710,123334026153954,113175589307106,
    103515277944698,94370956720734,85754530713438,77671496249776,70121790439098,63100667422748,
    56598391394272,50601939941872,45094408057060,40056395353820,35466372356658,31300810044890,
    27535579578452,24145158839760],
   [21104131982482,18386838198376,15967842819164,13822731570274,11927315695836,10258997962114,
    8795813411486,7517188956660,6404014515464,5438101946806,4603263435068,3884062735104,
    3266809504914,2738945931752,2288926868462,1906861523810,1583339441732,1310579445254,
    1081349768404,889352747940,729308706086,596106418968,485894548642,394804765180,319829585358,
    258379049534,207958276370,166967270132,133461759366,106314317742,84308566566,66402508004,
    52065429238,40329493780,30988547960,23402971892,17283952470,12483934600,8525941076,
    5584969230,3239002442,1601819198,590701610]]
private def rkmC_w1024_s0_17 : List ℤ := pzigCat
  [
   [276034062,674900020,1026844724,1460172640,2067757816,2722435996,3825411252,5080957294,
    6729178508,8900413742,11673756810,15360150502,19976987748,26158973868,33955082972,
    43785861216,56371370062,72142853746,92272064942,117407246574,148809051844,188064562404,
    236650820950,296792249762,370645461438,461341698674,572173890508,706949510166,870473111520,
    1067657838952,1304895574208,1589068794024,1928066618238,2331045202916,2807915308732,
    3370378882966,4030880488652,4803583972550,5703996270326,6748775395392,7956676805528,
    9347306118726,10942063694372,12763473048160,14835280941282,17182644764872,19830977814100,
    22806995050982,26137392847704,29848972012230,33968309181400,38520732732288,43530865509344,
    49020952285204,55011256154122,61519032004314,68557681527136,76137015691460,84261578911984,
    92931081394890,102138983142932,111872359390992,122111935431672,132830750953814,
    143994991784394,155562838411404,167485190486456,179705604185452,192159928755054,
    204777721759734,217481659143984,230189215674046,242812882062096,255261058246690,
    267439757989722,279252656772762,290603513675446,301396574278684,311538351115784,
    320939087650446,329513283068714,337182177139192,343873871619674,349525279317038,
    354082709118564,357502389046326,359752098294864,360810547020070,360668792590002,
    359329533653626,356807267399988,353128523797296,348330470910496,342461441579556,
    335579004749422,327749732194090,319048063052042,309554575278666,299355748922266,
    288541474055332,277204838032756,265440232148378,253342025960012,241003963242972,
    228516931326940,215969152528082,203444232465032,191020810518250,178771960267566,
    166763892338636,155056705112330,143702907328042,132748198086578,122230981021804,
    112182194263490,102626341045092,93580624850380,85056519146662,77059277508280,69588697719164,
    62639965161650,56203325026042,50265886799210,44811019085150,39819704142636,35270814503634,
    31141173804802,27407005446276],
   [24043157510154,21024660293650,18326322612442,15923147620284,13791097528452,11906283440136,
    10246403282614,8789786250136,7516174660774,6406755343858,5443579810328,4610649625576,
    3892656839508,3276034557376,2748341942180,2298158236240,1915712752706,1591681026320,
    1318347708162,1088506295696,895876795954,735189425846,601343726352,490509240088,398828107878,
    323308687348,261362490648,210495318536,169105716526,135244221234,107785865782,85509737492,
    67374745220,52844352476,40944858070,31464122716,23755322758,17529294598,12636878086,
    8606526120,5614291330,3240345450,1594236946,585113094]]
private def rkmC_w1024_s0_18 : List ℤ := pzigCat
  [
   [338158030,503401100,844605300,1306877860,1866761954,2624977192,3396293032,4588430976,
    6035217770,7984082146,10584601214,13781570682,18118561234,23531444560,30480302458,
    39307218368,50454786642,64766222098,82627574092,105188904362,133304794166,168237273420,
    211738809744,265379072942,331575969262,412623877690,511729270762,632495585430,778765638010,
    955597588434,1168235329238,1423234598878,1727742672692,2089879050544,2519178802494,
    3025734122080,3621476579886,4319173527706,5133130330684,6079199709704,7174273125832,
    8437234241514,9887705602440,11547091575692,13438044652422,15584158694528,18010431788180,
    20742034149080,23805331606896,27226620299750,31032058539084,35247563088018,39897628817592,
    45006012893988,50594013037686,56680735615274,63282332979120,70411006066368,78075317181592,
    86278411924336,95018592029218,104288086009222,114072676762178,124351876342774,
    135097602280148,146275114044678,157841769157452,169747635820864,181935730246792,
    194341633318456,206894908946946,219518372377156,232129809357622,244642370692270,
    256965334265568,269005834270232,280668816753630,291859510588734,302483823997584,
    312450016158648,321670244326954,330060999238366,337545580333696,344054102787462,
    349525406731208,353907717252070,357159080214322,359248976833230,360157591551150,
    359877258974908,358411801417402,355776640887498,351999036261750,347116607244342,
    341177903356054,334240469813728,326370627111188,317642384615796,308135714155006,
    297936370135294,287133360484990,275818759916892,264085856878680,252027881390450,
    239737448548626,227304278776900,214815396560438,202353193518866,189995171543834,
    177813395931338,165873172222488,154233759379232,142946848040892,132057408250234,
    121603250912222,111614887554268,102116510581068,93125047474866,84651723971602,76701585985470,
    69274344233162,62365215839568,55964565756248,50059651832304,44633966904080,39668629654378,
    35142669134202,31033133732534],
   [27316508937716,23967903790108,20962585020608,18275540601170,15881947990646,13757935490112,
    11879807625542,10225464884608,8773416019694,7503564349088,6397201315726,5436474067842,
    4605459999294,3888933733076,3273422997848,2746563635504,2297017838602,1915058327260,
    1591399288156,1318344609418,1088696401600,896196722082,735578225068,601764815296,
    490930148010,399226766308,323672345300,261673539194,210752773050,169301321278,135384449236,
    107876866520,85556307788,67388742554,52820791400,40889514138,31369428630,23622317860,
    17365797976,12449599456,8423090832,5448367824,3117038340,1520232134,553706758]]
private def rkmC_w1024_s0_19 : List ℤ := pzigCat
  [
   [421249814,687454066,1092710164,1591330150,2117309232,2918044768,3758937128,5088576074,
    6804836822,8952477502,11790754552,15271302436,19957594526,25822379302,33337535088,
    42964325944,55015344292,70406353462,89573498900,113659654712,143659903434,180846235004,
    227072759108,283901134940,353861976360,439416789318,543746865262,670571721096,823814060850,
    1008738031286,1230758923386,1496500679734,1813251316470,2189179790624,2634042019932,
    3158099743442,3773389302938,4492836216914,5330858741184,6303487831002,7427612172940,
    8722145075858,10206814296926,11903036166514,13833437932006,16021480126718,18492138495348,
    21270476464570,24382578754608,27854436146780,31711863942290,35980472632362,40684282221278,
    45846528598942,51488041619650,57627407847924,64280186264244,71457816036090,79168144144350,
    87413665424272,96192040277822,105494865056188,115307247607838,125608100372316,
    136368763097746,147553985589082,159120716178636,171018683962526,183190666469610,
    195572054331568,208092367325296,220674532683178,233236568670918,245691942954796,
    257950299315328,269919271507564,281504431256986,292611742424612,303147904998072,
    313022009325360,322147112373200,330440651361728,337826908501910,344236971022754,
    349610630648612,353897017914376,357055023619144,359054918143266,359877627906288,
    359516199090222,357975081257702,355270209760348,351429212598290,346489979569108,
    340501271661384,333520766222162,325614818142830,316857320256408,307328045165570,
    297112510431180,286299482314740,274980767985262,263249277404842,251197787561408,
    238918400714974,226500363263536,214030272405986,201590084368044,189256847565822,
    177102105355774,165190678842784,153581400507322,142325620457810,131468029365168,
    121046124621076,111090110344456,101623845544762,92663992263222,84221585147668,76301523060090,
    68903420829892,62022356502204,55648583452488,49769249118518,44367786070020,39425321026976,
    34920889864504,30831588266230],
   [27133896363796,23802927645686,20813954173760,18141975459958,15762243020440,13650936535280,
    11784453446820,10140749453590,8698379195142,7437300286360,6338826075914,5385181016744,
    4560489128674,3849607229504,3239135868830,2716759486454,2271214630126,1892792300240,
    1572265348646,1301961656688,1074716459252,884319131854,725510157156,593268226588,
    483769990504,393205493954,318617177036,257421980670,207190427080,166306906776,132878966390,
    105779123408,83793622568,65908416118,51550179022,39794514606,30400643992,22761538896,
    16609135390,11791173830,7891518614,5038998930,2846121292,1371156704,494209482]]
private def rkmC_w1024_s0_20 : List ℤ := pzigCat
  [
   [531584576,786803080,1142134118,1664218992,2208165964,3090024156,4047814442,5447386198,
    7230323720,9417908422,12381969796,16037466960,20933221512,27063200660,34857131532,
    44879630136,57407451710,73343406214,93115965588,117920753176,148895852808,187252381828,
    234837090944,293229418858,365028267198,452751268554,559556026100,689296314808,845969457346,
    1034862413948,1261384825878,1532207936844,1854782628748,2237312249962,2689590166736,
    3221952004702,3846560148002,4576443099368,5425995552290,6411293045710,7549299335976,
    8859009685480,10360175863938,12074202020406,14023786982772,16232440797954,18725142186788,
    21526870961138,24663603510320,28161262213082,32045590828896,36342140987182,41074830772258,
    46266741935868,51938491888694,58108423252414,64791878820224,72000087829572,79740655367598,
    88015776348360,96822795858014,106153021279416,115991292351176,126316219444188,
    137098797104940,148303421259986,159886712893310,171798121280258,183980144705852,
    196367911628554,208890685016814,221471159006180,234027157896164,246471968176406,
    258715115920908,270664135000920,282224536812102,293302253396298,303803989110838,
    313638949160338,322720352834134,330965863763376,338299973279912,344653984022472,
    349967984444856,354191460790000,357283769584226,359215630255936,359968427967068,
    359535693271312,357922398578388,355145105251908,351232027811370,346221629327142,
    340163169232168,333114811002020,325143464397516,316323560046900,306735429478322,
    296465020322466,285601458088346,274236866740432,262464431059910,250377240807900,
    238067592864250,225624863878080,213135643991422,200681799635514,188340301253782,
    176182553240960,164273270606138,152671064773740,141427001686694,130585426405222,
    120183420422214,110250832845240,100811112076014,91880552456180,83469769552802,75583205611746,
    68220052911156,61374927875646,55037733701056,49195260259766,43830639633460,38924722304562,
    34456232310928,30402033245738],
   [26738334269422,23440078562370,20482390361134,17840153240250,15488576384694,13403747532022,
    11562057555972,9941413162718,8520368942836,7278918582748,6198391370936,5261118411668,
    4451269168368,3753812244398,3155432689186,2643888145074,2208034754766,1838210194766,
    1525310055802,1261720532712,1040361163962,855112239282,700751864204,572367863480,
    466164053352,378420101534,306235307582,247067381078,198572429624,159134800076,126936545896,
    100852108568,79696566372,62497416082,48670668638,37364774298,28327289318,21005279526,
    15149538074,10599194558,6998655378,4341377538,2544011912,1049464956,302356370]]
private def rkmC_w1024_s0_21 : List ℤ := pzigCat
  [
   [450678140,757360554,1162379300,1710938256,2234465020,3140662560,4156128910,5553923344,
    7314122318,9491577828,12512864934,16233590798,21181308946,27398817464,35277353838,
    45363777548,57927755918,73961869582,93935651684,118967674068,150164086160,188750053592,
    236639744334,295406073752,367615090874,455824776330,563242003326,693747139678,851299549296,
    1041175914298,1268838521876,1541010537882,1865175240098,2249551711510,2703978776624,
    3238866547332,3866439504742,4599768872012,5453281890394,6443089110092,7586235064594,
    8901836248650,10409797634108,12131657229524,14090176711428,16308927454926,18812972183938,
    21627449312238,24778507978026,28292192504364,32194363439470,36510664301808,41265152811792,
    46481023275762,52178957140014,58377342453318,65091511875086,72332718222890,80108531898296,
    88421085348160,97267613551046,106639219046802,116520516024798,126889773867976,
    137717635785502,148968086798696,160597266378018,172554102116716,184780437679740,
    197210763885736,209773652217814,222391103739072,234980213518696,247453427536784,
    259719475551734,271685080995772,283255079364628,294334778065770,304830264241350,
    314650210379620,323707318164160,331918949143160,339209400224126,345509916875064,
    350760649326208,354911201716706,357921297753488,359762159877806,360415915427694,
    359876945635456,358151114434690,355256007255202,351220887283378,346085474135906,
    339900333375414,332724981555406,324627685804850,315684120132408,305975917480686,
    295590235164584,284617431205334,273150763132316,261284366664590,249112176546622,
    236727080840298,224218997964638,211674892446652,199176892335920,186802114604468,
    174621862406172,162700672209712,151096751937952,139860713891026,129036358171870,
    118660103907366,108761130247890,99362038363238,90478297044618,82119610964680,74289524775208,
    66986404189242,60203998780112,53931476438404,48154835584468,42856504842324,38016669778178,
    33613409747078,29623099702676],
   [26021447995692,22783054283768,19882731796382,17295079056782,14995191643836,12958876100470,
    11162623178304,9584049026050,8202017162268,6996268297432,5948474968542,5040994302552,
    4257985949300,3584982471328,3008272194448,2516269768850,2097810277270,1743218566280,
    1443980305014,1192190958858,981264138372,804976302526,658386539940,536806295690,436181820580,
    353413084416,285355637784,229739233958,184237007374,147158119442,117158573282,92731621598,
    73025578454,56919965802,43903120410,33460816192,25026209822,18424949312,13079578914,
    8952016072,5767047812,3370523508,1790702298,692059722]]
private def rkmC_w1024_s0_22 : List ℤ := pzigCat
  [
   [419640834,717879774,1116766352,1699489066,2248801900,3113976302,4049137690,5396591516,
    7171801132,9370030788,12363771610,16025523524,20907006238,27050574570,34824546286,
    44779124038,57222821836,73140089416,92970317400,117799257478,148726739378,187013374786,
    234571967672,292984783746,364802715530,452571379962,559517988450,689516902078,846556600018,
    1035890389986,1262974591458,1534577749006,1858247746274,2242324063490,2696664751058,
    3231695020052,3859663993800,4593728365258,5448509344210,6440257504850,7586197532638,
    8905583822766,10418503577950,12146738740830,14113257544620,16341919256666,18858023997476,
    21687019718534,24855379675872,28389450831196,32315461995974,36659331112250,41445436155224,
    46697208004758,52435540936086,58679058478766,65443225446684,72739445614176,80575252353448,
    88952677086974,97868766732084,107314314651914,117273600121952,127724305323946,
    138636398157178,149973007866824,161689333066208,173733336130840,186045689852518,
    198559658782164,211202362835856,223894327934746,236551174698400,249083831681728,
    261399600427214,273403665064154,284999453085944,296090940542600,306583054000236,
    316383548628740,325404268302726,333561983606074,340780522387422,346990993971578,
    352133757723134,356158883430098,359026933226808,360710088234690,361191756445420,
    360467813399138,358545874877678,355445577181336,351198300781188,345846072125606,
    339441753421056,332047198729410,323733147826762,314577559711228,304664587764956,
    294083391465980,282926574243264,271288943934118,259266411188508,246954103132698,
    234446055733518,221833136208180,209202600344836,196637214854806,184213654730548,
    172003244310800,160069953109702,148471042259454,137256704658618,126469100419684,
    116143793493976,106308471470462,96984064007284,88184903196088,79918785139576,72188079840108,
    64989461691182,58315372988222,52153682003838,46488802211524,41302435092296,36573273778744,
    32278660589056,28394189720780],
   [24894699629364,21754480505606,18947504795330,16448419499844,14231773319152,12273257585892,
    10549358167144,9037679614830,7717103008786,6567663672256,5570885201614,4709890075002,
    3968619962004,3333041795292,2789907242010,2327508432982,1935568580080,1604151455732,
    1325226799468,1091243366776,895636257762,732829929360,597621247280,485883038530,393616726074,
    317886799640,256004876444,205396948442,164240910532,130646352906,103479915128,81466933686,
    63589168204,49198206690,37564437376,28230242922,20965791732,14950861508,10379796488,
    6886553918,4168753560,2281117116,889637624,245620598]]
private theorem rkmHbEq_w1024_s0 : muxIntListEq (uHb rkmPhb_w1024_s0)
    (altBuildHbFrom 1024 1024 29614734693 0 1024) = true := by decide +kernel
private theorem rkmHhb_w1024_s0 : uHb rkmPhb_w1024_s0 = rkmDropInts 0 rkmHbWin_w1024_s0 :=
  (muxIntListEq_eq_true.mp rkmHbEq_w1024_s0).trans
    (drHb 1024 1024 29614734693 0 1024)
private theorem rkmWC_w1024_s0_0 :
    bWinChk 0 68 100000000 1024 rkmPhb_w1024_s0
      0 rkmXsWin_w1024_s0_in 0 rkmC_w1024_s0_1 2964874089 = true := by decide +kernel
private theorem rkmWC_w1024_s0_1 :
    bWinChk 0 32 100000000 1024 rkmPhb_w1024_s0
      0 rkmC_w1024_s0_1 2 rkmC_w1024_s0_2 1294946651 = true := by decide +kernel
private theorem rkmWC_w1024_s0_2 :
    bWinChk 0 23 100000000 1024 rkmPhb_w1024_s0
      2 rkmC_w1024_s0_2 10 rkmC_w1024_s0_3 2596446780 = true := by decide +kernel
private theorem rkmWC_w1024_s0_3 :
    bWinChk 0 19 100000000 1024 rkmPhb_w1024_s0
      10 rkmC_w1024_s0_3 20 rkmC_w1024_s0_4 2646909386 = true := by decide +kernel
private theorem rkmWC_w1024_s0_4 :
    bWinChk 4 17 100000000 1024 (drN 4 rkmPhb_w1024_s0)
      20 rkmC_w1024_s0_4 31 rkmC_w1024_s0_5 2473498056 = true := by decide +kernel
private theorem rkmWC_w1024_s0_5 :
    bWinChk 15 16 100000000 1024 (drN 15 rkmPhb_w1024_s0)
      31 rkmC_w1024_s0_5 44 rkmC_w1024_s0_6 2786033986 = true := by decide +kernel
private theorem rkmWC_w1024_s0_6 :
    bWinChk 28 15 100000000 1024 (drN 28 rkmPhb_w1024_s0)
      44 rkmC_w1024_s0_6 56 rkmC_w1024_s0_7 2695852261 = true := by decide +kernel
private theorem rkmWC_w1024_s0_7 :
    bWinChk 40 15 100000000 1024 (drN 40 rkmPhb_w1024_s0)
      56 rkmC_w1024_s0_7 71 rkmC_w1024_s0_8 3030402910 = true := by decide +kernel
private theorem rkmWC_w1024_s0_8 :
    bWinChk 55 14 100000000 1024 (drN 55 rkmPhb_w1024_s0)
      71 rkmC_w1024_s0_8 85 rkmC_w1024_s0_9 2660212565 = true := by decide +kernel
private theorem rkmWC_w1024_s0_9 :
    bWinChk 69 14 100000000 1024 (drN 69 rkmPhb_w1024_s0)
      85 rkmC_w1024_s0_9 100 rkmC_w1024_s0_10 2032630267 = true := by decide +kernel
private theorem rkmWC_w1024_s0_10 :
    bWinChk 84 13 100000000 1024 (drN 84 rkmPhb_w1024_s0)
      100 rkmC_w1024_s0_10 115 rkmC_w1024_s0_11 2085917728 = true := by decide +kernel
private theorem rkmWC_w1024_s0_11 :
    bWinChk 99 13 100000000 1024 (drN 99 rkmPhb_w1024_s0)
      115 rkmC_w1024_s0_11 131 rkmC_w1024_s0_12 2137386858 = true := by decide +kernel
private theorem rkmWC_w1024_s0_12 :
    bWinChk 115 13 100000000 1024 (drN 115 rkmPhb_w1024_s0)
      131 rkmC_w1024_s0_12 147 rkmC_w1024_s0_13 2501636719 = true := by decide +kernel
private theorem rkmWC_w1024_s0_13 :
    bWinChk 131 12 100000000 1024 (drN 131 rkmPhb_w1024_s0)
      147 rkmC_w1024_s0_13 163 rkmC_w1024_s0_14 1999687056 = true := by decide +kernel
private theorem rkmWC_w1024_s0_14 :
    bWinChk 147 12 100000000 1024 (drN 147 rkmPhb_w1024_s0)
      163 rkmC_w1024_s0_14 179 rkmC_w1024_s0_15 2138478813 = true := by decide +kernel
private theorem rkmWC_w1024_s0_15 :
    bWinChk 163 12 100000000 1024 (drN 163 rkmPhb_w1024_s0)
      179 rkmC_w1024_s0_15 196 rkmC_w1024_s0_16 2359795743 = true := by decide +kernel
private theorem rkmWC_w1024_s0_16 :
    bWinChk 180 12 100000000 1024 (drN 180 rkmPhb_w1024_s0)
      196 rkmC_w1024_s0_16 213 rkmC_w1024_s0_17 2258394173 = true := by decide +kernel
private theorem rkmWC_w1024_s0_17 :
    bWinChk 197 12 100000000 1024 (drN 197 rkmPhb_w1024_s0)
      213 rkmC_w1024_s0_17 230 rkmC_w1024_s0_18 2245018411 = true := by decide +kernel
private theorem rkmWC_w1024_s0_18 :
    bWinChk 214 12 100000000 1024 (drN 214 rkmPhb_w1024_s0)
      230 rkmC_w1024_s0_18 248 rkmC_w1024_s0_19 2122034458 = true := by decide +kernel
private theorem rkmWC_w1024_s0_19 :
    bWinChk 232 12 100000000 1024 (drN 232 rkmPhb_w1024_s0)
      248 rkmC_w1024_s0_19 266 rkmC_w1024_s0_20 2324779473 = true := by decide +kernel
private theorem rkmWC_w1024_s0_20 :
    bWinChk 250 12 100000000 1024 (drN 250 rkmPhb_w1024_s0)
      266 rkmC_w1024_s0_20 284 rkmC_w1024_s0_21 2607817040 = true := by decide +kernel
private theorem rkmWC_w1024_s0_21 :
    bWinChk 268 12 100000000 1024 (drN 268 rkmPhb_w1024_s0)
      284 rkmC_w1024_s0_21 302 rkmC_w1024_s0_22 2274624440 = true := by decide +kernel
private theorem rkmWC_w1024_s0_22 :
    bWinChk 286 12 100000000 1024 (drN 286 rkmPhb_w1024_s0)
      302 rkmC_w1024_s0_22 320 rkmXsWin_w1024_s0_out 2133630289 = true := by decide +kernel
private theorem rkmWinIter_w1024_s0 :
    RkmWinIterSound 392 1024 rkmHbWin_w1024_s0 0 rkmXsWin_w1024_s0_in
      320 rkmXsWin_w1024_s0_out 54371008152 :=
  rkmChS 392 54371008152 (rkmChS 380 52237377863 (rkmChS 368 49962753423 (rkmChS 356 47354936383
    (rkmChS 344 45030156910 (rkmChS 332 42908122452 (rkmChS 320 40663104041 (rkmChS 308
    38404709868 (rkmChS 296 36044914125 (rkmChS 284 33906435312 (rkmChS 272 31906748256 (rkmChS
    259 29405111537 (rkmChS 246 27267724679 (rkmChS 233 25181806951 (rkmChS 219 23149176684
    (rkmChS 205 20488964119 (rkmChS 190 17458561209 (rkmChS 175 14762708948 (rkmChS 159
    11976674962 (rkmChS 142 9503176906 (rkmChS 123 6856267520 (rkmChS 100 4259820740
    (bWinChk_sound rkmHhb_w1024_s0 rkmWC_w1024_s0_0) rkmHhb_w1024_s0 rkmWC_w1024_s0_1 rfl rfl)
    rkmHhb_w1024_s0 rkmWC_w1024_s0_2 rfl rfl) rkmHhb_w1024_s0 rkmWC_w1024_s0_3 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_4 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl)
    rkmWC_w1024_s0_5 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_6 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_7 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl)
    rkmWC_w1024_s0_8 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_9 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_10 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl)
    rkmWC_w1024_s0_11 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_12 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_13 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl)
    rkmWC_w1024_s0_14 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_15 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_16 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl)
    rkmWC_w1024_s0_17 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_18 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_19 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl)
    rkmWC_w1024_s0_20 rfl rfl) (drHbSub rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_21 rfl rfl) (drHbSub
    rkmHhb_w1024_s0 rfl) rkmWC_w1024_s0_22 rfl rfl
/-- Certified `w1024` seg `0` (`392` steps). -/
theorem rkmWinSegWalkSnd_w1024_s0 :
    RkmWinSegWalkSound 392 ⟨1024, rkmHbWin_w1024_s0, 0, rkmXsWin_w1024_s0_in,
      320, rkmXsWin_w1024_s0_out, 54371008152⟩ :=
  @rkmSegWalk_mk 392 1024 0 320 54371008152 rkmHbWin_w1024_s0 rkmXsWin_w1024_s0_in
    rkmXsWin_w1024_s0_out (rkmw_buildHbFrom_length 1024 1024 29614734693 1024 0)
    rfl rkmWinIter_w1024_s0
/-- Cumulative `w1024` part `0` lane witness. -/
theorem rkmHiLane_w1024_wint0 : @rkmWinSegWalkSnd_w1024_s0 = @rkmWinSegWalkSnd_w1024_s0 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi1024T9) rfl).right

end
end QuantumComputation.Specs.DickeSol
