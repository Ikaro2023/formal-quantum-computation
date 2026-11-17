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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T2
/-
 High-m Coupled Walk Part 3 (FindAllJohnsonRampKickMuxHi128T3, 67868 coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi128T3`). -/
def rkmWordBitsHi128T3 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi128T3 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi128T3`). -/
def rkmUnpackMaskHi128T3 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi128T3 n w ++ rkmUnpackMaskHi128T3 ns ws
/-- Mask segment `0` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s0 : List Bool := rkmUnpackMaskHi128T3 [1] [1]
/-- Mask segment `1` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s1 : List Bool := rkmUnpackMaskHi128T3 [50,50,50,8] [68719418496,0,
 2194728288256,252]
/-- Mask segment `2` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s2 : List Bool := rkmUnpackMaskHi128T3 [50,50,50,50,50] [0,1099511627776,
 132,68987912208,998765438918344]
/-- Mask segment `3` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s3 : List Bool := rkmUnpackMaskHi128T3 [50,50,50,50,50,3] [2513128,0,
 1099511627776,140737505132544,397289843590145,4]
/-- Mask segment `4` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s4 : List Bool := rkmUnpackMaskHi128T3 [50,50,50,50,50,4] [80749864,0,
 4947835879424,4398046773248,721279627821056,8]
/-- Mask segment `5` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s5 : List Bool := rkmUnpackMaskHi128T3 [50,50,50,50,50,5] [1073280,0,
 274877906944,1073741824,200111183364096,16]
/-- Mask segment `6` for `(m = 128, r = 256)`. -/
def rkmMkHiHiB_m128_r256_s6 : List Bool := rkmUnpackMaskHi128T3 [50,50,50,50,50,5] [1064960,0,
 2181038080,0,774056185954304,19]
/-- Prefix-kick masks for `(m = 128, r = 256)`. -/
def rkmMasksHiHiB_m128_r256 : List (List Bool) := [rkmMkHiHiB_m128_r256_s0, rkmMkHiHiB_m128_r256_s1,
 rkmMkHiHiB_m128_r256_s2, rkmMkHiHiB_m128_r256_s3, rkmMkHiHiB_m128_r256_s4, rkmMkHiHiB_m128_r256_s5,
 rkmMkHiHiB_m128_r256_s6, []]
/-- Part `0` of `rkmRowHiHiB_m128_r256`. -/
def rkmRowHiHiB_m128_r256_p0 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]
/-- Part `1` of `rkmRowHiHiB_m128_r256`. -/
def rkmRowHiHiB_m128_r256_p1 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Part `2` of `rkmRowHiHiB_m128_r256`. -/
def rkmRowHiHiB_m128_r256_p2 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Part `3` of `rkmRowHiHiB_m128_r256`. -/
def rkmRowHiHiB_m128_r256_p3 : List ℕ := [0,0,1,3,9,26,68,148,296,594,1163,2140,3605,5555,7474,8342,
 6965,2902,34,9960,49726,126182,213264,241997,161845,35087,8715,100500,123154,26889,9427,34665,286,
 105753,157248,20775,1481,334350,653040,56646,55901,203017,1878613,4483838,9645836,5198314,5629813,
 32211934,13746580,140363973,21400385,534597486,4001652,170147135,2293498986,4918272,1500758017,
 1742607598,1051090473,966749655,9333384650,3822037,5288940437,976868091764]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 256)`. -/
def rkmRowHiHiB_m128_r256 : List ℕ :=
  rkmRowHiHiB_m128_r256_p0 ++ (rkmRowHiHiB_m128_r256_p1 ++
    (rkmRowHiHiB_m128_r256_p2 ++ rkmRowHiHiB_m128_r256_p3))
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
 [297427150743892,418160100791166,509117940878876,584387484068094,649459028244548,707164881244888,
  759197174172344,806664594132206,850341473629458,890794651060164,928454323711360,963656464929116,
  996669635307552,1027712687424916,1056966886090784,1084584460142042,1110694793633344,
  1135409008508778,1158823422795818,1181022204913526,1202079441834550,1222060772306430,
  1241024692231456,1259023609420350,1276104704286362,1292310638524114,1307680143438332,
  1322248512060148,1336048013655326,1349108245111078,1361456430588556,1373117678470300,
  1384115202820736,1394470515173774,1404203591363744,1413333017250910,1421876116505862,
  1429849063067890,1437266980450456,1444144029708784,1450493487593032,1456327816171408,
  1461658725010900,1466497226840242,1470853687484270,1474737870745494,1478158978813632,
  1481125688703662,1483646185155064,1485728190367196,1487378990896514,1488605461999056,
  1489414089665348,1489810990563446,1489801930078614,1489392338614392,1488587326299024,
  1487391696222978,1485809956317032,1483846329966122,1481504765441206,1478788944219778,
  1475702288255138,1472247966244828],
 [1468428898939606,1464247763526008,1459706997107440,1454808799301170,1449555133960962,
  1443947730027802,1437988081503558,1431677446534912,1425016845586870,1418007058676994,
  1410648621632476,1402941821322762,1394886689809914,1386482997347422,1377730244145396,
  1368627650805648,1359174147313968,1349368360458378,1339208599520938,1328692840066262,
  1317818705621640,1306583447010662,1294983919063808,1283016554384114,1270677333792628,
  1257961753014946,1244864785094578,1231380837928438,1217503706210932,1203226516941518,
  1188541667490680,1173440755023824,1157914495842372,1141952632904342,1125543829417266,
  1108675545933464,1091333897794122,1073503489026852,1055167217851464,1036306047721352,
  1016898736227836,996921512088472,976347687637676,955147190466678,933285992721536,
  910725409472880,887421227629220,863322612709204,838370720270236,812496908464100,785620402376044,
  757645189878732,728455815857736,697911556290514,665838138010762,632015609440892,596159921571684,
  557893707265538,516697337107452,471821045348018,422111914813102,365626100816388,298568631622502,
  211132691078386]]
private def pvo_r256_0 : List ℤ := pzigCatZ 42
 [
 [10136230,70664226,346044312,1374440236,4696147702,14255320032,39235473250,99299592580,
  233476170514,514003497986,1066098730924,2093633404240,3908940878560,6962529870944,
  11865716871992,19396839435680,30480730895510,46132485015144,67360838704992,95033692368268,
  129717410280296,171510765474644,219901344369500,273674589957152,330901879044348,389023886583916,
  445030392257080,495720467325628,538011288586848,569253210595046,587505714578218,591734274881820,
  581900958003536,558938987602352,524619944320776,481338079733450,431846595935386,378984255778542,
  325427481371604,273494638684422,225017784667110,181285264063900,143048324547792,110577780208716,
  83753238200206,62167270817924,45229372131896,32258530429644,22557731226086,15467841961924,
  10401583573702,6860441877482,4438443991798,2816919260468,1753953204802,1071501047810,
  642281556598,377781010686,218050246960,123506911468,68652621746,37451027040,20050132966,
  10534660454],
 [5432166976,2748977474,1365235806,665383742,318237256,149357516,68782814,31080334,13778968,
  5992962,2556970,1070102,439228,176794,69770,26988,10222,3786,1366,476,158,44,10]]
private def pvm_r256_0_1 : List ℤ := pzigCatZ 64
 [
 [482157444324,2069459733300,6242160916968,15278314830702,32183832289068,60258596191506,
  102344882229162,159911103457048,232228709845460,315921694545902,405086920708370,492023452634396,
  568427592338210,626772713424818,661545308068642,670061081443558,652711685204232,612646272057534,
  555023389185944,486044180530160,411987297254724,338420759667524,269690576098904,208706722998788,
  156984456805412,114862988731710,81814538815884,56768154024586,38395129608644,25327736389752,
  16304144813330,10246987054486,6290572237106,3773677537546,2213052713476,1269201676744,
  712081734914,390955672710,210112678346,110566564590,56984100166,28770386638,14232998910,
  6900739988,3279645332,1528155268,698215022,312865962,137510550,59289598,25080562,10410206,
  4240208,1694950,664972,256058,96780,35902,13062,4660,1628,554,178,52],
 [12]]
private def phbv_g1 : List ℤ := pzigCatZ 0
 [
 [238026706488320,335305672317614,409053455842960,470474662043320,523927585290644,571656398394344,
  614999483163924,654832254173224,691765115731680,726244197279348,758607569431364,789118871508072,
  817988550087198,845387872864466,871458514781292,896319316620080,920071174283658,942800655104822,
  964582724797828,985482838999068,1005558571786280,1024860900829472,1043435233882326,
  1061322237656430,1078558513775200,1095177155013196,1111208206817490,1126679053156310,
  1141614741367578,1156038257427160,1169970760609250,1183431784650404,1196439411099864,
  1209010419431538,1221160417627814,1232903956263720,1244254628579054,1255225158593842,
  1265827478974658,1276072800077882,1285971671366726,1295534036211210,1304769280925766,
  1313686278771386,1322293429543054,1330598695274458,1338609632517740,1346333421593366,
  1353776893152320,1360946552347966,1367848600876684,1374488957113736,1380873274542858,
  1387006958654006,1392895182462900,1398542900788128,1403954863405938,1409135627189338,
  1414089567326334,1418820887701774,1423333630518264,1427631685223652,1431718796805616,
  1435598573507680],
 [1439274494015580,1442749914158060,1446028073161834,1449112099496762,1452005016343760,
  1454709746715034,1457229118253452,1459565867735500,1461722645300044,1463702018423206,
  1465506475657850,1467138430154680,1468600222980406,1469894126247250,1471022346066824,
  1471987025340382,1472790246396480,1473434033486220,1473920355145432,1474251126432428,
  1474428211049360,1474453423354506,1474328530272378,1474055253107922,1473635269270752,
  1473070213914790,1472361681498438,1471511227269946,1470520368682376,1469390586742218,
  1468123327295488,1466720002254810,1465181990770826,1463510640351000,1461707267928726,
  1459773160885400,1457709578028030,1455517750524732,1453198882800322,1450754153394104,
  1448184715781790,1445491699163410,1442676209218912,1439739328833096,1436682118791378,
  1433505618447858,1430210846367012,1426798800940304,1423270460978906,1419626786283666,
  1415868718193404,1411997180112530,1408013078018948,1403917300953158,1399710721489392,
  1395394196189612,1390968566041120,1386434656878518,1381793279790706,1377045231513542,
  1372191294808830,1367232238830186,1362168819476346,1357001779732464],
 [1351731849999872,1346359748414806,1340886181156544,1335311842745384,1329637416330880,
  1323863573970720,1317990976900634,1312020275795660,1305952111023152,1299787112887800,
  1293525901869016,1287169088850940,1280717275345392,1274171053707996,1267531007347754,
  1260797710930320,1253971730575172,1247053624046974,1240043940941258,1232943222864698,
  1225752003610142,1218470809326590,1211100158684296,1203640563035190,1196092526568756,
  1188456546463518,1180733113034338,1172922709875602,1165025814000480,1157042895976390,
  1148974420056760,1140820844309258,1132582620740574,1124260195417884,1115854008587102,
  1107364494788014,1098792082966420,1090137196583356,1081400253721490,1072581667188816,
  1063681844619680,1054701188573260,1045640096629578,1036498961483084,1027278171033942,
  1017978108477044,1008599152388836,999141676812040,989606051338304,979992641188858,
  970301807293248,960533906366180,950689290982552,940768309650698,930771306883946,920698623270478,
  910550595541586,900327556638362,890029835776836,879657758511658,869211646798310,858691819053944,
  848098590216826,837432271804486],
 [826693171970548,815881595560334,804997844165230,794042216175880,783015006834204,771916508284326,
  760747009622378,749506796945256,738196153398338,726815359222192,715364691798298,703844425693828,
  692254832705468,680596181902362,668868739668156,657072769742176,645208533259772,633276288791852,
  621276292383602,609208797592436,597074055525194,584872314874578,572603821954898,560268820737086,
  547867552883036,535400257779280,522867172569994,510268532189378,497604569393414,484875514791004,
  472081596874532,459223042049832,446300074665600,433312917042240,420261789500194,407146910387722,
  393968496108172,380726761146766,367421918096862,354054177685762,340623748800046,327130838510434,
  313575652096214,299958393069222,286279263197404,272538462527950,258736189410016,244872640517056,
  230948010868754,216962493852574,202916281244932,188809563232014,174642528430214,160415363906240,
  146128255196862,131781386328336,117374939835486,102909096780474,88384036771244,73799937979670,
  59156977159390,44455329663350,29695169461050,14876669155520]]
private def pvi_r256_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s0 pvo_r256_0
private def pvo_r256_1 : List ℤ := pzigCatZ 99
 [
 [11,47,167,537,1525,3893,9013,19263,38369,71723,126711,212475,339667,519465,762191,1075713,
  1463527,1923199,2445185,3012525,3601385,4182805,4725101,5196821,5569977,5822703,5941465,5922065,
  5769687,5497983,5127113,4681603,4187795,3671543,3156253,2661441,2201947,1787497,1422433,1105223,
  826445,563063,264109,182460,1023072,2796050,6660134,15063344,33072660,70954634,149068660,
  306928046,619588080,1226591044,2381883954,4537855684,8483407664,15565255690,28033802274,
  49569924640,86066270476,146754546602,245785872932,404379933666],
 [653653963822,1038216564704,1620555132604,2486151119404,3749119009944,5557982930534,
  8100987849148,11610110198226,16362717781422,22679675129820,30918650213862,41461504689786,
  54694986471328,70984512694190,90641621872724,113886632351676,140809070310118,171329384381026,
  205166179892998,241813517285452,280532589268428,320361243491558,360143362313250,398578159813996,
  434287216990110,465894832657510,492115338946078,511839719704844,524213412038314,528697685798948,
  525108461844308,513628681107696,494793084806770,469447146114878,438684521986442,403769430993942,
  366051566195198,326881409605920,287533156735532,249141043004556,212652938423686,178802937980228,
  148102613885926,120848855836724,97144972816302,76931039989312,60019334581476,46131032186268,
  34931000621288,26058384766864,19151581610972,13867043823484,9892042026356,6952018292108,
  4813468686682,3283419919164,2206550243812,1460890791692,952872924712,612296301140,387608373502,
  241726534104,148507810512,89879683834],
 [53586311040,31471570622,18207347750,10375988440,5824476918,3220464302,1753892350,940802232,
  497040852,258625196,132531936,66884632,33240902,16268344,7840076,3720356,1738262,799632,362136,
  161438,70834,30582,12982,5408,2204,878,334,120,38,8]]
private def pvm_r256_1_1 : List ℤ := pzigCatZ 146
 [
 [5033573,8447947,9985787,9597129,7944425,5808051,3663559,1418569,2008700,9889568,30881714,
  86747508,229757438,579869726,1400400240,3245099924,7231538718,15527504750,32179758516,
  64466470598,125010286594,234936303372,428378904414,758606636102,1305913702112,2187190221446,
  3566712189628,5667190361398,8779524744648,13269111676372,19576071160724,28206562596342,
  39712601585794,54658609570318,73574372789466,96896089038628,124899528544952,157631680820032,
  194849159414506,235972628899430,280066220167966,325849107680848,371743188274106,415956465292212,
  456596900617278,491806912456190,519905157846312,539520406755232,549702583182680,549998455240354,
  540483664391842,521748143281870,494837640783446,461159180409222,422362082536612,380208197661168,
  336445068869232,292694035404624,250362239341340,210583698260470,174190691580424,141713236430890,
  113401804668846,89266863335628],
 [69128318964470,52668364449000,39482315024908,29123485347802,21139724668354,15100667500360,
  10615923505486,7345251028508,5002229626640,3353112682144,2212474198034,1437045242354,
  918840446826,578363898792,358398647988,218648817174,131326918108,77659630202,45214713056,
  25918744928,14628628962,8129305082,4448022624,2396331656,1271144246,663913244,341425578,
  172881174,86191416,42309878,20449226,9731146,4559282,2103134,955136,427044,187958,81432,34718,
  14562,6006,2428,958,368,132,42,10]]
private def pvm_r256_1_2 : List ℤ := pzigCatZ 123
 [
 [72401,248547,600879,1181327,2003279,3026193,4156183,5263177,6209039,6877613,7197459,7151913,
  6775809,6141833,5341897,4468727,3601169,2794041,2070347,1409521,717719,248332,2063870,6050444,
  15176148,35944850,82235694,182874372,396126986,836646282,1724135088,3468720632,6816455382,
  13090172268,24576636058,45130563758,81088724590,142610608942,245581709324,414224503792,
  684551511392,1108753095516,1760528290702,2741229976676,4186501673118,6272836863910,
  9223211116122,13310656380942,18858416066216,26235201915672,35844137506500,48104278984566,
  63424189380052,82167907558906,104614743939252,130915542414836,161049208740132,194784222004308,
  231650313935402,270925348438828,311641559620186,352613712628146,392489561149774,429820429050892],
 [463147172656886,491094557922844,512465567302570,526326605620976,532075138120234,529482936274648,
  518710629725240,500292329575386,475092279989376,444238378747316,409039607748648,370895672018824,
  331207352828904,291295288362680,252333293823196,215300208204346,180951935556752,149813149819264,
  122186310381294,98174357450002,77712788642996,60606734169662,46569047806674,35256170400866,
  26299442867714,19330498720242,14000233760054,9991553659300,7026600375720,4869452837294,
  3325409730938,2237932071564,1484196054060,970026151954,624781052478,396577638308,248077619300,
  152935489600,92916310414,55633913068,32828539100,19090947112,10941236010,6179689828,3439743832,
  1886869134,1020023610,543409622,285291172,147600530,75252362,37807528,18717812,9131508,4389666,
  2079274,970436,446254,202180,90234,39666,17166,7306,3052],
 [1248,496,186,64,18,2]]
private def pvm_r256_1_3 : List ℤ := pzigCatZ 103
 [
 [53,271,999,3063,8101,19081,40847,80651,148327,256113,417767,646939,955127,1348957,1827947,
  2382669,2994027,3634003,4267705,4856771,5363393,5754493,6005267,6101819,6042139,5835735,5501931,
  5067107,4561655,4016675,3461291,2920495,2413651,1953873,1547429,1192933,878365,573219,209041,
  365546,1483760,3871450,9084386,20392674,44526392,95039074,198635780,406797452,816628774,
  1607360038,3102727660,5875006996,10914269544,19896921048,35600970376,62531540488,107837856372,
  182620176668,303738223614,496236205586,796486380518,1256114849890,1946701235568,2965130927104],
 [4439321493002,6533847262908,9454761345984,13452687620982,18823064003800,25902310357300,
  35058722651222,46677108916696,61136617167472,78781869066428,99888376401164,124624206916412,
  153010864543962,184887205277450,219880757590080,257390901120382,296587867983380,336430428089256,
  375703456550556,413074510098154,447166300590900,476639845328808,500281407595294,517085389928256,
  526325292328254,527605757851028,520890516383526,506503486999384,485103090905036,457632589729562,
  425251635047618,389255897609464,350992452339294,311778475803608,272829848969662,235204643776484,
  199764473664986,167154596680134,137801744038458,111927116814256,89570976196584,70624787721172,
  54866926370490,41998406937216,31675837725648,23539662372222,17236624808574,12436165481392,
  8841068346290,6193099630912,4274613662130,2907173354640,1948181325424,1286384198658,
  836936946370,536528401868,338896592126,210917266234,129337010046,78143690954,46517833228,
  27283047838,15765469204,8975396510],
 [5034131906,2781701806,1514264596,812059234,428999970,223253678,114445652,57789120,28742532,
  14080608,6793906,3228508,1510944,696362,316038,141220,62122,26890,11450,4790,1958,778,294,106,
  34,8]]
private def phbv_g2 : List ℤ := pzigCatZ 0
 [
 [221539479489964,312284199645140,381219145263750,438751162579884,488925408202916,533823424616092,
  574685792326770,612323430938450,647301411075608,680032465110764,710829156786874,739935079565284,
  767544555510046,793815629660622,818878956355620,842844062735518,865803878636774,887838086181050,
  909015644921262,929396728080160,949034229744510,967974953954500,986260564214730,
  1003928350004240,1021011851705994,1037541374722198,1053544415931698,1069046020129662,
  1084069080037202,1098634590454640,1112761864864584,1126468721067206,1139771641106558,
  1152685909721468,1165225734753342,1177404352312138,1189234119001120,1200726593100832,
  1211892606290968,1222742327228258,1233285318086522,1243530584991368,1253486623139164,
  1263161457271790,1272562678080390,1281697475029466,1290572666023876,1299194724283466,
  1307569802741184,1315703756239038,1323602161760980,1331270336911608,1338713356823784,
  1345936069655970,1352943110821030,1359738916071550,1366327733552482,1372713634919326,
  1378900525609226,1384892154342794,1390692121926190,1396303889415584,1401730785699752,
  1406976014550814],
 [1412042661188146,1416933698395982,1421651992231362,1426200307355464,1430581312018310,
  1434797582724018,1438851608601264,1442745795501402,1446482469844668,1450063882233114,
  1453492210847292,1456769564642238,1459897986356984,1462879455350694,1465715890277338,
  1468409151609956,1470961044024602,1473373318653282,1475647675214458,1477785764029062,
  1479789187929286,1481659504066932,1483398225627550,1485006823456166,1486486727599932,
  1487839328772686,1489065979746046,1490167996671278,1491146660335976,1492003217359214,
  1492738881328638,1493354833882720,1493852225741134,1494232177686082,1494495781497158,
  1494644100842180,1494678172126272,1494599005301314,1494407584637742,1494104869460574,
  1493691794851368,1493169272317768,1492538190432150,1491799415440786,1490953791844876,
  1490002142954688,1488945271417984,1487783959723828,1486518970682796,1485151047884560,
  1483680916133748,1482109281864906,1480436833537372,1478664242010772,1476792160901852,
  1474821226923258,1472752060204890,1470585264598346,1468321427965006,1465961122448218,
  1463504904730004,1460953316272722,1458306883546040,1455566118239542],
 [1452731517461304,1449803563922680,1446782726109568,1443669458440354,1440464201410734,
  1437167381725552,1433779412417816,1430300692954954,1426731609332416,1423072534154658,
  1419323826703540,1415485832994090,1411558885817664,1407543304772372,1403439396280726,
  1399247453594360,1394967756785676,1390600572726242,1386146155051710,1381604744113008,
  1376976566913544,1372261837032064,1367460754530836,1362573505848752,1357600263678900,
  1352541186830138,1347396420072132,1342166093963278,1336850324660866,1331449213712834,
  1325962847830316,1320391298640216,1314734622416906,1308992859792110,1303166035441940,
  1297254157749974,1291257218445176,1285175192213366,1279008036280820,1272755689968506,
  1266418074215296,1259995091068414,1253486623139164,1246892533021918,1240212662674078,
  1233446832754626,1226594841918616,1219656466064764,1212631457533072,1205519544249114,
  1198320428811376,1191033787517678,1183659269326408,1176196494747878,1168645054660730,
  1161004509047806,1153274385645466,1145454178499692,1137543346421766,1129541311335562,
  1121447456507776,1113261124651530,1104981615892860,1096608185588568],
 [1088140041982652,1079576343687340,1070916196973164,1062158652850920,1053302703926482,
  1044347281007324,1035291249437278,1026133405133330,1016872470295280,1007507088755586,
  998035820932886,988457138348122,978769417657164,968970934147974,959059854643590,949034229744510,
  938891985335146,928630913268610,918248661132146,907742720981496,897110416916156,886348891348330,
  875455089795784,864425744002304,853257353157794,841946162952674,830488142156318,818878956355620,
  807113938424954,795188055220414,783095869895814,770831499121220,758388564341290,745760136033074,
  732938669701906,719915932077002,706682915618756,693229739005356,679545530696794,665618291938212,
  651434734604596,636980088024342,622237867236330,607189592869454,591814449745548,576088867040874,
  559985996861584,543475059570504,526520511851528,509080975235200,491107835208214,472543378283398,
  453318266349198,433348035799896,412528118467700,390726542968506,367772843317914,343440450183480,
  317417174377888,289252172291300,258251443689034,223243421305994,181937532498654,128404538405038]]
private def pvi_r256_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s1 pvo_r256_1
private def pvo_r256_2 : List ℤ := pzigCatZ 0
 [
 [9,15,0,23,29,79,221,1039,4219,15947,55559,180563,555095,1634397,4637179,12637959,32722107,
  79306371,177217743,360009029,655758889,1054408965,1464682057,1694968905,1511318945,797377029,
  256622700,1119852288,1205770630,382885854,729252863,1139816713,417806329,720521564,1022816552,
  115294198,910291623,738949939,417413948,968355270,117889308,889789949,522929589,655128330,
  762252122,383382419,867945949,140739394,889388132,46953256,869445979,176385329,837686012,
  253482012,811220091,285828731,797674704,279330152,797898879,237434665,807772802,161788124,
  819260981,53682941],
 [821138358,84049371,799881359,244988610,741171702,417295901,632313965,582644458,465600842,
  716586545,242253061,791016876,23938795,779101763,304612308,662406200,558038009,439003757,
  734820028,130312998,788408095,216325784,689067426,532219123,437930515,740549328,76099512,
  777055147,316557004,613412770,636414059,275447275,784155668,152713089,699367887,544865918,
  389918312,769182819,57488982,735789356,495417245,438495967,762438214,28998875,745687931,
  495342434,434041786,773202079,60804026,734620826,541563663,381859113,794608914,148340591,
  698139157,620856092,278366540,812813649,281751266,621237760,715932723,122453169,804394974,
  447526151],
 [489547351,800254152,82458187,744030973,622317894,294208908,841346305,321279608,609637426,
  772951705,39057675,806741740,563279183,389979115,860086506,254259879,672101397,765978668,
  95652972,843831687,547325096,432102028,881366881,241012842,702047676,784130639,103489003,
  870323680,567607737,437222231,911019786,266215565,712312439,821917072,79619340,891140153,
  612724982,421597582,946486537,312695438,712662954,870870743,42114245,911245076,667198813,
  400737981,986667710,361574361,716622683,921300110,10225776,939503271,716177244,396516942,
  1030996799,393307694,742369156,966997663,10799325,986436800,743357793,434147515,1083827400,
  379994239],
 [810951205,996767136,73070276,1066513405,723118710,544225870,1140841737,290039392,949574504,
  992763013,246028131,1198721496,603990289,810017163,1169612982,46906574,1185114539,656906738,
  689499718,853846639,35407055,247868612,209177729,1284307752,619372557,3863948121,3285998306,
  8043818882,8881013443,15649267583,19241095564,31374278896,37392282189,66126667109,67038209170,
  143974405986,107952708153,315218942695,138754230128,676742144368,65068770479,1385943188499,
  409969134147,2601744971582,2049276489170,4129996621833,6420033741901,4241556381204,
  15601673588698,3034690202670,28481604905749,30742474936327,27301933151588,88977728711582,
  46003940089610,119834298441349,253500359603295,139406776771341,276963012712262,796827554983046,
  1118226015622100,1080588404004096,766739029055674,393298475432432],
 [129420173395782]]
private def pvm_r256_2_1 : List ℤ := pzigCatZ 79
 [
 [1039,2335,27582,97207,206166,311635,379566,383633,236512,70550,266251,135948,132128,238537,
  66135,358526,187626,335695,663007,57284,195110,1306934,195177,527362,1009987,1045269,192395,
  862159,71169,1159890,813366,1060340,2434024,2803102,2375196,2980110,4292338,4695712,4214212,
  4221328,5166172,6071674,6003908,5161392,4457828,4492054,5086876,5606386,5518856,4703004,3397312,
  1973624,737268,157905,696037,942773,989945,921027,797223,656457,517329,382641,238129,41571],
 [307142,1035316,2648672,6250184,14194614,31400348,67914426,143809296,298308158,606385330,
  1208241748,2360382782,4521982604,8497329358,15664920816,28336582192,50305803850,87662667350,
  149971507972,251923654838,415586201256,673361874648,1071746131338,1675906237684,2575004761380,
  3888041200272,5769791202462,8416193123842,12068288743366,17013604397586,23583708434226,
  32146656428076,43093192513660,56815957761472,73681583586720,93996404246248,117967537003308,
  145662159194414,176968747995258,211564822332350,248895744343794,288169342339490,328368788822638,
  368287597094144,406581801738194,441845975312548,472689908139558,497842155849412,516215841847190,
  527017866316140,529763520168276,524362722899752,511073008347740,490520162310850,463630531161072,
  431554312713812,395613204729778,357180771574606,317609993610168,278171176769858,239965131829362,
  203893849715096,170648983707470,140687591429184],
 [114248372689186,91391262365096,72019097758568,55906428978482,42749021780274,32202112756098,
  23899097767952,17472870152258,12582049220008,8924932321156,6238857608584,4298081481926,
  2916142336148,1946922318598,1279498939612,829426619096,531677806254,337056844144,210322124598,
  127907686624,74805614560,41440496910,21372868684,10020162112,4083100960,1277811180,131901352,
  224824015,258870557,193277001,119219633,64540669,31217095,13444897,5012623,1473899,205587,
  137988,165182,115394,66134,33664,15672,6758,2710,1010,348,108,30,6]]
private def pvm_r256_2_2 : List ℤ := pzigCatZ 60
 [
 [306300,473965,259276,138148,257983,19024,169768,47882,396899,385406,300885,589994,658163,63212,
  401890,319257,217474,28685,503451,384564,518230,384789,318227,113044,196103,109369,669438,
  611454,372451,730771,241499,56127,282553,19252,821026,1028506,309332,406701,410083,159477,
  386391,939329,1039513,396629,419332,730858,554998,504706,1036674,1966004,2712358,2910744,
  2736058,2689684,3129624,3985508,4852564,5320380,5252878,4838738,4429988,4315036,4572310,5063382],
 [5532500,5736188,5536582,4930122,4020152,2963848,1914394,995290,257920,240467,614623,657941,
  995347,302099,1718005,1615028,5125413,8964318,18681337,34500498,63583389,111210278,187484295,
  302544578,463205893,679268550,921730551,1210256358,1369469157,1611164832,1191196211,1539468248,
  570806932,1852742688,5229267962,7236326294,17393312632,30369369014,56038897496,102827426318,
  177891430912,308560046982,520320939456,856980030202,1389008791776,2200899986924,3418420718894,
  5210410543160,7783151261436,11404734847144,16399701732420,23136542030542,32035883409594,
  43548136168208,58116874508340,76158532836074,98019122387062,123913155426914,153883419403472,
  187760953049366,225115998504630,265238283888952,307148221522718,349615603349990],
 [391202830105378,430348758392918,465467652951328,495046343232118,517750615289734,532533242393374,
  538714353486602,536025652568514,524629521008248,505110174025790,478424630584418,445819638971542,
  408735380977414,368707076791224,327264414886224,285834981999640,245666832499570,207779612615816,
  172940897237332,141660717147178,114202592247500,90611960416014,70758224766466,54381532066064,
  41136285297722,30628511240928,22447773908424,16194032079782,11498097787744,8034177820982,
  5524718828806,3739664828204,2492777612134,1636888240488,1058828747418,674154669126,421730737162,
  258466077832,154599684326,89841909542,50464869470,27241590162,14036076990,6842048418,3114633948,
  1294970256,469562798,130081650,10015216,20959041,21341549,14524989,8261589,4163519,1894217,
  777617,282291,85087,16565,2452,5132,3762,2136,1054],
 [470,190,68,20,4]]
private def pvm_r256_2_3 : List ℤ := pzigCatZ 45
 [
 [272426,609452,103545,481344,750355,24975,371670,233789,148686,258986,446879,227709,492788,
  186326,352533,59571,196494,159273,200631,318158,357544,273321,484813,69940,433654,96504,246183,
  61323,159010,80161,350079,54679,500794,516228,100395,595223,430395,54214,232968,63628,19982,
  309444,536218,244484,432851,874389,671341,60149,380930,378420,164416,186222,424684,757352,
  327090,223558,1498171,510630,3765971,5544838,11118457,20087234,36351231,61451122],
 [102920295,165888004,254086935,381378714,538114377,734444164,941207395,1144622368,1286565247,
  1335096470,1215881965,930547632,456189631,101607097,654002618,1009527051,1065565776,737302721,
  144256276,531253312,959707319,960291866,459706075,271104755,871699944,947263983,443885644,
  360359796,920341525,831021054,123579697,685739139,950304308,429021371,468233339,954717692,
  569719713,361220453,946932192,586323539,386607105,957998532,488578225,535466565,955080698,
  252880179,764456723,848343338,140649244,960689307,524520252,649287314,864720615,100808692,
  1476005420,779753758,2181711918,7519216746,14902377272,29255401192,60876808324,119266999028,
  221979796968,404458488560],
 [718294203012,1235811414900,2067307107612,3372317414918,5362887195930,8314622464284,
  12581218388708,18594489028436,26851376965290,37898924522416,52310002196432,70636633510262,
  93346889405536,120759963785482,152981124980578,189834041351128,230802685984634,275002358107214,
  321187197370868,367790545909658,412998269612336,454859027686536,491425563503788,520907560177358,
  541815210173338,553080628608286,554148189677496,545022467272090,526263566263460,498929408966182,
  464476095101996,424632153036948,381260601883610,336220620748530,291241321918528,247820527877612,
  207157752003510,170123463039600,137260262352498,108808722935144,84750757191564,64864142346460,
  48781890601930,36050017583234,26178076814786,18678908921208,13096645360836,9024056104572,
  6111306530756,4068259749404,2662132932990,1711994567482,1081394716620,670273840732,407091885704,
  241831221172,140206804444,79140730790,43375463316,23016595806,11786882752,5803842202,2735458962,
  1226738360],
 [518967530,204270488,72947124,22348816,4907760,73871,942059,741245,423931,206219,89203,34711,
  12041,3589,815,61,66,50,20,4]]
private def pvm_r256_2_4 : List ℤ := pzigCatZ 32
 [
 [661451,30562,532828,160360,217107,160814,690186,525212,38013,165999,133078,148896,266513,452803,
  40573,431252,328666,149359,321841,36391,191036,19828,219579,79707,291150,345344,64899,446355,
  319093,156910,396996,178698,198209,167591,64625,385748,508385,754482,2195875,4260890,7264981,
  14498464,25989309,44131656,75427055,122192756,190598645,288104982,416312553,576099688,760266405,
  951172722,1119610701,1225993590,1228045075,1085271972,784051321,345780822,165866718,637072907,
  943002700,977491227,701350830,184876317],
 [402608731,833293472,916877089,591966050,11731062,611538521,899294736,698159957,103649424,
  555210860,877549405,642341840,15021486,665850813,850614064,420177555,327973825,824796498,
  673742327,27139147,709197072,786057641,177082170,598133794,824709041,280914504,540258016,
  831842153,298653888,552686200,823511793,232633858,627386076,790106623,77926810,740995852,
  693511515,163389463,844673740,484791585,466208157,853370910,133863795,752461611,666040522,
  326881896,875526499,227010662,751562558,668979209,377387731,883852174,86883927,850376257,
  502694298,622472968,789480399,292138583,916836214,61732373,905755337,376751414,792880324,
  624889683],
 [624436003,798047566,437391214,906117919,259721037,966426348,110926836,994217555,2804391,
  977116912,164915207,1203961593,181738129,825997762,617555470,3142796864,14295502742,40490969462,
  96460780692,214894633290,451576114892,893383017122,1676569294854,3009271990880,5188887897198,
  8615009197162,13801445139314,21380292881946,32084664715844,46704625683826,66020565737340,
  90717622258614,121281399322896,157881417840820,200260932778454,247656512542672,298764569245440,
  351763918758570,404399791125674,454130891321112,498330742170750,534520322423708,560599970260928,
  575049293678790,577070859862558,566661229418554,544600456265174,512360886767266,471948337204896,
  425699759861118,376066734483350,325412233677464,275841564871550,229080610465266,186407277029204,
  148635487091446,116144942266952,88944935566858,66757872254174,49108498752138,35407635153710,
  25023159447476,17334794723348,11772163104628],
 [7837472744384,5115310428744,3272561394376,2051604817648,1259702429510,756983800312,444757268662,
  255186177218,142787371510,77796461604,41205785982,21180479010,10546347884,5077057904,2357969986,
  1053956446,452064126,185384172,72326552,26656338,9179042,2897490,806898,179256,18988,9679,8745,
  4563,1929,709,229,61,11]]
private def pvm_r256_2_5 : List ℤ := pzigCatZ 21
 [
 [66961,196705,369611,491877,446309,192661,157314,383508,322870,28102,242431,231713,79292,440030,
  545614,349142,39250,35084,68368,685498,311717,1426684,3464301,5858360,12538621,23605062,
  42253473,74180444,124020973,198145210,303222217,442725972,613388685,804611490,993246287,
  1141000388,1204342967,1138553478,912443277,531899584,45905979,449318685,824468892,960060675,
  792049618,352594343,216495403,699757398,890629323,689205602,167007809,436689493,817272284,
  765142609,289919686,352434654,784582517,736099254,220966271,439745037,804274448,613117871,
  13658489,631318690],
 [778191273,329752966,377593394,783119953,550337724,142862284,716306579,667817406,30120463,
  637521263,722545076,132426883,584104113,740545376,171151041,571053947,739019218,148827639,
  599260075,717123524,68461239,659899905,664259390,72465266,730621875,558117436,264594332,
  780756421,373067736,485895724,759858373,100396112,688948900,616694857,242187265,793997704,
  319160261,581637431,714459840,110857234,791715967,393733438,554798554,732951069,121796997,
  811677938,334691787,629732629,682369972,284343344,825088389,132002804,778371190,488117395,
  554851563,745666722,252571012,846360293,91505566,832014588,384706423,691147575,635841028,
  506181638],
 [786525651,270525999,879193998,49095816,896389317,162251034,873691460,339760793,821138381,
  483577000,755745918,596080481,693523297,677225200,640535166,735277111,607735161,770482616,
  597175716,787042515,613678641,783081818,657558202,756197535,730974565,691392238,814760314,
  590594889,868307101,603635610,1287695912,17617431,1459882465,2316395109,5526269949,13561294371,
  22676573697,19921025349,22908793938,166797533946,534152977702,1341997314222,2936847388624,
  5831627995444,10737965012512,18576807064948,30449206665780,47557895573480,71079468064094,
  101992449562524,140874138507838,187693055261962,241637699556558,301025386903726,363323860401530,
  425298983566852,483281053888388,533522378925682,572600016680108,597803594679756,607445407160832,
  601042316867582,579343338935250,544205208976780],
 [498343017542460,444999952300140,387588270614584,329352937909526,273100426367726,221019641696698,
  174603278550606,134660568225908,101400126148304,74556070449618,53531145023486,37535262951854,
  25704491580262,17192318421540,11230997766536,7165309028668,4463926024646,2714836327660,
  1611131942080,932455076584,525914926152,288810763602,154272282024,80068661112,40329972758,
  19690172526,9306199566,4252273994,1875841756,797742342,326539174,128426444,48434192,17474408,
  6013786,1966902,608356,176696,47688,11750,2556,456,58,4]]
private def pvm_r256_2_6 : List ℤ := pzigCatZ 10
 [
 [83,369,2247,3375,25077,496,194891,235504,1253355,2366694,6870969,14113442,31088825,60352296,
  112479873,195784008,318755939,487208554,692164241,912318808,1103949957,1206658434,1159668275,
  919193126,490536715,52035309,574071388,905754223,915727606,574767789,296991,571597956,869787759,
  737783984,222650069,410507391,807272352,728144389,204930296,445325202,802909453,621197866,
  12532799,603387681,779569490,375772019,311385819,755601568,600108299,40796971,645666298,
  708297967,166568152,519602820,745717515,303361578,414268592,749091985,382087152,347951538,
  742782523,413061582,324079266,738135681],
 [405593212,343314092,736647249,359560028,398580908,732571745,274154592,484581974,710132269,
  145655930,584965268,653389109,27315799,678694988,540089161,235015899,734004526,356102977,
  454646013,714534512,97526287,642237321,585159326,209554226,742620037,328437324,509768170,
  692024841,29868835,716749204,456137569,415472055,733043112,58209635,699622453,500852568,
  393824704,744620397,51117948,717669920,471386509,453748363,729758068,53479038,762770013,
  354669062,583051262,656795179,255599737,788599570,124073501,734868897,467137792,527757312,
  707013881,226808577,806797816,107539259,771312147,412045332,620632182,646463009,391233849,
  790717368],
 [125622990,838708811,143722016,806328592,380440183,698823929,584948926,559153832,725316749,
  381512967,829636922,211829796,874564265,32693191,902138042,110810975,882868463,256545806,
  872045602,356182855,833130871,452752796,812887410,513179287,789283321,560539522,782982344,
  584576517,790699853,587570206,813976874,569536173,855556849,523610706,909430718,448377721,
  973327031,335012802,1033878768,183639957,1080462987,89686,1127835324,269779230,1129051749,
  774551437,495647232,457867890,69249739,2170611330,7684122602,11517352480,4759011344,24665838673,
  91990548945,205965291959,337529812787,363332344881,11430373212,1343085321968,4538014125344,
  10910449880650,22167325799802,40281190468236],
 [67235152525764,104657482912110,153397384033752,213121747160424,282029878503022,356779524914666,
  432684858831744,504188570229334,565542769226594,611579171443700,638424212559766,644024411464866,
  628387108675782,593501367624164,542969364625356,481434353129580,413923731489254,345228188445126,
  279413083372234,219516642787780,167444645842096,124034309204008,89237335548686,62364632345284,
  42340381325822,27926409990074,17894308087036,11138291722968,6733664470734,3952685981348,
  2251995393518,1244651666202,666880836146,346122912640,173862990416,84440133624,39608588486,
  17923837120,7815356550,3279381930,1322462082,511817542,189821104,67357060,22828960,7376256,
  2267372,661488,182666,47594,11654,2662,562,106,14]]
private def pvm_r256_2_7 : List ℤ := pzigCatZ 2
 [
 [559733,3114812,11914799,36073380,91364205,199036506,378439403,631906290,925657585,1178024652,
  1270892535,1094611592,617369485,56188447,685876960,987459105,789453520,170511359,534014125,
  897831970,678248637,5057210,660251062,838205803,384132388,359673956,810290775,596534094,
  111553800,717129169,695919478,59060513,624853621,732033666,159098785,560237583,738423424,
  200674633,530164379,731032838,195672935,534605093,712855620,151142869,566344053,682250158,
  69169943,614832997,630469862,45178102,668511839,546671012,187060372,708455049,423365862,
  346326066,715599615,253759956,503626336,669219497,42650088,634967210,551586559,195437079],
 [706636262,357509157,430771293,688685272,94211401,618443849,558648214,204499440,710808197,
  314521030,484516826,663408779,12508023,674655712,460227211,357866911,707357030,124135385,
  625730469,544944262,266832650,722421297,203306022,593289116,584849323,224820171,728960348,
  227853375,591664351,590132934,237442026,734939055,197544418,623288346,560227597,305149221,
  735538960,107816871,679955471,482764598,422331176,711349693,46269535,739719402,337583535,
  571873947,628538266,261424494,761556947,106918048,714774726,446184303,511182999,685389874,
  205613236,780906481,136598592,727093902,448568481,546430605,676006548,276876880,791431097,
  30186826],
 [787031450,325959167,673800105,572502674,478680508,742021873,231124159,826292134,33271107,
  825399961,284692728,746950440,506187681,613098857,679307456,439774786,799811231,246465261,
  867803010,49127904,888400579,141132530,874008952,307818309,822109217,462684728,763071598,
  580775069,681221937,688741632,611757308,760011129,530044479,832400118,480159058,866544993,
  420455081,913115928,402010450,928391045,385184163,950591170,403207678,954583489,439270499,
  950826668,502139808,930964503,590555989,886569912,697651666,814230667,818248647,714812530,
  960289528,583509305,1190585361,231356966,1341315228,622863498,197306341,7056790,1385485945,
  6689811467],
 [11446504715,4243533053,26062570912,79357027534,129246936958,104757378024,114716986997,
  656719220143,1532139252249,2424445612873,2427213818883,191042765782,8081717726982,
  24650876705390,53557188202528,97895744746806,159219542820508,236655676392958,326403621308194,
  421835757494466,514270117826192,594296816424884,653372457976230,685307612917262,687294184259886,
  660246581421156,608418902458188,538445290634468,458074600557440,374904169452240,295366007816740,
  224112958202492,163832772571800,115419605602950,78375489501298,51302568958304,32370517983302,
  19686053011594,11536155104298,6511706096334,3538633613574,1850092781794,929844047756,
  448804539714,207795614838,92167603988,39105876944,15845733074,6120610930,2249093012,784455338,
  259045976,80758700,23690982,6514916,1671952,398274,87474,17556,3174,500,62,4]]
private def pvm_r256_2_8 : List ℤ := pzigCatZ 0
 [
 [311910537,813998454,1311423235,1389197664,782815813,259779823,1021226468,885269183,30252083,
  869773422,816277879,65891441,847018688,693307655,215597825,859207110,513189439,414219989,
  840076252,270129019,609619523,743980826,21710650,748931567,548705950,324401928,783962811,
  261382952,581925272,683782017,79170443,733536586,447584027,407960695,732047310,111876115,
  648393011,562119216,252593036,733664881,252260322,555659562,629827331,125530935,711648942,
  353244323,470965273,666929022,26178952,681838773,423649530,400623730,685777087,47647136,
  653324918,470808531,347383711,694682146,98283105,631145611,500337316,312873494,698290859,
  128180858],
 [618914294,514739511,296788233,700503104,137007159,616725721,516740114,300839246,700956381,
  125823494,625976392,504728741,324225493,699444710,93117205,645449883,476427024,366743394,
  692804381,37418978,672521394,427976131,427552993,675230894,42804674,701876043,354469584,
  503955940,638672549,148761745,724431114,250377661,589461261,573185402,279337050,727297519,
  110385640,671908060,467246773,427740517,693965944,67484016,732608159,309390142,578260992,
  604685501,276482809,745998272,93428375,704078693,439616272,495474354,680611305,172835593,
  766205476,187817651,684499921,505559962,457930612,716391075,138213933,783503670,206586527,
  699241825],
 [510731502,486418058,720903277,189316443,804276476,138985917,755428799,442390410,589254916,
  674171707,334998205,807466042,36126342,829743771,263207968,743749556,527119721,569586335,
  725722260,333276378,842938269,65779527,874167092,201658921,821528143,447997526,701700520,
  652409467,532088183,801480172,327909070,895482161,111368403,933269982,104005519,923101665,
  303818930,871646500,481676517,789249485,636466932,694033904,754762965,579250217,857713292,
  475347340,924896565,364128343,987764842,281353952,1016564927,192131449,1059534988,147217270,
  1070991415,99625331,1101641792,95811120,1114873871,108050509,1131853636,154832712,1131880165,
  215030397],
 [1121044744,251902874,1188909379,324048055,1516997274,975759678,1629718715,2990464091,1530609007,
  2522910182,9326602150,15148067874,6149805912,33141438395,92203009207,109560354041,14196233900,
  341038831426,766783818400,903285056134,98191565278,2262849730167,6114809151021,9876042920851,
  9781892858195,140695174740,27112643404028,77666641126050,155205602271984,257881774876062,
  377676460205072,501232165429022,612381127856344,695678774555714,739867222505636,740225649515230,
  699181111589974,625160274441490,530206938547450,427180204215772,327322877053820,238719611601810,
  165795418902782,109685009252174,69123790929584,41488470085586,23705950625650,12886019935880,
  6657266350014,3264716071866,1517340647082,667063510024,276742768078,108038747266,39554439456,
  13524822032,4297342894,1260912628,338953764,82614698,18000436,3434894,555744,71850],
 [6410]]
private def pvm_r256_2_9 : List ℤ := pzigCatZ 0
 [
 [1792636721,702697403,1116543608,715651758,922684505,660738589,857350556,572818274,849602915,
  457794751,866197638,316223786,884406075,149496949,885555382,37508377,853698901,235142920,
  776315482,428715887,645961493,599295430,462205296,725655109,233227141,787299102,23523147,
  768262541,282141094,661116992,510886291,470382461,676604584,214435126,750519259,74921904,
  714498488,355746855,566532915,582087486,323994090,712246631,23424743,717740800,283915867,
  591112747,540416776,350178224,693752733,37958265,708017882,285000787,575414805,549540760,
  317274044,697798999,11584838,689909502,341938273,525400629,594727500,235987126,709034249,
  112418068],
 [653990026,435220697,437038457,653348338,109529988,709089137,247499672,583568958,544137217,
  306510053,701727006,51953331,675228313,399712024,469596742,643370253,137196671,715746866,
  233883853,594095275,545125738,311494060,708554185,58606798,679487210,414391551,463192253,
  659077120,119030680,723354071,259686358,588241234,569822455,291222785,724714634,87157223,
  681089169,444051450,451017536,681620233,96895419,735144360,285189227,589991831,592206662,
  284991548,742821913,97326972,696956772,455303059,466458299,696266098,112960546,758266845,
  271040438,625646898,587981119,333497621,758744098,43603735,741991071,412138778,543943362,
  682369105],
 [213928755,790806158,169181469,715205237,514948266,475500638,744418575,126760989,809700220,
  251940545,700072519,577544604,441086352,783760131,89823353,831354582,280573955,714236711,
  598315656,460609132,803763617,121305741,862060890,241909229,770229225,563685708,549069860,
  790941517,237596495,893695870,110207941,861542649,440569498,705128302,708704239,454107013,
  880507084,144851892,942009347,180125398,894477324,479383087,747544397,726369184,527097728,
  900406815,262569451,989785810,20642705,998196983,294902776,931934324,543860219,809408093,
  750152124,644856148,906470857,450351813,1021522504,255170842,1081757199,52279487,1115713028,
  125227471],
 [1105333331,303293090,1098728970,435936711,1062354409,568207424,1065213068,626041021,1061421311,
  593580500,994894922,415679769,538909801,471311966,639285627,2309464867,1107057512,8036612976,
  6567658512,11271751765,32420408977,23279859241,41795864150,131198241168,128561114494,
  99556037451,516945028579,743200364825,155097902703,1566255093920,3653017487036,3887860813128,
  580136209877,11006755346595,24202806478385,30775370370875,16221953088863,34533966391044,
  130508302458756,268830939068770,432768408616496,595069760445040,725637149217596,800489750199954,
  808472947980672,753343174661086,650990273723048,523501258279698,392653676419340,275066241003082,
  180075947691500,110159812883420,62923418628138,33512073530892,16605273731532,7631845860794,
  3240273240850,1264016808348,449796327448,144589697248,41419265800,10363680658,2193795090,
  370498626],
 [43242512]]
private def pvm_r256_2_10 : List ℤ := pzigCatZ 0
 [
 [72313517,280735451,693463347,1218552567,1518839351,1178125285,151461181,916978138,1089010164,
  143724110,915707213,830722127,309430040,993117510,261590320,828335673,637911715,538566898,
  824844770,245872175,880375707,3395306,862861408,175913828,814950623,297186243,763032960,
  370967330,721268529,407273179,695758100,413449508,687566919,393900553,694555940,350641928,
  712339429,284191077,734732148,194599374,753997797,82547437,761150554,49557785,746503609,
  196582616,700595154,349921653,615538393,497221028,486728620,622805131,314699461,709004530,
  106772496,738465045,121975698,697311674,348948477,578774911,545896190,386588446,682619799,
  137295923],
 [732223208,139614219,677417643,404076896,515927526,611786685,265415155,720882812,38406379,
  704733717,341314922,554518000,586905849,293628483,718284154,34066757,702951539,360435448,
  534882618,612482755,242650815,729982718,110102949,677122961,442068924,458628710,671391737,
  123271031,734678984,248270807,608690681,561095514,320917218,728697637,56918074,700319406,
  424450555,477717447,679395146,119137932,744280463,278964024,597033260,601130023,273756801,
  752632844,132951797,682632613,505953574,408135582,732594879,8066749,740488878,399607399,
  523364595,690769000,143587424,774195465,285039806,620993498,630874191,274102209,786489972,
  162245935],
 [701972669,553435926,399569066,778416967,30439632,766892846,456401165,519824067,747600122,
  110536704,814320519,337383252,634513276,689053915,261228285,838628952,194075789,739998835,
  597331594,421490980,831217407,23056490,827219372,465573755,586046755,781562970,177214954,
  882887725,285007666,742496164,675006501,400881103,888340676,50319225,870974463,494079272,
  631944258,816695945,233469517,939984522,226592103,840138059,636900444,544829014,903821753,
  124009453,973213360,326117441,834962219,710869312,524278130,955805453,110727793,1016201560,
  325950563,889811825,707082480,610271032,966889895,229060323,1071799600,187902533,1016097051,
  575877758],
 [817491636,885453563,516326975,1079128268,153674992,1149074889,219590826,1099513160,556794399,
  935109085,841119608,686250608,1044860977,334489163,1230479134,93390843,1499002647,583026882,
  2225125722,669452057,3778853623,1034565479,5759083466,7724627802,3409841211,21941916449,
  18479583143,31365629082,83234650492,26509569780,165540967603,276874687319,17956898914,
  670637474288,922675859728,176030775297,2403311920429,3454523124503,232665447171,7519693533780,
  14037497266370,9032783555970,14430757421183,49635380942759,71627483658757,44720708436071,
  59350746778128,242483786765566,472631042900622,693574457899538,847450784144048,897886325204152,
  841992388224094,706796364172216,534426800201968,365044435399870,225321218736050,125422679981310,
  62676836700410,27906898609366,10941142506992,3707879838142,1053383159308,236844278552],
 [36542028202]]
private def pvm_r256_2_11 : List ℤ := pzigCatZ 0
 [
 [5975,49875,288005,1320639,5074257,16773071,48353591,122336071,271939941,529234893,893624947,
  1286424437,1525698723,1378578107,721620927,264126624,1057479708,1091751850,271374186,758920935,
  1046259071,267930685,778591564,911889910,49720199,926686509,576111085,545953074,881264148,
  61222559,894832947,349498891,732122428,625483350,500753491,775318807,270617320,834040430,
  76301761,838661339,70861895,818319776,171571958,792433129,231025379,772075442,254810018,
  762039385,247156283,762554250,210609466,770430453,146508097,779753786,55921538,782378081,
  59152532,768491988,194490609,727507607,342442332,649449042,491098255,526895699],
 [624170158,357349944,721944197,145667021,763577874,94054475,730778201,337898170,612514522,
  553656843,409938421,704996684,140221728,758235453,162234250,690883474,448626253,500171845,
  663325114,209047450,755700283,132994396,693985670,456420041,477989075,685118790,145098828,
  756756913,230840068,640064496,557586029,354607399,741146776,35474021,724138933,422328702,
  496655294,693393075,115911157,759681114,307134497,587923343,641086008,223062252,771633219,
  221924934,644247696,599831641,292307005,775768694,168424173,677668129,576648656,330770356,
  780455287,144731498,695790722,573132083,343790343,789621332,146746371,701687989,588614774,
  335919140],
 [802677257,171792462,698405844,618036585,308205527,819033962,215239757,685580985,658251556,
  264603392,834365461,273895374,663086412,705578131,208435839,846271580,342155893,630308005,
  755777344,142035112,854085681,414974406,589658108,803859617,69087203,856313156,489209607,
  544748637,848020802,3927561,853130981,559876314,498253704,888072657,72192198,849050060,
  622117819,456357597,922456684,131144195,847943057,674575778,427150394,952869575,172758850,
  853844674,713905651,416460609,982446756,190328951,874427569,734682254,432779662,1010063609,
  177153180,914844918,732378089,486614033,1033107472,120944095,975770159,696583868,584740940,
  1044755727],
 [7316702,1054614788,607222101,730562415,1024145736,176499592,1135174499,439855244,915821808,
  939547849,431579519,1192463008,185374695,1146741641,785202264,841354364,1251361929,414893357,
  1515882048,91343948,1571857569,233188359,1384039148,1461438106,564816745,4748898183,2352581201,
  11348033906,11767065596,21043366013,37819852267,25994850164,98482718808,6747662082,208145716631,
  167318763695,317558774098,621693165148,141177402237,1463346322859,1110166158621,2000195919780,
  4506888212824,819129734872,8596533057421,12488678671187,1692486503802,28715288894518,
  38740077750212,16954952607,81462344732693,142926497789867,95853473333123,109150270026864,
  433999665031118,763964669422488,972477064264678,991964376802528,842013458635272,603390156774436,
  365519520089122,185336863289814,76745771574418,24610881418330],
 [5317163259234]]
private def phbv_g3 : List ℤ := pzigCatZ 0
 [
 [215205771486832,303356143394860,370320271813010,426207476207534,474947264090640,518561667639256,
  558255799756028,594817396239944,628795372615976,660590661435058,690506890391892,718780688726998,
  745600822929348,771120819606142,795467597750794,818747553175098,841050958895834,862455218960830,
  883027321402290,902825719119236,921901793981738,940301011924810,958063845313332,975226517537936,
  991821610078042,1007878561918864,1023424083816608,1038482504547698,1053076062341272,
  1067225151766328,1080948534142228,1094263517866734,1107186113770124,1119731169607838,
  1131912487025878,1143742923720130,1155234483024470,1166398392773716,1177245174975008,
  1187784707568034,1198026279348626,1207978638961558,1217650038729588,1227048273971056,
  1236180718362866,1245054355826164,1253675809345158,1262051367073430,1270187006034510,
  1278088413683266,1285761007560342,1293209953242558,1300440180767148,1307456399686040,
  1314263112887850,1320864629309118,1327265075642360,1333468407136388,1339478417573758,
  1345298748500954,1350932897778804,1356384227513532,1361655971422572,1366751241683732],
 [1371673035311432,1376424240099430,1381007640165560,1385425921130656,1389681674960744,
  1393777404498920,1397715527710860,1401498381665772,1405128226272652,1408607247789910,
  1411937562124960,1415121217938814,1418160199569576,1421056429787468,1423811772393066,
  1426428034669370,1428906969697610,1431250278545758,1433459612338140,1435536574213800,
  1437482721180722,1439299565872480,1440988578213374,1442551186997672,1443988781388154,
  1445302712338824,1446494293946194,1447564804733402,1448515488870930,1449347557337610,
  1450062189025196,1450660531789680,1451143703452210,1451512792752360,1451768860256266,
  1451912939221990,1451946036424328,1451869132941118,1451683184902976,1451389124208272,
  1450987859205028,1450480275341324,1449867235785672,1449149582018778,1448328134397956,
  1447403692695424,1446377036611632,1445248926264650,1444020102656666,1442691288118480,
  1441263186732896,1439736484737840,1438111850909920,1436389936929210,1434571377725864,
  1432656791809218,1430646781579950,1428541933625832,1426342819001570,1424049993493204,
  1421663997867480,1419185358106610,1416614585628744,1413952177494504],
 [1411198616599886,1408354371855752,1405419898354216,1402395637522058,1399282017261412,
  1396079452077834,1392788343195916,1389409078662502,1385942033437616,1382387569473132,
  1378746035779212,1375017768478480,1371203090847944,1367302313348558,1363315733642362,
  1359243636597062,1355086294277930,1350843965926798,1346516897927994,1342105323760932,
  1337609463939100,1333029525935130,1328365704091604,1323618179517216,1318787119967840,
  1313872679712064,1308874999380662,1303794205799422,1298630411804756,1293383716041396,
  1288054202741442,1282641941484024,1277146986934652,1271569378563412,1265909140340936,
  1260166280411118,1254340790739390,1248432646735292,1242441806847980,1236368212133204,
  1230211785790158,1223972432666488,1217650038729588,1211244470502188,1204755574460054,
  1198183176389442,1191527080701760,1184787069702676,1177962902812670,1171054315735798,
  1164061019573110,1156982699876916,1149819015641718,1142569598227260,1135234050208764,
  1127811944148954,1120302821285982,1112706190130814,1105021524967058,1097248264245514,
  1089385808864982,1081433520330102,1073390718775982,1065256680848406],
 [1057030637427306,1048711771179782,1040299213927664,1031792043812900,1023189282242280,
  1014489890590980,1005692766642112,996796740736822,987800571606604,978702941856104,
  969502453060902,960197620440424,950786867061178,941268517519820,931640791049040,921901793981738,
  912049511500304,902081798587712,891996370085568,881790789750538,871462458184844,861008599497754,
  850426246533230,839712224472938,828863132593276,817875323918580,806744882469188,795467597750794,
  784038936068666,772454008174084,760707532657694,748793794391162,736706597179000,724439209610008,
  711984302883028,699333879112556,686479188280242,673410631566556,660117648243626,646588582595272,
  632810526397634,618769131265556,604448383535096,589830332151546,574894757032754,559618761233580,
  543976264428658,527937366955944,511467541665786,494526593079420,477067296549280,459033588589248,
  440358113431298,420958822243890,400734136413254,379555857554180,357258393223420,333621651597628,
  308342368829380,280982590712510,250868158147878,216860998419438,176736025262518,124733513924856]]
private def pvi_r256_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s2 pvo_r256_2
private def pvo_r256_3 : List ℤ := pzigCatZ 0
 [
 [9,15,0,21,7,8,1,15,13,33,23,21,3,33,17,51,51,105,109,206,1102,772,12197,75617,272707,711819,
  1396677,2022549,2247535,4034777,18399181,76714249,238531203,575719989,1111299545,1723862653,
  2097171455,1839253317,807557729,571440750,1396662686,988242456,313956839,1217440537,729638829,
  595259124,1119339972,150645364,990765513,673117001,637204246,928753664,263364775,995296857,
  39038091,963433742,249152174,899130557,376728033,840458072,438572778,804847319,448354223,
  796605862],
 [413588890,810948623,338390481,840902588,215675184,856286735,75006067,888928970,162974927,
  788606695,308585498,749857216,565935221,557319295,765737470,258130998,841458605,76484810,
  777060340,366433233,642672939,679960778,288410086,771779971,55564514,762051394,450763381,
  535625837,736861376,167013828,849244313,279471966,702756964,656922897,296629247,808215492,
  240948661,669564877,686454100,283459586,810704313,256616580,572718894,745169953,156557445,
  789081540,447015389,536533173,773134182,46011741,737405097,618526396,329098960,848500687,
  264762710,567329468,794760843,44736071,784611700,572421023,325170245,855922886,322712655,
  580634993],
 [802917220,54321125,756897795,670414112,213992020,855120435,499160740,427365002,832758543,
  232188990,689279074,866999353,91257352,761794154,736299893,121926805,825862374,579784817,
  325895413,863476556,427176113,496260289,875161118,277877197,649321635,873445400,106538041,
  813188369,813550604,126621202,900664479,650293532,267794200,885350665,598329466,401979446,
  1006574333,423270348,552383494,924192923,377430470,725021876,894108757,206924632,803650316,
  897945773,50937304,873509222,848885077,98109039,949794552,774934583,247003203,1010761518,
  678848899,395854429,1058071090,604135337,474944003,982114906,273719833,972658757,1498356824,
  822733643],
 [370605143,938463530,604520871,58090552,118266527,629025344,744106935,243840432,155516102,
  201382844,708745003,550630372,187650615,500927100,1032095173,1247993470,1640263615,1534108712,
  747593979,1741879046,2976760983,3323853336,6951684527,10530997776,19790490551,30108497228,
  51651617767,78828799250,120506011873,173058037350,231942308249,276798169780,266377001137,
  133653581706,202851867164,777112091833,1548262185684,2303119792623,2923002017380,3404636044553,
  4238473665894,5269026761513,5853139329274,4412881959979,2053203902948,2257346168728,
  10833628806745,24451596361308,22812303291611,8916310956516,5838893761272,37200865370663,
  57691649855562,35468968920031,13595013907437,112611917657870,64194727414959,7192382563320,
  221125379247400,73892717101448,62874455527495,382196785546010,1116003129087798,1347885268516500],
 [841939523546900]]
private def phbv_g4 : List ℤ := pzigCatZ 0
 [
 [209616541368152,295477510393362,360702475773086,415138202152440,462612141594160,505093810940352,
  543757024428736,579369059128864,612464574371902,643434089864034,672573347614346,700112831232276,
  726236404646154,751093607137322,774808061414640,797483400024442,819207551452218,840055909441740,
  860093722241356,879377924636976,897958564031222,915879925537746,933181430390874,949898361203190,
  966062453262192,981702380976650,996844161382698,1011511491400428,1025726031697422,
  1039507647163858,1052874611858318,1065843784652436,1078430760550212,1090650001687678,
  1102514951260526,1114038133030192,1125231238585216,1136105204156008,1146670278476738,
  1156936082941570,1166911665101794,1176605546386210,1186025764791866,1195179913180498,
  1204075173723106,1212718348957488,1221115889858610,1229273921266876,1237198264973178,
  1244894460720296,1252367785346878,1259623270271644,1266665717491058,1273499714242626,
  1280129646467914,1286559711193646,1292793927935684,1298836149218852,1304690070295246,
  1310359238134694,1315847059753116,1321156809937586,1326291638420842,1331254576552572],
 [1336048543510050,1340676352086516,1345140714091916,1349444245397314,1353589470651330,
  1357578827694316,1361414671693596,1365099279021046,1368634850892288,1372023516785190,
  1375267337653742,1378368308952032,1381328363481798,1384149374075922,1386833156129158,
  1389381469986552,1391796023199070,1394078472655292,1396230426597268,1398253446528014,
  1400149049017584,1401918707414096,1403563853465618,1405085878858398,1406486136676492,
  1407765942787512,1408926577158838,1409969285108356,1410895278493504,1411705736842096,
  1412401808428230,1412984611296282,1413455234235838,1413814737710206,1414064154740960,
  1414204491750838,1414236729367122,1414161823187522,1413980704510452,1413694281031424,
  1413303437507244,1412809036389518,1412211918428928,1411512903251608,1410712789908910,
  1409812357401724,1408812365180454,1407713553621720,1406516644482726,1405222341334208,
  1403831329972846,1402344278813888,1400761839264776,1399084646080430,1397313317700874,
  1395448456571792,1393490649448578,1391440467684402,1389298467502784,1387065190255134,
  1384741162663642,1382326897049940,1379822891549846,1377229630314546],
 [1374547583698468,1371777208434132,1368918947794192,1365973231740890,1362940477063070,
  1359821087500934,1356615453858640,1353323954104854,1349946953461300,1346484804479398,
  1342937847104966,1339306408731004,1335590804238508,1331791336025278,1327908294022604,
  1323941955699734,1319892586055976,1315760437600252,1311545750317900,1307248751624514,
  1302869656306496,1298408666448090,1293865971344504,1289241747400748,1284536158015818,
  1279749353451708,1274881470686788,1269932633252982,1264902951056166,1259792520179112,
  1254601422666282,1249329726289726,1243977484295210,1238544735127714,1233031502135318,
  1227437793250406,1221763600647080,1216008900373534,1210173651958062,1204257797987290,
  1198261263655052,1192183956280244,1186025764791866,1179786559179262,1173466189905462,
  1167064487281326,1160581260798004,1154016298415024,1147369365801092,1140640205524444,
  1133828536189286,1126934051514626,1119956419351414,1112895280633552,1105750248258008,
  1098520905888722,1091206806678602,1083807471903358,1076322389500272,1068751012504452,
  1061092757374294,1053347002197162,1045513084765312,1037590300511174],
 [1029577900289924,1021475087996076,1013281017999408,1004994792383956,996615457972104,
  988142003113744,979573354218278,970908372004720,962145847442248,953284497350322,944322959623788,
  935259788044148,926093446633334,916822303500842,907444624128672,897958564031222,888362160718838,
  878653324883942,868829830717268,858889305248534,848829216590376,838646860946288,828339348221908,
  817903586053894,807336262040750,796633823924468,785792457429494,774808061414640,763676219932308,
  752392170715206,740950769520434,729346449650468,717573175834700,705624391487194,693492958147210,
  681171085646824,668650251219336,655921105341554,642973361564210,629795666888284,616375448336656,
  602698730174152,588749914636700,574511516886530,559963841988614,545084587667254,529848350943878,
  514226008697382,498183930502132,481682964818750,464677113497552,447111769108744,428921325218834,
  410025863932624,390326444791652,369698198923064,347979834578084,324956976061882,300334235762970,
  273685033830162,244352720129416,211228779471226,172145914557642,121493989687096]]
private def pvi_r256_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s3 pvo_r256_3
private def pvo_r256_4 : List ℤ := pzigCatZ 0
 [
 [9,11,27,4,14,12,13,7,4,18,30,51,25,0,64,271,514,585,362,20,469,170,620,14,1251,2367,703,11860,
  46626,87684,2516,573759,2133869,4438743,4630987,3947078,26520202,47742202,1523674,238932155,
  794415169,1614520397,2323338195,2317712325,1254413783,390395098,1406410048,905250770,546861725,
  1261131543,352714843,975245682,876449682,499655487,1062025021,71190184,1050941966,237241952,
  964609871,424673995,864434694,535616170,816155639,540645409],
 [746385838,577012784,816327615,452388465,801124816,367900954,837057405,243847275,900553854,
  35954282,921930873,253511984,790973958,453981681,665934965,711263532,365516708,815134419,
  48234623,823794254,302630863,678544795,604948844,394610716,798193731,905423,814962518,433305059,
  599125279,772390890,179049926,874764647,316024590,670197518,701848813,205828709,814987776,
  350850639,590377773,760002810,105073812,810385099,442558074,449018122,806067709,140383506,
  771618210,635080325,275954783,813846606,400085165,580809605,778963050,92017999,786000349,
  629571396,221332052,830955421,476768404,493458882,841756951,187036974,642601318,829717279],
 [14401037,742876840,626986209,246194707,863112692,468403803,468996725,940272864,371274529,
  586570183,878694728,185836861,678979209,761306906,54078101,685942963,766150920,23685218,
  870072097,634507000,132647374,890657111,631581900,283820070,932918967,575864414,415083582,
  960593657,458765580,523607826,930286999,384204966,532312964,932107437,388205772,612640848,
  978655037,275824994,667658892,889343151,243872308,734331670,999200011,159958126,762611630,
  932092813,189083428,830563500,867965175,186339884,850659284,1020531755,174800466,693146470,
  752284953,212889131,1254629828,1375881135,401689316,816944572,1246782951,686102140,130827372,
  420927015],
 [101739876,331799204,478413439,441727696,384245603,264226100,433926777,935426084,668066189,
  296597850,1739088393,1321918520,1546684747,832890244,1373210141,2332423640,4767700657,
  8422406884,12462657331,18836426994,31589372187,49431158128,71836932521,106076483940,
  146377523749,190553027938,227663939195,233372432572,175884126827,5519265292,302174849202,
  735272012305,1152259228582,1272420997987,773489431292,277009261300,950885103405,142576167650,
  969557048870,443142506586,1186052691097,1821321352659,2801709228023,3785396878369,6740763349647,
  4116061373949,5914924811017,7063051412897,864879813954,24997995123476,24302671960308,
  5577807020052,10842504634689,73798643022014,27565177498804,16806364877429,154183100916104,
  19120605091165,67901581541140,176333026539018,102819738379206,100051018962861,456889671520114,
  1368178487619448],
 [1353100589015114]]
private def phbv_g5 : List ℤ := pzigCatZ 0
 [
 [196307471668430,276716916621238,337800588547998,388780056791382,433239759070202,473024162758832,
  509232553742402,542583492782428,573577692374312,602580877167726,629870011784310,655660945862336,
  680125869357168,703404826933426,725613592190176,746849217788528,767194049418198,786718693888758,
  805484256676808,823544057638688,840944966544352,857728456736676,873931446498880,889586978263704,
  904724772367202,919371682609414,933552074140870,947288139305928,960600163483118,973506750291890,
  986025013525906,998170741645582,1009958539489760,1021401950957896,1032513565704120,
  1043305112325464,1053787540082754,1063971090838238,1073865362608752,1083479365902480,
  1092821573819436,1101899966741946,1110722072314858,1119295001310448,1127625479886012,
  1135719878669498,1143584239047602,1151224296979556,1158645504616426,1165853049969104,
  1172851874836770,1179646691181000,1186241996107692,1192642085599362,1198851067123360,
  1204872871226864,1210711262216786,1216369848011676,1221852089242988,1227161307674712,
  1232300694002948,1237273315090488,1242082120685790,1246729949670696],
 [1251219535876736,1255553513505994,1259734422188928,1263764711708516,1267646746417232,
  1271382809370944,1274975106201618,1278425768748674,1281736858467146,1284910369629112,
  1287948232333528,1290852315338190,1293624428726506,1296266326420588,1298779708551318,
  1301166223695102,1303427470986296,1305565002113552,1307580323207674,1309474896628014,
  1311250142653862,1312907441086842,1314448132769816,1315873521027448,1317184873033162,
  1318383421106900,1319470363947760,1320446867805340,1321314067593264,1322073067948228,
  1322724944237584,1323270743518316,1323711485450086,1324048163164776,1324281744094882,
  1324413170762886,1324443361533634,1324373211331586,1324203592324728,1323935354576756,
  1323569326669086,1323106316294156,1322547110821314,1321892477836616,1321143165657684,
  1320299903824718,1319363403568754,1318334358258078,1317213443823752,1316001319165080,
  1314698626535820,1313305991911898,1311824025341288,1310253321276762,1308594458892068,
  1306848002382134,1305014501247806,1303094490565636,1301088491243148,1298997010260018,
  1296820540895550,1294559562942816,1292214542909764,1289785934207632],
 [1287274177326890,1284679700000982,1282002917358098,1279244232061114,1276404034435928,
  1273482702588284,1270480602509222,1267398088169248,1264235501601260,1260993172972324,
  1257671420644260,1254270551223082,1250790859597216,1247232628964484,1243596130847722,
  1239881625098976,1236089359892096,1232219571703590,1228272485281540,1224248313602360,
  1220147257815138,1215969507173294,1211715238953214,1207384618359522,1202977798416612,
  1198494919845970,1193936110928874,1189301487353904,1184591152048740,1179805194995624,
  1174943693029812,1170006709620342,1164994294632270,1159906484069616,1154743299798030,
  1149504749246252,1144190825085266,1138801504884026,1133336750740474,1127796508886554,
  1122180709265724,1116489265081436,1110722072314858,1104879009210030,1098959935724454,
  1092964692942970,1086893102452600,1080744965675848,1074520063159690,1068218153817332,
  1061838974119496,1055382237231724,1048847632093920,1042234822437984,1035543445739002,
  1028773112095114,1021923403030652,1014993870216706,1007984034102680,1000893382451828,
  993721368773038,986467410640436,979130887891476,971711140693316],
 [964207467466180,956619122651276,948945314309524,941185201535854,933337891672240,925402437300728,
  917377832995626,909263011811700,901056841482470,892758120299680,884365572641588,875877844113658,
  867293496260850,858611000805402,849828733358128,840944966544352,831957862477712,822865464505908,
  813665688141778,804356311080758,794934962191242,785399109347410,775746045954100,765972875989722,
  756076497365300,746053583364418,735900561889260,725613592190176,715188538698944,704620941516328,
  693905983020066,683038449955948,672012690247534,660822563602662,649461384799010,637921858285580,
  626196002427084,614275061324554,602149401640680,589808391206268,577240255333436,564431905640806,
  551368734704704,538034367842710,524410360599656,510475826726168,496206976141258,481576534822400,
  466553007622390,451099728829362,435173620829276,418723543352348,401688055478882,383992313497386,
  365543658922416,346225151112934,325885739129942,304324658518666,281265276553488,256308097987016,
  228838165017052,197817344809528,161215947101752,113780037504272]]
private def pvi_r256_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s4 pvo_r256_4
private def pvo_r256_5 : List ℤ := pzigCatZ 0
 [
 [9,1,13,33,15,12,3,0,8,89,156,331,548,547,246,30,231,188,261,132,496,947,324,292,173,306,440,63,
  333,134,1098,1050,5211,26671,58233,27871,263632,1019492,1757672,31214,8620853,24984419,32448063,
  11823256,145564912,307723260,249432530,365896203,1578350337,2738834047,2781494955,1271838675,
  658724006,1229635812,34830421,1214077041,687553735,881352004,911626452,481155325,1053441167,
  241880948,1070189886,116840061],
 [1021715567,51580202,966234102,7656693,1011145605,146089266,939141680,254977047,900598549,
  453065134,768494408,638952299,569798545,791926660,301687416,871129399,14028884,844441442,
  338776525,698122499,635124452,414347494,834399969,7464551,847154548,438544877,620526255,
  785222316,186813382,894747535,326777698,694920590,731568023,228903939,848578852,335269281,
  597396721,754927602,62133932,818097993,513939718,462588312,829967041,157811780,694332424,
  716958399,160868691,870595088,461137147,499349831,845843308,289547895,572549011,664989318,
  205747660,879520503,625618676,324837774,914319615,393071462,500010740,824181165,122408994,
  561238384],
 [837115573,300204002,706740346,777794551,204023213,724567410,817420355,308360655,879842146,
  648847275,334465103,833371898,482705153,217117681,749957574,665946769,250155883,992568428,
  491437903,260797589,998503512,470097921,297790801,1009550386,541901005,453916505,913404854,
  568523249,458646991,918340550,596430111,286239705,800781786,436042437,536840803,1093566330,
  572995377,503709995,1025863078,562076031,340001549,865324796,653207589,146712709,1039475450,
  971570861,105016693,552894046,677135971,436563979,1195210152,1230517801,158979302,1070229392,
  1369355445,897561706,171193840,619629523,279918598,397783514,803190297,618312962,312572739,
  273828102],
 [512860845,698026212,792060759,997544236,1120990801,1124315980,1591784495,1856202928,1897256873,
  2272520116,4643484965,8401149166,12665098701,19338657144,29054755613,42213549286,62530787439,
  88040765018,119694587747,152874484674,185151306413,204379764672,190281288345,119874319358,
  28522052004,271035824909,588442145760,903773504057,1087590689684,978100935489,499153839690,
  206241159884,725868917299,610147320978,86014120108,569138602985,56859589410,822875858608,
  534477316021,406582281611,474613012851,1944513862088,702802942639,281324769296,319856962595,
  1842694100157,7463437895061,401077972094,5292423964765,13940146092245,18421250963429,
  38987072946068,10901518815096,33383235758869,98965144881184,24968691112073,36779944407560,
  118611274195202,18035327973408,71280997325948,164676242282212,122206121901366,131688467432807,
  808018275966118],
 [1803630150112150]]
private def phbv_g6 : List ℤ := pzigCatZ 0
 [
 [204094463948220,287693536487530,351200234281172,404201921660002,450425221398790,491787765958710,
  529432446955372,564106328533556,596329985113954,626483648664780,654855270253334,681669261695644,
  707104643261992,731307014814232,754396742380404,776474728441074,797626585119192,817925720007592,
  837435662473678,856211847429858,874303003844482,891752250197002,908597969220174,924874514051656,
  940612783953732,955840697944856,970583587675904,984864525802168,998704602368884,
  1012123158951318,1025137988201550,1037765504865984,1050020893118354,1061918234108374,
  1073470616888080,1084690235296570,1095588472922560,1106175977895578,1116462728960112,
  1126458094047102,1136170882361774,1145609390846874,1154781445748784,1163694439905096,
  1172355366281772,1180770848212532,1188947166729720,1196890285322726,1204605872414866,
  1212099321811544,1219375771339896,1226440119872410,1233297042903142,1239951006824746,
  1246406282036814,1252666955000814,1258736939343646,1264619986100338,1270319693176332,
  1275839514101116,1281182766137166,1286352637801516,1291352195851258,1296184391779082],
 [1300852067860300,1305357962788746,1309704716935226,1313894877259058,1317930901900248,
  1321815164477390,1325549958113962,1329137499213760,1332579931004218,1335879326864856,
  1339037693456492,1342056973665544,1344939049376588,1347685744085136,1350298825361710,
  1352780007177334,1355130952099746,1357353273368938,1359448536859892,1361418262939844,
  1363263928226766,1364986967255318,1366588774056014,1368070703652922,1369434073484844,
  1370680164754558,1371810223710350,1372825462863820,1373727062147576,1374516170016300,
  1375193904494288,1375761354172478,1376219579157698,1376569611976720,1376812458437496,
  1376949098449854,1376980486807716,1376907553934806,1376731206595676,1376452328573776,
  1376071781318132,1375590404560178,1375009016902098,1374328416378038,1373549380989372,
  1372672669215214,1371699020499228,1370629155713768,1369463777602270,1368203571200814,
  1366849204239648,1365401327525482,1363860575305268,1362227565612128,1360502900594080,
  1358687166826156,1356780935606434,1354784763236518,1352699191286944,1350524746847912,
  1348261942765800,1345911277865782,1343473237160934,1340948292048102],
 [1338336900490834,1335639507189618,1332856543739668,1329988428776420,1327035568108954,
  1323998354841458,1320877169482862,1317672380044726,1314384342127488,1311013398995050,
  1307559881637800,1304024108823988,1300406387139478,1296707011015790,1292926262746346,
  1289064412490828,1285121718267478,1281098425933194,1276994769151214,1272810969346154,
  1268547235646154,1264203764811806,1259780741151576,1255278336423316,1250696709721486,
  1246036007349620,1241296362677570,1236477895982970,1231580714276370,1226604911109362,
  1221550566365056,1216417746030132,1211206501947664,1205916871549852,1200548877569698,
  1195102527730620,1189577814412884,1183974714295658,1178293187973418,1172533179545266,
  1166694616175708,1160777407625208,1154781445748784,1148706603960746,1142552736663484,
  1136319678638096,1130007244394442,1123615227477984,1117143399730584,1110591510502186,
  1103959285810004,1097246427441626,1090452611998034,1083577489872274,1076620684159034,
  1069581789490096,1062460370789976,1055255961945758,1047968064384360,1040596145549968,
  1033139637273634,1025597934026204,1017970391044948,1010256322323216],
 [1002454998451438,994565644296504,986587436505226,978519500816078,970360909161682,
  962110676542544,953767757650426,945331043217232,936799356062494,928171446809414,919445989235738,
  910621575221728,901696709252678,892669802428136,883539165923740,874303003844482,864959405399968,
  855506336322732,845941629439584,836262974293080,826467905695168,816553791077370,806517816481132,
  796356971007440,786068029515738,775647533327676,765091768649870,754396742380404,743558154904130,
  732571369409538,721431377172178,710132758141990,698669636039786,687035627004430,675223780628724,
  663226511966668,651035522772860,638641709825236,626035057657770,613204512351552,600137832148332,
  586821409485654,573240057502420,559376751976362,545212316810110,530725037252656,515890179534130,
  500679387744496,485059917408304,468993648382984,452435794280778,435333186234196,417621946126618,
  399224261396718,380043798044798,359958976707406,338812754658852,316396403655486,292422317691456,
  266475154611554,237915562882576,205664229717926,167610952471598,118293387231156]]
private def pvi_r256_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s5 pvo_r256_5
private def pvo_r256_6 : List ℤ := pzigCatZ 0
 [
 [9,1,0,17,37,15,28,99,214,293,192,182,579,198,216,586,59,22,158,489,228,470,579,719,129,59,213,
  42,422,372,68,289,665,437,1342,8022,12998,5114,102741,293991,517779,611596,3683936,9219340,
  2896402,25571007,88120033,88320707,61974542,463294362,699594672,304012294,1198219103,2798676205,
  3182608629,1520656311,531955370,821606714,565029015,1316188181,78899507,1166790362,262864128,
  1001833431],
 [477886187,962149122,491987274,911280359,474469135,931247324,369246736,962851409,197224659,
  975191836,26085259,938277993,278784998,824848416,522635267,631771347,730246550,353603690,
  864039473,8860644,860855978,409650993,665298543,748030590,278772814,902524749,215338386,
  786466280,664007813,400289749,893371682,141673723,783506259,631412842,342654418,844115467,
  260785548,651550456,745412561,117947617,848358568,497594955,471342823,829788644,165941081,
  734191707,824871304,22805726,741207005,421227946,463725270,862787007,333119426,633360280,
  885518175,85867190,726207124,694711677,138479201,897430652,653508971,175057425,720173752,
  508410363],
 [296199747,860510580,551703669,652253515,1059567646,515798703,233772847,716564536,387124903,
  450711575,630985642,607567107,563100797,961973178,206744083,285652973,1093678566,339275355,
  603168525,884524820,394449621,495099123,1022816224,346938387,469730651,1096381586,416048979,
  285483435,817378294,358934379,542025869,952995752,614123629,472557809,1053288338,679707143,
  362681513,949159376,634051057,220764769,903353190,941243687,286835282,552242432,715194829,
  138698515,1081132480,1064241807,292754134,907460720,1717295595,951417106,126933497,662312127,
  432318886,77182425,887185259,907752372,515477121,264015202,258377075,640989230,917940843,
  972523602],
 [1058802643,1232401250,1463628553,1685722438,2143412207,2859406684,4004527155,6643453826,
  11372984123,17463585658,25261756825,36209473972,52310190751,73178976608,99191633075,
  129555814570,159129646275,182041935240,188804650609,161406680032,81504438897,70052753451,
  293744797130,571040244733,843285479900,1008833866693,951801927216,608370539583,38725181650,
  522157801956,742792130745,452888551914,117997691554,403814704283,48223290566,631841879034,
  829054500925,40466797424,137564026867,1334428647632,1644036238285,95561672742,348685065938,
  1047167575068,2065010671473,5180809856736,5997767289381,1954474517742,10603566300869,
  2990503332802,15213578996387,36416080150990,30589857601392,29979840200111,55085987717012,
  80540610370918,2736904993439,101192519729004,67344718141370,17723151920812,117365133511134,
  172102878484270,10123369410071,378249934507960],
 [1945563267969734]]
private def phbv_g7 : List ℤ := pzigCatZ 0
 [
 [205065480874096,289062291366962,352871133948224,406124986596750,452568202180130,494127536648450,
  531951319134244,566790168077280,599167134626738,629464259774308,657970864567424,684912428502576,
  710468823571884,734786342355306,757985923544388,780168949681792,801421440205880,821817151959600,
  841419916562998,860285432670268,878462661086788,895994925436092,912920791063850,929274774549082,
  945087922162994,960388285753902,975201317492668,989550199806980,1003456123081840,
  1016938520913616,1030015270606202,1042702865002170,1055016560516756,1066970505293330,
  1078577850657498,1089850848462792,1100800936457444,1111438813431410,1121774505604890,
  1131817425478484,1141576424168824,1151059838092890,1160275530731870,1169230930096134,
  1177933062421972,1186388582554828,1194603801410212,1202584710849910,1210337006265808,
  1217866107125324,1225177175699758,1232275134168880,1239164680271270,1245850301649266,
  1252336289019668,1258626748286038,1264725611695078,1270636648128048,1276363472608094,
  1281909555095500,1287278228635230,1292472696914272,1297496041280382,1302351227268514],
 [1307041110676634,1311568443228408,1315935877856698,1320145973638442,1324201200408706,
  1328103943079006,1331856505682780,1335461115168768,1338919924961206,1342235018304100,
  1345408411405318,1348442056394926,1351337844110906,1354097606724386,1356723120215432,
  1359216106709596,1361578236684594,1363811131055698,1365916363147832,1367895460561654,
  1369749906940422,1371481143643856,1373090571334828,1374579551484178,1375949407798672,
  1377201427576638,1378336862995624,1379356932335972,1380262821144040,1381055683338492,
  1381736642262830,1382306791687164,1382767196761976,1383118894926472,1383362896773922,
  1383500186876254,1383531724569998,1383458444705538,1383281258361530,1383001053526180,
  1382618695747022,1382135028750660,1381550875033936,1380867036427786,1380084294635066,
  1379203411743498,1378225130714784,1377150175850960,1375979253238896,1374713051173852,
  1373352240562928,1371897475309168,1370349392677068,1368708613640156,1366975743211282,
  1365151370756216,1363236070291090,1361230400764218,1359134906322754,1356950116564630,
  1354676546776180,1352314698155836,1349865058024210,1347328100020906],
 [1344704284288316,1341994057642676,1339197853732588,1336316093185228,1333349183740384,
  1330297520372514,1327161485400882,1323941448587940,1320637767225950,1317250786211962,
  1313780838111110,1310228243208244,1306593309547864,1302876332962302,1299077597088044,
  1295197373370108,1291235921054302,1287193487167234,1283070306483840,1278866601482204,
  1274582582285428,1270218446590234,1265774379581964,1261250553835646,1256647129202654,
  1251964252682592,1247202058279842,1242360666844284,1237440185895586,1232440709430432,
  1227362317711990,1222205077040882,1216969039506838,1211654242720146,1206260709521966,
  1200788447672462,1195237449515644,1189607691619732,1183899134391718,1178111721664750,
  1172245380256802,1166300019499008,1160275530731870,1154171786767436,1147988641315394,
  1141725928370780,1135383461560954,1128961033449130,1122458414791666,1115875353745990,
  1109211575025798,1102466778999872,1095640640730570,1088732808947612,1081742904952496,
  1074670521448382,1067515221289842,1060276536146340,1052953965072738,1045546972979494,
  1038054988994490,1030477404707656,1022813572288684,1015062802467120],
 [1007224362363100,999297473155668,991281307574386,983174987198268,974977579544484,
  966688094927224,958305483065004,949828629412180,941256351187636,932587393070428,923820422528560,
  914954024742904,905986697083570,896916843090616,887742765904792,878462661086788,869074608755270,
  859576564964374,849966352230186,840241649102834,830399978665684,820438695825324,810354973235280,
  800145785671628,789807892649618,779337819035600,768731833367132,757985923544388,747095769496006,
  736056712349994,724863719551976,713511345265006,701993685252418,690304325280684,678436281874766,
  666381934001888,654132943936222,641680165145452,629013534513130,616121945529296,602993098193284,
  589613320202160,575967352440542,562038089690294,547806264620242,533250059167452,518344621886606,
  503061461959208,487367679121952,471224971868678,454588340732160,437404363884248,419608859296436,
  401123644199844,381851926268056,361671547701454,340424718614716,317901717701210,293813570616642,
  267742959139160,239047489903128,206642715092982,168408392385762,118856189763858]]
private def pvi_r256_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r256_s6 pvo_r256_6
private def pvo_r256_7 : List ℤ := pzigCatZ 0
 [
 [9,1,2,5,29,57,94,211,270,141,217,534,399,94,457,206,318,83,272,212,703,38,348,375,629,275,149,
  299,139,238,358,438,251,680,3393,5066,16363,44306,63347,238892,397361,455380,2649835,1666588,
  1664055,21767924,7178396,3780824,128269919,150894809,63480629,484897418,942571282,689091592,
  860426231,2827590869,3284591047,1627308965,413580392,564434292,966771433,1207731591,250073504,
  1108527070],
 [131202355,1102122847,11644278,1071132262,25391085,1048868971,122452682,1004728852,280017075,
  920159917,471032078,771883424,655001185,560354611,804283658,286773362,891575811,50072526,
  867074468,419591219,678284401,740642280,314945364,903944705,160622642,820710394,616488101,
  473777553,888987064,49780329,848358951,565251862,471906470,850085133,111915492,747010102,
  646756277,269951983,861164530,371541023,594966607,795025994,30015308,850482519,713646060,
  175289420,763498057,322452976,609953190,835087669,94976206,735842540,784860845,48659481,
  840545258,578723789,376381939,944163936,647451399,197000241,648414628,354096615,326425017,
  1087749358],
 [536114907,51421827,550210404,620427583,5797240,1255581030,90882782,341348583,820785118,
  217669581,523705483,814933202,439587159,835228089,753989588,256771757,495342733,1153815746,
  84049509,562422779,905897388,356767937,643026817,1041232914,409953585,370670663,867728996,
  193538291,449454393,1045956976,451482387,451564109,1032651472,709754507,390401281,960594540,
  674643179,295819473,942862268,920589219,274589562,468085200,671379161,9120742,961281472,
  1158895589,250609304,905549950,1520067191,1293757256,125533151,733590627,486637988,96272481,
  747863925,922002214,871175723,108410530,289948001,524482192,882196303,1105817818,1054484671,
  1193613548],
 [1458714175,1742200372,2153651735,2879064568,4208244343,6477740118,10531617405,16705155858,
  24508362405,34565841762,48850327413,68304063106,92586687573,120155964840,149131232229,
  172971123980,182732502963,166971624868,107814868073,12019973093,199654123516,446035518325,
  710491470006,923658434299,983910174116,804645785391,374682358580,186768048418,634082789591,
  701913062266,328008971411,194245053959,372421629102,33965809626,650442905303,793136924016,
  288327640651,77038743710,1156506223201,1616263378220,476056630277,472917139657,901194894587,
  2741294833506,4235059845975,6211593787112,4560007005721,4745489902322,11351155968985,
  7415320443894,23695104600117,9252154429728,46242772639932,4000870520022,26088136021195,
  95781023058457,4435480355129,77479280410763,83489147472401,64841095029885,62185240214132,
  193218931812072,3910051087846,145450247691796],
 [1976732794546046]]
private abbrev pl_r256 : List ℕ := [1, 2, 3, 3, 3, 3, 3, 3]
private abbrev ptau_r256 : List ℕ :=
  [16430684, 10460158, 29500000, 2230754, 1002839, 1095694, 650947, 327022]
private abbrev pnsub_r256 : List ℕ := [40, 45, 167, 13, 6, 7, 4, 2]
private def pwalks_r256 : List RkmSegWalk := [ ⟨phbv_g0, pvi0, pvo_r256_0⟩,
  ⟨phbv_g1, pvi_r256_1, pvo_r256_1⟩, ⟨phbv_g2, pvi_r256_2, pvo_r256_2⟩,
  ⟨phbv_g3, pvi_r256_3, pvo_r256_3⟩, ⟨phbv_g4, pvi_r256_4, pvo_r256_4⟩,
  ⟨phbv_g5, pvi_r256_5, pvo_r256_5⟩, ⟨phbv_g6, pvi_r256_6, pvo_r256_6⟩,
  ⟨phbv_g7, pvi_r256_7, pvo_r256_7⟩]
private abbrev dP_0 : Prop := bSlideChk 14 257 phbv_g1 pvi_r256_1 pvm_r256_1_1 = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := bSlideChk 14 257 phbv_g1 pvm_r256_1_1 pvm_r256_1_2 = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := bSlideChk 14 257 phbv_g1 pvm_r256_1_2 pvm_r256_1_3 = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := bSlideChk 14 257 phbv_g2 pvi_r256_2 pvm_r256_2_1 = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_1 pvm_r256_2_2 = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_10 pvm_r256_2_11 = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_2 pvm_r256_2_3 = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_3 pvm_r256_2_4 = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_4 pvm_r256_2_5 = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_5 pvm_r256_2_6 = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_6 pvm_r256_2_7 = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_7 pvm_r256_2_8 = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_8 pvm_r256_2_9 = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := bSlideChk 14 257 phbv_g2 pvm_r256_2_9 pvm_r256_2_10 = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := bSlideChk 27 129 phbv_g0 pvi0 pvm_r256_0_1 = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := bSlideChk 13 257 phbv_g2 pvm_r256_2_11 pvo_r256_2 = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := bSlideChk 13 257 phbv_g3 pvi_r256_3 pvo_r256_3 = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := rkmCheckRowFromWalks 128 64 256 pl_r256 ptau_r256 pnsub_r256
  rkmMasksHiHiB_m128_r256 pwalks_r256 rkmRowHiHiB_m128_r256 = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := bSlideChk 7 257 phbv_g5 pvi_r256_5 pvo_r256_5 = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := rkmAllTrueF [ bSlideChk 13 129 phbv_g0 pvm_r256_0_1 pvo_r256_0,
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 128) 256) 1] [129], muxNatListEq [Nat.add
  (highdNatMin (Nat.mul 2 128) 256) 1] [257], muxNatListEq [Nat.add (highdNatMin (Nat.mul 3 128)
  256) 1] [257]] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := rkmAllTrueF [ bSlideChk 6 257 phbv_g4 pvi_r256_4 pvo_r256_4,
  bSlideChk 2 257 phbv_g7 pvi_r256_7 pvo_r256_7] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := rkmAllTrueF [ bSlideChk 4 257 phbv_g6 pvi_r256_6 pvo_r256_6,
  bSlideChk 3 257 phbv_g1 pvm_r256_1_3 pvo_r256_1] = true
private theorem bk_21 : dP_21 := by decide +kernel
private theorem pacc_r256_0_1 : muxFastIterFullT16 40 129 phbv_g0 pvi0 = pvo_r256_0 := bCh 40
    (bSlideChk_sound bk_14) (rkmHd bk_19) rfl
private theorem pwalk_r256_0 : muxFastIterFullT16 40 129 phbv_g0 pvi0 = pvo_r256_0 := pacc_r256_0_1
private theorem pseg_r256_0 : muxFastIterFullT16 40
    (Nat.add (highdNatMin (Nat.mul 1 128) 256) 1)
    phbv_g0 pvi0 = pvo_r256_0 := by
  rw [bDm (rkmHd (rkmTl bk_19))]; exact pwalk_r256_0
private theorem pacc_r256_1_1 : muxFastIterFullT16 28 257 phbv_g1 pvi_r256_1 = pvm_r256_1_2 := bCh
    28 (bSlideChk_sound bk_0) bk_1 rfl
private theorem pacc_r256_1_2 : muxFastIterFullT16 42 257 phbv_g1 pvi_r256_1 = pvm_r256_1_3 := bCh
    42 pacc_r256_1_1 bk_2 rfl
private theorem pacc_r256_1_3 : muxFastIterFullT16 45 257 phbv_g1 pvi_r256_1 = pvo_r256_1 := bCh 45
    pacc_r256_1_2 (rkmHd (rkmTl bk_21)) rfl
private theorem pwalk_r256_1 : muxFastIterFullT16 45 257 phbv_g1 pvi_r256_1 = pvo_r256_1 :=
    pacc_r256_1_3
private theorem pseg_r256_1 : muxFastIterFullT16 45
    (Nat.add (highdNatMin (Nat.mul 2 128) 256) 1)
    phbv_g1 pvi_r256_1 = pvo_r256_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl bk_19)))]; exact pwalk_r256_1
private theorem pacc_r256_2_1 : muxFastIterFullT16 28 257 phbv_g2 pvi_r256_2 = pvm_r256_2_2 := bCh
    28 (bSlideChk_sound bk_3) bk_4 rfl
private theorem pacc_r256_2_2 : muxFastIterFullT16 42 257 phbv_g2 pvi_r256_2 = pvm_r256_2_3 := bCh
    42 pacc_r256_2_1 bk_6 rfl
private theorem pacc_r256_2_3 : muxFastIterFullT16 56 257 phbv_g2 pvi_r256_2 = pvm_r256_2_4 := bCh
    56 pacc_r256_2_2 bk_7 rfl
private theorem pacc_r256_2_4 : muxFastIterFullT16 70 257 phbv_g2 pvi_r256_2 = pvm_r256_2_5 := bCh
    70 pacc_r256_2_3 bk_8 rfl
private theorem pacc_r256_2_5 : muxFastIterFullT16 84 257 phbv_g2 pvi_r256_2 = pvm_r256_2_6 := bCh
    84 pacc_r256_2_4 bk_9 rfl
private theorem pacc_r256_2_6 : muxFastIterFullT16 98 257 phbv_g2 pvi_r256_2 = pvm_r256_2_7 := bCh
    98 pacc_r256_2_5 bk_10 rfl
private theorem pacc_r256_2_7 : muxFastIterFullT16 112 257 phbv_g2 pvi_r256_2 = pvm_r256_2_8 := bCh
    112 pacc_r256_2_6 bk_11 rfl
private theorem pacc_r256_2_8 : muxFastIterFullT16 126 257 phbv_g2 pvi_r256_2 = pvm_r256_2_9 := bCh
    126 pacc_r256_2_7 bk_12 rfl
private theorem pacc_r256_2_9 : muxFastIterFullT16 140 257 phbv_g2 pvi_r256_2 = pvm_r256_2_10 :=
    bCh 140 pacc_r256_2_8 bk_13 rfl
private theorem pacc_r256_2_10 : muxFastIterFullT16 154 257 phbv_g2 pvi_r256_2 = pvm_r256_2_11 :=
    bCh 154 pacc_r256_2_9 bk_5 rfl
private theorem pacc_r256_2_11 : muxFastIterFullT16 167 257 phbv_g2 pvi_r256_2 = pvo_r256_2 := bCh
    167 pacc_r256_2_10 bk_15 rfl
private theorem pwalk_r256_2 : muxFastIterFullT16 167 257 phbv_g2 pvi_r256_2 = pvo_r256_2 :=
    pacc_r256_2_11
private theorem pseg_r256_2 : muxFastIterFullT16 167
    (Nat.add (highdNatMin (Nat.mul 3 128) 256) 1)
    phbv_g2 pvi_r256_2 = pvo_r256_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_19))))]; exact pwalk_r256_2
private theorem pwalk_r256_3 : muxFastIterFullT16 13 257 phbv_g3 pvi_r256_3 = pvo_r256_3 :=
    (bSlideChk_sound bk_16)
private theorem pseg_r256_3 : muxFastIterFullT16 13
    (Nat.add (highdNatMin (Nat.mul 3 128) 256) 1)
    phbv_g3 pvi_r256_3 = pvo_r256_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_19))))]; exact pwalk_r256_3
private theorem pwalk_r256_4 : muxFastIterFullT16 6 257 phbv_g4 pvi_r256_4 = pvo_r256_4 :=
    (bSlideChk_sound (rkmHd bk_20))
private theorem pseg_r256_4 : muxFastIterFullT16 6
    (Nat.add (highdNatMin (Nat.mul 3 128) 256) 1)
    phbv_g4 pvi_r256_4 = pvo_r256_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_19))))]; exact pwalk_r256_4
private theorem pwalk_r256_5 : muxFastIterFullT16 7 257 phbv_g5 pvi_r256_5 = pvo_r256_5 :=
    (bSlideChk_sound bk_18)
private theorem pseg_r256_5 : muxFastIterFullT16 7
    (Nat.add (highdNatMin (Nat.mul 3 128) 256) 1)
    phbv_g5 pvi_r256_5 = pvo_r256_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_19))))]; exact pwalk_r256_5
private theorem pwalk_r256_6 : muxFastIterFullT16 4 257 phbv_g6 pvi_r256_6 = pvo_r256_6 :=
    (bSlideChk_sound (rkmHd bk_21))
private theorem pseg_r256_6 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 3 128) 256) 1)
    phbv_g6 pvi_r256_6 = pvo_r256_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_19))))]; exact pwalk_r256_6
private theorem pwalk_r256_7 : muxFastIterFullT16 2 257 phbv_g7 pvi_r256_7 = pvo_r256_7 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_20)))
private theorem pseg_r256_7 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 3 128) 256) 1)
    phbv_g7 pvi_r256_7 = pvo_r256_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl bk_19))))]; exact pwalk_r256_7
private theorem pwalks_snd_r256 :
    RkmSegWalksSound 128 256 pl_r256 pnsub_r256 pwalks_r256 := by
  dsimp only [RkmSegWalksSound, pl_r256, pnsub_r256, pwalks_r256]
  exact ⟨pseg_r256_0, ⟨pseg_r256_1, ⟨pseg_r256_2, ⟨pseg_r256_3,
    ⟨pseg_r256_4, ⟨pseg_r256_5, ⟨pseg_r256_6, ⟨pseg_r256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 256)` (`FindAllJohnsonRampKickMuxHi128T3`). -/
theorem rkmTrajHiHiB_m128_r256 :
    rkmLo12EqHi 128 64 256 [1, 2, 3, 3, 3, 3, 3, 3]
      [16430684, 10460158, 29500000, 2230754, 1002839, 1095694, 650947, 327022]
      [40, 45, 167, 13, 6, 7, 4, 2] rkmMasksHiHiB_m128_r256 rkmRowHiHiB_m128_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r256 bk_17
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T3`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi128T3 : (0 : ℕ) = 0 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi128T2) rfl).right
end
end QuantumComputation.Specs.DickeSol
