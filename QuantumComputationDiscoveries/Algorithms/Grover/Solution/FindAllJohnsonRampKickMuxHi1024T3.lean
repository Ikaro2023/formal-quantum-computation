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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T2

/-
# High-`m` Checkpointed Walk Part `3` (`FindAllJohnsonRampKickMuxHi1024T3`)

Certifies `1` `T_16` checkpoint walk(s) (`43092` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m1024_r512_s0_c0`. -/
def rkmHbHi_m1024_r512_s0_c0 : List ℤ := altBuildHbFrom 1024 512 51956407114 0 512
/-- Input orbital vector for `m1024_r512_s0_c0`. -/
def rkmViHi_m1024_r512_s0_c0 : List ℤ := [rkmP 1000000000000000]
/-- Part 0 of `rkmVoHi_m1024_r512_s0_c0`. -/
def rkmVoHi_m1024_r512_s0_c0_p0 : List ℤ := let p := rkmP; [
  p 1413998,p 9305402,p 43236817,p 163783930,p 536491409,p 1569428382,p 4184762416,p 10314943692,
  p 23746851171,p 51464406083,p 105649177013,p 206473740185,p 385748348878,p 691346905444,
  p 1192142853144,p 1982944467065,p 3188665354697,p 4966749709579,p 7506753071595,p 11026016908918,
  p 15760612606133,p 21951181044811,p 29823931414640,p 39567817468221,p 51309674335953,
  p 65089745871866,p 80840433789605,p 98371153999425,p 117361839340995,p 137366891002528,
  p 157830329053994,p 178111657965524,p 197520713903425,p 215358673275475,p 230961631302514,
  p 243742813265412,p 253229603745363,p 259092145918141,p 261161186775002,p 259433992390641,
  p 254068374729730,p 245366004726081,p 233747106403122,p 219719244800549,p 203843195914712,
  p 186698827336380,p 168853572131337,p 150835522635291,p 133112496146436,p 116077721841196,
  p 100042146686464,p 85232817020521,p 71796397673863,p 59806654483368,p 49274641144562,
  p 40160374880727,p 32384925690841,p 25842046010083,p 20408698063382,p 15954066603520,
  p 12346853668859,p 9460825640432,p 7178714534816,p 5394664409968,p 4015463659845,p 2960821280420,
  p 2162937649006,p 1565595825028,p 1122964968258,p 798269057608,p 562436106293,p 392808500930,
  p 271965667227,p 186686685147,p 127062693115,p 85756393871,p 57397892097,p 38101544169,
  p 25086591394,p 16384284755,p 10615329344,p 6823263521,p 4351462009,p 2753553460,p 1729008779,
  p 1077396622,p 666280900,p 408950164,p 249139126,p 150660217,p 90441195,p 53897719,p 31888611,
  p 18732080,p 10925597,p 6327557,p 3638992,p 2078266,p 1178739,p 663972,p 371462,p 206406,
  p 113919,p 62447,p 33994,p 18382,p 9867,p 5255,p 2776,p 1451,p 748,p 381,p 188,p 88,p 38,p 13,
  p 4,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0]
/-- Part 1 of `rkmVoHi_m1024_r512_s0_c0`. -/
def rkmVoHi_m1024_r512_s0_c0_p1 : List ℤ := let p := rkmP; [
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0]
/-- Output orbital vector for `m1024_r512_s0_c0`. -/
def rkmVoHi_m1024_r512_s0_c0 : List ℤ :=
  rkmVoHi_m1024_r512_s0_c0_p0 ++ (rkmVoHi_m1024_r512_s0_c0_p1)
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
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws => (match Nat.mod w 2 with
    | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ | [] => [] | ws :: wss => pzig ws ++ pzigCat wss
private def phbv_g0 : List ℤ := pzigCat
  [
   [150481829054046,212501679689702,259878448770632,299640739583020,334515346534630,
    365902856004642,394636517395846,421260036920234,446151625249142,469587054794438,
    491774812093074,512877103405286,533023107701830,552317712370600,570847482703456,
    588684866312026,605891231571354,622519112693382,638613900956022,654215140547160,
    669357536521496,684071749434350,698385029405866,712321727605764,725903712957994,
    739150714704390,752080606353892,764709642839708,777052659986534,789123243367560,
    800933872110142,812496042053332,823820371773384,834916694306576,845794136862056,
    856461190395114,866925770576198,877195271423374,887276612650844,897176281611904,
    906900370573254,916454609941446,925844397967060,935074827373208,944150709289580,
    953076594818532,961856794513924,970495396014890,978996280044180,987363134953030,
    995599469971160,1003708627300288,1011693793172492,1019558007979908,1027304175569544,
    1034935071785996,1042453352335296,1049861560034848,1057162131507164,1064357403368782,
    1071449617960294,1078440928658442,1085333404807098,1092129036300040,1098829737845270,
    1105437352937498,1111953657562976,1118380363658406,1124719122343662,1130971526946194,
    1137139115833314,1143223375067164,1149225740895718,1155147602092122,1160990302153520,
    1166755141369550,1172443378769912,1178056233959508,1183594888849046,1189060489288302,
    1194454146608676,1199776939081140,1205029913295200,1210214085464052,1215330442660732,
    1220379943989656,1225363521697682,1230282082228432,1235136507223428,1239927654473272,
    1244656358821892,1249323433026690,1253929668577152,1258475836474404,1262962687973952,
    1267390955293698,1271761352289234,1276074575098242,1280331302755684,1284532197781442,
    1288677906741858,1292769060786602,1296806276162200,1300790154703408,1304721284303650,
    1308600239365546,1312427581232606,1316203858602998,1319929607926340,1323605353784314,
    1327231609255944,1330808876268266,1334337645933104,1337818398870618,1341251605520272,
    1344637726439778,1347977212592620,1351270505624678,1354518038130424,1357720233909208,
    1360877508212064,1363990267979448,1367058912070338,1370083831483058,1373065409568198,
    1376004022233960,1378900038144286,1381753818910036,1384565719273538,1387336087286786,
    1390065264483540,1392753586045594,1395401380963432,1398008972191534,1400576676798504,
    1403104806112264,1405593665860500,1408043556306542,1410454772380852,1412827603808320,
    1415162335231488,1417459246329890,1419718611935656,1421940702145488,1424125782429188,
    1426274113734832,1428385952590742,1430461551204344,1432501157558054,1434505015502276,
    1436473364845642,1438406441442554,1440304477278174,1442167700550904,1443996335752470,
    1445790603745696,1447550721840028,1449276903864900,1450969360241020,1452628298049624],
   [1454253921099792,1455846429993874,1457406022191088,1458932892069376,1460427230985520,
    1461889227333650,1463319066602114,1464716931428834,1466083001655156,1467417454378236,
    1468720464002046,1469992202287000,1471232838398280,1472442538952866,1473621468065336,
    1474769787392470,1475887656176686,1476975231288330,1478032667266896,1479060116361168,
    1480057728568316,1481025651672020,1481964031279586,1482873010858140,1483752731769890,
    1484603333306504,1485424952722598,1486217725268416,1486981784221652,1487717260918494,
    1488424284783892,1489102983361056,1489753482340232,1490375905586756,1490970375168412,
    1491537011382108,1492075932779900,1492587256194356,1493071096763306,1493527567953976,
    1493956781586520,1494358847856982,1494733875359672,1495081971109008,1495403240560804,
    1495697787633040,1495965714726108,1496207122742564,1496422111106380,1496610777781730,
    1496773219291286,1496909530734084,1497019805802910,1497104136801278,1497162614659954,
    1497195328953084,1497202367913888,1497183818449972,1497139766158242,1497070295339412,
    1496975489012176,1496855428926964,1496710195579368,1496539868223200,1496344524883200,
    1496124242367396,1495879096279154,1495609161028856,1495314509845294,1494995214786718,
    1494651346751588,1494282975489004,1493890169608844,1493472996591602,1493031522797926,
    1492565813477878,1492075932779900,1491561943759502,1491023908387684,1490461887559068,
    1489875941099774,1489266127775030,1488632505296514,1487975130329440,1487294058499394,
    1486589344398912,1485861041593804,1485109202629244,1484333879035596,1483535121334024,
    1482712979041834,1481867500677598,1480998733766032,1480106724842642,1479191519458146,
    1478253162182646,1477291696609594,1476307165359506,1475299610083474,1474269071466434,
    1473215589230210,1472139202136348,1471039947988716,1469917863635876,1468772984973256,
    1467605346945068,1466414983546042,1465201927822900,1463966211875642,1462707866858596,
    1461426922981236,1460123409508802,1458797354762682,1457448786120566,1456077730016398,
    1454684211940082,1453268256436968,1451829887107126,1450369126604368,1448885996635064,
    1447380517956712,1445852710376278,1444302592748316,1442730182972834,1441135497992932,
    1439518553792202,1437879365391874,1436217946847736,1434534311246794,1432828470703680,
    1431100436356818,1429350218364330,1427577825899672,1425783267147032,1423966549296434,
    1422127678538596,1420266660059500,1418383498034686,1416478195623272,1414550754961682,
    1412601177157084,1410629462280528,1408635609359794,1406619616371918,1404581480235426,
    1402521196802230,1400438760849220,1398334166069504,1396207405063344,1394058469328708,
    1391887349251514,1389694034095484,1387478511991654,1385240769927502,1382980793735702,
    1380698568082474,1378394076455562,1376067301151782,1373718223264160,1371346822668654],
   [1368953078010422,1366536966689666,1364098464846986,1361637547348302,1359154187769264,
    1356648358379186,1354120030124466,1351569172611496,1348995754089016,1346399741429958,
    1343781100112684,1341139794201690,1338475786327674,1335789037667030,1333079507920696,
    1330347155292352,1327591936465970,1324813806582674,1322012719216890,1319188626351778,
    1316341478353928,1313471223947260,1310577810186170,1307661182427828,1304721284303650,
    1301758057689904,1298771442677416,1295761377540352,1292727798704050,1289670640711876,
    1286589836191046,1283485315817418,1280357008279190,1277204840239478,1274028736297744,
    1270828618950022,1267604408547904,1264356023256252,1261083379009576,1257786389467060,
    1254464965966138,1251119017474632,1247748450541344,1244353169245086,1240933075142060,
    1237488067211556,1234018041799892,1230522892562512,1227002510404224,1223456783417440,
    1219885596818414,1216288832881326,1212666370870200,1209018086968520,1205343854206478,
    1201643542385750,1197917018001708,1194164144162970,1190384780508152,1186578783119750,
    1182746004434994,1178886293153580,1174999494142114,1171085448335178,1167143992632822,
    1163174959794362,1159178178328312,1155153472378290,1151100661604708,1147019561062072,
    1142909981071678,1138771727089522,1134604599569184,1130408393819464,1126182899856528,
    1121927902250308,1117643179964878,1113328506192532,1108983648181250,1104608367055246,
    1100202417628246,1095765548209140,1091297500399656,1086798008883604,1082266801207312,
    1077703597550794,1073108110489132,1068480044743636,1063819096922164,1059124955248100,
    1054397299277326,1049635799602566,1044840117544426,1040009904828342,1035144803246720,
    1030244444305382,1025308448853442,1020336426695666,1015327976186288,1010282683803196,
    1005200123701330,1000079857244028,994921432511000,989724383781482,984488230991040,
    979212479160366,973896617794288,968540120249084,963142443066036,957703025269006,
    952221287623652,946696631855678,941128439825336,935516072655172,929858869807720,
    924156148109630,918407200718350,912611296027234,906767676504492,900875557461076,
    894934125742120,888942538336044,882899920894946,876805366159266,870657932279048,
    864456641023414,858200475869014,851888379957336,845519253909708,839091953487724,
    832605287085498,826058013038806,819448836734478,812776407501642,806039315264418,
    799236086933276,792365182509724,785424990876052,778413825238414,771329918187788,
    764171416338924,756936374502392,749622749339086,742228392439946,734751042765960,
    727188318374736,719537707349638,711796557835526,703962067071244,696031269292604,
    688001022360444,679867992945686,671628640076470,663279196820524,654815649837942,
    646233716493758,637528819164888,628696056309378,619730169785086,610625507806040],
   [601375982803200,591975023306048,582415518774508,572689756076544,562789346011498,
    552705137903964,542427119812548,531944301277014,521244574718288,510314550540710,
    499139359569044,487702414546496,475985119823070,463966514778214,451622831498606,
    438926940080076,425847644558606,412348777158288,398388015407688,383915310862546,
    368870761182712,353181663725502,336758329478034,319487953211432,301225307808042,
    281777985428678,260881682800392,238155838178624,213016301570066,184479635726534,
    150628138795948,106510583894510]]
private def pvm_c0_1 : List ℤ := pzigCat
  [
   [1806218676134266,815571497643736,260017139881308,67586268451234,15191712562028,3049720851822,
    558061247842,94403531086,14916109820,2218720088,312626302,41937822,5378290,661686,78326,8942,
    984,102,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_2 : List ℤ := pzigCat
  [
   [1330265918833778,1202041725003758,766917404047684,398927472437634,179444774874692,
    72089584708000,26398691380114,8936688426946,2825735717100,841135228926,237178824538,
    63671215922,16340619060,4023130762,953054420,217790432,48116448,10297474,2138462,431588,84764,
    16216,3022,546,92,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_3 : List ℤ := pzigCat
  [
   [798684988364414,1083629365186182,1038086532899946,810778503596234,547598172090796,
    330313379106340,181617663462456,92315350283282,43827837418728,19588676542466,8293455751188,
    3342894619040,1288153290320,476192186892,169377013830,58115745302,19278198452,6194712792,
    1931566118,585331368,172623164,49607094,13906814,3807130,1018736,266676,68340,17150,4216,1010,
    232,50,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_4 : List ℤ := pzigCat
  [
   [390675078882382,707729120151810,905243413050816,944015144647956,851300814074658,
    685631796294528,503345277695916,341605118096714,216542140154268,129222701748926,
    73048280275408,39313100446838,20226545041004,9983328836496,4741174481838,2172016084450,
    961995042786,412728186832,171825851408,69521014744,27374624440,10503333254,3931378632,
    1436975454,513393454,179441950,61406854,20589662,6768888,2183214,691254,214966,65688,19728,
    5822,1682,472,126,28,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_5 : List ℤ := pzigCat
  [
   [183977827150532,403314616907404,624264672230506,787785901175872,859681373886590,
    837857214297228,744336002896820,611294838862510,468912150672636,338617928960868,
    231634139125056,150851862281308,93919389967216,56095558929474,32237247725884,17871184536294,
    9578131370340,4972663903612,2505127720514,1226516035802,584413752072,271340050136,
    122898192768,54357967894,23500483824,9939452520,4115918592,1669975386,664338280,259286794,
    99343766,37386096,13826544,5027606,1798248,632940,219314,74832,25148,8322,2704,860,264,74,16,
    2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0]]
private def pvm_c0_6 : List ℤ := pzigCat
  [
   [75054876252202,193242084856894,351293472613712,520657753403980,667303975885656,
    763831408871394,796961008783170,768702991424766,692529642688896,587347485651192,
    471873144621812,360919330760598,263906902503094,185122509920986,124946247002102,
    81349025096490,51205050860824,31221471182682,18472497602332,10621838928770,5943973813530,
    3241153401556,1724088885890,895581438466,454721653636,225869453858,109846763962,52342596288,
    24454479236,11209151796,5043772208,2229188626,968214832,413467334,173681498,71795214,29217498,
    11710150,4623922,1799428,690356,261192,97470,35884,13028,4660,1638,562,184,52,10,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_7 : List ℤ := pzigCat
  [
   [26504923416210,78437304316954,163894148678470,279201180433178,411300542491456,541131556417940,
    648950122813272,719450354836828,744985398962384,726224271613946,670604213327490,
    589543219753220,495472851064140,399476346852534,309896663645088,231903338699178,
    167775110236456,117578332219138,79957254060794,52843235657662,33987806392062,21301074481584,
    13023159872508,7775274274446,4537423358720,2590438705942,1447952640274,792999184226,
    425819364996,224330522664,116016251776,58932796918,29419003582,14439180702,6971065422,
    3311955838,1549083582,713569924,323837456,144842398,63868098,27773232,11913808,5042874,
    2106806,868954,353914,142362,56564,22198,8604,3288,1232,446,156,48,10,2,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_8 : List ℤ := pzigCat
  [
   [8095119636132,27090725802210,64012041995688,123314663866764,205425799114918,305629859508302,
    414477010685028,519619158490088,608451926010666,670721831865660,700374174963100,
    696258719852206,661705892845752,603288906795616,529223706658200,447833419572788,
    366372720623126,290340740309076,223266020703854,166854233221016,121353699038216,
    86002769995636,59457594552598,40140770580674,26488496244424,17100087232424,10808249358056,
    6693429944504,4064202724390,2421091960688,1415838443680,813247741182,459053924462,
    254769373840,139082260396,74717791038,39516660328,20582911686,10562366882,5341863586,
    2663440920,1309624026,635230746,304032218,143624054,66983088,30848886,14033028,6306636,
    2800728,1229298,533378,228812,97062,40714,16886,6916,2794,1106,428,158,50,12,2,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_9 : List ℤ := pzigCat
  [
   [2136125044346,7981927806104,21058694600526,45296636431496,84253225676554,139960830522008,
    211928424284888,296654408134376,387853456153770,477373645500080,556569722574776,
    617777964281802,655538098908480,667311024696462,653598628284846,617527182679608,
    564065195751286,499090846201484,428507634497632,357549623694532,290344855290546,
    229738844663250,177332796343628,133667560910046,98481594056886,70982680578206,50091563487688,
    34634743240984,23479642950236,15616335983252,10196054518640,6538690206630,4120784517378,
    2553351367874,1556256300054,933422538596,551160681004,320514290216,183629852758,103684810816,
    57717110614,31684450332,17158050568,9168363230,4835418230,2517709508,1294531368,657440336,
    329863302,163545488,80141824,38822326,18594638,8807582,4126320,1912402,876948,397930,178700,
    79430,34936,15206,6546,2780,1160,470,182,64,18,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_10 : List ℤ := pzigCat
  [
   [486446721254,2009015968464,5858315306736,13927452041656,28632244540348,52569909209514,
    87979300030918,136113560758092,196687277902030,267561595439014,344778652185430,
    422967867536774,496050384708846,558094527108104,604144638173956,630862803815366,
    636877512186636,622805879279132,590985561675048,545002581881354,489124049311542,
    427740804298154,364901290036760,303984309055452,247524242816444,197174757192580,
    153779510487898,117511277485468,88042318854536,64715790094304,46697444279748,33096364886860,
    23051369439060,15785321108900,10632825694210,7048055408582,4599296735556,2955843909160,
    1871530904524,1167850352548,718445285568,435864077784,260847902182,154036783848,89779797974,
    51660769624,29354671784,16475140188,9135106978,5005227504,2710496778,1451023646,768038268,
    402025002,208142682,106605682,54023298,27091388,13446104,6606006,3213066,1547376,737940,
    348536,163040,75542,34672,15754,7084,3148,1374,586,242,94,30,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_11 : List ℤ := pzigCat
  [
   [95474292542,432208289852,1381463956280,3599930992264,8112078859930,16325513047668,
    29947566142276,50784645102898,80437000907476,119936266948350,169399781462924,227784495198138,
    292809698473220,361084537257052,428432187536176,490359624968040,542591381816696,
    581574630374142,604872682908862,611390364152122,601409874765752,576450879361454,
    538996181159150,492140040145564,439218977878568,383476780775536,327800199359600,
    274543930608326,225446715057310,181627420904444,143642041744734,111579556647708,
    85175663390732,63927136668206,47194582043764,34286484492350,24521885298498,17272344110232,
    11985957340662,8197236037550,5526841936930,3674820275934,2410308525180,1559942441280,
    996460711220,628403266080,391335618058,240710168126,146275201760,87835731704,52129698382,
    30584283244,17741599218,10177653326,5774827792,3241456026,1800202968,989352456,538138900,
    289744232,154444824,81513416,42602882,22052514,11306792,5742950,2889970,1440992,712004,348652,
    169210,81394,38804,18332,8574,3964,1810,812,352,146,56,16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_12 : List ℤ := pzigCat
  [
   [16127013976,79473455290,276521230074,784406974022,1924137982778,4215276771962,8417331434588,
    15538081153382,26789914759396,43482541333448,66853568925992,97854702431536,136926409445116,
    183803300637734,237392825601788,295760190541436,356234396460486,415627993379524,
    470541701018794,517709313351422,554331574054800,578350976455338,588631356369384,
    585023586245114,568317691088770,540098519750662,502533937399930,458129999612858,
    409486822841852,359083131036844,309108650107776,261353701671666,217156292251806,
    177399931801106,142550937282548,112722097567144,87749887026584,67274275731806,50812896444998,
    37824271620554,27757511048944,20088076804644,14340758010358,10101914638402,7023432054724,
    4820811606162,3267548636226,2187542561698,1446840342400,945599844678,610809920550,
    390033863346,246251194960,153749335620,94947400834,58004416796,35060469742,20971092814,
    12414711440,7274911448,4220417458,2424257596,1378970062,776852958,433495042,239630704,
    131239296,71219168,38299086,20411928,10782710,5646282,2931088,1508568,769850,389572,195494,
    97290,48012,23486,11386,5468,2594,1212,552,246,100,36,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_13 : List ℤ := pzigCat
  [
   [2340697692,12483945536,47010506780,144325429446,383151792102,908431650918,1963226376738,
    3922124773874,7318493603280,12855527671998,21390576377732,33884475709402,51312803983392,
    74543463832476,104193317953378,140483813989788,183119669381532,231214351512186,
    283280869288228,337297030079466,390842557539008,441293646095726,486051005069922,
    522772049420450,549577534050432,565207447152568,569109268014684,561452019603502,
    543069964256246,515348568283450,480071283219608,439248216045338,394947011290700,
    349142894248632,303599788084804,259788761142738,218844711624052,181557835836760,
    148393431257994,119532042851510,94921723623686,74334951828982,57424167173518,43771604855122,
    32930825911904,24458856219302,17939034946572,12995495489390,9300676567022,6577444777962,
    4597376504860,3176572426654,2170128929740,1466119825474,979685351032,647605009622,
    423555917372,274129806792,175595058080,111337667862,69888683130,43437571534,26734694674,
    16296379432,9839355368,5885095204,3487399910,2047669942,1191448166,687057334,392697106,
    222490912,124967884,69591574,38426096,21039990,11424876,6152902,3286734,1741564,915450,477402,
    247000,126790,64572,32622,16346,8116,3988,1938,922,430,194,80,28,6,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_14 : List ℤ := pzigCat
  [
   [291406154,1673769732,6787773836,22442022374,64161545050,163824611622,381274996400,
    820292091476,1648337382918,3118097768698,5587220832722,9531160181636,15543202775262,
    24316004872744,36600627139134,53142144359770,74595053148710,101426207464454,133816952000592,
    171578557800292,214095269824742,260306942626626,308738574990590,357577763727186,
    404794247703552,448289509395672,486059930341038,516355009764242,537812928362586,
    549559043241598,551258079141634,543116908526708,525840886019556,500551829798574,
    468679286817098,431838372659722,391707266738998,349915672653242,307952706605088,
    267099310449798,228386928100144,192581258417654,160187681689036,131473571951738,
    106502137354378,85172555889066,67261813788302,52464607895610,40428753227804,30784589225912,
    23167794830794,17235742251914,12678021879078,9222067297322,6634931205930,4722251666024,
    3325346695446,2317222920910,1598112517642,1090985109882,737332420114,493400869172,
    326953230818,214573307482,139483715960,89821599106,57305671002,36226176712,22693554832,
    14089102392,8669801594,5288384318,3197912710,1917257684,1139735406,671855004,392764532,
    227724820,130961938,74708624,42278610,23737084,13222760,7308622,4008638,2181908,1178636,
    631900,336248,177598,93102,48438,25012,12808,6498,3264,1618,794,374,170,72,26,6,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_15 : List ℤ := pzigCat
  [
   [31058442,191302794,831947164,2949654216,9043209948,24760737918,61795571034,142567353586,
    307204917206,623160943608,1197382013860,2190317180038,3830222956728,6425338585958,
    10370758728924,16146456984982,24303135500438,35433539522762,50128592231416,68920015648532,
    92213681565090,120220334133298,152892056016830,189873489490922,230476112040542,
    273681775218468,318178474493378,362427380347510,404756126005162,443469847995492,
    476969061537444,503862489529220,523063573845866,533861447263664,535960281309146,
    529484652399752,514952337201120,493219251762018,465403699492972,432798467228352,
    396779561399172,358719622932192,319912534341816,281513736141562,244498614515162,
    209639286094580,177498400083094,148437331885534,122635402161678,100116495987138,
    80779601792134,64430232134668,50810312101438,39624817803770,30564127759600,23321649669158,
    17606765991512,13153488994960,9725433277948,7117817538250,5157221054530,3699769637518,
    2628335080040,1849222148656,1288703952884,889661227708,608490331656,412371601204,276934406746,
    184316331478,121588844062,79507780264,51541048228,33125704354,21109825552,13339824248,
    8359855060,5195971798,3203239890,1958849592,1188324534,715194082,427070250,253041740,
    148775888,86806014,50265796,28888728,16479528,9331430,5245214,2926954,1621544,891916,487096,
    264130,142218,76028,40348,21254,11110,5756,2952,1494,742,358,168,70,24,6,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private theorem pchk_c0_s0 : rkmAllTrueF [
    muxIntListEq rkmHbHi_m1024_r512_s0_c0 phbv_g0,
    bSlideChk 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c0 pvm_c0_1
  ] = true := by decide +kernel
private theorem pchk_c0_s1 : bSlideChk 6 513
    phbv_g0 pvm_c0_1 pvm_c0_2 = true := by decide +kernel
private theorem pchk_c0_s2 : bSlideChk 6 513
    phbv_g0 pvm_c0_2 pvm_c0_3 = true := by decide +kernel
private theorem pchk_c0_s3 : bSlideChk 6 513
    phbv_g0 pvm_c0_3 pvm_c0_4 = true := by decide +kernel
private theorem pchk_c0_s4 : bSlideChk 5 513
    phbv_g0 pvm_c0_4 pvm_c0_5 = true := by decide +kernel
private theorem pchk_c0_s5 : bSlideChk 5 513
    phbv_g0 pvm_c0_5 pvm_c0_6 = true := by decide +kernel
private theorem pchk_c0_s6 : bSlideChk 5 513
    phbv_g0 pvm_c0_6 pvm_c0_7 = true := by decide +kernel
private theorem pchk_c0_s7 : bSlideChk 5 513
    phbv_g0 pvm_c0_7 pvm_c0_8 = true := by decide +kernel
private theorem pchk_c0_s8 : bSlideChk 5 513
    phbv_g0 pvm_c0_8 pvm_c0_9 = true := by decide +kernel
private theorem pchk_c0_s9 : bSlideChk 5 513
    phbv_g0 pvm_c0_9 pvm_c0_10 = true := by decide +kernel
private theorem pchk_c0_s10 : bSlideChk 5 513
    phbv_g0 pvm_c0_10 pvm_c0_11 = true := by decide +kernel
private theorem pchk_c0_s11 : bSlideChk 5 513
    phbv_g0 pvm_c0_11 pvm_c0_12 = true := by decide +kernel
private theorem pchk_c0_s12 : bSlideChk 5 513
    phbv_g0 pvm_c0_12 pvm_c0_13 = true := by decide +kernel
private theorem pchk_c0_s13 : bSlideChk 5 513
    phbv_g0 pvm_c0_13 pvm_c0_14 = true := by decide +kernel
private theorem pchk_c0_s14 : bSlideChk 5 513
    phbv_g0 pvm_c0_14 pvm_c0_15 = true := by decide +kernel
private theorem pchk_c0_s15 : bSlideChk 5 513
    phbv_g0 pvm_c0_15 rkmVoHi_m1024_r512_s0_c0 = true := by decide +kernel
private theorem pacc_c0_s1 : muxFastIterFullT16 12 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_2 :=
  (muxFastIterFullT16_add 6 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_g0)
      (bSlideChk_sound (rkmHd (rkmTl pchk_c0_s0)))).trans (bSlideChk_sound pchk_c0_s1))
private theorem pacc_c0_s2 : muxFastIterFullT16 18 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_3 :=
  (muxFastIterFullT16_add 12 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_g0)
      pacc_c0_s1).trans (bSlideChk_sound pchk_c0_s2))
private theorem pacc_c0_s3 : muxFastIterFullT16 24 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_4 :=
  (muxFastIterFullT16_add 18 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_g0)
      pacc_c0_s2).trans (bSlideChk_sound pchk_c0_s3))
private theorem pacc_c0_s4 : muxFastIterFullT16 29 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_5 :=
  (muxFastIterFullT16_add 24 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s3).trans (bSlideChk_sound pchk_c0_s4))
private theorem pacc_c0_s5 : muxFastIterFullT16 34 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_6 :=
  (muxFastIterFullT16_add 29 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s4).trans (bSlideChk_sound pchk_c0_s5))
private theorem pacc_c0_s6 : muxFastIterFullT16 39 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_7 :=
  (muxFastIterFullT16_add 34 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s5).trans (bSlideChk_sound pchk_c0_s6))
private theorem pacc_c0_s7 : muxFastIterFullT16 44 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_8 :=
  (muxFastIterFullT16_add 39 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s6).trans (bSlideChk_sound pchk_c0_s7))
private theorem pacc_c0_s8 : muxFastIterFullT16 49 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_9 :=
  (muxFastIterFullT16_add 44 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s7).trans (bSlideChk_sound pchk_c0_s8))
private theorem pacc_c0_s9 : muxFastIterFullT16 54 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_10 :=
  (muxFastIterFullT16_add 49 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s8).trans (bSlideChk_sound pchk_c0_s9))
private theorem pacc_c0_s10 : muxFastIterFullT16 59 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_11 :=
  (muxFastIterFullT16_add 54 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s9).trans (bSlideChk_sound pchk_c0_s10))
private theorem pacc_c0_s11 : muxFastIterFullT16 64 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_12 :=
  (muxFastIterFullT16_add 59 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s10).trans (bSlideChk_sound pchk_c0_s11))
private theorem pacc_c0_s12 : muxFastIterFullT16 69 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_13 :=
  (muxFastIterFullT16_add 64 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s11).trans (bSlideChk_sound pchk_c0_s12))
private theorem pacc_c0_s13 : muxFastIterFullT16 74 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_14 :=
  (muxFastIterFullT16_add 69 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s12).trans (bSlideChk_sound pchk_c0_s13))
private theorem pacc_c0_s14 : muxFastIterFullT16 79 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = pvm_c0_15 :=
  (muxFastIterFullT16_add 74 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s13).trans (bSlideChk_sound pchk_c0_s14))
private theorem pacc_c0_s15 : muxFastIterFullT16 84 513
    phbv_g0 rkmViHi_m1024_r512_s0_c0 = rkmVoHi_m1024_r512_s0_c0 :=
  (muxFastIterFullT16_add 79 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s14).trans (bSlideChk_sound pchk_c0_s15))
/-- Certified `T_16` walk chunk `m1024_r512_s0_c0`. -/
theorem rkmWalkChkHi_m1024_r512_s0_c0 : muxFastIterFullT16 84 513
    rkmHbHi_m1024_r512_s0_c0 rkmViHi_m1024_r512_s0_c0 = rkmVoHi_m1024_r512_s0_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 84 513 h rkmViHi_m1024_r512_s0_c0)
    (muxIntListEq_eq_true.mp (rkmHd pchk_c0_s0))).trans pacc_c0_s15
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi1024T3`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T3 :
    rkmWalkChkHi_m1024_r512_s0_c0 = rkmWalkChkHi_m1024_r512_s0_c0 :=
  rfl
private theorem laneRoot_Hi1024T3 : rkmHbHi_m1024_r512_s0_c0 = rkmHbHi_m1024_r512_s0_c0 :=
  (And.intro (Eq.refl rkmFlipGapsHi1024T2) rfl).right
end
end QuantumComputation.Specs.DickeSol
