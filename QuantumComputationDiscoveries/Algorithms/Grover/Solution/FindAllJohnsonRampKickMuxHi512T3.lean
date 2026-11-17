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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T2

/-
# High-`m` Checkpointed Walk Part `3` (`FindAllJohnsonRampKickMuxHi512T3`)

Certifies `1` `T_16` checkpoint walk(s) (`29754` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m512_r512_s0_c0`. -/
def rkmHbHi_m512_r512_s0_c0 : List ℤ := altBuildHbFrom 512 512 83769689655 0 512
/-- Input orbital vector for `m512_r512_s0_c0`. -/
def rkmViHi_m512_r512_s0_c0 : List ℤ := [rkmP 1000000000000000]
/-- Part 0 of `rkmVoHi_m512_r512_s0_c0`. -/
def rkmVoHi_m512_r512_s0_c0_p0 : List ℤ := let p := rkmP; [
  p 3432741364,p 17655272984,p 64079898934,p 189518204759,p 484435964816,p 1105327151791,
  p 2297613731212,p 4412761526084,p 7911646707288,p 13346405411144,p 21315648405512,
  p 32392933534914,p 47034859330127,p 65481520644908,p 87666562322847,p 113155195551839,
  p 141125607776344,p 170402550511038,p 199542868300713,p 226963311089557,p 251093232692577,
  p 270530367357037,p 284177615602128,p 291342508727317,p 291787752840310,p 285729435290568,
  p 273787438482878,p 256898932307880,p 236209610338379,p 212958322228732,p 188369230146218,
  p 163562278377968,p 139488496431934,p 116892318806258,p 96299382834397,p 78025582085654,
  p 62201656595285,p 48807213761617,p 37708562109047,p 28695799482930,p 21515922350375,
  p 15900058086479,p 11584087403210,p 8322819796184,p 5898481434867,p 4124594149881,
  p 2846418704030,p 1939070337421,p 1304253114025,p 866355237174,p 568439665854,p 368478239974,
  p 236026022147,p 149419327576,p 93503482364,p 57848930259,p 35389884548,p 21411465984,
  p 12813325649,p 7585566010,p 4443089606,p 2575202091,p 1477144452,p 838637710,p 471322472,
  p 262243734,p 144472284,p 78814127,p 42580415,p 22784878,p 12076965,p 6341400,p 3298902,
  p 1700394,p 868484,p 439583,p 220506,p 109630,p 54019,p 26381,p 12766,p 6121,p 2907,p 1364,p 630,
  p 285,p 124,p 50,p 18,p 5,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0]
/-- Part 1 of `rkmVoHi_m512_r512_s0_c0`. -/
def rkmVoHi_m512_r512_s0_c0_p1 : List ℤ := let p := rkmP; [
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
/-- Output orbital vector for `m512_r512_s0_c0`. -/
def rkmVoHi_m512_r512_s0_c0 : List ℤ :=
  rkmVoHi_m512_r512_s0_c0_p0 ++ (rkmVoHi_m512_r512_s0_c0_p1)
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
private def phbv_0 : List ℤ := pNZCat
  [
   [85780162206720,121074532312855,147995225789071,170555088137580,190311756051003,
    208065697503977,224293371426976,239305827076290,253319541516720,266492436304416,
    278943959907711,290767090667940,302035911380807,312810603129220,323140858498975,
    333068286068280,342628148443393,351850646740881,360761888397054,369384628870647,
    377738848686404,385842208447369,393710411978660,401357499327198,408796085516400,
    416037556861296,423092233726405,429969506490448,436677949926375,443225420048361,
    449619136607567,455865753757209,461971420900028,467941835338199,473782288038677,
    479497703585220,485092675196553,490571495536965,495938183922389,501196510425402,
    506350017301397,511402038091825,516355714705768,521214012735923,525979735227575,
    530655535087807,535243926295960,539747294054261,544167903998880,548507910575852,
    552769364672844,556954220586209,561064342392979,565101509788908,569067423446437,
    572963709940095,576791926281407,580553564100614,584250053508348,587882766666811,
    591453021096803,594962082744190,598411168826913,601801450481520,605134055226255,
    608410069256080,611630539583472,614796476037541,617908853132788,620968611817801,
    623976661113210,626933879647389,629841117097638,632699195543879,635508910741307,
    638271033317865,640986309901929,643655464185128,646279197924828,648858191890428,
    651393106757280,653884583951769,656333246450771,658739699538486,661104531523402,
    663428314417947,665711604583171,667954943340660,670158857553694,672323860179531,
    674450450794560,676539116093943,678590330367250,680604555951491,682582243662851,
    684523833208351,686429753578554,688300423422398,690136251405135,691937636550300,
    693704968566581,695438628160411,697138987335018,698806409676675,700441250628792,
    702043857754499,703614570988300,705153722877341,706661638812846,708138637252170,
    709585029931964,711001122072865,712387212576143,713743594212660,715070553804542,
    716368372399880,717637325440799,718877682925202,720089709562472,721273664923420,
    722429803584720,723558375268099,724659624974504,725733793113460,726781115627846,
    727801824114278,728796145939284,729764304351458],
   [730706518589765,731623003988143,732513972076582,733379630678794,734220184006649,
    735035832751474,735826774172366,736593202181632,737335307427468,738053277373981,
    738747296378674,739417545767476,740064203907422,740687446277072,741287445534748,
    741864371584680,742418391641136,742949670290614,743458369552160,743944648935890,
    744408665499779,744850573904770,745270526468289,745668673216186,746045161933196,
    746400138211941,746733745500548,747046125148916,747337416453680,747607756701933,
    747857281213719,748086123383371,748294414719709,748482284885148,748649861733751,
    748797271348252,748924638076106,749032084564568,749119731794854,749187699115413,
    749236104274320,749265063450842,749274691286190,749265100913476,749236403986924,
    749188710710327,749122129864802,749036768835847,748932733639725,748810128949196,
    748669058118626,748509623208473,748331925009184,748136063064517,747922135694301,
    747690240016653,747440471969672,747172926332614,746887696746578,746584875734709,
    746264554721921,745926824054184,745571773017349,745199489855561,744810061789235,
    744403575032646,743980114811108,743539765377780,743082610030087,742608731125793,
    742118210098705,741611127474047,741087562883485,740547595079843,739991301951484,
    739418760536402,738830047035993,738225236828551,737604404482470,736967623769171,
    736314967675753,735646508417395,734962317449485,734262465479507,733547022478688,
    732816057693397,732069639656320,731307836197411,730530714454613,729738340884376,
    728930781271955,728108100741512,727270363766015,726417634176941,725549975173792,
    724667449333424,723770118619200,722858044389954,721931287408800,720989907851759,
    720033965316230,719063518829293,718078626855865,717079347306693,716065737546206,
    715037854400216,713995754163476,712939492607104,711869124985861,710784706045309,
    709686290028825,708573930684500,707447681271904,706307594568733,705153722877341,
    703986118031150,702804831400948,701609913901076,700401415995506,699179387703815,
    697943878607050,696694937853493,695432614164331,694156955839219,692868010761756,
    691565826404864,690250449836072,688921927722720],
   [687580306337062,686225631561299,684857948892508,683477303447511,682083739967644,
    680677302823457,679258036019337,677825983198049,676381187645208,674923692293677,
    673453539727893,671970772188120,670475431574640,668967559451874,667447197052433,
    665914385281112,664369164718812,662811575626410,661241657948560,659659451317436,
    658064995056421,656458328183734,654839489416001,653208517171773,651565449574989,
    649910324458385,648243179366853,646564051560747,644872978019137,643169995443020,
    641455140258477,639728448619785,637989956412480,636239699256379,634477712508555,
    632704031266264,630918690369835,629121724405517,627313167708276,625493054364564,
    623661418215038,621818292857243,619963711648257,618097707707299,616220313918293,
    614331562932405,612431487170536,610520118825784,608597489865872,606663632035535,
    604718576858883,602762355641722,600794999473851,598816539231320,596827005578660,
    594826428971083,592814839656652,590792267678414,588758742876515,586714294890282,
    584658953160269,582592746930290,580515705249408,578427856973915,576329230769267,
    574219855112011,572099758291671,569968968412620,567827513395918,565675420981139,
    563512718728156,561339434018920,559155594059203,556961225880328,554756356340866,
    552541012128323,550315219760795,548079005588608,545832395795934,543575416402387,
    541308093264600,539030452077782,536742518377249,534444317539947,532135874785946,
    529817215179922,527488363632612,525149344902263,522800183596050,520440904171489,
    518071530937821,515692088057386,513302599546979,510903089279187,508493580983715,
    506074098248688,503644664521943,501205303112305,498756037190844,496296889792122,
    493827883815421,491349042025958,488860387056083,486361941406469,483853727447280,
    481335767419330,478808083435232,476270697480518,473723631414770,471166906972714,
    468600545765317,466024569280863,463438998886024,460843855826909,458239161230108,
    455624936103725,453001201338391,450367977708274,447725285872074,445073146374006,
    442411579644772,439740606002525,437060245653817,434370518694542,431671445110863,
    428963044780135,426245337471808,423518342848332],
   [420782080466043,418036569776042,415281830125064,412517880756342,409744740810451,
    406962429326153,404170965241229,401370367393302,398560654520648,395741845263004,
    392913958162366,390077011663772,387231024116085,384376013772764,381511998792626,
    378638997240600,375757027088474,372866106215638,369966252409808,367057483367754,
    364139816696013,361213269911602,358277860442712,355333605629407,352380522724306,
    349418628893267,346447941216055,343468476687009,340480252215698,337483284627577,
    334477590664629,331463186986002,328440090168643,325408316707924,322367883018258,
    319318805433714,316261100208623,313194783518179,310119871459032,307036380049879,
    303944325232042,300843722870051,297734588752208,294616938591160,291490788024451,
    288356152615083,285213047852061,282061489150936,278901491854346,275733071232546,
    272556242483938,269371020735590,266177421043756,262975458394391,259765147703652,
    256546503818404,253319541516720,250084275508369,246840720435309,243588890872166,
    240328801326718,237060466240365,233783899988600,230499116881477,227206131164069,
    223904957016924,220595608556524,217278099835723,213952444844201,210618657508897,
    207276751694447,203926741203617,200568639777728,197202461097084,193828218781386,
    190445926390154,187055597423134,183657245320710,180250883464309,176836525176796,
    173414183722881,169983872309504,166545604086231,163099392145636,159645249523688,
    156183189200130,152713224098852,149235367088269,145749630981687,142256028537671,
    138754572460405,135245275400058,131728149953134,128203208662829,124670464019383,
    121129928460421,117581614371305,114025534085470,110461699884763,106890123999780,
    103310818610197,99723795845101,96129067783315,92526646453721,88916543835584,85298771858868,
    81673342404553,78040267304946,74399558343992,70751227257583,67095285733859,63431745413515,
    59760617890098,56081914710305,52395647374275,48701827335886,45000466003042,41291574737959,
    37575164857454,33851247633222,30119834292120,26380936016446,22634563944210,18880729169411,
    15119442742305,11350715669677,7574558915106,3790983399228]]
private theorem dkhb_0 : muxIntListEq rkmHbHi_m512_r512_s0_c0 phbv_0 = true := by
  decide +kernel
private def pvm_0_1 : List ℤ := pZZZ 34
  [
   [1934857520965836,497960074386656,90443204776100,13386312337612,1712474638186,195559181618,
    20346318710,1955971770,175543258,14824106,1185252,90174,6554,454,28]]
private def pvm_0_2 : List ℤ := pZZZ 77
  [
   [1751856532711620,901958067870736,327725232307392,97036883324940,24833722095922,5673322846362,
    1180827840882,227093452612,40772497086,6887992804,1101733466,167687064,24387206,3400752,
    456062,58964,7362,886,100,10]]
private def pvm_0_3 : List ℤ := pZZZ 121
  [
   [1484418338452164,1146892298219586,625351806123750,277862112150788,106711690577792,
    36583486866534,11426449984004,3297662588892,888475599222,225240869554,54063865552,12348263500,
    2694907828,563939700,113490396,22020754,4128732,749476,131944,22558,3746,602,92,12]]
private def pvm_0_4 : List ℤ := pZZZ 165
  [
   [1177023248866448,1213256180120524,882581956320330,523191094328672,268066780946582,
    122607122172374,51090616392860,19671381836474,7070865922440,2391510836082,765825683228,
    233359782020,67945538036,18969077842,5092942984,1318371222,329775520,79865464,18759026,
    4279974,949836,205288,43254,8890,1782,346,62,8]]
private def pvm_0_5 : List ℤ := pZZZ 209
  [
   [873237585887724,1126024186025124,1024701994225598,759888221794996,487055784128782,
    278674508362172,145267354878724,69969150178602,31462170489406,13311661972384,5332528776272,
    2032694662682,740371064170,258569071034,86844143376,28122265518,8799771188,2665949360,
    783326396,223569954,62067528,16781754,4424078,1138324,286134,70318,16906,3974,910,200,40,6]]
private def pvm_0_6 : List ℤ := pZZZ 253
  [
   [606081425939592,938730794840810,1026089183346148,913967627053060,703643641887804,
    483574797513068,302779304100432,175168451156100,94608137787926,48079728707012,23134080320368,
    10592046343070,4633884947812,1943837067772,784170833592,305004824670,114633995714,41713725930,
    14721575134,5046715130,1682841008,546511018,173048340,53480556,16147052,4766882,1377092,
    389578,107996,29350,7820,2038,518,124,24,2]]
private def pvm_0_7 : List ℤ := pZZZ 298
  [
   [393457562507660,711777825594248,908707769823172,945376852651860,850082771879022,
    682347614481486,499000583885850,337180835176454,212699704946272,126249910635352,
    70949814460336,37940943606832,19386616051080,9498267700446,4475301420114,2033034047294,
    892435805480,379286538262,156338842334,62595749864,24378212802,9246549624,3419554508,
    1234294102,435247346,150071234,50634726,16730488,5417184,1719958,535788,163844,49200,14512,
    4202,1188,326,84,16]]
private def pvm_0_8 : List ℤ := pZZZ 341
  [
   [238855276401332,494469635968700,722398453812780,860030957246682,884964905926792,
    812878032014616,680259788140938,526004942710950,379704888909310,257906269962450,
    165856602858228,101493790209586,59344756969432,33271541007968,17938995754514,9325389371026,
    4684302756432,2278138945008,1074542610192,492316881962,219403746414,95227708740,40298954434,
    16644957226,6716439632,2649955476,1023120896,386833320,143326188,52072358,18562020,6495596,
    2232602,754066,250382,81760,26260,8294,2574,778,226,62,14,2]]
private def pvm_0_9 : List ℤ := pZZZ 386
  [
   [135558784339110,316175651670512,520427951968254,698058703867514,809276651480444,
    837507090185362,789639913514090,687914318534548,559474102354698,428138239353304,
    310200324139586,213862854892332,140884655958306,88989496951590,54056447641746,31659126883338,
    17916721535978,9816902281746,5216721091830,2692758873768,1351993432506,661105435414,
    315193364262,146669870950,66676274546,29637653608,12891524404,5491264056,2292156204,938199562,
    376774816,148540082,57518132,21886452,8187528,3012468,1090580,388612,136342,47112,16032,5366,
    1764,564,174,50,10]]
private def pvm_0_10 : List ℤ := pZZZ 430
  [
   [71902859428038,186648992380840,341928654522086,510438483575058,658603415649544,
    758559915875294,795983094005068,771758425496066,698551166403518,594938920689342,
    479733076539350,368095708507534,269870860179754,189712906504066,128253841413816,
    83595998904854,52651131155036,32105922965596,18987542718062,10907569566056,6094855492674,
    3316780945422,1759864716106,911377306274,461086741432,228090952822,110413042190,52340662424,
    24314246278,11075426762,4949880228,2171715944,935857368,396300756,164985706,67555376,27217048,
    10793324,4214624,1621056,614342,229466,84492,30672,10972,3864,1338,452,144,40,8]]
private def pvm_0_11 : List ℤ := pZZZ 458
  [
   [35632287491910,101933192747202,205786420740062,338543646288200,481375608882100,
    610994976742170,706542099630258,754919831721130,753011718057454,706738506738344,
    628011650858936,531018020963136,429026156328508,332355392922152,247601409910264,
    177845919859446,123435649694562,82945217715502,54056391459366,34219777197518,21070861981452,
    12635841995582,7388120887038,4216178947596,2350543973328,1281319781210,683490334934,
    357036446366,182765528922,91738765358,45179858094,21842872440,10372220958,4839953376,
    2220320202,1001800136,444747010,194346692,83623852,35442188,14800930,6092128,2472216,989374,
    390570,152124,58464,22170,8294,3058,1106,386,128,38,8]]
private def pvm_0_12 : List ℤ := pZZZ 454
  [
   [16491375391734,51569915753774,113805645767542,204657064052610,318097173518784,441342453521044,
    557875289301716,651567793440724,710426058612002,728841269898792,707941929165068,
    654325139010620,577858104427296,489318842678362,398467380237984,312847507078508,
    237343428382142,174330930092676,124186766315024,85930887569646,57835827693370,37910547172854,
    24228679941346,15113093534038,9209583092442,5487380274384,3199444066382,1826787344912,
    1022119586642,560778010218,301864672130,159516349022,82793056890,42226853824,21173235560,
    10441802232,5066742836,2419987550,1138112076,527221436,240645688,108261470,48018410,21003938,
    9062916,3858506,1621278,672484,275406,111378,44482,17546,6830,2618,986,358,124,38,8]]
private def pvm_0_13 : List ℤ := pZZZ 450
  [
   [7125331144654,24191676093046,57963320702858,113170870272322,190978616700036,287684330368846,
    394813276689596,500641568306952,592648795251534,660117516705912,696136278091300,
    698549396348958,669776893265824,615750653453728,544387642936992,464033439947778,
    382202426909698,304781694230894,235714612681418,177074406776022,129388988264556,
    92077354382600,63887148511722,43263997818264,28622089081004,18514545326900,11719462813636,
    7264486517034,4412664793434,2628276528520,1535931263374,881135414242,496487013924,
    274901921996,149640762400,80114353782,42202140264,21882052128,11171919762,5618265544,
    2783891404,1359601730,654647902,310857736,145609226,67297606,30697216,13822532,6145558,
    2698434,1170374,501506,212346,88852,36744,15014,6056,2406,940,356,128,40,10]]
private def pvm_0_14 : List ℤ := pZZZ 445
  [
   [2872697546006,10528728381172,27232452483272,57397120707512,104558795344554,170024236399650,
    251885747428902,344789787679518,440594384670240,529755282131444,603058182519614,
    653237940644182,676101959443978,670954535418884,640325903366774,589176091304866,
    523830430973168,450906020531774,376428031702504,305244582461906,240760163366412,
    184941217438648,138511673441570,101248812010746,72302524030194,50483847586868,34493144856500,
    23078847930458,15131872842934,9728452655484,6136544483576,3799903626462,2311075132046,
    1381206516202,811528642090,468959997362,266642819260,149228523682,82235323988,44637318270,
    23873263142,12584422672,6540182934,3351990356,1694678788,845383980,416205574,202278478,
    97067904,46002136,21535018,9960056,4552066,2056188,918114,405294,176912,76362,32594,13752,
    5732,2352,950,376,138,44,12,2]]
private def pvm_0_15 : List ℤ := pZZZ 441
  [
   [1080176879722,4252720027858,11815764021080,26751468821656,52347850760424,91438304509114,
    145511816002128,213956105301656,293685942569076,379307733702080,463816405384998,
    539668501606268,599977455754968,639559843515582,655620934505666,647975810224208,
    618820410894684,572161270111556,513063580270238,446881415387930,378601515397634,
    312379921473938,251296099312388,197304763632688,151337880823582,113498855927346,
    83294239723940,59860140710524,42155671845522,29110195266346,19722480963338,13117311861966,
    8568784537660,5500408780784,3471120450162,2154415218068,1315677882220,790853225150,
    468085422418,272888829844,156754024524,88747832976,49537056704,27268245918,14806563494,
    7932893624,4194638620,2189493642,1128431934,574356904,288769650,143439680,70407126,34156362,
    16379836,7766090,3640986,1688202,774252,351272,157674,70028,30768,13366,5742,2436,1014,410,
    158,56,16,2]]
private def pvm_0_16 : List ℤ := pZZZ 437
  [
   [378603483498,1594378139688,4738264578078,11474565267466,24016887462264,44871794858884,
    76378143449776,120121080773242,176359787961382,243628515449392,318640291627630,
    396550015647032,471541911958464,537624652972980,589469816401638,623126868044048,
    636486785683372,629431464854602,603676908566284,562376556249740,509585373022212,
    449692415532556,386913781392804,324907829722116,266540104984948,213794665599850,
    167806573640434,128978853069242,97145284467768,71745375981740,51986620631936,36978925421536,
    25834866604792,17736081785314,11970334124332,7945807275448,5189534231722,3336130599406,
    2111731870942,1316631014000,808834829124,489733579528,292342169808,172097978868,99937458842,
    57261046546,32379786804,18074782026,9962144948,5422575518,2915545144,1548745964,812958406,
    421757156,216290702,109664710,54981846,27262280,13370880,6487460,3114342,1479414,695506,
    323630,149060,67956,30668,13696,6048,2636,1130,474,192,72,22,4]]
private def pvm_0_17 : List ℤ := pZZZ 433
  [
   [123624415574,554792636852,1757018698464,4534287385020,10113541447662,20135931210348,
    36523898322396,61211781217386,95768155301592,140978683274388,196484279519442,260570283666986,
    330175634661944,401143457846934,468679479390200,527937709257282,574626232659226,
    605525404683644,618834272347000,614300528546800,593133610355356,557739054679192,
    511337470138062,457540493459022,399950161965308,341831550756462,285886884898964,
    234137927877510,187906150907632,147869027219044,114166038293392,86528602565008,64412432844266,
    47116959222062,33882851673782,23964249683462,16676477985014,11422657623090,7703872231030,
    5117744228910,3349782108344,2161010291788,1374442813486,862079376166,533376754522,
    325609734882,196174440330,116672865694,68513481062,39733167668,22760918112,12881624782,
    7204059052,3981877656,2175594008,1175220904,627744042,331615096,173276378,89569514,45809662,
    23183988,11612062,5756710,2825108,1372594,660298,314532,148372,69310,32064,14684,6650,2976,
    1316,568,236,92,30,6]]
private def pvm_0_18 : List ℤ := pZZZ 428
  [
   [37581905314,179145396636,602628448584,1651879758082,3913511831080,8276123752622,
    15944911334744,28383607277336,47167096693794,73748770790216,109171762429394,153775248912570,
    206958600196412,267062517788020,331407091360330,396496209587652,458363648857158,
    513007031018652,556838688500524,587080823700258,602045575373174,601264533193872,
    585460652822088,556381988250728,516536128296576,468873988241866,416471479043180,
    362249429985044,308759062876578,258045673006896,211589842022738,170315417235272,
    134647482011322,104601502006364,79885990668144,60004301369380,44345405678440,32257824938608,
    23104601869240,16299991053500,11330330878326,7762435228076,5243011666782,3492305881420,
    2294604552584,1487571228266,951759698268,601114397580,374855211156,230854763512,140433731794,
    84400728220,50123868366,29420149586,17069560862,9791504244,5553871258,3115506768,1728672984,
    948878728,515326620,276940610,147291996,77537974,40405924,20845942,10648616,5386504,2698412,
    1338880,658028,320368,154520,73838,34948,16380,7602,3488,1580,702,302,122,42,12,2]]
private def pvm_0_19 : List ℤ := pZZZ 426
  [
   [16324351146,80876713098,282765659118,805588301818,1983615737314,4359859907928,8730132237016,
    16151689169984,27895852645034,45331898691070,69743953841152,102100599629024,142813556847806,
    191532065518282,247019613988230,307148404051098,369026425040148,429246916200786,
    484226251923514,530579394946788,565475645768382,586922378536252,593938989177738,
    586603596270102,565976493046954,533922666989616,492867870465872,445527456993596,
    394644899849350,342769267201184,292090290801902,244338430068840,200747460500428,
    162069857523624,128631092776708,100407746641108,77115463219708,58295418156708,43391317005788,
    31812310317530,22980127748938,16360943228346,11483920457382,7949121432576,5427635981564,
    3656580505376,2431183223710,1595655088448,1034035523294,661758097222,418329875334,
    261263753896,161235837504,98343215894,59292930366,35343497536,20832143724,12143486880,
    7001685784,3993687262,2253813628,1258614332,695591562,380502272,206041216,110457624,58631526,
    30818270,16042530,8271220,4224168,2137122,1071200,531986,261792,127658,61682,29526,14002,6574,
    3052,1400,626,268,110,40,10]]
private theorem pchk_0_0 : pChk 3 513
    phbv_0 rkmViHi_m512_r512_s0_c0 pvm_0_1 = true := by
  decide +kernel
private theorem pchk_0_1 : pChk 3 513
    phbv_0 pvm_0_1 pvm_0_2 = true := by
  decide +kernel
private theorem pchk_0_2 : pChk 3 513
    phbv_0 pvm_0_2 pvm_0_3 = true := by
  decide +kernel
private theorem pchk_0_3 : pChk 3 513
    phbv_0 pvm_0_3 pvm_0_4 = true := by
  decide +kernel
private theorem pchk_0_4 : pChk 3 513
    phbv_0 pvm_0_4 pvm_0_5 = true := by
  decide +kernel
private theorem pchk_0_5 : pChk 3 513
    phbv_0 pvm_0_5 pvm_0_6 = true := by
  decide +kernel
private theorem pchk_0_6 : pChk 3 513
    phbv_0 pvm_0_6 pvm_0_7 = true := by
  decide +kernel
private theorem pchk_0_7 : pChk 3 513
    phbv_0 pvm_0_7 pvm_0_8 = true := by
  decide +kernel
private theorem pchk_0_8 : pChk 3 513
    phbv_0 pvm_0_8 pvm_0_9 = true := by
  decide +kernel
private theorem pchk_0_9 : pChk 3 513
    phbv_0 pvm_0_9 pvm_0_10 = true := by
  decide +kernel
private theorem pchk_0_10 : pChk 3 513
    phbv_0 pvm_0_10 pvm_0_11 = true := by
  decide +kernel
private theorem pchk_0_11 : pChk 3 513
    phbv_0 pvm_0_11 pvm_0_12 = true := by
  decide +kernel
private theorem pchk_0_12 : pChk 3 513
    phbv_0 pvm_0_12 pvm_0_13 = true := by
  decide +kernel
private theorem pchk_0_13 : pChk 3 513
    phbv_0 pvm_0_13 pvm_0_14 = true := by
  decide +kernel
private theorem pchk_0_14 : pChk 3 513
    phbv_0 pvm_0_14 pvm_0_15 = true := by
  decide +kernel
private theorem pchk_0_15 : pChk 3 513
    phbv_0 pvm_0_15 pvm_0_16 = true := by
  decide +kernel
private theorem pchk_0_16 : pChk 3 513
    phbv_0 pvm_0_16 pvm_0_17 = true := by
  decide +kernel
private theorem pchk_0_17 : pChk 3 513
    phbv_0 pvm_0_17 pvm_0_18 = true := by
  decide +kernel
private theorem pchk_0_18 : pChk 2 513
    phbv_0 pvm_0_18 pvm_0_19 = true := by
  decide +kernel
private theorem pchk_0_19 : pChk 2 513
    phbv_0 pvm_0_19 rkmVoHi_m512_r512_s0_c0 = true := by
  decide +kernel
private theorem pwalkF_0 : muxFastIterFullT16 58 513
    phbv_0 rkmViHi_m512_r512_s0_c0 = rkmVoHi_m512_r512_s0_c0 :=
  pChFull 56 2 513 (pChFull 54 2 513 (pChFull 51 3 513 (pChFull 48 3 513 (pChFull 45 3 513
    (pChFull 42 3 513 (pChFull 39 3 513 (pChFull 36 3 513 (pChFull 33 3 513 (pChFull 30 3 513
    (pChFull 27 3 513 (pChFull 24 3 513 (pChFull 21 3 513 (pChFull 18 3 513 (pChFull 15 3 513
    (pChFull 12 3 513 (pChFull 9 3 513 (pChFull 6 3 513 (pChFull 3 3 513 (pCS pchk_0_0) pchk_0_1)
    pchk_0_2) pchk_0_3) pchk_0_4) pchk_0_5) pchk_0_6) pchk_0_7) pchk_0_8) pchk_0_9) pchk_0_10)
    pchk_0_11) pchk_0_12) pchk_0_13) pchk_0_14) pchk_0_15) pchk_0_16) pchk_0_17) pchk_0_18)
    pchk_0_19
/-- Certified `T_16` walk chunk `m512_r512_s0_c0`. -/
theorem rkmWalkChkHi_m512_r512_s0_c0 : muxFastIterFullT16 58 513
    rkmHbHi_m512_r512_s0_c0 rkmViHi_m512_r512_s0_c0 = rkmVoHi_m512_r512_s0_c0 :=
  (congrArg (fun h => muxFastIterFullT16 58 513 h rkmViHi_m512_r512_s0_c0)
    (muxIntListEq_eq_true.mp dkhb_0)).trans pwalkF_0
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T3`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T3 :
    rkmWalkChkHi_m512_r512_s0_c0 = rkmWalkChkHi_m512_r512_s0_c0 :=
  rfl
private theorem laneRoot_Hi512T3 : rkmHbHi_m512_r512_s0_c0 = rkmHbHi_m512_r512_s0_c0 :=
  (And.intro (Eq.refl rkmFlipGapsHi512T2) rfl).right
end
end QuantumComputation.Specs.DickeSol
