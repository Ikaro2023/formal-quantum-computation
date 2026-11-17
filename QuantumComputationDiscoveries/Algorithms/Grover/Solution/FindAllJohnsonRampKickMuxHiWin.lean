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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxEval
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase
/-
# Halo-16 Windowed Evaluator Core & Row Stitcher (`FindAllJohnsonRampKickMuxHiWin`)
-/
namespace QuantumComputation.Specs.DickeSol
section Sec_FindAllJohnsonRampKickMuxHiWinCore
@[expose] public section
open Real
open scoped Matrix NNRat NNReal ENNReal
/-- Primitive `|z|` on `ℤ` avoiding typeclass synthesis inside `decide +kernel`. -/
def rkmIntAbsNat : ℤ → ℕ
  | Int.ofNat n => n
  | Int.negSucc n => Nat.add n 1
/-- Prepends `k` forced zero coordinates to `xs`. -/
def rkmPrependZeros : ℕ → List ℤ → List ℤ
  | 0, xs => xs
  | k + 1, xs => highdStrictConsInt (Int.ofNat 0) (rkmPrependZeros k xs)
/-- Drops the first `k` coordinates of `xs`. -/
def rkmDropInts : ℕ → List ℤ → List ℤ
  | 0, xs => xs
  | _, [] => []
  | k + 1, _ :: xs => rkmDropInts k xs
/-- Left-trims leading coordinates `|x| <= thr`, advancing `off` and accumulating `L1` mass. -/
def rkmTrimLeft (thr : ℕ) : ℕ → List ℤ → ℕ → ℕ × List ℤ × ℕ
  | _, [], acc => (0, [], acc)
  | off, x :: xs, acc =>
    let ax := rkmIntAbsNat x
    match Nat.ble ax thr with
    | true =>
      HighDForce.withForcedNat (Nat.add off 1) fun off1 =>
        HighDForce.withForcedNat (Nat.add acc ax) fun acc1 =>
          rkmTrimLeft thr off1 xs acc1
    | false => (off, x :: xs, acc)
/-- Right-trims trailing coordinates `|x| <= thr` in one pass, returning `(trimmed, dropR)`. -/
def rkmTrimRight (thr : ℕ) : List ℤ → List ℤ × ℕ
  | [] => ([], 0)
  | x :: xs =>
    match rkmTrimRight thr xs with
    | ([], dTail) =>
      let ax := rkmIntAbsNat x
      match Nat.ble ax thr with
      | true => HighDForce.withForcedNat (Nat.add ax dTail) fun dSum => ([], dSum)
      | false => (highdStrictConsInt x [], dTail)
    | (y :: ys, dTail) => (highdStrictConsInt x (y :: ys), dTail)
/-- Two-sided window trim on `(off, xs)`, accumulating exact dropped `L1` mass into
  `dropAcc`. -/
def rkmTrimWin (thr off : ℕ) (xs : List ℤ) (dropAcc : ℕ) : ℕ × List ℤ × ℕ :=
  match rkmTrimLeft thr off xs dropAcc with
  | (off1, xs1, d1) =>
    match rkmTrimRight thr xs1 with
    | ([], d2) => HighDForce.withForcedNat (Nat.add d1 d2) fun dOut => (0, [], dOut)
    | (y :: ys, d2) => HighDForce.withForcedNat (Nat.add d1 d2) fun dOut => (off1, y :: ys, dOut)
/-- Single `+16`-halo `T_16` substep followed by two-sided `thr` window trim. -/
def muxWinStepT16 (thr d : ℕ) (hb : List ℤ)
    (off : ℕ) (xs : List ℤ) (dropAcc : ℕ) : ℕ × List ℤ × ℕ :=
  HighDForce.withForcedNat (Nat.sub off 16) fun sLo =>
    HighDForce.withForcedNat (Nat.sub off sLo) fun padL =>
      HighDForce.withForcedNat (Nat.sub (Nat.add d 1) sLo) fun remMax =>
        HighDForce.withForcedList (rkmDropInts sLo hb) fun hbSl =>
          HighDForce.withForcedList (rkmPrependZeros padL xs) fun vecSl =>
            HighDForce.withForcedNat (altIntLen vecSl) fun curLen =>
              HighDForce.withForcedList
                (muxUltraIterFullT16Rkm 1 remMax curLen hbSl vecSl) fun rawSl =>
                rkmTrimWin thr sLo rawSl dropAcc
/-- Iterates `steps` halo-windowed `T_16` substeps with `O(wHi - wLo + 32)` stage work. -/
def muxWinIterT16 : ℕ → ℕ → ℕ → List ℤ → ℕ → List ℤ → ℕ → ℕ × List ℤ × ℕ
  | 0, _, _, _, off, xs, dropAcc => (off, xs, dropAcc)
  | k + 1, thr, d, hb, off, xs, dropAcc =>
    match muxWinStepT16 thr d hb off xs dropAcc with
    | (off1, xs1, drop1) => muxWinIterT16 k thr d hb off1 xs1 drop1
/-- Bounded `steps`-substep windowed `T_16` chunk checker for `decide +kernel` parts. -/
def muxWinIterT16HiChk (steps thr tag d : ℕ) (hb : List ℤ)
    (offIn : ℕ) (xsIn : List ℤ) (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  let _ := tag
  HighDForce.withForcedList hb fun hbF =>
    HighDForce.withForcedList xsIn fun inF =>
      HighDForce.withForcedList xsOut fun outF =>
        match muxWinIterT16 steps thr d hbF offIn inF 0 with
        | (oRes, xRes, dRes) =>
          Bool.and (Nat.beq oRes offOut)
            (Bool.and (muxIntListEq xRes outF) (Nat.beq dRes dropExp))
/-- Semantic soundness of `steps` windowed `T_16` substeps with `L1` trim budget
  `dropChunk`. -/
def RkmWinIterSound (steps d : ℕ) (hb : List ℤ)
    (offIn : ℕ) (xsIn : List ℤ) (offOut : ℕ) (xsOut : List ℤ) (dropChunk : ℕ) : Prop :=
  hb.length = d →
  offIn + xsIn.length ≤ d + 1 → offOut + xsOut.length ≤ d + 1 ∧ ∀ (_hd : d ≤ 1024)
      (_hG : ∀ u, vecNorm (rkmPtGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u),
      vecNorm (rkmListToOrbVec d (rkmPrependZeros offOut xsOut) -
        ((taylor16OfMat (rkmPtGenMat d hb)) ^ steps) *ᵥ
          rkmListToOrbVec d (rkmPrependZeros offIn xsIn)) ≤
        (((297 / 2) * (steps : ℝ) + (dropChunk : ℝ))) / wdScaleR
/-- Pre-certified windowed segment walk witness (`m`-independent, reusable across equal
  `mEff`). -/
structure RkmWinSegWalk where
  d : ℕ
  hbExp : List ℤ
  offIn : ℕ
  xsIn : List ℤ
  offOut : ℕ
  xsOut : List ℤ
  dropSeg : ℕ
/-- Semantic soundness of one pre-certified windowed segment walk over `nSub` substeps. -/
def RkmWinSegWalkSound (nSub : ℕ) (w : RkmWinSegWalk) : Prop := w.hbExp.length = w.d ∧
  w.offIn + w.xsIn.length ≤ w.d + 1 ∧
  w.offOut + w.xsOut.length ≤ w.d + 1 ∧
  ∀ (_hd : w.d ≤ 1024)
    (_hG : ∀ u, vecNorm (rkmPtGenMat w.d w.hbExp *ᵥ u) ≤ (3 / 2) * vecNorm u),
    vecNorm (rkmListToOrbVec w.d (rkmPrependZeros w.offOut w.xsOut) -
      ((taylor16OfMat (rkmPtGenMat w.d w.hbExp)) ^ nSub) *ᵥ
        rkmListToOrbVec w.d (rkmPrependZeros w.offIn w.xsIn)) ≤
      (((297 / 2) * (nSub : ℝ) + (w.dropSeg : ℝ))) / wdScaleR
/-- Conjunction of `RkmWinSegWalkSound` across all segments of an active row. -/
def RkmWinSegWalksSound : List ℕ → List RkmWinSegWalk → Prop
  | [], [] => True
  | nSub :: nsubRest, w :: wRest => RkmWinSegWalkSound nSub w ∧ RkmWinSegWalksSound nsubRest wRest
  | _, _ => False
end
public section
open Real
open scoped Matrix NNRat NNReal ENNReal
theorem rkmw_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkmw_nat_ble_eq_true]
theorem rkmw_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, rkmw_nat_ble_eq_true]; omega
theorem rkmw_primNatBlt_eq_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  change Nat.blt a b = true ↔ a < b; unfold Nat.blt; exact rkmw_nat_ble_eq_true
theorem rkmw_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, rkmw_primNatBlt_eq_true]; omega
theorem rkmw_nat_beq_eq_true : ∀ {a b : ℕ}, Nat.beq a b = true ↔ a = b
  | 0, 0 => ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | 0, _ + 1 => ⟨Bool.noConfusion, fun h ↦ nomatch h⟩
  | _ + 1, 0 => ⟨Bool.noConfusion, fun h ↦ nomatch h⟩
  | a + 1, b + 1 =>
    ⟨fun h ↦ congrArg Nat.succ ((@rkmw_nat_beq_eq_true a b).mp h),
      fun h ↦ (@rkmw_nat_beq_eq_true a b).mpr (Nat.succ.inj h)⟩
theorem rkmw_nat_beq_eq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, rkmw_nat_beq_eq_true]
theorem rkmw_strictConsInt_eq (x : ℤ) (xs : List ℤ) : highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.ofNat 0] | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t) =
      Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]; cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.negSucc 0] | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t) =
      Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]; cases xs <;> rfl
private theorem rkmw_intAbsNat_eq (z : ℤ) : rkmIntAbsNat z = Int.natAbs z := by
  cases z <;> rfl
theorem rkmw_altIntLen_eq : ∀ xs : List ℤ, altIntLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (rkmw_altIntLen_eq xs)
theorem rkmw_prependZeros_cons (k : ℕ) (xs : List ℤ) :
    rkmPrependZeros (k + 1) xs = (0 : ℤ) :: rkmPrependZeros k xs := by
  simp only [rkmPrependZeros, rkmw_strictConsInt_eq]; rfl
theorem rkmw_prependZeros_length :
    ∀ (k : ℕ) (xs : List ℤ), (rkmPrependZeros k xs).length = k + xs.length
  | 0, xs => by simp [rkmPrependZeros]
  | k + 1, xs => by
    rw [rkmw_prependZeros_cons, List.length_cons, rkmw_prependZeros_length k xs]; omega
private theorem rkmw_prependZeros_add : ∀ (a b : ℕ) (xs : List ℤ),
      rkmPrependZeros (a + b) xs = rkmPrependZeros a (rkmPrependZeros b xs)
  | 0, _, _ => by simp [rkmPrependZeros]
  | a + 1, b, xs => by
    rw [show a + 1 + b = (a + b) + 1 by omega, rkmw_prependZeros_cons, rkmw_prependZeros_cons,
      rkmw_prependZeros_add a b xs]
private theorem rkmw_dropInts_eq : ∀ (k : ℕ) (xs : List ℤ), rkmDropInts k xs = xs.drop k
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: xs => rkmw_dropInts_eq k xs
private theorem rkmw_ultraIter_eq (steps maxLen : ℕ) (hb vec : List ℤ) :
    muxUltraIterFullT16Rkm steps maxLen (altIntLen vec) hb vec =
      muxFastIterFullT16 steps maxLen hb vec := by
  have hchk : muxUltraIterFullT16HiChk steps 0 maxLen hb vec
      (muxUltraIterFullT16Rkm steps maxLen (altIntLen vec) hb vec) = true := by
    unfold muxUltraIterFullT16HiChk; simp only [rkmb_forceList_eq, rkmb_forceNat_eq]
    exact muxIntListEq_eq_true.mpr rfl
  exact (muxUltraIterFullT16HiChk_sound hchk).symm
/- ## Section 1: `L1` Trim Accounting & Orbital Norm Lift -/
private def rkmListL1Diff : List ℤ → List ℤ → ℕ
  | [], [] => 0
  | x :: xs, [] => Int.natAbs x + rkmListL1Diff xs []
  | [], y :: ys => Int.natAbs y + rkmListL1Diff [] ys
  | x :: xs, y :: ys => Int.natAbs (x - y) + rkmListL1Diff xs ys
private theorem rkmw_l1Diff_self : ∀ u : List ℤ, rkmListL1Diff u u = 0
  | [] => by simp [rkmListL1Diff]
  | x :: xs => by simp [rkmListL1Diff, rkmw_l1Diff_self xs]
private theorem rkmw_l1Diff_nil_prepend : ∀ k : ℕ, rkmListL1Diff [] (rkmPrependZeros k []) = 0
  | 0 => by simp [rkmPrependZeros, rkmListL1Diff]
  | k + 1 => by rw [rkmw_prependZeros_cons]; simp [rkmListL1Diff, rkmw_l1Diff_nil_prepend k]
private theorem rkmw_l1Diff_prepend_nil : ∀ k : ℕ, rkmListL1Diff (rkmPrependZeros k []) [] = 0
  | 0 => by simp [rkmPrependZeros, rkmListL1Diff]
  | k + 1 => by rw [rkmw_prependZeros_cons]; simp [rkmListL1Diff, rkmw_l1Diff_prepend_nil k]
private theorem rkmw_l1Diff_prepend : ∀ (k : ℕ) (u v : List ℤ),
      rkmListL1Diff (rkmPrependZeros k u) (rkmPrependZeros k v) = rkmListL1Diff u v
  | 0, _, _ => rfl
  | k + 1, u, v => by
    rw [rkmw_prependZeros_cons, rkmw_prependZeros_cons]
    simp [rkmListL1Diff, rkmw_l1Diff_prepend k u v]
private theorem rkmw_l1Diff_tri :
    ∀ u v w : List ℤ, rkmListL1Diff u w ≤ rkmListL1Diff u v + rkmListL1Diff v w
  | [], [], _ => by simp [rkmListL1Diff]
  | _ :: _, [], [] => by simp [rkmListL1Diff]
  | x :: xs, [], z :: zs => by
    simp only [rkmListL1Diff]
    have h1 : Int.natAbs (x - z) ≤ Int.natAbs x + Int.natAbs z := by
      simpa [sub_eq_add_neg] using Int.natAbs_add_le x (-z)
    have ih := rkmw_l1Diff_tri xs [] zs; omega
  | [], _ :: _, [] => by simp [rkmListL1Diff]
  | [], y :: ys, z :: zs => by
    simp only [rkmListL1Diff]
    have h1 : Int.natAbs z ≤ Int.natAbs y + Int.natAbs (y - z) := by
      have h := Int.natAbs_add_le y (z - y)
      have heq : Int.natAbs (z - y) = Int.natAbs (y - z) := by
        rw [← Int.natAbs_neg]; congr 1; ring
      rw [show y + (z - y) = z by ring, heq] at h; exact h
    have ih := rkmw_l1Diff_tri [] ys zs; omega
  | x :: xs, y :: ys, [] => by
    simp only [rkmListL1Diff]
    have h1 : Int.natAbs x ≤ Int.natAbs (x - y) + Int.natAbs y := by
      simpa using Int.natAbs_add_le (x - y) y
    have ih := rkmw_l1Diff_tri xs ys []; omega
  | x :: xs, y :: ys, z :: zs => by
    simp only [rkmListL1Diff]
    have h1 : Int.natAbs (x - z) ≤ Int.natAbs (x - y) + Int.natAbs (y - z) := by
      simpa [show (x - y) + (y - z) = x - z by ring] using Int.natAbs_add_le (x - y) (y - z)
    have ih := rkmw_l1Diff_tri xs ys zs; omega
private theorem rkmw_sum_range_succ_shift (f : ℕ → ℕ) :
    ∀ m : ℕ, (∑ j ∈ Finset.range (m + 1), f j) = f 0 + ∑ j ∈ Finset.range m, f (j + 1)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, rkmw_sum_range_succ_shift f m, Finset.sum_range_succ, add_assoc]
private theorem rkmw_sum_getD_le_l1Diff : ∀ (m : ℕ) (u v : List ℤ),
      (∑ j ∈ Finset.range m, Int.natAbs (u.getD j 0 - v.getD j 0)) ≤ rkmListL1Diff u v
  | 0, _, _ => by simp
  | m + 1, [], [] => by rw [rkmw_sum_range_succ_shift]; simp [rkmListL1Diff]
  | m + 1, x :: xs, [] => by
    rw [rkmw_sum_range_succ_shift]
    simp only [List.getD_cons_zero, List.getD_nil, sub_zero, List.getD_cons_succ, rkmListL1Diff]
    have ih := rkmw_sum_getD_le_l1Diff m xs []; simp only [List.getD_nil, sub_zero] at ih; omega
  | m + 1, [], y :: ys => by
    rw [rkmw_sum_range_succ_shift]
    simp only [List.getD_nil, List.getD_cons_zero, zero_sub, Int.natAbs_neg, List.getD_cons_succ,
      rkmListL1Diff]
    have ih := rkmw_sum_getD_le_l1Diff m [] ys
    simp only [List.getD_nil, zero_sub, Int.natAbs_neg] at ih; omega
  | m + 1, x :: xs, y :: ys => by
    rw [rkmw_sum_range_succ_shift]
    simp only [List.getD_cons_zero, List.getD_cons_succ, rkmListL1Diff]
    have ih := rkmw_sum_getD_le_l1Diff m xs ys; omega
private theorem rkmw_cast_natAbs_eq_abs (z : ℤ) : ((Int.natAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n => exact (abs_of_nonneg (Nat.cast_nonneg n)).symm
  | negSucc n =>
    have hneg : (Int.negSucc n : ℝ) = -((n + 1 : ℕ) : ℝ) := (by push_cast; ring)
    rw [hneg, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; rfl
private theorem rkmw_vecNorm_orbVec_sub_le (d : ℕ) (u v : List ℤ) :
    vecNorm (rkmListToOrbVec d u - rkmListToOrbVec d v) ≤ (rkmListL1Diff u v : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; positivity)
  set w := rkmListToOrbVec d u - rkmListToOrbVec d v; set S : ℝ := ∑ a : Fin (d + 1), |w a|
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hw_le_S : vecNorm w ≤ S := by
    rw [vecNorm, Real.sqrt_le_iff]; refine ⟨hS_nn, ?_⟩
    calc vecSqNorm w
        = ∑ a : Fin (d + 1), |w a| * |w a| := by
            unfold vecSqNorm; refine Finset.sum_congr rfl fun a _ ↦ ?_; rw [← sq_abs, sq]
      _ ≤ ∑ a : Fin (d + 1), |w a| * S := by
            refine Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact Finset.single_le_sum (f := fun b : Fin (d + 1) ↦ |w b|)
              (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ a)
      _ = S ^ 2 := by rw [← Finset.sum_mul, sq]
  have hS_eq : S = ((∑ j ∈ Finset.range (d + 1),
      Int.natAbs (u.getD j 0 - v.getD j 0) : ℕ) : ℝ) / wdScaleR := by
    dsimp only [S, w, rkmListToOrbVec, Pi.sub_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ |(u.getD j 0 : ℝ) / wdScaleR -
      (v.getD j 0 : ℝ) / wdScaleR|) (d + 1), Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← sub_div, ← Int.cast_sub, abs_div, abs_of_pos hB, rkmw_cast_natAbs_eq_abs]
  have hnat := rkmw_sum_getD_le_l1Diff (d + 1) u v
  exact hw_le_S.trans (hS_eq.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hnat) hB.le))
private theorem rkmw_trimLeft_sound (thr : ℕ) : ∀ (xs : List ℤ) (off acc : ℕ),
      acc ≤ (rkmTrimLeft thr off xs acc).2.2 ∧
      (rkmTrimLeft thr off xs acc).1 + (rkmTrimLeft thr off xs acc).2.1.length ≤ off + xs.length ∧
      rkmListL1Diff (rkmPrependZeros (rkmTrimLeft thr off xs acc).1
        (rkmTrimLeft thr off xs acc).2.1) (rkmPrependZeros off xs) ≤
        (rkmTrimLeft thr off xs acc).2.2 - acc
  | [], off, acc => by
    dsimp only [rkmTrimLeft, rkmPrependZeros]
    refine ⟨le_rfl, by omega, ?_⟩
    rw [rkmw_l1Diff_nil_prepend]; omega
  | x :: xs, off, acc => by
    unfold rkmTrimLeft; dsimp only
    cases hble : Nat.ble (rkmIntAbsNat x) thr with
    | false => dsimp only; exact ⟨le_rfl, le_rfl, by rw [rkmw_l1Diff_self]; omega⟩
    | true =>
      dsimp only; simp only [rkmb_forceNat_eq]
      have ih := rkmw_trimLeft_sound thr xs (off + 1) (acc + Int.natAbs x)
      rw [show Nat.add off 1 = off + 1 from rfl, rkmw_intAbsNat_eq,
        show Nat.add acc (Int.natAbs x) = acc + Int.natAbs x from rfl]
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
      have hstep : rkmListL1Diff (rkmPrependZeros (off + 1) xs)
          (rkmPrependZeros off (x :: xs)) = Int.natAbs x := by
        rw [rkmw_prependZeros_add off 1 xs,
          rkmw_l1Diff_prepend off (rkmPrependZeros 1 xs) (x :: xs), rkmw_prependZeros_cons]
        simp [rkmPrependZeros, rkmListL1Diff, rkmw_l1Diff_self]
      have htri := rkmw_l1Diff_tri (rkmPrependZeros (rkmTrimLeft thr (off + 1) xs
        (acc + Int.natAbs x)).1 (rkmTrimLeft thr (off + 1) xs (acc + Int.natAbs x)).2.1)
        (rkmPrependZeros (off + 1) xs) (rkmPrependZeros off (x :: xs))
      have ih3 := ih.2.2; omega
private theorem rkmw_trimRight_sound (thr : ℕ) :
    ∀ xs : List ℤ, (rkmTrimRight thr xs).1.length ≤ xs.length ∧
      rkmListL1Diff (rkmTrimRight thr xs).1 xs ≤ (rkmTrimRight thr xs).2
  | [] => by simp [rkmTrimRight, rkmListL1Diff]
  | x :: xs => by
    unfold rkmTrimRight
    rcases hrec : rkmTrimRight thr xs with ⟨ys, dTail⟩
    have ih := rkmw_trimRight_sound thr xs; rw [hrec] at ih
    cases ys with
    | nil =>
      dsimp only
      cases hble : Nat.ble (rkmIntAbsNat x) thr with
      | true =>
        dsimp only; rw [rkmb_forceNat_eq, rkmw_intAbsNat_eq]
        refine ⟨Nat.zero_le _, ?_⟩
        simp only [rkmListL1Diff, Nat.add_eq]; exact Nat.add_le_add_left ih.2 _
      | false =>
        dsimp only; rw [rkmw_strictConsInt_eq]
        refine ⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩
        simp only [rkmListL1Diff, sub_self, Int.natAbs_zero, zero_add]; exact ih.2
    | cons y ys' =>
      dsimp only; rw [rkmw_strictConsInt_eq]
      refine ⟨Nat.succ_le_succ ih.1, ?_⟩
      simp only [rkmListL1Diff, sub_self, Int.natAbs_zero, zero_add]; exact ih.2
private theorem rkmw_trimWin_sound (thr off : ℕ) (xs : List ℤ) (dropAcc : ℕ) :
    dropAcc ≤ (rkmTrimWin thr off xs dropAcc).2.2 ∧
    (rkmTrimWin thr off xs dropAcc).1 + (rkmTrimWin thr off xs dropAcc).2.1.length ≤
      off + xs.length ∧
    rkmListL1Diff (rkmPrependZeros (rkmTrimWin thr off xs dropAcc).1
      (rkmTrimWin thr off xs dropAcc).2.1) (rkmPrependZeros off xs) ≤
      (rkmTrimWin thr off xs dropAcc).2.2 - dropAcc := by
  unfold rkmTrimWin; have hl := rkmw_trimLeft_sound thr xs off dropAcc
  rcases hL : rkmTrimLeft thr off xs dropAcc with ⟨off1, xs1, d1⟩
  rw [hL] at hl; dsimp only at hl ⊢; have hr := rkmw_trimRight_sound thr xs1
  rcases hR : rkmTrimRight thr xs1 with ⟨xs2, d2⟩
  rw [hR] at hr; dsimp only at hr ⊢; have hl1 := hl.1; have hl2 := hl.2.1; have hl3 := hl.2.2
  have hr1 := hr.1; have hr2 := hr.2
  cases xs2 with
  | nil =>
    dsimp only; simp only [rkmb_forceNat_eq]
    have h0 : rkmListL1Diff (rkmPrependZeros 0 []) (rkmPrependZeros off1 xs1) =
        rkmListL1Diff [] xs1 := by
      have htri1 := rkmw_l1Diff_tri [] (rkmPrependZeros off1 []) (rkmPrependZeros off1 xs1)
      have htri2 := rkmw_l1Diff_tri (rkmPrependZeros off1 []) [] (rkmPrependZeros off1 xs1)
      rw [rkmw_l1Diff_nil_prepend, rkmw_l1Diff_prepend] at htri1
      rw [rkmw_l1Diff_prepend_nil, rkmw_l1Diff_prepend] at htri2
      dsimp only [rkmPrependZeros]; omega
    have htri := rkmw_l1Diff_tri (rkmPrependZeros 0 []) (rkmPrependZeros off1 xs1)
      (rkmPrependZeros off xs)
    refine ⟨by simp only [Nat.add_eq]; omega, by omega, ?_⟩
    simp only [Nat.add_eq]; omega
  | cons y ys =>
    dsimp only; simp only [rkmb_forceNat_eq]
    have hp : rkmListL1Diff (rkmPrependZeros off1 (y :: ys)) (rkmPrependZeros off1 xs1) =
        rkmListL1Diff (y :: ys) xs1 := rkmw_l1Diff_prepend off1 (y :: ys) xs1
    have htri := rkmw_l1Diff_tri (rkmPrependZeros off1 (y :: ys)) (rkmPrependZeros off1 xs1)
      (rkmPrependZeros off xs)
    refine ⟨by simp only [Nat.add_eq]; omega, by omega, ?_⟩
    simp only [Nat.add_eq]; omega
/- ## Section 2: Exact `+16`-Halo Shift Identity for `muxFastHornerT16Step` -/
private def rkmZeroPrefix : ℕ → List ℤ → Prop
  | 0, _ => True
  | _, [] => True
  | k + 1, x :: xs => x = 0 ∧ rkmZeroPrefix k xs
private theorem rkmw_zeroPrefix_prepend : ∀ (k : ℕ) (xs : List ℤ),
    rkmZeroPrefix k (rkmPrependZeros k xs)
  | 0, _ => trivial
  | k + 1, xs => by rw [rkmw_prependZeros_cons]; exact ⟨rfl, rkmw_zeroPrefix_prepend k xs⟩
private theorem rkmw_zeroPrefix_mono :
    ∀ {j k : ℕ} {xs : List ℤ}, j ≤ k → rkmZeroPrefix k xs → rkmZeroPrefix j xs
  | 0, _, _, _, _ => trivial
  | _ + 1, _, [], _, _ => trivial
  | j + 1, 0, _ :: _, hjk, _ => absurd hjk (Nat.not_le_of_gt (Nat.succ_pos j))
  | _ + 1, _ + 1, _ :: _, hjk, ⟨hx, hrest⟩ => ⟨hx, rkmw_zeroPrefix_mono (by omega) hrest⟩
private theorem rkmw_rawMul_zero (b : ℤ) : muxRawIntMul b (Int.ofNat 0) = Int.ofNat 0 := by
  cases b <;> rfl
private theorem rkmw_primMul_zero (b : ℤ) : primIntMul b (Int.ofNat 0) = Int.ofNat 0 := by
  rw [primIntMul_eq]; change b * 0 = 0; ring
private theorem rkmw_tdiv_zero (dNat : ℕ) :
    muxRawIntTdivNat (Int.ofNat 0) dNat = Int.ofNat 0 := by
  change Int.ofNat (0 / dNat) = Int.ofNat 0; rw [Nat.zero_div]
private theorem rkmw_zero_q (dNat : ℕ) :
    muxRawIntTdivNat (muxRawIntSub (Int.ofNat 0) (Int.ofNat 0)) dNat = Int.ofNat 0 :=
  rkmw_tdiv_zero dNat
private theorem rkmw_zeroPrefix_slide (dNat : ℕ) : ∀ (rem k : ℕ) (hb vec cur : List ℤ),
      rkmZeroPrefix k vec → rkmZeroPrefix (k + 1) cur →
      rkmZeroPrefix k (muxFastSlideLoopAux dNat rem (Int.ofNat 0) hb vec cur)
  | 0, k, _, _, _, _, _ => by cases k <;> trivial
  | _ + 1, 0, _, _, _, _, _ => trivial
  | rem + 1, k + 1, [], vec, cur, hv, hc => by
    rcases vec with _ | ⟨v, vt⟩ <;> rcases cur with _ | ⟨c0, ct⟩
    · unfold muxFastSlideLoopAux; dsimp only; rw [rkmw_tdiv_zero, rkmw_strictConsInt_eq]
      exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k [] [] [] (by cases k <;> trivial) trivial⟩
    · unfold muxFastSlideLoopAux; dsimp only; rw [rkmw_tdiv_zero, rkmw_strictConsInt_eq]
      exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k [] [] ct (by cases k <;> trivial) hc.2⟩
    · have hv0 : v = Int.ofNat 0 := hv.1; unfold muxFastSlideLoopAux; dsimp only
      rw [hv0, rkmw_tdiv_zero, rkmw_strictConsInt_eq]
      exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k [] vt [] hv.2 trivial⟩
    · have hv0 : v = Int.ofNat 0 := hv.1; unfold muxFastSlideLoopAux; dsimp only
      rw [hv0, rkmw_tdiv_zero, rkmw_strictConsInt_eq]
      exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k [] vt ct hv.2 hc.2⟩
  | rem + 1, k + 1, b :: hbRest, vec, cur, hv, hc => by
    rcases vec with _ | ⟨v, vTail⟩
    · rcases cur with _ | ⟨c0, cTail⟩
      · unfold muxFastSlideLoopAux; dsimp only
        rw [rkmw_strictConsInt_eq, rkmw_rawMul_zero, rkmw_primMul_zero, rkmw_zero_q]
        exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k hbRest [] []
          (by cases k <;> trivial) trivial⟩
      · have hc0 : c0 = Int.ofNat 0 := hc.1
        rcases cTail with _ | ⟨cn, ct2⟩
        · unfold muxFastSlideLoopAux; dsimp only
          rw [rkmw_strictConsInt_eq, hc0, rkmw_rawMul_zero, rkmw_primMul_zero, rkmw_zero_q]
          exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k hbRest [] []
            (by cases k <;> trivial) trivial⟩
        · have hcn : cn = Int.ofNat 0 := hc.2.1; unfold muxFastSlideLoopAux; dsimp only
          rw [rkmw_strictConsInt_eq, hc0, hcn, rkmw_rawMul_zero, rkmw_primMul_zero, rkmw_zero_q]
          exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k hbRest [] _
            (by cases k <;> trivial) ⟨rfl, hc.2.2⟩⟩
    · have hv0 : v = Int.ofNat 0 := hv.1
      rcases cur with _ | ⟨c0, cTail⟩
      · unfold muxFastSlideLoopAux; dsimp only
        rw [rkmw_strictConsInt_eq, hv0, rkmw_rawMul_zero, rkmw_primMul_zero, rkmw_zero_q]
        exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k hbRest vTail [] hv.2 trivial⟩
      · have hc0 : c0 = Int.ofNat 0 := hc.1
        rcases cTail with _ | ⟨cn, ct2⟩
        · unfold muxFastSlideLoopAux; dsimp only
          rw [rkmw_strictConsInt_eq, hv0, hc0, rkmw_rawMul_zero, rkmw_primMul_zero, rkmw_zero_q]
          exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k hbRest vTail [] hv.2 trivial⟩
        · have hcn : cn = Int.ofNat 0 := hc.2.1; unfold muxFastSlideLoopAux; dsimp only
          rw [rkmw_strictConsInt_eq, hv0, hc0, hcn, rkmw_rawMul_zero, rkmw_primMul_zero,
            rkmw_zero_q]
          exact ⟨rfl, rkmw_zeroPrefix_slide dNat rem k hbRest vTail _ hv.2 ⟨rfl, hc.2.2⟩⟩
private theorem rkmw_slide_shift (dNat remSl : ℕ) : ∀ (hbPre hbSl vecSl curSl : List ℤ),
      rkmZeroPrefix 1 curSl →
      muxFastSlideLoopAux dNat (hbPre.length + remSl) (Int.ofNat 0) (hbPre ++ hbSl)
        (rkmPrependZeros hbPre.length vecSl) (rkmPrependZeros hbPre.length curSl) =
      rkmPrependZeros hbPre.length (muxFastSlideLoopAux dNat remSl (Int.ofNat 0) hbSl vecSl curSl)
  | [], _, _, _, _ => by simp [rkmPrependZeros]
  | b :: hbPre, hbSl, vecSl, curSl, hc1 => by
    simp only [List.length_cons, List.cons_append]
    rw [show hbPre.length + 1 + remSl = (hbPre.length + remSl) + 1 by omega,
      rkmw_prependZeros_cons, rkmw_prependZeros_cons, rkmw_prependZeros_cons]
    have hcn : (match rkmPrependZeros hbPre.length curSl with
        | cn :: _ => cn | [] => Int.ofNat 0) = Int.ofNat 0 := by
      cases hbPre with
      | nil =>
        simp only [List.length_nil, rkmPrependZeros]
        rcases curSl with _ | ⟨cn, _⟩
        · rfl
        · exact hc1.1
      | cons _ _ => rw [List.length_cons, rkmw_prependZeros_cons]; rfl
    conv_lhs => unfold muxFastSlideLoopAux
    change highdStrictConsInt
        (muxRawIntAdd (Int.ofNat 0) (muxRawIntTdivNat (muxRawIntSub (Int.ofNat 0) (muxRawIntMul b
                (match rkmPrependZeros hbPre.length curSl with
                  | cn :: _ => cn | [] => Int.ofNat 0))) dNat))
        (muxFastSlideLoopAux dNat (hbPre.length + remSl) (primIntMul b (Int.ofNat 0))
          (hbPre ++ hbSl) (rkmPrependZeros hbPre.length vecSl)
          (rkmPrependZeros hbPre.length curSl)) = _
    rw [hcn, rkmw_rawMul_zero, rkmw_primMul_zero, rkmw_zero_q, rkmw_strictConsInt_eq,
      rkmw_slide_shift dNat remSl hbPre hbSl vecSl curSl hc1]
    rfl
private theorem rkmw_stage_shift {deg sLo remMax k : ℕ} {hb hbSl vecSl curSl : List ℤ}
    (hhb : hb = hb.take sLo ++ hbSl) (hhb_take : (hb.take sLo).length = sLo)
    (hv : rkmZeroPrefix k vecSl) (hc : rkmZeroPrefix (k + 1) curSl) :
    rkmPrependZeros sLo (muxFastHornerStage deg remMax hbSl vecSl curSl) =
      muxFastHornerStage deg (sLo + remMax) hb
        (rkmPrependZeros sLo vecSl) (rkmPrependZeros sLo curSl) ∧
    rkmZeroPrefix k (muxFastHornerStage deg remMax hbSl vecSl curSl) := by
  unfold muxFastHornerStage
  simp only [rkmb_forceNat_eq, rkmb_natMin_eq, rkmw_altIntLen_eq, rkmw_prependZeros_length]
  have hmin : min (sLo + remMax) (Nat.add (sLo + curSl.length) 1) =
      sLo + min remMax (Nat.add curSl.length 1) := by simp only [Nat.add_eq]; omega
  rw [hmin]
  have hc1 : rkmZeroPrefix 1 curSl := rkmw_zeroPrefix_mono (Nat.succ_le_succ (Nat.zero_le k)) hc
  refine ⟨?_, rkmw_zeroPrefix_slide _ _ k hbSl vecSl curSl hv hc⟩
  conv_rhs => rw [hhb]
  have hsh := rkmw_slide_shift (Nat.mul deg wdScale) (min remMax (Nat.add curSl.length 1))
    (hb.take sLo) hbSl vecSl curSl hc1
  simpa only [hhb_take] using hsh.symm
private theorem rkmw_fastIter1_eq (maxLen : ℕ) (hb vec : List ℤ) :
    muxFastIterFullT16 1 maxLen hb vec = muxFastHornerT16Step maxLen hb vec := by
  conv_lhs => unfold muxFastIterFullT16
  rw [rkmb_forceList_eq]; rfl
private theorem rkmw_step_halo16_eq {d off : ℕ} {hb xs : List ℤ}
    (hhb_len : hb.length = d) (hoff_le : off ≤ d + 1) :
    rkmPrependZeros (Nat.sub off 16)
      (muxUltraIterFullT16Rkm 1 (Nat.sub (Nat.add d 1) (Nat.sub off 16))
        (altIntLen (rkmPrependZeros (Nat.sub off (Nat.sub off 16)) xs))
        (rkmDropInts (Nat.sub off 16) hb) (rkmPrependZeros (Nat.sub off (Nat.sub off 16)) xs)) =
      muxFastIterFullT16 1 (d + 1) hb (rkmPrependZeros off xs) := by
  set sLo := Nat.sub off 16; set padL := Nat.sub off sLo
  set remMax := Nat.sub (Nat.add d 1) sLo; set hbSl := rkmDropInts sLo hb
  set vecSl := rkmPrependZeros padL xs
  rw [rkmw_ultraIter_eq, rkmw_fastIter1_eq, rkmw_fastIter1_eq]
  by_cases hs0 : sLo = 0
  · have hpad : padL = off := (by dsimp [padL]; omega)
    have hrem : remMax = d + 1 := (by dsimp [remMax]; rw [hs0]; rfl)
    have hhbSl : hbSl = hb := (by dsimp [hbSl]; rw [hs0]; rfl)
    have hvecSl : vecSl = rkmPrependZeros off xs := (by dsimp [vecSl]; rw [hpad])
    rw [hs0, hrem, hhbSl, hvecSl]; rfl
  · have hpad16 : padL = 16 := (by dsimp [padL, sLo] at hs0 ⊢; omega)
    have hrem_eq : sLo + remMax = d + 1 := (by dsimp [remMax, sLo]; omega)
    have hvec_full : rkmPrependZeros sLo vecSl = rkmPrependZeros off xs := by
      dsimp [vecSl]; rw [← rkmw_prependZeros_add, show sLo + padL = off by
        dsimp [padL, sLo] at hs0 ⊢; omega]
    have hhb_split : hb = hb.take sLo ++ hbSl := by
      dsimp [hbSl]; rw [rkmw_dropInts_eq, List.take_append_drop]
    have hhb_take : (hb.take sLo).length = sLo := (by rw [List.length_take]; dsimp [sLo]; omega)
    have hv16 : rkmZeroPrefix 16 vecSl := by
      dsimp [vecSl]; rw [hpad16]; exact rkmw_zeroPrefix_prepend 16 xs
    rw [← hrem_eq, ← hvec_full]; unfold muxFastHornerT16Step; simp only [rkmb_forceList_eq]
    have mk (deg k : ℕ) (hk : k ≤ 16) (cur : List ℤ) (hc : rkmZeroPrefix (k + 1) cur) :=
      rkmw_stage_shift (deg := deg) (hbSl := hbSl) (vecSl := vecSl) (remMax := remMax)
        hhb_split hhb_take (rkmw_zeroPrefix_mono hk hv16) hc
    obtain ⟨e15, z15⟩ := mk 16 15 (by omega) vecSl hv16
    obtain ⟨e14, z14⟩ := mk 15 14 (by omega) _ z15; obtain ⟨e13, z13⟩ := mk 14 13 (by omega) _ z14
    obtain ⟨e12, z12⟩ := mk 13 12 (by omega) _ z13; obtain ⟨e11, z11⟩ := mk 12 11 (by omega) _ z12
    obtain ⟨e10, z10⟩ := mk 11 10 (by omega) _ z11; obtain ⟨e9, z9⟩ := mk 10 9 (by omega) _ z10
    obtain ⟨e8, z8⟩ := mk 9 8 (by omega) _ z9; obtain ⟨e7, z7⟩ := mk 8 7 (by omega) _ z8
    obtain ⟨e6, z6⟩ := mk 7 6 (by omega) _ z7; obtain ⟨e5, z5⟩ := mk 6 5 (by omega) _ z6
    obtain ⟨e4, z4⟩ := mk 5 4 (by omega) _ z5; obtain ⟨e3, z3⟩ := mk 4 3 (by omega) _ z4
    obtain ⟨e2, z2⟩ := mk 3 2 (by omega) _ z3; obtain ⟨e1, z1⟩ := mk 2 1 (by omega) _ z2
    obtain ⟨e0, _⟩ := mk 1 0 (by omega) _ z1
    rw [← e15, ← e14, ← e13, ← e12, ← e11, ← e10, ← e9, ← e8, ← e7, ← e6, ← e5, ← e4,
      ← e3, ← e2, ← e1, ← e0]
/- ## Section 3: Windowed Multi-Step Soundness & Chaining -/
private theorem rkmw_len_slideLoop (dNat : ℕ) : ∀ (rem : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      (muxFastSlideLoopAux dNat rem prev hb vec cur).length = rem
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    rcases hb with _ | ⟨b, hbR⟩
    · simp only [muxFastSlideLoopAux, rkmw_strictConsInt_eq, List.length_cons,
        rkmw_len_slideLoop dNat rem]
    · rcases vec with _ | ⟨v, vT⟩ <;> rcases cur with _ | ⟨c0, cT⟩ <;>
        simp only [muxFastSlideLoopAux, rkmw_strictConsInt_eq, List.length_cons,
          rkmw_len_slideLoop dNat rem]
private theorem rkmw_len_fastIter1 (maxLen : ℕ) (hb vec : List ℤ) :
    (muxFastIterFullT16 1 maxLen hb vec).length ≤ maxLen := by
  rw [rkmw_fastIter1_eq]; unfold muxFastHornerT16Step; simp only [rkmb_forceList_eq]
  unfold muxFastHornerStage; simp only [rkmb_forceNat_eq, rkmb_natMin_eq, rkmw_len_slideLoop]
  exact Nat.min_le_left _ _
private theorem rkmw_iter_sound_aux :
    ∀ (steps thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ), hb.length = d →
      off + xs.length ≤ d + 1 →
      dropAcc ≤ (muxWinIterT16 steps thr d hb off xs dropAcc).2.2 ∧
      (muxWinIterT16 steps thr d hb off xs dropAcc).1 +
        (muxWinIterT16 steps thr d hb off xs dropAcc).2.1.length ≤ d + 1 ∧
      ∀ (_hd : d ≤ 1024) (_hG : ∀ u, vecNorm (rkmPtGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u),
        vecNorm (rkmListToOrbVec d
          (rkmPrependZeros (muxWinIterT16 steps thr d hb off xs dropAcc).1
            (muxWinIterT16 steps thr d hb off xs dropAcc).2.1) -
          ((taylor16OfMat (rkmPtGenMat d hb)) ^ steps) *ᵥ
            rkmListToOrbVec d (rkmPrependZeros off xs)) ≤
          (((297 / 2) * (steps : ℝ) +
            (((muxWinIterT16 steps thr d hb off xs dropAcc).2.2 - dropAcc : ℕ) : ℝ))) / wdScaleR
  | 0, _, _, _, _, _, _, _, hlen => by
    dsimp only [muxWinIterT16]
    exact ⟨le_rfl, hlen, fun _ _ ↦ by simp [pow_zero, Matrix.one_mulVec, vecNorm_zero]⟩
  | k + 1, thr, d, hb, off, xs, dropAcc, hhb, hlen => by
    unfold muxWinIterT16
    rcases hst : muxWinStepT16 thr d hb off xs dropAcc with ⟨off1, xs1, drop1⟩
    unfold muxWinStepT16 at hst; simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at hst
    set sLo := Nat.sub off 16; set padL := Nat.sub off sLo
    set remMax := Nat.sub (Nat.add d 1) sLo; set hbSl := rkmDropInts sLo hb
    set vecSl := rkmPrependZeros padL xs
    set rawSl := muxUltraIterFullT16Rkm 1 remMax (altIntLen vecSl) hbSl vecSl
    have htrim := rkmw_trimWin_sound thr sLo rawSl dropAcc; rw [hst] at htrim; dsimp only at htrim
    have hhalo : rkmPrependZeros sLo rawSl =
        muxFastIterFullT16 1 (d + 1) hb (rkmPrependZeros off xs) :=
      rkmw_step_halo16_eq (xs := xs) hhb (by omega : off ≤ d + 1)
    have hfull_in_len : (rkmPrependZeros off xs).length ≤ d + 1 := by
      rw [rkmw_prependZeros_length]; exact hlen
    have hraw_len : sLo + rawSl.length ≤ d + 1 := by
      rw [← rkmw_prependZeros_length, hhalo]
      exact rkmw_len_fastIter1 (d + 1) hb (rkmPrependZeros off xs)
    have hl1_le : off1 + xs1.length ≤ d + 1 := htrim.2.1.trans hraw_len
    have ih := rkmw_iter_sound_aux k thr d hb off1 xs1 drop1 hhb hl1_le
    dsimp only; refine ⟨htrim.1.trans ih.1, ih.2.1, fun hd hG ↦ ?_⟩
    set B := taylor16OfMat (rkmPtGenMat d hb)
    have h1 := (rkmIterFullT16_approx hd hhb.le hG 1 (rkmPrependZeros off xs) hfull_in_len).2
    rw [pow_one, ← hhalo] at h1
    have hskew : (rkmPtGenMat d hb)ᵀ = -rkmPtGenMat d hb := tridiagSkewMat_transpose d _
    have hBk_contr (w : Fin (d + 1) → ℝ) : vecNorm ((B ^ k) *ᵥ w) ≤ vecNorm w := by
      have hB1 (u : Fin (d + 1) → ℝ) : vecNorm (B *ᵥ u) ≤ 1 * vecNorm u := by
        rw [one_mul]; exact vecNorm_taylor16OfMat_mulVec_le hskew hG u
      simpa using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) hB1 k w
    have htrim_vec : vecNorm (rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
        rkmListToOrbVec d (rkmPrependZeros sLo rawSl)) ≤
        ((drop1 - dropAcc : ℕ) : ℝ) / wdScaleR := by
      have hB_pos : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; positivity)
      exact (rkmw_vecNorm_orbVec_sub_le d _ _).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast htrim.2.2) hB_pos.le)
    have hstep1 : vecNorm (rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
        B *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs)) ≤
        ((297 / 2) + ((drop1 - dropAcc : ℕ) : ℝ)) / wdScaleR := by
      have hsp : rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
          B *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs) =
          (rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
            rkmListToOrbVec d (rkmPrependZeros sLo rawSl)) +
          (rkmListToOrbVec d (rkmPrependZeros sLo rawSl) -
            B *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs)) :=
        (sub_add_sub_cancel _ _ _).symm
      rw [hsp]
      have htr := vecNorm_add_le (rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
          rkmListToOrbVec d (rkmPrependZeros sLo rawSl))
        (rkmListToOrbVec d (rkmPrependZeros sLo rawSl) -
          B *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs))
      have hadd_div : ((drop1 - dropAcc : ℕ) : ℝ) / wdScaleR + (297 / 2) / wdScaleR =
          ((297 / 2) + ((drop1 - dropAcc : ℕ) : ℝ)) / wdScaleR := by ring
      linarith [htr, htrim_vec, h1, hadd_div]
    have ih_bd := ih.2.2 hd hG
    set outV := rkmListToOrbVec d (rkmPrependZeros (muxWinIterT16 k thr d hb off1 xs1 drop1).1
        (muxWinIterT16 k thr d hb off1 xs1 drop1).2.1)
    have hsplit : outV - (B ^ (k + 1)) *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs) =
        (outV - (B ^ k) *ᵥ rkmListToOrbVec d (rkmPrependZeros off1 xs1)) +
        (B ^ k) *ᵥ (rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
          B *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs)) := by
      rw [pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    have htr_k := vecNorm_add_le (outV - (B ^ k) *ᵥ rkmListToOrbVec d (rkmPrependZeros off1 xs1))
      ((B ^ k) *ᵥ (rkmListToOrbVec d (rkmPrependZeros off1 xs1) -
        B *ᵥ rkmListToOrbVec d (rkmPrependZeros off xs)))
    have hBk_le := (hBk_contr _).trans hstep1
    have hd_sum : ((muxWinIterT16 k thr d hb off1 xs1 drop1).2.2 - drop1) + (drop1 - dropAcc) =
        (muxWinIterT16 k thr d hb off1 xs1 drop1).2.2 - dropAcc := by
      have h_t1 := htrim.1; have h_ih1 := ih.1; omega
    have hd_cast : (((muxWinIterT16 k thr d hb off1 xs1 drop1).2.2 - drop1 : ℕ) : ℝ) +
        ((drop1 - dropAcc : ℕ) : ℝ) =
        (((muxWinIterT16 k thr d hb off1 xs1 drop1).2.2 - dropAcc : ℕ) : ℝ) := by
      exact_mod_cast hd_sum
    have hgoal_eq : (((297 / 2) * (k : ℝ) +
          (((muxWinIterT16 k thr d hb off1 xs1 drop1).2.2 - drop1 : ℕ) : ℝ))) / wdScaleR +
        ((297 / 2) + ((drop1 - dropAcc : ℕ) : ℝ)) / wdScaleR =
        (((297 / 2) * ((k + 1 : ℕ) : ℝ) +
          (((muxWinIterT16 k thr d hb off1 xs1 drop1).2.2 - dropAcc : ℕ) : ℝ))) / wdScaleR := by
      rw [← add_div]; congr 1; push_cast; linarith [hd_cast]
    dsimp only [outV] at hsplit htr_k; rw [hsplit]; linarith [htr_k, ih_bd, hBk_le, hgoal_eq]
/-- Soundness of one `muxWinIterT16HiChk` `decide +kernel` chunk certificate. -/
theorem muxWinIterT16HiChk_sound {steps thr tag d : ℕ} {hb : List ℤ}
    {offIn : ℕ} {xsIn : List ℤ} {offOut : ℕ} {xsOut : List ℤ} {dropExp : ℕ}
    (h : muxWinIterT16HiChk steps thr tag d hb offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d hb offIn xsIn offOut xsOut dropExp := by
  unfold muxWinIterT16HiChk at h; simp only [rkmb_forceList_eq] at h
  rcases hres : muxWinIterT16 steps thr d hb offIn xsIn 0 with ⟨oRes, xRes, dRes⟩
  rw [hres] at h; simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, muxIntListEq_eq_true] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  intro hhb hlen; have hsnd := rkmw_iter_sound_aux steps thr d hb offIn xsIn 0 hhb hlen
  rw [hres] at hsnd
  exact ⟨hsnd.2.1, fun hd hG ↦ by simpa using hsnd.2.2 hd hG⟩
/-- Transitive chaining of two windowed `T_16` chunk certificates across part boundaries. -/
theorem rkmChainWinIterT16 {k1 k2 kTot d : ℕ} {hb1 hb2 : List ℤ}
    {o0 : ℕ} {x0 : List ℤ} {o1 o1' : ℕ} {x1 x1' : List ℤ} {o2 : ℕ} {x2 : List ℤ} {d1 d2 dTot : ℕ}
    (hk : k1 + k2 = kTot) (hdrop : d1 + d2 = dTot)
    (hhb : muxIntListEq hb1 hb2 = true) (ho : o1 = o1') (hx : muxIntListEq x1 x1' = true)
    (h1 : RkmWinIterSound k1 d hb1 o0 x0 o1 x1 d1)
    (h2 : RkmWinIterSound k2 d hb2 o1' x1' o2 x2 d2) :
    RkmWinIterSound kTot d hb1 o0 x0 o2 x2 dTot := by
  subst hk; subst hdrop; subst ho
  rw [← muxIntListEq_eq_true.mp hhb, ← muxIntListEq_eq_true.mp hx] at h2; intro hhb_len h0_len
  obtain ⟨h1_len, h1_bd⟩ := h1 hhb_len h0_len; obtain ⟨h2_len, h2_bd⟩ := h2 hhb_len h1_len
  refine ⟨h2_len, fun hd hG ↦ ?_⟩
  set B := taylor16OfMat (rkmPtGenMat d hb1)
  have hskew : (rkmPtGenMat d hb1)ᵀ = -rkmPtGenMat d hb1 := tridiagSkewMat_transpose d _
  have hBk2_contr (w : Fin (d + 1) → ℝ) : vecNorm ((B ^ k2) *ᵥ w) ≤ vecNorm w := by
    have hB1 (u : Fin (d + 1) → ℝ) : vecNorm (B *ᵥ u) ≤ 1 * vecNorm u := by
      rw [one_mul]; exact vecNorm_taylor16OfMat_mulVec_le hskew hG u
    simpa using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) hB1 k2 w
  set v0 := rkmListToOrbVec d (rkmPrependZeros o0 x0)
  set v1 := rkmListToOrbVec d (rkmPrependZeros o1 x1)
  set v2 := rkmListToOrbVec d (rkmPrependZeros o2 x2)
  have hsp : v2 - (B ^ (k1 + k2)) *ᵥ v0 =
      (v2 - (B ^ k2) *ᵥ v1) + (B ^ k2) *ᵥ (v1 - (B ^ k1) *ᵥ v0) := by
    rw [add_comm k1 k2, pow_add, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [hsp]; have htr := vecNorm_add_le (v2 - (B ^ k2) *ᵥ v1) ((B ^ k2) *ᵥ (v1 - (B ^ k1) *ᵥ v0))
  have hb1 := (hBk2_contr _).trans (h1_bd hd hG); have hb2 := h2_bd hd hG
  have hsum : (((297 / 2) * (k2 : ℝ) + (d2 : ℝ))) / wdScaleR +
      (((297 / 2) * (k1 : ℝ) + (d1 : ℝ))) / wdScaleR =
      (((297 / 2) * ((k1 + k2 : ℕ) : ℝ) + ((d1 + d2 : ℕ) : ℝ))) / wdScaleR := by
    rw [← add_div]; congr 1; push_cast; ring
  linarith [htr, hb1, hb2, hsum]
/-- Packages a chained `RkmWinIterSound` proof into a segment walk witness
  `RkmWinSegWalkSound`. -/
theorem rkmWinSegWalkSound_of_iter {nSub d : ℕ} {hb : List ℤ}
    {offIn : ℕ} {xsIn : List ℤ} {offOut : ℕ} {xsOut : List ℤ} {dropSeg : ℕ}
    (hchk : Bool.and (Nat.beq (altIntLen hb) d)
      (Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1)) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, rkmw_nat_ble_eq_true,
    rkmw_altIntLen_eq, Nat.add_eq] at hchk
  obtain ⟨hout_len, hbd⟩ := hiter hchk.1 hchk.2; exact ⟨hchk.1, hchk.2, hout_len, hbd⟩
/- ## Section 4: Shared Fixed-Point Coupling & Substep Bounds -/
theorem rkmw_ceil_div_mul_ge (n d : ℕ) (hd : 0 < d) : n ≤ (((d - 1) + n) / d) * d := by
  have h := Nat.lt_mul_div_succ ((d - 1) + n) hd
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d] at h; omega
theorem rkmw_mulCeil15_ge (a b : ℕ) :
    ((a : ℝ) / wdScaleR) * ((b : ℝ) / wdScaleR) ≤ (highdMulCeil15 a b : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; positivity)
  have hnat : a * b ≤ highdMulCeil15 a b * wdScale := by
    have h := rkmw_ceil_div_mul_ge (a * b) wdScale (by unfold wdScale; positivity)
    have hsub : wdScale - 1 = 999999999999999 := (by unfold wdScale; rfl); rw [hsub] at h; exact h
  have hreal : (a : ℝ) * (b : ℝ) ≤ (highdMulCeil15 a b : ℝ) * wdScaleR := by
    unfold wdScaleR; exact_mod_cast hnat
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hB hB) hB]
  exact (mul_le_mul_of_nonneg_right hreal hB.le).trans_eq (by ring)
private theorem rkmw_powCeilLoop_ge (x : ℕ) :
    ∀ (k acc : ℕ) {p : ℝ}, 0 ≤ p → p ≤ (acc : ℝ) / wdScaleR →
      p * ((x : ℝ) / wdScaleR) ^ k ≤ (highdPowCeilLoop k acc x : ℝ) / wdScaleR := by
  intro k; induction k with
  | zero => intro acc p _ hacc; dsimp only [highdPowCeilLoop]; simpa using hacc
  | succ k ih =>
    intro acc p hp0 hacc; dsimp only [highdPowCeilLoop]
    have hx0 : 0 ≤ (x : ℝ) / wdScaleR := (by unfold wdScaleR wdScale; positivity)
    have hnext : p * ((x : ℝ) / wdScaleR) ≤ (highdMulCeil15 acc x : ℝ) / wdScaleR :=
      (mul_le_mul_of_nonneg_right hacc hx0).trans (rkmw_mulCeil15_ge acc x)
    simpa only [pow_succ', ← mul_assoc] using ih (highdMulCeil15 acc x) (mul_nonneg hp0 hx0) hnext
theorem rkmw_pow17Ceil15_ge (x : ℕ) :
    ((x : ℝ) / wdScaleR) ^ 17 ≤ (altPow17Ceil15 x : ℝ) / wdScaleR := by
  have hx0 : 0 ≤ (x : ℝ) / wdScaleR := (by unfold wdScaleR wdScale; positivity)
  dsimp only [altPow17Ceil15]; simpa only [pow_succ'] using rkmw_powCeilLoop_ge x 16 x hx0 le_rfl
theorem rkmw_maxBHiFrom_ge (m r : ℕ) :
    ∀ (rem w j : ℕ), j < rem → (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤
        altMaxBHiFrom m r w rem
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, j, hj => by
    unfold altMaxBHiFrom altMaxBHiFromAux; simp only [rkmb_forceNat_eq]
    set rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    set bHi := (altIsqrt15 rad).2; set rMax := altMaxBHiFromAux m r rem (Nat.add w 1)
    rcases j with _ | j'
    · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = rad := by
        change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
          4 * (w + 1) * (m - w) * (r - w); simp
      rw [hrad]
      cases hlt : primNatBlt rMax bHi
      · simp only [cond]; exact rkmw_primNatBlt_eq_false.mp hlt
      · simp only [cond]; exact le_rfl
    · have ih := rkmw_maxBHiFrom_ge m r rem (w + 1) j' (by omega)
      rw [show w + 1 + j' = w + (j' + 1) by omega] at ih
      cases hlt : primNatBlt rMax bHi
      · simp only [cond]; exact ih
      · simp only [cond]; exact ih.trans (rkmw_primNatBlt_eq_true.mp hlt).le
theorem rkmw_checkHbTight_sound (m r : ℕ) : ∀ (rem w : ℕ), altCheckHbTight m r w rem = true →
      ∀ j < rem, (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤
          (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1 + 1
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, hchk, j, hj => by
    unfold altCheckHbTight altCheckHbTightAux at hchk; dsimp only at hchk
    generalize hp : altIsqrt15 (Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1))
      (Nat.sub m w)) (Nat.sub r w)) = p at hchk
    cases hble : Nat.ble p.2 (Nat.add p.1 1) with
    | false => rw [hble, Bool.cond_false] at hchk; exact Bool.noConfusion hchk
    | true =>
      rw [hble, Bool.cond_true] at hchk
      rcases j with _ | j'
      · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w) := by
          change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            4 * (w + 1) * (m - w) * (r - w); simp
        rw [hrad, hp]; exact rkmw_nat_ble_eq_true.mp hble
      · simpa [show w + 1 + j' = w + (j' + 1) by omega] using
          rkmw_checkHbTight_sound m r rem (w + 1) hchk j' (by omega)
theorem rkmw_buildHbFrom_length (m r hPt : ℕ) :
    ∀ (rem w : ℕ), (altBuildHbFrom m r hPt w rem).length = rem
  | 0, _ => rfl
  | rem + 1, w => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    exact congrArg Nat.succ (rkmw_buildHbFrom_length m r hPt rem (w + 1))
theorem rkmw_buildHbFrom_getD (m r hPt : ℕ) :
    ∀ (rem w j : ℕ), j < rem → (altBuildHbFrom m r hPt w rem).getD j 0 =
        (((hPt * (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1) /
          wdScale : ℕ) : ℤ)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, 0, _ => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    change (((hPt * (altIsqrt15 (4 * (w + 1) * (m - w) * (r - w))).1) / wdScale : ℕ) : ℤ) = _
    simp
  | rem + 1, w, j + 1, hj => by
    dsimp only [altBuildHbFrom, altBuildHbFromAux]
    rw [strictConsInt_eq, List.getD_cons_succ, show Nat.add w 1 = w + 1 from rfl]
    have ih := rkmw_buildHbFrom_getD m r hPt rem (w + 1) j (by omega)
    dsimp only [altBuildHbFrom] at ih; simpa [show w + 1 + j = w + (j + 1) by omega] using ih
theorem rkmw_substep_bounds {n tau9 nSub : ℕ}
    (hn : altN0 ≤ n) (htau : tau9 ≤ 4000000000) (hnsub1 : 1 ≤ nSub) (hnsub : nSub ≤ 16384) :
    let q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000); let hPt := (tau9 * 1000000) / nSub
    0 ≤ (q : ℝ) / √(2 ^ n : ℝ) ∧ (q : ℝ) / √(2 ^ n : ℝ) ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR ∧
      |(q : ℝ) / √(2 ^ n : ℝ) - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
  intro q hPt; set N := 2 ^ n
  have hN_cast : (2 : ℝ) ^ n = (N : ℝ) := (by dsimp [N]; norm_cast); rw [hN_cast]
  have h200 : 200 ≤ n := (by unfold altN0 at hn; omega)
  have hN_ge : (2 : ℝ) ^ 200 ≤ (N : ℝ) := by
    dsimp [N]; rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) h200
  have hsqrtN_ge : (2 : ℝ) ^ 100 ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : 0 < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  have hnsub_pos : (0 : ℝ) < (nSub : ℝ) := (by exact_mod_cast hnsub1)
  have hB : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have hB_pos : (0 : ℝ) < wdScaleR := (by rw [hB]; positivity)
  have hhPt_lo : (hPt : ℝ) / wdScaleR ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hR : (hPt : ℝ) * (nSub : ℝ) ≤ (tau9 : ℝ) * 1000000 := by
      exact_mod_cast Nat.div_mul_le_self (tau9 * 1000000) nSub
    rw [hB, div_le_div_iff₀ (by norm_num) (by positivity), ← mul_assoc]; linarith
  have hhPt_hi : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) ≤ ((hPt + 1 : ℕ) : ℝ) / wdScaleR := by
    have hnat : tau9 * 1000000 < (hPt + 1) * nSub :=
      (Nat.lt_mul_div_succ _ (by omega : 0 < nSub)).trans_eq (Nat.mul_comm _ _)
    have hR : (tau9 : ℝ) * 1000000 ≤ ((hPt + 1 : ℕ) : ℝ) * (nSub : ℝ) := by exact_mod_cast hnat.le
    rw [hB, div_le_div_iff₀ (by positivity) (by norm_num), ← mul_assoc]; linarith
  have hq_hi : (q : ℝ) / √(N : ℝ) ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hR : ((nSub : ℝ) * 1000000000) * (q : ℝ) ≤ (tau9 : ℝ) * (Nat.sqrt N : ℝ) := by
      exact_mod_cast Nat.mul_div_le (tau9 * Nat.sqrt N) (nSub * 1000000000)
    have hsq : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) :=
      Real.le_sqrt_of_sq_le (by simpa [sq, Nat.cast_mul] using
        (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N))
    rw [div_le_div_iff₀ hsqrtN_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg tau9)]
  have hq_lo : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) - (q : ℝ) / √(N : ℝ) ≤ 1 / wdScaleR := by
    set S_N := Nat.sqrt N
    have hS_gt : √(N : ℝ) ≤ (S_N : ℝ) + 1 := by
      rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      have hlt := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N); push_cast at hlt; linarith
    have hdiv_lt : tau9 * S_N < (q + 1) * (nSub * 1000000000) :=
      (Nat.lt_mul_div_succ _ (by positivity : 0 < nSub * 1000000000)).trans_eq (Nat.mul_comm _ _)
    have hdivR : (tau9 : ℝ) * (S_N : ℝ) ≤ ((q : ℝ) + 1) * ((nSub : ℝ) * 1000000000) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hdiv_lt.le; push_cast at hc; linarith
    have htauR : (tau9 : ℝ) ≤ 4000000000 := (by exact_mod_cast htau)
    have hnsubR : (nSub : ℝ) ≤ 16384 := (by exact_mod_cast hnsub)
    have hgap : (tau9 : ℝ) * √(N : ℝ) - (q : ℝ) * ((nSub : ℝ) * 1000000000) ≤ 20384000000000 := by
      nlinarith [mul_le_mul_of_nonneg_left hS_gt (Nat.cast_nonneg tau9)]
    have h2 : (1 : ℝ) ≤ (nSub : ℝ) := (by exact_mod_cast hnsub1)
    have hbig : (20384000000000 : ℝ) * 1000000000000000 ≤
        ((nSub : ℝ) * 1000000000) * √(N : ℝ) := by
      have h1 : (20384000000000 : ℝ) * 1000000000000000 ≤ 1000000000 * (2 : ℝ) ^ 100 := by norm_num
      nlinarith
    rw [hB, div_sub_div _ _ (by positivity) hsqrtN_pos.ne',
      div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨div_nonneg (Nat.cast_nonneg q) hsqrtN_pos.le,
    hq_hi.trans (hhPt_hi.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast (by omega : hPt + 1 ≤ 2 + hPt)) hB_pos.le)), ?_⟩
  rw [abs_le]; refine ⟨by linarith [hhPt_lo, hq_lo], ?_⟩
  have h1 : ((hPt + 1 : ℕ) : ℝ) / wdScaleR - (hPt : ℝ) / wdScaleR = 1 / wdScaleR := by
    push_cast; ring
  linarith [hq_hi, hhPt_hi, h1]
end
end Sec_FindAllJohnsonRampKickMuxHiWinCore
section Sec_FindAllJohnsonRampKickMuxHiWin
@[expose] public section
open Real
open scoped Matrix NNRat NNReal ENNReal
/-- Zero-substep multi-segment stitcher substituting pre-certified `RkmWinSegWalk`
  witnesses. -/
def rkmEvalSegsWinWithWalks (m lTableMax r : ℕ) : List ℕ → List ℕ → List ℕ → List (List Bool) → List
    RkmWinSegWalk → ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tauRem, nsubRem, maskRem, walkRem, _, dEnd, accPad, vec =>
    match tauRem, nsubRem, maskRem, walkRem with
    | [], [], [], [] => (dEnd, accPad, vec)
    | _, _, _, _ => (0, 0, [])
  | lS :: lRest, tau9 :: tauRest, nSub :: nsubRest, mask :: maskRest, w :: wRest,
      lPrev, _, accPad, vec =>
    let mEff := Nat.mul lS m; let d := highdNatMin mEff r
    let g1 := Bool.or (primNatBlt lS 1) (Bool.or (primNatBlt lS lPrev) (Bool.or (primNatBlt
        lTableMax lS) (Bool.or (primNatBlt mEff 1) (Bool.or (primNatBlt 8192 mEff) (Bool.or
        (primNatBlt d 1) (Bool.or (Nat.beq tau9 0) (Bool.or (primNatBlt 4000000000 tau9) (Bool.or
        (Nat.beq nSub 0) (Bool.or (primNatBlt 16384 nSub) (primNatBlt (Nat.add d 1) (rkmBoolListLen
        mask)))))))))))
    match g1 with
    | true => (0, 0, [])
    | false =>
      HighDForce.withForcedNat (Nat.div (Nat.mul tau9 1000000) nSub) fun hPt =>
      match primNatBlt hPt 1 with
      | true => (0, 0, [])
      | false =>
        HighDForce.withForcedNat (altMaxBHiFrom mEff r 0 d) fun maxBHi15 =>
        HighDForce.withForcedNat (Nat.mul 2 maxBHi15) fun bCapHi15 =>
        HighDForce.withForcedNat (highdMulCeil15 (Nat.add 2 hPt) bCapHi15) fun hgHi15 =>
        match Bool.or (primNatBlt 1500000000000000 hgHi15)
            (Bool.not (altCheckHbTight mEff r 0 d)) with
        | true => (0, 0, [])
        | false =>
          let hgPow := altPow17Ceil15 hgHi15
          let truncPad15 := Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
          let bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
          let segPad := Nat.add (Nat.add truncPad15 256) (Nat.mul nSub (Nat.add 256 (Nat.mul 10
              bCapCeil)))
          HighDForce.withForcedNat (Nat.add accPad (Nat.add segPad w.dropSeg)) fun nextPad =>
          match Bool.or (Nat.beq nextPad 0) (primNatBlt 100000000000000 nextPad) with
          | true => (0, 0, [])
          | false =>
            HighDForce.withForcedList (altBuildHbFrom mEff r hPt 0 d) fun hbPt =>
            HighDForce.withForcedList (rkmPrependZeros w.offIn w.xsIn) fun vInExp =>
            let eqOk := Bool.and (Nat.beq d w.d) (Bool.and (muxIntListEq hbPt w.hbExp) (muxIntListEq
                (altPadRightInts (Nat.add d 1) vec) (altPadRightInts (Nat.add d 1) vInExp)))
            match eqOk with
            | false => (0, 0, [])
            | true =>
              HighDForce.withForcedList (rkmPrependZeros w.offOut w.xsOut) fun vWalk =>
              HighDForce.withForcedList (rkmApplyMaskBits mask vWalk) fun vNext =>
              rkmEvalSegsWinWithWalks m lTableMax r lRest tauRest nsubRest maskRest wRest
                lS d nextPad vNext
  | _, _, _, _, _, _, _, _, _ => (0, 0, [])
/-- Evaluates post-trajectory `rowLo12` from pre-certified windowed segment walks `walks`. -/
def rkmEvalT16FromWinWalks (m lTableMax r : ℕ) (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List
    Bool)) (walks : List RkmWinSegWalk) : List ℕ := let nSegs := altListLen lSegs
  match Bool.or (Nat.beq nSegs 0)
      (Bool.or (primNatBlt 8 nSegs)
        (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))) with
  | true => []
  | false =>
    match rkmEvalSegsWinWithWalks m lTableMax r lSegs tauSegs nsubSegs masks walks
        1 0 0 [Int.ofNat wdScale] with
    | (dEnd, accPad, vecFinal) =>
      match Bool.or (Nat.beq dEnd 0) (Nat.beq accPad 0) with
      | true => []
      | false =>
        match altPadRightInts (Nat.add dEnd 1) vecFinal with
        | [] => []
        | _ :: tail => altVecTailToLo12 accPad tail
/-- Boolean `O(d)` row stitcher checking `rkmEvalT16FromWinWalks... = rowOut`. -/
def rkmCheckRowFromWinWalks (m lTableMax r : ℕ) (lSegs tauSegs nsubSegs : List ℕ) (masks : List
    (List Bool)) (walks : List RkmWinSegWalk) (rowOut : List ℕ) : Bool :=
  match primNatBlt (altListLen rowOut) 1 with
  | true => false
  | false =>
      muxNatListEq (rkmEvalT16FromWinWalks m lTableMax r lSegs tauSegs nsubSegs masks walks) rowOut
/-- Quantum hit-probability soundness of one `RampKickAnchor` (unwindowed or windowed). -/
abbrev RkmAnchorHitSound (m : ℕ) (a : RampKickAnchor) : Prop := ∀ {n : ℕ}, altN0 ≤ n → ∀ {R : Finset
    (Fin (2 ^ n))}, R.card = a.rAct → ∀ w ∈ Finset.Icc 1 (min (rkmLastNat 0 a.lSegs * m) a.rAct),
    ((a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000) ≤ symHitProb R (rkmEvalSegs R (a.lSegs.headD 1)
    (rkmSegOps n m a.rAct (a.lSegs.headD 1) (a.tauSegs.headD 0) (a.nsubSegs.headD 0) (a.masks.headD
    [])) (rkmBuildTailSegs n m a.rAct a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail)
    (u0Vec (2 ^ n) (a.lSegs.headD 1 * m))) w
/-- Conjunction of `RkmAnchorHitSound` across an anchor table. -/
def RkmAnchorsHitSound (m _lTableMax : ℕ) : List RampKickAnchor → Prop
  | [] => True
  | a :: rest => RkmAnchorHitSound m a ∧ RkmAnchorsHitSound m _lTableMax rest
/-- Semantic validity bundle for a full `r = 0.. kMax` `RampKickMux` table with
  lower-bounded
  active anchor hit-probability certificates. -/
structure RampKickTableBoundValid (m kMax lTableMax : ℕ) (useColdR2 : Bool)
    (vPot : List ℕ) (anchors : List RampKickAnchor) : Prop where
  hm1 : 1 ≤ m
  hlMax1 : 1 ≤ lTableMax
  hlMax_hi : lTableMax * m ≤ 8192
  hkMax_lo : 2 ≤ kMax
  hkMax_hi : kMax ≤ 1024
  hv_len : vPot.length = kMax + 1
  hv0 : vPot.getD 0 0 = 0
  heig1 : checkEigStep m 1 (vPot.getD 1 0) (vPot.getD 0 0) = true
  hrows : ∀ s : ℕ, 2 ≤ s → s ≤ kMax →
    match rkmFindAnchor s anchors with
    | none =>
        (s = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨ checkEigStep m s
            (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
    | some a => a.rAct = s ∧ RkmAnchorHitSound m a ∧
        RampKickActiveValid m lTableMax s vPot a.lSegs a.tauSegs a.rowLo12
end
public section
local notation "qWR" => wdScaleR
local notation "qLO" => rkmListToOrbVec
local notation "qOE" => orbEmbedGen
local notation "qVN" => vecNorm
local notation "qPB" => primNatBlt
local notation "qDL" => div_le_div_of_nonneg_right
local notation "qEW" => rkmEvalSegsWinWithWalks
local notation "qDC" => dAltCoupling
local notation "qMR" => mul_le_mul_of_nonneg_right
local notation "qFN" => finVecNorm
local notation "qML" => mul_le_mul_of_nonneg_left
local notation "qEM" => evalMuxSymOps
local notation "qWN" => wdScale
local notation "qWS" => RkmWinSegWalk
local notation "qPZ" => rkmPrependZeros
local notation "qPR" => altPadRightInts
local notation "qMK" => rkmMaskKicksDown
local notation "qBT" => rkmBuildTailSegs
local notation "qCT" => rkmCheckTableAux
local notation "qEL" => rkmEvalSegsLoop
local notation "qAM" => rkmApplyMaskBits
open Real
open scoped Matrix NNRat NNReal ENNReal
private theorem ys (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem xf {α : Type*} {p : Prop} {uo : Decidable p} {a b : α} (h : p) :
    @ite α p uo a b = a := by cases uo with | isTrue _ => rfl | isFalse hn => exact absurd h hn
private theorem xg {α : Type*} {p : Prop} {uo : Decidable p} {a b : α} (h : ¬ p) :
    @ite α p uo a b = b := by cases uo with | isTrue hp => exact absurd hp h | isFalse _ => rfl
private theorem z8 {b : Bool} (h : b = true → False) : b = false := by cases b <;> simp_all
private theorem v5 {b : Bool} (h : b = false → False) : b = true := by cases b <;> simp_all
private theorem yk {α : Type*} : ∀ (xs : List α), (xs = [] → False) → ∃ a b, xs = a :: b
  | [], h => False.elim (h rfl)
  | a :: b, _ => ⟨a, b, rfl⟩
private theorem v6 {m zci r lP dE aP dO pO : ℕ} {ts ss : List ℕ} {ms : List (List Bool)} {ws : List
    qWS} {v vO : List ℤ} (h : qEW m zci r [] ts ss ms ws lP dE aP v = (dO, pO, vO)) (hd : dO ≠ 0) :
    ts = [] ∧ ss = [] ∧ ms = [] ∧ ws = [] ∧ dE = dO ∧ aP = pO ∧ v = vO := by
  match ts, ss, ms, ws, h with
  | [], [], [], [], rfl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | _ :: _, _, _, _, h | [], _ :: _, _, _, h | [], [], _ :: _, _, h | [], [], [], _ :: _, h =>
    exact False.elim (hd (Prod.mk.inj h).1.symm)
private theorem yz {m zci r l0 lP dP aP dO pO : ℕ} {ls ts ss : List ℕ} {ms : List (List Bool)} {ws :
    List qWS} {v vO : List ℤ} (h : qEW m zci r (l0 :: ls) ts ss ms ws lP dP aP v = (dO, pO, vO))
    (hd : dO ≠ 0) : ∃ t0 tr s0 sr m0 mr w0 wr, ts = t0 :: tr ∧ ss = s0 :: sr ∧ ms = m0 :: mr ∧ ws =
    w0 :: wr := by
  match ts, ss, ms, ws, h with
  | t0 :: tr, s0 :: sr, m0 :: mr, w0 :: wr, _ =>
    exact ⟨t0, tr, s0, sr, m0, mr, w0, wr, rfl, rfl, rfl, rfl⟩
  | [], _, _, _, h | _ :: _, [], _, _, h | _ :: _, _ :: _, [], _, h
  | _ :: _, _ :: _, _ :: _, [], h => exact False.elim (hd (Prod.mk.inj h).1.symm)
private theorem z6 : ∀ (xy : ℕ) (xs : List ℤ), xs.length ≤ xy → ∀ j : ℕ, (qPR xy xs).getD j 0 =
    xs.getD j 0
  | 0, [], _, _ => rfl
  | 0, _ :: _, uh, _ => absurd uh (Nat.not_le_of_gt (Nat.succ_pos _))
  | _ + 1, xs, _, 0 => by
      cases xs <;> dsimp only [altPadRightInts] <;> rw [rkmw_strictConsInt_eq] <;> rfl
  | rem + 1, [], _, j' + 1 => by
    dsimp only [altPadRightInts]; rw [rkmw_strictConsInt_eq]; exact z6 rem [] (Nat.zero_le _) j'
  | rem + 1, _ :: xs, uh, j' + 1 => by
    dsimp only [altPadRightInts]; rw [rkmw_strictConsInt_eq]; exact z6 rem xs (by simpa using uh) j'
/-- Single-segment windowed orbital `T_16` + `mask` bound from a certified `RkmWinSegWalk`. -/
theorem rkmSingleSegWinT16_bound {n z7 r tau9 nSub : ℕ} {mask : List Bool} {vec : List ℤ} {w :
    RkmWinSegWalk} (hn : altN0 ≤ n) (hm1 : 1 ≤ z7) (vj : z7 ≤ 8192) (hr2 : 2 ≤ r) (y0 : r ≤ 1024)
    (_ : 0 < tau9) (v7 : tau9 ≤ 4000000000) (zdg : 0 < nSub) (up : nSub ≤ 16384) (u2 :
    highdMulCeil15 (2 + (tau9 * 1000000) / nSub) (2 * altMaxBHiFrom z7 r 0 (min z7 r)) ≤
    1500000000000000) (zcj : altCheckHbTight z7 r 0 (min z7 r) = true) (uq : RkmWinSegWalkSound nSub
    w) (ur : w.d = min z7 r) (us : w.hbExp = altBuildHbFrom z7 r ((tau9 * 1000000) / nSub) 0 (min z7
    r)) (x4 : rkmListToOrbVec (min z7 r) (rkmPrependZeros w.offIn w.xsIn) = rkmListToOrbVec (min z7
    r) vec) {uIn : Fin (orbDim z7 r) → ℝ} (xk : vecNorm uIn ≤ 1) : let d := min z7 r
    let hPt := (tau9 * 1000000) / nSub; let zp := 2 * altMaxBHiFrom z7 r 0 d
    let y1 := highdMulCeil15 (2 + hPt) zp
    let zb := (299999999999999 + nSub * altPow17Ceil15 y1) / 300000000000000
    let z2 := (999999999999999 + zp) / qWN; let y4 := (zb + 256) + nSub * (256 + 10 * z2)
    let yg := qAM mask (qPZ w.offOut w.xsOut); let K := altStepCount tau9 nSub (2 ^ n)
    ∃ zu : Fin (orbDim z7 r) → ℝ, qVN zu ≤ 1 ∧ yg.length ≤ d + 1 ∧ qVN (rkmMaskSignVec d mask
        (((dAltStepOrbMat (2 ^ n) z7 r) ^ K) *ᵥ uIn) - zu) + qVN (zu - qLO d yg) ≤ qVN (uIn - qLO d
        vec) + (((y4 + w.dropSeg : ℕ) : ℝ) - 253) / qWR := by
  intro d hPt zp y1 zb z2 y4 yg K; set yt := altBuildHbFrom z7 r hPt 0 d
  obtain ⟨x5, vk, zbh, u3, xv, ut, x8, xl, uu⟩ : hPt = (tau9 * 1000000) / nSub ∧ zp = 2 *
      altMaxBHiFrom z7 r 0 d ∧ y1 = highdMulCeil15 (2 + hPt) zp ∧ zb = (299999999999999 + nSub *
      altPow17Ceil15 y1) / 300000000000000 ∧ z2 = (999999999999999 + zp) / qWN ∧ y4 = (zb + 256) +
      nSub * (256 + 10 * z2) ∧ yt = altBuildHbFrom z7 r hPt 0 d ∧ yg = qAM mask (qPZ w.offOut
      w.xsOut) ∧ K = altStepCount tau9 nSub (2 ^ n) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have u2' : y1 ≤ 1500000000000000 := u2; clear_value hPt zp y1 zb z2 y4 yt yg K
  have uv : qWR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have z4 : (0 : ℝ) < qWR := (by rw [uv]; positivity); have hn80 : 80000 ≤ n := hn
  have xz : (2 : ℝ) ^ 100 ≤ √(2 ^ n : ℝ) := Real.le_sqrt_of_sq_le ((by
      norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans (pow_le_pow_right₀ (by norm_num) (by
      omega : 200 ≤ n)))
  have ua : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) xz
  set q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
  have zdi : K = nSub * q := (by rw [uu]; rfl)
  have zce : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ) := by
    have h1 : (K : ℝ) ≤ ((tau9 : ℝ) / 1000000000) * √(2 ^ n : ℝ) := by
      rw [uu]; simpa [Nat.cast_pow, Nat.cast_ofNat] using altStepCount_le_tau_sqrt tau9 nSub (2 ^ n)
    exact h1.trans (qMR (by linarith [show (tau9 : ℝ) ≤ 4000000000 by exact_mod_cast v7]) ua.le)
  set η : ℝ := 1 / √(2 ^ n : ℝ); have hη_nn : 0 ≤ η := (by positivity)
  set G := dAltGenMat z7 r; set xm := ((dAltStepOrbMat (2 ^ n) z7 r) ^ K) *ᵥ uIn
  set vT8 := ((taylor8Mat η G) ^ K) *ᵥ uIn; set vl := ((taylor16Mat η G) ^ K) *ᵥ uIn
  have zdj : qVN (xm - vl) ≤ (3 / 2) / qWR := by
    have ht8 : qVN (xm - vT8) ≤ 1 / (2 * qWR) := by
      have h := vecNorm_dAltStepOrbMat_pow_sub_taylor8_vec_le hn hm1 vj (by omega) y0 zce (u := uIn)
          xk
      rw [sub_self, vecNorm_zero, zero_add] at h; simpa [xm, vT8, wdScaleR, η, G] using h
    have ht16 : qVN (vT8 - vl) ≤ 1 / qWR := rkmTaylor8_sub_taylor16_pow_vec_le hn80 hm1 vj (by
        omega) y0 zce xk
    rw [(sub_add_sub_cancel xm vT8 vl).symm]
    linarith [vecNorm_add_le (xm - vT8) (vT8 - vl), ht8, ht16, (by
        ring : 1 / (2 * qWR) + 1 / qWR = (3 / 2) / qWR)]
  set yq := (zp : ℝ) / qWR; have x9 : 0 ≤ yq := div_nonneg (Nat.cast_nonneg _) z4.le
  have x2 (j : ℕ) (hj : j < d) : |qDC z7 r j| ≤ (1 / 2) * yq := by
    have hc0 : 0 ≤ qDC z7 r j := (by unfold dAltCoupling; positivity); rw [abs_of_nonneg hc0]
    have uw := rkmw_maxBHiFrom_ge z7 r d 0 j hj; set rad := 4 * (j + 1) * (z7 - j) * (r - j)
    have zdk : ((altIsqrt15 rad).2 : ℝ) ≤ (altMaxBHiFrom z7 r 0 d : ℝ) := by
      have zdl : 4 * (0 + j + 1) * (z7 - (0 + j)) * (r - (0 + j)) = rad := (by simp [rad])
      rw [zdl] at uw; exact_mod_cast uw
    exact ((altIsqrt15_sound rad).2.trans (qDL zdk z4.le)).trans_eq (by
        dsimp only [yq]; rw [vk]; push_cast; ring)
  have xa (u : Fin (d + 1) → ℝ) : qVN (G *ᵥ u) ≤ yq * qVN u := by
    simpa [G, dAltGenMat, ← mul_assoc] using vecNorm_tridiagSkewMat_mulVec_le (mul_nonneg (by
        norm_num) x9) x2 u
  have v8 : yq ≤ (z2 : ℝ) := by
    have v9 : zp ≤ z2 * qWN := by
      rw [xv]; exact rkmw_ceil_div_mul_ge zp qWN (by unfold wdScale; positivity)
    exact (div_le_iff₀ z4).mpr (by unfold wdScaleR; exact_mod_cast v9)
  set zj : ℝ := (q : ℝ) * η; have vm := rkmw_substep_bounds hn v7 (by omega) up
  have vn : 0 ≤ zj := mul_nonneg (Nat.cast_nonneg _) hη_nn
  have zdm : zj ≤ ((2 + hPt : ℕ) : ℝ) / qWR := by
    rw [x5]; dsimp only [zj, η, q]; simpa [div_eq_mul_inv] using vm.2.1
  have zbi : |zj - (hPt : ℝ) / qWR| ≤ 1 / qWR := by
    rw [x5]; dsimp only [zj, η, q]; simpa [div_eq_mul_inv] using vm.2.2
  have xh : (((2 + hPt : ℕ) : ℝ) / qWR) * yq ≤ (y1 : ℝ) / qWR := by
    rw [zbh]; exact rkmw_mulCeil15_ge (2 + hPt) zp
  have xn : zj * yq ≤ (y1 : ℝ) / qWR := (qMR zdm x9).trans xh
  have ux : (y1 : ℝ) / qWR ≤ 3 / 2 := by
    rw [uv]; linarith [show (y1 : ℝ) ≤ 1500000000000000 by exact_mod_cast u2']
  have va : zj * yq ≤ 3 / 2 := xn.trans ux
  have uy : (hPt : ℝ) / qWR ≤ 4 := by
    have v9 : hPt ≤ 4000000000 * 1000000 := x5 ▸ (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _
        v7)
    rw [uv]; linarith [show (hPt : ℝ) ≤ 4000000000000000 by exact_mod_cast v9]
  have ui : (nSub : ℝ) * ((zj * yq) ^ 17 / 300000000000000) ≤ (zb : ℝ) / qWR := by
    have zck : (zj * yq) ^ 17 ≤ (altPow17Ceil15 y1 : ℝ) / qWR := (pow_le_pow_left₀ (mul_nonneg vn
        x9) xn 17).trans (rkmw_pow17Ceil15_ge y1)
    have v9 : nSub * altPow17Ceil15 y1 ≤ zb * 300000000000000 := by
      rw [u3]; exact rkmw_ceil_div_mul_ge _ 300000000000000 (by norm_num)
    have hR : (nSub : ℝ) * (altPow17Ceil15 y1 : ℝ) ≤ (zb : ℝ) * 300000000000000 := by
      exact_mod_cast v9
    have h1 := qML (qDL zck (by norm_num : (0 : ℝ) ≤ 300000000000000)) (Nat.cast_nonneg nSub)
    refine h1.trans ?_
    rw [div_div, mul_comm qWR 300000000000000, ← mul_div_assoc, div_le_div_iff₀ (mul_pos (by
        norm_num) z4) z4]
    simpa only [mul_assoc] using qMR hR z4.le
  have vb (u : Fin (d + 1) → ℝ) : qVN (rkmPtGenMat d yt *ᵥ u) ≤ (3 / 2) * qVN u := by
    have zdn (j : ℕ) (hj : j < d) : |(yt.getD j 0 : ℝ) / qWR| ≤ 3 / 4 := by
      have hget' := rkmw_buildHbFrom_getD z7 r hPt d 0 j hj; rw [← x8] at hget'
      set rad := 4 * (j + 1) * (z7 - j) * (r - j); set sq := (altIsqrt15 rad).1
      have vc : yt.getD j 0 = (((hPt * sq) / qWN : ℕ) : ℤ) := (by simpa [rad, sq] using hget')
      have uz : (sq : ℝ) / qWR ≤ qDC z7 r j := (altIsqrt15_sound rad).1; set yh := (hPt * sq) / qWN
      have hR : (yh : ℝ) * qWR ≤ (hPt : ℝ) * (sq : ℝ) := by
        unfold wdScaleR; exact_mod_cast Nat.div_mul_le_self (hPt * sq) qWN
      rw [vc, Int.cast_natCast, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) z4.le)]
      have h1 : (yh : ℝ) / qWR ≤ ((hPt : ℝ) / qWR) * ((sq : ℝ) / qWR) := by
        rw [div_mul_div_comm, div_le_div_iff₀ z4 (mul_pos z4 z4),
          show (yh : ℝ) * (qWR * qWR) = ((yh : ℝ) * qWR) * qWR by ring]
        exact qMR hR z4.le
      have zaa : qDC z7 r j ≤ (1 / 2) * yq := (le_abs_self _).trans (x2 j hj)
      have zbj : (hPt : ℝ) / qWR ≤ ((2 + hPt : ℕ) : ℝ) / qWR := qDL (by
          exact_mod_cast (by omega : hPt ≤ 2 + hPt)) z4.le
      have h2 := h1.trans (mul_le_mul zbj (uz.trans zaa) (div_nonneg (Nat.cast_nonneg _) z4.le)
          (div_nonneg (Nat.cast_nonneg _) z4.le))
      have h3 := (qML xh (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (qML ux (by norm_num))
      exact (h2.trans_eq (by ring)).trans (h3.trans_eq (by norm_num))
    exact (vecNorm_tridiagSkewMat_mulVec_le (by norm_num : (0 : ℝ) ≤ 3 / 4) zdn u).trans (le_of_eq
        (by
        ring))
  have u4 (u : Fin (d + 1) → ℝ) : qVN ((zj • G - rkmPtGenMat d yt) *ᵥ u) ≤ (((z2 : ℝ) + 10) / qWR) *
      qVN u := by
    have zab : zj • G - rkmPtGenMat d yt = tridiagSkewMat d (fun j ↦ zj * qDC z7 r j - (yt.getD j
        0 : ℝ) / qWR) := tridiagSkewMat_smul_sub d zj (qDC z7 r) (fun w ↦ (yt.getD w 0 : ℝ) / qWR)
    rw [zab]
    have vo (j : ℕ) (hj : j < d) :
        |zj * qDC z7 r j - (yt.getD j 0 : ℝ) / qWR| ≤ ((1 / 2 : ℝ) * (z2 : ℝ) + 5) / qWR := by
      have hget' := rkmw_buildHbFrom_getD z7 r hPt d 0 j hj; rw [← x8] at hget'
      set rad := 4 * (j + 1) * (z7 - j) * (r - j); set sq := (altIsqrt15 rad).1
      have vc : yt.getD j 0 = (((hPt * sq) / qWN : ℕ) : ℤ) := (by simpa [rad, sq] using hget')
      have zcf : 0 ≤ qDC z7 r j := (by unfold dAltCoupling; positivity)
      have zaa : qDC z7 r j ≤ (1 / 2) * (z2 : ℝ) := ((le_abs_self _).trans (x2 j hj)).trans (qML v8
          (by
          norm_num))
      have zac : (altIsqrt15 rad).2 ≤ sq + 1 := by
        simpa [rad, sq] using rkmw_checkHbTight_sound z7 r d 0 zcj j hj
      set yh := (hPt * sq) / qWN
      have hloR : (yh : ℝ) * qWR ≤ (hPt : ℝ) * (sq : ℝ) := by
        unfold wdScaleR; exact_mod_cast Nat.div_mul_le_self (hPt * sq) qWN
      have hhiR : (hPt : ℝ) * (sq : ℝ) ≤ ((yh + 1 : ℕ) : ℝ) * qWR := by
        have v9 := (Nat.lt_mul_div_succ (hPt * sq) (by
            unfold wdScale; positivity : 0 < qWN)).trans_eq (Nat.mul_comm _ _)
        unfold wdScaleR; exact_mod_cast v9.le
      rw [vc, Int.cast_natCast]
      have zad : |qDC z7 r j - (sq : ℝ) / qWR| ≤ 1 / qWR := by
        have hlo : (sq : ℝ) / qWR ≤ qDC z7 r j := (altIsqrt15_sound rad).1
        have hhi : qDC z7 r j ≤ ((altIsqrt15 rad).2 : ℝ) / qWR := (altIsqrt15_sound rad).2
        rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
        linarith [hhi.trans (qDL (by
            exact_mod_cast zac : ((altIsqrt15 rad).2 : ℝ) ≤ ((sq + 1 : ℕ) : ℝ)) z4.le), show ((sq +
            1 : ℕ) : ℝ) / qWR - (sq : ℝ) / qWR = 1 / qWR by
            push_cast; ring]
      have zae : |((hPt : ℝ) / qWR) * ((sq : ℝ) / qWR) - (yh : ℝ) / qWR| ≤ 1 / qWR := by
        have zaf : 0 ≤ ((hPt : ℝ) / qWR) * ((sq : ℝ) / qWR) - (yh : ℝ) / qWR := by
          rw [div_mul_div_comm, sub_nonneg, div_le_div_iff₀ z4 (mul_pos z4 z4),
            show (yh : ℝ) * (qWR * qWR) = ((yh : ℝ) * qWR) * qWR by ring]
          exact qMR hloR z4.le
        rw [abs_of_nonneg zaf, div_mul_div_comm]
        have h1 : (hPt : ℝ) * (sq : ℝ) ≤ ((yh : ℝ) + 1) * qWR := by
          simpa only [Nat.cast_add, Nat.cast_one] using hhiR
        exact (sub_le_sub_right (qDL h1 (mul_nonneg z4.le z4.le)) _).trans_eq (by
            field_simp [z4.ne']; ring)
      set e1 : ℝ := (zj - (hPt : ℝ) / qWR) * qDC z7 r j
      set e2 : ℝ := ((hPt : ℝ) / qWR) * (qDC z7 r j - (sq : ℝ) / qWR)
      set e3 : ℝ := ((hPt : ℝ) / qWR) * ((sq : ℝ) / qWR) - (yh : ℝ) / qWR
      rw [show zj * qDC z7 r j - (yh : ℝ) / qWR = e1 + e2 + e3 by
        dsimp [e1, e2, e3]; ring]
      have ht1 : |e1| ≤ (1 / qWR) * ((1 / 2) * (z2 : ℝ)) := by
        dsimp [e1]; rw [abs_mul, abs_of_nonneg zcf]
        exact mul_le_mul zbi zaa zcf (div_nonneg (by norm_num) z4.le)
      have ht2 : |e2| ≤ 4 * (1 / qWR) := by
        dsimp [e2]; rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) z4.le)]
        exact mul_le_mul uy zad (abs_nonneg _) (by norm_num)
      linarith [abs_add_le e1 e2, abs_add_le (e1 + e2) e3, ht1, ht2, zae,
        (by ring : (1 / qWR) * ((1 / 2) * (z2 : ℝ)) + 4 * (1 / qWR) +
          1 / qWR = ((1 / 2 : ℝ) * (z2 : ℝ) + 5) / qWR)]
    exact (vecNorm_tridiagSkewMat_mulVec_le (div_nonneg (by positivity) z4.le) vo u).trans (le_of_eq
        (by
        ring))
  have zcl (u : Fin (d + 1) → ℝ) : qVN ((zj • G) *ᵥ u) ≤ (3 / 2) * qVN u := by
    rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg vn]
    exact ((qML (xa u) vn).trans_eq (by ring)).trans (qMR va (vecNorm_nonneg u))
  set x1 := taylor16Mat zj G; set xo := taylor16OfMat (rkmPtGenMat d yt)
  have u5 (u : Fin (d + 1) → ℝ) : qVN ((x1 - xo) *ᵥ u) ≤ ((5 * (z2 : ℝ) + 50) / qWR) * qVN u :=
      (vecNorm_taylor16OfMat_sub_mulVec_le zcl vb (div_nonneg (by positivity) z4.le) u4 u).trans
      (le_of_eq (by ring))
  set vp := (taylor16Mat η G) ^ q
  have zcm : 0 ≤ dAltGenNormBound z7 r := (by unfold dAltGenNormBound; positivity)
  have zcn : dAltGenNormBound z7 r ≤ 200000 := by
    unfold dAltGenNormBound; rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩
    have v9 : 4 * (min z7 r + 1) ^ 2 * max z7 r ≤ 4 * 1025 ^ 2 * 8192 := Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by have := Nat.min_le_right z7 r; omega) 2))
        (Nat.max_le.mpr ⟨vj, by omega⟩)
    exact (by exact_mod_cast v9 : _ ≤ ((4 * 1025 ^ 2 * 8192 : ℕ) : ℝ)).trans (by norm_num)
  have hηBf1 : η * dAltGenNormBound z7 r ≤ 1 := by
    dsimp [η]; rw [one_div_mul_eq_div, div_le_one ua]
    exact zcn.trans ((by norm_num : (200000 : ℝ) ≤ (2 : ℝ) ^ 100).trans xz)
  have vd (u : Fin (d + 1) → ℝ) : qVN (vp *ᵥ u) ≤ qVN u := by
    have h1 (x : Fin (d + 1) → ℝ) : qVN (taylor16Mat η G *ᵥ x) ≤ 1 * qVN x := by
      rw [one_mul]
      exact vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose z7 r) hη_nn zcm
          (vecNorm_dAltGenMat_mulVec_le z7 r) (hηBf1.trans (by norm_num)) x
    have hp := vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) h1 q u
    rw [one_pow, one_mul] at hp; exact hp
  have yn (u : Fin (d + 1) → ℝ) : qVN (x1 *ᵥ u) ≤ qVN u := vecNorm_taylor16Mat_mulVec_le
      (dAltGenMat_transpose z7 r) vn x9 xa va u
  have vq (u : Fin (d + 1) → ℝ) : qVN (xo *ᵥ u) ≤ qVN u := vecNorm_taylor16OfMat_mulVec_le
      (tridiagSkewMat_transpose d _) vb u
  have uj (u : Fin (d + 1) → ℝ) : qVN ((vp - x1) *ᵥ u) ≤ ((zj * yq) ^ 17 / 300000000000000) * qVN
      u := vecNorm_taylor16Mat_substep_le (dAltGenMat_transpose z7 r) hη_nn x9 xa q va u
  have uk : xo = taylor16OfMat (rkmPtGenMat d yt) := rfl
  have u6 : vp = (taylor16Mat η G) ^ q := rfl; clear_value x1 xo vp
  have ul : qVN (vl - (x1 ^ nSub) *ᵥ uIn) ≤ (zb : ℝ) / qWR := by
    have zco : (vp ^ nSub) *ᵥ uIn = vl := by
      dsimp only [vl]; rw [u6, zdi, mul_comm nSub q, pow_mul]
    rw [← zco]
    have zag := vecNorm_pow_mulVec_sub_le vd yn (div_nonneg (pow_nonneg (mul_nonneg vn x9) 17) (by
        norm_num)) uj nSub uIn uIn
    rw [sub_self, vecNorm_zero, zero_add] at zag
    exact (zag.trans (mul_le_of_le_one_right (by positivity) xk)).trans ui
  have vr : qVN ((x1 ^ nSub) *ᵥ uIn - (xo ^ nSub) *ᵥ qLO d vec) ≤ qVN (uIn - qLO d vec) + ((nSub :
      ℝ) * (5 * (z2 : ℝ) + 50)) / qWR := by
    have zcp (u : Fin (d + 1) → ℝ) : qVN ((xo - x1) *ᵥ u) ≤ ((5 * (z2 : ℝ) + 50) / qWR) * qVN
        u := by
      rw [Matrix.sub_mulVec, ← neg_sub (x1 *ᵥ u), ← Matrix.sub_mulVec, vecNorm_neg]; exact u5 u
    have zag := vecNorm_pow_mulVec_sub_le vq yn (div_nonneg (by positivity) z4.le) zcp nSub (qLO d
        vec) uIn
    rw [← neg_sub ((x1 ^ nSub) *ᵥ uIn), vecNorm_neg, ← neg_sub uIn, vecNorm_neg] at zag
    have hc0 : 0 ≤ (nSub : ℝ) * ((5 * (z2 : ℝ) + 50) / qWR) := mul_nonneg (Nat.cast_nonneg nSub)
        (div_nonneg (by positivity) z4.le)
    have zcq : (nSub : ℝ) * ((5 * (z2 : ℝ) + 50) / qWR) * qVN uIn ≤ ((nSub : ℝ) * (5 * (z2 : ℝ) +
        50)) / qWR := (mul_le_of_le_one_right hc0 xk).trans_eq (by ring)
    linarith [zag, zcq]
  set xp := qPZ w.offOut w.xsOut
  have zbk : xp.length ≤ d + 1 := by
    dsimp only [xp, d]; rw [rkmw_prependZeros_length, ← ur]; exact uq.2.2.1
  have u7 : qVN (qLO d xp - (xo ^ nSub) *ᵥ qLO d vec) ≤ (((297 / 2) * (nSub : ℝ) + (w.dropSeg : ℝ)))
      / qWR := by
    rcases w with ⟨wd, whb, woffIn, wxsIn, zef, wxsOut, wdrop⟩
    dsimp only at ur us x4 xp; subst ur; have zcr : whb = yt := (by rw [us, x8, x5])
    subst zcr; have hbd := uq.2.2.2 ((Nat.min_le_right z7 r).trans y0) vb
    dsimp only at hbd; rwa [x4, ← uk] at hbd
  set zbl := (x1 ^ nSub) *ᵥ uIn; set zu := rkmMaskSignVec d mask zbl; refine ⟨zu, ?_, ?_, ?_⟩
  · rw [vecNorm_rkmMaskSignVec]
    have hpow := vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) (fun x ↦ by
        rw [one_mul]; exact yn x) nSub uIn
    rw [one_pow, one_mul] at hpow; exact hpow.trans xk
  · rw [xl, rkmApplyMaskBits_length]; exact zbk
  · have h1 : qVN (rkmMaskSignVec d mask xm - zu) ≤
        (3 / 2) / qWR + (zb : ℝ) / qWR := by
      dsimp only [zu]; rw [rkmMaskSignVec_sub, vecNorm_rkmMaskSignVec, (sub_add_sub_cancel xm vl
          zbl).symm]
      exact (vecNorm_add_le _ _).trans (add_le_add zdj ul)
    have h2 : qVN (zu - qLO d yg) ≤ qVN (uIn - qLO d vec) + ((nSub : ℝ) * (5 * (z2 : ℝ) + 50)) / qWR
        + (((297 / 2) * (nSub : ℝ) + (w.dropSeg : ℝ))) / qWR := by
      dsimp only [zu]
      rw [xl, rkmApplyMaskBits_orbVec, rkmMaskSignVec_sub, vecNorm_rkmMaskSignVec,
          (sub_add_sub_cancel zbl ((xo ^ nSub) *ᵥ qLO d vec) (qLO d xp)).symm]
      have hneg : qVN ((xo ^ nSub) *ᵥ qLO d vec - qLO d xp) ≤ (((297 / 2) * (nSub : ℝ) +
          (w.dropSeg : ℝ))) / qWR := by
        rw [← vecNorm_neg, neg_sub]; exact u7
      linarith [vecNorm_add_le (zbl - (xo ^ nSub) *ᵥ qLO d vec) ((xo ^ nSub) *ᵥ qLO d vec - qLO d
          xp), vr, hneg]
    have zdp : ((y4 + w.dropSeg : ℕ) : ℝ) = ((zb : ℝ) + 256) + (nSub : ℝ) * (256 + 10 * (z2 : ℝ)) +
        (w.dropSeg : ℝ) := by
      rw [ut]; push_cast; ring
    have zbm : (3 / 2) / qWR + (zb : ℝ) / qWR + ((nSub : ℝ) * (5 * (z2 : ℝ) + 50)) / qWR + (((297 /
        2) * (nSub : ℝ) + (w.dropSeg : ℝ))) / qWR ≤ (((y4 + w.dropSeg : ℕ) : ℝ) - 253) / qWR := by
      rw [← add_div, ← add_div, ← add_div]; refine qDL ?_ z4.le
      rw [zdp]; have hn0 : (0 : ℝ) ≤ nSub := Nat.cast_nonneg nSub
      have hb0 : (0 : ℝ) ≤ z2 := Nat.cast_nonneg z2; linarith [hn0, mul_nonneg hn0 hb0]
    linarith [h1, h2, zbm]
/- ## Multi-Segment Symmetric-Subspace & Windowed Row Stitcher Soundness -/
private theorem z9 {n x r : ℕ} (hn : altN0 ≤ n) (hx : x ≤ 8192) (hr : r ≤ 1024) : 1 ≤ n ∧ 2 * x < 2
    ^ n ∧ 2 * x ≤ 2 ^ n ∧ x + r ≤ 2 ^ n := by
  have h15 : 15 ≤ n := le_trans (show 15 ≤ altN0 by unfold altN0; norm_num) hn
  have hp : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h15
  have h2x : 2 * x < 2 ^ n := lt_of_le_of_lt (Nat.mul_le_mul_left 2 hx) (lt_of_lt_of_le (by
      norm_num : 2 * 8192 < 2 ^ 15) hp)
  exact ⟨le_trans (by norm_num : 1 ≤ 15) h15, h2x, h2x.le, le_trans (Nat.add_le_add hx hr) (le_trans
      (by
      norm_num : 8192 + 1024 ≤ 2 ^ 15) hp)⟩
private theorem y5 (N M : ℕ) (R : Finset (Fin N)) (x y : Fin (orbDim M R.card) → ℝ) : qOE N M R (x -
    y) = qOE N M R x - qOE N M R y := by
  funext E; simp only [orbEmbedGen, Pi.sub_apply, sub_div]
private theorem yo (M₁ M₂ r : ℕ) (x y : Fin (orbDim M₁ r) → ℝ) : zeroPadOrbVec M₁ M₂ r (x - y) =
    zeroPadOrbVec M₁ M₂ r x - zeroPadOrbVec M₁ M₂ r y := by
  funext u; by_cases hu : u.1 < orbDim M₁ r <;> simp [zeroPadOrbVec, Pi.sub_apply, hu]
private theorem y2 {M₁ M₂ r : ℕ} {vs : List ℤ} (h12 : M₁ ≤ M₂) (hvs : vs.length ≤ min M₁ r + 1) :
    zeroPadOrbVec M₁ M₂ r (qLO (min M₁ r) vs) = qLO (min M₂ r) vs := by
  have _ := h12; funext u; unfold zeroPadOrbVec rkmListToOrbVec
  by_cases hu : u.1 < orbDim M₁ r
  · rw [dite_eq_left hu]
  · rw [dite_eq_right hu]; have hge : vs.length ≤ u.1 := (by unfold orbDim at hu; omega)
    rw [rkm_getD_eq_zero_of_le vs u.1 hge]; simp
private def z3 (d : ℕ) : List ℕ → (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ)
  | [], x => x
  | j0 :: xw, x => z3 d xw (fun w ↦ (if w.1 ≤ j0 then (-1 : ℝ) else 1) * x w)
private theorem zc (N M : ℕ) (R : Finset (Fin N)) : ∀ (ks : List ℕ) (x : Fin (orbDim M R.card) → ℝ),
    qEM R (ks.map MuxSymOp.prefixKick) (qOE N M R x) = qOE N M R (z3 (min M R.card) ks x)
  | [], _ => rfl
  | j0 :: xw, x => by
    have h1 : symPrefixKickVec R j0 (qOE N M R x) = qOE N M R (fun w ↦ (if w.1 ≤ j0 then (-1 : ℝ)
        else 1) * x w) := by
      funext E; dsimp only [symPrefixKickVec, orbEmbedGen]; split_ifs <;> ring
    simp only [List.map_cons, evalMuxSymOps, h1]; exact zc N M R xw _
private theorem zf (mask : List Bool) : ∀ (k : ℕ) (yx : Bool) (j : ℕ), j ∈ qMK mask k yx → j ≤ k
  | 0, yx, j, hj => by unfold rkmMaskKicksDown at hj; split_ifs at hj <;> simp at hj; omega
  | k + 1, yx, j, hj => by
    unfold rkmMaskKicksDown at hj; split_ifs at hj
    · rcases List.mem_cons.mp hj with rfl | hmem
      · exact le_rfl
      · exact (zf mask k (Bool.not yx) j hmem).trans (Nat.le_succ k)
    · exact (zf mask k yx j hj).trans (Nat.le_succ k)
private theorem zv (d : ℕ) : ∀ (ks : List ℕ) (x : Fin (d + 1) → ℝ) (w : Fin (d + 1)), (∀ j ∈ ks, j <
    w.1) → z3 d ks x w = x w
  | [], _, _, _ => rfl
  | j0 :: xw, x, w, hgt => by
    unfold z3; rw [zv d xw _ w (fun j hj ↦ hgt j (List.mem_cons_of_mem _ hj))]
    have hnle : ¬ w.1 ≤ j0 := (by have := hgt j0 List.mem_cons_self; omega); simp [hnle]
private theorem z5 (d : ℕ) (mask : List Bool) : ∀ (k : ℕ) (yx : Bool) (x0 x : Fin (d + 1) → ℝ), (∀
    w : Fin (d + 1), w.1 ≤ k → x w = (if yx then (-1 : ℝ) else 1) * x0 w) → ∀ w : Fin (d + 1), w.1 ≤
    k → z3 d (qMK mask k yx) x w = (if mask.getD w.1 false then (-1 : ℝ) else 1) * x0 w
  | 0, yx, x0, x, hx, w, hw => by
    have hw0 : w.1 = 0 := (by omega); have hxw := hx w hw
    unfold rkmMaskKicksDown; rw [hw0]; generalize mask.getD 0 false = b0
    cases yx <;> cases b0 <;> simp [rkmBoolXor, z3, hw, hxw]
  | k + 1, yx, x0, x, hx, w, hw => by
    unfold rkmMaskKicksDown
    by_cases hwk : w.1 ≤ k
    · by_cases hxor : rkmBoolXor yx (mask.getD (k + 1) false) = true
      · rw [xf hxor, z3]
        exact z5 d mask k (Bool.not yx) x0 _ (fun u hu ↦ by
            have hu1 : u.1 ≤ k + 1 := hu.trans (Nat.le_succ k)
            rw [xf hu1, hx u hu1]; cases yx <;> simp [Bool.not]) w hwk
      · rw [xg hxor]; exact z5 d mask k yx x0 x (fun u hu ↦ hx u (hu.trans (Nat.le_succ k))) w hwk
    · have hweq : w.1 = k + 1 := (by omega); have hxw := hx w hw
      have hg (fl' : Bool) (x' : Fin (d + 1) → ℝ) := zv d (qMK mask k fl') x' w fun j hj ↦ by
          have := zf mask k fl' j hj; omega
      rw [hweq]; generalize mask.getD (k + 1) false = bk1
      cases yx <;> cases bk1 <;> simp [rkmBoolXor, z3, hg, hw, hxw]
private theorem y7 {N M : ℕ} (R : Finset (Fin N)) (K : ℕ) (D : SymOrthogonal N M) (xw : List
    (MuxSymOp N M)) (v : SymSubset N M → ℝ) : qEM R (.walk K D :: xw) v = qEM R xw (evalSymStage R
    D.1 K v) := rfl
private theorem ye {N M : ℕ} (D : Matrix (SymSubset N M) (SymSubset N M) ℝ) (hsym : Dᵀ = D) (hinv :
    D * D = 1) : (SymOrthogonal.ofSymmInvolution D hsym hinv).1 = D := rfl
private theorem zz {N M r K : ℕ} {D : SymOrthogonal N M} (hD : D.1 = dAltSymMat N M) {R : Finset
    (Fin N)} (hR : R.card = r) (zah : M + R.card ≤ N) (mask : List Bool) (uIn : Fin (orbDim M
    R.card) → ℝ) : qEM R (MuxSymOp.walk K D :: (qMK mask (min M r) false).map MuxSymOp.prefixKick)
    (qOE N M R uIn) = qOE N M R (rkmMaskSignVec (min M R.card) mask (((dAltStepOrbMat N M R.card) ^
    K) *ᵥ uIn)) := by
  subst hR; rw [y7, hD, evalSymStage_dAltSymMat_orbEmbedGen zah K uIn, zc]
  apply congrArg (qOE N M R); funext w; unfold rkmMaskSignVec
  exact z5 (min M R.card) mask (min M R.card) false _ _ (fun _ _ ↦ by
      rw [xg Bool.false_ne_true, one_mul]) w (Nat.lt_succ_iff.mp w.2)
private theorem ya {n m r lS : ℕ} (tau9 nSub : ℕ) (mask : List Bool) (hn : altN0 ≤ n) (vj : lS * m ≤
    8192) (y0 : r ≤ 1024) {R : Finset (Fin (2 ^ n))} (hR : R.card = r) (uIn : Fin (orbDim (lS * m)
    R.card) → ℝ) : qEM R (rkmSegOps n m r lS tau9 nSub mask) (qOE (2 ^ n) (lS * m) R uIn) = qOE (2 ^
    n) (lS * m) R (rkmMaskSignVec (min (lS * m) R.card) mask (((dAltStepOrbMat (2 ^ n) (lS * m)
    R.card) ^ altStepCount tau9 nSub (2 ^ n)) *ᵥ uIn)) := by
  subst hR; obtain ⟨hn1, zcs, _, zah⟩ := z9 hn vj y0
  have hhm : 1 ≤ n ∧ 2 * (lS * m) < 2 ^ n := ⟨hn1, zcs⟩; unfold rkmSegOps; rw [dite_eq_left hhm]
  exact zz (ye _ _ _) rfl zah mask uIn
private theorem zh {m z1 r lS tau9 nSub : ℕ} {mask : List Bool} {w : qWS} {yi zx zi : List ℕ} {zl :
    List (List Bool)} {x6 : List qWS} {yr vt zk yy y8 : ℕ} {vec y9 : List ℤ} (zm : qEW m z1 r (lS ::
    yi) (tau9 :: zx) (nSub :: zi) (mask :: zl) (w :: x6) yr vt zk vec = (yy, y8, y9)) (y6 : yy ≠
    0) : 1 ≤ lS ∧ yr ≤ lS ∧ lS ≤ z1 ∧ 1 ≤ lS * m ∧ lS * m ≤ 8192 := by
  unfold rkmEvalSegsWinWithWalks at zm; dsimp only at zm
  have hg1 : Bool.or (qPB lS 1) (Bool.or (qPB lS yr) (Bool.or (qPB z1 lS) (Bool.or
      (qPB (Nat.mul lS m) 1) (Bool.or (qPB 8192 (Nat.mul lS m)) (Bool.or
      (qPB (highdNatMin (Nat.mul lS m) r) 1) (Bool.or (tau9.beq 0) (Bool.or
      (qPB 4000000000 tau9) (Bool.or (nSub.beq 0) (Bool.or (qPB 16384 nSub)
      (qPB (Nat.add (highdNatMin (Nat.mul lS m) r) 1) (rkmBoolListLen mask))))))))))) = false :=
    z8 fun h ↦ by rw [h] at zm; exact y6 (Prod.mk.inj zm).1.symm
  simp only [Bool.or_eq_false_iff, rkmw_primNatBlt_eq_false] at hg1
  exact ⟨hg1.1, hg1.2.1, hg1.2.2.1, hg1.2.2.2.1, hg1.2.2.2.2.1⟩
private theorem yj {n m z1 : ℕ} (hn : altN0 ≤ n) {R : Finset (Fin (2 ^ n))} (hr2 : 2 ≤ R.card) (y0 :
    R.card ≤ 1024) {l0 t0 s0 : ℕ} {mk0 : List Bool} {w0 : qWS} {yi zx zi : List ℕ} {zl : List (List
    Bool)} {x6 : List qWS} {yr vt zk yy y8 : ℕ} {vec y9 : List ℤ} {v : SymSubset (2 ^ n) (l0 * m) →
    ℝ} {uIn : Fin (orbDim (l0 * m) R.card) → ℝ} (yw : RkmWinSegWalkSound s0 w0) (xk : qVN uIn ≤ 1)
    (zai : vec.length ≤ min (l0 * m) R.card + 1) (zaj : qFN (v - qOE (2 ^ n) (l0 * m) R uIn) + qVN
    (uIn - qLO (min (l0 * m) R.card) vec) ≤ ((zk : ℝ) + 1) / qWR) (zm : qEW m z1 R.card (l0 :: yi)
    (t0 :: zx) (s0 :: zi) (mk0 :: zl) (w0 :: x6) yr vt zk vec = (yy, y8, y9)) (y6 : yy ≠ 0) : ∃ zg :
    ℕ, ∃ zu : Fin (orbDim (l0 * m) R.card) → ℝ, 1 ≤ l0 * m ∧ l0 * m ≤ 8192 ∧ qVN zu ≤ 1 ∧ (qAM mk0
    (qPZ w0.offOut w0.xsOut)).length ≤ min (l0 * m) R.card + 1 ∧ qFN (qEM R (rkmSegOps n m R.card l0
    t0 s0 mk0) v - qOE (2 ^ n) (l0 * m) R zu) + qVN (zu - qLO (min (l0 * m) R.card) (qAM mk0 (qPZ
    w0.offOut w0.xsOut))) ≤ ((zg : ℝ) - 252) / qWR ∧ qEW m z1 R.card yi zx zi zl x6 l0 (highdNatMin
    (Nat.mul l0 m) R.card) zg (qAM mk0 (qPZ w0.offOut w0.xsOut)) = (yy, y8, y9) := by
  obtain ⟨_, _, _, ub, x3⟩ := zh zm y6
  conv at zm => lhs; unfold rkmEvalSegsWinWithWalks
  dsimp only at zm; simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at zm
  have hg1 : Bool.or (qPB l0 1) (Bool.or (qPB l0 yr) (Bool.or (qPB z1 l0) (Bool.or
      (qPB (Nat.mul l0 m) 1) (Bool.or (qPB 8192 (Nat.mul l0 m)) (Bool.or
      (qPB (highdNatMin (Nat.mul l0 m) R.card) 1) (Bool.or (t0.beq 0) (Bool.or
      (qPB 4000000000 t0) (Bool.or (s0.beq 0) (Bool.or (qPB 16384 s0)
      (qPB (Nat.add (highdNatMin (Nat.mul l0 m) R.card) 1) (rkmBoolListLen mk0))))))))))) =
      false := z8 fun h ↦ by rw [h] at zm; exact y6 (Prod.mk.inj zm).1.symm
  rw [hg1] at zm; simp only [Bool.or_eq_false_iff, rkmw_primNatBlt_eq_false] at hg1
  have zbn : 0 < t0 := Nat.pos_of_ne_zero (rkmw_nat_beq_eq_false.mp hg1.2.2.2.2.2.2.1)
  have zct : t0 ≤ 4000000000 := hg1.2.2.2.2.2.2.2.1
  have zbo : 0 < s0 := Nat.pos_of_ne_zero (rkmw_nat_beq_eq_false.mp hg1.2.2.2.2.2.2.2.2.1)
  have zcu : s0 ≤ 16384 := hg1.2.2.2.2.2.2.2.2.2.1; set hPt := Nat.div (Nat.mul t0 1000000) s0
  have ghPt : qPB hPt 1 = false := z8 fun h ↦ by
    rw [h] at zm; exact y6 (Prod.mk.inj zm).1.symm
  rw [ghPt] at zm; set d0 := highdNatMin (Nat.mul l0 m) R.card
  have yp : d0 = min (l0 * m) R.card := rkmb_natMin_eq (l0 * m) R.card
  set zcv := altMaxBHiFrom (Nat.mul l0 m) R.card 0 d0; set zbp := Nat.mul 2 zcv
  set zbq := highdMulCeil15 (Nat.add 2 hPt) zbp
  have ghg : Bool.or (qPB 1500000000000000 zbq) (Bool.not (altCheckHbTight (Nat.mul l0 m) R.card 0
      d0)) = false := z8 fun h ↦ by
    rw [h] at zm; exact y6 (Prod.mk.inj zm).1.symm
  rw [ghg] at zm
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkmw_primNatBlt_eq_false] at ghg
  set zcg := altPow17Ceil15 zbq
  set vu := Nat.div (Nat.add 299999999999999 (Nat.mul s0 zcg)) 300000000000000
  set z2 := Nat.div (Nat.add 999999999999999 zbp) qWN
  set y4 := Nat.add (Nat.add vu 256) (Nat.mul s0 (Nat.add 256 (Nat.mul 10 z2)))
  set zg := Nat.add zk (Nat.add y4 w0.dropSeg)
  have gnp : Bool.or (zg.beq 0) (qPB 100000000000000 zg) = false :=
    z8 fun h ↦ by rw [h] at zm; exact y6 (Prod.mk.inj zm).1.symm
  rw [gnp] at zm; set yt := altBuildHbFrom (Nat.mul l0 m) R.card hPt 0 d0
  set xb := qPZ w0.offIn w0.xsIn
  have geq : Bool.and (d0.beq w0.d) (Bool.and (muxIntListEq yt w0.hbExp) (muxIntListEq
      (qPR (Nat.add d0 1) vec) (qPR (Nat.add d0 1) xb))) = true := v5 fun h ↦ by
    rw [h] at zm; exact y6 (Prod.mk.inj zm).1.symm
  rw [geq] at zm; dsimp only at zm; simp only [Bool.and_eq_true, muxIntListEq_eq_true] at geq
  obtain ⟨hdw0_b, zdt, zbr⟩ := geq; have hdw0 := rkmw_nat_beq_eq_true.mp hdw0_b
  have x4 : qLO (min (l0 * m) R.card) xb = qLO (min (l0 * m) R.card) vec := by
    funext a; unfold rkmListToOrbVec
    have zak : xb.length ≤ d0 + 1 := by
      dsimp [xb]; rw [rkmw_prependZeros_length, hdw0]; exact yw.2.1
    have zal : vec.length ≤ d0 + 1 := (by rw [yp]; exact zai)
    have hp' : qPR (d0 + 1) vec = qPR (d0 + 1) xb := zbr; have hg1' := z6 (d0 + 1) xb zak a.1
    have hg2' := z6 (d0 + 1) vec zal a.1; rw [← hg1', ← hp', hg2']
  have hseg := rkmSingleSegWinT16_bound (mask := mk0) hn ub x3 hr2 y0 zbn zct zbo zcu
    (by dsimp only [zbq, hPt, zbp, zcv] at ghg
        simpa only [yp, Nat.add_eq, Nat.mul_eq, ys] using ghg.1)
    (by simpa only [yp, Nat.mul_eq] using ghg.2)
    yw (hdw0.symm.trans yp)
    (by rw [← zdt]; dsimp only [yt, hPt]
        simp only [yp, Nat.mul_eq, ys])
    x4 xk
  dsimp only at hseg; obtain ⟨zu, vv, zy, yu⟩ := hseg
  have zbs : ((299999999999999 + s0 * altPow17Ceil15 (highdMulCeil15 (2 + (t0 * 1000000) / s0) (2 *
      altMaxBHiFrom (l0 * m) R.card 0 (min (l0 * m) R.card)))) / 300000000000000 + 256) + s0 * (256
      + 10 * ((999999999999999 + 2 * altMaxBHiFrom (l0 * m) R.card 0 (min (l0 * m) R.card)) / qWN))
      = y4 := by
    dsimp only [y4, vu, zcg, zbq, z2, zbp, zcv, hPt]; simp only [yp, Nat.add_eq, Nat.mul_eq, ys]
  rw [zbs] at yu; have zah : l0 * m + R.card ≤ 2 ^ n := (z9 hn x3 y0).2.2.2
  let ops0 := rkmSegOps n m R.card l0 t0 s0 mk0; let xc := qEM R ops0 (qOE (2 ^ n) (l0 * m) R uIn)
  have uc := ya t0 s0 mk0 hn x3 y0 rfl uIn
  generalize (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^ altStepCount t0 s0 (2 ^ n)) *ᵥ uIn) =
      uWalk0 at uc yu
  have hq1 : qFN (qEM R ops0 v - xc) = qFN (v - qOE (2 ^ n) (l0 * m) R uIn) :=
      finVecNorm_evalMuxSymOps_sub R ops0 v _
  have hq2 : qFN (xc - qOE (2 ^ n) (l0 * m) R zu) = qVN (rkmMaskSignVec (min (l0 * m) R.card) mk0
      uWalk0 - zu) := by
    dsimp [xc]; rw [uc, ← y5, finVecNorm_orbEmbedGen zah]
  have htri : qFN (qEM R ops0 v - qOE (2 ^ n) (l0 * m) R zu) ≤ qFN (qEM R ops0 v - xc) + qFN (xc -
      qOE (2 ^ n) (l0 * m) R zu) := by
    rw [(sub_add_sub_cancel _ xc _).symm]; exact finVecNorm_add_le _ _
  have hnpR : (zg : ℝ) = (zk : ℝ) + ((y4 + w0.dropSeg : ℕ) : ℝ) := by
    change ((zk + (y4 + w0.dropSeg) : ℕ) : ℝ) = _; push_cast; rfl
  have ve : ((zk : ℝ) + 1) / qWR + (((y4 + w0.dropSeg : ℕ) : ℝ) - 253) / qWR =
      ((zg : ℝ) - 252) / qWR := by rw [← add_div, hnpR]; ring
  refine ⟨zg, zu, ub, x3, vv, zy, ?_, zm⟩
  change qFN (qEM R ops0 v - qOE (2 ^ n) (l0 * m) R zu) + _ ≤ _
  linarith [htri, hq1, hq2, yu, zaj, ve]
private theorem y3 {n m z1 r : ℕ} (hn : altN0 ≤ n) (hr2 : 2 ≤ r) (y0 : r ≤ 1024) {R : Finset (Fin (2
    ^ n))} (hR : R.card = r) : ∀ (yi : List ℕ) (l0 t0 s0 : ℕ) (mk0 : List Bool) (w0 : qWS) (zx zi :
    List ℕ) (zl : List (List Bool)) (x6 : List qWS) (yr vt zk yy y8 : ℕ) (vec y9 : List ℤ) (v :
    SymSubset (2 ^ n) (l0 * m) → ℝ) (uIn : Fin (orbDim (l0 * m) R.card) → ℝ), RkmWinSegWalksSound
    (s0 :: zi) (w0 :: x6) → qVN uIn ≤ 1 → vec.length ≤ min (l0 * m) R.card + 1 → qFN (v - qOE (2 ^
    n) (l0 * m) R uIn) + qVN (uIn - qLO (min (l0 * m) R.card) vec) ≤ ((zk : ℝ) + 1) / qWR → qEW m z1
    r (l0 :: yi) (t0 :: zx) (s0 :: zi) (mk0 :: zl) (w0 :: x6) yr vt zk vec = (yy, y8, y9) → yy ≠ 0 →
    y8 ≠ 0 → let segs := qBT n m r yi zx zi zl
      let lEnd := rkmEndL l0 segs
      yi.length = zx.length ∧ yi.length = zi.length ∧ yi.length = zl.length ∧ lEnd * m ≤ 8192 ∧ yy =
          min (lEnd * m) r ∧ y9.length ≤ yy + 1 ∧ ∃ yc : Fin (orbDim (lEnd * m) R.card) → ℝ, qFN
          (rkmEvalSegs R l0 (rkmSegOps n m r l0 t0 s0 mk0) segs v - qOE (2 ^ n) (lEnd * m) R yc) +
          qVN (yc - qLO (min (lEnd * m) R.card) y9) ≤ (y8 : ℝ) / qWR := by
  subst hR; intro yi
  induction yi with
  | nil =>
    intro l0 t0 s0 mk0 w0 zx zi zl x6 yr _dPrev zk yy y8
      vec y9 v uIn hws xk zai zaj zm y6 _hpadOut
    have z4 : (0 : ℝ) < qWR := (by unfold wdScaleR wdScale; positivity); obtain ⟨yw, _⟩ := hws
    obtain ⟨zg, zu, _, x3, _, zy, zdw, yb⟩ := yj hn hr2 y0 yw xk zai zaj zm y6
    obtain ⟨rfl, rfl, rfl, rfl, zbt, rfl, rfl⟩ := v6 yb y6
    have yp : yy = min (l0 * m) R.card := zbt.symm.trans (rkmb_natMin_eq (l0 * m) R.card)
    refine ⟨rfl, rfl, rfl, x3, yp, by rw [yp]; exact zy, zu, ?_⟩
    exact zdw.trans (qDL (by linarith) z4.le)
  | cons l1 lRest2 ih =>
    intro l0 t0 s0 mk0 w0 zx zi zl x6 yr _dPrev zk yy y8
      vec y9 v uIn hws xk zai zaj zm y6 hpadOut
    have z4 : (0 : ℝ) < qWR := (by unfold wdScaleR wdScale; positivity); obtain ⟨yw, xq⟩ := hws
    obtain ⟨zg, zu, ub, x3, vv, zy, xi, yb⟩ := yj hn hr2 y0 yw xk zai zaj zm y6
    set yg := qAM mk0 (qPZ w0.offOut w0.xsOut)
    obtain ⟨t1, zam, s1, zan, mk1, ud, w1, zao, rfl, rfl, rfl, rfl⟩ := yz yb y6
    obtain ⟨_, hl01, _, _, zap⟩ := zh yb y6; set v1 := qEM R (rkmSegOps n m R.card l0 t0 s0 mk0) v
    have vw : yg.length ≤ min (l1 * m) R.card + 1 :=
      zy.trans (by
        have zcq : l0 * m ≤ l1 * m := Nat.mul_le_mul_right m hl01
        have hmin : min (l0 * m) R.card ≤ min (l1 * m) R.card := le_min ((Nat.min_le_left _ _).trans
            zcq) (Nat.min_le_right _ _)
        omega)
    by_cases hEq : l0 = l1
    · subst hEq
      have zaq : qFN (v1 - qOE (2 ^ n) (l0 * m) R zu) + qVN (zu - qLO (min (l0 * m) R.card) yg) ≤
          ((zg : ℝ) + 1) / qWR := xi.trans (qDL (by linarith) z4.le)
      obtain ⟨zar, zas, zat, yv, xr, yl, yc, zcw⟩ := ih l0 t1 s1 mk1 w1 zam zan ud zao l0
          (highdNatMin (Nat.mul l0 m) R.card) zg yy y8 yg y9 v1 zu xq vv zy zaq yb y6 hpadOut
      refine ⟨congrArg Nat.succ zar, congrArg Nat.succ zas, congrArg Nat.succ zat, yv, xr, yl, yc,
          ?_⟩
      dsimp only [rkmBuildTailSegs, rkmEndL, rkmEvalSegs]; rw [dite_eq_left rfl]; exact zcw
    · have zau : l0 * m ≤ l1 * m := Nat.mul_le_mul_right m hl01
      have zcx : 2 * (l1 * m) ≤ 2 ^ n := (z9 hn zap y0).2.2.1
      set v2 := stepUpFrom (2 ^ n) (l0 * m) (l1 * m) *ᵥ v1
      set vf := zeroPadOrbVec (l0 * m) (l1 * m) R.card zu
      have u8 : qVN vf ≤ 1 := (by rw [vecNorm_zeroPadOrbVec zau]; exact vv)
      set vUp := stepUpFrom (2 ^ n) (l0 * m) (l1 * m) *ᵥ qOE (2 ^ n) (l0 * m) R zu
      have hiso : qFN (v2 - vUp) = qFN (v1 - qOE (2 ^ n) (l0 * m) R zu) := by
        dsimp only [v2, vUp]; rw [← Matrix.mulVec_sub, finVecNorm_mulVec_of_transpose_mul_self
            (stepUpFrom_transpose_mul_self zau zcx)]
      have zbu := finVecNorm_stepUpFrom_orbEmbedGen_sub_le hn ub zau zap (le_trans (by
          omega : 1 ≤ 2) hr2) y0 zu
      have vg : qFN (vUp - qOE (2 ^ n) (l1 * m) R vf) ≤ (1 / 2) / qWR := by
        have h1 : (1 / (2 * (qWN : ℝ))) * qVN zu ≤ (1 / (2 * (qWN : ℝ))) * 1 := qML vv (by
            unfold wdScale; positivity)
        exact zbu.trans (h1.trans_eq (by unfold wdScaleR; ring))
      have zbv : qFN (v2 - qOE (2 ^ n) (l1 * m) R vf) ≤ qFN (v1 - qOE (2 ^ n) (l0 * m) R zu) + (1 /
          2) / qWR := by
        have htr := finVecNorm_add_le (v2 - vUp) (vUp - qOE (2 ^ n) (l1 * m) R vf)
        rw [sub_add_sub_cancel] at htr; linarith [htr, hiso, vg]
      have zav : qVN (vf - qLO (min (l1 * m) R.card) yg) = qVN (zu - qLO (min (l0 * m) R.card)
          yg) := by
        dsimp only [vf]; rw [← y2 zau zy, ← yo, vecNorm_zeroPadOrbVec zau]
      have zaq : qFN (v2 - qOE (2 ^ n) (l1 * m) R vf) + qVN (vf - qLO (min (l1 * m) R.card) yg) ≤
          ((zg : ℝ) + 1) / qWR := by
        have hsum : ((zg : ℝ) - 252) / qWR + (1 / 2) / qWR ≤ ((zg : ℝ) + 1) / qWR := by
          rw [← add_div]; exact qDL (by linarith) z4.le
        linarith [zbv, zav, xi, hsum]
      obtain ⟨zar, zas, zat, yv, xr, yl, yc, zcw⟩ := ih l1 t1 s1 mk1 w1 zam zan ud zao l0
          (highdNatMin (Nat.mul l0 m) R.card) zg yy y8 yg y9 v2 vf xq u8 vw zaq yb y6 hpadOut
      refine ⟨congrArg Nat.succ zar, congrArg Nat.succ zas, congrArg Nat.succ zat, yv, xr, yl, yc,
          ?_⟩
      dsimp only [rkmBuildTailSegs, rkmEndL, rkmEvalSegs]; rw [dite_eq_right hEq]; exact zcw
/-- Certifies `RkmAnchorHitSound` from pre-certified windowed segment walks
  `RkmWinSegWalksSound`
  and `rkmCheckRowFromWinWalks`. -/
theorem rkmCheckRowFromWinWalks_sound {m z1 r : ℕ} {lSegs tauSegs nsubSegs : List ℕ} {masks : List
    (List Bool)} {walks : List RkmWinSegWalk} {rowOut : List ℕ} (zcy : RkmWinSegWalksSound nsubSegs
    walks) (zn : rkmCheckRowFromWinWalks m z1 r lSegs tauSegs nsubSegs masks walks rowOut = true) :
    RkmAnchorHitSound m ⟨r, lSegs, tauSegs, nsubSegs, masks, rowOut⟩ := by
  unfold rkmCheckRowFromWinWalks at zn
  have uh : qPB (altListLen rowOut) 1 = false :=
    z8 fun h ↦ by rw [h] at zn; exact Bool.noConfusion zn
  rw [uh] at zn; dsimp only at zn
  have ue : rowOut ≠ [] := (by intro zbw; subst zbw; exact Bool.noConfusion uh)
  have zd : rowOut = rkmEvalT16FromWinWalks m z1 r lSegs tauSegs nsubSegs masks walks :=
      (muxNatListEq_eq_true.mp zn).symm
  unfold rkmEvalT16FromWinWalks at zd; rw [rkmb_altListLen_eq] at zd; dsimp only at zd
  have hg0 : Bool.or (lSegs.length.beq 0) (Bool.or (qPB 8 lSegs.length) (Bool.or (qPB r 2)
      (qPB 1024 r))) = false := z8 fun h ↦ by rw [h] at zd; exact ue zd
  rw [hg0] at zd; simp only [Bool.or_eq_false_iff, rkmw_primNatBlt_eq_false] at hg0
  obtain ⟨uf_b, _, hr2, y0⟩ := hg0; have uf := rkmw_nat_beq_eq_false.mp uf_b
  rcases zm : qEW m z1 r lSegs tauSegs nsubSegs masks walks 1 0 0 [Int.ofNat qWN] with ⟨xx, zk, xt⟩
  rw [zm] at zd; dsimp only at zd
  have ug : Bool.or (xx.beq 0) (zk.beq 0) = false := z8 fun h ↦ by rw [h] at zd; exact ue zd
  rw [ug] at zd; simp only [Bool.or_eq_false_iff] at ug
  have xu := rkmw_nat_beq_eq_false.mp ug.1; have zbx := rkmw_nat_beq_eq_false.mp ug.2
  obtain ⟨lh, lt, rfl⟩ := yk lSegs fun h ↦ by rw [h] at uf; exact uf rfl
  obtain ⟨th, tt, sh, st, mkh, mkt, wh, wt, rfl, rfl, rfl, rfl⟩ := yz zm xu; intro n hn R hR w hw
  dsimp only [List.headD_cons, List.tail_cons, rkmLastNat] at hw ⊢
  obtain ⟨_, _, _, hmh1, zaw⟩ := zh zm xu; subst hR
  let z0 : Fin (orbDim (lh * m) R.card) := ⟨0, Nat.succ_pos _⟩
  let e0 : Fin (orbDim (lh * m) R.card) → ℝ := Pi.single z0 1
  have zax : qVN e0 ≤ 1 := by
    refine le_of_eq ?_; unfold vecNorm vecSqNorm; rw [Finset.sum_eq_single z0]
    · dsimp [e0]; rw [Pi.single_eq_same, one_pow, Real.sqrt_one]
    · intro b _ hb; dsimp [e0]; rw [Pi.single_eq_of_ne hb, zero_pow two_ne_zero]
    · intro hz; exact absurd (Finset.mem_univ z0) hz
  have zay : e0 = qLO (min (lh * m) R.card) [Int.ofNat qWN] := by
    funext ⟨j, hj⟩; rcases j with _ | j'
    · change e0 z0 = _; dsimp [e0]; rw [Pi.single_eq_same]
      unfold rkmListToOrbVec wdScaleR wdScale; norm_num
    · have zdz : (⟨j' + 1, hj⟩ : Fin (orbDim (lh * m) R.card)) ≠ z0 :=
        fun h ↦ Nat.succ_ne_zero j' (congrArg Fin.val h)
      dsimp only [e0]; unfold rkmListToOrbVec; rw [Pi.single_eq_of_ne zdz]; simp
  have zch : lh * m + R.card ≤ 2 ^ n := (z9 hn zaw y0).2.2.2
  have zby : qFN (u0Vec (2 ^ n) (lh * m) - qOE (2 ^ n) (lh * m) R e0) + qVN (e0 - qLO (min (lh * m)
      R.card) [Int.ofNat qWN]) ≤ (((0 : ℕ) : ℝ) + 1) / qWR := by
    rw [← zay, sub_self, vecNorm_zero, add_zero, ← orbEmbedGen_u0OrbVecGen zch, ← y5,
        finVecNorm_orbEmbedGen zch]
    have hb := vecNorm_u0OrbVecGen_sub_e0_le hn hmh1 zaw (le_trans (by omega : 1 ≤ 2) hr2) y0
    dsimp only at hb; exact hb.trans (by unfold wdScaleR wdScale; norm_num)
  obtain ⟨zar, zas, zat, yv, zaz, yl, yc, zba⟩ := y3 hn hr2 y0 rfl lt lh th sh mkh wh tt st mkt wt 1
      0 0 xx zk [Int.ofNat qWN] xt (u0Vec (2 ^ n) (lh * m)) e0 zcy zax (by simp) zby zm xu zbx
  subst zaz; simp only [Nat.add_eq] at zd
  have zbz : rkmEndL lh (qBT n m R.card lt tt st mkt) = rkmLastNat lh lt := (rkmLastNat_eq_endL n m
      R.card lt lh tt st mkt zar zas zat).symm
  rw [← zbz] at hw
  rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
  have zbb : rkmEndL lh (qBT n m R.card lt tt st mkt) * m + R.card ≤ 2 ^ n := (z9 hn yv y0).2.2.2
  set vEnd := rkmEvalSegs R lh (rkmSegOps n m R.card lh th sh mkh) (qBT n m R.card lt tt st mkt)
      (u0Vec (2 ^ n) (lh * m))
  let zca : Fin (orbDim (rkmEndL lh (qBT n m R.card lt tt st mkt) * m) R.card) := ⟨w,
      Nat.lt_succ_of_le hwd⟩
  have htail := rkmPadTailToLo12_sound (w := w) (sProb := √(symHitProb R vEnd w)) hw1 yl
      (Real.sqrt_nonneg _) zba
  dsimp only at htail
  rcases hpad : qPR
      (min (rkmEndL lh (qBT n m R.card lt tt st mkt) * m) R.card + 1) xt
      with _ | ⟨_, tl⟩
  · rw [hpad] at htail; dsimp only at htail; simp only [List.length_nil] at htail; omega
  rw [hpad] at zd htail; dsimp only at zd htail; rw [← zd] at htail
  have hp := symHitProb_orbEmbedGen zbb yc zca; dsimp only [zca] at hp
  have vx : √(symHitProb R (qOE (2 ^ n) _ R yc) w) = |yc zca| := (by rw [hp, Real.sqrt_sq_eq_abs])
  have vy := sqrt_symHitProb_ge_of_finVecNorm_sub_le R (qOE (2 ^ n) _ R yc) vEnd w; rw [vx] at vy
  have zcz := htail.2 zca rfl vy
    (by rw [htail.1]; exact Nat.sub_lt_left_of_lt_add hw1
          (by rw [Nat.add_comm]; exact Nat.lt_succ_of_le hwd))
  rwa [Real.sq_sqrt (by unfold symHitProb; positivity)] at zcz
/- ## Unwindowed Row Lift & Bound-Table Verification -/
private theorem ze {b : Bool} {x : ℕ × ℕ × List ℤ} (h : (cond b (0, 0, []) x).1 ≠ 0) : x.1 ≠ 0 := by
    cases b <;> simp_all
private theorem _cGuardNil {α : Type*} {b : Bool} {z : List α} (h : cond b [] z ≠ []) :
    b = false ∧ z ≠ [] := by cases b <;> simp_all
private theorem _cSplit {b x y : Bool} (h : cond b x y = true) :
    (b = true ∧ x = true) ∨ (b = false ∧ y = true) := by cases b <;> simp_all
private theorem zt (m z1 r : ℕ) : ∀ (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool)) (yr
    xx zk : ℕ) (vec : List ℤ), (qEL m z1 r lSegs tauSegs nsubSegs masks yr xx zk vec).1 ≠ 0 →
    lSegs.length = tauSegs.length ∧ lSegs.length = nsubSegs.length ∧ lSegs.length = masks.length
  | [], ts, ss, ms, _, _, _, _, h => by
    rcases ts with _ | _ <;> rcases ss with _ | _ <;> rcases ms with _ | _ <;>
      simp [rkmEvalSegsLoop] at h ⊢
  | _ :: _, [], _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | lS :: yi, _ :: zx, _ :: zi, _ :: zl, _, _, _, _, h => by
    unfold rkmEvalSegsLoop at h; dsimp only at h
    simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h; have hrec := ze (ze (ze (ze h)))
    obtain ⟨h1, h2, h3⟩ := zt m z1 r yi zx zi zl lS _ _ _ hrec
    exact ⟨congrArg Nat.succ h1, congrArg Nat.succ h2, congrArg Nat.succ h3⟩
/-- Lifts an unwindowed `rkmLo12EqHi` trajectory equality to `RkmAnchorHitSound`. -/
theorem rkmAnchorHitSound_of_lo12Eq {m z1 r : ℕ} {lSegs tauSegs nsubSegs : List ℕ} {masks : List
    (List Bool)} {rowLo12 : List ℕ} (h : rkmLo12EqHi m z1 r lSegs tauSegs nsubSegs masks rowLo12) :
    RkmAnchorHitSound m ⟨r, lSegs, tauSegs, nsubSegs, masks, rowLo12⟩ := by
  intro n hn R hR w hw
  by_cases zbw : rowLo12 = []
  · subst zbw; simp only [List.getD_nil, Nat.cast_zero, zero_div]; unfold symHitProb; positivity
  · have hne : rkmEvalT16Lo12 m z1 r lSegs tauSegs nsubSegs masks ≠ [] := (by rw [h]; exact zbw)
    have x7 : lSegs.length = tauSegs.length ∧ lSegs.length = nsubSegs.length ∧ lSegs.length =
        masks.length := by
      unfold rkmEvalT16Lo12 at hne; dsimp only at hne
      replace hne := (_cGuardNil hne).2
      rcases zm : qEL m z1 r lSegs tauSegs nsubSegs masks 1 0 0 [Int.ofNat qWN] with ⟨xx, zk, xt⟩
      rw [zm] at hne; dsimp only at hne
      have zeb : xx ≠ 0 := rkmw_nat_beq_eq_false.mp (Bool.or_eq_false_iff.mp (_cGuardNil hne).1).1
      exact zt m z1 r lSegs tauSegs nsubSegs masks 1 0 0 [Int.ofNat qWN] (by rw [zm]; exact zeb)
    have zda := rkmEvalT16Lo12_sound hn hne hR; dsimp only at zda hw ⊢
    obtain ⟨lh, lt, rfl⟩ := yk lSegs fun hh ↦ by
      rw [hh] at hne; unfold rkmEvalT16Lo12 at hne; simp [altListLen] at hne
    obtain ⟨th, tt, rfl⟩ := yk tauSegs fun hh ↦ by rw [hh] at x7; simp at x7
    obtain ⟨sh, st, rfl⟩ := yk nsubSegs fun hh ↦ by rw [hh] at x7; simp at x7
    obtain ⟨mkh, mkt, rfl⟩ := yk masks fun hh ↦ by rw [hh] at x7; simp at x7
    dsimp only [List.headD_cons, List.tail_cons, rkmLastNat] at zda hw ⊢
    have hend := (rkmLastNat_eq_endL n m r lt lh tt st mkt (Nat.succ.inj x7.1) (Nat.succ.inj x7.2.1)
        (Nat.succ.inj x7.2.2)).symm
    rw [← hend] at hw; have zec := zda.2.2.2.2.2 w hw; rwa [h] at zec
private theorem zr {g x : Bool} (h : cond g false x = true) : g = false ∧ x = true := by
  cases g <;> cases x <;> simp_all
private theorem zs {g x : Bool} (h : cond g x false = true) : g = true ∧ x = true := by
  cases g <;> cases x <;> simp_all
private theorem yf {m z1 s : ℕ} {lSegs tauSegs vPot rowLo12 yd : List ℕ} (vh : ∀ j < s, yd.getD j 0
  =
    vPot.getD (s - 1 - j) 0) (h : rkmCheckDrift m z1 s lSegs tauSegs (vPot.getD s 0) (muxRunningCap
    vPot s) rowLo12 yd = true) : RampKickActiveValid m z1 s vPot lSegs tauSegs rowLo12 := by
  unfold RampKickActiveValid; dsimp only; unfold rkmCheckDrift at h; dsimp only at h
  rw [rkmb_altListLen_eq lSegs] at h; obtain ⟨hg1, h⟩ := zr h
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkmw_primNatBlt_eq_false] at hg1
  obtain ⟨hn1, hn8, _, zbc⟩ := hg1; set lEnd := rkmLastNat 0 lSegs
  rw [show Nat.mul lEnd m = lEnd * m from rfl, rkmb_natMin_eq (lEnd * m) s] at h
  set xx := min (lEnd * m) s; obtain ⟨hg2, h⟩ := zr h
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkmw_nat_beq_eq_true,
      rkmw_primNatBlt_eq_false, rkmb_altListLen_eq] at hg2
  obtain ⟨zbd, zed, zcb, zdb⟩ := hg2; have hlt := rkmw_primNatBlt_eq_true.mp h
  rw [muxHitValSum27_eq_sum_range xx rowLo12 yd zbd zdb] at hlt
  have ve : (∑ j ∈ Finset.range xx, rowLo12.getD j 0 * yd.getD j 0) = ∑ j ∈ Finset.range xx,
      rowLo12.getD j 0 * vPot.getD (s - 1 - j) 0 := Finset.sum_congr rfl fun j hj ↦ by
      rw [vh j ((Finset.mem_range.mp hj).trans_le (Nat.min_le_right _ _))]
  rw [ve] at hlt; refine ⟨hn1, hn8, zbc, zbd, zed, zcb, ?_⟩
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ← add_assoc] at hlt; exact hlt
private theorem zq : ∀ (za : List RampKickAnchor) (s : ℕ), (∀ a ∈ za, s < a.rAct) → rkmFindAnchor s
    za = none
  | [], _, _ => rfl
  | a :: xw, s, hgt => by
    have hsa : a.rAct ≠ s := (by have := hgt a List.mem_cons_self; omega)
    unfold rkmFindAnchor; rw [ite_eq_right hsa]
    exact zq xw s (fun b hb ↦ hgt b (List.mem_cons_of_mem _ hb))
private theorem zo : ∀ (um : List ℕ) (m z1 : ℕ) (useColdR2 : Bool) (r vz : ℕ) (yd : List ℕ) (za :
    List RampKickAnchor), qCT m z1 useColdR2 um r vz yd za = true → ∀ a ∈ za, r ≤ a.rAct
  | [], _, _, _, _, _, _, za, h, _, ha => by
    cases za with | nil => nomatch ha | cons _ _ => simp [rkmCheckTableAux] at h
  | vR :: ym, m, z1, useColdR2, r, vz, yd, za, h, b, hb => by
    cases yd with
    | nil => simp [rkmCheckTableAux] at h
    | cons v3 vi =>
      unfold rkmCheckTableAux at h; simp only [rkmb_forceNat_eq] at h
      cases za with
      | nil => nomatch hb
      | cons a xj =>
        dsimp only at h; obtain ⟨hlt, h⟩ := zr h
        have hra : r ≤ a.rAct := rkmw_primNatBlt_eq_false.mp hlt
        rcases _cSplit h with ⟨_, h⟩ | ⟨_, h⟩
        · obtain ⟨_, h⟩ := zs h; rcases List.mem_cons.mp hb with rfl | hmem
          · exact hra
          · exact (Nat.le_succ r).trans (zo ym m z1 useColdR2 (r + 1) _ _ xj h b hmem)
        · exact (Nat.le_succ r).trans (zo ym m z1 useColdR2 (r + 1) _ _ (a :: xj) (zs h).2 b hb)
private theorem xd (a b : ℕ) : cond (qPB a b) b a = max a b := by
  cases h : qPB a b
  · simp [cond, Nat.max_eq_left (rkmw_primNatBlt_eq_false.mp h)]
  · simp [cond, Nat.max_eq_right (rkmw_primNatBlt_eq_true.mp h).le]
private theorem zw (m z1 : ℕ) (useColdR2 : Bool) (vPot : List ℕ) : ∀ (um : List ℕ) (r : ℕ) (yd :
  List
    ℕ) (za : List RampKickAnchor), 1 ≤ r → yd.getD 0 0 = vPot.getD (r - 1) 0 → 1 ≤ yd.length → (∀ j
      <
    r, yd.getD j 0 = vPot.getD (r - 1 - j) 0) → (∀ j < um.length, um.getD j 0 = vPot.getD (r + j) 0)
      →
    RkmAnchorsHitSound m z1 za → qCT m z1 useColdR2 um r (muxRunningCap vPot (r - 1)) yd za = true →
    ∀ s : ℕ, r ≤ s → s < r + um.length →
        match rkmFindAnchor s za with
        | none =>
            (s = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨ checkEigStep
              m
                s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
        | some a => a.rAct = s ∧ RkmAnchorHitSound m a ∧
            RampKickActiveValid m z1 s vPot a.lSegs a.tauSegs a.rowLo12
  | [], _, _, _, _, _, _, _, _, _, _, _, _, hslt => by simp at hslt; omega
  | vR :: ym, r, yd, za, hr1, hvh0, hvh_len, vh, hvrem_eq, hasound, zn,
      s, hrs, hslt => by
    rcases yd with _ | ⟨v3, vi⟩
    · simp at hvh_len
    · have xe : vR = vPot.getD r 0 := (by simpa using hvrem_eq 0 (Nat.succ_pos _))
      have un : v3 = vPot.getD (r - 1) 0 := (by simpa using hvh0)
      have zcc : max (muxRunningCap vPot (r - 1)) vR = muxRunningCap vPot r := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp [muxRunningCap, xe]
      have zbe : ∀ j < r + 1, (vR :: v3 :: vi).getD j 0 = vPot.getD (r - j) 0 := by
        intro j hj; rcases j with _ | j'
        · simp [xe]
        · rw [List.getD_cons_succ, vh j' (by omega)]; congr 1; omega
      have u9 : ∀ j < ym.length, ym.getD j 0 = vPot.getD (r + 1 + j) 0 := fun j hj ↦ by
        simpa [show r + (j + 1) = r + 1 + j by omega] using hvrem_eq (j + 1) (by simp; omega)
      unfold rkmCheckTableAux at zn; simp only [rkmb_forceNat_eq, xd, zcc] at zn
      have u0 (hfb : cond (Bool.and (r.beq 2) useColdR2) (rkmCheckColdR2Step m vR) (checkEigStep
          m r vR v3) = true) : (r = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) =
          true) ∨ checkEigStep m r (vPot.getD r 0) (vPot.getD (r - 1) 0) = true := by
        rcases _cSplit hfb with ⟨v4, hfb⟩ | ⟨_, hfb⟩
        · simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true] at v4
          exact Or.inl ⟨v4.1, v4.2, by simpa [v4.1, xe] using hfb⟩
        · exact Or.inr (by simpa [xe, un] using hfb)
      have zdc (as' : List RampKickAnchor) (hs' : RkmAnchorsHitSound m z1 as') (hc' : qCT m z1
          useColdR2 ym (Nat.add r 1) (muxRunningCap vPot r) (vR :: v3 :: vi) as' = true) (hne : s ≠
          r) := zw m z1 useColdR2 vPot ym (r + 1) (vR :: v3 :: vi) as' (by omega) (by simp [xe]) (by
          simp) (fun j hj ↦ by simpa [Nat.add_sub_cancel] using zbe j hj) u9 hs' (by
          simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hc') s (by omega) (by
          simp only [List.length_cons] at hslt; omega)
      rcases za with _ | ⟨a, xj⟩
      · dsimp only at zn; obtain ⟨hfb, zn⟩ := zs zn
        by_cases hsr : s = r
        · subst hsr; simpa [rkmFindAnchor] using u0 hfb
        · exact zdc [] trivial zn hsr
      · dsimp only at zn; obtain ⟨_, zn⟩ := zr zn
        rcases _cSplit zn with ⟨heq, zn⟩ | ⟨_, zn⟩
        · obtain ⟨hdr, zn⟩ := zs zn
          have zbf : a.rAct = r := rkmw_nat_beq_eq_true.mp heq; obtain ⟨zdd, u1⟩ := hasound
          by_cases hsr : s = r
          · subst hsr; unfold rkmFindAnchor; rw [ite_eq_left zbf]; dsimp only
            rw [xe] at hdr; exact ⟨zbf, zdd, yf vh hdr⟩
          · unfold rkmFindAnchor; rw [ite_eq_right (by omega : a.rAct ≠ s)]; exact zdc xj u1 zn hsr
        · obtain ⟨hfb, zn⟩ := zs zn; by_cases hsr : s = r
          · subst hsr; have zcd : ∀ b ∈ a :: xj, s < b.rAct := fun b hb ↦ by
              have hge := zo ym m z1 useColdR2 (s + 1) _ _ (a :: xj)
                (by simpa [show Nat.add s 1 = s + 1 from rfl] using zn) b hb; omega
            rw [zq (a :: xj) s zcd]; exact u0 hfb
          · exact zdc (a :: xj) hasound zn hsr
/-- Turns `rkmCheckTable... = true` and `RkmAnchorsHitSound` into `RampKickTableBoundValid`. -/
theorem rkmCheckTable_bound_sound {m kMax z1 : ℕ} {useColdR2 : Bool} {vPot : List ℕ} {za : List
    RampKickAnchor} (zn : rkmCheckTable m kMax z1 useColdR2 vPot za = true) (zde :
      RkmAnchorsHitSound
    m z1 za) : RampKickTableBoundValid m kMax z1 useColdR2 vPot za := by
  unfold rkmCheckTable at zn; rw [rkmb_altListLen_eq] at zn; obtain ⟨hg1, zn⟩ := zr zn
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkmw_primNatBlt_eq_false,
      rkmw_nat_beq_eq_true] at hg1
  obtain ⟨hm1, hlMax1, hlMax_hi, hk2, zdf, hv_len⟩ := hg1
  rcases hv_cases : vPot with _ | ⟨v0, _ | ⟨v1, ym⟩⟩
  · rw [hv_cases] at hv_len; simp at hv_len
  · rw [hv_cases] at hv_len; simp [Nat.add_eq] at hv_len; omega
  · rw [hv_cases] at zn hv_len; dsimp only at zn; obtain ⟨zbg, zn⟩ := zr zn
    simp only [Bool.not_eq_false', rkmw_nat_beq_eq_true] at zbg; obtain ⟨heig1, zn⟩ := zs zn
    have zee : muxRunningCap (v0 :: v1 :: ym) 1 = v1 := Nat.max_eq_right (zbg ▸ Nat.zero_le v1)
    have zdh : ym.length = kMax - 1 := (by simp [Nat.add_eq] at hv_len; omega)
    have hrows := zw m z1 useColdR2 (v0 :: v1 :: ym) ym 2 [v1, v0] za (by omega) rfl (by simp) (fun
        j hj ↦ by rcases j with _ | _ | _ <;> first | rfl | omega) (fun j _ ↦ by
        rw [show 2 + j = (j + 1) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]) zde (by
        simpa [zee] using zn)
    exact ⟨hm1, hlMax1, hlMax_hi, hk2, zdf, hv_len, zbg, heig1,
      fun s hs2 hsk ↦ hrows s hs2 (by omega)⟩
end
end Sec_FindAllJohnsonRampKickMuxHiWin
end QuantumComputation.Specs.DickeSol
