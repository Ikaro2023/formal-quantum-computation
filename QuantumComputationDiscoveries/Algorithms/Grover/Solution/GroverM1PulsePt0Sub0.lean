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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulseTable
/-
# `m = 1` Multi-Pulse WKB Certificates (`GroverM1PulsePt0Sub0`)
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.GroverM1PulsePt0
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
  (IvInt swScale ceilDivScaleP ivAddIntP ivSubIntP headIvP)
open QuantumComputation.Specs.GroverFindAll.PulseM1
open QuantumComputation.Specs.GroverFindAll.GroverM1PulseTable
/-- Atomic-WHNF `10^9`-scale quotient interval constructor (`= (loProd / S, ⌈hiProd / S⌉)`). -/
def solFastScaleDivIv (loProd hiProd : ℤ) : IvInt :=
  solSeqInt (Int.ediv loProd swScale) fun qLo ↦
    solSeqInt (ceilDivScaleP hiProd) fun qHi ↦ (qLo, qHi)
private theorem solFastScaleDivIv_eq (loProd hiProd : ℤ) :
    solFastScaleDivIv loProd hiProd = (Int.ediv loProd swScale, ceilDivScaleP hiProd) := by
  simp only [solFastScaleDivIv, solSeqInt_eq]
private theorem solIvMul_unfold (a b : IvInt) : solIvMul a b =
      (Int.ediv (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2))) swScale,
       ceilDivScaleP (max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))) := by
  unfold solIvMul; simp only [solSeqInt_eq, solMinZ_eq, solMaxZ_eq, solIntMul_eq]
private theorem solFastScaleDivIv_eq_solIvMul {a b : IvInt} {lo hi : ℤ} (hlo_le : lo ≤ a.1 * b.1 ∧
    lo ≤ a.1 * b.2 ∧ lo ≤ a.2 * b.1 ∧ lo ≤ a.2 * b.2) (hlo_mem : lo = a.1 * b.1 ∨ lo = a.1 * b.2 ∨
    lo = a.2 * b.1 ∨ lo = a.2 * b.2) (hhi_ge : a.1 * b.1 ≤ hi ∧ a.1 * b.2 ≤ hi ∧ a.2 * b.1 ≤ hi ∧
    a.2 * b.2 ≤ hi) (hhi_mem : hi = a.1 * b.1 ∨ hi = a.1 * b.2 ∨ hi = a.2 * b.1 ∨ hi = a.2 * b.2) :
    solFastScaleDivIv lo hi = solIvMul a b := by
  rw [solFastScaleDivIv_eq, solIvMul_unfold]
  have hmin : lo = min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)) := by
    refine le_antisymm (le_min (le_min hlo_le.1 hlo_le.2.1) (le_min hlo_le.2.2.1 hlo_le.2.2.2)) ?_
    rcases hlo_mem with h | h | h | h <;> rw [h]
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmax : hi = max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)) := by
    refine le_antisymm ?_ (max_le (max_le hhi_ge.1 hhi_ge.2.1) (max_le hhi_ge.2.2.1 hhi_ge.2.2.2))
    rcases hhi_mem with h | h | h | h <;> rw [h]
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  rw [← hmin, ← hmax]
/-- Sign-dispatched `10^9`-scale interval multiplication (`= solIvMul`). -/
def solFastIvMul (a b : IvInt) : IvInt := cond (solBleZ a.1 a.2 && solBleZ b.1 b.2)
    (cond (solBleZ 0 a.1) (cond (solBleZ 0 b.1)
        (solFastScaleDivIv (Int.mul a.1 b.1) (Int.mul a.2 b.2)) (cond (solBleZ b.2 0)
          (solFastScaleDivIv (Int.mul a.2 b.1) (Int.mul a.1 b.2))
          (solFastScaleDivIv (Int.mul a.2 b.1) (Int.mul a.2 b.2))))
      (cond (solBleZ a.2 0) (cond (solBleZ 0 b.1)
          (solFastScaleDivIv (Int.mul a.1 b.2) (Int.mul a.2 b.1)) (cond (solBleZ b.2 0)
            (solFastScaleDivIv (Int.mul a.2 b.2) (Int.mul a.1 b.1))
            (solFastScaleDivIv (Int.mul a.1 b.2) (Int.mul a.1 b.1))))
        (solIvMul a b)))
    (solIvMul a b)
private theorem solFastIvMul_eq (a b : IvInt) : solFastIvMul a b = solIvMul a b := by
  unfold solFastIvMul; by_cases hab : (solBleZ a.1 a.2 && solBleZ b.1 b.2) = true
  · rw [hab, Bool.cond_true]
    rw [Bool.and_eq_true, solBleZ_eq_decide, solBleZ_eq_decide, decide_eq_true_eq,
      decide_eq_true_eq] at hab
    rcases hab with ⟨ha, hb⟩; simp only [solBleZ_eq_decide, solIntMul_eq]; by_cases ha0 : 0 ≤ a.1
    · have ha2 : 0 ≤ a.2 := le_trans ha0 ha; simp only [ha0, decide_true, Bool.cond_true]
      by_cases hb0 : 0 ≤ b.1
      · have hb2 : 0 ≤ b.2 := le_trans hb0 hb; have h12 := mul_le_mul_of_nonneg_left hb ha0
        have h13 := mul_le_mul_of_nonneg_right ha hb0
        have h24 := mul_le_mul_of_nonneg_right ha hb2; have h34 := mul_le_mul_of_nonneg_left hb ha2
        have h14 := le_trans h12 h24; simp only [hb0, decide_true, Bool.cond_true]
        exact solFastScaleDivIv_eq_solIvMul ⟨le_rfl, h12, h13, h14⟩ (Or.inl rfl)
          ⟨h14, h24, h34, le_rfl⟩ (Or.inr (Or.inr (Or.inr rfl)))
      · simp only [hb0, decide_false, Bool.cond_false]; by_cases hb2 : b.2 ≤ 0
        · have hb1 : b.1 ≤ 0 := le_trans hb hb2; have h31 := mul_le_mul_of_nonpos_right ha hb1
          have h34 := mul_le_mul_of_nonneg_left hb ha2; have h12 := mul_le_mul_of_nonneg_left hb ha0
          have h42 := mul_le_mul_of_nonpos_right ha hb2; have h32 := le_trans h34 h42
          simp only [hb2, decide_true, Bool.cond_true]
          exact solFastScaleDivIv_eq_solIvMul ⟨h31, h32, le_rfl, h34⟩ (Or.inr (Or.inr (Or.inl rfl)))
            ⟨h12, le_rfl, h32, h42⟩ (Or.inr (Or.inl rfl))
        · have hb1 : b.1 ≤ 0 := le_of_not_ge hb0; have hb2' : 0 ≤ b.2 := le_of_not_ge hb2
          have h31 := mul_le_mul_of_nonpos_right ha hb1
          have h34 := mul_le_mul_of_nonneg_left hb ha2; have h12 := mul_le_mul_of_nonneg_left hb ha0
          have h24 := mul_le_mul_of_nonneg_right ha hb2'; have h32 := le_trans h31 h12
          have h14 := le_trans h12 h24; simp only [hb2, decide_false, Bool.cond_false]
          exact solFastScaleDivIv_eq_solIvMul ⟨h31, h32, le_rfl, h34⟩ (Or.inr (Or.inr (Or.inl rfl)))
            ⟨h14, h24, h34, le_rfl⟩ (Or.inr (Or.inr (Or.inr rfl)))
    · simp only [ha0, decide_false, Bool.cond_false]; by_cases ha2 : a.2 ≤ 0
      · have ha1 : a.1 ≤ 0 := le_trans ha ha2; simp only [ha2, decide_true, Bool.cond_true]
        by_cases hb0 : 0 ≤ b.1
        · have hb2 : 0 ≤ b.2 := le_trans hb0 hb; have h21 := mul_le_mul_of_nonpos_left hb ha1
          have h24 := mul_le_mul_of_nonneg_right ha hb2
          have h13 := mul_le_mul_of_nonneg_right ha hb0
          have h43 := mul_le_mul_of_nonpos_left hb ha2; have h23 := le_trans h24 h43
          simp only [hb0, decide_true, Bool.cond_true]
          exact solFastScaleDivIv_eq_solIvMul ⟨h21, le_rfl, h23, h24⟩ (Or.inr (Or.inl rfl))
            ⟨h13, h23, le_rfl, h43⟩ (Or.inr (Or.inr (Or.inl rfl)))
        · simp only [hb0, decide_false, Bool.cond_false]; by_cases hb2 : b.2 ≤ 0
          · have hb1 : b.1 ≤ 0 := le_trans hb hb2; have h42 := mul_le_mul_of_nonpos_right ha hb2
            have h43 := mul_le_mul_of_nonpos_left hb ha2
            have h21 := mul_le_mul_of_nonpos_left hb ha1
            have h31 := mul_le_mul_of_nonpos_right ha hb1; have h41 := le_trans h42 h21
            simp only [hb2, decide_true, Bool.cond_true]
            exact solFastScaleDivIv_eq_solIvMul ⟨h41, h42, h43, le_rfl⟩ (Or.inr (Or.inr (Or.inr
              rfl))) ⟨le_rfl, h21, h31, h41⟩ (Or.inl rfl)
          · have hb1 : b.1 ≤ 0 := le_of_not_ge hb0; have hb2' : 0 ≤ b.2 := le_of_not_ge hb2
            have h21 := mul_le_mul_of_nonpos_left hb ha1
            have h24 := mul_le_mul_of_nonneg_right ha hb2'
            have h43 := mul_le_mul_of_nonpos_left hb ha2
            have h31 := mul_le_mul_of_nonpos_right ha hb1; have h23 := le_trans h24 h43
            have h41 := le_trans h43 h31; simp only [hb2, decide_false, Bool.cond_false]
            exact solFastScaleDivIv_eq_solIvMul ⟨h21, le_rfl, h23, h24⟩ (Or.inr (Or.inl rfl))
              ⟨le_rfl, h21, h31, h41⟩ (Or.inl rfl)
      · simp only [ha2, decide_false, Bool.cond_false]
  · rw [Bool.eq_false_iff.mpr hab, Bool.cond_false]
/-- Atomic-WHNF `10^9`-scale interval-by-scalar multiplication (`= solIvScaleZ`). -/
def solFastIvScaleZ (a : IvInt) (c : ℤ) : IvInt :=
  solSeqInt (Int.mul a.1 c) fun p1 ↦
    solSeqInt (Int.mul a.2 c) fun p2 ↦
      cond (solBleZ p1 p2) (solFastScaleDivIv p1 p2) (solFastScaleDivIv p2 p1)
private theorem solFastIvScaleZ_eq (a : IvInt) (c : ℤ) : solFastIvScaleZ a c = solIvScaleZ a c := by
  unfold solFastIvScaleZ solIvScaleZ; simp only [solSeqInt_eq, solFastScaleDivIv_eq]
/-- Single-stratum Grover rotation step with flat `solSeqIv` CPS sharing. -/
def solFastGroverStep (cw sw : IvInt) (ce co : ℤ) (rest : List IvInt) : List IvInt :=
  cond (solBeqZ ce 0 && solBeqZ co 0) ((0, 0) :: (0, 0) :: rest)
    (solSeqIv (solFastIvScaleZ cw ce) fun cwe ↦
      solSeqIv (solFastIvScaleZ sw co) fun swo ↦
        solSeqIv (solFastIvScaleZ sw ce) fun swe ↦
          solSeqIv (solFastIvScaleZ cw co) fun cwo ↦
            solSeqIv (ivSubIntP cwe swo) fun e' ↦
              solSeqIv (ivAddIntP swe cwo) fun o' ↦ e' :: o' :: rest)
/-- Structural multi-stratum Grover rotation walk (`= solGroverWalk`). -/
def solFastGroverWalk : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, (cw, sw) :: ts', ce :: co :: cs' =>
      solFastGroverStep cw sw ce co (solFastGroverWalk k ts' cs')
  | k + 1, (cw, sw) :: ts', [ce] =>
      solFastGroverStep cw sw ce 0 (solFastGroverWalk k ts' [])
  | k + 1, _ :: ts', [] =>
      (0, 0) :: (0, 0) :: solFastGroverWalk k ts' []
  | k + 1, [], ce :: co :: cs' =>
      solFastGroverStep (0, 0) (0, 0) ce co (solFastGroverWalk k [] cs')
  | k + 1, [], [ce] =>
      solFastGroverStep (0, 0) (0, 0) ce 0 (solFastGroverWalk k [] [])
  | k + 1, [], [] =>
      (0, 0) :: (0, 0) :: solFastGroverWalk k [] []
private theorem solFastGroverWalk_eq : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ),
      solFastGroverWalk k ts cs = solGroverWalk k ts cs
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
      have hz0 : (solBeqZ 0 0 && solBeqZ 0 0) = true := rfl
      rcases ts with _ | ⟨⟨cw, sw⟩, ts'⟩ <;> rcases cs with _ | ⟨ce, _ | ⟨co, cs'⟩⟩ <;>
        simp only [solFastGroverWalk, solFastGroverStep, solGroverWalk, solSeqList_eq,
          solSeqIv_eq, solFastIvScaleZ_eq, SchurWeylLCert.headZP, SchurWeylLCert.secondZP,
          SchurWeylLCert.drop2ZP, SchurWeylLCert.headTrigP, SchurWeylLCert.drop1TrigP,
          hz0, Bool.cond_true, solFastGroverWalk_eq k]
/-- Single-stratum Pieri mixing step with flat `solSeqIv` CPS sharing. -/
def solFastPieriPair (uvDenZ u : ℤ) (lv rv : IvInt) (rest : List IvInt) : List IvInt :=
  cond (solBeqZ u 0) (lv :: rv :: rest)
    (cond (solIvIsZero lv && solIvIsZero rv) ((0, 0) :: (0, 0) :: rest)
      (match solIvPythag u uvDenZ with
      | (cu, su) =>
          solSeqIv (solFastIvMul cu lv) fun cl ↦
            solSeqIv (solFastIvMul su rv) fun sr ↦
              solSeqIv (solFastIvMul su lv) fun sl ↦
                solSeqIv (solFastIvMul cu rv) fun cr ↦
                  solSeqIv (ivSubIntP cl sr) fun l' ↦
                    solSeqIv (ivAddIntP sl cr) fun r' ↦ l' :: r' :: rest))
private theorem solFastPieriPair_eq (uvDenZ u : ℤ) (lv rv : IvInt) (rest1 rest2 : List IvInt)
    (hr : rest1 = rest2) : solFastPieriPair uvDenZ u lv rv rest1 =
      (cond (solBeqZ u 0) (lv :: rv :: rest2)
        (cond (solIvIsZero lv && solIvIsZero rv) ((0, 0) :: (0, 0) :: rest2)
          (match solIvPythag u uvDenZ with
          | (cu, su) =>
              solSeqIv (ivSubIntP (solIvMul cu lv) (solIvMul su rv)) fun l' ↦
                solSeqIv (ivAddIntP (solIvMul su lv) (solIvMul cu rv)) fun r' ↦
                  l' :: r' :: rest2))) := by
  subst hr; unfold solFastPieriPair
  rcases solIvPythag u uvDenZ with ⟨cu, su⟩; simp only [solSeqIv_eq, solFastIvMul_eq]
/-- Auxiliary structural Pieri walk across active window (`= solPieriWalkAux`). -/
def solFastPieriWalkAux (uvDenZ : ℤ) (cv : IvInt) : ℕ → ℕ → List ℤ → List IvInt → List IvInt
  | 0, _, _, ss =>
      solSeqIv (headIvP ss) fun lastIv ↦ solSeqIv
          (cond ((solBeqZ cv.1 swScale && solBeqZ cv.2 swScale) || solIvIsZero lastIv) lastIv
            (solFastIvMul cv lastIv))
          fun outIv ↦ [outIv]
  | m + 1, s + 1, us, lv :: rv :: ss' =>
      lv :: rv :: solFastPieriWalkAux uvDenZ cv m s us ss'
  | m + 1, s + 1, us, [lv] =>
      lv :: (0, 0) :: solFastPieriWalkAux uvDenZ cv m s us []
  | m + 1, s + 1, us, [] =>
      (0, 0) :: (0, 0) :: solFastPieriWalkAux uvDenZ cv m s us []
  | m + 1, 0, [], lv :: rv :: ss' =>
      lv :: rv :: solFastPieriWalkAux uvDenZ cv m 0 [] ss'
  | m + 1, 0, [], [lv] =>
      lv :: (0, 0) :: solFastPieriWalkAux uvDenZ cv m 0 [] []
  | m + 1, 0, [], [] =>
      (0, 0) :: (0, 0) :: solFastPieriWalkAux uvDenZ cv m 0 [] []
  | m + 1, 0, u :: us', lv :: rv :: ss' =>
      solFastPieriPair uvDenZ u lv rv (solFastPieriWalkAux uvDenZ cv m 0 us' ss')
  | m + 1, 0, u :: us', [lv] =>
      solFastPieriPair uvDenZ u lv (0, 0) (solFastPieriWalkAux uvDenZ cv m 0 us' [])
  | m + 1, 0, u :: us', [] =>
      solFastPieriPair uvDenZ u (0, 0) (0, 0) (solFastPieriWalkAux uvDenZ cv m 0 us' [])
private theorem solFastPieriWalkAux_eq (uvDenZ : ℤ) (cv : IvInt) : ∀ (m sk : ℕ) (us : List ℤ) (ss :
    List IvInt), solFastPieriWalkAux uvDenZ cv m sk us ss = solPieriWalkAux uvDenZ cv m sk us ss
  | 0, _, _, ss => by simp only [solFastPieriWalkAux, solPieriWalkAux, solSeqIv_eq, solFastIvMul_eq]
  | m + 1, sk, us, ss => by
      rcases sk with _ | s <;> rcases us with _ | ⟨u, us'⟩ <;>
        rcases ss with _ | ⟨lv, _ | ⟨rv, ss'⟩⟩ <;>
        simp only [solFastPieriWalkAux, solPieriWalkAux, solSeqList_eq, headIvP,
          SchurWeylLCert.secondIvP, SchurWeylLCert.drop2IvP,
          solFastPieriWalkAux_eq uvDenZ cv m, solFastPieriPair_eq _ _ _ _ _ _ rfl]
/-- Window-sparse Pieri walk wrapper (`= solPieriWalk`). -/
def solFastPieriWalk (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse)
    (naIv : List IvInt) : List IvInt :=
  match hNext, naIv with
  | 0, _ => []
  | m + 1, h0 :: ss =>
      h0 :: solFastPieriWalkAux (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin ss
  | m + 1, [] =>
      (0, 0) :: solFastPieriWalkAux (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin []
private theorem solFastPieriWalk_eq (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse)
    (naIv : List IvInt) :
    solFastPieriWalk hNext uvDen cv sp naIv = solPieriWalk hNext uvDen cv sp naIv := by
  rcases hNext with _ | m <;> rcases naIv with _ | ⟨h0, ss⟩ <;>
    simp only [solFastPieriWalk, solPieriWalk, solSeqList_eq, headIvP,
      SchurWeylLCert.drop1IvP, solFastPieriWalkAux_eq]
/-- Interval midpoint recentering and squared-radius sum (`= solRecenterAndRadSq`). -/
def solFastRecenterAndRadSq : List IvInt → List ℤ × ℕ
  | [] => ([], 0)
  | iv :: ivs =>
      match solIvMidRad iv, solFastRecenterAndRadSq ivs with
      | (mid, rad), (cs, acc) =>
          solLitNat (Nat.add (Nat.mul rad rad) acc) fun acc' ↦ (mid :: cs, acc')
private theorem solFastRecenterAndRadSq_eq :
    ∀ (ivs : List IvInt), solFastRecenterAndRadSq ivs = solRecenterAndRadSq ivs
  | [] => rfl
  | iv :: ivs => by
      unfold solFastRecenterAndRadSq solRecenterAndRadSq; rw [solFastRecenterAndRadSq_eq ivs]
      rcases solIvMidRad iv with ⟨mid, rad⟩
      rcases solRecenterAndRadSq ivs with ⟨cs, acc⟩; simp only [solSeqInt_eq]
/-- Trailing zero-pair trimmer on `List ℤ` (`= solTrimZeroPairs`). -/
def solFastTrimZeroPairs : List ℤ → List ℤ
  | x :: y :: rest =>
      match solFastTrimZeroPairs rest with
      | [] =>
          cond (solBeqZ x 0 && solBeqZ y 0) [] [x, y]
      | z :: zs =>
          x :: y :: z :: zs
  | _ => []
private theorem solFastTrimZeroPairs_eq :
    ∀ (cs : List ℤ), solFastTrimZeroPairs cs = solTrimZeroPairs cs
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
      unfold solFastTrimZeroPairs solTrimZeroPairs; rw [solFastTrimZeroPairs_eq rest]
      rcases solTrimZeroPairs rest with _ | ⟨z, zs⟩ <;> simp only [solSeqInt_eq]
/-- Single-pulse causal `L2Ball` evolution step (`= solPulseStepL2`). -/
def solFastPulseStepL2 (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) (sp : SolSparsePulse) : List ℤ × ℕ × ℕ × ℤ :=
  solLitNat (solSumSqAbs cPref 0) fun normSqC ↦
    solLitNat (solCeilIsqrt normSqC) fun normCUb ↦
      solLitNat (Nat.add normCUb rho) fun sumR ↦ solSeqInt
          (solMinZ swScale (ceilDivScaleP (Int.ofNat (Nat.mul sumR sumR))))
          fun oneMinusCumUb ↦
            solSeqInt (Int.add survUb oneMinusCumUb) fun survUb' ↦
              solLitNat (solMinNat L (Nat.add hAct 1)) fun hNext ↦ solSeqIv
                  (cond (!Nat.beq hNext L || solBeqZ sp.vNum 0) (swScale, swScale)
                    ((solIvPythag sp.vNum (Int.ofNat uvDen)).1))
                  fun cv ↦
                    match solFastRecenterAndRadSq
                        (solFastPieriWalk hNext uvDen cv sp
                          (solFastGroverWalk hNext trigIvs cPref)) with
                    | (cNextRaw, radSqSum) =>
                        solSeqList (solPadEmptyPair (solFastTrimZeroPairs cNextRaw))
                          fun cOut ↦
                            solLitNat (solMaxNat 1 (Nat.div cOut.length 2)) fun hAct' ↦
                              solLitNat (Nat.add rho (solCeilIsqrt radSqSum)) fun rho' ↦
                                (cOut, hAct', rho', survUb')
private theorem solFastPulseStepL2_eq (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) (cPref : List
    ℤ) (hAct rho : ℕ) (survUb : ℤ) (sp : SolSparsePulse) : solFastPulseStepL2 L uvDen trigIvs cPref
    hAct rho survUb sp = solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp := by
  unfold solFastPulseStepL2 solPulseStepL2
  simp only [solLitNat_eq, solSeqInt_eq, solSeqIv_eq, solWithIvList_eq, solWithIntList_eq,
    solSeqList_eq, solFastGroverWalk_eq, solFastPieriWalk_eq, solFastRecenterAndRadSq_eq,
    solFastTrimZeroPairs_eq]
/-- Atomic-WHNF single-stratum WKB window element evaluator. -/
def solFastEvalWkbWinElem (tauNumZ tauDenZ scQ sMaxQ : ℤ) (hasLnch hasLand : Bool)
    (ilp : ℕ) (wlp : ℤ) (idp : ℕ) (wdp : ℤ)
    (rbTree ulnTree uldTree : SolPairTree) (swQ gwQ : ℤ) : ℤ :=
  solSeqInt (Int.sub swQ scQ) fun xiQ ↦
    let inBulk : Bool := solBleZ (-32767) xiQ && solBleZ xiQ 32767
    solSeqInt
      (cond inBulk (let sh := Int.add xiQ 32768
        let ix := (Int.ediv sh 1024).toNat
        let wx := Int.emod sh 1024
        solLerp1024 (solLookupPair rbTree ix) wx) 0)
      fun ru0 ↦
        let inLnch : Bool := hasLnch && solBleZ swQ 37887
        solSeqInt
          (cond inLnch (let (ils, wls) := solLinIdxFrac (Int.sub swQ 1024) 36864 17
            let r0 := Nat.add (Nat.mul ilp 18) ils
            let r1 := Nat.add (Nat.mul (Nat.add ilp 1) 18) ils
            let v0 := solLerp1024 (solLookupPair ulnTree r0) wls
            let v1 := solLerp1024 (solLookupPair ulnTree r1) wls
            Int.add ru0 (solLerp1024 (v0, v1) wlp)) ru0)
          fun ru1 ↦
            solSeqInt (Int.sub sMaxQ swQ) fun dsQ ↦
              let inLand : Bool := hasLand && solBleZ dsQ 36863
              solSeqInt
                (cond inLand (let (ids, wds) := solLinIdxFrac dsQ 36864 17
                  let r0 := Nat.add (Nat.mul idp 18) ids
                  let r1 := Nat.add (Nat.mul (Nat.add idp 1) 18) ids
                  let v0 := solLerp1024 (solLookupPair uldTree r0) wds
                  let v1 := solLerp1024 (solLookupPair uldTree r1) wds
                  Int.add ru1 (solLerp1024 (v0, v1) wdp)) ru1)
                fun ru2 ↦
                  let active : Bool := inBulk || inLnch || inLand
                  cond (active && !solBeqZ ru2 0)
                    (solSeqInt (Int.ediv (Int.mul (Int.mul tauNumZ gwQ) ru2)
                        (Int.mul 2048 tauDenZ))
                      fun thH ↦ Int.add thH
                          (Int.ediv (Int.mul (Int.mul thH thH) thH) 30000000000)) 0
/-- Direct WHNF-forced WKB active window builder (`= solEvalWkbWindow`). -/
def solFastEvalWkbWindow (tauNumZ tauDenZ scQ sMaxQ : ℤ) (hasLnch hasLand : Bool)
    (ilp : ℕ) (wlp : ℤ) (idp : ℕ) (wdp : ℤ) (rbTree ulnTree uldTree : SolPairTree) :
    ℕ → List (ℤ × ℤ) → List ℤ
  | 0, _ => []
  | count + 1, (swQ, gwQ) :: restSG =>
      solSeqInt (solFastEvalWkbWinElem tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
        ilp wlp idp wdp rbTree ulnTree uldTree swQ gwQ) fun uVal' ↦
        uVal' :: solFastEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
          ilp wlp idp wdp rbTree ulnTree uldTree count restSG
  | count + 1, [] =>
      solSeqInt (solFastEvalWkbWinElem tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
        ilp wlp idp wdp rbTree ulnTree uldTree 0 0) fun uVal' ↦
        uVal' :: solFastEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
          ilp wlp idp wdp rbTree ulnTree uldTree count []
private theorem solFastEvalWkbWindow_eq (tauNumZ tauDenZ scQ sMaxQ : ℤ)
    (hasLnch hasLand : Bool) (ilp : ℕ) (wlp : ℤ) (idp : ℕ) (wdp : ℤ)
    (rbTree ulnTree uldTree : SolPairTree) : ∀ (count : ℕ) (sgList : List (ℤ × ℤ)),
      solFastEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
        ilp wlp idp wdp rbTree ulnTree uldTree count sgList =
      solEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
        ilp wlp idp wdp rbTree ulnTree uldTree count sgList
  | 0, _ => rfl
  | count + 1, (swQ, gwQ) :: restSG => by
      unfold solFastEvalWkbWindow solEvalWkbWindow solFastEvalWkbWinElem
      simp only [solSeqList_eq, solSeqInt_eq]
      rw [solFastEvalWkbWindow_eq _ _ _ _ _ _ _ _ _ _ _ _ _ count restSG]
  | count + 1, [] => by
      unfold solFastEvalWkbWindow solEvalWkbWindow solFastEvalWkbWinElem
      simp only [solSeqList_eq, solSeqInt_eq]
      rw [solFastEvalWkbWindow_eq _ _ _ _ _ _ _ _ _ _ _ _ _ count []]
/-- Single-pulse WKB evaluator without double list reversal (`= solEvalWkbPulse`). -/
def solFastEvalWkbPulse (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (t : ℕ) : SolSparsePulse :=
  let tauNumZ := Int.ofNat q.tauNum
  let tauDenZ := Int.ofNat q.tauDen
  let rZ := Int.ofNat q.r
  let tZ := Int.ofNat t
  solSeqInt (Int.ediv (Int.mul (Int.mul tZ tauNumZ) 1024) tauDenZ) fun phiQ ↦
    solSeqInt (Int.sub phiTotQ phiQ) fun dPhiQ ↦
      let accTerm := Int.ediv
        (Int.mul (Int.mul (Int.ediv (Int.mul q.accelQ sMaxQ) 1024) tZ) tZ) km1Sq
      solSeqInt (Int.add (Int.add q.sOffQ (Int.ediv (Int.mul q.vBulkQ phiQ) 1024)) accTerm)
        fun scQ ↦
          let hasLnch : Bool := solBleZ phiQ 36863
          let hasLand : Bool := solBleZ dPhiQ 36863
          let sLoQ : ℤ := cond hasLnch 0
              (cond hasLand (solMinZ (Int.sub scQ 32768) (Int.sub sMaxQ 36864))
                (Int.sub scQ 32768))
          let sHiQ : ℤ := cond hasLand sMaxQ
              (cond hasLnch (solMaxZ (Int.add scQ 32768) 37888) (Int.add scQ 32768))
          let lM1 := solMaxNat 1 (Nat.sub q.L 1)
          let twoKR := Int.mul 2048 rZ
          let den4M := Int.mul 4194304 rZ
          let wLo : ℕ := cond (solBleZ sLoQ 0) 1
              (cond (solBleZ twoKR sLoQ) lM1 (let remLo := Int.sub twoKR sLoQ
                let qLo := Int.ediv (Int.mul remLo remLo) den4M
                let cand := Int.sub (Int.sub rZ qLo) 2
                solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let wHi : ℕ := cond (solBleZ sHiQ 0) 0
              (cond (solBleZ twoKR sHiQ) lM1 (let remHi := Int.sub twoKR sHiQ
                let qHi := Int.ediv (Int.mul remHi remHi) den4M
                let cand := Int.add (Int.sub rZ qHi) 2
                solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let (ilp, wlp) := cond hasLnch (solLinIdxFrac phiQ 36864 17) (0, 0)
          let (idp, wdp) := cond hasLand (solLinIdxFrac dPhiQ 36864 17) (0, 0)
          solLitNat wLo fun wLo' ↦
            solLitNat (cond (Nat.ble wLo' wHi) (Nat.sub (Nat.add wHi 1) wLo') 0)
              fun count ↦
                let vNum : ℤ := cond hasLand
                    (let (ivd, wvd) := solLinIdxFrac dPhiQ 36864 23
                    let rv := solLerp1024 (solLookupPair vdTree ivd) wvd
                    solSeqInt
                      (Int.ediv (Int.mul (Int.mul tauNumZ gTopQ) rv) (Int.mul 2048 tauDenZ))
                      fun thHv ↦
                        Int.add thHv (Int.ediv (Int.mul (Int.mul thHv thHv) thHv) 30000000000)) 0
                solSeqInt vNum fun vNum' ↦ ⟨wLo',
                   solFastEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
                     ilp wlp idp wdp rbTree ulnTree uldTree count (solDropSG wLo' sgArr),
                   vNum'⟩
private theorem solFastEvalWkbPulse_eq (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) (t : ℕ) :
    solFastEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t =
      solEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t := by
  unfold solFastEvalWkbPulse solEvalWkbPulse
  simp only [solSeqInt_eq, solLitNat_eq, solSeqList_eq, solWithIntList_eq, solFastEvalWkbWindow_eq]
private theorem wkbWLo_ge_one (b1 b2 : Bool) (lM1 c : ℕ) (hl : 1 ≤ lM1) :
    1 ≤ cond b1 1 (cond b2 lM1 (solMinNat lM1 (solMaxNat 1 c))) := by
  cases b1 <;> cases b2 <;> dsimp only [Bool.cond_true, Bool.cond_false]
  · rw [solMinNat_eq, solMaxNat_eq]; exact le_min hl (le_max_left _ _)
  · exact hl
  · exact le_rfl
  · exact le_rfl
private theorem solEvalWkbPulse_valid (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr :
    List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) (t : ℕ) : solSparsePulseValid
    (solEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t) = true := by
  unfold solEvalWkbPulse solSparsePulseValid
  simp only [solSeqInt_eq, solLitNat_eq, solSeqList_eq, solWithIntList_eq]
  rw [natBle_eq_decide, decide_eq_true_eq]
  exact wkbWLo_ge_one _ _ _ _ (by rw [solMaxNat_eq]; exact le_max_left _ _)
private theorem solUnrollWkbLoop_length (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) : ∀ (t rem : ℕ),
      (solUnrollWkbLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree t rem).length = rem
  | _, 0 => rfl
  | t, rem + 1 => by
      rw [solUnrollWkbLoop_succ, List.length_cons, solUnrollWkbLoop_length q sMaxQ gTopQ phiTotQ
        km1Sq sgArr rbTree ulnTree uldTree vdTree (t + 1) rem]
private theorem solUnrollWkbLoop_valid (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) : ∀ (t rem : ℕ),
      (solUnrollWkbLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree t rem).all solSparsePulseValid = true
  | _, 0 => rfl
  | t, rem + 1 => by
      rw [solUnrollWkbLoop_succ, List.all_cons, solEvalWkbPulse_valid, Bool.true_and]
      exact solUnrollWkbLoop_valid q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree (t + 1) rem
private theorem solUnrollWkbSlice_length (q : SolWkbSched) (t0 len : ℕ) :
    (solUnrollWkbSlice q t0 len).length = len := by
  unfold solUnrollWkbSlice
  simp only [solSeqList_eq, solSeqInt_eq, solWithPairTree_eq, solRevForcePulseList_id]
  exact solUnrollWkbLoop_length q _ _ _ _ _ _ _ _ _ t0 len
private theorem solUnrollWkbSlice_valid (q : SolWkbSched) (t0 len : ℕ) :
    (solUnrollWkbSlice q t0 len).all solSparsePulseValid = true := by
  unfold solUnrollWkbSlice
  simp only [solSeqList_eq, solSeqInt_eq, solWithPairTree_eq, solRevForcePulseList_id]
  exact solUnrollWkbLoop_valid q _ _ _ _ _ _ _ _ _ t0 len
/-- Tail-recursive WKB segment evolution loop with `SolSparsePulse.casesOn` sharing. -/
def solFastWkbEvolveLoop (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (trigIvs : List (IvInt × IvInt)) : ℕ → ℕ → List ℤ → ℕ → ℕ → ℤ → List ℤ × ℕ × ℕ × ℤ
  | _, 0, cPref, hAct, rho, survUb => (cPref, hAct, rho, survUb)
  | t, rem + 1, cPref, hAct, rho, survUb =>
      match solFastEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with
      | ⟨wLo, uWin, vNum⟩ =>
          match solFastPulseStepL2 q.L q.uvDen trigIvs cPref hAct rho survUb
              ⟨wLo, uWin, vNum⟩ with
          | (cNext, hAct', rho', survUb') =>
              solSeqList cNext fun cNext' ↦
                solLitNat hAct' fun ha ↦
                  solLitNat rho' fun rh ↦
                    solSeqInt survUb' fun sv ↦
                      solLitNat (Nat.add t 1) fun tNext ↦
                        solFastWkbEvolveLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
                          rbTree ulnTree uldTree vdTree trigIvs tNext rem cNext' ha rh sv
private theorem solFastWkbEvolveLoop_eq (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (trigIvs : List (IvInt × IvInt)) : ∀ (t rem : ℕ) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      solFastWkbEvolveLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree trigIvs t rem cPref hAct rho survUb =
        solEvolutionL2Seg q.L q.uvDen trigIvs cPref hAct rho survUb
          (solUnrollWkbLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t rem)
  | _, 0, _, _, _, _ => rfl
  | t, rem + 1, cPref, hAct, rho, survUb => by
      rw [solUnrollWkbLoop_succ]; unfold solFastWkbEvolveLoop solEvolutionL2Seg
      rw [solFastEvalWkbPulse_eq]; rcases solEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with ⟨wLo, uWin, vNum⟩
      dsimp only; rw [solFastPulseStepL2_eq]
      rcases solPulseStepL2 q.L q.uvDen trigIvs cPref hAct rho survUb
          ⟨wLo, uWin, vNum⟩ with ⟨cNext, hAct', rho', survUb'⟩
      dsimp only
      simp only [solSeqList_eq, solWithIntList_eq, solLitNat_eq, solSeqInt_eq, solNatAdd_eq]
      exact solFastWkbEvolveLoop_eq q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree trigIvs (t + 1) rem cNext hAct' rho' survUb'
/-- Fast boolean checker for a `len`-pulse WKB slice (`= checkPulseWkbSlice`). -/
def solFastCheckWkbSlice (q : SolWkbSched) (t len : ℕ) (trigIvs : List (IvInt × IvInt))
    (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ)
    (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) : Bool :=
  solWithTrigList trigIvs fun trigIvs' ↦
    solWithIntList cIn fun cIn' ↦
      solSeqList (solRevSGList (solBuildWkbSGRev q.r 0 (Nat.add q.L 1) []) []) fun sgArr ↦
        solSeqInt (sgArr.getD (Nat.sub q.L 1) (0, 0)).1 fun sMaxQ ↦
          let gTopNat := solFloorIsqrt
            (Nat.div (Nat.mul 1048576 (Nat.sub q.r (Nat.sub q.L 1))) q.r)
          solSeqInt (Int.ofNat gTopNat) fun gTopQ ↦
            let km1 := Int.ofNat (solMaxNat 1 (Nat.sub q.K 1))
            solSeqInt (Int.mul km1 km1) fun km1Sq ↦ solSeqInt
                (Int.ediv (Int.mul (Int.mul (Int.ofNat (Nat.sub q.K 1)) (Int.ofNat q.tauNum)) 1024)
                  (Int.ofNat q.tauDen))
                fun phiTotQ ↦
                  solWithPairTree (solBuildPairTree q.rBulkQ 8) fun rbTree ↦
                    solWithPairTree (solBuildPairTree q.uLnchQ 10) fun ulnTree ↦
                      solWithPairTree (solBuildPairTree q.uLandQ 10) fun uldTree ↦
                        solWithPairTree (solBuildPairTree q.vDrainQ 6) fun vdTree ↦
                          match solFastWkbEvolveLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
                              rbTree ulnTree uldTree vdTree trigIvs' t len
                              cIn' hIn rhoIn survIn with
                          | (c1, h1, rh1, sv1) =>
                              solListIntBeq c1 cOut &&
                              Nat.beq h1 hOut &&
                              Nat.beq rh1 rhoOut &&
                              solBeqZ sv1 survOut
private theorem solNatBeq_refl : ∀ (n : ℕ), n.beq n = true
  | 0 => rfl
  | n + 1 => solNatBeq_refl n
private theorem solFastCheckWkbSlice_eq (q : SolWkbSched) (t len : ℕ) (trigIvs : List (IvInt ×
    IvInt)) (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ) (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut :
    ℤ) : solFastCheckWkbSlice q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut =
    checkPulseWkbSlice q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut := by
  have hlen : (solUnrollWkbSlice q t len).length = len := solUnrollWkbSlice_length q t len
  have hbeq : (solUnrollWkbSlice q t len).length.beq len = true := by
    rw [hlen]; exact solNatBeq_refl len
  have hval : (solUnrollWkbSlice q t len).all solSparsePulseValid = true :=
    solUnrollWkbSlice_valid q t len
  unfold checkPulseWkbSlice; rw [solWithTrigList_eq, solWithIntList_eq, solWithPulseList_eq]
  dsimp only; rw [hbeq, hval]
  simp only [Bool.true_and]; unfold solFastCheckWkbSlice solUnrollWkbSlice
  simp only [solWithTrigList_eq, solWithIntList_eq, solSeqList_eq, solSeqInt_eq,
    solWithPairTree_eq, solRevForcePulseList_id, solFastWkbEvolveLoop_eq]
theorem solFastWkbStep_eq {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)} {t len tNext : ℕ} {cIn
    : List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ} {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ} (ht : t +
    len = tNext) (hprev : SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn) (hfast :
    solFastCheckWkbSlice q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut = true) :
    SolWkbRunPrefix q trigIvs tNext cOut hOut rhoOut survOut := by
  rw [solFastCheckWkbSlice_eq] at hfast; exact solWkbRunPrefix_step_eq ht hprev hfast
private def fastEvolutionL2Aux (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) : List SolSparsePulse → List ℤ × ℕ × ℤ
  | [] => (cPref, rho, survUb)
  | sp :: sps =>
      match solFastPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with
      | (cNext, hAct', rho', survUb') =>
        solSeqList cNext fun cNext' ↦
          solLitNat hAct' fun ha ↦
            solLitNat rho' fun rh ↦
              solSeqInt survUb' fun sv ↦ fastEvolutionL2Aux L uvDen trigIvs cNext' ha rh sv sps
private theorem fastEvolutionL2Aux_eq (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) :
    ∀ (sps : List SolSparsePulse) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      fastEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb sps =
        solEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb sps
  | [], _, _, _, _ => rfl
  | sp :: sps, cPref, hAct, rho, survUb => by
      unfold fastEvolutionL2Aux solEvolutionL2Aux; rw [solFastPulseStepL2_eq]
      rcases solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with
        ⟨cNext, hAct', rho', survUb'⟩
      dsimp only; simp only [solSeqList_eq, solWithIntList_eq, solLitNat_eq, solSeqInt_eq]
      exact fastEvolutionL2Aux_eq L uvDen trigIvs sps cNext hAct' rho' survUb'
private def fastCheckBucketCertL2 (L rMin rMax tauNum tauDen uvDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) (sps : List SolSparsePulse)
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ) : Bool :=
  solWithPulseList sps fun sps ↦
    Nat.ble 2 L && Nat.ble L 1024 && Nat.ble L rMin && Nat.ble rMin rMax &&
    Nat.ble rMax 1024 && Nat.ble 1 uvDen &&
    Nat.ble 1 sps.length && Nat.ble sps.length 5120 &&
    certTailLbs.length.beq L &&
    sps.all solSparsePulseValid &&
    PulseM1.checkPulseBucketAngles L rMin rMax tauNum tauDen ratios trigIvs &&
    solWithTrigList trigIvs fun trigIvs' ↦
      match fastEvolutionL2Aux L uvDen trigIvs' [swScale, 0] 1 0 0 sps with
      | (cEnd, rhoEnd, survEnd) =>
          match solTerminalBoundsL2 L cEnd rhoEnd survEnd with
          | (p0Lb, tailLbs, sUb) =>
              tailLbs.length.beq L &&
              solBleZ 0 certP0Lb && solBleZ certP0Lb p0Lb &&
              solBleZ 0 certSurvUb && solBleZ sUb certSurvUb &&
              solBleZ 1 (certTailLbs.getD 0 0) &&
              solBleZ (certTailLbs.getD 0 0) swScale &&
              solBleZ 0 (certTailLbs.getD (Nat.sub L 1) 0) &&
              solAllLeZip certTailLbs tailLbs
private theorem fastCheckBucketCertL2_eq (L rMin rMax tauNum tauDen uvDen : ℕ) (ratios : List IvInt)
    (trigIvs : List (IvInt × IvInt)) (sps : List SolSparsePulse) (certP0Lb : ℤ) (certTailLbs : List
    ℤ) (certSurvUb : ℤ) : fastCheckBucketCertL2 L rMin rMax tauNum tauDen uvDen ratios trigIvs sps
    certP0Lb certTailLbs certSurvUb = checkPulseBucketCertL2 L rMin rMax tauNum tauDen uvDen
    ratios trigIvs sps certP0Lb certTailLbs certSurvUb := by
  unfold fastCheckBucketCertL2 checkPulseBucketCertL2 solEvolutionL2
  simp only [solWithPulseList_eq, solWithTrigList_eq, fastEvolutionL2Aux_eq]
private def fastCheckExplicitStage (L r tauNum tauDen uvDen : ℕ) (ratios : List IvInt) (trigIvs :
    List (IvInt × IvInt)) (sps : List SolSparsePulse) (p0Lb : ℤ) (tailLbs : List ℤ) (survUb : ℤ)
    (vTable : ℕ → ℤ) : Bool :=
  fastCheckBucketCertL2 L r r tauNum tauDen uvDen ratios trigIvs sps
    p0Lb tailLbs survUb &&
  checkPulseCascadeStepTable L r tauNum tauDen survUb p0Lb tailLbs vTable
private theorem fastCheckExplicitStage_eq (L r tauNum tauDen uvDen : ℕ) (ratios : List IvInt)
    (trigIvs : List (IvInt × IvInt)) (sps : List SolSparsePulse) (p0Lb : ℤ) (tailLbs : List ℤ)
    (survUb : ℤ) (vTable : ℕ → ℤ) : fastCheckExplicitStage L r tauNum tauDen uvDen ratios trigIvs
    sps p0Lb tailLbs survUb vTable = checkPulseExplicitStageTable L r tauNum tauDen uvDen ratios
    trigIvs sps p0Lb tailLbs survUb vTable := by
  unfold fastCheckExplicitStage checkPulseExplicitStageTable; rw [fastCheckBucketCertL2_eq]
private lemma _bL {a b : Bool} (h : (a && b) = true) : a = true := by
  simp only [Bool.and_eq_true] at h; exact h.1
private lemma _bR {a b : Bool} (h : (a && b) = true) : b = true := by
  simp only [Bool.and_eq_true] at h; exact h.2
private def _s0EvalWkbPulseRef (qR qL qTauNum qTauDen : ℕ)
    (qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (t : ℕ) : SolSparsePulse :=
  let tauNumZ := Int.ofNat qTauNum
  let tauDenZ := Int.ofNat qTauDen
  let rZ := Int.ofNat qR
  let tZ := Int.ofNat t
  solSeqInt (Int.ediv (Int.mul (Int.mul tZ tauNumZ) 1024) tauDenZ) fun phiQ ↦
    solSeqInt (Int.sub phiTotQ phiQ) fun dPhiQ ↦
      let accTerm := Int.ediv
        (Int.mul (Int.mul (Int.ediv (Int.mul qAccelQ sMaxQ) 1024) tZ) tZ) km1Sq
      solSeqInt (Int.add (Int.add qSOffQ (Int.ediv (Int.mul qVBulkQ phiQ) 1024)) accTerm)
        fun scQ ↦
          let hasLnch : Bool := solBleZ phiQ 36863
          let hasLand : Bool := solBleZ dPhiQ 36863
          let sLoQ : ℤ :=
            cond hasLnch 0
              (cond hasLand (solMinZ (Int.sub scQ 32768) (Int.sub sMaxQ 36864))
                (Int.sub scQ 32768))
          let sHiQ : ℤ :=
            cond hasLand sMaxQ
              (cond hasLnch (solMaxZ (Int.add scQ 32768) 37888)
                (Int.add scQ 32768))
          let lM1 := solMaxNat 1 (Nat.sub qL 1)
          let twoKR := Int.mul 2048 rZ
          let den4M := Int.mul 4194304 rZ
          let wLo : ℕ :=
            cond (solBleZ sLoQ 0) 1
              (cond (solBleZ twoKR sLoQ) lM1
                (let remLo := Int.sub twoKR sLoQ
                let qLo := Int.ediv (Int.mul remLo remLo) den4M
                let cand := Int.sub (Int.sub rZ qLo) 2
                solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let wHi : ℕ :=
            cond (solBleZ sHiQ 0) 0
              (cond (solBleZ twoKR sHiQ) lM1
                (let remHi := Int.sub twoKR sHiQ
                let qHi := Int.ediv (Int.mul remHi remHi) den4M
                let cand := Int.add (Int.sub rZ qHi) 2
                solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let (ilp, wlp) := cond hasLnch (solLinIdxFrac phiQ 36864 17) (0, 0)
          let (idp, wdp) := cond hasLand (solLinIdxFrac dPhiQ 36864 17) (0, 0)
          solLitNat wLo fun wLo' ↦
            solLitNat (cond (Nat.ble wLo' wHi) (Nat.sub (Nat.add wHi 1) wLo') 0)
              fun count ↦
                let vNum : ℤ :=
                  cond hasLand
                    (let (ivd, wvd) := solLinIdxFrac dPhiQ 36864 23
                    let rv := solLerp1024 (solLookupPair vdTree ivd) wvd
                    solSeqInt
                      (Int.ediv (Int.mul (Int.mul tauNumZ gTopQ) rv) (Int.mul 2048 tauDenZ))
                      fun thHv ↦
                        Int.add thHv (Int.ediv (Int.mul (Int.mul thHv thHv) thHv) 30000000000))
                    0
                solSeqInt vNum fun vNum' ↦
                  ⟨wLo',
                   solFastEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
                     ilp wlp idp wdp rbTree ulnTree uldTree count (solDropSG wLo' sgArr),
                   vNum'⟩
private theorem _s0EvalWkbPulseRef_eq (q : SolWkbSched)
    (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ))
    (rbTree ulnTree uldTree vdTree : SolPairTree) (t : ℕ) :
    _s0EvalWkbPulseRef q.r q.L q.tauNum q.tauDen q.sOffQ q.vBulkQ q.accelQ
        sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t =
      solFastEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree t :=
  rfl
private def _s0WkbEvolveLoopRef (qR qL qTauNum qTauDen qUvDen : ℕ)
    (qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (trigIvs : List (IvInt × IvInt)) :
    ℕ → ℕ → List ℤ → ℕ → ℕ → ℤ → List ℤ × ℕ × ℕ × ℤ
  | 0, _, cPref, hAct, rho, survUb => (cPref, hAct, rho, survUb)
  | rem + 1, t, cPref, hAct, rho, survUb =>
      match _s0EvalWkbPulseRef qR qL qTauNum qTauDen qSOffQ qVBulkQ qAccelQ
          sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t with
      | ⟨wLo, uWin, vNum⟩ =>
          match solFastPulseStepL2 qL qUvDen trigIvs cPref hAct rho survUb
              ⟨wLo, uWin, vNum⟩ with
          | (cNext, hAct', rho', survUb') =>
              solSeqList cNext fun cNext' ↦
                solLitNat hAct' fun ha ↦
                  solLitNat rho' fun rh ↦
                    solSeqInt survUb' fun sv ↦
                      solLitNat (Nat.add t 1) fun tNext ↦
                        _s0WkbEvolveLoopRef qR qL qTauNum qTauDen qUvDen
                          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
                          rbTree ulnTree uldTree vdTree trigIvs rem tNext cNext' ha rh sv
private theorem _s0WkbEvolveLoopRef_eq (q : SolWkbSched)
    (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ))
    (rbTree ulnTree uldTree vdTree : SolPairTree)
    (trigIvs : List (IvInt × IvInt)) :
    ∀ (rem t : ℕ) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      _s0WkbEvolveLoopRef q.r q.L q.tauNum q.tauDen q.uvDen
          q.sOffQ q.vBulkQ q.accelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree trigIvs rem t cPref hAct rho survUb =
        solFastWkbEvolveLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree trigIvs t rem cPref hAct rho survUb
  | 0, _, _, _, _, _ => rfl
  | rem + 1, t, cPref, hAct, rho, survUb => by
      unfold _s0WkbEvolveLoopRef solFastWkbEvolveLoop
      rw [_s0EvalWkbPulseRef_eq]
      rcases solFastEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with ⟨wLo, uWin, vNum⟩
      dsimp only
      rcases solFastPulseStepL2 q.L q.uvDen trigIvs cPref hAct rho survUb
          ⟨wLo, uWin, vNum⟩ with ⟨cNext, hAct', rho', survUb'⟩
      dsimp only
      simp only [solSeqList_eq, solLitNat_eq, solSeqInt_eq]
      exact _s0WkbEvolveLoopRef_eq q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree trigIvs rem (Nat.add t 1) cNext hAct' rho' survUb'
private def _s0CheckWkbSliceRef (q : SolWkbSched) (t len : ℕ)
    (trigIvs : List (IvInt × IvInt))
    (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ)
    (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) : Bool :=
  solLitNat q.r fun qR ↦
    solLitNat q.L fun qL ↦
      solLitNat q.tauNum fun qTauNum ↦
        solLitNat q.tauDen fun qTauDen ↦
          solLitNat q.uvDen fun qUvDen ↦
            solSeqInt q.sOffQ fun qSOffQ ↦
              solSeqInt q.vBulkQ fun qVBulkQ ↦
                solSeqInt q.accelQ fun qAccelQ ↦
                  solWithTrigList trigIvs fun trigIvs' ↦
                    solWithIntList cIn fun cIn' ↦
                      solSeqList (solRevSGList (solBuildWkbSGRev qR 0 (Nat.add qL 1) []) [])
                        fun sgArr ↦
                        solSeqInt (sgArr.getD (Nat.sub qL 1) (0, 0)).1 fun sMaxQ ↦
                          let gTopNat := solFloorIsqrt
                            (Nat.div (Nat.mul 1048576 (Nat.sub qR (Nat.sub qL 1))) qR)
                          solSeqInt (Int.ofNat gTopNat) fun gTopQ ↦
                            let km1 := Int.ofNat (solMaxNat 1 (Nat.sub q.K 1))
                            solSeqInt (Int.mul km1 km1) fun km1Sq ↦
                              solSeqInt
                                (Int.ediv
                                  (Int.mul (Int.mul (Int.ofNat (Nat.sub q.K 1))
                                    (Int.ofNat qTauNum)) 1024)
                                  (Int.ofNat qTauDen))
                                fun phiTotQ ↦
                                  solWithPairTree (solBuildPairTree q.rBulkQ 8) fun rbTree ↦
                                    solWithPairTree (solBuildPairTree q.uLnchQ 10) fun ulnTree ↦
                                      solWithPairTree (solBuildPairTree q.uLandQ 10) fun uldTree ↦
                                        solWithPairTree (solBuildPairTree q.vDrainQ 6) fun vdTree ↦
                                          match _s0WkbEvolveLoopRef qR qL qTauNum qTauDen qUvDen
                                              qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
                                              rbTree ulnTree uldTree vdTree trigIvs' len t
                                              cIn' hIn rhoIn survIn with
                                          | (c1, h1, rh1, sv1) =>
                                              solListIntBeq c1 cOut &&
                                              h1.beq hOut &&
                                              rh1.beq rhoOut &&
                                              solBeqZ sv1 survOut
private theorem _s0CheckWkbSliceRef_eq (q : SolWkbSched) (t len : ℕ)
    (trigIvs : List (IvInt × IvInt))
    (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ)
    (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) :
    _s0CheckWkbSliceRef q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut =
      solFastCheckWkbSlice q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut := by
  unfold _s0CheckWkbSliceRef solFastCheckWkbSlice
  simp only [solLitNat_eq, solSeqInt_eq, solWithTrigList_eq, solWithIntList_eq,
    solSeqList_eq, solWithPairTree_eq, _s0WkbEvolveLoopRef_eq]
private theorem _s0WkbStepRef_eq {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)}
    {t len tNext : ℕ} {cIn : List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ}
    {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ}
    (ht : t + len = tNext)
    (hprev : SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn)
    (hfast : _s0CheckWkbSliceRef q t len trigIvs cIn hIn rhoIn survIn
      cOut hOut rhoOut survOut = true) :
    SolWkbRunPrefix q trigIvs tNext cOut hOut rhoOut survOut := by
  rw [_s0CheckWkbSliceRef_eq] at hfast
  exact solFastWkbStep_eq ht hprev hfast
private def solKeepZS2V {α : Type*} (x : ℤ) (k : ℤ → α) : α :=
  @Int.casesOn (fun _ ↦ α) x (fun n ↦ k (Int.ofNat n)) (fun n ↦ k (Int.negSucc n))
private theorem solKeepZS2V_eq {α : Type*} (x : ℤ) (k : ℤ → α) : solKeepZS2V x k = k x := by
  cases x <;> rfl
private def solForcePairS2V {α β γ : Type*} (p : α × β) (k : α × β → γ) : γ :=
  @Prod.casesOn α β (fun _ ↦ γ) p fun a b ↦ k (a, b)
private theorem solForcePairS2V_eq {α β γ : Type*} (p : α × β) (k : α × β → γ) :
    solForcePairS2V p k = k p := by rcases p with ⟨a, b⟩; rfl
private def solBindIvS2V {α : Type*} (iv : IvInt) (k : IvInt → α) : α :=
  match iv with | (lo, hi) => solKeepZS2V lo fun a ↦ solKeepZS2V hi fun b ↦ k (a, b)
private theorem solBindIvS2V_eq {α : Type*} (iv : IvInt) (k : IvInt → α) : solBindIvS2V iv k = k iv
    := by
  rcases iv with ⟨lo, hi⟩; simp only [solBindIvS2V, solKeepZS2V_eq]
private def solIsZeroZS2V : ℤ → Bool
  | .ofNat m => m.beq 0
  | .negSucc _ => false
private theorem solIsZeroZS2V_eq (x : ℤ) : solIsZeroZS2V x = solBeqZ x 0 := by cases x <;> rfl
private def solIvIsZeroS2V : IvInt → Bool | (lo, hi) => solIsZeroZS2V lo && solIsZeroZS2V hi
private theorem solIvIsZeroS2V_eq (iv : IvInt) : solIvIsZeroS2V iv = solIvIsZero iv := by
  rcases iv with ⟨lo, hi⟩; simp only [solIvIsZeroS2V, solIvIsZero, solIsZeroZS2V_eq]
private def solGmpNegZS2V : ℤ → ℤ
  | .ofNat m => cond (Nat.ble m 0) (Int.ofNat 0) (solLitNat (Nat.sub m 1) Int.negSucc)
  | .negSucc m => solLitNat (Nat.add m 1) Int.ofNat
private theorem solGmpNegZS2V_eq (a : ℤ) : solGmpNegZS2V a = Int.neg a := by
  rcases a with (_ | k) | m
  · rfl
  · change cond false (Int.ofNat 0)
      (solLitNat (Nat.sub (k + 1) 1) Int.negSucc) = Int.negSucc k
    rw [Bool.cond_false, solLitNat_eq]; rfl
  · change solLitNat (Nat.add m 1) Int.ofNat = Int.ofNat (m + 1); rw [solLitNat_eq]
private def solGmpSubNatS2V (m n : ℕ) : ℤ :=
  cond (Nat.ble n m) (solLitNat (Nat.sub m n) Int.ofNat)
    (solLitNat (Nat.sub (Nat.sub n m) 1) Int.negSucc)
private theorem solGmpSubNatS2V_eq (m n : ℕ) : solGmpSubNatS2V m n = (m : ℤ) - (n : ℤ) := by
  unfold solGmpSubNatS2V
  rw [natBle_eq_decide, solLitNat_eq, solLitNat_eq, solNatSub_eq, solNatSub_eq, solNatSub_eq]
  by_cases h : n ≤ m
  · rw [decide_eq_true h, Bool.cond_true, Int.ofNat_eq_natCast]; omega
  · rw [decide_eq_false h, Bool.cond_false]; omega
private def solGmpAddZS2V : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solLitNat (Nat.add m n) Int.ofNat
  | .ofNat m, .negSucc n => solGmpSubNatS2V m (Nat.add n 1)
  | .negSucc m, .ofNat n => solGmpSubNatS2V n (Nat.add m 1)
  | .negSucc m, .negSucc n => solLitNat (Nat.add (Nat.add m n) 1) Int.negSucc
private theorem solGmpAddZS2V_eq (a b : ℤ) : solGmpAddZS2V a b = Int.add a b := by
  rw [solIntAdd_eq]
  rcases a with m | m <;> rcases b with n | n <;> dsimp only [solGmpAddZS2V] <;>
    simp only [solGmpSubNatS2V_eq, solLitNat_eq, solNatAdd_eq, Int.ofNat_eq_natCast] <;> omega
private def solGmpSubZS2V : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solGmpSubNatS2V m n
  | .ofNat m, .negSucc n => solLitNat (Nat.add (Nat.add m n) 1) Int.ofNat
  | .negSucc m, .ofNat n => solLitNat (Nat.add m n) Int.negSucc
  | .negSucc m, .negSucc n => solGmpSubNatS2V n m
private theorem solGmpSubZS2V_eq (a b : ℤ) : solGmpSubZS2V a b = Int.sub a b := by
  rw [solIntSub_eq]
  rcases a with m | m <;> rcases b with n | n <;> dsimp only [solGmpSubZS2V] <;>
    simp only [solGmpSubNatS2V_eq, solLitNat_eq, solNatAdd_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      <;> omega
private def solGmpMulZS2V : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solLitNat (Nat.mul m n) Int.ofNat
  | .ofNat m, .negSucc n => solGmpNegZS2V (solLitNat (Nat.mul m (Nat.add n 1)) Int.ofNat)
  | .negSucc m, .ofNat n => solGmpNegZS2V (solLitNat (Nat.mul (Nat.add m 1) n) Int.ofNat)
  | .negSucc m, .negSucc n => solLitNat (Nat.mul (Nat.add m 1) (Nat.add n 1)) Int.ofNat
private theorem solGmpMulZS2V_eq (a b : ℤ) : solGmpMulZS2V a b = Int.mul a b := by
  rw [solIntMul_eq]
  rcases a with m | m <;> rcases b with n | n <;> dsimp only [solGmpMulZS2V] <;>
    simp only [solGmpNegZS2V_eq, solIntNeg_eq, solLitNat_eq, solNatMul_eq, solNatAdd_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> push_cast <;> ring
private def solGmpEdivZS2V : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solLitNat (Nat.div m n) Int.ofNat
  | .ofNat m, .negSucc n => solGmpNegZS2V (solLitNat (Nat.div m (Nat.add n 1)) Int.ofNat)
  | .negSucc m, .ofNat n => cond (Nat.ble n 0) (Int.ofNat 0) (solLitNat (Nat.div m n) Int.negSucc)
  | .negSucc m, .negSucc n => solLitNat (Nat.add (Nat.div m (Nat.add n 1)) 1) Int.ofNat
private theorem solGmpEdivZS2V_eq (a b : ℤ) : solGmpEdivZS2V a b = Int.ediv a b := by
  rcases a with m | m <;> rcases b with (_ | k) | n
  · exact solLitNat_eq (Nat.div m 0) Int.ofNat
  · exact solLitNat_eq (Nat.div m (k + 1)) Int.ofNat
  · exact (congrArg solGmpNegZS2V (solLitNat_eq _ Int.ofNat)).trans (solGmpNegZS2V_eq _)
  · exact rfl
  · exact solLitNat_eq (Nat.div m (k + 1)) Int.negSucc
  · exact solLitNat_eq (Nat.add (Nat.div m (Nat.add n 1)) 1) Int.ofNat
private def solGmpDivScaleS2V : ℤ → ℤ
  | .ofNat m => solLitNat (Nat.div m 1000000000) Int.ofNat
  | .negSucc m => solLitNat (Nat.div m 1000000000) Int.negSucc
private theorem solGmpDivScaleS2V_eq (a : ℤ) : solGmpDivScaleS2V a = Int.ediv a swScale := by
  unfold swScale; rw [solIntEdiv_eq]
  rcases a with m | m <;> dsimp only [solGmpDivScaleS2V] <;>
    simp only [solLitNat_eq, solNatDiv_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private def solGmpCeilDivScaleS2V : ℤ → ℤ
  | .ofNat m => solLitNat (Nat.div (Nat.add m 999999999) 1000000000) Int.ofNat
  | .negSucc m =>
      cond (Nat.ble m 999999998) (Int.ofNat 0)
        (solLitNat (Nat.div (Nat.sub m 999999999) 1000000000) Int.negSucc)
private theorem solGmpCeilDivScaleS2V_eq (x : ℤ) : solGmpCeilDivScaleS2V x =
    SchurWeylLCert.ceilDivScaleP x := by
  unfold SchurWeylLCert.ceilDivScaleP swScale; rw [solIntNeg_eq, solIntNeg_eq, solIntEdiv_eq]
  rcases x with m | m
  · dsimp only [solGmpCeilDivScaleS2V]
    simp only [solLitNat_eq, solNatDiv_eq, solNatAdd_eq, Int.ofNat_eq_natCast]; omega
  · dsimp only [solGmpCeilDivScaleS2V]; rw [natBle_eq_decide]
    by_cases h : m ≤ 999999998
    · rw [decide_eq_true h, Bool.cond_true]; simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
    · rw [decide_eq_false h, Bool.cond_false, solLitNat_eq, solNatDiv_eq, solNatSub_eq,
        Int.negSucc_eq]; omega
private def solGmpDiv2S2V : ℤ → ℤ
  | .ofNat m => solLitNat (Nat.div m 2) Int.ofNat
  | .negSucc m => solLitNat (Nat.div m 2) Int.negSucc
private theorem solGmpDiv2S2V_eq (a : ℤ) : solGmpDiv2S2V a = Int.ediv a 2 := by
  rw [solIntEdiv_eq]
  rcases a with m | m <;> dsimp only [solGmpDiv2S2V] <;>
    simp only [solLitNat_eq, solNatDiv_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private def solFastScaleDivIvS2V (loProd hiProd : ℤ) : IvInt :=
  solKeepZS2V (solGmpDivScaleS2V loProd) fun qLo ↦
    solKeepZS2V (solGmpCeilDivScaleS2V hiProd) fun qHi ↦ (qLo, qHi)
private theorem solFastScaleDivIvS2V_eq (loProd hiProd : ℤ) : solFastScaleDivIvS2V loProd hiProd =
    solFastScaleDivIv loProd hiProd := by
  unfold solFastScaleDivIvS2V solFastScaleDivIv
  simp only [solKeepZS2V_eq, solSeqInt_eq, solGmpDivScaleS2V_eq, solGmpCeilDivScaleS2V_eq]
private def solFastIvMulS2V : IvInt → IvInt → IvInt
  | (a1, a2), (b1, b2) =>
      cond (solBleZ a1 a2 && solBleZ b1 b2) (cond (solBleZ (Int.ofNat 0) a1)
          (cond (solBleZ (Int.ofNat 0) b1)
            (solFastScaleDivIvS2V (solGmpMulZS2V a1 b1) (solGmpMulZS2V a2 b2))
            (cond (solBleZ b2 (Int.ofNat 0))
              (solFastScaleDivIvS2V (solGmpMulZS2V a2 b1) (solGmpMulZS2V a1 b2))
              (solFastScaleDivIvS2V (solGmpMulZS2V a2 b1) (solGmpMulZS2V a2 b2))))
          (cond (solBleZ a2 (Int.ofNat 0)) (cond (solBleZ (Int.ofNat 0) b1)
              (solFastScaleDivIvS2V (solGmpMulZS2V a1 b2) (solGmpMulZS2V a2 b1))
              (cond (solBleZ b2 (Int.ofNat 0))
                (solFastScaleDivIvS2V (solGmpMulZS2V a2 b2) (solGmpMulZS2V a1 b1))
                (solFastScaleDivIvS2V (solGmpMulZS2V a1 b2) (solGmpMulZS2V a1 b1))))
            (solIvMul (a1, a2) (b1, b2))))
        (solIvMul (a1, a2) (b1, b2))
private theorem solFastIvMulS2V_eq (a b : IvInt) : solFastIvMulS2V a b =
    solFastIvMul a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  dsimp only [solFastIvMulS2V, solFastIvMul]
  simp only [solFastScaleDivIvS2V_eq, solGmpMulZS2V_eq]; rfl
private def solScaleNegFloorS2V (p : ℕ) : ℤ :=
  cond (Nat.ble p 0) (Int.ofNat 0) (solLitNat (Nat.div (Nat.sub p 1) 1000000000) Int.negSucc)
private theorem solScaleNegFloorS2V_eq (p : ℕ) : solScaleNegFloorS2V p = Int.ediv (-(p : ℤ)) swScale
    := by
  unfold swScale; rw [solIntEdiv_eq]
  rcases p with _ | k
  · rfl
  · change cond false (Int.ofNat 0)
      (solLitNat (Nat.div (Nat.sub (k + 1) 1) 1000000000) Int.negSucc) = _
    rw [Bool.cond_false, solLitNat_eq, solNatDiv_eq, solNatSub_eq, Int.negSucc_eq]; omega
private def solScaleNegCeilS2V (p : ℕ) : ℤ :=
  cond (Nat.ble p 999999999) (Int.ofNat 0)
    (solLitNat (Nat.div (Nat.sub p 1000000000) 1000000000) Int.negSucc)
private theorem solScaleNegCeilS2V_eq (p : ℕ) : solScaleNegCeilS2V p = SchurWeylLCert.ceilDivScaleP
    (-(p : ℤ)) := by
  unfold SchurWeylLCert.ceilDivScaleP swScale; rw [solIntNeg_eq, solIntNeg_eq, solIntEdiv_eq]
  dsimp only [solScaleNegCeilS2V]; rw [natBle_eq_decide]
  by_cases h : p ≤ 999999999
  · rw [decide_eq_true h, Bool.cond_true, Int.ofNat_eq_natCast]; omega
  · rw [decide_eq_false h, Bool.cond_false, solLitNat_eq, solNatDiv_eq, solNatSub_eq,
      Int.negSucc_eq]; omega
private def solFastIvScaleZRefS2V : IvInt → ℤ → IvInt
  | (a1, a2), c =>
      solKeepZS2V (solGmpMulZS2V a1 c) fun p1 ↦ solKeepZS2V (solGmpMulZS2V a2 c) fun p2 ↦
          cond (solBleZ p1 p2) (solFastScaleDivIvS2V p1 p2) (solFastScaleDivIvS2V p2 p1)
private theorem solFastIvScaleZRefS2V_eq (a : IvInt) (c : ℤ) : solFastIvScaleZRefS2V a c =
    solFastIvScaleZ a c := by
  rcases a with ⟨a1, a2⟩; dsimp only [solFastIvScaleZRefS2V, solFastIvScaleZ]
  simp only [solKeepZS2V_eq, solSeqInt_eq, solGmpMulZS2V_eq, solFastScaleDivIvS2V_eq]
private def solFastIvScaleZS2V : IvInt → ℤ → IvInt
  | (.ofNat m1, .ofNat m2), .ofNat n =>
      cond (Nat.ble m1 m2) (solLitNat (Nat.div (Nat.mul m1 n) 1000000000) fun q1 ↦
          solLitNat (Nat.div (Nat.add (Nat.mul m2 n) 999999999) 1000000000) fun q2 ↦
            (Int.ofNat q1, Int.ofNat q2))
        (solFastIvScaleZRefS2V (.ofNat m1, .ofNat m2) (.ofNat n))
  | (.ofNat m1, .ofNat m2), .negSucc n =>
      cond (Nat.ble m1 m2) (solLitNat (Nat.add n 1) fun n1 ↦
          solKeepZS2V (solScaleNegFloorS2V (Nat.mul m2 n1)) fun q1 ↦
            solKeepZS2V (solScaleNegCeilS2V (Nat.mul m1 n1)) fun q2 ↦ (q1, q2))
        (solFastIvScaleZRefS2V (.ofNat m1, .ofNat m2) (.negSucc n))
  | a, c => solFastIvScaleZRefS2V a c
private theorem solFastIvScaleZS2V_eq (a : IvInt) (c : ℤ) : solFastIvScaleZS2V a c =
    solFastIvScaleZ a c := by
  rw [← solFastIvScaleZRefS2V_eq]
  rcases a with ⟨m1 | m1, m2 | m2⟩
  · rcases c with n | n
    · dsimp only [solFastIvScaleZS2V]; rw [natBle_eq_decide]
      by_cases h : m1 ≤ m2
      · rw [decide_eq_true h, Bool.cond_true]; dsimp only [solFastIvScaleZRefS2V, solGmpMulZS2V]
        simp only [solLitNat_eq, solKeepZS2V_eq]; dsimp only [solBleZ]
        have hm : Nat.mul m1 n ≤ Nat.mul m2 n := by
          rw [solNatMul_eq, solNatMul_eq]; exact Nat.mul_le_mul_right n h
        rw [natBle_eq_decide, decide_eq_true hm, Bool.cond_true]
        dsimp only [solFastScaleDivIvS2V, solGmpDivScaleS2V, solGmpCeilDivScaleS2V]
        simp only [solLitNat_eq, solKeepZS2V_eq]
      · rw [decide_eq_false h, Bool.cond_false]
    · dsimp only [solFastIvScaleZS2V]; rw [natBle_eq_decide]
      by_cases h : m1 ≤ m2
      · have hfl (p : ℕ) :
            solScaleNegFloorS2V p = solGmpDivScaleS2V (solGmpNegZS2V (Int.ofNat p)) := by
          rw [solScaleNegFloorS2V_eq, solGmpDivScaleS2V_eq, solGmpNegZS2V_eq, solIntNeg_eq,
            Int.ofNat_eq_natCast]
        have hcl (p : ℕ) :
            solScaleNegCeilS2V p = solGmpCeilDivScaleS2V (solGmpNegZS2V (Int.ofNat p)) := by
          rw [solScaleNegCeilS2V_eq, solGmpCeilDivScaleS2V_eq, solGmpNegZS2V_eq, solIntNeg_eq,
            Int.ofNat_eq_natCast]
        rw [decide_eq_true h, Bool.cond_true, solLitNat_eq]
        dsimp only [solFastIvScaleZRefS2V, solGmpMulZS2V, solFastScaleDivIvS2V]
        simp only [solKeepZS2V_eq, solLitNat_eq, hfl, hcl]
        by_cases heq : m1 = m2
        · subst heq
          cases solBleZ (solGmpNegZS2V (Int.ofNat (Nat.mul m1 (Nat.add n 1))))
            (solGmpNegZS2V (Int.ofNat (Nat.mul m1 (Nat.add n 1)))) <;> rfl
        · have hm : m1 * (n + 1) < m2 * (n + 1) :=
            Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_ne h heq) (Nat.succ_pos n)
          have hlt : ¬ (solGmpNegZS2V (Int.ofNat (Nat.mul m1 (Nat.add n 1))) ≤
              solGmpNegZS2V (Int.ofNat (Nat.mul m2 (Nat.add n 1)))) := by
            simp only [solGmpNegZS2V_eq, solIntNeg_eq, solNatMul_eq, solNatAdd_eq,
              Int.ofNat_eq_natCast]; omega
          rw [solBleZ_eq_decide, decide_eq_false hlt, Bool.cond_false]
      · rw [decide_eq_false h, Bool.cond_false]
  · rfl
  · rfl
  · rfl
private def solIvAddGmpS2V : IvInt → IvInt → IvInt
  | (alo, ahi), (blo, bhi) =>
      solKeepZS2V (solGmpAddZS2V alo blo) fun lo ↦
        solKeepZS2V (solGmpAddZS2V ahi bhi) fun hi ↦ (lo, hi)
private theorem solIvAddGmpS2V_eq (a b : IvInt) : solIvAddGmpS2V a b = SchurWeylLCert.ivAddIntP a b
    := by
  rcases a with ⟨alo, ahi⟩; rcases b with ⟨blo, bhi⟩
  dsimp only [solIvAddGmpS2V, SchurWeylLCert.ivAddIntP]
  simp only [solKeepZS2V_eq, solGmpAddZS2V_eq]
private def solIvSubGmpS2V : IvInt → IvInt → IvInt
  | (alo, ahi), (blo, bhi) =>
      solKeepZS2V (solGmpSubZS2V alo bhi) fun lo ↦
        solKeepZS2V (solGmpSubZS2V ahi blo) fun hi ↦ (lo, hi)
private theorem solIvSubGmpS2V_eq (a b : IvInt) : solIvSubGmpS2V a b = SchurWeylLCert.ivSubIntP a b
    := by
  rcases a with ⟨alo, ahi⟩; rcases b with ⟨blo, bhi⟩
  dsimp only [solIvSubGmpS2V, SchurWeylLCert.ivSubIntP]
  simp only [solKeepZS2V_eq, solGmpSubZS2V_eq]
private def solIvRatDivS2V (num den : ℤ) : IvInt :=
  solKeepZS2V (solGmpMulZS2V num (Int.ofNat 1000000000)) fun sc ↦
    solKeepZS2V (solGmpEdivZS2V sc den) fun qLo ↦
      solKeepZS2V (solGmpNegZS2V (solGmpEdivZS2V (solGmpNegZS2V sc) den)) fun qHi ↦ (qLo, qHi)
private theorem solIvRatDivS2V_eq (num den : ℤ) : solIvRatDivS2V num den = solIvRatDiv num den := by
  unfold solIvRatDivS2V solIvRatDiv swScale
  simp only [solKeepZS2V_eq, solSeqInt_eq, solGmpMulZS2V_eq, solGmpEdivZS2V_eq, solGmpNegZS2V_eq]
  rfl
private def solIvPythagS2V (uNum uDen : ℤ) : IvInt × IvInt :=
  solKeepZS2V (solGmpMulZS2V uDen uDen) fun dSq ↦ solKeepZS2V (solGmpMulZS2V uNum uNum) fun nSq ↦
      solKeepZS2V (solGmpAddZS2V dSq nSq) fun d ↦
        solForcePairS2V (solIvRatDivS2V (solGmpSubZS2V dSq nSq) d) fun cu ↦
          solForcePairS2V (solIvRatDivS2V (solGmpMulZS2V (solGmpMulZS2V (Int.ofNat 2) uNum) uDen) d)
            fun su ↦ (cu, su)
private theorem solIvPythagS2V_eq (uNum uDen : ℤ) : solIvPythagS2V uNum uDen = solIvPythag uNum uDen
    := by
  unfold solIvPythagS2V solIvPythag
  simp only [solKeepZS2V_eq, solSeqInt_eq, solForcePairS2V_eq, solSeqIv_eq, solGmpMulZS2V_eq,
    solGmpAddZS2V_eq, solGmpSubZS2V_eq, solIvRatDivS2V_eq]; rfl
private def solFastGroverStepS2V (cw sw : IvInt) (ce co : ℤ) (rest : List IvInt) : List IvInt :=
  cond (solIsZeroZS2V ce && solIsZeroZS2V co)
    ((Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: rest)
    (solForcePairS2V (solIvSubGmpS2V (solFastIvScaleZS2V cw ce) (solFastIvScaleZS2V sw co)) fun e' ↦
        solForcePairS2V (solIvAddGmpS2V (solFastIvScaleZS2V sw ce) (solFastIvScaleZS2V cw co))
          fun o' ↦ e' :: o' :: rest)
private theorem solFastGroverStepS2V_eq (cw sw : IvInt) (ce co : ℤ) (rest : List IvInt) :
    solFastGroverStepS2V cw sw ce co rest = solFastGroverStep cw sw ce co rest
    := by
  unfold solFastGroverStepS2V solFastGroverStep
  simp only [solIsZeroZS2V_eq, solForcePairS2V_eq, solSeqIv_eq, solFastIvScaleZS2V_eq,
    solIvSubGmpS2V_eq, solIvAddGmpS2V_eq]; rfl
private def solFastGroverWalkS2V : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, (cw, sw) :: ts', ce :: co :: cs' =>
      solFastGroverStepS2V cw sw ce co (solFastGroverWalkS2V k ts' cs')
  | k + 1, (cw, sw) :: ts', [ce] =>
      solFastGroverStepS2V cw sw ce (Int.ofNat 0) (solFastGroverWalkS2V k ts' [])
  | k + 1, _ :: ts', [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: solFastGroverWalkS2V k ts' []
  | k + 1, [], ce :: co :: cs' =>
      solFastGroverStepS2V (Int.ofNat 0, Int.ofNat 0) (Int.ofNat 0, Int.ofNat 0) ce co
        (solFastGroverWalkS2V k [] cs')
  | k + 1, [], [ce] =>
      solFastGroverStepS2V (Int.ofNat 0, Int.ofNat 0) (Int.ofNat 0, Int.ofNat 0) ce (Int.ofNat 0)
        (solFastGroverWalkS2V k [] [])
  | k + 1, [], [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: solFastGroverWalkS2V k [] []
private theorem solFastGroverWalkS2V_eq : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ),
    solFastGroverWalkS2V k ts cs = solFastGroverWalk k ts cs
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
      rcases ts with _ | ⟨⟨cw, sw⟩, ts'⟩ <;> rcases cs with _ | ⟨ce, _ | ⟨co, cs'⟩⟩ <;>
        simp only [solFastGroverWalkS2V, solFastGroverWalk,
          solFastGroverStepS2V_eq, solFastGroverWalkS2V_eq k] <;> rfl
private def solFastPieriPairS2V (uvDenZ u : ℤ) (lv rv : IvInt) (rest : List IvInt) : List IvInt :=
  cond (solIsZeroZS2V u) (lv :: rv :: rest) (cond (solIvIsZeroS2V lv && solIvIsZeroS2V rv)
      ((Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: rest)
      (match solIvPythagS2V u uvDenZ with
      | (cu, su) =>
          solForcePairS2V (solIvSubGmpS2V (solFastIvMulS2V cu lv) (solFastIvMulS2V su rv)) fun l' ↦
              solForcePairS2V (solIvAddGmpS2V (solFastIvMulS2V su lv) (solFastIvMulS2V cu rv))
                fun r' ↦ l' :: r' :: rest))
private theorem solFastPieriPairS2V_eq (uvDenZ u : ℤ) (lv rv : IvInt) (rest : List IvInt) :
    solFastPieriPairS2V uvDenZ u lv rv rest = solFastPieriPair uvDenZ u lv rv
    rest := by
  unfold solFastPieriPairS2V solFastPieriPair; rw [solIvPythagS2V_eq]
  rcases solIvPythag u uvDenZ with ⟨cu, su⟩
  simp only [solIsZeroZS2V_eq, solIvIsZeroS2V_eq, solForcePairS2V_eq, solSeqIv_eq,
    solFastIvMulS2V_eq, solIvSubGmpS2V_eq, solIvAddGmpS2V_eq]; rfl
private def solFastPieriWalkAuxS2V
    (uvDenZ : ℤ) (cv : IvInt) : ℕ → ℕ → List ℤ → List IvInt → List IvInt
  | 0, _, _, ss =>
      solBindIvS2V (SchurWeylLCert.headIvP ss) fun lastIv ↦
        let sc := Int.ofNat 1000000000
        solBindIvS2V
          (cond ((solBeqZ cv.1 sc && solBeqZ cv.2 sc) || solIvIsZeroS2V lastIv) lastIv
            (solFastIvMulS2V cv lastIv))
          fun outIv ↦ [outIv]
  | m + 1, s + 1, us, lv :: rv :: ss' => lv :: rv :: solFastPieriWalkAuxS2V uvDenZ cv m s us ss'
  | m + 1, s + 1, us, [lv] =>
      lv :: (Int.ofNat 0, Int.ofNat 0) :: solFastPieriWalkAuxS2V uvDenZ cv m s us []
  | m + 1, s + 1, us, [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) ::
        solFastPieriWalkAuxS2V uvDenZ cv m s us []
  | m + 1, 0, [], lv :: rv :: ss' => lv :: rv :: solFastPieriWalkAuxS2V uvDenZ cv m 0 [] ss'
  | m + 1, 0, [], [lv] =>
      lv :: (Int.ofNat 0, Int.ofNat 0) :: solFastPieriWalkAuxS2V uvDenZ cv m 0 [] []
  | m + 1, 0, [], [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) ::
        solFastPieriWalkAuxS2V uvDenZ cv m 0 [] []
  | m + 1, 0, u :: us', lv :: rv :: ss' =>
      solFastPieriPairS2V uvDenZ u lv rv (solFastPieriWalkAuxS2V uvDenZ cv m 0 us' ss')
  | m + 1, 0, u :: us', [lv] =>
      solFastPieriPairS2V uvDenZ u lv (Int.ofNat 0, Int.ofNat 0)
        (solFastPieriWalkAuxS2V uvDenZ cv m 0 us' [])
  | m + 1, 0, u :: us', [] =>
      solFastPieriPairS2V uvDenZ u (Int.ofNat 0, Int.ofNat 0) (Int.ofNat 0, Int.ofNat 0)
        (solFastPieriWalkAuxS2V uvDenZ cv m 0 us' [])
private theorem solFastPieriWalkAuxS2V_eq (uvDenZ : ℤ) (cv : IvInt) : ∀ (m sk : ℕ) (us : List ℤ) (ss
    : List IvInt), solFastPieriWalkAuxS2V uvDenZ cv m sk us ss =
    solFastPieriWalkAux uvDenZ cv m sk us ss
  | 0, _, _, ss => by
      unfold solFastPieriWalkAuxS2V solFastPieriWalkAux swScale
      simp only [solBindIvS2V_eq, solSeqIv_eq, solIvIsZeroS2V_eq, solFastIvMulS2V_eq]; rfl
  | m + 1, sk, us, ss => by
      rcases sk with _ | s <;> rcases us with _ | ⟨u, us'⟩ <;>
        rcases ss with _ | ⟨lv, _ | ⟨rv, ss'⟩⟩ <;>
        simp only [solFastPieriWalkAuxS2V, solFastPieriWalkAux,
          solFastPieriPairS2V_eq, solFastPieriWalkAuxS2V_eq uvDenZ cv m] <;> rfl
private def solFastPieriWalkS2V
    (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse) (naIv : List IvInt) :
    List IvInt :=
  match hNext, naIv with
  | 0, _ => []
  | m + 1, h0 :: ss =>
      h0 :: solFastPieriWalkAuxS2V (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin ss
  | m + 1, [] =>
      (Int.ofNat 0, Int.ofNat 0) ::
        solFastPieriWalkAuxS2V (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin []
private theorem solFastPieriWalkS2V_eq (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse) (naIv :
    List IvInt) : solFastPieriWalkS2V hNext uvDen cv sp naIv =
    solFastPieriWalk hNext uvDen cv sp naIv := by
  rcases hNext with _ | m <;> rcases naIv with _ | ⟨h0, ss⟩ <;>
    simp only [solFastPieriWalkS2V, solFastPieriWalk,
      solFastPieriWalkAuxS2V_eq]; rfl
private def solIvMidRadS2V : IvInt → ℤ × ℕ
  | (.ofNat a, .ofNat b) =>
      cond (Nat.ble a b) (solLitNat (Nat.div (Nat.add a b) 2) fun m ↦
          solLitNat (Nat.div (Nat.add (Nat.sub b a) 1) 2) fun r ↦ (Int.ofNat m, r))
        (solIvMidRad (.ofNat a, .ofNat b))
  | (.negSucc a, .negSucc b) =>
      cond (Nat.ble b a) (solLitNat (Nat.div (Nat.add (Nat.add a b) 1) 2) fun m ↦
          solLitNat (Nat.div (Nat.add (Nat.sub a b) 1) 2) fun r ↦ (Int.negSucc m, r))
        (solIvMidRad (.negSucc a, .negSucc b))
  | (.negSucc a, .ofNat b) =>
      solKeepZS2V (solGmpDiv2S2V (solGmpSubNatS2V b (Nat.add a 1))) fun mid ↦
        solLitNat (Nat.div (Nat.add (Nat.add b a) 2) 2) fun r ↦ (mid, r)
  | iv => solIvMidRad iv
private theorem solIvMidRadS2V_eq (iv : IvInt) : solIvMidRadS2V iv = solIvMidRad iv := by
  rcases iv with ⟨lo, hi⟩
  rcases lo with a | a <;> rcases hi with b | b
  · dsimp only [solIvMidRadS2V]; rw [natBle_eq_decide]
    by_cases h : a ≤ b
    · rw [decide_eq_true h, Bool.cond_true]; unfold solIvMidRad
      simp only [solSeqInt_eq, solLitNat_eq, solMaxZ_eq, solIntAdd_eq, solIntEdiv_eq, solIntSub_eq,
        solNatDiv_eq, solNatAdd_eq, solNatSub_eq, Int.ofNat_eq_natCast]
      exact Prod.ext (by omega) (by omega)
    · rw [decide_eq_false h, Bool.cond_false]
  · rfl
  · dsimp only [solIvMidRadS2V]; unfold solIvMidRad
    simp only [solKeepZS2V_eq, solGmpDiv2S2V_eq, solGmpSubNatS2V_eq, solSeqInt_eq, solLitNat_eq,
      solMaxZ_eq, solIntAdd_eq, solIntEdiv_eq, solIntSub_eq, solNatDiv_eq, solNatAdd_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq]
    exact Prod.ext (by omega) (by omega)
  · dsimp only [solIvMidRadS2V]; rw [natBle_eq_decide]
    by_cases h : b ≤ a
    · rw [decide_eq_true h, Bool.cond_true]; unfold solIvMidRad
      simp only [solSeqInt_eq, solLitNat_eq, solMaxZ_eq, solIntAdd_eq, solIntEdiv_eq, solIntSub_eq,
        solNatDiv_eq, solNatAdd_eq, solNatSub_eq, Int.negSucc_eq]
      exact Prod.ext (by omega) (by omega)
    · rw [decide_eq_false h, Bool.cond_false]
private def solFastRecenterS2V : List IvInt → List ℤ × ℕ
  | [] => ([], 0)
  | iv :: ivs =>
      match solIvMidRadS2V iv, solFastRecenterS2V ivs with
      | (mid, rad), (cs, acc) =>
          solLitNat (Nat.add (Nat.mul rad rad) acc) fun acc' ↦ (mid :: cs, acc')
private theorem solFastRecenterS2V_eq : ∀ (ivs : List IvInt), solFastRecenterS2V ivs =
    solFastRecenterAndRadSq ivs
  | [] => rfl
  | iv :: ivs => by
      unfold solFastRecenterS2V solFastRecenterAndRadSq
      rw [solIvMidRadS2V_eq, solFastRecenterS2V_eq ivs]
private def solFastPulseStepL2S2V
    (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) (cPref : List ℤ) (hAct rho
    : ℕ) (survUb : ℤ) (sp : SolSparsePulse) : List ℤ × ℕ × ℕ × ℤ :=
  solLitNat (solSumSqAbs cPref 0) fun normSqC ↦ solLitNat (solCeilIsqrt normSqC) fun normCUb ↦
      solLitNat (Nat.add normCUb rho) fun sumR ↦
        let sc := Int.ofNat 1000000000
        solKeepZS2V (solMinZ sc (solGmpCeilDivScaleS2V (Int.ofNat (Nat.mul sumR sumR))))
          fun oneMinusCumUb ↦ solKeepZS2V (solGmpAddZS2V survUb oneMinusCumUb) fun survUb' ↦
              solLitNat (solMinNat L (Nat.add hAct 1)) fun hNext ↦
                solBindIvS2V
                  (cond (Bool.not (hNext.beq L) || solIsZeroZS2V sp.vNum) (sc, sc)
                    ((solIvPythagS2V sp.vNum (Int.ofNat uvDen)).1))
                  fun cv ↦
                    match solFastRecenterS2V
                        (solFastPieriWalkS2V hNext uvDen cv sp
                          (solFastGroverWalkS2V hNext trigIvs cPref)) with
                    | (cNextRaw, radSqSum) =>
                        solSeqList
                          (solPadEmptyPair (solFastTrimZeroPairs cNextRaw))
                          fun cOut ↦ solLitNat (solMaxNat 1 (Nat.div cOut.length 2)) fun hAct' ↦
                              solLitNat (Nat.add rho (solCeilIsqrt radSqSum)) fun rho' ↦
                                (cOut, hAct', rho', survUb')
private theorem solFastPulseStepL2S2V_eq (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) (cPref :
    List ℤ) (hAct rho : ℕ) (survUb : ℤ) (sp : SolSparsePulse) : solFastPulseStepL2S2V L uvDen
    trigIvs cPref hAct rho survUb sp = solFastPulseStepL2 L uvDen trigIvs
    cPref hAct rho survUb sp := by
  unfold solFastPulseStepL2S2V solFastPulseStepL2 swScale
  simp only [solLitNat_eq, solKeepZS2V_eq, solSeqInt_eq, solBindIvS2V_eq, solSeqIv_eq,
    solSeqList_eq, solGmpCeilDivScaleS2V_eq, solGmpAddZS2V_eq, solIsZeroZS2V_eq,
    solIvPythagS2V_eq, solFastRecenterS2V_eq, solFastPieriWalkS2V_eq, solFastGroverWalkS2V_eq]; rfl
private def solFastWkbEvolveLoopS2V
    (qR qL qTauNum qTauDen qUvDen : ℕ) (qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ
    phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) (trigIvs
    : List (IvInt × IvInt)) : ℕ → ℕ → List ℤ → ℕ → ℕ → ℤ → List ℤ × ℕ × ℕ × ℤ
  | 0, _, cPref, hAct, rho, survUb => (cPref, hAct, rho, survUb)
  | rem + 1, t, cPref, hAct, rho, survUb =>
      match _s0EvalWkbPulseRef qR qL qTauNum qTauDen
          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with
      | ⟨wLo, uWin, vNum⟩ =>
          match solFastPulseStepL2S2V qL qUvDen trigIvs cPref hAct rho survUb
              ⟨wLo, uWin, vNum⟩ with
          | (cNext, hAct', rho', survUb') =>
              solSeqList cNext fun cNext' ↦ solLitNat hAct' fun ha ↦
                  solLitNat rho' fun rh ↦ solKeepZS2V survUb' fun sv ↦
                      solLitNat (Nat.add t 1) fun tNext ↦
                        solFastWkbEvolveLoopS2V qR qL qTauNum qTauDen qUvDen
                          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
                          rbTree ulnTree uldTree vdTree trigIvs rem tNext cNext' ha rh sv
private theorem solFastWkbEvolveLoopS2V_eq (qR qL qTauNum qTauDen qUvDen : ℕ) (qSOffQ qVBulkQ
    qAccelQ sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree :
    SolPairTree) (trigIvs : List (IvInt × IvInt)) : ∀ (rem t : ℕ) (cPref : List ℤ) (hAct rho : ℕ)
    (survUb : ℤ), solFastWkbEvolveLoopS2V qR qL qTauNum qTauDen qUvDen qSOffQ qVBulkQ qAccelQ sMaxQ
    gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree trigIvs rem t cPref hAct rho survUb =
    _s0WkbEvolveLoopRef qR qL qTauNum qTauDen qUvDen qSOffQ qVBulkQ qAccelQ
    sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree trigIvs rem t cPref hAct rho
    survUb
  | 0, _, _, _, _, _ => rfl
  | rem + 1, t, cPref, hAct, rho, survUb => by
      unfold solFastWkbEvolveLoopS2V _s0WkbEvolveLoopRef
      rcases _s0EvalWkbPulseRef qR qL qTauNum qTauDen
          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with ⟨wLo, uWin, vNum⟩
      dsimp only; rw [solFastPulseStepL2S2V_eq]
      rcases solFastPulseStepL2 qL qUvDen trigIvs cPref hAct rho survUb
          ⟨wLo, uWin, vNum⟩ with ⟨cNext, hAct', rho', survUb'⟩
      dsimp only; simp only [solSeqList_eq, solLitNat_eq, solKeepZS2V_eq, solSeqInt_eq]
      exact solFastWkbEvolveLoopS2V_eq qR qL qTauNum qTauDen qUvDen
        qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree trigIvs rem (Nat.add t 1) cNext hAct' rho' survUb'
private def solFastCheckWkbSliceS2V
    (q : SolWkbSched) (t len : ℕ) (trigIvs : List (IvInt × IvInt)) (cIn :
    List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ) (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) : Bool :=
  solLitNat q.r fun qR ↦ solLitNat q.L fun qL ↦
  solLitNat q.tauNum fun qTauNum ↦ solLitNat q.tauDen fun qTauDen ↦
  solLitNat q.uvDen fun qUvDen ↦ solSeqInt q.sOffQ fun qSOffQ ↦
  solSeqInt q.vBulkQ fun qVBulkQ ↦ solSeqInt q.accelQ fun qAccelQ ↦
  solWithTrigList trigIvs fun trigIvs' ↦ solWithIntList cIn fun cIn' ↦
  solSeqList (solRevSGList (solBuildWkbSGRev qR 0 (Nat.add qL 1) []) []) fun sgArr ↦
  solSeqInt (sgArr.getD (Nat.sub qL 1) (0, 0)).1 fun sMaxQ ↦
  let gTopNat := solFloorIsqrt (Nat.div (Nat.mul 1048576 (Nat.sub qR (Nat.sub qL 1))) qR)
  solSeqInt (Int.ofNat gTopNat) fun gTopQ ↦
  let km1 := Int.ofNat (solMaxNat 1 (Nat.sub q.K 1))
  solSeqInt (Int.mul km1 km1) fun km1Sq ↦
  solSeqInt (Int.ediv (Int.mul (Int.mul (Int.ofNat (Nat.sub q.K 1)) (Int.ofNat qTauNum)) 1024)
      (Int.ofNat qTauDen))
    fun phiTotQ ↦
  solWithPairTree (solBuildPairTree q.rBulkQ 8) fun rbTree ↦
  solWithPairTree (solBuildPairTree q.uLnchQ 10) fun ulnTree ↦
  solWithPairTree (solBuildPairTree q.uLandQ 10) fun uldTree ↦
  solWithPairTree (solBuildPairTree q.vDrainQ 6) fun vdTree ↦
  match solFastWkbEvolveLoopS2V qR qL qTauNum qTauDen qUvDen
      qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
      rbTree ulnTree uldTree vdTree trigIvs' len t cIn' hIn rhoIn survIn with
  | (c1, h1, rh1, sv1) =>
      solListIntBeq c1 cOut && h1.beq hOut && rh1.beq rhoOut && solBeqZ sv1 survOut
private theorem solFastCheckWkbSliceS2V_eq (q : SolWkbSched) (t len : ℕ) (trigIvs : List (IvInt ×
    IvInt)) (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ) (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut :
    ℤ) : solFastCheckWkbSliceS2V q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut =
    _s0CheckWkbSliceRef q t len trigIvs cIn hIn rhoIn survIn cOut hOut
    rhoOut survOut := by
  unfold solFastCheckWkbSliceS2V _s0CheckWkbSliceRef
  simp only [solLitNat_eq, solSeqInt_eq, solWithTrigList_eq, solWithIntList_eq, solSeqList_eq,
    solWithPairTree_eq, solFastWkbEvolveLoopS2V_eq]
private theorem solFastWkbStepS2V_eq
    {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)} {t len tNext : ℕ}
    {cIn : List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ} {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ} (ht
    : t + len = tNext) (hprev : SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn) (hfast :
    solFastCheckWkbSliceS2V q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut = true) :
    SolWkbRunPrefix q trigIvs tNext cOut hOut rhoOut survOut := by
  rw [solFastCheckWkbSliceS2V_eq] at hfast
  exact _s0WkbStepRef_eq ht hprev hfast
private def _s2vEvolutionL2Aux (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) : List SolSparsePulse → List ℤ × ℕ × ℤ
  | [] => (cPref, rho, survUb)
  | sp :: sps =>
      match solFastPulseStepL2S2V L uvDen trigIvs cPref hAct rho survUb sp with
      | (cNext, hAct', rho', survUb') =>
        solSeqList cNext fun cNext' ↦
          solLitNat hAct' fun ha ↦
            solLitNat rho' fun rh ↦
              solSeqInt survUb' fun sv ↦ _s2vEvolutionL2Aux L uvDen trigIvs cNext' ha rh sv sps
private theorem _s2vEvolutionL2Aux_eq (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) :
    ∀ (sps : List SolSparsePulse) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      _s2vEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb sps =
        fastEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb sps
  | [], _, _, _, _ => rfl
  | sp :: sps, cPref, hAct, rho, survUb => by
      unfold _s2vEvolutionL2Aux fastEvolutionL2Aux; rw [solFastPulseStepL2S2V_eq]
      rcases solFastPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with
        ⟨cNext, hAct', rho', survUb'⟩
      dsimp only; simp only [solSeqList_eq, solLitNat_eq, solSeqInt_eq]
      exact _s2vEvolutionL2Aux_eq L uvDen trigIvs sps cNext hAct' rho' survUb'
private def _s2vCheckBucketCertL2 (L rMin rMax tauNum tauDen uvDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) (sps : List SolSparsePulse)
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ) : Bool :=
  solWithPulseList sps fun sps ↦
    Nat.ble 2 L && Nat.ble L 1024 && Nat.ble L rMin && Nat.ble rMin rMax &&
    Nat.ble rMax 1024 && Nat.ble 1 uvDen &&
    Nat.ble 1 sps.length && Nat.ble sps.length 5120 &&
    certTailLbs.length.beq L &&
    sps.all solSparsePulseValid &&
    PulseM1.checkPulseBucketAngles L rMin rMax tauNum tauDen ratios trigIvs &&
    solWithTrigList trigIvs fun trigIvs' ↦
      match _s2vEvolutionL2Aux L uvDen trigIvs' [swScale, 0] 1 0 0 sps with
      | (cEnd, rhoEnd, survEnd) =>
          match solTerminalBoundsL2 L cEnd rhoEnd survEnd with
          | (p0Lb, tailLbs, sUb) =>
              tailLbs.length.beq L &&
              solBleZ 0 certP0Lb && solBleZ certP0Lb p0Lb &&
              solBleZ 0 certSurvUb && solBleZ sUb certSurvUb &&
              solBleZ 1 (certTailLbs.getD 0 0) &&
              solBleZ (certTailLbs.getD 0 0) swScale &&
              solBleZ 0 (certTailLbs.getD (Nat.sub L 1) 0) &&
              solAllLeZip certTailLbs tailLbs
private theorem _s2vCheckBucketCertL2_eq (L rMin rMax tauNum tauDen uvDen : ℕ) (ratios : List IvInt)
    (trigIvs : List (IvInt × IvInt)) (sps : List SolSparsePulse) (certP0Lb : ℤ) (certTailLbs : List
    ℤ) (certSurvUb : ℤ) : _s2vCheckBucketCertL2 L rMin rMax tauNum tauDen uvDen ratios trigIvs sps
    certP0Lb certTailLbs certSurvUb = fastCheckBucketCertL2 L rMin rMax tauNum tauDen uvDen
    ratios trigIvs sps certP0Lb certTailLbs certSurvUb := by
  unfold _s2vCheckBucketCertL2 fastCheckBucketCertL2
  simp only [solWithPulseList_eq, solWithTrigList_eq, _s2vEvolutionL2Aux_eq]
private def _s2vCheckExplicitStage (L r tauNum tauDen uvDen : ℕ) (ratios : List IvInt) (trigIvs :
    List (IvInt × IvInt)) (sps : List SolSparsePulse) (p0Lb : ℤ) (tailLbs : List ℤ) (survUb : ℤ)
    (vTable : ℕ → ℤ) : Bool :=
  _s2vCheckBucketCertL2 L r r tauNum tauDen uvDen ratios trigIvs sps
    p0Lb tailLbs survUb &&
  checkPulseCascadeStepTable L r tauNum tauDen survUb p0Lb tailLbs vTable
private theorem _s2vCheckExplicitStage_eq (L r tauNum tauDen uvDen : ℕ) (ratios : List IvInt)
    (trigIvs : List (IvInt × IvInt)) (sps : List SolSparsePulse) (p0Lb : ℤ) (tailLbs : List ℤ)
    (survUb : ℤ) (vTable : ℕ → ℤ) : _s2vCheckExplicitStage L r tauNum tauDen uvDen ratios trigIvs
    sps p0Lb tailLbs survUb vTable = checkPulseExplicitStageTable L r tauNum tauDen uvDen ratios
    trigIvs sps p0Lb tailLbs survUb vTable := by
  unfold _s2vCheckExplicitStage; rw [_s2vCheckBucketCertL2_eq]; apply fastCheckExplicitStage_eq
/-- Chunk 0 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c0 : List (SolSparsePulse) := [⟨1,[5188,4315],(-52)⟩, ⟨1,[5139,2213],
  (-19)⟩, ⟨1,[5082,1728],(-3)⟩, ⟨1,[5045,1828],0⟩, ⟨1,[4877,3310],0⟩, ⟨1,[4747,2655],0⟩, ⟨1,[4633,
  2251],0⟩, ⟨1,[4404,2808],0⟩, ⟨1,[4233,2667],0⟩, ⟨1,[4070,2707],0⟩, ⟨1,[3906,2786],0⟩, ⟨1,[3761,
  2759],0⟩]
/-- Chunk 1 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c1 : List (SolSparsePulse) := [⟨1,[3545,2852],0⟩, ⟨1,[3340,2842],0⟩, ⟨1,
  [3208,2788],0⟩, ⟨1,[3062,2858],0⟩, ⟨1,[2893,2935],0⟩, ⟨1,[2764,2936],0⟩, ⟨1,[2666,2917],0⟩, ⟨1,
  [2557,2908],0⟩, ⟨1,[2423,2893],0⟩, ⟨1,[2284,2873],0⟩, ⟨1,[2176,2856],0⟩, ⟨1,[2101,2846],0⟩]
/-- Chunk 2 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c2 : List (SolSparsePulse) := [⟨1,[2010,2842],0⟩, ⟨1,[1909,2823],0⟩, ⟨1,
  [1868,2781],0⟩, ⟨1,[1847,2738],0⟩, ⟨1,[1732,2700],0⟩, ⟨1,[1591,2642],0⟩, ⟨1,[1514,2597],0⟩, ⟨1,
  [1453,2609],0⟩, ⟨1,[1453,2565],0⟩, ⟨1,[1428,2499],0⟩, ⟨1,[1306,2513],11⟩, ⟨1,[1154,2379],278⟩ ]
/-- Chunk 3 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c3 : List (SolSparsePulse) := [⟨1,[1194,2377],(-163)⟩, ⟨1,[881,2338],
  (-1631)⟩, ⟨1,[943,2302],1769⟩, ⟨1,[1025,1751],10905⟩, ⟨1,[935,1421],13626⟩, ⟨1,[944,1313],14328⟩,
  ⟨1,[1051,1310],14089⟩, ⟨1,[1143,1288],13804⟩, ⟨1,[1164,1238],13885⟩, ⟨1,[1118,1190],14181⟩, ⟨1,
  [1031,1158],14393⟩, ⟨1,[931,1140],14413⟩]
/-- Chunk 4 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c4 : List (SolSparsePulse) := [⟨1,[841,1132],14315⟩, ⟨1,[777,1127],14213⟩,
  ⟨1,[744,1114],14181⟩, ⟨1,[741,1085],14225⟩, ⟨1,[761,1045],14321⟩, ⟨1,[792,1001],14426⟩, ⟨1,[827,
  969],14506⟩, ⟨1,[856,946],14552⟩, ⟨1,[872,924],14558⟩, ⟨1,[876,904],14537⟩, ⟨1,[868,881],14499⟩,
  ⟨1,[849,859],14464⟩]
/-- Chunk 5 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c5 : List (SolSparsePulse) := [⟨1,[819,845],14445⟩, ⟨1,[786,838],14452⟩,
  ⟨1,[750,831],14477⟩, ⟨1,[712,819],14518⟩, ⟨1,[675,800],14568⟩, ⟨1,[640,777],14615⟩, ⟨1,[605,754],
  14654⟩, ⟨1,[576,735],14671⟩, ⟨1,[550,721],14675⟩, ⟨1,[529,711],14669⟩, ⟨1,[515,700],14633⟩, ⟨1,
  [499,683],14607⟩]
/-- Chunk 6 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c6 : List (SolSparsePulse) := [⟨1,[487,662],14580⟩, ⟨1,[484,638],14539⟩,
  ⟨1,[475,616],14520⟩, ⟨1,[472,597],14510⟩, ⟨1,[473,583],14516⟩, ⟨1,[458,577],14500⟩, ⟨1,[458,570],
  14534⟩, ⟨1,[462,563],14578⟩, ⟨1,[461,556],14593⟩, ⟨1,[459,548],14572⟩, ⟨1,[451,532],14602⟩, ⟨1,
  [439,509],14697⟩]
/-- Chunk 7 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c7 : List (SolSparsePulse) := [⟨1,[438,493],14675⟩, ⟨1,[432,473],14695⟩,
  ⟨1,[430,453],14708⟩, ⟨1,[440,446],14649⟩, ⟨1,[426,435],14624⟩, ⟨1,[407,426],14637⟩, ⟨1,[388,413],
  14697⟩, ⟨1,[404,417],14637⟩, ⟨1,[396,406],14649⟩, ⟨1,[390,396],14643⟩, ⟨1,[421,418],14465⟩, ⟨1,
  [395,407],14472⟩]
/-- Chunk 8 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c8 : List (SolSparsePulse) := [⟨1,[371,401],14426⟩, ⟨1,[362,397],14290⟩,
  ⟨1,[387,407],14333⟩, ⟨1,[399,407],14278⟩, ⟨1,[398,401],14202⟩, ⟨1,[382,383],14219⟩, ⟨1,[396,389],
  14411⟩, ⟨1,[389,377],14498⟩, ⟨1,[346,334],14395⟩, ⟨1,[399,370],14294⟩, ⟨1,[433,392],13634⟩, ⟨1,
  [442,403],12965⟩]
/-- Chunk 9 of `solExplicitPulses_r3`. -/
def solExplicitPulses_r3_c9 : List (SolSparsePulse) := [⟨1,[401,375],13649⟩, ⟨1,[372,363],14619⟩,
  ⟨1,[254,268],10873⟩, ⟨1,[0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 3` (`L = 3`). -/
def solExplicitPulses_r3 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r3_c0) ( solExplicitPulses_r3_c1)) ( List.append ( solExplicitPulses_r3_c2) (
  List.append ( solExplicitPulses_r3_c3) ( solExplicitPulses_r3_c4)))) ( List.append ( List.append (
  solExplicitPulses_r3_c5) ( solExplicitPulses_r3_c6)) ( List.append ( solExplicitPulses_r3_c7) (
  List.append ( solExplicitPulses_r3_c8) ( solExplicitPulses_r3_c9))))
/-- Stratum angle-ratio intervals for `r = 3`. -/
def solRatios_r3 : List (IvInt) := [(816496579,816496582),(577350268,577350271)]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 3`. -/
def solTrigIvs_r3 : List (IvInt × IvInt) := [((996018251,996018252),(89149547,89149548)),
  ((997344913,997344914),(72822547,72822548)),((998672162,998672163),(51516124,51516125))]
/-- Certified suffix probability lower bounds for `r = 3`. -/
def solTailLbs_r3 : List (ℤ) := [999999912,999998529,999642477]
/-- Stage specification for explicit `m = 1` conveyor at `r = 3`. -/
def solStage_r3 : PulseM1StageSpec := ⟨3, 8926806, 100000000,
    solToSwLPulses 3 65536 solExplicitPulses_r3⟩
/-- Chunk 0 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c0 : List (SolSparsePulse) := [⟨1,[6107,4315,4315],(-52)⟩, ⟨1,[6035,3260,
  4294],(-19)⟩, ⟨1,[5923,3390,4127],(-3)⟩, ⟨1,[5766,3472,3643],0⟩, ⟨1,[5584,3441,2842],(-2)⟩, ⟨1,
  [5371,3508,2062],0⟩, ⟨1,[5145,3533,1750],0⟩, ⟨1,[4904,3606,1979],0⟩, ⟨1,[4658,3637,2318],0⟩, ⟨1,
  [4418,3653,2365],0⟩, ⟨1,[4175,3701,2218],0⟩, ⟨1,[3942,3726,2195],0⟩]
/-- Chunk 1 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c1 : List (SolSparsePulse) := [⟨1,[3724,3731,2291],0⟩, ⟨1,[3513,3740,2311],
  0⟩, ⟨1,[3313,3742,2283],0⟩, ⟨1,[3134,3721,2332],0⟩, ⟨1,[2971,3684,2396],0⟩, ⟨1,[2814,3647,2395],
  0⟩, ⟨1,[2667,3604,2394],0⟩, ⟨1,[2537,3541,2444],0⟩, ⟨1,[2423,3467,2489],0⟩, ⟨1,[2315,3397,2501],
  0⟩, ⟨1,[2212,3324,2521],0⟩, ⟨1,[2120,3240,2559],0⟩]
/-- Chunk 2 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c2 : List (SolSparsePulse) := [⟨1,[2038,3152,2588],0⟩, ⟨1,[1963,3065,2604],
  0⟩, ⟨1,[1894,2974,2623],0⟩, ⟨1,[1829,2879,2648],0⟩, ⟨1,[1764,2786,2666],0⟩, ⟨1,[1707,2697,2676],
  0⟩, ⟨1,[1658,2612,2684],0⟩, ⟨1,[1605,2529,2691],0⟩, ⟨1,[1557,2443,2695],0⟩, ⟨1,[1515,2361,2693],
  0⟩, ⟨1,[1453,2288,2684],0⟩, ⟨1,[1437,2217,2677],2⟩]
/-- Chunk 3 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c3 : List (SolSparsePulse) := [⟨1,[1373,2151,2662],0⟩, ⟨1,[1326,2080,2649],
  (-2)⟩, ⟨1,[1281,2007,2633],(-3)⟩, ⟨1,[1233,1940,2615],(-2)⟩, ⟨1,[1186,1879,2594],0⟩, ⟨1,[1142,
  1819,2568],0⟩, ⟨1,[1098,1755,2541],4⟩, ⟨1,[1048,1683,2514],0⟩, ⟨1,[998,1598,2489],3⟩, ⟨1,[966,
  1510,2465],2⟩, ⟨1,[973,1414,2442],(-5)⟩, ⟨1,[1032,1283,2417],(-11)⟩]
/-- Chunk 4 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c4 : List (SolSparsePulse) := [⟨1,[1129,1119,2389],7⟩, ⟨1,[1212,942,2371],
  (-422)⟩, ⟨1,[1191,1146,1590],12533⟩, ⟨1,[1083,1441,1377],13898⟩, ⟨1,[1008,1238,1427],13449⟩, ⟨1,
  [964,1227,1342],13848⟩, ⟨1,[938,1268,1320],13798⟩, ⟨1,[916,1247,1301],13786⟩, ⟨1,[892,1194,1268],
  13871⟩, ⟨1,[877,1151,1237],13958⟩, ⟨1,[867,1130,1214],13974⟩, ⟨1,[861,1121,1192],13949⟩]
/-- Chunk 5 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c5 : List (SolSparsePulse) := [⟨1,[855,1114,1169],13938⟩, ⟨1,[854,1101,
  1144],13971⟩, ⟨1,[855,1082,1117],14031⟩, ⟨1,[856,1058,1090],14091⟩, ⟨1,[855,1030,1063],14147⟩, ⟨1,
  [851,1002,1039],14184⟩, ⟨1,[839,975,1018],14201⟩, ⟨1,[825,951,998],14210⟩, ⟨1,[807,932,978],
  14213⟩, ⟨1,[785,917,957],14219⟩, ⟨1,[765,907,936],14226⟩, ⟨1,[737,897,916],14235⟩]
/-- Chunk 6 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c6 : List (SolSparsePulse) := [⟨1,[710,889,897],14248⟩, ⟨1,[691,884,879],
  14262⟩, ⟨1,[666,871,862],14280⟩, ⟨1,[649,859,844],14291⟩, ⟨1,[640,847,824],14308⟩, ⟨1,[618,819,
  809],14307⟩, ⟨1,[619,802,791],14323⟩, ⟨1,[630,787,773],14346⟩, ⟨1,[641,768,758],14364⟩, ⟨1,[657,
  752,745],14353⟩, ⟨1,[672,737,730],14350⟩, ⟨1,[687,721,711],14380⟩]
/-- Chunk 7 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c7 : List (SolSparsePulse) := [⟨1,[717,717,699],14339⟩, ⟨1,[744,711,684],
  14345⟩, ⟨1,[776,709,667],14359⟩, ⟨1,[821,720,655],14319⟩, ⟨1,[839,710,645],14293⟩, ⟨1,[849,695,
  636],14278⟩, ⟨1,[857,678,622],14303⟩, ⟨1,[895,690,614],14245⟩, ⟨1,[904,676,598],14270⟩, ⟨1,[909,
  661,579],14304⟩, ⟨1,[946,680,575],14198⟩, ⟨1,[918,641,560],14247⟩]
/-- Chunk 8 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c8 : List (SolSparsePulse) := [⟨1,[886,603,555],14232⟩, ⟨1,[863,579,550],
  14112⟩, ⟨1,[868,586,544],14126⟩, ⟨1,[854,579,538],14026⟩, ⟨1,[823,561,535],13885⟩, ⟨1,[772,529,
  521],13813⟩, ⟨1,[748,527,518],13901⟩, ⟨1,[700,504,509],13927⟩, ⟨1,[614,447,479],13832⟩, ⟨1,[624,
  484,504],13792⟩, ⟨1,[614,503,531],13257⟩, ⟨1,[580,498,561],12688⟩]
/-- Chunk 9 of `solExplicitPulses_r4`. -/
def solExplicitPulses_r4_c9 : List (SolSparsePulse) := [⟨1,[500,444,554],13374⟩, ⟨1,[433,402,552],
  14379⟩, ⟨1,[282,270,448],10853⟩, ⟨1,[0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 4` (`L = 4`). -/
def solExplicitPulses_r4 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r4_c0) ( solExplicitPulses_r4_c1)) ( List.append ( solExplicitPulses_r4_c2) (
  List.append ( solExplicitPulses_r4_c3) ( solExplicitPulses_r4_c4)))) ( List.append ( List.append (
  solExplicitPulses_r4_c5) ( solExplicitPulses_r4_c6)) ( List.append ( solExplicitPulses_r4_c7) (
  List.append ( solExplicitPulses_r4_c8) ( solExplicitPulses_r4_c9))))
/-- Stratum angle-ratio intervals for `r = 4`. -/
def solRatios_r4 : List (IvInt) := [(866025402,866025405),(707106780,707106783),(499999999,
  500000002)]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 4`. -/
def solTrigIvs_r4 : List (IvInt × IvInt) := [((994924353,994924354),(100625696,100625697)),
  ((996192459,996192460),(87181329,87181331)),((997461102,997461103),(71213410,71213412)),
  ((998730282,998730283),(50376812,50376813))]
/-- Certified suffix probability lower bounds for `r = 4`. -/
def solTailLbs_r4 : List (ℤ) := [999999785,999999642,999987492,998659877]
/-- Stage specification for explicit `m = 1` conveyor at `r = 4`. -/
def solStage_r4 : PulseM1StageSpec := ⟨4, 10079629, 100000000,
    solToSwLPulses 4 65536 solExplicitPulses_r4⟩
/-- Chunk 0 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c0 : List (SolSparsePulse) := [⟨1,[7599,4912,4315,4315],(-52)⟩, ⟨1,[7440,
  4446,3605,4294],(-19)⟩, ⟨1,[7203,4387,3602,4127],(-3)⟩, ⟨1,[6982,4453,3457,3642],0⟩, ⟨1,[6614,
  4773,3281,2844],(-2)⟩, ⟨1,[6267,4637,3242,2085],0⟩, ⟨1,[5922,4653,3211,1821],0⟩, ⟨1,[5482,4828,
  3205,2076],0⟩, ⟨1,[5146,4818,3273,2368],0⟩, ⟨1,[4813,4885,3472,2364],0⟩, ⟨1,[4459,4864,3651,2249],
  0⟩, ⟨1,[4165,4807,3471,2229],0⟩]
/-- Chunk 1 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c1 : List (SolSparsePulse) := [⟨1,[3882,4811,3345,2234],0⟩, ⟨1,[3615,4736,
  3562,2243],0⟩, ⟨1,[3400,4626,3653,2270],0⟩, ⟨1,[3216,4556,3615,2295],0⟩, ⟨1,[3044,4441,3692,2349],
  0⟩, ⟨1,[2875,4274,3750,2403],0⟩, ⟨1,[2706,4137,3716,2389],0⟩, ⟨1,[2575,4017,3720,2333],0⟩, ⟨1,
  [2498,3869,3771,2346],0⟩, ⟨1,[2407,3715,3784,2442],0⟩, ⟨1,[2266,3569,3770,2505],0⟩, ⟨1,[2139,3420,
  3768,2510],0⟩]
/-- Chunk 2 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c2 : List (SolSparsePulse) := [⟨1,[2094,3277,3760,2514],0⟩, ⟨1,[2104,3150,
  3722,2547],0⟩, ⟨1,[2080,3033,3664,2588],0⟩, ⟨1,[1980,2922,3603,2619],0⟩, ⟨1,[1842,2827,3539,2665],
  0⟩, ⟨1,[1730,2742,3464,2715],0⟩, ⟨1,[1673,2647,3385,2730],0⟩, ⟨1,[1659,2541,3312,2724],0⟩, ⟨1,
  [1657,2440,3247,2738],0⟩, ⟨1,[1649,2353,3183,2776],0⟩, ⟨1,[1621,2285,3109,2815],0⟩, ⟨1,[1590,2228,
  3012,2844],0⟩]
/-- Chunk 3 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c3 : List (SolSparsePulse) := [⟨1,[1538,2165,2896,2865],0⟩, ⟨1,[1483,2081,
  2789,2877],0⟩, ⟨1,[1421,2003,2711,2873],0⟩, ⟨1,[1355,1965,2647,2860],0⟩, ⟨1,[1296,1961,2573,2857],
  0⟩, ⟨1,[1252,1939,2504,2862],0⟩, ⟨1,[1220,1851,2457,2859],0⟩, ⟨1,[1193,1705,2368,2859],0⟩, ⟨1,
  [1167,1568,2227,2857],0⟩, ⟨1,[1148,1497,2171,2827],0⟩, ⟨1,[1147,1466,2143,2795],0⟩, ⟨1,[1175,1415,
  1965,2806],0⟩]
/-- Chunk 4 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c4 : List (SolSparsePulse) := [⟨1,[1231,1361,1922,2804],0⟩, ⟨1,[1278,1326,
  1922,2685],(-4)⟩, ⟨1,[1236,1411,1585,2785],(-246)⟩, ⟨1,[1129,1617,1594,2663],418⟩, ⟨1,[1069,1606,
  1352,2628],(-375)⟩, ⟨1,[1041,1546,1363,2461],6346⟩, ⟨1,[1027,1480,1411,1766],12629⟩, ⟨1,[1015,
  1424,1444,1656],13985⟩, ⟨1,[997,1383,1545,1572],14185⟩, ⟨1,[984,1352,1607,1519],14162⟩, ⟨1,[973,
  1324,1562,1484],14282⟩, ⟨1,[962,1293,1444,1438],14504⟩]
/-- Chunk 5 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c5 : List (SolSparsePulse) := [⟨1,[950,1259,1321,1389],14648⟩, ⟨1,[941,
  1226,1242,1361],14624⟩, ⟨1,[934,1195,1218,1359],14478⟩, ⟨1,[925,1170,1239,1365],14330⟩, ⟨1,[917,
  1149,1280,1352],14287⟩, ⟨1,[904,1132,1320,1307],14387⟩, ⟨1,[884,1118,1343,1240],14592⟩, ⟨1,[864,
  1107,1346,1175],14825⟩, ⟨1,[839,1099,1328,1130],15008⟩, ⟨1,[811,1091,1295,1106],15088⟩, ⟨1,[786,
  1085,1253,1096],15056⟩, ⟨1,[754,1075,1207,1088],14935⟩]
/-- Chunk 6 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c6 : List (SolSparsePulse) := [⟨1,[723,1062,1161,1081],14773⟩, ⟨1,[701,
  1051,1120,1075],14624⟩, ⟨1,[673,1030,1080,1069],14532⟩, ⟨1,[655,1010,1046,1058],14520⟩, ⟨1,[643,
  989,1015,1037],14588⟩, ⟨1,[621,951,980,1006],14714⟩, ⟨1,[621,925,951,967],14866⟩, ⟨1,[630,902,925,
  927],15011⟩, ⟨1,[641,876,898,891],15131⟩, ⟨1,[656,853,875,865],15202⟩, ⟨1,[671,831,853,846],
  15226⟩, ⟨1,[687,809,832,830],15223⟩]
/-- Chunk 7 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c7 : List (SolSparsePulse) := [⟨1,[716,800,820,818],15160⟩, ⟨1,[744,791,
  808,800],15102⟩, ⟨1,[777,788,800,778],15045⟩, ⟨1,[821,799,804,755],14973⟩, ⟨1,[840,788,797,733],
  14921⟩, ⟨1,[851,774,791,714],14879⟩, ⟨1,[860,759,782,698],14871⟩, ⟨1,[898,775,793,692],14807⟩, ⟨1,
  [907,765,786,686],14798⟩, ⟨1,[913,754,775,680],14800⟩, ⟨1,[950,776,790,684],14694⟩, ⟨1,[923,740,
  762,677],14712⟩]
/-- Chunk 8 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c8 : List (SolSparsePulse) := [⟨1,[891,703,735,673],14687⟩, ⟨1,[868,678,
  714,670],14589⟩, ⟨1,[873,683,710,659],14618⟩, ⟨1,[859,674,694,650],14559⟩, ⟨1,[828,650,670,645],
  14466⟩, ⟨1,[776,611,632,630],14417⟩, ⟨1,[752,601,616,618],14509⟩, ⟨1,[703,569,584,606],14557⟩, ⟨1,
  [617,502,522,580],14520⟩, ⟨1,[626,530,541,583],14558⟩, ⟨1,[616,539,549,593],14089⟩, ⟨1,[582,524,
  544,612],13490⟩]
/-- Chunk 9 of `solExplicitPulses_r5`. -/
def solExplicitPulses_r5_c9 : List (SolSparsePulse) := [⟨1,[500,461,497,601],14048⟩, ⟨1,[434,411,
  461,608],14889⟩, ⟨1,[282,273,333,544],11190⟩, ⟨1,[0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 5` (`L = 5`). -/
def solExplicitPulses_r5 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r5_c0) ( solExplicitPulses_r5_c1)) ( List.append ( solExplicitPulses_r5_c2) (
  List.append ( solExplicitPulses_r5_c3) ( solExplicitPulses_r5_c4)))) ( List.append ( List.append (
  solExplicitPulses_r5_c5) ( solExplicitPulses_r5_c6)) ( List.append ( solExplicitPulses_r5_c7) (
  List.append ( solExplicitPulses_r5_c8) ( solExplicitPulses_r5_c9))))
/-- Stratum angle-ratio intervals for `r = 5`. -/
def solRatios_r5 : List (IvInt) := [(894427189,894427192),(774596668,774596671),(632455531,
  632455534),(447213594,447213597)]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 5`. -/
def solTrigIvs_r5 : List (IvInt × IvInt) := [((992452499,992452500),(122629669,122629670)),
  ((993960478,993960479),(109738633,109738634)),((995469217,995469218),(95084369,95084371)),
  ((996978717,996978718),(77675205,77675206)),((998488977,998488978),(54952350,54952352))]
/-- Certified suffix probability lower bounds for `r = 5`. -/
def solTailLbs_r5 : List (ℤ) := [999999780,999999713,999999659,999986124,998768839]
/-- Stage specification for explicit `m = 1` conveyor at `r = 5`. -/
def solStage_r5 : PulseM1StageSpec := ⟨5, 12293912, 100000000,
    solToSwLPulses 5 65536 solExplicitPulses_r5⟩
/-- Chunk 0 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c0 : List (SolSparsePulse) := [⟨1,[8820,5584,4614,4315,4315],(-52)⟩, ⟨1,
  [8596,5342,4025,3777,4294],(-19)⟩, ⟨1,[8267,5402,4087,3733,4127],(-3)⟩, ⟨1,[7854,5472,4216,3506,
  3642],0⟩, ⟨1,[7366,5646,4259,3197,2844],(-2)⟩, ⟨1,[6870,5626,4174,3056,2086],0⟩, ⟨1,[6332,5740,
  4236,3110,1822],0⟩, ⟨1,[5851,5778,4272,3292,2078],0⟩, ⟨1,[5406,5791,4313,3394,2373],0⟩, ⟨1,[4980,
  5749,4434,3345,2376],0⟩, ⟨1,[4607,5690,4416,3274,2282],0⟩, ⟨1,[4268,5622,4450,3301,2292],0⟩]
/-- Chunk 1 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c1 : List (SolSparsePulse) := [⟨1,[3975,5484,4559,3362,2323],0⟩, ⟨1,[3716,
  5328,4594,3356,2333],0⟩, ⟨1,[3465,5170,4622,3394,2335],0⟩, ⟨1,[3253,4981,4662,3470,2311],0⟩, ⟨1,
  [3087,4775,4675,3487,2293],0⟩, ⟨1,[2928,4557,4695,3461,2298],0⟩, ⟨1,[2784,4342,4691,3526,2326],0⟩,
  ⟨1,[2673,4156,4650,3596,2354],0⟩, ⟨1,[2571,3984,4605,3608,2359],0⟩, ⟨1,[2480,3811,4546,3634,2375],
  0⟩, ⟨1,[2392,3656,4460,3684,2417],0⟩, ⟨1,[2292,3508,4367,3720,2441],0⟩]
/-- Chunk 2 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c2 : List (SolSparsePulse) := [⟨1,[2202,3342,4271,3754,2439],0⟩, ⟨1,[2144,
  3181,4159,3787,2437],0⟩, ⟨1,[2102,3068,4047,3794,2466],0⟩, ⟨1,[2053,2983,3943,3792,2510],0⟩, ⟨1,
  [1991,2883,3822,3805,2528],0⟩, ⟨1,[1926,2768,3675,3816,2547],0⟩, ⟨1,[1872,2677,3531,3807,2587],0⟩,
  ⟨1,[1831,2622,3410,3783,2628],0⟩, ⟨1,[1797,2569,3310,3751,2666],0⟩, ⟨1,[1760,2489,3220,3703,2706],
  0⟩, ⟨1,[1712,2397,3130,3637,2740],0⟩, ⟨1,[1665,2320,3031,3567,2759],0⟩]
/-- Chunk 3 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c3 : List (SolSparsePulse) := [⟨1,[1608,2267,2924,3501,2780],0⟩, ⟨1,[1557,
  2224,2820,3439,2814],0⟩, ⟨1,[1506,2179,2723,3376,2852],0⟩, ⟨1,[1457,2123,2643,3305,2884],0⟩, ⟨1,
  [1415,2056,2584,3223,2907],0⟩, ⟨1,[1386,1988,2523,3135,2922],0⟩, ⟨1,[1369,1927,2439,3047,2933],0⟩,
  ⟨1,[1356,1865,2349,2967,2948],0⟩, ⟨1,[1341,1797,2280,2885,2974],0⟩, ⟨1,[1325,1737,2243,2796,2994],
  0⟩, ⟨1,[1319,1686,2194,2727,2989],0⟩, ⟨1,[1337,1637,2089,2640,2980],0⟩]
/-- Chunk 4 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c4 : List (SolSparsePulse) := [⟨1,[1380,1599,1960,2555,2971],0⟩, ⟨1,[1412,
  1576,1888,2505,2966],0⟩, ⟨1,[1356,1621,1863,2422,2958],2⟩, ⟨1,[1235,1727,1797,2254,2949],27⟩, ⟨1,
  [1162,1713,1669,2235,2905],6⟩, ⟨1,[1122,1663,1556,2159,2901],(-88)⟩, ⟨1,[1096,1603,1555,1869,
  2948],(-2)⟩, ⟨1,[1072,1551,1710,1917,2842],(-167)⟩, ⟨1,[1043,1514,1837,1632,2897],484⟩, ⟨1,[1021,
  1492,1814,1277,2817],(-314)⟩, ⟨1,[1001,1475,1739,1521,2256],10047⟩, ⟨1,[983,1458,1679,1668,1858],
  13553⟩]
/-- Chunk 5 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c5 : List (SolSparsePulse) := [⟨1,[965,1437,1640,1708,1688],14306⟩, ⟨1,
  [951,1414,1611,1700,1635],14530⟩, ⟨1,[940,1389,1583,1665,1611],14645⟩, ⟨1,[929,1361,1553,1617,
  1579],14705⟩, ⟨1,[919,1331,1520,1571,1539],14722⟩, ⟨1,[905,1300,1486,1535,1499],14720⟩, ⟨1,[885,
  1266,1451,1510,1463],14729⟩, ⟨1,[864,1233,1419,1492,1429],14765⟩, ⟨1,[839,1199,1389,1476,1397],
  14825⟩, ⟨1,[812,1164,1364,1455,1363],14896⟩, ⟨1,[788,1133,1345,1429,1328],14961⟩, ⟨1,[756,1097,
  1329,1397,1297],15010⟩]
/-- Chunk 6 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c6 : List (SolSparsePulse) := [⟨1,[726,1062,1317,1362,1272],15036⟩, ⟨1,
  [704,1032,1311,1329,1250],15040⟩, ⟨1,[677,995,1300,1298,1227],15032⟩, ⟨1,[658,963,1290,1272,1204],
  15026⟩, ⟨1,[646,934,1278,1253,1178],15035⟩, ⟨1,[624,891,1252,1234,1152],15064⟩, ⟨1,[624,864,1230,
  1219,1123],15112⟩, ⟨1,[633,844,1205,1203,1092],15170⟩, ⟨1,[643,823,1172,1186,1060],15228⟩, ⟨1,
  [658,807,1139,1167,1029],15277⟩, ⟨1,[673,792,1101,1147,1002],15307⟩, ⟨1,[688,777,1061,1123,979],
  15322⟩]
/-- Chunk 7 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c7 : List (SolSparsePulse) := [⟨1,[717,778,1029,1103,960],15312⟩, ⟨1,[745,
  777,996,1080,943],15295⟩, ⟨1,[777,783,967,1058,926],15274⟩, ⟨1,[821,802,951,1044,909],15249⟩, ⟨1,
  [840,800,920,1025,890],15236⟩, ⟨1,[851,792,889,1008,870],15227⟩, ⟨1,[860,783,858,991,849],15243⟩,
  ⟨1,[898,804,854,991,831],15227⟩, ⟨1,[908,799,831,979,812],15243⟩, ⟨1,[914,793,807,965,792],15266⟩,
  ⟨1,[951,819,815,973,779],15206⟩, ⟨1,[924,784,774,947,761],15223⟩]
/-- Chunk 8 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c8 : List (SolSparsePulse) := [⟨1,[893,748,734,922,746],15199⟩, ⟨1,[870,
  724,705,898,737],15108⟩, ⟨1,[876,729,702,884,722],15113⟩, ⟨1,[862,719,686,859,713],15040⟩, ⟨1,
  [831,693,660,826,708],14931⟩, ⟨1,[779,651,619,778,700],14839⟩, ⟨1,[755,637,606,747,689],14860⟩,
  ⟨1,[706,601,573,702,680],14861⟩, ⟨1,[620,529,508,630,664],14827⟩, ⟨1,[628,553,532,626,661],14915⟩,
  ⟨1,[618,557,541,616,672],14550⟩, ⟨1,[583,537,531,600,693],13996⟩]
/-- Chunk 9 of `solExplicitPulses_r6`. -/
def solExplicitPulses_r6_c9 : List (SolSparsePulse) := [⟨1,[501,470,477,549,682],14476⟩, ⟨1,[435,
  417,435,512,690],15232⟩, ⟨1,[282,275,302,392,658],11502⟩, ⟨1,[0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 6` (`L = 6`). -/
def solExplicitPulses_r6 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r6_c0) ( solExplicitPulses_r6_c1)) ( List.append ( solExplicitPulses_r6_c2) (
  List.append ( solExplicitPulses_r6_c3) ( solExplicitPulses_r6_c4)))) ( List.append ( List.append (
  solExplicitPulses_r6_c5) ( solExplicitPulses_r6_c6)) ( List.append ( solExplicitPulses_r6_c7) (
  List.append ( solExplicitPulses_r6_c8) ( solExplicitPulses_r6_c9))))
/-- Stratum angle-ratio intervals for `r = 6`. -/
def solRatios_r6 : List (IvInt) := [(912870928,912870931),(816496579,816496582),(707106780,
  707106783),(577350268,577350271),(408248289,408248292)]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 6`. -/
def solTrigIvs_r6 : List (IvInt × IvInt) := [((990064033,990064034),(140617248,140617249)),
  ((991717737,991717738),(128436479,128436480)),((993372357,993372358),(114940677,114940678)),
  ((995027893,995027894),(99596642,99596643)),((996684345,996684346),(81365318,81365319)),
  ((998341714,998341715),(57565799,57565800))]
/-- Certified suffix probability lower bounds for `r = 6`. -/
def solTailLbs_r6 : List (ℤ) := [999999737,999999733,999999731,999999469,999981059,998355322]
/-- Stage specification for explicit `m = 1` conveyor at `r = 6`. -/
def solStage_r6 : PulseM1StageSpec := ⟨6, 14108483, 100000000,
    solToSwLPulses 6 65536 solExplicitPulses_r6⟩
/-- Chunk 0 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c0 : List (SolSparsePulse) := [⟨1,[9884,6231,5002,4494,4315,4315],(-52)⟩,
  ⟨1,[9560,6151,4552,3926,3880,4294],(-19)⟩, ⟨1,[9107,6221,4754,3946,3812,4127],(-3)⟩, ⟨1,[8531,
  6338,5006,3939,3533,3642],0⟩, ⟨1,[7927,6419,5010,3880,3126,2844],(-2)⟩, ⟨1,[7295,6541,5004,3879,
  2864,2086],0⟩, ⟨1,[6683,6558,5070,4063,2858,1822],0⟩, ⟨1,[6096,6595,5112,4196,3066,2078],0⟩, ⟨1,
  [5552,6549,5180,4181,3229,2373],0⟩, ⟨1,[5080,6459,5222,4145,3237,2376],0⟩, ⟨1,[4670,6338,5318,
  4181,3232,2283],0⟩, ⟨1,[4325,6155,5339,4225,3310,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c1 : List (SolSparsePulse) := [⟨1,[4016,5936,5367,4240,3370,2326],0⟩, ⟨1,
  [3759,5684,5447,4286,3343,2341],0⟩, ⟨1,[3550,5442,5475,4315,3321,2350],0⟩, ⟨1,[3349,5194,5483,
  4348,3329,2337],0⟩, ⟨1,[3158,4932,5455,4418,3361,2331],0⟩, ⟨1,[3000,4680,5393,4436,3383,2339],0⟩,
  ⟨1,[2876,4438,5314,4464,3388,2350],0⟩, ⟨1,[2773,4230,5190,4536,3409,2348],0⟩, ⟨1,[2672,4063,5064,
  4557,3430,2330],0⟩, ⟨1,[2573,3884,4963,4569,3445,2327],0⟩, ⟨1,[2485,3699,4829,4622,3498,2345],0⟩,
  ⟨1,[2410,3551,4658,4650,3563,2362],0⟩]
/-- Chunk 2 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c2 : List (SolSparsePulse) := [⟨1,[2340,3426,4487,4639,3577,2371],0⟩, ⟨1,
  [2270,3294,4323,4611,3587,2376],0⟩, ⟨1,[2202,3164,4168,4559,3633,2385],0⟩, ⟨1,[2142,3053,4025,
  4503,3660,2399],0⟩, ⟨1,[2089,2962,3887,4462,3682,2411],0⟩, ⟨1,[2038,2875,3758,4404,3745,2432],0⟩,
  ⟨1,[1985,2787,3635,4312,3804,2465],0⟩, ⟨1,[1931,2708,3498,4211,3812,2492],0⟩, ⟨1,[1880,2644,3352,
  4106,3807,2499],0⟩, ⟨1,[1832,2593,3236,3991,3823,2514],0⟩, ⟨1,[1782,2541,3155,3877,3840,2561],0⟩,
  ⟨1,[1739,2479,3078,3774,3838,2616],0⟩]
/-- Chunk 3 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c3 : List (SolSparsePulse) := [⟨1,[1691,2410,2989,3671,3821,2651],0⟩, ⟨1,
  [1650,2345,2905,3561,3794,2680],0⟩, ⟨1,[1610,2290,2834,3451,3761,2719],0⟩, ⟨1,[1570,2239,2763,
  3353,3726,2751],0⟩, ⟨1,[1534,2184,2682,3258,3689,2775],0⟩, ⟨1,[1507,2123,2602,3157,3635,2809],0⟩,
  ⟨1,[1487,2058,2532,3058,3562,2850],0⟩, ⟨1,[1469,1992,2474,2965,3490,2885],0⟩, ⟨1,[1445,1923,2416,
  2874,3426,2911],0⟩, ⟨1,[1419,1863,2355,2792,3359,2935],0⟩, ⟨1,[1402,1817,2297,2726,3281,2962],0⟩,
  ⟨1,[1408,1786,2240,2662,3199,2989],0⟩]
/-- Chunk 4 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c4 : List (SolSparsePulse) := [⟨1,[1438,1774,2170,2582,3124,3009],0⟩, ⟨1,
  [1459,1771,2086,2493,3041,3032],0⟩, ⟨1,[1394,1800,2011,2426,2941,3058],0⟩, ⟨1,[1264,1864,1961,
  2381,2853,3062],0⟩, ⟨1,[1184,1844,1892,2309,2780,3053],0⟩, ⟨1,[1138,1799,1840,2195,2690,3043],
  (-4)⟩, ⟨1,[1108,1741,1840,2091,2605,3037],0⟩, ⟨1,[1081,1682,1909,2025,2563,3034],(-15)⟩, ⟨1,[1049,
  1628,1978,1937,2409,3041],(-4)⟩, ⟨1,[1025,1586,1971,1796,2326,3028],3⟩, ⟨1,[1003,1548,1911,1701,
  2236,2958],127⟩, ⟨1,[985,1510,1844,1715,2038,3067],(-225)⟩]
/-- Chunk 5 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c5 : List (SolSparsePulse) := [⟨1,[966,1469,1790,1889,2024,2899],(-20)⟩,
  ⟨1,[952,1429,1752,2020,1588,3041],(-1055)⟩, ⟨1,[941,1388,1725,1984,1437,2914],2704⟩, ⟨1,[930,1347,
  1704,1906,1687,2160],11914⟩, ⟨1,[919,1307,1683,1842,1793,1847],14249⟩, ⟨1,[905,1267,1661,1796,
  1798,1726],14647⟩, ⟨1,[885,1226,1635,1761,1781,1687],14729⟩, ⟨1,[864,1186,1606,1731,1764,1665],
  14761⟩, ⟨1,[840,1147,1574,1700,1742,1629],14787⟩, ⟨1,[813,1109,1539,1667,1708,1581],14828⟩, ⟨1,
  [788,1075,1505,1632,1664,1536],14888⟩, ⟨1,[756,1037,1467,1595,1618,1502],14956⟩]
/-- Chunk 6 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c6 : List (SolSparsePulse) := [⟨1,[726,1000,1428,1560,1575,1478],15021⟩,
  ⟨1,[704,970,1392,1529,1538,1454],15072⟩, ⟨1,[676,933,1349,1501,1506,1425],15110⟩, ⟨1,[657,903,
  1309,1481,1476,1391],15137⟩, ⟨1,[646,877,1270,1466,1448,1355],15157⟩, ⟨1,[623,837,1217,1447,1422,
  1321],15173⟩, ⟨1,[623,816,1175,1435,1399,1289],15185⟩, ⟨1,[633,802,1135,1423,1378,1258],15198⟩,
  ⟨1,[643,787,1092,1406,1359,1228],15214⟩, ⟨1,[658,777,1053,1387,1342,1200],15239⟩, ⟨1,[673,767,
  1013,1362,1325,1173],15274⟩, ⟨1,[688,759,974,1331,1306,1147],15317⟩]
/-- Chunk 7 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c7 : List (SolSparsePulse) := [⟨1,[717,765,947,1303,1289,1122],15360⟩, ⟨1,
  [745,770,921,1268,1267,1099],15399⟩, ⟨1,[777,781,901,1233,1244,1076],15426⟩, ⟨1,[822,806,896,1206,
  1225,1054],15439⟩, ⟨1,[840,808,873,1165,1200,1033],15441⟩, ⟨1,[851,804,849,1123,1177,1013],15430⟩,
  ⟨1,[860,798,826,1080,1152,992],15422⟩, ⟨1,[898,823,831,1059,1141,972],15395⟩, ⟨1,[908,821,815,
  1022,1123,951],15382⟩, ⟨1,[914,817,798,985,1106,928],15380⟩, ⟨1,[951,846,813,976,1109,910],15334⟩,
  ⟨1,[924,813,775,926,1088,889],15338⟩]
/-- Chunk 8 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c8 : List (SolSparsePulse) := [⟨1,[892,778,737,879,1069,870],15321⟩, ⟨1,
  [870,754,711,840,1051,856],15259⟩, ⟨1,[875,759,711,821,1037,836],15265⟩, ⟨1,[862,748,698,792,1013,
  823],15214⟩, ⟨1,[830,721,673,755,980,815],15132⟩, ⟨1,[779,677,631,705,932,807],15038⟩, ⟨1,[755,
  662,618,678,891,796],15010⟩, ⟨1,[706,623,584,635,837,789],14961⟩, ⟨1,[620,548,517,564,756,778],
  14902⟩, ⟨1,[628,569,540,573,730,766],14998⟩, ⟨1,[618,570,548,572,701,773],14735⟩, ⟨1,[583,547,534,
  558,670,793],14260⟩]
/-- Chunk 9 of `solExplicitPulses_r7`. -/
def solExplicitPulses_r7_c9 : List (SolSparsePulse) := [⟨1,[502,477,475,504,608,777],14677⟩, ⟨1,
  [435,420,428,464,566,782],15405⟩, ⟨1,[282,277,292,337,453,789],11812⟩, ⟨1,[0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 7` (`L = 7`). -/
def solExplicitPulses_r7 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r7_c0) ( solExplicitPulses_r7_c1)) ( List.append ( solExplicitPulses_r7_c2) (
  List.append ( solExplicitPulses_r7_c3) ( solExplicitPulses_r7_c4)))) ( List.append ( List.append (
  solExplicitPulses_r7_c5) ( solExplicitPulses_r7_c6)) ( List.append ( solExplicitPulses_r7_c7) (
  List.append ( solExplicitPulses_r7_c8) ( solExplicitPulses_r7_c9))))
/-- Stratum angle-ratio intervals for `r = 7`. -/
def solRatios_r7 : List (IvInt) := [(925820098,925820101),(845154253,845154256),(755928945,
  755928948),(654653669,654653672),(534522482,534522485),(377964472,377964475)]
/-- Chunk 0 of `solTrigIvs_r7`. -/
def solTrigIvs_r7_c0 : List (IvInt × IvInt) := [((987725581,987725582),(156199151,156199152)),
  ((989475987,989475988),(144697166,144697167)),((991227420,991227421),(132167323,132167325)),
  ((992979880,992979881),(118283379,118283380)),((994733367,994733368),(102496474,102496475)),
  ((996487883,996487884),(83737079,83737081))]
/-- Chunk 1 of `solTrigIvs_r7`. -/
def solTrigIvs_r7_c1 : List (IvInt × IvInt) := [((998243427,998243428),(59245758,59245760))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 7`. -/
def solTrigIvs_r7 : List (IvInt × IvInt) := List.append ( solTrigIvs_r7_c0) ( solTrigIvs_r7_c1)
/-- Certified suffix probability lower bounds for `r = 7`. -/
def solTailLbs_r7 : List (ℤ) := [999999650,999999650,999999647,999999638,999999147,999960725,
  997572079]
/-- Stage specification for explicit `m = 1` conveyor at `r = 7`. -/
def solStage_r7 : PulseM1StageSpec := ⟨7, 15684139, 100000000,
    solToSwLPulses 7 65536 solExplicitPulses_r7⟩
/-- Chunk 0 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c0 : List (SolSparsePulse) := [⟨1,[10885,6840,5412,4748,4434,4315,4315],
  (-52)⟩, ⟨1,[10481,6860,5085,4239,3911,3949,4294],(-19)⟩, ⟨1,[9897,6972,5444,4350,3901,3865,4127],
  (-3)⟩, ⟨1,[9178,7158,5711,4487,3804,3551,3642],0⟩, ⟨1,[8406,7229,5638,4532,3630,3079,2844],(-2)⟩,
  ⟨1,[7620,7337,5713,4668,3545,2734,2086],0⟩, ⟨1,[6901,7366,5789,4871,3678,2685,1822],0⟩, ⟨1,[6244,
  7334,5902,4883,3866,2901,2078],0⟩, ⟨1,[5663,7223,5946,4818,3970,3087,2373],0⟩, ⟨1,[5170,7061,6002,
  4861,4032,3098,2376],0⟩, ⟨1,[4757,6823,6112,4936,4111,3085,2283],0⟩, ⟨1,[4392,6547,6155,4980,4145,
  3167,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c1 : List (SolSparsePulse) := [⟨1,[4078,6237,6193,5063,4104,3247,2326],0⟩,
  ⟨1,[3820,5921,6201,5080,4076,3265,2341],0⟩, ⟨1,[3601,5614,6180,5098,4114,3293,2351],0⟩, ⟨1,[3415,
  5319,6113,5204,4173,3327,2339],0⟩, ⟨1,[3253,5040,6013,5262,4205,3345,2335],0⟩, ⟨1,[3107,4771,5889,
  5292,4254,3328,2346],0⟩, ⟨1,[2977,4521,5733,5335,4301,3298,2362],0⟩, ⟨1,[2866,4298,5559,5366,4288,
  3298,2366],0⟩, ⟨1,[2772,4110,5367,5386,4311,3332,2354],0⟩, ⟨1,[2684,3945,5168,5370,4403,3374,
  2351],0⟩, ⟨1,[2595,3785,4975,5334,4452,3402,2355],0⟩, ⟨1,[2511,3635,4779,5297,4474,3438,2349],0⟩]
/-- Chunk 2 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c2 : List (SolSparsePulse) := [⟨1,[2437,3510,4586,5233,4525,3485,2338],0⟩,
  ⟨1,[2372,3398,4412,5136,4570,3493,2332],0⟩, ⟨1,[2311,3283,4251,5024,4596,3473,2341],0⟩, ⟨1,[2250,
  3171,4089,4907,4617,3503,2364],0⟩, ⟨1,[2191,3079,3934,4785,4627,3575,2388],0⟩, ⟨1,[2134,3008,3800,
  4651,4633,3612,2405],0⟩, ⟨1,[2076,2943,3684,4504,4633,3629,2422],0⟩, ⟨1,[2021,2869,3570,4362,4610,
  3670,2447],0⟩, ⟨1,[1970,2789,3459,4227,4567,3714,2466],0⟩, ⟨1,[1923,2715,3359,4090,4516,3745,
  2466],0⟩, ⟨1,[1877,2655,3271,3955,4448,3781,2469],0⟩, ⟨1,[1839,2602,3183,3838,4365,3819,2500],0⟩]
/-- Chunk 3 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c3 : List (SolSparsePulse) := [⟨1,[1796,2547,3092,3727,4285,3844,2548],0⟩,
  ⟨1,[1758,2487,3009,3605,4206,3864,2577],0⟩, ⟨1,[1718,2422,2944,3488,4114,3880,2594],0⟩, ⟨1,[1675,
  2355,2891,3393,4007,3883,2628],0⟩, ⟨1,[1632,2288,2833,3310,3895,3875,2670],0⟩, ⟨1,[1597,2223,2761,
  3222,3785,3863,2703],0⟩, ⟨1,[1567,2165,2686,3133,3682,3848,2730],0⟩, ⟨1,[1538,2114,2619,3052,3582,
  3826,2756],0⟩, ⟨1,[1504,2065,2563,2975,3484,3794,2786],0⟩, ⟨1,[1467,2024,2509,2896,3385,3751,
  2819],0⟩, ⟨1,[1440,1995,2451,2817,3290,3696,2859],0⟩, ⟨1,[1437,1976,2385,2747,3204,3633,2902],0⟩]
/-- Chunk 4 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c4 : List (SolSparsePulse) := [⟨1,[1459,1970,2308,2684,3120,3567,2942],0⟩,
  ⟨1,[1475,1964,2223,2620,3028,3501,2978],0⟩, ⟨1,[1405,1966,2155,2552,2937,3430,3009],0⟩, ⟨1,[1272,
  1980,2125,2487,2859,3353,3032],0⟩, ⟨1,[1189,1930,2080,2430,2787,3273,3049],0⟩, ⟨1,[1141,1863,2051,
  2361,2707,3194,3066],0⟩, ⟨1,[1110,1786,2054,2268,2619,3114,3088],0⟩, ⟨1,[1082,1708,2096,2178,2545,
  3025,3109],0⟩, ⟨1,[1050,1636,2139,2108,2476,2937,3119],0⟩, ⟨1,[1025,1575,2137,2048,2376,2864,
  3122],0⟩, ⟨1,[1004,1522,2097,2023,2260,2782,3122],9⟩, ⟨1,[985,1472,2043,2053,2178,2684,3112],0⟩]
/-- Chunk 5 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c5 : List (SolSparsePulse) := [⟨1,[966,1422,1987,2142,2109,2591,3116],0⟩,
  ⟨1,[952,1376,1934,2214,1986,2471,3124],(-6)⟩, ⟨1,[941,1332,1885,2190,1831,2409,3115],21⟩, ⟨1,[930,
  1290,1837,2112,1779,2185,3090],(-30)⟩, ⟨1,[919,1250,1787,2029,1955,2065,3079],40⟩, ⟨1,[905,1211,
  1734,1964,2208,1810,3084],(-67)⟩, ⟨1,[885,1171,1678,1921,2215,1452,3057],(-215)⟩, ⟨1,[864,1133,
  1620,1894,2098,1761,2360],11036⟩, ⟨1,[840,1096,1562,1874,1999,1899,1929],14234⟩, ⟨1,[813,1059,
  1503,1855,1935,1915,1812],14729⟩, ⟨1,[788,1026,1449,1838,1892,1890,1764],14843⟩, ⟨1,[756,989,1392,
  1815,1859,1854,1732],14921⟩]
/-- Chunk 6 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c6 : List (SolSparsePulse) := [⟨1,[726,953,1339,1789,1828,1816,1697],
  14992⟩, ⟨1,[704,925,1292,1761,1796,1779,1653],15046⟩, ⟨1,[676,890,1241,1724,1761,1744,1607],
  15086⟩, ⟨1,[657,861,1195,1686,1725,1711,1567],15119⟩, ⟨1,[646,838,1153,1646,1691,1682,1535],
  15154⟩, ⟨1,[623,801,1100,1592,1656,1654,1506],15195⟩, ⟨1,[623,783,1061,1543,1628,1625,1475],
  15241⟩, ⟨1,[633,773,1027,1492,1605,1594,1441],15288⟩, ⟨1,[643,762,991,1437,1585,1561,1406],15333⟩,
  ⟨1,[658,756,960,1382,1570,1528,1372],15369⟩, ⟨1,[673,751,929,1325,1557,1495,1339],15396⟩, ⟨1,[688,
  747,900,1267,1542,1465,1308],15416⟩]
/-- Chunk 7 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c7 : List (SolSparsePulse) := [⟨1,[717,756,884,1218,1530,1438,1278],15434⟩,
  ⟨1,[745,766,868,1168,1513,1413,1250],15455⟩, ⟨1,[777,780,859,1124,1493,1389,1222],15479⟩, ⟨1,[822,
  808,864,1094,1475,1368,1194],15505⟩, ⟨1,[840,813,850,1050,1443,1346,1167],15526⟩, ⟨1,[851,811,833,
  1008,1407,1323,1140],15538⟩, ⟨1,[860,808,815,967,1364,1296,1115],15542⟩, ⟨1,[898,836,828,953,1337,
  1277,1090],15533⟩, ⟨1,[908,836,816,922,1292,1253,1067],15520⟩, ⟨1,[914,833,804,891,1246,1230,
  1043],15510⟩, ⟨1,[951,863,824,892,1223,1225,1022],15484⟩, ⟨1,[924,831,788,847,1163,1206,999],
  15478⟩]
/-- Chunk 8 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c8 : List (SolSparsePulse) := [⟨1,[892,797,751,803,1106,1192,979],15466⟩,
  ⟨1,[870,773,725,770,1055,1182,961],15429⟩, ⟨1,[875,778,728,761,1019,1174,941],15425⟩, ⟨1,[862,766,
  715,740,974,1159,925],15391⟩, ⟨1,[830,739,689,710,922,1134,912],15339⟩, ⟨1,[779,693,647,664,858,
  1093,902],15261⟩, ⟨1,[755,676,633,645,813,1050,891],15202⟩, ⟨1,[706,636,597,607,754,990,885],
  15112⟩, ⟨1,[620,559,527,539,669,902,881],15008⟩, ⟨1,[628,578,550,555,656,850,867],15061⟩, ⟨1,[618,
  577,555,559,638,797,872],14878⟩, ⟨1,[583,553,538,546,611,745,892],14484⟩]
/-- Chunk 9 of `solExplicitPulses_r8`. -/
def solExplicitPulses_r8_c9 : List (SolSparsePulse) := [⟨1,[501,481,475,490,549,666,874],14796⟩, ⟨1,
  [435,423,425,446,504,613,874],15504⟩, ⟨1,[282,278,287,315,378,510,943],12248⟩, ⟨1,[0,0,0,0,0,0,0],
  (-96)⟩]
/-- Explicit rational pulses for `r = 8` (`L = 8`). -/
def solExplicitPulses_r8 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r8_c0) ( solExplicitPulses_r8_c1)) ( List.append ( solExplicitPulses_r8_c2) (
  List.append ( solExplicitPulses_r8_c3) ( solExplicitPulses_r8_c4)))) ( List.append ( List.append (
  solExplicitPulses_r8_c5) ( solExplicitPulses_r8_c6)) ( List.append ( solExplicitPulses_r8_c7) (
  List.append ( solExplicitPulses_r8_c8) ( solExplicitPulses_r8_c9))))
/-- Stratum angle-ratio intervals for `r = 8`. -/
def solRatios_r8 : List (IvInt) := [(935414345,935414348),(866025402,866025405),(790569414,
  790569417),(707106780,707106783),(612372434,612372437),(499999999,500000002),(353553389,
  353553392)]
/-- Chunk 0 of `solTrigIvs_r8`. -/
def solTrigIvs_r8_c0 : List (IvInt × IvInt) := [((985214125,985214126),(171327544,171327545)),
  ((987058361,987058362),(160361435,160361437)),((988903739,988903740),(148557709,148557710)),
  ((990750259,990750260),(135697909,135697911)),((992597921,992597922),(121446966,121446968)),
  ((994446726,994446727),(105241191,105241193))]
/-- Chunk 1 of `solTrigIvs_r8`. -/
def solTrigIvs_r8_c1 : List (IvInt × IvInt) := [((996296673,996296674),(85982192,85982193)),
  ((998147765,998147766),(60836165,60836167))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 8`. -/
def solTrigIvs_r8 : List (IvInt × IvInt) := List.append ( solTrigIvs_r8_c0) ( solTrigIvs_r8_c1)
/-- Certified suffix probability lower bounds for `r = 8`. -/
def solTailLbs_r8 : List (ℤ) := [999999552,999999550,999999548,999999544,999999536,999998515,
  999935778,996459295]
/-- Stage specification for explicit `m = 1` conveyor at `r = 8`. -/
def solStage_r8 : PulseM1StageSpec := ⟨8, 17217698, 100000000,
    solToSwLPulses 8 65536 solExplicitPulses_r8⟩
/-- Chunk 0 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c0 : List (SolSparsePulse) := [⟨1,[11869,7418,5820,5032,4614,4400,4315,
  4315],(-52)⟩, ⟨1,[11360,7709,5592,4602,4098,3922,3999,4294],(-19)⟩, ⟨1,[10590,7765,6174,4819,4158,
  3891,3902,4127],(-3)⟩, ⟨1,[9736,7863,6397,5045,4194,3732,3564,3642],0⟩, ⟨1,[8790,8078,6433,5179,
  4146,3472,3046,2844],(-2)⟩, ⟨1,[7884,8097,6465,5464,4198,3313,2641,2086],0⟩, ⟨1,[7101,8091,6519,
  5613,4406,3394,2562,1822],0⟩, ⟨1,[6358,8010,6604,5585,4573,3592,2784,2078],0⟩, ⟨1,[5732,7804,6685,
  5643,4703,3725,2985,2373],0⟩, ⟨1,[5249,7505,6869,5663,4844,3786,2995,2376],0⟩, ⟨1,[4801,7215,6833,
  5637,4904,3870,2971,2283],0⟩, ⟨1,[4440,6825,6908,5768,4885,3972,3044,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c1 : List (SolSparsePulse) := [⟨1,[4169,6432,6933,5745,4903,4045,3120,
  2326],0⟩, ⟨1,[3912,6073,6869,5878,4955,4110,3145,2341],0⟩, ⟨1,[3689,5743,6717,5998,4933,4174,3182,
  2351],0⟩, ⟨1,[3491,5423,6608,5923,4930,4190,3232,2339],0⟩, ⟨1,[3316,5092,6457,6014,5020,4175,3282,
  2335],0⟩, ⟨1,[3183,4808,6218,6113,5004,4189,3316,2347],0⟩, ⟨1,[3087,4599,5970,6115,5055,4227,3342,
  2363],0⟩, ⟨1,[2995,4408,5755,6049,5229,4231,3373,2369],0⟩, ⟨1,[2888,4184,5545,6004,5201,4207,3393,
  2361],0⟩, ⟨1,[2779,3990,5279,5980,5199,4254,3394,2364],0⟩, ⟨1,[2685,3881,5041,5852,5331,4299,3389,
  2376],0⟩, ⟨1,[2606,3776,4881,5698,5370,4263,3405,2380],0⟩]
/-- Chunk 2 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c2 : List (SolSparsePulse) := [⟨1,[2535,3615,4690,5585,5355,4327,3433,
  2379],0⟩, ⟨1,[2468,3459,4459,5446,5351,4480,3440,2379],0⟩, ⟨1,[2406,3370,4284,5264,5355,4467,3429,
  2383],0⟩, ⟨1,[2348,3324,4164,5073,5356,4423,3459,2388],0⟩, ⟨1,[2291,3260,4032,4913,5300,4516,3514,
  2388],0⟩, ⟨1,[2234,3162,3882,4765,5222,4592,3504,2391],0⟩, ⟨1,[2177,3060,3769,4596,5153,4622,3494,
  2405],0⟩, ⟨1,[2122,2975,3689,4441,5056,4653,3586,2424],0⟩, ⟨1,[2072,2907,3586,4303,4954,4646,3668,
  2430],0⟩, ⟨1,[2026,2848,3457,4139,4863,4644,3617,2426],0⟩, ⟨1,[1979,2791,3357,3987,4726,4688,3586,
  2439],0⟩, ⟨1,[1939,2735,3313,3899,4561,4691,3695,2474],0⟩]
/-- Chunk 3 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c3 : List (SolSparsePulse) := [⟨1,[1891,2677,3281,3819,4438,4636,3784,
  2487],0⟩, ⟨1,[1848,2617,3217,3697,4335,4589,3786,2470],0⟩, ⟨1,[1800,2553,3116,3574,4203,4548,3799,
  2487],0⟩, ⟨1,[1748,2490,3008,3495,4068,4482,3843,2557],0⟩, ⟨1,[1697,2429,2920,3432,3964,4402,3878,
  2619],0⟩, ⟨1,[1652,2374,2852,3339,3862,4324,3908,2623],0⟩, ⟨1,[1613,2326,2798,3218,3730,4245,3931,
  2615],0⟩, ⟨1,[1575,2281,2746,3121,3601,4164,3929,2655],0⟩, ⟨1,[1533,2234,2691,3078,3516,4076,3921,
  2704],0⟩, ⟨1,[1489,2187,2631,3059,3448,3966,3930,2719],0⟩, ⟨1,[1456,2145,2566,3019,3360,3842,3933,
  2741],0⟩, ⟨1,[1449,2111,2500,2942,3258,3733,3906,2787],0⟩]
/-- Chunk 4 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c4 : List (SolSparsePulse) := [⟨1,[1467,2088,2439,2848,3175,3646,3867,
  2828],0⟩, ⟨1,[1480,2062,2383,2760,3110,3554,3836,2860],0⟩, ⟨1,[1408,2029,2350,2684,3036,3447,3798,
  2899],0⟩, ⟨1,[1274,1999,2353,2620,2949,3348,3739,2941],0⟩, ⟨1,[1191,1923,2329,2557,2871,3275,3670,
  2979],0⟩, ⟨1,[1142,1838,2309,2490,2804,3196,3604,3017],0⟩, ⟨1,[1110,1750,2300,2418,2737,3086,3534,
  3055],0⟩, ⟨1,[1082,1664,2307,2363,2666,2980,3454,3086],0⟩, ⟨1,[1050,1585,2307,2330,2604,2917,3372,
  3110],0⟩, ⟨1,[1025,1520,2270,2307,2554,2869,3303,3130],0⟩, ⟨1,[1004,1464,2202,2301,2485,2780,3243,
  3148],0⟩, ⟨1,[985,1413,2120,2318,2378,2659,3143,3175],0⟩]
/-- Chunk 5 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c5 : List (SolSparsePulse) := [⟨1,[966,1363,2033,2360,2269,2593,3017,3195],
  0⟩, ⟨1,[952,1319,1950,2394,2193,2557,2952,3190],0⟩, ⟨1,[941,1278,1873,2377,2146,2423,2889,3182],
  0⟩, ⟨1,[930,1239,1799,2325,2158,2246,2791,3178],0⟩, ⟨1,[919,1203,1728,2261,2258,2161,2722,3201],
  0⟩, ⟨1,[905,1167,1658,2199,2390,2096,2529,3198],0⟩, ⟨1,[885,1130,1589,2145,2421,1967,2498,3163],
  (-4)⟩, ⟨1,[864,1095,1522,2095,2341,1838,2247,3201],23⟩, ⟨1,[840,1059,1458,2045,2226,2010,2112,
  3162],80⟩, ⟨1,[813,1023,1397,1991,2129,2435,2002,3115],507⟩, ⟨1,[788,992,1341,1934,2067,2381,1269,
  3288],356⟩, ⟨1,[756,955,1285,1870,2030,2197,1842,2087],13383⟩]
/-- Chunk 6 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c6 : List (SolSparsePulse) := [⟨1,[726,921,1233,1804,2005,2079,2076,1901],
  14842⟩, ⟨1,[704,893,1189,1739,1989,2011,2072,1869],14809⟩, ⟨1,[676,859,1140,1668,1973,1968,1986,
  1821],14890⟩, ⟨1,[657,832,1099,1600,1959,1940,1910,1777],15068⟩, ⟨1,[646,810,1062,1536,1943,1920,
  1862,1731],15205⟩, ⟨1,[623,776,1013,1461,1915,1899,1829,1680],15271⟩, ⟨1,[623,761,980,1398,1887,
  1876,1799,1635],15293⟩, ⟨1,[633,753,953,1340,1853,1849,1769,1604],15301⟩, ⟨1,[643,745,924,1281,
  1810,1817,1743,1581],15315⟩, ⟨1,[658,743,901,1226,1762,1784,1720,1554],15346⟩, ⟨1,[673,740,878,
  1172,1707,1752,1697,1516],15399⟩, ⟨1,[688,739,856,1120,1645,1721,1669,1474],15464⟩]
/-- Chunk 7 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c7 : List (SolSparsePulse) := [⟨1,[717,751,847,1081,1587,1697,1636,1433],
  15525⟩, ⟨1,[745,763,839,1042,1524,1675,1599,1396],15568⟩, ⟨1,[777,780,836,1010,1461,1658,1559,
  1364],15586⟩, ⟨1,[822,811,848,993,1409,1648,1522,1335],15586⟩, ⟨1,[840,817,839,962,1345,1632,1490,
  1308],15585⟩, ⟨1,[851,817,827,930,1281,1615,1463,1281],15594⟩, ⟨1,[860,816,813,899,1218,1592,1438,
  1252],15615⟩, ⟨1,[898,844,830,897,1180,1579,1420,1222],15643⟩, ⟨1,[908,846,822,874,1128,1549,1399,
  1192],15662⟩, ⟨1,[914,845,812,852,1078,1514,1377,1165],15663⟩, ⟨1,[951,876,835,862,1059,1495,1363,
  1142],15641⟩, ⟨1,[924,844,800,821,999,1441,1340,1121],15602⟩]
/-- Chunk 8 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c8 : List (SolSparsePulse) := [⟨1,[892,810,765,781,944,1387,1322,1101],
  15557⟩, ⟨1,[870,787,739,752,899,1333,1307,1082],15509⟩, ⟨1,[875,792,743,748,875,1288,1297,1063],
  15477⟩, ⟨1,[862,780,730,731,841,1233,1286,1046],15451⟩, ⟨1,[830,753,704,703,800,1169,1273,1028],
  15435⟩, ⟨1,[779,706,661,659,746,1090,1246,1012],15409⟩, ⟨1,[755,688,646,641,715,1026,1213,996],
  15383⟩, ⟨1,[706,646,609,604,668,947,1159,985],15321⟩, ⟨1,[620,568,537,535,592,841,1068,980],
  15214⟩, ⟨1,[628,585,558,554,596,799,994,970],15195⟩, ⟨1,[618,583,561,558,591,752,908,974],15061⟩,
  ⟨1,[583,557,542,543,572,701,823,993],14734⟩]
/-- Chunk 9 of `solExplicitPulses_r9`. -/
def solExplicitPulses_r9_c9 : List (SolSparsePulse) := [⟨1,[502,484,477,483,513,619,717,981],14840⟩,
  ⟨1,[435,424,424,437,470,557,645,960],15483⟩, ⟨1,[282,278,284,303,341,426,556,1087],12932⟩, ⟨1,[0,
  0,0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 9` (`L = 9`). -/
def solExplicitPulses_r9 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r9_c0) ( solExplicitPulses_r9_c1)) ( List.append ( solExplicitPulses_r9_c2) (
  List.append ( solExplicitPulses_r9_c3) ( solExplicitPulses_r9_c4)))) ( List.append ( List.append (
  solExplicitPulses_r9_c5) ( solExplicitPulses_r9_c6)) ( List.append ( solExplicitPulses_r9_c7) (
  List.append ( solExplicitPulses_r9_c8) ( solExplicitPulses_r9_c9))))
/-- Stratum angle-ratio intervals for `r = 9`. -/
def solRatios_r9 : List (IvInt) := [(942809040,942809043),(881917102,881917105),(816496579,
  816496582),(745355991,745355994),(666666665,666666668),(577350268,577350271),(471404519,
  471404522),(333333332,333333335)]
/-- Chunk 0 of `solTrigIvs_r9`. -/
def solTrigIvs_r9_c0 : List (IvInt × IvInt) := [((982528462,982528463),(186112388,186112389)),
  ((984464701,984464702),(175582607,175582609)),((986402199,986402200),(164349324,164349326)),
  ((988340958,988340959),(152256855,152256857)),((990280977,990280978),(139081219,139081220)),
  ((992222257,992222258),(124478877,124478879))]
/-- Chunk 1 of `solTrigIvs_r9`. -/
def solTrigIvs_r9_c1 : List (IvInt × IvInt) := [((994164799,994164800),(107871918,107871920)),
  ((996108603,996108604),(88134269,88134270)),((998053670,998053671),(62360813,62360814))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 9`. -/
def solTrigIvs_r9 : List (IvInt × IvInt) := List.append ( solTrigIvs_r9_c0) ( solTrigIvs_r9_c1)
/-- Certified suffix probability lower bounds for `r = 9`. -/
def solTailLbs_r9 : List (ℤ) := [999999446,999999444,999999433,999999430,999999418,999999388,
  999997037,999889053,995032408]
/-- Stage specification for explicit `m = 1` conveyor at `r = 9`. -/
def solStage_r9 : PulseM1StageSpec := ⟨9, 18720391, 100000000,
    solToSwLPulses 9 65536 solExplicitPulses_r9⟩
/-- Chunk 0 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c0 : List (SolSparsePulse) := [⟨1,[12882,7974,6219,5328,4823,4534,4379,
  4315,4315],(-52)⟩, ⟨1,[12243,8395,6121,4973,4350,4032,3941,4036,4294],(-19)⟩, ⟨1,[11315,8519,6946,
  5327,4488,4058,3894,3930,4127],(-3)⟩, ⟨1,[10234,8711,6989,5619,4620,4021,3690,3574,3642],0⟩, ⟨1,
  [9143,8851,7106,5932,4667,3894,3366,3020,2844],(-2)⟩, ⟨1,[8127,8892,7158,6248,4860,3866,3145,2572,
  2086],0⟩, ⟨1,[7219,8814,7287,6204,5114,4028,3186,2469,1822],0⟩, ⟨1,[6458,8604,7399,6196,5325,4212,
  3390,2696,2078],0⟩, ⟨1,[5824,8313,7493,6354,5535,4360,3540,2909,2373],0⟩, ⟨1,[5303,7918,7596,6314,
  5582,4512,3589,2918,2376],0⟩, ⟨1,[4874,7477,7625,6413,5507,4657,3649,2885,2283],0⟩, ⟨1,[4512,7038,
  7609,6539,5541,4784,3751,2950,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c1 : List (SolSparsePulse) := [⟨1,[4225,6594,7561,6558,5658,4894,3839,
  3021,2326],0⟩, ⟨1,[4000,6187,7407,6678,5638,4926,3924,3045,2341],0⟩, ⟨1,[3779,5819,7210,6732,5617,
  4872,4028,3081,2351],0⟩, ⟨1,[3585,5462,6989,6762,5780,4872,4115,3126,2339],0⟩, ⟨1,[3440,5167,6722,
  6788,5813,4950,4178,3176,2335],0⟩, ⟨1,[3317,4917,6438,6794,5823,5005,4222,3219,2347],0⟩, ⟨1,[3192,
  4668,6158,6735,5945,4954,4219,3264,2364],0⟩, ⟨1,[3070,4451,5874,6639,5995,4951,4184,3322,2370],0⟩,
  ⟨1,[2971,4295,5603,6510,6023,5084,4193,3374,2362],0⟩, ⟨1,[2889,4143,5369,6355,6055,5137,4254,3410,
  2366],0⟩, ⟨1,[2813,3986,5134,6184,6095,5097,4296,3428,2381],0⟩, ⟨1,[2735,3857,4921,5986,6099,5193,
  4279,3432,2388],0⟩]
/-- Chunk 2 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c2 : List (SolSparsePulse) := [⟨1,[2656,3743,4737,5787,6053,5271,4226,
  3419,2393],0⟩, ⟨1,[2576,3631,4552,5584,6006,5287,4288,3409,2401],0⟩, ⟨1,[2499,3519,4387,5373,5939,
  5331,4402,3432,2414],0⟩, ⟨1,[2427,3416,4264,5175,5838,5377,4420,3480,2424],0⟩, ⟨1,[2363,3335,4150,
  5000,5714,5415,4396,3510,2426],0⟩, ⟨1,[2306,3269,4006,4824,5582,5426,4472,3501,2421],0⟩, ⟨1,[2253,
  3208,3873,4641,5444,5413,4544,3459,2417],0⟩, ⟨1,[2203,3140,3790,4493,5281,5405,4551,3470,2417],0⟩,
  ⟨1,[2155,3062,3720,4369,5122,5372,4588,3563,2425],0⟩, ⟨1,[2109,2976,3633,4231,4973,5320,4631,3614,
  2446],0⟩, ⟨1,[2059,2888,3532,4098,4809,5263,4667,3602,2475],0⟩, ⟨1,[2013,2806,3433,4002,4647,5175,
  4716,3606,2494],0⟩]
/-- Chunk 3 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c3 : List (SolSparsePulse) := [⟨1,[1959,2734,3351,3918,4516,5065,4741,
  3674,2495],0⟩, ⟨1,[1907,2673,3293,3809,4390,4963,4737,3724,2481],0⟩, ⟨1,[1851,2623,3248,3696,4250,
  4854,4743,3726,2479],0⟩, ⟨1,[1791,2577,3200,3618,4127,4727,4741,3772,2518],0⟩, ⟨1,[1731,2533,3135,
  3563,4025,4598,4715,3823,2563],0⟩, ⟨1,[1679,2488,3052,3494,3915,4476,4682,3850,2572],0⟩, ⟨1,[1634,
  2442,2957,3401,3802,4349,4643,3883,2575],0⟩, ⟨1,[1591,2392,2862,3299,3711,4218,4586,3925,2598],0⟩,
  ⟨1,[1544,2332,2774,3210,3640,4101,4510,3961,2642],0⟩, ⟨1,[1497,2268,2700,3147,3560,4000,4423,3982,
  2684],0⟩, ⟨1,[1461,2206,2643,3107,3463,3896,4336,3998,2698],0⟩, ⟨1,[1452,2152,2603,3073,3373,3784,
  4250,4007,2722],0⟩]
/-- Chunk 4 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c4 : List (SolSparsePulse) := [⟨1,[1469,2112,2577,3025,3311,3678,4159,
  4012,2759],0⟩, ⟨1,[1481,2070,2554,2952,3260,3586,4056,4017,2787],0⟩, ⟨1,[1409,2013,2539,2858,3191,
  3499,3946,4009,2824],0⟩, ⟨1,[1274,1954,2540,2764,3097,3412,3845,3980,2870],0⟩, ⟨1,[1191,1864,2501,
  2666,3002,3332,3753,3944,2910],0⟩, ⟨1,[1142,1774,2453,2587,2928,3259,3654,3908,2945],0⟩, ⟨1,[1110,
  1685,2402,2532,2874,3184,3549,3865,2985],0⟩, ⟨1,[1082,1601,2359,2515,2824,3104,3452,3809,3026],0⟩,
  ⟨1,[1050,1524,2309,2523,2767,3029,3365,3744,3065],0⟩, ⟨1,[1025,1461,2234,2531,2700,2951,3281,3672,
  3102],0⟩, ⟨1,[1004,1407,2139,2536,2627,2857,3184,3599,3134],0⟩, ⟨1,[985,1359,2039,2541,2556,2765,
  3093,3523,3164],0⟩]
/-- Chunk 5 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c5 : List (SolSparsePulse) := [⟨1,[966,1313,1938,2548,2509,2689,3024,3443,
  3192],0⟩, ⟨1,[952,1272,1846,2539,2492,2632,2942,3364,3214],0⟩, ⟨1,[941,1235,1762,2489,2482,2569,
  2836,3282,3234],0⟩, ⟨1,[930,1200,1684,2411,2482,2463,2740,3191,3255],0⟩, ⟨1,[919,1167,1613,2318,
  2500,2340,2678,3101,3267],0⟩, ⟨1,[905,1134,1545,2223,2524,2270,2569,3015,3276],0⟩, ⟨1,[885,1099,
  1479,2131,2510,2278,2382,2924,3285],0⟩, ⟨1,[864,1065,1418,2045,2455,2363,2296,2814,3285],0⟩, ⟨1,
  [840,1031,1359,1961,2386,2519,2292,2684,3288],0⟩, ⟨1,[813,997,1303,1878,2324,2662,2111,2574,3290],
  6⟩, ⟨1,[788,966,1253,1798,2280,2611,1907,2423,3262],(-9)⟩, ⟨1,[756,930,1201,1717,2242,2443,2011,
  2192,3283],(-50)⟩]
/-- Chunk 6 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c6 : List (SolSparsePulse) := [⟨1,[726,896,1154,1639,2202,2293,2508,1950,
  3272],22⟩, ⟨1,[704,869,1114,1568,2157,2197,2598,1447,3279],(-252)⟩, ⟨1,[676,836,1069,1495,2101,
  2138,2347,2106,2218],13454⟩, ⟨1,[657,810,1031,1428,2041,2101,2187,2075,1988],14888⟩, ⟨1,[646,790,
  998,1367,1976,2079,2120,2034,1914],15189⟩, ⟨1,[623,757,953,1298,1897,2061,2089,2038,1858],15257⟩,
  ⟨1,[623,744,925,1243,1824,2052,2067,2023,1820],15268⟩, ⟨1,[633,738,903,1194,1750,2044,2047,1982,
  1787],15313⟩, ⟨1,[643,733,880,1146,1673,2031,2023,1932,1749],15377⟩, ⟨1,[658,732,861,1102,1598,
  2013,1996,1887,1705],15435⟩, ⟨1,[673,732,843,1060,1523,1986,1963,1849,1662],15484⟩, ⟨1,[688,732,
  827,1020,1448,1948,1925,1817,1623],15528⟩]
/-- Chunk 7 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c7 : List (SolSparsePulse) := [⟨1,[717,747,824,992,1383,1906,1886,1788,
  1585],15574⟩, ⟨1,[745,761,820,966,1319,1854,1844,1757,1547],15622⟩, ⟨1,[777,779,823,945,1261,1797,
  1803,1723,1511],15668⟩, ⟨1,[822,812,839,939,1218,1743,1770,1687,1477],15706⟩, ⟨1,[840,820,834,916,
  1163,1675,1739,1652,1444],15729⟩, ⟨1,[851,821,825,892,1110,1605,1714,1621,1412],15738⟩, ⟨1,[860,
  821,815,867,1060,1533,1692,1595,1382],15741⟩, ⟨1,[898,851,834,872,1038,1480,1684,1573,1352],
  15746⟩, ⟨1,[908,854,828,855,999,1413,1669,1554,1320],15760⟩, ⟨1,[914,853,821,838,963,1348,1652,
  1534,1288],15778⟩, ⟨1,[951,885,845,852,959,1310,1649,1515,1258],15789⟩, ⟨1,[924,854,811,814,909,
  1237,1618,1490,1230],15785⟩]
/-- Chunk 8 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c8 : List (SolSparsePulse) := [⟨1,[892,821,776,775,863,1168,1583,1464,
  1206],15764⟩, ⟨1,[870,797,751,748,827,1108,1546,1436,1185],15732⟩, ⟨1,[875,803,755,747,814,1067,
  1511,1409,1163],15701⟩, ⟨1,[862,790,743,732,790,1017,1463,1385,1142],15675⟩, ⟨1,[830,762,716,704,
  756,961,1404,1367,1121],15655⟩, ⟨1,[779,715,672,661,707,892,1328,1345,1103],15627⟩, ⟨1,[755,696,
  657,644,683,844,1257,1324,1087],15586⟩, ⟨1,[706,653,619,607,640,781,1168,1285,1075],15520⟩, ⟨1,
  [620,575,545,537,567,690,1049,1208,1072],15405⟩, ⟨1,[628,591,565,556,578,674,979,1125,1070],
  15306⟩, ⟨1,[618,587,567,560,576,651,902,1016,1072],15187⟩, ⟨1,[583,560,546,543,559,620,821,896,
  1085],14941⟩]
/-- Chunk 9 of `solExplicitPulses_r10`. -/
def solExplicitPulses_r10_c9 : List (SolSparsePulse) := [⟨1,[501,486,479,481,499,551,710,755,1087],
  14843⟩, ⟨1,[435,426,425,432,453,501,623,656,1055],15336⟩, ⟨1,[282,279,283,296,322,372,480,581,
  1170],13760⟩, ⟨1,[0,0,0,0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 10` (`L = 10`). -/
def solExplicitPulses_r10 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r10_c0) ( solExplicitPulses_r10_c1)) ( List.append ( solExplicitPulses_r10_c2) (
  List.append ( solExplicitPulses_r10_c3) ( solExplicitPulses_r10_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r10_c5) ( solExplicitPulses_r10_c6)) ( List.append ( solExplicitPulses_r10_c7)
  ( List.append ( solExplicitPulses_r10_c8) ( solExplicitPulses_r10_c9))))
/-- Stratum angle-ratio intervals for `r = 10`. -/
def solRatios_r10 : List (IvInt) := [(948683297,948683300),(894427189,894427192),(836660025,
  836660028),(774596668,774596671),(707106780,707106783),(632455531,632455534),(547722556,
  547722559),(447213594,447213597),(316227765,316227768)]
/-- Chunk 0 of `solTrigIvs_r10`. -/
def solTrigIvs_r10_c0 : List (IvInt × IvInt) := [((979481683,979481684),(201533202,201533203)),
  ((981527173,981527174),(191322785,191322787)),((983574070,983574071),(180504979,180504980)),
  ((985622376,985622377),(168963105,168963106)),((987672091,987672092),(156537024,156537026)),
  ((989723215,989723216),(142996351,142996353))]
/-- Chunk 1 of `solTrigIvs_r10`. -/
def solTrigIvs_r10_c1 : List (IvInt × IvInt) := [((991775749,991775750),(127987741,127987742)),
  ((993829694,993829695),(110916804,110916805)),((995885051,995885052),(90625408,90625410)),
  ((997941819,997941820),(64125853,64125854))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 10`. -/
def solTrigIvs_r10 : List (IvInt × IvInt) := List.append ( solTrigIvs_r10_c0) ( solTrigIvs_r10_c1)
/-- Certified suffix probability lower bounds for `r = 10`. -/
def solTailLbs_r10 : List (ℤ) := [999999345,999999345,999999344,999999343,999999338,999999324,
  999999297,999995612,999838472,993635369]
/-- Stage specification for explicit `m = 1` conveyor at `r = 10`. -/
def solStage_r10 : PulseM1StageSpec := ⟨10, 20292299, 100000000,
    solToSwLPulses 10 65536 solExplicitPulses_r10⟩
/-- Chunk 0 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c0 : List (SolSparsePulse) := [⟨1,[13979,8520,6609,5625,5047,4694,4482,
  4365,4315,4315],(-52)⟩, ⟨1,[13167,9168,6627,5356,4627,4209,4002,3962,4064,4294],(-19)⟩, ⟨1,[12013,
  9383,7629,5867,4861,4297,4003,3902,3952,4127],(-3)⟩, ⟨1,[10721,9587,7763,6156,5064,4354,3910,3664,
  3581,3642],0⟩, ⟨1,[9454,9705,7852,6614,5235,4323,3718,3289,3001,2844],(-2)⟩, ⟨1,[8314,9689,7954,
  6949,5517,4419,3626,3018,2518,2086],0⟩, ⟨1,[7342,9509,8104,6943,5741,4634,3747,3027,2398,1822],0⟩,
  ⟨1,[6541,9183,8224,6980,6010,4843,3938,3236,2627,2078],0⟩, ⟨1,[5892,8743,8333,7053,6275,5054,4087,
  3400,2849,2373],0⟩, ⟨1,[5370,8236,8386,7123,6285,5215,4207,3440,2857,2376],0⟩, ⟨1,[4945,7709,8371,
  7236,6268,5348,4330,3479,2818,2283],0⟩, ⟨1,[4602,7189,8282,7316,6318,5529,4463,3573,2878,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c1 : List (SolSparsePulse) := [⟨1,[4324,6707,8106,7415,6364,5669,4598,
  3659,2944,2326],0⟩, ⟨1,[4082,6268,7869,7483,6406,5656,4707,3732,2967,2341],0⟩, ⟨1,[3877,5877,7578,
  7524,6500,5632,4791,3827,3000,2351],0⟩, ⟨1,[3709,5547,7249,7526,6554,5673,4900,3916,3039,2339],0⟩,
  ⟨1,[3558,5253,6914,7481,6629,5714,5005,3997,3084,2335],0⟩, ⟨1,[3418,4990,6582,7387,6706,5734,5034,
  4077,3124,2347],0⟩, ⟨1,[3298,4773,6258,7248,6762,5791,4997,4140,3169,2364],0⟩, ⟨1,[3191,4584,5956,
  7065,6804,5858,5003,4192,3225,2370],0⟩, ⟨1,[3089,4409,5680,6852,6826,5892,5042,4259,3280,2362],0⟩,
  ⟨1,[2993,4254,5433,6617,6817,5959,5067,4325,3326,2366],0⟩, ⟨1,[2902,4116,5213,6375,6772,6023,5083,
  4340,3367,2381],0⟩, ⟨1,[2819,3987,5006,6130,6700,6073,5129,4318,3406,2390],0⟩]
/-- Chunk 2 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c2 : List (SolSparsePulse) := [⟨1,[2740,3865,4825,5889,6593,6121,5189,
  4312,3438,2395],0⟩, ⟨1,[2666,3760,4670,5661,6457,6154,5218,4345,3466,2405],0⟩, ⟨1,[2596,3667,4521,
  5444,6300,6172,5262,4370,3505,2421],0⟩, ⟨1,[2529,3575,4378,5239,6126,6170,5322,4380,3538,2437],0⟩,
  ⟨1,[2465,3480,4257,5060,5937,6148,5365,4401,3540,2447],0⟩, ⟨1,[2402,3389,4151,4898,5746,6099,5412,
  4448,3529,2454],0⟩, ⟨1,[2339,3305,4047,4738,5559,6024,5455,4488,3529,2464],0⟩, ⟨1,[2278,3227,3941,
  4591,5372,5931,5491,4510,3554,2474],0⟩, ⟨1,[2218,3152,3845,4467,5194,5816,5519,4551,3577,2485],0⟩,
  ⟨1,[2160,3080,3763,4352,5027,5688,5529,4601,3585,2498],0⟩, ⟨1,[2100,3009,3688,4238,4864,5547,5528,
  4639,3599,2509],0⟩, ⟨1,[2045,2941,3609,4133,4718,5394,5510,4684,3631,2511],0⟩]
/-- Chunk 3 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c3 : List (SolSparsePulse) := [⟨1,[1983,2872,3521,4041,4589,5240,5469,
  4730,3667,2510],0⟩, ⟨1,[1925,2804,3433,3952,4460,5092,5412,4762,3686,2518],0⟩, ⟨1,[1864,2736,3352,
  3859,4333,4942,5343,4796,3709,2535],0⟩, ⟨1,[1800,2667,3278,3767,4224,4794,5257,4827,3751,2552],0⟩,
  ⟨1,[1738,2596,3208,3685,4129,4656,5158,4848,3790,2560],0⟩, ⟨1,[1683,2525,3140,3615,4034,4522,5049,
  4859,3822,2571],0⟩, ⟨1,[1637,2455,3075,3552,3936,4392,4931,4856,3862,2592],0⟩, ⟨1,[1593,2383,3010,
  3482,3848,4274,4807,4840,3902,2616],0⟩, ⟨1,[1545,2306,2943,3400,3770,4170,4679,4814,3939,2636],0⟩,
  ⟨1,[1498,2227,2876,3312,3695,4066,4555,4773,3979,2653],0⟩, ⟨1,[1462,2155,2810,3226,3613,3962,4434,
  4718,4017,2676],0⟩, ⟨1,[1452,2096,2749,3150,3528,3867,4312,4655,4047,2705],0⟩]
/-- Chunk 4 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c4 : List (SolSparsePulse) := [⟨1,[1470,2054,2694,3084,3450,3784,4194,
  4579,4075,2732],0⟩, ⟨1,[1481,2013,2637,3023,3384,3701,4084,4492,4100,2761],0⟩, ⟨1,[1409,1951,2580,
  2969,3322,3616,3977,4400,4116,2796],0⟩, ⟨1,[1274,1881,2538,2931,3256,3534,3871,4304,4123,2832],0⟩,
  ⟨1,[1191,1790,2460,2880,3177,3459,3775,4202,4123,2868],0⟩, ⟨1,[1142,1704,2377,2831,3089,3385,3687,
  4097,4112,2908],0⟩, ⟨1,[1110,1621,2298,2785,3003,3307,3598,3994,4090,2952],0⟩, ⟨1,[1082,1543,2229,
  2754,2929,3223,3506,3894,4059,2992],0⟩, ⟨1,[1050,1471,2159,2725,2873,3143,3418,3793,4020,3030],0⟩,
  ⟨1,[1025,1412,2078,2679,2829,3068,3336,3691,3974,3071],0⟩, ⟨1,[1004,1362,1985,2619,2799,2993,3259,
  3591,3918,3113],0⟩, ⟨1,[985,1318,1892,2555,2782,2913,3180,3496,3854,3155],0⟩]
/-- Chunk 5 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c5 : List (SolSparsePulse) := [⟨1,[966,1275,1801,2491,2782,2837,3096,3405,
  3782,3195],0⟩, ⟨1,[952,1237,1718,2422,2787,2777,3006,3313,3707,3230],0⟩, ⟨1,[941,1203,1644,2333,
  2773,2734,2913,3220,3628,3263],0⟩, ⟨1,[930,1170,1575,2231,2742,2700,2825,3134,3544,3293],0⟩, ⟨1,
  [919,1139,1513,2127,2704,2683,2743,3044,3457,3319],0⟩, ⟨1,[905,1109,1453,2026,2659,2692,2658,2943,
  3369,3341],0⟩, ⟨1,[885,1075,1394,1932,2587,2703,2558,2839,3279,3360],0⟩, ⟨1,[864,1043,1339,1846,
  2490,2705,2475,2735,3182,3377],0⟩, ⟨1,[840,1010,1285,1765,2384,2712,2469,2617,3086,3385],0⟩, ⟨1,
  [813,976,1234,1688,2282,2716,2531,2481,2988,3390],0⟩, ⟨1,[788,946,1189,1616,2194,2657,2597,2365,
  2869,3394],0⟩, ⟨1,[756,911,1141,1544,2112,2558,2669,2253,2737,3394],0⟩]
/-- Chunk 6 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c6 : List (SolSparsePulse) := [⟨1,[726,877,1096,1475,2032,2468,2746,2139,
  2581,3393],0⟩, ⟨1,[704,851,1059,1415,1956,2403,2674,2155,2383,3391],0⟩, ⟨1,[676,819,1017,1351,
  1876,2347,2500,2434,2087,3393],(-6)⟩, ⟨1,[657,793,982,1294,1800,2293,2382,2673,1702,3396],83⟩, ⟨1,
  [646,774,952,1243,1727,2237,2321,2516,1925,2626],11434⟩, ⟨1,[623,742,910,1182,1644,2171,2282,2361,
  2209,2048],15219⟩, ⟨1,[623,730,885,1136,1573,2108,2255,2278,2190,1990],15348⟩, ⟨1,[633,726,866,
  1096,1506,2043,2233,2228,2134,1946],15422⟩, ⟨1,[643,723,847,1057,1439,1972,2212,2191,2091,1899],
  15497⟩, ⟨1,[658,724,833,1022,1376,1901,2190,2158,2056,1856],15555⟩, ⟨1,[673,725,819,988,1315,1827,
  2164,2127,2023,1813],15609⟩, ⟨1,[688,727,806,955,1255,1750,2130,2095,1987,1771],15661⟩]
/-- Chunk 7 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c7 : List (SolSparsePulse) := [⟨1,[717,744,807,936,1207,1680,2092,2063,
  1949,1728],15714⟩, ⟨1,[745,759,807,917,1160,1607,2045,2030,1910,1687],15763⟩, ⟨1,[777,779,813,905,
  1119,1537,1990,1995,1873,1648],15808⟩, ⟨1,[822,813,833,906,1093,1479,1938,1961,1837,1608],15849⟩,
  ⟨1,[840,822,831,889,1053,1410,1872,1925,1802,1570],15886⟩, ⟨1,[851,825,824,870,1013,1342,1805,
  1890,1769,1532],15917⟩, ⟨1,[860,826,816,850,975,1277,1735,1855,1738,1496],15940⟩, ⟨1,[898,856,838,
  860,965,1237,1681,1831,1709,1462],15955⟩, ⟨1,[908,860,834,846,936,1184,1615,1803,1682,1429],
  15965⟩, ⟨1,[914,860,828,832,908,1133,1551,1776,1656,1397],15972⟩, ⟨1,[951,892,854,850,912,1113,
  1510,1763,1632,1365],15978⟩, ⟨1,[924,862,821,813,867,1053,1438,1730,1608,1334],15983⟩]
/-- Chunk 8 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c8 : List (SolSparsePulse) := [⟨1,[892,829,786,775,824,997,1369,1698,1585,
  1305],15981⟩, ⟨1,[870,805,761,749,792,952,1306,1663,1559,1278],15970⟩, ⟨1,[875,811,766,749,784,
  927,1258,1630,1534,1254],15949⟩, ⟨1,[862,798,753,735,764,893,1202,1587,1508,1232],15919⟩, ⟨1,[830,
  770,726,708,733,850,1138,1536,1484,1211],15882⟩, ⟨1,[779,722,682,665,687,793,1060,1468,1458,1192],
  15837⟩, ⟨1,[755,703,665,649,666,758,1000,1403,1434,1176],15785⟩, ⟨1,[706,659,626,611,626,707,924,
  1318,1395,1163],15722⟩, ⟨1,[620,580,552,540,554,626,820,1199,1323,1156],15633⟩, ⟨1,[628,595,571,
  560,569,624,782,1115,1237,1151],15544⟩, ⟨1,[618,591,572,563,570,613,738,1017,1115,1150],15452⟩,
  ⟨1,[583,563,549,545,552,588,688,913,972,1159],15267⟩]
/-- Chunk 9 of `solExplicitPulses_r11`. -/
def solExplicitPulses_r11_c9 : List (SolSparsePulse) := [⟨1,[502,488,480,481,491,524,604,778,807,
  1170],15100⟩, ⟨1,[435,427,425,430,444,475,541,670,681,1150],15415⟩, ⟨1,[282,279,282,291,310,344,
  407,523,612,1229],14262⟩, ⟨1,[0,0,0,0,0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 11` (`L = 11`). -/
def solExplicitPulses_r11 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r11_c0) ( solExplicitPulses_r11_c1)) ( List.append ( solExplicitPulses_r11_c2) (
  List.append ( solExplicitPulses_r11_c3) ( solExplicitPulses_r11_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r11_c5) ( solExplicitPulses_r11_c6)) ( List.append ( solExplicitPulses_r11_c7)
  ( List.append ( solExplicitPulses_r11_c8) ( solExplicitPulses_r11_c9))))
/-- Stratum angle-ratio intervals for `r = 11`. -/
def solRatios_r11 : List (IvInt) := [(953462588,953462591),(904534032,904534035),(852802864,
  852802867),(797724034,797724037),(738548944,738548947),(674199861,674199864),(603022688,
  603022691),(522232966,522232969),(426401431,426401434),(301511343,301511346)]
/-- Chunk 0 of `solTrigIvs_r11`. -/
def solTrigIvs_r11_c0 : List (IvInt × IvInt) := [((975945128,975945129),(218016296,218016297)),
  ((978123925,978123926),(208023043,208023045)),((980304321,980304322),(197492877,197492879)),
  ((982486318,982486319),(186334735,186334736)),((984669916,984669917),(174428078,174428080)),
  ((986855117,986855118),(161607480,161607481))]
/-- Chunk 1 of `solTrigIvs_r11`. -/
def solTrigIvs_r11_c1 : List (IvInt × IvInt) := [((989041920,989041921),(147634955,147634957)),
  ((991230326,991230327),(132145525,132145527)),((993420336,993420337),(114525255,114525257)),
  ((995611952,995611953),(93577992,93577993)),((997805172,997805173),(66218099,66218101))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 11`. -/
def solTrigIvs_r11 : List (IvInt × IvInt) := List.append ( solTrigIvs_r11_c0) ( solTrigIvs_r11_c1)
/-- Certified suffix probability lower bounds for `r = 11`. -/
def solTailLbs_r11 : List (ℤ) := [999999262,999999260,999999259,999999259,999999258,999999250,
  999999239,999999172,999994104,999797123,992601491]
/-- Stage specification for explicit `m = 1` conveyor at `r = 11`. -/
def solStage_r11 : PulseM1StageSpec := ⟨11, 21978141, 100000000,
    solToSwLPulses 11 65536 solExplicitPulses_r11⟩
/-- Chunk 0 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c0 : List (SolSparsePulse) := [⟨1,[15001,9066,6991,5920,5278,4871,4609,
  4447,4355,4315,4315],(-52)⟩, ⟨1,[14009,9877,7135,5737,4918,4418,4126,3990,3983,4087,4294],(-19)⟩,
  ⟨1,[12630,10204,8366,6395,5263,4579,4179,3973,3912,3970,4127],(-3)⟩, ⟨1,[11116,10415,8403,6799,
  5501,4709,4176,3836,3647,3587,3642],0⟩, ⟨1,[9703,10491,8547,7429,5801,4779,4081,3589,3231,2985,
  2844],(-2)⟩, ⟨1,[8451,10397,8757,7601,6184,4969,4102,3443,2918,2475,2086],0⟩, ⟨1,[7432,10093,8850,
  7552,6508,5195,4279,3531,2901,2340,1822],0⟩, ⟨1,[6620,9644,9019,7679,6850,5462,4481,3728,3114,
  2572,2078],0⟩, ⟨1,[5947,9086,9092,7767,6946,5774,4670,3881,3290,2801,2373],0⟩, ⟨1,[5434,8457,9097,
  7902,6874,5997,4822,3977,3324,2809,2376],0⟩, ⟨1,[5028,7847,9010,7971,6949,6202,4972,4075,3347,
  2765,2283],0⟩, ⟨1,[4708,7304,8797,8115,7026,6329,5181,4198,3434,2819,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c1 : List (SolSparsePulse) := [⟨1,[4411,6789,8541,8163,7105,6296,5402,
  4323,3516,2882,2326],0⟩, ⟨1,[4164,6325,8198,8222,7193,6270,5550,4432,3579,2904,2341],0⟩, ⟨1,[3983,
  5975,7804,8219,7226,6347,5661,4543,3662,2935,2351],0⟩, ⟨1,[3816,5627,7421,8139,7363,6409,5718,
  4689,3743,2969,2339],0⟩, ⟨1,[3659,5309,7024,8022,7415,6469,5686,4849,3821,3009,2335],0⟩, ⟨1,[3528,
  5100,6662,7824,7474,6553,5660,4972,3902,3047,2347],0⟩, ⟨1,[3413,4906,6341,7585,7514,6546,5705,
  5038,3978,3089,2364],0⟩, ⟨1,[3301,4697,6026,7331,7512,6637,5758,5076,4058,3141,2370],0⟩, ⟨1,[3192,
  4525,5759,7048,7471,6721,5791,5073,4162,3191,2362],0⟩, ⟨1,[3087,4379,5517,6746,7399,6760,5866,
  5047,4272,3238,2366],0⟩, ⟨1,[2988,4238,5307,6468,7253,6838,5914,5059,4344,3283,2381],0⟩, ⟨1,[2899,
  4111,5133,6230,7083,6869,5927,5108,4374,3331,2390],0⟩]
/-- Chunk 2 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c2 : List (SolSparsePulse) := [⟨1,[2821,4001,4946,5969,6918,6863,6030,
  5148,4381,3378,2396],0⟩, ⟨1,[2750,3898,4761,5706,6717,6854,6076,5174,4377,3429,2406],0⟩, ⟨1,[2683,
  3795,4629,5517,6478,6828,6095,5231,4365,3493,2423],0⟩, ⟨1,[2617,3690,4525,5343,6253,6748,6170,
  5262,4374,3553,2441],0⟩, ⟨1,[2549,3583,4409,5140,6033,6638,6225,5257,4411,3579,2453],0⟩, ⟨1,[2480,
  3481,4289,4976,5821,6505,6250,5339,4451,3581,2464],0⟩, ⟨1,[2409,3392,4185,4857,5628,6358,6247,
  5408,4476,3574,2479],0⟩, ⟨1,[2338,3317,4097,4730,5430,6196,6243,5414,4514,3571,2495],0⟩, ⟨1,[2267,
  3251,4012,4600,5258,6011,6214,5473,4558,3570,2512],0⟩, ⟨1,[2199,3189,3923,4490,5117,5837,6152,
  5530,4546,3581,2530],0⟩, ⟨1,[2130,3124,3827,4388,4956,5657,6091,5561,4546,3609,2543],0⟩, ⟨1,[2067,
  3054,3725,4280,4795,5463,5996,5600,4629,3636,2542],0⟩]
/-- Chunk 3 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c3 : List (SolSparsePulse) := [⟨1,[1999,2976,3620,4174,4688,5303,5862,
  5621,4683,3654,2537],0⟩, ⟨1,[1936,2893,3524,4082,4602,5166,5726,5624,4698,3686,2537],0⟩, ⟨1,[1872,
  2805,3444,4004,4482,5006,5599,5608,4760,3730,2543],0⟩, ⟨1,[1805,2713,3380,3933,4351,4847,5460,
  5578,4814,3737,2552],0⟩, ⟨1,[1741,2618,3324,3858,4252,4728,5305,5540,4839,3727,2566],0⟩, ⟨1,[1685,
  2525,3270,3774,4174,4616,5155,5478,4876,3775,2586],0⟩, ⟨1,[1638,2437,3211,3681,4090,4484,5003,
  5402,4908,3840,2601],0⟩, ⟨1,[1593,2351,3144,3582,3997,4371,4857,5304,4939,3860,2612],0⟩, ⟨1,[1546,
  2262,3065,3483,3908,4290,4742,5183,4959,3889,2635],0⟩, ⟨1,[1498,2176,2976,3394,3834,4196,4627,
  5077,4942,3948,2666],0⟩, ⟨1,[1462,2099,2884,3322,3770,4081,4478,4979,4925,3977,2682],0⟩, ⟨1,[1452,
  2039,2793,3269,3706,3982,4344,4848,4922,4004,2685],0⟩]
/-- Chunk 4 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c4 : List (SolSparsePulse) := [⟨1,[1470,2000,2709,3229,3632,3915,4255,
  4711,4884,4064,2708],0⟩, ⟨1,[1481,1961,2624,3190,3543,3852,4167,4599,4821,4103,2748],0⟩, ⟨1,[1409,
  1897,2540,3149,3443,3771,4060,4476,4768,4116,2769],0⟩, ⟨1,[1274,1820,2468,3112,3346,3681,3963,
  4337,4703,4148,2777],0⟩, ⟨1,[1191,1730,2368,3044,3252,3599,3887,4228,4610,4189,2811],0⟩, ⟨1,[1142,
  1647,2270,2966,3175,3531,3806,4140,4512,4208,2864],0⟩, ⟨1,[1110,1570,2179,2882,3122,3470,3712,
  4030,4421,4212,2900],0⟩, ⟨1,[1082,1497,2100,2806,3094,3404,3623,3913,4322,4211,2932],0⟩, ⟨1,[1050,
  1428,2025,2728,3084,3325,3549,3822,4213,4201,2977],0⟩, ⟨1,[1025,1373,1945,2636,3072,3233,3475,
  3743,4103,4181,3021],0⟩, ⟨1,[1004,1326,1860,2534,3052,3136,3389,3654,4000,4153,3060],0⟩, ⟨1,[985,
  1284,1776,2433,3024,3047,3300,3560,3903,4110,3104],0⟩]
/-- Chunk 5 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c5 : List (SolSparsePulse) := [⟨1,[966,1244,1694,2338,2991,2984,3216,3468,
  3803,4059,3148],0⟩, ⟨1,[952,1208,1620,2246,2946,2956,3138,3378,3693,4003,3188],0⟩, ⟨1,[941,1177,
  1554,2148,2871,2949,3062,3294,3594,3938,3232],0⟩, ⟨1,[930,1146,1494,2046,2776,2952,2986,3214,3513,
  3865,3276],0⟩, ⟨1,[919,1118,1437,1948,2672,2963,2914,3120,3419,3787,3313],0⟩, ⟨1,[905,1088,1383,
  1855,2566,2978,2864,3012,3305,3706,3346],0⟩, ⟨1,[885,1056,1330,1770,2450,2971,2833,2919,3211,3622,
  3380],0⟩, ⟨1,[864,1025,1279,1692,2327,2934,2824,2847,3129,3530,3409],0⟩, ⟨1,[840,993,1230,1619,
  2205,2880,2849,2765,3017,3438,3426],0⟩, ⟨1,[813,960,1183,1549,2092,2815,2889,2665,2897,3345,3449],
  0⟩, ⟨1,[788,931,1140,1486,1995,2718,2886,2578,2800,3239,3472],0⟩, ⟨1,[756,896,1095,1421,1904,2598,
  2851,2551,2672,3140,3469],0⟩]
/-- Chunk 6 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c6 : List (SolSparsePulse) := [⟨1,[726,862,1053,1361,1821,2481,2815,2634,
  2503,3037,3479],0⟩, ⟨1,[704,836,1018,1307,1745,2377,2746,2775,2405,2903,3486],0⟩, ⟨1,[676,804,978,
  1250,1668,2277,2654,2900,2311,2735,3485],0⟩, ⟨1,[657,780,945,1200,1597,2181,2591,2909,2165,2558,
  3490],6⟩, ⟨1,[646,761,917,1156,1531,2088,2553,2738,2281,2305,3487],(-2)⟩, ⟨1,[623,730,876,1100,
  1456,1989,2512,2553,2804,1910,3496],9⟩, ⟨1,[623,719,854,1061,1396,1900,2467,2449,2797,1732,3140],
  7731⟩, ⟨1,[633,717,838,1027,1340,1816,2414,2395,2505,2348,2111],15385⟩, ⟨1,[643,715,822,994,1284,
  1734,2349,2358,2378,2254,2073],15490⟩, ⟨1,[658,717,811,965,1233,1656,2277,2331,2330,2216,2012],
  15601⟩, ⟨1,[673,720,800,937,1183,1581,2196,2310,2297,2196,1968],15638⟩, ⟨1,[688,723,790,911,1135,
  1507,2108,2290,2265,2158,1930],15690⟩]
/-- Chunk 7 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c7 : List (SolSparsePulse) := [⟨1,[717,741,794,898,1099,1444,2021,2273,
  2233,2111,1881],15768⟩, ⟨1,[745,758,798,884,1063,1382,1930,2251,2200,2065,1828],15845⟩, ⟨1,[777,
  779,806,877,1034,1326,1839,2222,2166,2023,1782],15903⟩, ⟨1,[822,814,829,884,1019,1283,1759,2191,
  2132,1984,1743],15944⟩, ⟨1,[840,824,829,872,988,1229,1670,2144,2095,1949,1706],15975⟩, ⟨1,[851,
  827,824,856,956,1176,1583,2089,2055,1916,1665],16006⟩, ⟨1,[860,829,818,840,925,1124,1500,2025,
  2013,1883,1624],16042⟩, ⟨1,[898,861,842,853,923,1100,1442,1970,1976,1850,1585],16078⟩, ⟨1,[908,
  864,839,843,900,1059,1373,1901,1937,1818,1547],16106⟩, ⟨1,[914,865,834,831,877,1020,1309,1830,
  1900,1788,1510],16121⟩, ⟨1,[951,898,862,851,887,1012,1276,1777,1877,1760,1476],16125⟩, ⟨1,[924,
  868,829,815,845,960,1207,1697,1845,1734,1445],16124⟩]
/-- Chunk 8 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c8 : List (SolSparsePulse) := [⟨1,[892,835,794,779,805,911,1145,1618,1816,
  1710,1414],16124⟩, ⟨1,[870,812,770,753,775,872,1092,1545,1789,1683,1382],16123⟩, ⟨1,[875,817,775,
  754,770,856,1059,1483,1766,1655,1351],16116⟩, ⟨1,[862,805,762,741,753,829,1016,1414,1735,1624,
  1325],16097⟩, ⟨1,[830,776,735,714,724,792,967,1338,1697,1593,1303],16061⟩, ⟨1,[779,728,690,670,
  678,740,903,1250,1644,1560,1283],16013⟩, ⟨1,[755,708,673,654,660,713,859,1176,1591,1532,1266],
  15955⟩, ⟨1,[706,664,633,616,621,667,798,1086,1516,1500,1253],15891⟩, ⟨1,[620,584,557,543,549,591,
  708,967,1404,1444,1244],15812⟩, ⟨1,[628,598,576,563,565,597,692,907,1311,1366,1239],15713⟩, ⟨1,
  [618,594,576,565,567,591,667,839,1196,1241,1239],15604⟩, ⟨1,[583,565,552,546,549,570,631,766,1065,
  1073,1247],15454⟩]
/-- Chunk 9 of `solExplicitPulses_r12`. -/
def solExplicitPulses_r12_c9 : List (SolSparsePulse) := [⟨1,[502,489,482,481,487,508,558,662,900,
  865,1262],15245⟩, ⟨1,[435,427,425,428,439,460,503,582,756,691,1254],15342⟩, ⟨1,[282,280,281,288,
  303,327,370,442,585,609,1308],14760⟩, ⟨1,[0,0,0,0,0,0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 12` (`L = 12`). -/
def solExplicitPulses_r12 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r12_c0) ( solExplicitPulses_r12_c1)) ( List.append ( solExplicitPulses_r12_c2) (
  List.append ( solExplicitPulses_r12_c3) ( solExplicitPulses_r12_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r12_c5) ( solExplicitPulses_r12_c6)) ( List.append ( solExplicitPulses_r12_c7)
  ( List.append ( solExplicitPulses_r12_c8) ( solExplicitPulses_r12_c9))))
/-- Stratum angle-ratio intervals for `r = 12`. -/
def solRatios_r12 : List (IvInt) := [(957427106,957427109),(912870928,912870931),(866025402,
  866025405),(816496579,816496582),(763762614,763762617),(707106780,707106783),(645497223,
  645497226),(577350268,577350271),(499999999,500000002),(408248289,408248292),(288675133,
  288675136)]
/-- Chunk 0 of `solTrigIvs_r12`. -/
def solTrigIvs_r12_c0 : List (IvInt × IvInt) := [((972364508,972364509),(233467904,233467905)),
  ((974657687,974657688),(223701570,223701571)),((976952641,976952642),(213456170,213456172)),
  ((979249371,979249372),(202658996,202658998)),((981547877,981547879),(191216534,191216536)),
  ((983848162,983848163),(179005007,179005009))]
/-- Chunk 1 of `solTrigIvs_r12`. -/
def solTrigIvs_r12_c1 : List (IvInt × IvInt) := [((986150225,986150226),(165854551,165854553)),
  ((988454068,988454069),(151520807,151520808)),((990759690,990759691),(135629033,135629035)),
  ((993067094,993067095),(117548907,117548909)),((995376280,995376281),(96052386,96052388)),
  ((997687248,997687249),(67971718,67971720))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 12`. -/
def solTrigIvs_r12 : List (IvInt × IvInt) := List.append ( solTrigIvs_r12_c0) ( solTrigIvs_r12_c1)
/-- Certified suffix probability lower bounds for `r = 12`. -/
def solTailLbs_r12 : List (ℤ) := [999999155,999999154,999999154,999999153,999999151,999999149,
  999999145,999999133,999998968,999991554,999724512,991041971]
/-- Stage specification for explicit `m = 1` conveyor at `r = 12`. -/
def solStage_r12 : PulseM1StageSpec := ⟨12, 23564263, 100000000,
    solToSwLPulses 12 65536 solExplicitPulses_r12⟩
/-- Chunk 0 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c0 : List (SolSparsePulse) := [⟨1,[16059,9605,7369,6212,5512,5056,4752,
  4550,4422,4348,4315,4315],(-52)⟩, ⟨1,[14850,10724,7633,6118,5216,4645,4285,4077,3988,4002,4106,
  4294],(-19)⟩, ⟨1,[13212,11031,9056,6933,5675,4890,4397,4104,3956,3922,3984,4127],(-3)⟩, ⟨1,[11486,
  11253,9160,7418,5973,5069,4467,4053,3785,3637,3592,3642],0⟩, ⟨1,[9908,11290,9321,8152,6413,5243,
  4462,3902,3491,3186,2972,2844],(-2)⟩, ⟨1,[8578,11083,9503,8278,6821,5522,4575,3862,3300,2837,2439,
  2086],0⟩, ⟨1,[7513,10643,9673,8304,7217,5804,4779,4007,3359,2799,2293,1822],0⟩, ⟨1,[6676,10039,
  9803,8423,7585,6148,5017,4207,3560,3016,2527,2078],0⟩, ⟨1,[6024,9344,9846,8536,7607,6466,5277,
  4383,3720,3201,2763,2373],0⟩, ⟨1,[5515,8636,9771,8663,7605,6716,5482,4515,3799,3230,2770,2376],0⟩,
  ⟨1,[5119,7974,9569,8786,7700,6961,5700,4647,3876,3241,2721,2283],0⟩, ⟨1,[4787,7378,9260,8884,7764,
  7018,5941,4829,3990,3322,2771,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c1 : List (SolSparsePulse) := [⟨1,[4515,6857,8867,8936,7866,6983,6142,
  5025,4103,3401,2832,2326],0⟩, ⟨1,[4292,6420,8424,8921,7956,7035,6310,5183,4200,3456,2853,2341],0⟩,
  ⟨1,[4094,6042,7970,8829,8056,7105,6425,5341,4306,3530,2882,2351],0⟩, ⟨1,[3922,5721,7529,8661,8140,
  7152,6417,5508,4439,3603,2912,2339],0⟩, ⟨1,[3773,5448,7117,8428,8196,7234,6398,5646,4589,3674,
  2948,2335],0⟩, ⟨1,[3637,5211,6740,8142,8220,7298,6449,5759,4723,3748,2983,2347],0⟩, ⟨1,[3509,5011,
  6406,7822,8196,7379,6503,5828,4830,3819,3023,2364],0⟩, ⟨1,[3390,4828,6107,7490,8118,7460,6537,
  5822,4940,3898,3071,2370],0⟩, ⟨1,[3281,4658,5850,7155,7987,7523,6603,5802,5042,4001,3116,2362],0⟩,
  ⟨1,[3179,4509,5632,6843,7804,7567,6663,5837,5125,4114,3159,2366],0⟩, ⟨1,[3086,4379,5422,6551,7588,
  7582,6721,5886,5182,4206,3203,2381],0⟩, ⟨1,[3000,4254,5232,6278,7347,7562,6795,5914,5197,4276,
  3249,2390],0⟩]
/-- Chunk 2 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c2 : List (SolSparsePulse) := [⟨1,[2919,4132,5074,6034,7089,7507,6852,
  5952,5178,4341,3296,2396],0⟩, ⟨1,[2841,4013,4930,5814,6827,7413,6907,6011,5182,4406,3349,2406],0⟩,
  ⟨1,[2763,3903,4788,5618,6574,7278,6951,6054,5223,4455,3420,2424],0⟩, ⟨1,[2684,3801,4657,5440,6334,
  7114,6971,6110,5261,4487,3491,2441],0⟩, ⟨1,[2604,3706,4544,5269,6103,6931,6966,6171,5281,4495,
  3539,2454],0⟩, ⟨1,[2524,3616,4440,5118,5890,6729,6938,6219,5313,4483,3573,2466],0⟩, ⟨1,[2443,3530,
  4333,4991,5698,6519,6878,6271,5360,4485,3606,2482],0⟩, ⟨1,[2363,3445,4224,4872,5516,6307,6789,
  6317,5392,4516,3640,2501],0⟩, ⟨1,[2285,3361,4117,4750,5353,6098,6673,6350,5437,4551,3663,2522],0⟩,
  ⟨1,[2212,3274,4017,4632,5213,5901,6533,6364,5495,4571,3673,2545],0⟩, ⟨1,[2138,3181,3927,4528,5077,
  5716,6378,6360,5540,4592,3675,2565],0⟩, ⟨1,[2073,3086,3843,4437,4944,5539,6210,6335,5590,4629,
  3671,2574],0⟩]
/-- Chunk 3 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c3 : List (SolSparsePulse) := [⟨1,[2003,2984,3759,4349,4827,5378,6037,
  6284,5637,4662,3680,2581],0⟩, ⟨1,[1939,2881,3675,4253,4722,5225,5862,6215,5674,4688,3706,2591],0⟩,
  ⟨1,[1873,2776,3592,4151,4618,5083,5685,6125,5707,4734,3732,2602],0⟩, ⟨1,[1806,2670,3509,4051,4513,
  4960,5516,6013,5729,4781,3749,2609],0⟩, ⟨1,[1742,2566,3423,3957,4412,4846,5361,5885,5736,4820,
  3766,2612],0⟩, ⟨1,[1686,2467,3333,3873,4323,4728,5210,5750,5725,4867,3796,2617],0⟩, ⟨1,[1638,2376,
  3237,3797,4245,4613,5064,5608,5698,4913,3826,2623],0⟩, ⟨1,[1593,2289,3136,3725,4169,4515,4930,
  5459,5654,4952,3848,2635],0⟩, ⟨1,[1546,2201,3026,3648,4081,4428,4806,5311,5592,4990,3883,2654],0⟩,
  ⟨1,[1498,2116,2912,3567,3984,4340,4688,5164,5515,5020,3924,2671],0⟩, ⟨1,[1462,2042,2801,3485,3884,
  4247,4581,5020,5422,5045,3958,2684],0⟩, ⟨1,[1452,1986,2698,3405,3792,4154,4483,4888,5312,5060,
  3995,2699],0⟩]
/-- Chunk 4 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c4 : List (SolSparsePulse) := [⟨1,[1470,1952,2608,3328,3711,4071,4380,
  4764,5199,5058,4041,2721],0⟩, ⟨1,[1481,1918,2521,3245,3640,3999,4278,4637,5082,5045,4081,2743],0⟩,
  ⟨1,[1409,1853,2433,3157,3577,3928,4189,4516,4956,5023,4121,2763],0⟩, ⟨1,[1274,1770,2356,3078,3524,
  3848,4111,4408,4830,4981,4166,2787],0⟩, ⟨1,[1191,1681,2255,2970,3460,3753,4031,4305,4707,4926,
  4202,2817],0⟩, ⟨1,[1142,1601,2158,2858,3394,3652,3944,4206,4581,4864,4233,2845],0⟩, ⟨1,[1110,1528,
  2068,2749,3327,3558,3854,4116,4456,4788,4265,2872],0⟩, ⟨1,[1082,1459,1990,2653,3266,3479,3769,
  4026,4344,4697,4292,2908],0⟩, ⟨1,[1050,1394,1916,2562,3206,3421,3694,3933,4238,4601,4306,2949],0⟩,
  ⟨1,[1025,1342,1841,2463,3132,3374,3621,3843,4129,4501,4311,2987],0⟩, ⟨1,[1004,1297,1763,2358,3047,
  3335,3543,3760,4025,4398,4307,3027],0⟩, ⟨1,[985,1257,1686,2257,2956,3301,3454,3681,3927,4291,4294,
  3072],0⟩]
/-- Chunk 5 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c5 : List (SolSparsePulse) := [⟨1,[966,1219,1612,2163,2867,3273,3362,3595,
  3833,4182,4270,3116],0⟩, ⟨1,[952,1185,1545,2075,2776,3248,3283,3505,3742,4074,4235,3161],0⟩, ⟨1,
  [941,1155,1485,1985,2668,3208,3221,3415,3652,3969,4189,3208],0⟩, ⟨1,[930,1126,1430,1894,2550,3151,
  3179,3329,3560,3864,4134,3254],0⟩, ⟨1,[919,1100,1379,1808,2433,3085,3159,3242,3467,3760,4071,
  3298],0⟩, ⟨1,[905,1072,1330,1726,2322,3013,3161,3156,3373,3662,4000,3343],0⟩, ⟨1,[885,1041,1280,
  1649,2210,2921,3164,3079,3277,3564,3922,3384],0⟩, ⟨1,[864,1011,1233,1579,2098,2809,3156,3024,3175,
  3463,3840,3422],0⟩, ⟨1,[840,979,1187,1512,1991,2692,3147,3005,3073,3361,3752,3457],0⟩, ⟨1,[813,
  947,1142,1449,1893,2576,3131,3018,2979,3260,3658,3489],0⟩, ⟨1,[788,918,1102,1392,1808,2454,3070,
  3029,2890,3149,3565,3515],0⟩, ⟨1,[756,883,1059,1332,1727,2328,2975,3034,2794,3032,3468,3538],0⟩]
/-- Chunk 6 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c6 : List (SolSparsePulse) := [⟨1,[726,850,1018,1277,1652,2211,2875,3047,
  2715,2915,3361,3557],0⟩, ⟨1,[704,824,985,1229,1584,2109,2762,3032,2706,2780,3252,3569],0⟩, ⟨1,
  [676,793,946,1177,1515,2011,2637,2986,2790,2619,3137,3578],0⟩, ⟨1,[657,769,915,1131,1452,1920,
  2529,2924,2917,2487,3000,3583],0⟩, ⟨1,[646,751,888,1091,1394,1836,2433,2828,2992,2377,2837,3589],
  0⟩, ⟨1,[623,720,850,1040,1327,1746,2335,2734,3002,2304,2632,3591],0⟩, ⟨1,[623,711,829,1005,1274,
  1669,2243,2675,2858,2483,2352,3594],(-6)⟩, ⟨1,[633,709,816,976,1226,1597,2152,2627,2676,2890,1924,
  3605],(-9)⟩, ⟨1,[643,708,803,947,1179,1527,2060,2574,2584,2840,1927,3042],9682⟩, ⟨1,[658,712,794,
  923,1136,1462,1971,2513,2536,2592,2391,2175],15610⟩, ⟨1,[673,716,786,900,1094,1398,1882,2443,2500,
  2480,2342,2121],15717⟩, ⟨1,[688,720,778,878,1053,1336,1793,2364,2468,2430,2303,2068],15793⟩]
/-- Chunk 7 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c7 : List (SolSparsePulse) := [⟨1,[717,739,785,869,1026,1286,1714,2284,
  2440,2394,2267,2019],15854⟩, ⟨1,[745,756,790,861,999,1237,1634,2197,2411,2358,2221,1973],15922⟩,
  ⟨1,[777,779,801,858,977,1193,1560,2107,2380,2322,2173,1924],15993⟩, ⟨1,[822,815,826,870,970,1164,
  1498,2022,2350,2288,2129,1876],16054⟩, ⟨1,[840,825,828,861,946,1120,1427,1928,2309,2253,2089,
  1830],16103⟩, ⟨1,[851,830,825,848,920,1076,1359,1835,2261,2219,2053,1787],16146⟩, ⟨1,[860,832,820,
  834,894,1034,1293,1743,2204,2182,2019,1743],16185⟩, ⟨1,[898,864,845,851,898,1020,1253,1672,2152,
  2146,1985,1701],16221⟩, ⟨1,[908,868,844,842,879,987,1200,1591,2086,2103,1951,1660],16253⟩, ⟨1,
  [914,870,840,832,861,955,1150,1516,2016,2058,1917,1620],16277⟩, ⟨1,[951,903,869,854,874,955,1131,
  1468,1961,2022,1883,1583],16293⟩, ⟨1,[924,873,836,819,834,908,1072,1391,1882,1977,1852,1547],
  16301⟩]
/-- Chunk 8 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c8 : List (SolSparsePulse) := [⟨1,[892,840,802,783,795,863,1017,1319,1804,
  1937,1823,1512],16304⟩, ⟨1,[870,817,778,757,767,828,972,1257,1729,1901,1794,1479],16303⟩, ⟨1,[875,
  823,782,760,765,817,949,1213,1665,1871,1765,1448],16295⟩, ⟨1,[862,810,770,747,749,795,915,1161,
  1593,1838,1734,1420],16276⟩, ⟨1,[830,781,743,720,720,761,872,1102,1515,1804,1703,1394],16246⟩, ⟨1,
  [779,732,697,676,676,713,815,1030,1424,1760,1668,1371],16204⟩, ⟨1,[755,712,679,660,658,689,780,
  976,1344,1717,1635,1351],16153⟩, ⟨1,[706,668,639,621,619,647,727,905,1248,1655,1600,1335],16092⟩,
  ⟨1,[620,587,562,548,547,572,644,805,1122,1556,1547,1324],16017⟩, ⟨1,[628,601,580,567,565,583,641,
  773,1045,1465,1474,1317],15923⟩, ⟨1,[618,596,579,569,567,581,626,732,957,1343,1349,1317],15812⟩,
  ⟨1,[583,566,555,548,548,561,598,682,862,1194,1168,1323],15681⟩]
/-- Chunk 9 of `solExplicitPulses_r13`. -/
def solExplicitPulses_r13_c9 : List (SolSparsePulse) := [⟨1,[502,490,483,481,485,498,531,597,736,
  1001,931,1339],15490⟩, ⟨1,[435,428,426,428,435,450,479,532,634,824,715,1344],15461⟩, ⟨1,[282,280,
  281,287,297,316,347,397,483,633,615,1382],15055⟩, ⟨1,[0,0,0,0,0,0,0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 13` (`L = 13`). -/
def solExplicitPulses_r13 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r13_c0) ( solExplicitPulses_r13_c1)) ( List.append ( solExplicitPulses_r13_c2) (
  List.append ( solExplicitPulses_r13_c3) ( solExplicitPulses_r13_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r13_c5) ( solExplicitPulses_r13_c6)) ( List.append ( solExplicitPulses_r13_c7)
  ( List.append ( solExplicitPulses_r13_c8) ( solExplicitPulses_r13_c9))))
/-- Stratum angle-ratio intervals for `r = 13`. -/
def solRatios_r13 : List (IvInt) := [(960768921,960768924),(919866210,919866213),(877058018,
  877058021),(832050293,832050296),(784464539,784464542),(733799384,733799387),(679366219,
  679366222),(620173671,620173674),(554700195,554700198),(480384460,480384463),(392232269,
  392232272),(277350097,277350100)]
/-- Chunk 0 of `solTrigIvs_r13`. -/
def solTrigIvs_r13_c0 : List (IvInt × IvInt) := [((968377598,968377599),(249489133,249489134)),
  ((970798178,970798180),(239897676,239897678)),((973220741,973220742),(229872547,229872548)),
  ((975645286,975645288),(219354220,219354221)),((978071815,978071816),(208267911,208267912)),
  ((980500329,980500330),(196517439,196517440))]
/-- Chunk 1 of `solTrigIvs_r13`. -/
def solTrigIvs_r13_c1 : List (IvInt × IvInt) := [((982930828,982930829),(183975504,183975506)),
  ((985363314,985363315),(170467413,170467415)),((987797787,987797788),(155741873,155741875)),
  ((990234248,990234250),(139413529,139413530)),((992672700,992672701),(120834226,120834228)),
  ((995113141,995113142),(98741253,98741255))]
/-- Chunk 2 of `solTrigIvs_r13`. -/
def solTrigIvs_r13_c2 : List (IvInt × IvInt) := [((997555574,997555575),(69877574,69877576))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 13`. -/
def solTrigIvs_r13 : List (IvInt × IvInt) := List.append ( solTrigIvs_r13_c0) ( List.append (
  solTrigIvs_r13_c1) ( solTrigIvs_r13_c2))
/-- Certified suffix probability lower bounds for `r = 13`. -/
def solTailLbs_r13 : List (ℤ) := [999999058,999999058,999999058,999999058,999999057,999999055,
  999999054,999999052,999999037,999998831,999988733,999656675,989709204]
/-- Stage specification for explicit `m = 1` conveyor at `r = 13`. -/
def solStage_r13 : PulseM1StageSpec := ⟨13, 25215267, 100000000,
    solToSwLPulses 13 65536 solExplicitPulses_r13⟩
/-- Chunk 0 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c0 : List (SolSparsePulse) := [⟨1,[17094,10143,7741,6501,5745,5246,4904,
  4668,4507,4403,4342,4315,4315],(-52)⟩, ⟨1,[15647,11530,8148,6497,5517,4883,4465,4198,4047,3991,
  4019,4122,4294],(-19)⟩, ⟨1,[13742,11859,9742,7463,6094,5217,4644,4275,4055,3948,3933,3996,4127],
  (-3)⟩, ⟨1,[11796,12080,9883,8115,6454,5445,4768,4294,3963,3748,3629,3597,3642],0⟩, ⟨1,[10079,
  12038,10081,8891,7028,5731,4852,4228,3765,3415,3151,2961,2844],(-2)⟩, ⟨1,[8674,11704,10273,8920,
  7503,6066,5048,4278,3675,3184,2771,2410,2086],0⟩, ⟨1,[7580,11105,10469,9024,8012,6419,5292,4457,
  3791,3219,2715,2254,1822],0⟩, ⟨1,[6747,10354,10564,9151,8278,6851,5585,4680,3992,3424,2934,2490,
  2078],0⟩, ⟨1,[6093,9550,10538,9296,8237,7208,5883,4904,4162,3590,3128,2730,2373],0⟩, ⟨1,[5606,
  8764,10361,9434,8320,7517,6142,5080,4276,3657,3153,2737,2376],0⟩, ⟨1,[5212,8064,10034,9563,8412,
  7678,6449,5265,4390,3718,3155,2685,2283],0⟩, ⟨1,[4882,7448,9606,9627,8527,7641,6727,5492,4549,
  3823,3231,2732,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c1 : List (SolSparsePulse) := [⟨1,[4623,6941,9099,9629,8618,7680,6946,
  5718,4718,3928,3306,2790,2326],0⟩, ⟨1,[4398,6503,8586,9517,8745,7767,7085,5937,4859,4014,3356,
  2810,2341],0⟩, ⟨1,[4202,6134,8084,9326,8827,7834,7085,6161,5007,4112,3422,2837,2351],0⟩, ⟨1,[4033,
  5828,7606,9057,8886,7919,7068,6340,5180,4231,3487,2864,2339],0⟩, ⟨1,[3880,5563,7189,8710,8913,
  7987,7132,6467,5356,4362,3553,2897,2335],0⟩, ⟨1,[3737,5340,6824,8342,8857,8101,7195,6523,5532,
  4485,3620,2930,2347],0⟩, ⟨1,[3603,5137,6484,7965,8748,8169,7253,6503,5693,4592,3687,2968,2364],0⟩,
  ⟨1,[3480,4953,6209,7585,8575,8232,7321,6503,5814,4711,3761,3013,2370],0⟩, ⟨1,[3370,4793,5975,7237,
  8337,8272,7375,6559,5891,4843,3856,3053,2362],0⟩, ⟨1,[3271,4647,5742,6915,8070,8256,7472,6609,
  5925,4977,3960,3093,2366],0⟩, ⟨1,[3178,4509,5543,6625,7779,8204,7536,6655,5913,5102,4050,3135,
  2381],0⟩, ⟨1,[3088,4373,5376,6364,7476,8107,7594,6714,5910,5197,4128,3178,2390],0⟩]
/-- Chunk 2 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c2 : List (SolSparsePulse) := [⟨1,[3000,4241,5215,6133,7189,7949,7650,
  6757,5952,5252,4209,3222,2396],0⟩, ⟨1,[2912,4118,5064,5927,6911,7765,7663,6832,6001,5280,4301,
  3274,2406],0⟩, ⟨1,[2823,4011,4931,5730,6638,7557,7651,6899,6035,5282,4392,3343,2424],0⟩, ⟨1,[2732,
  3915,4809,5558,6400,7313,7620,6942,6078,5273,4476,3414,2441],0⟩, ⟨1,[2642,3823,4691,5414,6188,
  7067,7535,7008,6117,5288,4535,3468,2454],0⟩, ⟨1,[2552,3728,4571,5276,5978,6833,7410,7057,6158,
  5330,4562,3513,2467],0⟩, ⟨1,[2463,3629,4450,5139,5793,6600,7266,7070,6233,5369,4571,3563,2483],0⟩,
  ⟨1,[2376,3526,4333,5011,5636,6370,7100,7069,6282,5399,4572,3620,2503],0⟩, ⟨1,[2294,3418,4229,4898,
  5486,6159,6903,7053,6323,5435,4570,3670,2525],0⟩, ⟨1,[2218,3306,4137,4793,5344,5977,6698,6994,
  6387,5464,4582,3711,2550],0⟩, ⟨1,[2142,3189,4054,4689,5218,5798,6501,6906,6433,5496,4614,3736,
  2573],0⟩, ⟨1,[2075,3073,3970,4583,5098,5622,6301,6799,6457,5563,4648,3743,2586],0⟩]
/-- Chunk 3 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c3 : List (SolSparsePulse) := [⟨1,[2004,2954,3876,4472,4979,5477,6104,
  6668,6470,5613,4674,3743,2599],0⟩, ⟨1,[1939,2838,3773,4362,4867,5352,5919,6515,6472,5647,4705,
  3745,2616],0⟩, ⟨1,[1874,2724,3663,4259,4766,5219,5744,6351,6447,5705,4735,3750,2634],0⟩, ⟨1,[1806,
  2613,3547,4167,4674,5089,5586,6181,6395,5755,4755,3766,2648],0⟩, ⟨1,[1742,2506,3427,4087,4583,
  4977,5438,6010,6325,5790,4799,3793,2656],0⟩, ⟨1,[1686,2407,3305,4011,4486,4877,5290,5838,6235,
  5818,4858,3819,2661],0⟩, ⟨1,[1638,2317,3182,3933,4386,4776,5159,5671,6123,5840,4891,3839,2663],0⟩,
  ⟨1,[1593,2232,3059,3847,4283,4674,5049,5516,5994,5847,4927,3868,2667],0⟩, ⟨1,[1546,2147,2933,3746,
  4182,4578,4934,5364,5862,5830,4981,3894,2675],0⟩, ⟨1,[1498,2065,2808,3632,4088,4492,4814,5216,
  5720,5800,5025,3911,2686],0⟩, ⟨1,[1462,1994,2692,3513,4005,4411,4710,5087,5568,5756,5066,3942,
  2702],0⟩, ⟨1,[1452,1942,2589,3394,3933,4326,4622,4966,5422,5689,5103,3993,2720],0⟩]
/-- Chunk 4 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c4 : List (SolSparsePulse) := [⟨1,[1470,1911,2504,3280,3867,4231,4536,
  4841,5277,5608,5130,4026,2736],0⟩, ⟨1,[1481,1881,2423,3164,3799,4130,4443,4729,5133,5510,5156,
  4052,2753],0⟩, ⟨1,[1409,1815,2337,3049,3724,4029,4348,4634,5000,5397,5166,4101,2775],0⟩, ⟨1,[1274,
  1729,2258,2947,3649,3939,4260,4534,4872,5285,5158,4149,2794],0⟩, ⟨1,[1191,1640,2158,2824,3547,
  3855,4181,4429,4744,5164,5144,4185,2809],0⟩, ⟨1,[1142,1563,2064,2703,3435,3783,4106,4336,4631,
  5033,5116,4230,2832],0⟩, ⟨1,[1110,1493,1977,2590,3320,3723,4022,4255,4526,4904,5066,4275,2867],0⟩,
  ⟨1,[1082,1428,1901,2492,3211,3675,3926,4174,4417,4781,5006,4311,2898],0⟩, ⟨1,[1050,1365,1829,2402,
  3107,3631,3826,4083,4312,4655,4936,4344,2922],0⟩, ⟨1,[1025,1316,1758,2307,2994,3577,3729,3989,
  4221,4534,4853,4375,2956],0⟩, ⟨1,[1004,1273,1685,2208,2876,3510,3645,3901,4133,4422,4758,4394,
  3002],0⟩, ⟨1,[985,1235,1614,2113,2762,3432,3579,3820,4038,4309,4659,4404,3042],0⟩]
/-- Chunk 5 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c5 : List (SolSparsePulse) := [⟨1,[966,1198,1546,2024,2656,3349,3534,3741,
  3943,4198,4555,4405,3080],0⟩, ⟨1,[952,1166,1485,1941,2555,3261,3508,3657,3858,4098,4446,4396,
  3124],0⟩, ⟨1,[941,1137,1431,1859,2446,3154,3487,3568,3773,4002,4336,4377,3170],0⟩, ⟨1,[930,1110,
  1380,1778,2333,3035,3462,3480,3682,3904,4224,4346,3218],0⟩, ⟨1,[919,1085,1333,1700,2224,2915,3432,
  3404,3588,3807,4115,4302,3269],0⟩, ⟨1,[905,1058,1287,1627,2121,2797,3395,3353,3494,3711,4009,4249,
  3318],0⟩, ⟨1,[885,1028,1241,1557,2021,2673,3335,3325,3403,3613,3900,4187,3365],0⟩, ⟨1,[864,999,
  1196,1493,1923,2544,3249,3315,3311,3517,3795,4115,3410],0⟩, ⟨1,[840,967,1153,1431,1830,2418,3152,
  3324,3228,3419,3695,4037,3454],0⟩, ⟨1,[813,936,1110,1373,1744,2300,3049,3343,3171,3312,3589,3955,
  3496],0⟩, ⟨1,[788,907,1072,1319,1668,2188,2921,3332,3143,3200,3479,3864,3535],0⟩, ⟨1,[756,872,
  1030,1264,1595,2077,2776,3291,3141,3100,3377,3767,3569],0⟩]
/-- Chunk 6 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c6 : List (SolSparsePulse) := [⟨1,[726,840,990,1212,1527,1976,2638,3240,
  3167,3007,3266,3671,3597],0⟩, ⟨1,[704,814,958,1168,1466,1888,2505,3160,3193,2912,3135,3573,3621],
  0⟩, ⟨1,[676,783,921,1119,1402,1802,2373,3052,3204,2834,3005,3461,3642],0⟩, ⟨1,[657,759,890,1077,
  1345,1723,2257,2940,3190,2822,2872,3345,3659],0⟩, ⟨1,[646,742,865,1040,1293,1650,2155,2818,3124,
  2893,2707,3222,3669],0⟩, ⟨1,[623,712,828,992,1231,1570,2052,2693,3042,3039,2557,3078,3677],0⟩, ⟨1,
  [623,703,810,961,1185,1504,1961,2585,2946,3141,2453,2905,3682],0⟩, ⟨1,[633,703,799,936,1143,1443,
  1876,2484,2858,3125,2403,2675,3686],0⟩, ⟨1,[643,703,787,911,1102,1382,1792,2381,2804,2960,2614,
  2365,3692],(-14)⟩, ⟨1,[658,707,780,891,1065,1326,1714,2279,2758,2775,3058,1881,3708],0⟩, ⟨1,[673,
  712,774,871,1029,1271,1637,2177,2704,2686,2896,2158,2804],12308⟩, ⟨1,[688,718,768,853,995,1219,
  1562,2075,2639,2639,2653,2477,2215],15841⟩]
/-- Chunk 7 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c7 : List (SolSparsePulse) := [⟨1,[717,737,777,848,974,1178,1498,1981,
  2566,2602,2559,2403,2169],15905⟩, ⟨1,[745,755,785,843,953,1138,1434,1888,2482,2567,2515,2367,
  2111],15994⟩, ⟨1,[777,779,798,844,938,1103,1376,1799,2391,2534,2477,2331,2060],16057⟩, ⟨1,[822,
  815,824,859,937,1083,1331,1722,2302,2505,2439,2282,2010],16127⟩, ⟨1,[840,827,828,853,918,1048,
  1274,1638,2201,2470,2401,2233,1960],16197⟩, ⟨1,[851,831,826,842,896,1012,1218,1557,2098,2433,2365,
  2188,1912],16253⟩, ⟨1,[860,834,822,831,875,977,1164,1478,1994,2388,2329,2148,1867],16297⟩, ⟨1,
  [898,867,848,849,882,969,1137,1425,1908,2345,2294,2112,1822],16335⟩, ⟨1,[908,872,848,842,867,942,
  1094,1361,1813,2288,2255,2077,1777],16371⟩, ⟨1,[914,874,845,834,851,916,1053,1300,1724,2225,2211,
  2042,1733],16405⟩, ⟨1,[951,907,874,858,868,922,1043,1270,1661,2172,2168,2007,1690],16434⟩, ⟨1,
  [924,877,842,823,829,877,990,1204,1573,2095,2117,1973,1650],16453⟩]
/-- Chunk 8 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c8 : List (SolSparsePulse) := [⟨1,[892,844,808,788,791,835,940,1143,1492,
  2018,2067,1940,1613],16460⟩, ⟨1,[870,821,784,763,764,802,900,1091,1421,1940,2019,1909,1578],
  16457⟩, ⟨1,[875,827,789,766,763,796,883,1059,1367,1870,1978,1878,1545],16449⟩, ⟨1,[862,814,777,
  753,748,776,855,1018,1306,1793,1939,1847,1513],16435⟩, ⟨1,[830,785,749,726,720,744,817,969,1241,
  1710,1905,1814,1484],16414⟩, ⟨1,[779,736,703,681,676,698,764,905,1162,1615,1867,1777,1459],16380⟩,
  ⟨1,[755,716,685,664,659,677,735,862,1100,1528,1835,1738,1437],16332⟩, ⟨1,[706,671,644,625,620,636,
  688,802,1021,1425,1788,1697,1419],16269⟩, ⟨1,[620,590,566,551,548,562,609,712,912,1291,1708,1646,
  1406],16194⟩, ⟨1,[628,603,583,570,566,576,613,696,865,1197,1629,1578,1399],16102⟩, ⟨1,[618,598,
  582,571,568,575,604,670,809,1089,1509,1461,1398],15990⟩, ⟨1,[583,568,557,550,548,556,580,633,744,
  970,1350,1275,1403],15859⟩]
/-- Chunk 9 of `solExplicitPulses_r14`. -/
def solExplicitPulses_r14_c9 : List (SolSparsePulse) := [⟨1,[502,491,484,482,484,493,515,558,644,
  818,1133,1009,1420],15683⟩, ⟨1,[435,429,426,427,433,444,465,501,567,690,918,741,1433],15570⟩, ⟨1,
  [282,280,281,285,294,308,331,367,426,524,693,607,1465],15283⟩, ⟨1,[0,0,0,0,0,0,0,0,0,0,0,0,0],
  (-96)⟩]
/-- Explicit rational pulses for `r = 14` (`L = 14`). -/
def solExplicitPulses_r14 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r14_c0) ( solExplicitPulses_r14_c1)) ( List.append ( solExplicitPulses_r14_c2) (
  List.append ( solExplicitPulses_r14_c3) ( solExplicitPulses_r14_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r14_c5) ( solExplicitPulses_r14_c6)) ( List.append ( solExplicitPulses_r14_c7)
  ( List.append ( solExplicitPulses_r14_c8) ( solExplicitPulses_r14_c9))))
/-- Chunk 0 of `solRatios_r14`. -/
def solRatios_r14_c0 : List (IvInt) := [(963624110,963624113),(925820098,925820101),(886405259,
  886405262),(845154253,845154256),(801783724,801783727),(755928945,755928948),(707106780,
  707106783),(654653669,654653672),(597614303,597614306),(534522482,534522485),(462910048,
  462910051),(377964472,377964475)]
/-- Chunk 1 of `solRatios_r14`. -/
def solRatios_r14_c1 : List (IvInt) := [(267261240,267261243)]
/-- Stratum angle-ratio intervals for `r = 14`. -/
def solRatios_r14 : List (IvInt) := List.append ( solRatios_r14_c0) ( solRatios_r14_c1)
/-- Chunk 0 of `solTrigIvs_r14`. -/
def solTrigIvs_r14_c0 : List (IvInt × IvInt) := [((964209916,964209917),(265140032,265140033)),
  ((966752086,966752087),(255715473,255715475)),((969296445,969296447),(245895098,245895100)),
  ((971842996,971842998),(235629346,235629348)),((974391740,974391741),(224857146,224857147)),
  ((976942677,976942678),(213501769,213501770))]
/-- Chunk 1 of `solTrigIvs_r14`. -/
def solTrigIvs_r14_c1 : List (IvInt × IvInt) := [((979495808,979495809),(201464540,201464542)),
  ((982051135,982051136),(188614864,188614866)),((984608659,984608660),(174773532,174773534)),
  ((987168381,987168382),(159682769,159682770)),((989730302,989730303),(142947292,142947294)),
  ((992294423,992294424),(123902287,123902289))]
/-- Chunk 2 of `solTrigIvs_r14`. -/
def solTrigIvs_r14_c2 : List (IvInt × IvInt) := [((994860746,994860747),(101252633,101252634)),
  ((997429271,997429272),(71657859,71657860))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 14`. -/
def solTrigIvs_r14 : List (IvInt × IvInt) := List.append ( solTrigIvs_r14_c0) ( List.append (
  solTrigIvs_r14_c1) ( solTrigIvs_r14_c2))
/-- Certified suffix probability lower bounds for `r = 14`. -/
def solTailLbs_r14 : List (ℤ) := [999998963,999998963,999998963,999998962,999998962,999998962,
  999998960,999998959,999998957,999998939,999998614,999985382,999574975,988094166]
/-- Stage specification for explicit `m = 1` conveyor at `r = 14`. -/
def solStage_r14 : PulseM1StageSpec := ⟨14, 26834915, 100000000,
    solToSwLPulses 14 65536 solExplicitPulses_r14⟩
/-- Chunk 0 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c0 : List (SolSparsePulse) := [⟨1,[18081,10678,8111,6788,5978,5438,5062,
  4795,4606,4475,4389,4338,4315,4315],(-52)⟩, ⟨1,[16387,12298,8669,6878,5818,5127,4658,4342,4140,
  4030,3998,4035,4135,4294],(-19)⟩, ⟨1,[14208,12665,10412,7989,6516,5554,4908,4474,4190,4022,3944,
  3942,4006,4127],(-3)⟩, ⟨1,[12056,12862,10591,8878,6965,5834,5081,4549,4167,3897,3720,3624,3600,
  3642],0⟩, ⟨1,[10214,12729,10807,9584,7660,6229,5258,4564,4050,3657,3354,3122,2952,2844],(-2)⟩, ⟨1,
  [8755,12243,11038,9575,8236,6625,5518,4693,4046,3524,3089,2715,2385,2086],0⟩, ⟨1,[7647,11490,
  11219,9724,8816,7081,5812,4907,4201,3615,3103,2644,2221,1822],0⟩, ⟨1,[6809,10601,11269,9870,8897,
  7582,6174,5167,4415,3817,3311,2866,2458,2078],0⟩, ⟨1,[6175,9696,11153,10032,8908,7999,6521,5431,
  4619,3986,3483,3067,2703,2373],0⟩, ⟨1,[5694,8865,10853,10184,9021,8294,6868,5654,4771,4086,3541,
  3089,2709,2376],0⟩, ⟨1,[5300,8138,10400,10289,9110,8294,7238,5914,4929,4183,3588,3082,2654,2283],
  0⟩, ⟨1,[4991,7526,9853,10303,9253,8303,7536,6194,5130,4326,3686,3154,2698,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c1 : List (SolSparsePulse) := [⟨1,[4725,7016,9268,10216,9364,8397,7731,
  6476,5337,4475,3784,3226,2754,2326],0⟩, ⟨1,[4497,6597,8696,10006,9485,8447,7739,6757,5534,4599,
  3862,3272,2774,2341],0⟩, ⟨1,[4307,6236,8160,9705,9546,8566,7720,6993,5750,4733,3953,3332,2800,2351
    ],0⟩, ⟨1,[4138,5940,7685,9322,9569,8645,7795,7151,5971,4891,4059,3392,2824,2339 ],0⟩, ⟨1,[3980,
  5694,7268,8901,9508,8756,7842,7195,6192,5059,4176,3452,2853,2335 ],0⟩, ⟨1,[3829,5460,6896,8471,
  9367,8846,7905,7162,6396,5232,4286,3514,2885,2347 ],0⟩, ⟨1,[3691,5253,6599,8047,9155,8900,8001,
  7190,6542,5404,4385,3576,2921,2364 ],0⟩, ⟨1,[3568,5082,6328,7664,8875,8932,8058,7250,6617,5571,
  4497,3646,2963,2370 ],0⟩, ⟨1,[3459,4927,6082,7316,8561,8899,8162,7278,6618,5735,4626,3733,3000,
  2362 ],0⟩, ⟨1,[3360,4776,5878,6993,8228,8810,8236,7346,6599,5882,4768,3828,3037,2366 ],0⟩, ⟨1,
  [3263,4624,5686,6713,7887,8667,8291,7426,6635,5982,4909,3911,3077,2381 ],0⟩, ⟨1,[3166,4477,5502,
  6476,7563,8466,8331,7472,6683,6024,5038,3986,3118,2390 ],0⟩]
/-- Chunk 2 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c2 : List (SolSparsePulse) := [⟨1,[3067,4344,5343,6244,7258,8232,8325,
  7559,6704,6020,5153,4067,3159,2396 ],0⟩, ⟨1,[2967,4227,5209,6038,6978,7969,8282,7624,6755,6007,
  5260,4162,3207,2406 ],0⟩, ⟨1,[2866,4124,5082,5873,6723,7692,8196,7680,6827,6033,5340,4266,3273,
  2424 ],0⟩, ⟨1,[2764,4027,4948,5715,6488,7419,8060,7734,6865,6077,5378,4373,3342,2441 ],0⟩, ⟨1,
  [2665,3924,4810,5554,6283,7151,7889,7754,6932,6098,5381,4466,3394,2454 ],0⟩, ⟨1,[2568,3812,4677,
  5405,6097,6893,7693,7742,7001,6126,5370,4539,3442,2467 ],0⟩, ⟨1,[2473,3690,4557,5281,5922,6663,
  7469,7708,7049,6188,5376,4601,3497,2484 ],0⟩, ⟨1,[2383,3562,4451,5172,5772,6452,7238,7631,7108,
  6228,5410,4648,3562,2503 ],0⟩, ⟨1,[2298,3429,4355,5060,5634,6244,7010,7516,7154,6265,5440,4664,
  3627,2525 ],0⟩, ⟨1,[2220,3295,4262,4936,5496,6063,6781,7376,7172,6337,5455,4661,3687,2551 ],0⟩,
  ⟨1,[2143,3161,4165,4808,5359,5911,6562,7212,7168,6392,5489,4657,3739,2575 ],0⟩, ⟨1,[2075,3032,
  4057,4686,5236,5759,6361,7025,7144,6438,5544,4666,3775,2591 ],0⟩]
/-- Chunk 3 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c3 : List (SolSparsePulse) := [⟨1,[2004,2904,3933,4578,5133,5611,6179,
  6830,7087,6492,5573,4692,3802,2606 ],0⟩, ⟨1,[1939,2783,3797,4481,5039,5483,6000,6637,7003,6536,
  5605,4718,3818,2627 ],0⟩, ⟨1,[1874,2667,3654,4391,4938,5366,5828,6441,6895,6563,5670,4731,3820,
  2651 ],0⟩, ⟨1,[1806,2555,3507,4303,4825,5247,5686,6249,6762,6573,5721,4755,3818,2671 ],0⟩, ⟨1,
  [1742,2449,3362,4210,4704,5127,5557,6067,6612,6567,5764,4802,3824,2687 ],0⟩, ⟨1,[1686,2353,3220,
  4109,4588,5017,5420,5897,6451,6538,5814,4839,3838,2699 ],0⟩, ⟨1,[1638,2265,3084,3996,4486,4926,
  5291,5740,6283,6487,5859,4858,3860,2706 ],0⟩, ⟨1,[1593,2183,2953,3869,4399,4844,5183,5591,6114,
  6412,5898,4903,3879,2712 ],0⟩, ⟨1,[1546,2101,2824,3727,4317,4756,5085,5444,5945,6317,5925,4956,
  3890,2716 ],0⟩, ⟨1,[1498,2021,2700,3576,4234,4652,4982,5317,5780,6202,5942,4994,3913,2719 ],0⟩,
  ⟨1,[1462,1953,2587,3425,4147,4537,4873,5206,5624,6074,5941,5039,3954,2726 ],0⟩, ⟨1,[1452,1904,
  2490,3281,4055,4423,4769,5087,5474,5939,5922,5087,3985,2738 ],0⟩]
/-- Chunk 4 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c4 : List (SolSparsePulse) := [⟨1,[1470,1877,2412,3150,3956,4321,4682,
  4969,5332,5793,5889,5131,4002,2752 ],0⟩, ⟨1,[1481,1850,2339,3025,3844,4234,4607,4871,5205,5643,
  5833,5175,4036,2768 ],0⟩, ⟨1,[1409,1784,2256,2903,3723,4162,4527,4785,5077,5499,5761,5207,4080,
  2779 ],0⟩, ⟨1,[1274,1694,2176,2798,3601,4101,4434,4693,4954,5352,5676,5233,4112,2791 ],0⟩, ⟨1,
  [1191,1605,2078,2674,3456,4031,4325,4592,4850,5209,5571,5254,4154,2813 ],0⟩, ⟨1,[1142,1531,1987,
  2556,3308,3953,4212,4489,4753,5078,5457,5257,4205,2842 ],0⟩, ⟨1,[1110,1464,1903,2448,3164,3867,
  4105,4398,4646,4950,5339,5247,4247,2864 ],0⟩, ⟨1,[1082,1401,1828,2355,3036,3777,4018,4321,4543,
  4829,5212,5225,4290,2880 ],0⟩, ⟨1,[1050,1341,1758,2269,2918,3679,3953,4249,4457,4717,5082,5184,
  4337,2907 ],0⟩, ⟨1,[1025,1293,1690,2179,2798,3566,3902,4166,4375,4604,4956,5130,4376,2940 ],0⟩,
  ⟨1,[1004,1252,1622,2087,2678,3440,3856,4067,4282,4493,4828,5065,4411,2969 ],0⟩, ⟨1,[985,1215,1556,
  1997,2564,3309,3810,3958,4181,4396,4702,4987,4444,3002],0⟩]
/-- Chunk 5 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c5 : List (SolSparsePulse) := [⟨1,[966,1180,1493,1913,2461,3182,3759,3855,
  4080,4305,4584,4896,4470,3045],0⟩, ⟨1,[952,1149,1436,1836,2364,3058,3701,3772,3991,4206,4469,4796,
  4485,3088],0⟩, ⟨1,[941,1122,1386,1760,2263,2927,3623,3713,3912,4108,4355,4690,4489,3129],0⟩, ⟨1,
  [930,1096,1338,1686,2160,2792,3526,3675,3834,4020,4248,4582,4483,3174],0⟩, ⟨1,[919,1072,1295,1616,
  2061,2664,3416,3655,3749,3934,4147,4472,4467,3220],0⟩, ⟨1,[905,1046,1252,1548,1968,2544,3302,3644,
  3660,3838,4046,4358,4442,3269],0⟩, ⟨1,[885,1017,1208,1484,1877,2424,3172,3625,3578,3734,3945,4245,
  4401,3321],0⟩, ⟨1,[864,988,1166,1424,1791,2304,3030,3588,3512,3634,3845,4134,4348,3371],0⟩, ⟨1,
  [840,958,1124,1367,1707,2190,2888,3538,3476,3538,3744,4023,4288,3420],0⟩, ⟨1,[813,926,1083,1312,
  1630,2084,2754,3475,3473,3446,3646,3914,4217,3469],0⟩, ⟨1,[788,898,1046,1262,1561,1986,2614,3374,
  3475,3361,3545,3810,4138,3516],0⟩, ⟨1,[756,863,1006,1210,1493,1890,2471,3244,3473,3296,3433,3701,
  4054,3560],0⟩]
/-- Chunk 6 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c6 : List (SolSparsePulse) := [⟨1,[726,831,967,1161,1430,1802,2341,3109,
  3472,3268,3312,3590,3963,3601],0⟩, ⟨1,[704,806,936,1119,1374,1725,2222,2964,3447,3277,3202,3482,
  3864,3638],0⟩, ⟨1,[676,775,900,1073,1315,1648,2108,2809,3391,3311,3107,3362,3765,3669],0⟩, ⟨1,
  [657,752,870,1034,1263,1578,2008,2665,3315,3347,3014,3226,3662,3695],0⟩, ⟨1,[646,734,846,1000,
  1216,1513,1920,2529,3206,3346,2934,3100,3548,3718],0⟩, ⟨1,[623,705,810,954,1158,1440,1827,2395,
  3082,3314,2921,2954,3430,3736],0⟩, ⟨1,[623,697,793,926,1116,1381,1748,2280,2958,3239,3010,2764,
  3302,3747],0⟩, ⟨1,[633,698,784,905,1080,1328,1675,2175,2836,3140,3170,2617,3147,3757],0⟩, ⟨1,[643,
  698,774,883,1043,1274,1602,2074,2724,3038,3279,2534,2958,3766],0⟩, ⟨1,[658,704,769,866,1012,1226,
  1534,1978,2616,2956,3233,2493,2718,3770],0⟩, ⟨1,[673,709,765,849,981,1179,1468,1886,2505,2908,
  3025,2778,2361,3780],(-10)⟩, ⟨1,[688,715,761,834,951,1133,1404,1797,2391,2864,2849,3213,1850,
  3795],(-116)⟩]
/-- Chunk 7 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c7 : List (SolSparsePulse) := [⟨1,[717,736,771,832,935,1100,1350,1718,
  2282,2812,2779,2876,2373,2588],14288⟩, ⟨1,[745,755,780,830,919,1067,1298,1641,2172,2746,2736,2707,
  2541,2254],16013⟩, ⟨1,[777,779,795,833,909,1040,1250,1569,2067,2667,2695,2641,2470,2206],16076⟩,
  ⟨1,[822,816,823,851,913,1027,1217,1511,1972,2583,2656,2598,2415,2149],16170⟩, ⟨1,[840,828,828,847,
  898,998,1170,1442,1872,2483,2617,2557,2379,2095],16235⟩, ⟨1,[851,833,827,838,880,968,1123,1375,
  1775,2378,2579,2516,2340,2044],16294⟩, ⟨1,[860,836,824,829,861,938,1078,1310,1681,2267,2539,2475,
  2296,1994],16356⟩, ⟨1,[898,869,851,849,872,936,1060,1271,1612,2169,2505,2437,2250,1945],16412⟩,
  ⟨1,[908,874,852,844,860,914,1025,1218,1534,2062,2461,2399,2207,1897],16458⟩, ⟨1,[914,877,850,837,
  846,891,990,1168,1461,1958,2411,2358,2168,1850],16495⟩, ⟨1,[951,910,880,862,865,901,988,1148,1418,
  1879,2367,2316,2130,1805],16528⟩, ⟨1,[924,881,848,828,828,859,938,1089,1344,1778,2301,2264,2095,
  1762],16553⟩]
/-- Chunk 8 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c8 : List (SolSparsePulse) := [⟨1,[892,848,814,793,790,818,892,1034,1276,
  1685,2231,2208,2060,1721],16569⟩, ⟨1,[870,825,790,768,763,787,855,988,1217,1602,2158,2148,2028,
  1682],16574⟩, ⟨1,[875,831,795,771,764,783,843,965,1178,1535,2087,2091,1996,1646],16570⟩, ⟨1,[862,
  818,783,758,749,765,818,931,1130,1465,2008,2038,1964,1611],16561⟩, ⟨1,[830,788,754,731,722,735,
  784,888,1075,1391,1921,1993,1931,1579],16545⟩, ⟨1,[779,740,708,686,677,689,734,831,1006,1306,1823,
  1954,1892,1551],16516⟩, ⟨1,[755,719,690,669,661,670,709,795,956,1235,1730,1928,1849,1527],16470⟩,
  ⟨1,[705,674,648,630,622,630,664,742,889,1148,1621,1898,1801,1508],16408⟩, ⟨1,[620,592,570,555,549,
  557,588,658,791,1031,1480,1843,1746,1494],16334⟩, ⟨1,[628,605,586,573,567,572,596,652,763,969,
  1371,1786,1677,1485],16246⟩, ⟨1,[618,599,584,574,569,573,591,636,724,896,1242,1684,1569,1483],
  16139⟩, ⟨1,[583,569,558,551,549,553,569,605,676,814,1098,1528,1386,1489],16008⟩]
/-- Chunk 9 of `solExplicitPulses_r15`. -/
def solExplicitPulses_r15_c9 : List (SolSparsePulse) := [⟨1,[502,492,485,482,483,490,505,535,591,
  698,918,1296,1098,1506],15841⟩, ⟨1,[435,429,426,427,431,440,455,482,526,605,759,1040,770,1527],
  15684⟩, ⟨1,[282,280,281,284,291,303,321,348,389,456,570,769,585,1553],15461⟩, ⟨1,[0,0,0,0,0,0,0,0,
  0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 15` (`L = 15`). -/
def solExplicitPulses_r15 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r15_c0) ( solExplicitPulses_r15_c1)) ( List.append ( solExplicitPulses_r15_c2) (
  List.append ( solExplicitPulses_r15_c3) ( solExplicitPulses_r15_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r15_c5) ( solExplicitPulses_r15_c6)) ( List.append ( solExplicitPulses_r15_c7)
  ( List.append ( solExplicitPulses_r15_c8) ( solExplicitPulses_r15_c9))))
/-- Chunk 0 of `solRatios_r15`. -/
def solRatios_r15_c0 : List (IvInt) := [(966091782,966091785),(930949335,930949338),(894427189,
  894427192),(856348837,856348840),(816496579,816496582),(774596668,774596671),(730296742,
  730296745),(683130050,683130053),(632455531,632455534),(577350268,577350271),(516397778,
  516397781),(447213594,447213597)]
/-- Chunk 1 of `solRatios_r15`. -/
def solRatios_r15_c1 : List (IvInt) := [(365148370,365148373),(258198888,258198891)]
/-- Stratum angle-ratio intervals for `r = 15`. -/
def solRatios_r15 : List (IvInt) := List.append ( solRatios_r15_c0) ( solRatios_r15_c1)
/-- Chunk 0 of `solTrigIvs_r15`. -/
def solTrigIvs_r15_c0 : List (IvInt × IvInt) := [((959963406,959963407),(280125431,280125432)),
  ((962615752,962615753),(270870657,270870659)),((965270486,965270487),(261252535,261252537)),
  ((967927611,967927612),(251229256,251229257)),((970587126,970587128),(240750137,240750139)),
  ((973249035,973249036),(229752724,229752726))]
/-- Chunk 1 of `solTrigIvs_r15`. -/
def solTrigIvs_r15_c1 : List (IvInt × IvInt) := [((975913337,975913339),(218158558,218158560)),
  ((978580035,978580036),(205866737,205866739)),((981249129,981249130),(192743729,192743731)),
  ((983920621,983920622),(178606298,178606300)),((986594512,986594513),(163190891,163190893)),
  ((989270804,989270805),(146093379,146093381))]
/-- Chunk 2 of `solTrigIvs_r15`. -/
def solTrigIvs_r15_c2 : List (IvInt × IvInt) := [((991949497,991949498),(126634096,126634097)),
  ((994630593,994630594),(103489043,103489045)),((997314094,997314095),(73243414,73243416))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 15`. -/
def solTrigIvs_r15 : List (IvInt × IvInt) := List.append ( solTrigIvs_r15_c0) ( List.append (
  solTrigIvs_r15_c1) ( solTrigIvs_r15_c2))
/-- Certified suffix probability lower bounds for `r = 15`. -/
def solTailLbs_r15 : List (ℤ) := [999998830,999998830,999998828,999998828,999998828,999998826,
  999998826,999998824,999998817,999998815,999998803,999998300,999979688,999445445,985953556]
/-- Stage specification for explicit `m = 1` conveyor at `r = 15`. -/
def solStage_r15 : PulseM1StageSpec := ⟨15, 28392477, 100000000,
    solToSwLPulses 15 65536 solExplicitPulses_r15⟩
/-- Chunk 0 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c0 : List (SolSparsePulse) := [⟨1,[19144,11206,8477,7071,6209,5631,5223,
  4928,4714,4560,4451,4378,4335,4315,4315],(-52)⟩, ⟨1,[17154,13136,9187,7262,6121,5374,4859,4500,
  4255,4101,4021,4006,4049,4147,4294],(-19)⟩, ⟨1,[14671,13534,11118,8509,6937,5898,5185,4691,4352,
  4130,4000,3944,3951,4015,4127],(-3)⟩, ⟨1,[12297,13694,11339,9739,7512,6238,5403,4815,4385,4071,
  3847,3700,3621,3603,3642],0⟩, ⟨1,[10337,13430,11612,10266,8316,6740,5674,4911,4344,3910,3571,3304,
  3097,2945,2844],(-2)⟩, ⟨1,[8830,12769,11856,10311,9068,7213,5992,5105,4416,3859,3400,3009,2668,
  2364,2086],0⟩, ⟨1,[7719,11833,12014,10456,9594,7798,6357,5360,4604,3992,3469,3005,2583,2192,1822],
  0⟩, ⟨1,[6880,10814,11982,10657,9532,8371,6789,5670,4845,4201,3672,3216,2808,2431,2078],0⟩, ⟨1,
  [6272,9820,11748,10823,9650,8862,7214,5977,5083,4393,3842,3394,3015,2679,2373],0⟩, ⟨1,[5788,8952,
  11293,10980,9739,8993,7665,6268,5276,4526,3930,3444,3035,2686,2376],0⟩, ⟨1,[5409,8216,10709,11027,
  9903,8933,8081,6605,5492,4663,4013,3479,3021,2627,2283],0⟩, ⟨1,[5099,7605,10051,10967,10022,9045,
  8383,6955,5741,4843,4143,3572,3089,2669,2294],0⟩]
/-- Chunk 1 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c1 : List (SolSparsePulse) := [⟨1,[4833,7116,9397,10753,10170,9111,8426,
  7315,5999,5029,4278,3665,3159,2724,2326],0⟩, ⟨1,[4618,6701,8782,10427,10246,9230,8371,7627,6269,
  5201,4389,3736,3201,2743,2341],0⟩, ⟨1,[4426,6356,8239,9994,10276,9329,8461,7842,6552,5390,4510,
  3820,3256,2768,2351],0⟩, ⟨1,[4244,6078,7770,9518,10200,9453,8526,7885,6835,5597,4653,3916,3310,
  2789,2339],0⟩, ⟨1,[4073,5815,7348,9038,10033,9546,8593,7825,7089,5819,4807,4020,3366,2816,2335],
  0⟩, ⟨1,[3920,5590,7019,8555,9788,9603,8695,7873,7268,6053,4965,4121,3424,2847,2347],0⟩, ⟨1,[3786,
  5407,6718,8128,9451,9631,8768,7947,7338,6279,5121,4212,3483,2882,2364],0⟩, ⟨1,[3668,5235,6452,
  7749,9088,9564,8889,7982,7300,6487,5286,4315,3549,2921,2370],0⟩, ⟨1,[3560,5058,6227,7389,8709,
  9441,8954,8073,7289,6653,5465,4437,3628,2955,2362],0⟩, ⟨1,[3455,4883,6012,7095,8322,9249,9012,
  8142,7361,6749,5655,4571,3715,2989,2366],0⟩, ⟨1,[3348,4724,5819,6839,7963,8994,9032,8216,7403,
  6760,5833,4706,3792,3027,2381],0⟩, ⟨1,[3237,4590,5663,6586,7636,8708,8991,8310,7434,6721,5985,
  4837,3863,3066,2390],0⟩]
/-- Chunk 2 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c2 : List (SolSparsePulse) := [⟨1,[3124,4474,5520,6379,7340,8395,8911,
  8366,7517,6735,6096,4968,3939,3104,2396],0⟩, ⟨1,[3010,4367,5367,6201,7063,8084,8765,8431,7571,
  6801,6153,5110,4030,3150,2406],0⟩, ⟨1,[2897,4260,5205,6019,6824,7781,8573,8456,7640,6833,6152,
  5248,4133,3212,2424],0⟩, ⟨1,[2786,4145,5051,5849,6610,7480,8355,8437,7721,6860,6124,5365,4244,
  3278,2441],0⟩, ⟨1,[2678,4016,4919,5711,6409,7217,8094,8401,7770,6926,6132,5451,4347,3328,2454],0⟩,
  ⟨1,[2576,3874,4809,5591,6237,6982,7828,8303,7838,6972,6187,5496,4442,3374,2467],0⟩, ⟨1,[2478,3722,
  4711,5462,6080,6744,7576,8155,7882,7024,6222,5500,4538,3429,2484],0⟩, ⟨1,[2385,3565,4612,5316,
  5925,6543,7317,7992,7881,7109,6240,5482,4631,3496,2504],0⟩, ⟨1,[2299,3410,4505,5168,5774,6374,
  7063,7797,7869,7155,6289,5476,4703,3565,2526],0⟩, ⟨1,[2220,3260,4385,5035,5646,6203,6846,7569,
  7827,7209,6342,5509,4750,3635,2552],0⟩, ⟨1,[2143,3114,4249,4924,5540,6043,6648,7345,7731,7270,
  6369,5552,4770,3701,2576],0⟩, ⟨1,[2076,2979,4098,4833,5432,5902,6441,7129,7609,7299,6438,5570,
  4764,3759,2593],0⟩]
/-- Chunk 3 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c3 : List (SolSparsePulse) := [⟨1,[2004,2848,3934,4747,5308,5769,6262,
  6906,7468,7305,6506,5593,4753,3812,2609],0⟩, ⟨1,[1940,2727,3762,4654,5171,5635,6118,6688,7297,
  7299,6545,5645,4758,3858,2632],0⟩, ⟨1,[1874,2612,3590,4547,5037,5510,5968,6493,7106,7261,6600,
  5687,4787,3889,2659],0⟩, ⟨1,[1806,2502,3423,4423,4920,5407,5818,6322,6912,7189,6653,5711,4822,
  3904,2684],0⟩, ⟨1,[1742,2399,3263,4284,4824,5317,5690,6148,6721,7093,6685,5772,4838,3905,2705],0⟩,
  ⟨1,[1686,2305,3114,4131,4743,5218,5575,5977,6530,6974,6702,5830,4853,3900,2724],0⟩, ⟨1,[1638,2220,
  2977,3968,4666,5099,5460,5840,6341,6833,6708,5868,4896,3902,2740],0⟩, ⟨1,[1593,2141,2847,3799,
  4583,4971,5340,5713,6160,6678,6688,5921,4941,3918,2754],0⟩, ⟨1,[1546,2061,2722,3623,4482,4847,
  5230,5576,5994,6512,6645,5973,4961,3946,2765],0⟩, ⟨1,[1498,1984,2603,3448,4360,4740,5142,5450,
  5849,6338,6578,6014,5001,3971,2771],0⟩, ⟨1,[1462,1918,2496,3283,4221,4652,5062,5344,5700,6170,
  6490,6042,5058,3981,2774],0⟩, ⟨1,[1452,1872,2406,3133,4070,4578,4969,5245,5552,6004,6382,6065,
  5095,3999,2778],0⟩]
/-- Chunk 4 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c4 : List (SolSparsePulse) := [⟨1,[1470,1848,2335,3003,3915,4510,4856,
  5141,5433,5843,6255,6073,5140,4038,2785],0⟩, ⟨1,[1481,1824,2269,2882,3755,4436,4730,5031,5325,
  5687,6121,6055,5194,4073,2798],0⟩, ⟨1,[1409,1757,2188,2765,3593,4352,4609,4927,5204,5538,5978,
  6024,5238,4090,2816],0⟩, ⟨1,[1274,1664,2107,2664,3442,4256,4509,4844,5089,5408,5824,5975,5282,
  4124,2834],0⟩, ⟨1,[1191,1576,2011,2545,3277,4130,4428,4772,4993,5283,5677,5906,5318,4173,2847],0⟩,
  ⟨1,[1142,1503,1922,2433,3119,3987,4363,4688,4902,5148,5531,5821,5348,4205,2857],0⟩, ⟨1,[1110,1438,
  1840,2330,2972,3834,4306,4581,4804,5031,5384,5718,5371,4245,2878],0⟩, ⟨1,[1082,1378,1767,2241,
  2846,3682,4252,4458,4698,4936,5247,5603,5374,4300,2907],0⟩, ⟨1,[1050,1320,1698,2159,2733,3533,
  4191,4337,4596,4835,5113,5484,5363,4344,2929],0⟩, ⟨1,[1025,1274,1633,2074,2620,3380,4113,4235,
  4509,4723,4986,5355,5343,4387,2947],0⟩, ⟨1,[1004,1234,1569,1987,2507,3225,4012,4159,4437,4625,
  4874,5220,5306,4435,2976],0⟩, ⟨1,[985,1199,1508,1903,2400,3077,3894,4107,4362,4539,4762,5090,5250,
  4479,3014],0⟩]
/-- Chunk 5 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c5 : List (SolSparsePulse) := [⟨1,[966,1164,1448,1823,2303,2942,3765,4073,
  4267,4447,4643,4963,5181,4517,3045],0⟩, ⟨1,[952,1135,1395,1750,2212,2818,3630,4048,4154,4343,4537,
  4835,5101,4549,3078],0⟩, ⟨1,[941,1109,1348,1680,2119,2691,3480,4015,4039,4238,4446,4711,5009,4573,
  3123],0⟩, ⟨1,[930,1084,1304,1612,2024,2565,3324,3964,3941,4144,4349,4592,4907,4588,3167],0⟩, ⟨1,
  [919,1061,1263,1547,1934,2446,3170,3894,3873,4061,4245,4473,4799,4594,3210],0⟩, ⟨1,[905,1036,1222,
  1485,1848,2335,3025,3808,3840,3984,4147,4362,4686,4588,3257],0⟩, ⟨1,[885,1008,1181,1425,1765,2226,
  2879,3695,3829,3899,4054,4261,4569,4570,3306],0⟩, ⟨1,[864,979,1141,1369,1686,2119,2732,3558,3825,
  3806,3954,4157,4453,4539,3360],0⟩, ⟨1,[840,949,1100,1315,1611,2016,2594,3412,3824,3719,3845,4048,
  4338,4494,3415],0⟩, ⟨1,[813,918,1061,1263,1539,1921,2466,3265,3816,3657,3743,3942,4224,4440,3466],
  0⟩, ⟨1,[788,890,1025,1216,1476,1834,2342,3103,3771,3621,3651,3839,4108,4375,3516],0⟩, ⟨1,[756,856,
  985,1166,1413,1748,2219,2932,3689,3609,3563,3737,3995,4300,3567],0⟩]
/-- Chunk 6 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c6 : List (SolSparsePulse) := [⟨1,[726,823,948,1120,1353,1669,2107,2772,
  3588,3621,3476,3629,3886,4215,3617],0⟩, ⟨1,[704,799,918,1080,1302,1600,2007,2621,3459,3634,3408,
  3505,3771,4125,3663],0⟩, ⟨1,[676,768,882,1036,1246,1529,1909,2473,3305,3632,3384,3373,3653,4029,
  3704],0⟩, ⟨1,[657,745,853,999,1198,1465,1823,2342,3146,3613,3411,3262,3538,3927,3741],0⟩, ⟨1,[646,
  728,830,967,1154,1407,1745,2224,2980,3555,3459,3178,3407,3821,3774],0⟩, ⟨1,[623,700,795,924,1100,
  1340,1661,2108,2812,3469,3501,3098,3258,3710,3800],0⟩, ⟨1,[623,692,780,898,1062,1287,1591,2010,
  2660,3360,3496,3029,3117,3587,3823],0⟩, ⟨1,[633,693,772,879,1030,1240,1526,1921,2521,3235,3437,
  3038,2950,3456,3841],0⟩, ⟨1,[643,694,763,859,998,1192,1462,1835,2394,3108,3337,3172,2758,3310,
  3851],0⟩, ⟨1,[658,700,760,845,970,1150,1402,1754,2277,2983,3221,3370,2659,3120,3863],0⟩, ⟨1,[673,
  707,757,831,943,1108,1344,1676,2165,2865,3116,3444,2600,2894,3870],0⟩, ⟨1,[688,713,754,818,918,
  1068,1288,1599,2057,2744,3047,3289,2650,2575,3880],0⟩]
/-- Chunk 7 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c7 : List (SolSparsePulse) := [⟨1,[717,734,766,819,906,1041,1243,1534,
  1960,2623,3014,3014,3253,2060,3898],(-13)⟩, ⟨1,[745,754,777,819,894,1014,1199,1469,1866,2498,2977,
  2881,3193,2213,3074],11709⟩, ⟨1,[777,778,792,825,887,993,1160,1410,1779,2375,2925,2834,2796,2628,
  2331 ],16180⟩, ⟨1,[822,816,822,845,895,986,1136,1364,1705,2260,2860,2798,2719,2561,2278 ],16253⟩,
  ⟨1,[840,829,828,843,883,962,1097,1306,1624,2140,2774,2758,2697,2522,2219 ],16332⟩, ⟨1,[851,834,
  828,836,868,936,1057,1249,1545,2025,2676,2717,2664,2466,2166 ],16404⟩, ⟨1,[860,838,826,828,852,
  911,1018,1194,1469,1913,2566,2675,2621,2413,2111 ],16482⟩, ⟨1,[898,871,854,850,866,914,1008,1166,
  1418,1824,2461,2641,2576,2369,2056 ],16545⟩, ⟨1,[908,877,855,846,855,895,978,1122,1354,1729,2344,
  2605,2531,2329,2005],16593⟩, ⟨1,[914,879,853,840,844,876,948,1079,1295,1640,2227,2569,2488,2290,
  1957],16633⟩, ⟨1,[951,913,884,866,864,888,951,1068,1265,1581,2131,2540,2446,2251,1909],16671⟩, ⟨1,
  [924,884,853,832,828,848,904,1014,1199,1496,2016,2493,2399,2212,1861],16708⟩]
/-- Chunk 8 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c8 : List (SolSparsePulse) := [⟨1,[892,851,819,797,791,808,860,963,1138,
  1419,1908,2441,2346,2173,1815],16736⟩, ⟨1,[870,828,795,772,765,779,826,922,1086,1352,1811,2381,
  2282,2135,1772],16750⟩, ⟨1,[875,834,800,776,766,776,817,904,1056,1304,1729,2318,2213,2100,1733],
  16750⟩, ⟨1,[862,821,788,763,752,760,796,875,1016,1250,1645,2242,2142,2065,1697],16738⟩, ⟨1,[830,
  791,759,736,725,731,763,836,969,1190,1560,2157,2078,2030,1663],16722⟩, ⟨1,[779,742,713,691,680,
  685,715,782,907,1116,1466,2057,2025,1990,1632],16698⟩, ⟨1,[755,721,694,674,663,667,692,752,865,
  1059,1385,1959,1995,1945,1606],16659⟩, ⟨1,[705,676,652,634,624,627,650,703,806,985,1289,1843,1977,
  1894,1585],16601⟩, ⟨1,[620,594,573,558,551,554,575,623,716,880,1163,1696,1952,1834,1568],16526⟩,
  ⟨1,[628,607,589,576,569,571,586,625,701,839,1086,1573,1931,1763,1557],16437⟩, ⟨1,[618,600,586,576,
  570,571,583,613,675,788,996,1425,1867,1665,1554],16332⟩, ⟨1,[583,570,560,553,550,552,563,587,637,
  727,895,1256,1738,1496,1559],16201⟩]
/-- Chunk 9 of `solExplicitPulses_r16`. -/
def solExplicitPulses_r16_c9 : List (SolSparsePulse) := [⟨1,[502,493,486,483,483,487,498,520,560,
  630,760,1045,1507,1197,1577],16038⟩, ⟨1,[435,429,427,427,430,437,449,469,501,555,648,847,1212,802,
  1602],15857⟩, ⟨1,[282,280,281,283,289,299,313,334,366,413,488,625,875,539,1632],15650⟩, ⟨1,[0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0],(-96)⟩]
/-- Explicit rational pulses for `r = 16` (`L = 16`). -/
def solExplicitPulses_r16 : List (SolSparsePulse) := List.append ( List.append ( List.append (
  solExplicitPulses_r16_c0) ( solExplicitPulses_r16_c1)) ( List.append ( solExplicitPulses_r16_c2) (
  List.append ( solExplicitPulses_r16_c3) ( solExplicitPulses_r16_c4)))) ( List.append ( List.append
  ( solExplicitPulses_r16_c5) ( solExplicitPulses_r16_c6)) ( List.append ( solExplicitPulses_r16_c7)
  ( List.append ( solExplicitPulses_r16_c8) ( solExplicitPulses_r16_c9))))
/-- Chunk 0 of `solRatios_r16`. -/
def solRatios_r16_c0 : List (IvInt) := [(968245835,968245838),(935414345,935414348),(901387817,
  901387820),(866025402,866025405),(829156196,829156199),(790569414,790569417),(749999999,
  750000002),(707106780,707106783),(661437826,661437829),(612372434,612372437),(559016993,
  559016996),(499999999,500000002)]
/-- Chunk 1 of `solRatios_r16`. -/
def solRatios_r16_c1 : List (IvInt) := [(433012700,433012703),(353553389,353553392),(249999999,
  250000002)]
/-- Stratum angle-ratio intervals for `r = 16`. -/
def solRatios_r16 : List (IvInt) := List.append ( solRatios_r16_c0) ( solRatios_r16_c1)
/-- Chunk 0 of `solTrigIvs_r16`. -/
def solTrigIvs_r16_c0 : List (IvInt × IvInt) := [((955094644,955094645),(296300894,296300895)),
  ((957881353,957881355),(287164258,287164260)),((960670706,960670707),(277690103,277690105)),
  ((963462703,963462704),(267842525,267842527)),((966257346,966257347),(257578609,257578611)),
  ((969054637,969054638),(246846328,246846330))]
/-- Chunk 1 of `solTrigIvs_r16`. -/
def solTrigIvs_r16_c1 : List (IvInt × IvInt) := [((971854576,971854577),(235581581,235581582)),
  ((974657166,974657168),(223703836,223703838)),((977462409,977462410),(211109541,211109543)),
  ((980270304,980270306),(197661653,197661655)),((983080855,983080856),(183172135,183172137)),
  ((985894062,985894063),(167370536,167370538))]
/-- Chunk 2 of `solTrigIvs_r16`. -/
def solTrigIvs_r16_c2 : List (IvInt × IvInt) := [((988709928,988709929),(149842176,149842177)),
  ((991528453,991528454),(129889670,129889672)),((994349638,994349640),(106154582,106154584)),
  ((997173487,997173488),(75133453,75133455))]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 16`. -/
def solTrigIvs_r16 : List (IvInt × IvInt) := List.append ( solTrigIvs_r16_c0) ( List.append (
  solTrigIvs_r16_c1) ( solTrigIvs_r16_c2))
/-- Certified suffix probability lower bounds for `r = 16`. -/
def solTailLbs_r16 : List (ℤ) := [999998735,999998734,999998734,999998734,999998733,999998733,
  999998730,999998729,999998725,999998718,999998708,999998704,999997953,999974888,999349558,
  984719531]
/-- Stage specification for explicit `m = 1` conveyor at `r = 16`. -/
def solStage_r16 : PulseM1StageSpec := ⟨16, 30081729, 100000000,
    solToSwLPulses 16 65536 solExplicitPulses_r16⟩
private def _allExplicitOk : Bool :=
  (_s2vCheckExplicitStage 3 3 8926806 100000000 65536 solRatios_r3 solTrigIvs_r3
    solExplicitPulses_r3 0 solTailLbs_r3 51119424699 solM1VTable16 &&
  (_s2vCheckExplicitStage 4 4 10079629 100000000 65536 solRatios_r4 solTrigIvs_r4
    solExplicitPulses_r4 12 solTailLbs_r4 62428864409 solM1VTable16 &&
  (_s2vCheckExplicitStage 5 5 12293912 100000000 65536 solRatios_r5 solTrigIvs_r5
    solExplicitPulses_r5 5 solTailLbs_r5 65536843640 solM1VTable16 &&
  (_s2vCheckExplicitStage 6 6 14108483 100000000 65536 solRatios_r6 solTrigIvs_r6
    solExplicitPulses_r6 0 solTailLbs_r6 69770888130 solM1VTable16 &&
  (_s2vCheckExplicitStage 7 7 15684139 100000000 65536 solRatios_r7 solTrigIvs_r7
    solExplicitPulses_r7 0 solTailLbs_r7 74261320493 solM1VTable16 &&
  (_s2vCheckExplicitStage 8 8 17217698 100000000 65536 solRatios_r8 solTrigIvs_r8
    solExplicitPulses_r8 0 solTailLbs_r8 78202195664 solM1VTable16 &&
  (_s2vCheckExplicitStage 9 9 18720391 100000000 65536 solRatios_r9 solTrigIvs_r9
    solExplicitPulses_r9 0 solTailLbs_r9 81693628260 solM1VTable16 &&
  (_s2vCheckExplicitStage 10 10 20292299 100000000 65536 solRatios_r10 solTrigIvs_r10
    solExplicitPulses_r10 0 solTailLbs_r10 84431962291 solM1VTable16 &&
  (_s2vCheckExplicitStage 11 11 21978141 100000000 65536 solRatios_r11 solTrigIvs_r11
    solExplicitPulses_r11 0 solTailLbs_r11 86378585066 solM1VTable16 &&
  (_s2vCheckExplicitStage 12 12 23564263 100000000 65536 solRatios_r12 solTrigIvs_r12
    solExplicitPulses_r12 0 solTailLbs_r12 88448720894 solM1VTable16 &&
  (_s2vCheckExplicitStage 13 13 25215267 100000000 65536 solRatios_r13 solTrigIvs_r13
    solExplicitPulses_r13 0 solTailLbs_r13 90062410326 solM1VTable16 &&
  (_s2vCheckExplicitStage 14 14 26834915 100000000 65536 solRatios_r14 solTrigIvs_r14
    solExplicitPulses_r14 0 solTailLbs_r14 91608686352 solM1VTable16 &&
  (_s2vCheckExplicitStage 15 15 28392477 100000000 65536 solRatios_r15 solTrigIvs_r15
    solExplicitPulses_r15 0 solTailLbs_r15 93198667791 solM1VTable16 &&
  _s2vCheckExplicitStage 16 16 30081729 100000000 65536 solRatios_r16 solTrigIvs_r16
    solExplicitPulses_r16 0 solTailLbs_r16 94248272251 solM1VTable16 )))))))))))))
private theorem _cExpAll : _allExplicitOk = true := by decide +kernel
theorem cert_solExplicit_r3 : checkPulseExplicitStageTable 3 3 8926806 100000000 65536
    solRatios_r3 solTrigIvs_r3 solExplicitPulses_r3 0 solTailLbs_r3 51119424699 solM1VTable16 = true
    := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL _cExpAll
theorem cert_solExplicit_r4 : checkPulseExplicitStageTable 4 4 10079629 100000000 65536
    solRatios_r4 solTrigIvs_r4 solExplicitPulses_r4 12 solTailLbs_r4 62428864409 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR _cExpAll)
theorem cert_solExplicit_r5 : checkPulseExplicitStageTable 5 5 12293912 100000000 65536
    solRatios_r5 solTrigIvs_r5 solExplicitPulses_r5 5 solTailLbs_r5 65536843640 solM1VTable16 = true
    := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR _cExpAll))
theorem cert_solExplicit_r6 : checkPulseExplicitStageTable 6 6 14108483 100000000 65536
    solRatios_r6 solTrigIvs_r6 solExplicitPulses_r6 0 solTailLbs_r6 69770888130 solM1VTable16 = true
    := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR _cExpAll)))
theorem cert_solExplicit_r7 : checkPulseExplicitStageTable 7 7 15684139 100000000 65536
    solRatios_r7 solTrigIvs_r7 solExplicitPulses_r7 0 solTailLbs_r7 74261320493 solM1VTable16 = true
    := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR _cExpAll))))
theorem cert_solExplicit_r8 : checkPulseExplicitStageTable 8 8 17217698 100000000 65536
    solRatios_r8 solTrigIvs_r8 solExplicitPulses_r8 0 solTailLbs_r8 78202195664 solM1VTable16 = true
    := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR _cExpAll)))))
theorem cert_solExplicit_r9 : checkPulseExplicitStageTable 9 9 18720391 100000000 65536
    solRatios_r9 solTrigIvs_r9 solExplicitPulses_r9 0 solTailLbs_r9 81693628260 solM1VTable16 = true
    := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR _cExpAll))))))
theorem cert_solExplicit_r10 : checkPulseExplicitStageTable 10 10 20292299 100000000 65536
    solRatios_r10 solTrigIvs_r10 solExplicitPulses_r10 0 solTailLbs_r10 84431962291 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR (_bR _cExpAll)))))))
theorem cert_solExplicit_r11 : checkPulseExplicitStageTable 11 11 21978141 100000000 65536
    solRatios_r11 solTrigIvs_r11 solExplicitPulses_r11 0 solTailLbs_r11 86378585066 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR
    _cExpAll))))))))
theorem cert_solExplicit_r12 : checkPulseExplicitStageTable 12 12 23564263 100000000 65536
    solRatios_r12 solTrigIvs_r12 solExplicitPulses_r12 0 solTailLbs_r12 88448720894 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR
    _cExpAll)))))))))
theorem cert_solExplicit_r13 : checkPulseExplicitStageTable 13 13 25215267 100000000 65536
    solRatios_r13 solTrigIvs_r13 solExplicitPulses_r13 0 solTailLbs_r13 90062410326 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR
    _cExpAll))))))))))
theorem cert_solExplicit_r14 : checkPulseExplicitStageTable 14 14 26834915 100000000 65536
    solRatios_r14 solTrigIvs_r14 solExplicitPulses_r14 0 solTailLbs_r14 91608686352 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR
    _cExpAll)))))))))))
theorem cert_solExplicit_r15 : checkPulseExplicitStageTable 15 15 28392477 100000000 65536
    solRatios_r15 solTrigIvs_r15 solExplicitPulses_r15 0 solTailLbs_r15 93198667791 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact _bL (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR
    (_bR _cExpAll))))))))))))
theorem cert_solExplicit_r16 : checkPulseExplicitStageTable 16 16 30081729 100000000 65536
    solRatios_r16 solTrigIvs_r16 solExplicitPulses_r16 0 solTailLbs_r16 94248272251 solM1VTable16 =
    true := by
  rw [← _s2vCheckExplicitStage_eq]; exact (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR (_bR
    (_bR (_bR _cExpAll)))))))))))))
/-- Chunk 0 of `solWkb_rBulkQ_r32`. -/
def solWkb_rBulkQ_r32_c0 : List (ℤ) := [181,11575,38863,66394,78122,78746,79937,81681,83260,84238,
  85046,85989,86991,87975,89078,90148,90833,91494,92319,93191]
/-- Chunk 1 of `solWkb_rBulkQ_r32`. -/
def solWkb_rBulkQ_r32_c1 : List (ℤ) := [93073,90648,87989,85497,82060,81101,82767,82083,77683,80012,
  99585,111208,87371,91671,126332,92682,112322,100312,101464,102757]
/-- Chunk 2 of `solWkb_rBulkQ_r32`. -/
def solWkb_rBulkQ_r32_c2 : List (ℤ) := [101465,99613,97972,96638,95517,94501,93532,92593,91685,
  90810,89965,89144,88338,87541,86749,85964,85185,84416,83659,82917]
/-- Chunk 3 of `solWkb_rBulkQ_r32`. -/
def solWkb_rBulkQ_r32_c3 : List (ℤ) := [82188,69540,40381,11724,0]
/-- WKB bulk profile table for `r = 32`. -/
def solWkb_rBulkQ_r32 : List (ℤ) := List.append ( List.append ( solWkb_rBulkQ_r32_c0) (
  solWkb_rBulkQ_r32_c1)) ( List.append ( solWkb_rBulkQ_r32_c2) ( solWkb_rBulkQ_r32_c3))
/-- Chunk 0 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c0 : List (ℤ) := [79905,75740,44148,29982,17651,12955,9442,6489,4068,2657,
  1554,623,1609,47095,78261,61362,20793,0,(-19143),15326]
/-- Chunk 1 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c1 : List (ℤ) := [34905,28883,22483,16734,11488,6468,2236,(-423),(-2602),
  (-4467),(-5877),(-4787),40914,56890,19184,0,(-22806),(-8751),3632,19460]
/-- Chunk 2 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c2 : List (ℤ) := [22194,20143,16643,12685,9050,5963,2974,75,(-2243),(-3902),
  (-2840),34387,19923,0,(-31576),(-11964),(-4825),5062,13670,18791]
/-- Chunk 3 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c3 : List (ℤ) := [18529,15860,13144,10466,7706,4881,2426,444,(-1304),(-155),
  12709,0,(-25299),(-22770),(-13850),(-4188),4919,10155,14724,15233]
/-- Chunk 4 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c4 : List (ℤ) := [13865,12147,10389,8465,6438,4390,2331,193,437,0,(-38236),
  (-20827),(-17139),(-11526),(-3481),4683,8132,12601,13961,13502]
/-- Chunk 5 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c5 : List (ℤ) := [12679,11507,9956,8062,6003,3085,539,0,(-39273),(-20664),
  (-17515),(-14363),(-8792),(-3047),3653,7063,10959,12728,12556,11652]
/-- Chunk 6 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c6 : List (ℤ) := [10567,9269,7853,5133,1374,0,(-33439),(-27046),(-17322),
  (-17447),(-11798),(-6955),(-2060),3311,6656,9417,10883,10848,10459,9910]
/-- Chunk 7 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c7 : List (ℤ) := [9213,6738,2041,0,(-31033),(-30648),(-23272),(-14173),
  (-15075),(-10064),(-5621),(-1134),3599,5529,8264,9950,10421,10474,10278,7838]
/-- Chunk 8 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c8 : List (ℤ) := [2479,0,(-32234),(-32180),(-27042),(-17765),(-13964),
  (-13537),(-8489),(-5548),(-196),3659,5727,7946,9369,10033,10099,7807,2536,0]
/-- Chunk 9 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c9 : List (ℤ) := [(-33981),(-31104),(-26939),(-22327),(-15138),(-12594),
  (-11107),(-7636),(-4451),88,3774,5295,6941,8477,8959,7178,2450,0,(-33996),(-29261)]
/-- Chunk 10 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c10 : List (ℤ) := [(-24878),(-22521),(-18826),(-12620),(-11214),(-9317),
  (-6332),(-4633),342,2823,5084,6144,7499,6588,2397,0,(-33196),(-28084),(-24104),(-21579)]
/-- Chunk 11 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c11 : List (ℤ) := [(-20362),(-16491),(-11194),(-10072),(-8670),(-7075),
  (-4584),539,2906,4499,5803,5849,2246,2,(-32550),(-28042),(-24740),(-21752),(-19387),(-18895)]
/-- Chunk 12 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c12 : List (ℤ) := [(-14130),(-10352),(-9555),(-7930),(-6325),(-3802),(-548),
  3063,4761,4741,2015,39,(-32406),(-28811),(-25647),(-22946),(-18745),(-18381),(-17395),(-12647)]
/-- Chunk 13 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c13 : List (ℤ) := [(-9214),(-8434),(-7214),(-7033),(-4207),(-345),3596,4299,
  2340,204,(-20622),(-23463),(-20911),(-18882),(-15380),(-13258),(-13629),(-12618),(-8759),(-6854)]
/-- Chunk 14 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c14 : List (ℤ) := [(-6604),(-6321),(-6535),(-4392),42,4282,3276,695,6710,
  (-6300),(-7223),(-6671),(-6080),(-4034),(-2998),(-4239),(-3989),(-2852),(-2398),(-2607)]
/-- Chunk 15 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c15 : List (ℤ) := [(-4498),(-5279),(-3712),330,3346,2250,1,(-1),(-17),(-83),
  (-447),26,506,157,(-198),8,(-205),(-207),(-586),(-2085)]
/-- Chunk 16 of `solWkb_uLnchQ_r32`. -/
def solWkb_uLnchQ_r32_c16 : List (ℤ) := [(-2964),(-1780),1712,1782]
/-- WKB launch correction table for `r = 32`. -/
def solWkb_uLnchQ_r32 : List (ℤ) := List.append ( List.append ( List.append ( List.append (
  solWkb_uLnchQ_r32_c0) ( solWkb_uLnchQ_r32_c1)) ( List.append ( solWkb_uLnchQ_r32_c2) (
  solWkb_uLnchQ_r32_c3))) ( List.append ( List.append ( solWkb_uLnchQ_r32_c4) (
  solWkb_uLnchQ_r32_c5)) ( List.append ( solWkb_uLnchQ_r32_c6) ( solWkb_uLnchQ_r32_c7)))) (
  List.append ( List.append ( List.append ( solWkb_uLnchQ_r32_c8) ( solWkb_uLnchQ_r32_c9)) (
  List.append ( solWkb_uLnchQ_r32_c10) ( solWkb_uLnchQ_r32_c11))) ( List.append ( List.append (
  solWkb_uLnchQ_r32_c12) ( solWkb_uLnchQ_r32_c13)) ( List.append ( solWkb_uLnchQ_r32_c14) (
  List.append ( solWkb_uLnchQ_r32_c15) ( solWkb_uLnchQ_r32_c16)))))
/-- Chunk 0 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c0 : List (ℤ) := [(-82033),(-82398),(-80478),(-78225),(-76117),(-74056),
  (-38186),4822,5424,5418,5415,5413,5425,5418,5419,4347,1513,5,36166,14009]
/-- Chunk 1 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c1 : List (ℤ) := [861,(-5262),(-11315),(-8249),(-3571),36735,81056,80205,
  78015,75211,72463,69588,66666,50995,16816,27,26337,12711,5933,5613]
/-- Chunk 2 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c2 : List (ℤ) := [1614,594,476,2113,39238,81109,81630,82103,82171,81667,80816,
  63883,21690,12,17915,11138,8773,4617,1683,823]
/-- Chunk 3 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c3 : List (ℤ) := [3,589,2145,40250,81116,81368,80953,80595,80802,65051,22577,
  44,10422,7178,11906,5516,5199,4455,3514,2236]
/-- Chunk 4 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c4 : List (ℤ) := [2287,3377,41176,80515,79797,78948,78918,63932,22412,54,3444,
  3766,12862,5018,5008,5512,5466,5595,4149,3797]
/-- Chunk 5 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c5 : List (ℤ) := [4072,42042,80019,79078,78210,62943,22059,72,(-5981),(-562),
  8416,8285,7260,5424,5045,7559,7249,5738,5319,5019]
/-- Chunk 6 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c6 : List (ℤ) := [42903,79820,78665,62534,21757,28,(-10304),(-6073),1520,7088,
  6896,5325,3936,4636,8023,7651,6975,6365,5632,43956]
/-- Chunk 7 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c7 : List (ℤ) := [80009,63054,21872,67,(-2260),(-7180),(-5186),780,3950,6618,
  4403,2540,5156,7799,8245,7567,7471,6539,45422,64211]
/-- Chunk 8 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c8 : List (ℤ) := [22225,177,25775,907,(-3455),(-3570),(-1039),4715,4547,3616,
  2794,4967,7347,7484,7967,8073,6947,37041,22554,190]
/-- Chunk 9 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c9 : List (ℤ) := [2496,8526,3961,(-100),(-1562),765,4135,4176,3061,1165,3824,
  6389,7298,8059,8578,5449,13287,158,(-18799),(-4181)]
/-- Chunk 10 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c10 : List (ℤ) := [6223,4266,2029,664,3828,2581,1877,(-282),1288,3846,5989,
  6562,7852,5911,2031,132,(-21436),(-16921),(-4055),3778]
/-- Chunk 11 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c11 : List (ℤ) := [3346,1960,2180,3261,1742,2117,1574,1302,3197,4543,5090,
  4500,1779,77,(-16907),(-16120),(-12567),(-2825),2710,2428]
/-- Chunk 12 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c12 : List (ℤ) := [1460,1925,2843,2344,1926,1796,1873,2239,3885,2727,1199,
  (-51),(-17029),(-16502),(-16801),(-10770),(-2271),1996,2010,925]
/-- Chunk 13 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c13 : List (ℤ) := [860,1578,1141,2154,2030,1754,2293,3585,1234,145,(-14611),
  (-14618),(-14498),(-10948),(-7003),(-1470),1551,1539,617,515]
/-- Chunk 14 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c14 : List (ℤ) := [872,829,1615,1525,1536,3431,3614,402,(-5425),(-5108),
  (-4753),(-3985),(-3251),(-2176),(-291),563,416,(-39),406,492]
/-- Chunk 15 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c15 : List (ℤ) := [37,236,1092,750,2870,1400,0,0,0,0,2,6,46,102,80,(-147),
  (-97),415,31,(-161)]
/-- Chunk 16 of `solWkb_uLandQ_r32`. -/
def solWkb_uLandQ_r32_c16 : List (ℤ) := [(-296),(-192),(-862),991]
/-- WKB landing correction table for `r = 32`. -/
def solWkb_uLandQ_r32 : List (ℤ) := List.append ( List.append ( List.append ( List.append (
  solWkb_uLandQ_r32_c0) ( solWkb_uLandQ_r32_c1)) ( List.append ( solWkb_uLandQ_r32_c2) (
  solWkb_uLandQ_r32_c3))) ( List.append ( List.append ( solWkb_uLandQ_r32_c4) (
  solWkb_uLandQ_r32_c5)) ( List.append ( solWkb_uLandQ_r32_c6) ( solWkb_uLandQ_r32_c7)))) (
  List.append ( List.append ( List.append ( solWkb_uLandQ_r32_c8) ( solWkb_uLandQ_r32_c9)) (
  List.append ( solWkb_uLandQ_r32_c10) ( solWkb_uLandQ_r32_c11))) ( List.append ( List.append (
  solWkb_uLandQ_r32_c12) ( solWkb_uLandQ_r32_c13)) ( List.append ( solWkb_uLandQ_r32_c14) (
  List.append ( solWkb_uLandQ_r32_c15) ( solWkb_uLandQ_r32_c16)))))
/-- Chunk 0 of `solWkb_vDrainQ_r32`. -/
def solWkb_vDrainQ_r32_c0 : List (ℤ) := [35306,205886,283920,283214,280646,282936,286636,291781,
  300650,313943,331648,336518,290030,131502,(-43304),(-43681),11133,11655,(-9364),(-11918)]
/-- Chunk 1 of `solWkb_vDrainQ_r32`. -/
def solWkb_vDrainQ_r32_c1 : List (ℤ) := [(-1391),2307,194,0]
/-- WKB drain probe table for `r = 32`. -/
def solWkb_vDrainQ_r32 : List (ℤ) := List.append ( solWkb_vDrainQ_r32_c0) ( solWkb_vDrainQ_r32_c1)
/-- Compact pure-integer WKB spline schedule for `r = 32` (`L = 32`). -/
def solWkbSched_r32 : SolWkbSched where
  r := 32
  L := 32
  K := 260
  tauNum := 224053
  tauDen := 1000000
  uvDen := 100000
  vBulkQ := 955
  sOffQ := (-1728)
  accelQ := 121
  rBulkQ := solWkb_rBulkQ_r32
  uLnchQ := solWkb_uLnchQ_r32
  uLandQ := solWkb_uLandQ_r32
  vDrainQ := solWkb_vDrainQ_r32
/-- Chunk 0 of `solRatios_r32`. -/
def solRatios_r32_c0 : List (IvInt) := [(984250983,984250986),(968245835,968245838),(951971637,
  951971640),(935414345,935414348),(918558652,918558655),(901387817,901387820),(883883475,
  883883478),(866025402,866025405),(847791246,847791249),(829156196,829156199),(810092586,
  810092589),(790569414,790569417)]
/-- Chunk 1 of `solRatios_r32`. -/
def solRatios_r32_c1 : List (IvInt) := [(770551749,770551752),(749999999,750000002),(728868985,
  728868988),(707106780,707106783),(684653195,684653198),(661437826,661437829),(637377438,
  637377441),(612372434,612372437),(586301968,586301971),(559016993,559016996),(530330084,
  530330087),(499999999,500000002)]
/-- Chunk 2 of `solRatios_r32`. -/
def solRatios_r32_c2 : List (IvInt) := [(467707172,467707175),(433012700,433012703),(395284706,
  395284709),(353553389,353553392),(306186216,306186219),(249999999,250000002),(176776694,
  176776697)]
/-- Stratum angle-ratio intervals for WKB `r = 32`. -/
def solRatios_r32 : List (IvInt) := List.append ( solRatios_r32_c0) ( List.append (
  solRatios_r32_c1) ( solRatios_r32_c2))
/-- Chunk 0 of `solTrigIvs_r32`. -/
def solTrigIvs_r32_c0 : List (IvInt × IvInt) := [((975004951,975004952),(222183132,222183133)),
  ((975782878,975782879),(218741339,218741341)),((976561009,976561010),(215240781,215240783)),
  ((977339344,977339345),(211678541,211678543)),((978117884,978117885),(208051446,208051448)),
  ((978896627,978896628),(204356042,204356044))]
/-- Chunk 1 of `solTrigIvs_r32`. -/
def solTrigIvs_r32_c1 : List (IvInt × IvInt) := [((979675575,979675576),(200588550,200588552)),
  ((980454727,980454728),(196744827,196744829)),((981234083,981234084),(192820312,192820314)),
  ((982013644,982013645),(188809963,188809965)),((982793409,982793410),(184708188,184708190)),
  ((983573378,983573379),(180508750,180508752))]
/-- Chunk 2 of `solTrigIvs_r32`. -/
def solTrigIvs_r32_c2 : List (IvInt × IvInt) := [((984353551,984353553),(176204666,176204668)),
  ((985133930,985133931),(171788065,171788067)),((985914512,985914513),(167250032,167250034)),
  ((986695299,986695300),(162580395,162580397)),((987476291,987476292),(157767467,157767468)),
  ((988257487,988257488),(152797702,152797704))]
/-- Chunk 3 of `solTrigIvs_r32`. -/
def solTrigIvs_r32_c3 : List (IvInt × IvInt) := [((989038888,989038889),(147655264,147655265)),
  ((989820493,989820494),(142321431,142321433)),((990602303,990602304),(136773810,136773812)),
  ((991384318,991384319),(130985237,130985239)),((992166538,992166539),(124922217,124922219)),
  ((992948962,992948963),(118542641,118542643))]
/-- Chunk 4 of `solTrigIvs_r32`. -/
def solTrigIvs_r32_c4 : List (IvInt × IvInt) := [((993731591,993731592),(111792325,111792327)),
  ((994514425,994514426),(104599511,104599513)),((995297463,995297465),(96865670,96865671)),
  ((996080707,996080708),(88448990,88448991)),((996864156,996864157),(79131878,79131880)),
  ((997647809,997647810),(68548143,68548145))]
/-- Chunk 5 of `solTrigIvs_r32`. -/
def solTrigIvs_r32_c5 : List (IvInt × IvInt) := [((998431668,998431669),(55983964,55983965)),
  ((999215731,999215732),(39596993,39596995))]
/-- Stratum `(cosIv, sinIv)` intervals for WKB `r = 32`. -/
def solTrigIvs_r32 : List (IvInt × IvInt) := List.append ( List.append ( solTrigIvs_r32_c0) (
  List.append ( solTrigIvs_r32_c1) ( solTrigIvs_r32_c2))) ( List.append ( solTrigIvs_r32_c3) (
  List.append ( solTrigIvs_r32_c4) ( solTrigIvs_r32_c5)))
/-- Chunk 0 of `solTailLbs_r32`. -/
def solTailLbs_r32_c0 : List (ℤ) := [999981055,999958790,999944020,999936119,999929576,999876984,
  999823064,999799470,999788636,999728369,999615381,999582927,999558521,999404541,999380220,
  999379090,999302323,999302199,999216032,999195731]
/-- Chunk 1 of `solTailLbs_r32`. -/
def solTailLbs_r32_c1 : List (ℤ) := [999162565,999126398,999026543,999026039,998970333,998815970,
  998750776,997931644,997311994,996711943,979973077,813788293]
/-- Certified suffix probability lower bounds for WKB `r = 32`. -/
def solTailLbs_r32 : List (ℤ) := List.append ( solTailLbs_r32_c0) ( solTailLbs_r32_c1)
/-- Stage specification for WKB Multi-pulse conveyor at `r = 32`. -/
def solStage_r32 : PulseM1StageSpec := ⟨32, 224053, 1000000, solWkbToSwLPulses solWkbSched_r32⟩
/-- WKB `L2Ball` center checkpoint after pulse `260` at `r = 32`. -/
def solCkptEnd_r32 : List ℤ := List.append ( [1195271,2918910,(-3707379),504684,3809972,(-2088001),
  (-1881822),(-2496511),558048,6937933,2110781,(-4512211),(-5793108),1746819,4532437,3107816,
  (-1084440),(-6491015),(-4258442),6958871,8035114,207378,(-5693061),(-4250542),(-2517654),10113850,
  7189666,(-3482949),(-3491289),(-835441),(-657818),8653536] ) ( [1371924,(-349487),(-65510),
  (-6235172),(-6876690),(-4390056),(-1014384),5752336,276668,5172187,3068553,8511393,5235643,656752,
  269909,(-3564537),(-6557324),(-8357438),9193399,7166087,3720360,(-27776190),(-6900625),
  (-23337262),8661747,(-13986083),20110738,21701890,127545976,141257755,382402763,859191566] )
private def _ck32_52 : List ℤ := List.append [(-474692), (-14676805), (-18441065), 3680103,
  13953174, 11127782, (-3089988), (-5805922), (-1238542), 4500450, 18755711, 14453878, 55084501,
  61585052, 178715004, 176091521, 285180183, 207415742, 394674360, 320496640, 541343796, 331810540,
  305022272, 158994175, 138530555, 57522392, 40155574, 14272473, 9056569, 2786471, 1537299, 404402]
  [192945, 43454, 18088, 3493, 1267, 201, 56, 3]
private def _ck32_104 : List ℤ := List.append [(-2490842), (-3704162), 1578655, 4644179, (-2545213),
  (-4939413), (-744468), 11666442, 4215574, (-6103036), (-12313040), (-3328681), 12568622, 17070478,
  8909786, (-2296699), (-6643784), (-3810089), 6278521, 4769017, 4180741, 2012359, 3648316, 3593403,
  13598649, 10609926, 29135573, 19952038, 52799384, 34171261, 101147190, 89015874] [243391359,
  227881249, 356081806, 269233681, 462697419, 378580713, 414892387, 248704342, 228340716, 113176157,
  81192863, 35265014, 22092273, 8250605, 4331703, 1388022, 609895, 168594, 60991, 14420, 4264, 831,
  189, 18, 1, 0]
private def _ck32_156 : List ℤ := List.append [(-3096770), 455216, 1707712, (-3466152), (-1812981),
  4233924, 3600832, 2008133, (-4651313), (-5627260), 5234604, 5967166, 47813, (-5929164),
  (-2696127), 6045443, 8702462, (-2436619), (-12528140), (-8819567), 4291045, 10272308, 3650966,
  (-7593934), (-14275314), (-6226754), 1279519, 6007635, 4201173, 917546, 1046687, 1181404]
  [1771949, 2998397, 2310546, 1577937, 1544994, 3816228, 14709225, 16722044, 31876008, 34479190,
  69562412, 68086178, 133680308, 120837368, 277384262, 279158550, 425868710, 347794904, 486680986,
  348677892, 309458006, 169247819, 107223884, 46347979, 22257600, 7438497, 2700627, 700317, 189850,
  35276, 4710, 514]
private def _ck32_208 : List ℤ := List.append [(-1586229), 2726272, (-2134192), (-3073211), 3075661,
  3068547, 2305451, (-2111569), (-6959330), (-118522), 3708024, 3326556, 1207202, (-5929094),
  (-5293431), 1476859, 4859027, 4438374, 786271, (-8120466), (-7861685), 1673320, 5749561, 4173798,
  4508196, (-9638432), (-7252913), 1367962, 10568079, 9085669, 3658408, (-8469056) ] [(-5885260),
  (-1531647), 2893868, 3425287, 4491632, 4047408, (-4185568), (-9001517), (-5608086), (-14443884),
  (-7177136), (-15317904), 1891624, (-7588012), 4925139, (-6111403), 3558707, (-4546456), 15356749,
  13696890, 51452915, 57756162, 134997781, 155352876, 315919452, 363606395, 547319363, 462942357,
  395059782, 201281562, 80777601, 21605566]
private theorem _cWkb32_0 : solFastCheckWkbSliceS2V solWkbSched_r32 0 52 solTrigIvs_r32 [swScale, 0]
  1 0 0 _ck32_52 20 728 52000000000 = true := by decide +kernel
private theorem _cWkb32_1 : solFastCheckWkbSliceS2V solWkbSched_r32 52 52 solTrigIvs_r32 _ck32_52 20
  728 52000000000 _ck32_104 29 1686 104000000000 = true := by decide +kernel
private theorem _cWkb32_2 : solFastCheckWkbSliceS2V solWkbSched_r32 104 52 solTrigIvs_r32 _ck32_104
  29 1686 104000000000 _ck32_156 32 2716 156000000000 = true := by decide +kernel
private theorem _cWkb32_3 : solFastCheckWkbSliceS2V solWkbSched_r32 156 52 solTrigIvs_r32 _ck32_156
  32 2716 156000000000 _ck32_208 32 3683 207999967677 = true := by decide +kernel
private theorem _cWkb32_4 : solFastCheckWkbSliceS2V solWkbSched_r32 208 52 solTrigIvs_r32 _ck32_208
  32 3683 207999967677 solCkptEnd_r32 32 4522 258879974653 = true := by decide +kernel
/-- Chunk 0 of `solWkb_rBulkQ_r64`. -/
def solWkb_rBulkQ_r64_c0 : List (ℤ) := [56,11281,38839,67060,79430,80344,81400,82516,83490,84268,
  85030,85948,86985,88051,89060,89881,90984,92928,94178,93236]
/-- Chunk 1 of `solWkb_rBulkQ_r64`. -/
def solWkb_rBulkQ_r64_c1 : List (ℤ) := [91058,89480,88687,87800,86943,88780,95960,97988,84792,80662,
  100293,109442,88492,88453,123032,91499,110784,104907,105557,109581]
/-- Chunk 2 of `solWkb_rBulkQ_r64`. -/
def solWkb_rBulkQ_r64_c2 : List (ℤ) := [109595,106551,102462,98775,96178,94532,93408,92489,91631,
  90794,89969,89156,88351,87552,86757,85969,85188,84418,83660,82917]
/-- Chunk 3 of `solWkb_rBulkQ_r64`. -/
def solWkb_rBulkQ_r64_c3 : List (ℤ) := [82188,69540,40381,11724,0]
/-- WKB bulk profile table for `r = 64`. -/
def solWkb_rBulkQ_r64 : List (ℤ) := List.append ( List.append ( solWkb_rBulkQ_r64_c0) (
  solWkb_rBulkQ_r64_c1)) ( List.append ( solWkb_rBulkQ_r64_c2) ( solWkb_rBulkQ_r64_c3))
/-- Chunk 0 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c0 : List (ℤ) := [92317,73625,44209,29983,17651,12955,9442,6489,4068,2657,
  1554,623,1609,47095,78261,61362,20793,0,(-15109),23106]
/-- Chunk 1 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c1 : List (ℤ) := [35925,28937,22486,16734,11488,6468,2236,(-423),(-2602),
  (-4467),(-5877),(-4787),40914,56890,19184,0,(-21458),(-5144),7982,20536]
/-- Chunk 2 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c2 : List (ℤ) := [22260,20159,16643,12685,9050,5963,2974,75,(-2243),(-3902),
  (-2840),34387,19923,0,(-31710),(-9569),(-1308),6169,14264,18904]
/-- Chunk 3 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c3 : List (ℤ) := [18558,15861,13144,10466,7706,4881,2426,444,(-1304),(-155),
  12709,0,(-20416),(-23695),(-9092),(-604),5451,10425,14817,15267]
/-- Chunk 4 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c4 : List (ℤ) := [13867,12147,10389,8465,6438,4390,2331,193,437,0,(-35633),
  (-18986),(-14602),(-8053),(-372),4785,8436,12681,13961,13506]
/-- Chunk 5 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c5 : List (ℤ) := [12679,11507,9956,8062,6003,3085,539,0,(-37485),(-20925),
  (-17616),(-10050),(-6131),(-398),4299,6889,11057,12748,12560,11652]
/-- Chunk 6 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c6 : List (ℤ) := [10567,9269,7853,5133,1374,0,(-31685),(-27532),(-17538),
  (-18072),(-7115),(-4473),(-461),4474,5663,9395,10879,10856,10460,9910]
/-- Chunk 7 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c7 : List (ℤ) := [9213,6738,2041,0,(-29761),(-30027),(-24581),(-13994),
  (-15597),(-6054),(-3140),(-368),4231,4509,8034,9965,10430,10474,10278,7838]
/-- Chunk 8 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c8 : List (ℤ) := [2479,0,(-31843),(-30623),(-28022),(-18809),(-14120),
  (-13133),(-5115),(-2397),254,3394,4581,7440,9389,10040,10100,7807,2536,0]
/-- Chunk 9 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c9 : List (ℤ) := [(-33915),(-29632),(-27028),(-23682),(-15558),(-13106),
  (-9887),(-4500),(-1496),750,2729,3876,6532,8448,8967,7180,2450,0,(-34040),(-28471)]
/-- Chunk 10 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c10 : List (ℤ) := [(-23743),(-23854),(-19882),(-12470),(-12421),(-8359),
  (-3574),(-1049),954,2547,3552,5698,7470,6596,2399,0,(-33202),(-27853),(-22774),(-22014)]
/-- Chunk 11 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c11 : List (ℤ) := [(-21502),(-17300),(-11438),(-11902),(-6959),(-2999),(-919),
  812,2498,3250,5186,5794,2246,1,(-32528),(-28046),(-23879),(-21098),(-20589),(-19254)]
/-- Chunk 12 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c12 : List (ℤ) := [(-14673),(-10777),(-10424),(-4919),(-3169),(-1205),849,
  2259,3166,3988,1870,9,(-32390),(-28809),(-25288),(-22004),(-19031),(-19439),(-17261),(-12911)]
/-- Chunk 13 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c13 : List (ℤ) := [(-9213),(-8972),(-4612),(-3288),(-1807),458,1964,2195,1106,
  29,(-20619),(-23450),(-20837),(-18051),(-15094),(-14219),(-14363),(-12464),(-8726),(-7088)]
/-- Chunk 14 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c14 : List (ℤ) := [(-6555),(-3405),(-2888),(-2286),(-311),1713,524,(-111),
  6708,(-6288),(-7180),(-6259),(-5380),(-4546),(-4256),(-4340),(-3516),(-2695),(-2707),(-2021)]
/-- Chunk 15 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c15 : List (ℤ) := [(-1263),(-2225),(-1760),73,648,(-227),(-1),0,(-1),(-14),
  (-46),(-58),2,(-127),222,40,(-29),(-397),99,(-427)]
/-- Chunk 16 of `solWkb_uLnchQ_r64`. -/
def solWkb_uLnchQ_r64_c16 : List (ℤ) := [(-1096),(-665),(-244),(-65)]
/-- WKB launch correction table for `r = 64`. -/
def solWkb_uLnchQ_r64 : List (ℤ) := List.append ( List.append ( List.append ( List.append (
  solWkb_uLnchQ_r64_c0) ( solWkb_uLnchQ_r64_c1)) ( List.append ( solWkb_uLnchQ_r64_c2) (
  solWkb_uLnchQ_r64_c3))) ( List.append ( List.append ( solWkb_uLnchQ_r64_c4) (
  solWkb_uLnchQ_r64_c5)) ( List.append ( solWkb_uLnchQ_r64_c6) ( solWkb_uLnchQ_r64_c7)))) (
  List.append ( List.append ( List.append ( solWkb_uLnchQ_r64_c8) ( solWkb_uLnchQ_r64_c9)) (
  List.append ( solWkb_uLnchQ_r64_c10) ( solWkb_uLnchQ_r64_c11))) ( List.append ( List.append (
  solWkb_uLnchQ_r64_c12) ( solWkb_uLnchQ_r64_c13)) ( List.append ( solWkb_uLnchQ_r64_c14) (
  List.append ( solWkb_uLnchQ_r64_c15) ( solWkb_uLnchQ_r64_c16)))))
/-- Chunk 0 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c0 : List (ℤ) := [(-84217),(-82385),(-80379),(-78316),(-76204),(-74089),
  (-38248),4733,5422,5416,5415,5415,5413,5414,5415,4340,1500,0,30133,14290]
/-- Chunk 1 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c1 : List (ℤ) := [2404,(-6025),(-11742),(-8363),(-3731),36375,80974,80203,
  78010,75267,72427,69559,66644,50967,16761,2,23032,13708,9395,4022]
/-- Chunk 2 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c2 : List (ℤ) := [1582,600,453,1909,38938,81177,81579,82141,82260,81680,80806,
  63875,21658,10,16749,12914,11607,3744,3261,1504]
/-- Chunk 3 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c3 : List (ℤ) := [68,651,1883,40026,81226,81229,80984,80732,80841,64992,22461,
  15,11644,10962,11994,6694,8044,6471,3990,2691]
/-- Chunk 4 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c4 : List (ℤ) := [2258,3067,41066,80591,79652,79010,79138,63937,22274,8,10626,
  9802,11286,5978,6810,8126,7793,6581,4642,3870]
/-- Chunk 5 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c5 : List (ℤ) := [3789,42032,80037,78836,78439,63098,21949,(-1),7027,6156,
  5911,5448,6014,7576,9251,10096,8529,6564,5388,4809]
/-- Chunk 6 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c6 : List (ℤ) := [42947,79675,78580,62749,21741,23,4654,(-1944),(-2416),3440,
  3738,4532,6908,9650,10575,9307,7776,6527,5531,44028]
/-- Chunk 7 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c7 : List (ℤ) := [79846,63103,21763,51,4012,(-9146),(-6427),(-329),(-541),
  2152,4604,6795,9441,10311,9875,8314,7834,6505,45415,64219]
/-- Chunk 8 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c8 : List (ℤ) := [21953,55,21033,707,(-1931),(-2721),(-4971),(-1242),1481,
  2538,6060,8881,10069,8360,8987,8384,6933,37106,22303,39]
/-- Chunk 9 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c9 : List (ℤ) := [1342,9280,5062,627,(-3294),(-2995),(-1762),(-1511),2084,
  5460,8111,6887,8583,9103,8854,5573,13174,27,(-18421),(-4254)]
/-- Chunk 10 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c10 : List (ℤ) := [5750,5619,1609,(-141),(-1767),(-3093),(-1626),(-8),4533,
  4707,6942,7737,8584,6302,1975,22,(-21413),(-16762),(-3959),4309]
/-- Chunk 11 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c11 : List (ℤ) := [4130,2006,265,(-1390),(-1568),(-2747),1085,1486,4342,4352,
  5266,5315,1899,(-19),(-16911),(-16052),(-12251),(-2759),3269,3217]
/-- Chunk 12 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c12 : List (ℤ) := [1213,(-241),(-639),(-2299),(-460),(-1883),2200,1680,2114,
  3675,1556,(-87),(-17025),(-16501),(-16701),(-10635),(-2136),2429,2072,221]
/-- Chunk 13 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c13 : List (ℤ) := [(-913),(-1838),(-824),(-3116),107,588,1243,1804,792,(-118),
  (-14610),(-14618),(-14517),(-10921),(-6942),(-1735),1444,1365,288,(-951)]
/-- Chunk 14 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c14 : List (ℤ) := [(-779),(-2173),(-1581),(-528),1146,640,176,(-103),(-5425),
  (-5110),(-4771),(-4038),(-3315),(-2393),(-762),494,679,167,(-425),(-930)]
/-- Chunk 15 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c15 : List (ℤ) := [(-1913),(-1336),(-202),896,299,39,1,(-1),(-5),(-20),(-55),
  (-51),(-163),(-126),253,237,(-92),(-180),(-467),(-385)]
/-- Chunk 16 of `solWkb_uLandQ_r64`. -/
def solWkb_uLandQ_r64_c16 : List (ℤ) := [(-259),650,321,124]
/-- WKB landing correction table for `r = 64`. -/
def solWkb_uLandQ_r64 : List (ℤ) := List.append ( List.append ( List.append ( List.append (
  solWkb_uLandQ_r64_c0) ( solWkb_uLandQ_r64_c1)) ( List.append ( solWkb_uLandQ_r64_c2) (
  solWkb_uLandQ_r64_c3))) ( List.append ( List.append ( solWkb_uLandQ_r64_c4) (
  solWkb_uLandQ_r64_c5)) ( List.append ( solWkb_uLandQ_r64_c6) ( solWkb_uLandQ_r64_c7)))) (
  List.append ( List.append ( List.append ( solWkb_uLandQ_r64_c8) ( solWkb_uLandQ_r64_c9)) (
  List.append ( solWkb_uLandQ_r64_c10) ( solWkb_uLandQ_r64_c11))) ( List.append ( List.append (
  solWkb_uLandQ_r64_c12) ( solWkb_uLandQ_r64_c13)) ( List.append ( solWkb_uLandQ_r64_c14) (
  List.append ( solWkb_uLandQ_r64_c15) ( solWkb_uLandQ_r64_c16)))))
/-- Chunk 0 of `solWkb_vDrainQ_r64`. -/
def solWkb_vDrainQ_r64_c0 : List (ℤ) := [35172,205061,283342,283763,281935,284410,288225,294333,
  305390,320118,336923,339795,291115,131492,(-43314),(-43693),11134,11657,(-9364),(-11919)]
/-- Chunk 1 of `solWkb_vDrainQ_r64`. -/
def solWkb_vDrainQ_r64_c1 : List (ℤ) := [(-1391),2307,194,0]
/-- WKB drain probe table for `r = 64`. -/
def solWkb_vDrainQ_r64 : List (ℤ) := List.append ( solWkb_vDrainQ_r64_c0) ( solWkb_vDrainQ_r64_c1)
/-- Compact pure-integer WKB spline schedule for `r = 64` (`L = 64`). -/
def solWkbSched_r64 : SolWkbSched where
  r := 64
  L := 64
  K := 480
  tauNum := 249905
  tauDen := 1000000
  uvDen := 100000
  vBulkQ := 974
  sOffQ := (-1720)
  accelQ := 32
  rBulkQ := solWkb_rBulkQ_r64
  uLnchQ := solWkb_uLnchQ_r64
  uLandQ := solWkb_uLandQ_r64
  vDrainQ := solWkb_vDrainQ_r64
/-- Chunk 0 of `solRatios_r64`. -/
def solRatios_r64_c0 : List (IvInt) := [(992156740,992156743),(984250983,984250986),(976281208,
  976281211),(968245835,968245838),(960143217,960143220),(951971637,951971640),(943729303,
  943729306),(935414345,935414348),(927024809,927024812),(918558652,918558655),(910013735,
  910013738),(901387817,901387820)]
/-- Chunk 1 of `solRatios_r64`. -/
def solRatios_r64_c1 : List (IvInt) := [(892678552,892678555),(883883475,883883478),(874999999,
  875000002),(866025402,866025405),(856956824,856956827),(847791246,847791249),(838525490,
  838525493),(829156196,829156199),(819679814,819679817),(810092586,810092589),(800390528,
  800390531),(790569414,790569417)]
/-- Chunk 2 of `solRatios_r64`. -/
def solRatios_r64_c2 : List (IvInt) := [(780624748,780624751),(770551749,770551752),(760345315,
  760345318),(749999999,750000002),(739509971,739509974),(728868985,728868988),(718070329,
  718070332),(707106780,707106783),(695970544,695970547),(684653195,684653198),(673145599,
  673145602),(661437826,661437829)]
/-- Chunk 3 of `solRatios_r64`. -/
def solRatios_r64_c3 : List (IvInt) := [(649519051,649519054),(637377438,637377441),(624999999,
  625000002),(612372434,612372437),(599478939,599478942),(586301968,586301971),(572821960,
  572821963),(559016993,559016996),(544862366,544862369),(530330084,530330087),(515388202,
  515388205),(499999999,500000002)]
/-- Chunk 4 of `solRatios_r64`. -/
def solRatios_r64_c4 : List (IvInt) := [(484122917,484122920),(467707172,467707175),(450693908,
  450693911),(433012700,433012703),(414578097,414578100),(395284706,395284709),(374999999,
  375000002),(353553389,353553392),(330718912,330718915),(306186216,306186219),(279508496,
  279508499),(249999999,250000002)]
/-- Chunk 5 of `solRatios_r64`. -/
def solRatios_r64_c5 : List (IvInt) := [(216506349,216506352),(176776694,176776697),(124999999,
  125000002)]
/-- Stratum angle-ratio intervals for WKB `r = 64`. -/
def solRatios_r64 : List (IvInt) := List.append ( List.append ( solRatios_r64_c0) ( List.append (
  solRatios_r64_c1) ( solRatios_r64_c2))) ( List.append ( solRatios_r64_c3) ( List.append (
  solRatios_r64_c4) ( solRatios_r64_c5)))
/-- Chunk 0 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c0 : List (IvInt × IvInt) := [((968935920,968935921),(247311911,247311913)),
  ((969418807,969418808),(245412255,245412257)),((969901773,969901774),(243496508,243496510)),
  ((970384817,970384819),(241564286,241564288)),((970867941,970867942),(239615190,239615192)),
  ((971351143,971351145),(237648804,237648807))]
/-- Chunk 1 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c1 : List (IvInt × IvInt) := [((971834425,971834426),(235664696,235664698)),
  ((972317785,972317786),(233662412,233662415)),((972801224,972801226),(231641482,231641484)),
  ((973284742,973284744),(229601412,229601414)),((973768339,973768341),(227541687,227541689)),
  ((974252015,974252017),(225461768,225461770))]
/-- Chunk 2 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c2 : List (IvInt × IvInt) := [((974735770,974735772),(223361090,223361092)),
  ((975219604,975219605),(221239061,221239063)),((975703517,975703518),(219095060,219095062)),
  ((976187509,976187510),(216928436,216928438)),((976671580,976671581),(214738502,214738504)),
  ((977155729,977155730),(212524538,212524540))]
/-- Chunk 3 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c3 : List (IvInt × IvInt) := [((977639958,977639959),(210285784,210285786)),
  ((978124266,978124267),(208021439,208021442)),((978608652,978608654),(205730658,205730661)),
  ((979093118,979093119),(203412547,203412549)),((979577663,979577664),(201066160,201066162)),
  ((980062287,980062288),(198690495,198690497))]
/-- Chunk 4 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c4 : List (IvInt × IvInt) := [((980546989,980546991),(196284487,196284489)),
  ((981031771,981031773),(193847007,193847009)),((981516632,981516633),(191376851,191376853)),
  ((982001572,982001573),(188872737,188872739)),((982486591,982486592),(186333294,186333296)),
  ((982971689,982971691),(183757058,183757060))]
/-- Chunk 5 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c5 : List (IvInt × IvInt) := [((983456867,983456868),(181142458,181142460)),
  ((983942123,983942124),(178487808,178487810)),((984427458,984427459),(175791291,175791293)),
  ((984912873,984912874),(173050952,173050954)),((985398366,985398367),(170264671,170264673)),
  ((985883939,985883940),(167430157,167430159))]
/-- Chunk 6 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c6 : List (IvInt × IvInt) := [((986369591,986369592),(164544915,164544917)),
  ((986855322,986855323),(161606227,161606228)),((987341132,987341133),(158611122,158611124)),
  ((987827021,987827022),(155556340,155556342)),((988312990,988312991),(152438293,152438295)),
  ((988799037,988799038),(149253016,149253018))]
/-- Chunk 7 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c7 : List (IvInt × IvInt) := [((989285164,989285165),(145996106,145996108)),
  ((989771370,989771371),(142662658,142662660)),((990257655,990257656),(139247174,139247175)),
  ((990744019,990744020),(135743459,135743461)),((991230463,991230464),(132144497,132144499)),
  ((991716986,991716987),(128442279,128442281))]
/-- Chunk 8 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c8 : List (IvInt × IvInt) := [((992203588,992203589),(124627603,124627605)),
  ((992690269,992690270),(120689805,120689806)),((993177029,993177030),(116616411,116616413)),
  ((993663869,993663870),(112392679,112392681)),((994150788,994150789),(108000971,108000973)),
  ((994637786,994637787),(103419888,103419890))]
/-- Chunk 9 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c9 : List (IvInt × IvInt) := [((995124864,995124865),(98623044,98623046)),
  ((995612020,995612021),(93577262,93577264)),((996099256,996099257),(88239846,88239848)),
  ((996586572,996586573),(82554250,82554252)),((997073966,997073967),(76442820,76442822)),
  ((997561440,997561441),(69793783,69793784))]
/-- Chunk 10 of `solTrigIvs_r64`. -/
def solTrigIvs_r64_c10 : List (IvInt × IvInt) := [((998048993,998048994),(62435613,62435615)),
  ((998536626,998536627),(54079624,54079625)),((999024338,999024339),(44163011,44163013)),
  ((999512129,999512130),(31233044,31233046))]
/-- Stratum `(cosIv, sinIv)` intervals for WKB `r = 64`. -/
def solTrigIvs_r64 : List (IvInt × IvInt) := List.append ( List.append ( List.append (
  solTrigIvs_r64_c0) ( solTrigIvs_r64_c1)) ( List.append ( solTrigIvs_r64_c2) ( List.append (
  solTrigIvs_r64_c3) ( solTrigIvs_r64_c4)))) ( List.append ( List.append ( solTrigIvs_r64_c5) (
  List.append ( solTrigIvs_r64_c6) ( solTrigIvs_r64_c7))) ( List.append ( solTrigIvs_r64_c8) (
  List.append ( solTrigIvs_r64_c9) ( solTrigIvs_r64_c10))))
/-- Chunk 0 of `solTailLbs_r64`. -/
def solTailLbs_r64_c0 : List (ℤ) := [999960569,999941218,999940240,999938556,999930572,999911091,
  999899212,999889892,999884630,999867508,999842752,999820744,999817874,999786886,999737212,
  999717897,999703849,999679136,999534704,999528716]
/-- Chunk 1 of `solTailLbs_r64`. -/
def solTailLbs_r64_c1 : List (ℤ) := [999427718,999359085,999340316,999308483,999224786,999214141,
  999197669,999147830,999123025,999100303,999037350,999032285,998995589,998995500,998992861,
  998992702,998984960,998984749,998963827,998962779]
/-- Chunk 2 of `solTailLbs_r64`. -/
def solTailLbs_r64_c2 : List (ℤ) := [998938066,998929942,998914194,998908995,998902032,998898953,
  998879303,998873361,998862294,998840067,998836616,998815595,998714313,998620167,998594164,
  998565219,998554085,998527557,998496015,998387362]
/-- Chunk 3 of `solTailLbs_r64`. -/
def solTailLbs_r64_c3 : List (ℤ) := [994479037,989675601,978932742,801478743]
/-- Certified suffix probability lower bounds for WKB `r = 64`. -/
def solTailLbs_r64 : List (ℤ) := List.append ( List.append ( solTailLbs_r64_c0) (
  solTailLbs_r64_c1)) ( List.append ( solTailLbs_r64_c2) ( solTailLbs_r64_c3))
/-- Stage specification for WKB Multi-pulse conveyor at `r = 64`. -/
def solStage_r64 : PulseM1StageSpec := ⟨64, 249905, 1000000, solWkbToSwLPulses solWkbSched_r64⟩
/-- WKB `L2Ball` center checkpoint after pulse `480` at `r = 64`. -/
def solCkptEnd_r64 : List ℤ := List.append ( List.append ( [1459261,(-4048410),(-1720967),(-502896),
  852023,78148,1294661,(-2516414),(-1285107),4231723,1254547,(-817742),(-3348256),(-2545171),
  1686057,2121305,(-872558),(-3323748),(-2464841),2352536,4384367,(-1557388),(-4424973),(-1482149),
  821072,5445822,1154063,(-4192877),(-5665178),2021903,3902195,3088125] ) ( [(-2123810),(-3275088),
  (-3739968),8094983,8882831,158087,(-2442003),(-7867464),(-6253251),4833829,6728056,470759,
  (-4306718),(-5239454),(-2093386),6834444,6081711,(-1120670),(-3064300),(-3889425),(-1159182),
  4876593,5104823,(-1974851),(-4572207),(-4192318),(-2268729),5786121,5429018,2189558,519635,
  (-5233136)] )) ( List.append ( [(-3051540),(-285583),78229,1581015,373683,(-159013),(-365928),
  1160643,2529016,457439,7280,(-3186223),(-3281749),25556,1023262,3701123,3319014,(-1753472),
  (-2247037),(-3108457),(-2467054),2115783,850037,1858951,1872525,523936,1675112,(-2820412),
  (-3419698),(-2018393),(-1366766),3069688] ) ( [1282010,(-251569),(-4707862),(-113955),(-1854445),
  4272491,1663762,(-3216272),(-9536087),(-3073674),(-9203333),5089121,(-322901),4977751,2041100,
  2479922,(-2232623),(-1008604),5050741,(-4185858),(-3744541),(-9098659),(-5086189),(-58482406),
  (-22094602),(-56320731),40391334,(-17580395),102146453,101765017,408778401,856246887] ))
private def _ck64_30 : List ℤ := List.append [37200388, 21222644, 11341966, 7618003, 50569847,
  43149894, 143108712, 122287990, 271399886, 189009745, 310684897, 192183344, 427893623, 329538454,
  518432826, 267995680, 245946064, 104200864, 98412009, 34378300, 26439459, 7545288, 5288950,
  1282644, 819365, 168141, 94462, 16298, 7879, 1135, 472, 53] [16, 0]
private def _ck64_60 : List ℤ := List.append [(-3645894), (-7267085), (-227499), 5628154, 10381311,
  (-5823174), (-20097849), (-15735525), (-10400230), 6234299, 9849381, 4649161, 8778565, 12356813,
  30635744, 27912057, 52829672, 25800749, 85686801, 66365435, 206822464, 182395778, 306891615,
  195417232, 319075311, 218991473, 474053052, 350798695, 397527968, 199711915, 225251729, 111020523]
  [105187400, 43751496, 37600351, 14046670, 11580189, 3945549, 2899088, 884817, 559748, 151056,
  82865, 19804, 9654, 2054, 900, 164, 59, 4, 1, 0]
private def _ck64_90 : List ℤ := List.append [1532342, (-1740299), 1265670, 3494805, (-2543145),
  (-3515773), 3832613, 7006105, 13442294, (-641084), (-8544013), (-2887073), 10664077, 13512479,
  20498179, (-2711220), (-1089787), (-13288456), 978427, (-3899065), 8789481, (-800155), 6176094,
  (-1586628), 19749989, 11807801, 49898285, 31238304, 67487960, 31962307, 84196765, 44836864]
  (List.append [174421500, 147030791, 304364834, 207725110, 307264517, 196261197, 414572678,
  331054483, 428277311, 236404768, 278701498, 154912485, 156988077, 73888442, 69002696, 30175999,
  27014195, 11072364, 8724431, 3251991, 2186679, 730073, 426317, 128565, 66555, 18313, 8500, 2132,
  876, 190, 61, 6] [1, 0])
private def _ck64_120 : List ℤ := List.append [(-2665567), 3004296, 1887842, (-2612460), (-624972),
  (-3102898), 1431185, 2264382, (-2555163), (-3595112), (-1260253), 7100703, 2940736, (-2868833),
  (-10976693), (-5588152), 5170647, 13411397, 7404737, (-752023), (-8249090), (-3721116), 9205966,
  14697935, 21326421, 10770819, 10516242, 541935, 9830083, 3521023, 14328219, 2817696] (List.append
  [13989155, 1770414, 20071163, 8754876, 34665032, 23051745, 62825108, 44090349, 85525134, 45497805,
  99455802, 61776528, 189354142, 163026213, 305885241, 210299593, 308272247, 208259823, 426398947,
  326621386, 384661156, 228396300, 277850190, 155633999, 154395376, 78127715, 73923639, 36457234,
  30727784, 14033107, 9798354, 3987546] [2335239, 846580, 436373, 143353, 67137, 20152, 8701, 2388,
  938, 220, 68, 6, 1, 0])
private def _ck64_150 : List ℤ := List.append [(-1837982), (-3891128), (-1774409), (-257070),
  741332, 573827, 2630399, (-308642), (-4587684), (-2046861), 1729688, 1833447, 1415142, (-2745407),
  (-3656390), 3954250, 4074979, (-893111), (-7749888), (-6657950), 905073, 7888370, 5537857,
  (-5031359), (-12991232), (-8198202), (-1003143), 9221145, 7506844, 422892, (-7523794), (-6997551)
  ] (List.append [(-1162581), 8074248, 14231462, 12243677, 13227438, 7449368, 12997782, 8333756,
  13300060, 7465785, 12846166, 9328693, 15026805, 10534598, 24038684, 20206206, 42633755, 37608549,
  75797534, 57530533, 93727616, 60666494, 128669646, 108049918, 251879149, 216742736, 305482950,
  209896110, 345179949, 291607588, 431016001, 276785057] [327175800, 208320933, 211296098,
  117651541, 112788326, 60644265, 52283343, 25628016, 18071895, 7782600, 4569210, 1751120, 902177,
  314164, 147317, 47120, 20318, 5968, 2363, 621, 210, 36, 6, 0])
private def _ck64_180 : List ℤ := List.append (List.append [3003999, (-3081406), (-481272),
  (-1727134), (-109318), 848601, 1260050, 2533902, (-174117), (-4419128), (-1428693), 448842,
  146943, 4203215, 2003724, (-1824229), (-3283204), (-1014497), (-1315972), 3300226, 4757073,
  (-529321), (-3762560), (-5563483), 141446, 5686526, 8158003, (-2835176), (-8306360), (-7593073),
  1105207, 8822050] [6828363, (-1622294), (-11929545), (-9015835), (-4048743), 5488870, 6426991,
  1145988, (-5828587), (-8519985), (-2425794), (-213130), 6751716, 7042815, 12699286, 8174363,
  13666767, 9330781, 15029931, 8219130, 15246710, 7656664, 17196897, 9353950, 22968606, 16461981,
  39196897, 30346095, 67562831, 54576184, 96922104, 68696039]) (List.append [123716197, 96860282,
  227296962, 201910544, 309879564, 216455637, 340461279, 287157996, 429399527, 282875121, 337753525,
  216893491, 219520240, 127552912, 123272775, 68725100, 56017030, 27506507, 17895076, 7632825,
  4168544, 1587321, 772339, 268078, 118797, 37824, 15329, 4464, 1645, 417, 123, 15] [1, 0])
private def _ck64_210 : List ℤ := List.append (List.append [3936620, 1738418, 1385766, (-1137660),
  (-804675), 290806, (-1538234), 2375343, 3562369, (-2620790), (-1226810), (-858817), (-3072009),
  2872522, 2705858, 145045, (-1770738), (-2945016), (-3021292), 1575329, 4057490, 2277025, 843154,
  (-4589809), (-5276048), (-1579344), 1176932, 4186522, 5760545, (-1731628), (-1240495), (-4837727)
  ] [(-2273858), 3553745, 9265024, 9131184, 5434593, (-5477116), (-7907256), (-5085518), 6546002,
  9058649, 7000192, (-6135139), (-7989438), (-6116694), 521722, 3612693, 4649698, (-662225),
  (-3620619), (-5989930), (-3584295), (-728267), 3381284, 4711768, 9962337, 8159092, 13200365,
  9856853, 15891803, 10349409, 16004456, 9340649]) (List.append [17521675, 11773258, 25912059,
  20657290, 41644775, 32375566, 69227736, 60004938, 106583983, 83077795, 144484071, 119215475,
  254915645, 221124714, 311755905, 230345884, 391008022, 328784622, 387736225, 268840130, 299662566,
  185294380, 184805449, 110923334, 96473910, 51119014, 34468862, 15532204, 8555780, 3391794,
  1635941, 585627] [254128, 82747, 32534, 9642, 3419, 895, 267, 45, 6, 0])
private def _ck64_240 : List ℤ := List.append (List.append [(-253822), 4295885, 1600334, 808430,
  (-626564), (-582657), (-2827650), (-113223), 4166987, 1481626, (-67203), (-1496032), (-4183911),
  (-428402), 1797228, 2027970, 643610, (-3375563), (-3348410), (-630887), 2048948, 4177306, 3080599,
  (-3505304), (-3970973), (-3816069), (-586642), 4309058, 6007233, 309121, 127838, (-4974674) ]
  [(-3033233), 2456886, 5741825, 6822577, 7504156, (-4755770), (-2652954), (-7798867), (-7843975),
  970120, 2613229, 6228025, 5641483, (-3894861), (-5320896), (-7653576), (-1955859), 5052905,
  10012264, 5478508, 535987, (-5618289), (-4254896), (-425509), 3264185, 3217243, 1779552,
  (-1427961), (-4333577), (-4090787), (-3306303), 382264]) (List.append [2176166, 5496179, 8058386,
  8291550, 13117372, 12554412, 14981676, 11425411, 14549895, 11832315, 20806248, 18936047, 32167259,
  26115163, 47996077, 44244763, 91132173, 85321832, 133879913, 106073643, 201827023, 187510210,
  311778522, 240840954, 363150337, 319039487, 409894992, 286578584, 327099292, 211481500, 211891449,
  131924962] [110363097, 58476823, 36889240, 16398476, 8438160, 3286931, 1479112, 514967, 206555,
  64659, 23112, 6486, 2047, 487, 116, 11])
private def _ck64_270 : List ℤ := List.append (List.append [(-4113942), 1262748, (-93437), 1790501,
  231681, (-823649), (-1343388), (-2490730), 1108183, 4281461, 1144867, (-965352), (-2426118),
  (-3435493), (-181272), 2703667, 2730147, (-2086840), (-2240863), (-2566788), (-683202), 4602316,
  4443498, (-1425686), (-1787923), (-5209064), (-2253271), 3719530, 5552378, 2313773, 1482544,
  (-4750345) ] [(-3477937), 1772216, 4721896, 7564381, 7830333, (-4197095), (-2626689), (-7807752),
  (-7761609), 1492136, 3441410, 5800442, 4772754, (-4818789), (-5447628), (-4627644), (-4170573),
  4566119, 3530598, 3471675, 2975233, (-4033958), (-4625657), (-3000410), (-3646871), 5303008,
  5320591, 6914792, 3602683, (-240436), (-4403401), (-1327704) ]) (List.append [(-138777), 2889306,
  2536112, 1799750, (-3003017), (-2994364), (-5807921), (-1610239), (-2800338), 1739911, 1948422,
  6877641, 9342170, 12385972, 13120698, 11206077, 12023703, 13297173, 20251803, 19732185, 27593349,
  22885713, 40999925, 42749954, 88056126, 88674734, 139451354, 114693931, 202748742, 196015113,
  321963908, 259069335] [388778762, 336423985, 392421105, 287931995, 305605857, 204634829,
  191375532, 113188819, 78184203, 37390725, 19760845, 8012126, 3581501, 1270980, 494089, 154437,
  52374, 14409, 4222, 984, 221, 26, 1, 0])
private def _ck64_300 : List ℤ := List.append (List.append [(-2620235), (-3413710), (-1675788),
  637470, 838434, (-170572), 1458619, (-2425051), (-2924882), 3317235, 1463179, 318940, 995721,
  (-4086225), (-2051859), 1769906, 3426152, 264760, (-173188), (-3402920), (-3174073), 3401961,
  4544940, 1058665, 790436, (-5450343), (-3547548), 2515357, 4449093, 4048212, 2724367, (-4164318) ]
  [(-3770499), 1010018, 3607512, 8154877, 8114988, (-3616167), (-2600398), (-7816547), (-7644544),
  2007485, 4206210, 5272210, 3664522, (-5707121), (-6521789), (-2925397), (-2316691), 5733765,
  4657647, 1680454, 646011, (-4970666), (-5472955), 77417, 51930, 6203045, 6186916, 590137, 3224892,
  (-4885544), (-3720777), (-3716395) ]) (List.append [(-2929363), 901250, (-93085), 1575575,
  (-448918), (-1210430), (-4602732), (-2017733), (-1651758), 2793887, 1302839, 1400030, (-2863499),
  (-2646650), (-5820364), (-2429809), (-6240615), (-1582362), (-1454977), 6752903, 8310319,
  11126962, 7948686, 9871918, 12982755, 17879463, 20217906, 18926398, 22679887, 26035827, 48878518,
  59113501] [106141091, 107351283, 155987651, 141439570, 267305769, 260728820, 355526740, 304425502,
  427981614, 320026852, 357711119, 250485323, 235833386, 143681340, 96299913, 45710445, 22799517,
  8984342, 3702594, 1244466, 430625, 123611, 35869, 8705, 2059, 380, 22, 0])
private def _ck64_330 : List ℤ := List.append (List.append [2283410, (-3647619), (-1259829),
  (-1275723), 535074, 667654, 2829853, 19392, (-4386525), (-563349), 639245, 1354244, 3734612,
  (-1934265), (-2701004), (-217468), 2377125, 2481507, 1968692, (-2781030), (-4543979), 1000162,
  3356128, 3242477, 3194034, (-4486557), (-4255603), 895525, 2826223, 5309883, 3758754, (-3261213) ]
  [(-3898119), 203635, 2420975, 8582252, 8356614, (-3016062), (-2574071), (-7825253), (-7493300),
  2513859, 4891121, 4643847, 2395580, (-6345166), (-7078792), (-991176), (-172014), 6181710,
  4933873, (-417735), (-1845271), (-4660454), (-4527017), 3076583, 3845788, 4867275, 4970620,
  (-3730842), (-1364813), (-5692603), (-5224202), 602892]) (List.append [(-877659), 2936516,
  1336835, 847698, 241377, (-326598), (-247484), 1191536, 2233919, 1270731, 2257319, (-2248678),
  (-1283321), (-3586024), (-4679064), (-841657), (-1135023), 2321616, (-1370862), 192560,
  (-4026015), (-876459), (-8342232), (-5459366), (-10741960), 987318, 375992, 8411702, 2173510,
  7304784, 7275747, 16218909] [16530478, 16793850, 14128503, 19279305, 34933710, 48229428, 83185610,
  93041813, 147894637, 144841411, 249382966, 261661853, 364537618, 316703012, 435119881, 340677109,
  365266640, 259643074, 214716202, 118188690, 64502839, 27167575, 11294937, 3863313, 1285446,
  357390, 93254, 20714, 3737, 482])
private def _ck64_360 : List ℤ := List.append (List.append [4215466, 865437, 658429, (-1667663),
  (-349103), 781146, 1425251, 2444815, (-1991742), (-3948662), (-683715), 1332347, 3911980, 1544385,
  (-1742266), (-2075385), 117368, 3434366, 3267060, (-967570), (-4309125), (-1754858), 1214548,
  4505788, 4891435, (-2530802), (-4260426), (-872292), 873299, 5951448, 4506939, (-2109791) ]
  [(-3855215), (-611654), 1186008, 8837961, 8553933, (-2399969), (-2547713), (-7833870), (-7308557),
  3008993, 5483137, 3927284, 1021580, (-6704943), (-7074461), 1021643, 1994255, 5853726, 4308813,
  (-2439617), (-3873655), (-3181145), (-2086663), 5060143, 6022835, 1485252, 1161285, (-6105544),
  (-5089600), (-2892127), (-2776474), 4466200]) (List.append [1954384, 2360892, 1388962, (-759278),
  (-199590), (-353684), 1044378, 624721, 1777440, (-1856303), (-1867680), (-2581438), (-3160940),
  882609, 623357, 3789032, 3753726, (-2535), 934465, (-3720009), (-2773165), (-1784034), (-2369454),
  (-332548), (-3521478), (-277253), (-1415459), 601919, (-7925774), (-8246774), (-13827478),
  (-2799714) ] [(-4317896), 3040434, (-4397433), 3989567, 5692812, 16265235, 12547949, 11559824,
  10407428, 18525874, 37180458, 46122781, 81720866, 98827045, 164148157, 179292468, 294843793,
  310915927, 401061980, 385560217, 429276340, 338871678, 293883345, 171472220, 93365442, 38706749,
  14777871, 4617159, 1125858, 264271, 37383, 4601])
private def _ck64_390 : List ℤ := List.append (List.append [661576, 4252226, 1791534, (-70976),
  (-854325), 46713, (-1377398), 2472090, 2154085, (-3862497), (-1472927), 270341, 1406169, 3963758,
  253622, (-2697849), (-2202170), 2638008, 3165612, 1260454, (-2552449), (-3890130), (-1271825),
  4489956, 5507345, (-15490), (-3561221), (-2495962), (-1181609), 5897978, 4911958, (-797727) ]
  [(-3643661), (-1400190), (-72678), 8916888, 8705896, (-1771149), (-2521323), (-7842403),
  (-7091136), 3490675, 5971015, 3136131, (-397222), (-6770672), (-6509142), 2953451, 3910201,
  4790977, 2896649, (-4015843), (-4930312), (-903824), 1042513, 5373305, 5667817, (-2521195),
  (-3253863), (-5295152), (-5588984), 1741157, 1771148, 4951644]) (List.append [3048761, (-313833),
  8132, (-1582924), (-404350), 37798, 932792, (-781599), (-1366456), (-2176685), (-2841930),
  1440651, 671816, 3212352, 3771064, (-724181), (-456879), (-3725823), (-3834069), (-107770),
  (-777240), 3155757, 1387488, 1501043, 1876011, 511314, 2459196, (-2170972), (-1556565),
  (-3720133), (-3085048), 999991] [1609478, (-1029498), (-9255775), (-11649847), (-9921806),
  (-4386198), (-7088289), (-5754757), (-7228060), 7874943, 8292416, 12806268, 3637277, 11017350,
  14283639, 26327325, 37691839, 60737669, 112515131, 150157877, 245106886, 290374450, 410137505,
  417344151, 469323574, 373804025, 288345463, 148012736, 66528499, 22416662, 4606188, 885323])
private def _ck64_420 : List ℤ := List.append (List.append [(-3753278), 2105231, 788298, 1610347,
  (-432188), (-738427), (-2828942), 74465, 4406147, (-380611), (-1112286), (-1002705), (-2064114),
  3664444, 2098531, (-1714313), (-3400087), 498044, 1707823, 2948422, 105658, (-4651553),
  (-3397140), 3199480, 4905592, 2503254, (-2273531), (-3707178), (-3098525), 5155724, 4942973,
  575074] [(-3272714), (-2127470), (-1329915), 8817454, 8811701, (-1132940), (-2494915), (-7850846),
  (-6842013), 3956750, 6345486, 2285420, (-1798599), (-6539478), (-5427665), 4651054, 5335341,
  3126865, 955346, (-4858483), (-4750171), 1600224, 3827546, 3912689, 2929980, (-5467703),
  (-5971561), (-1722426), (-2546499), 5271022, 4979217, 1692075]) (List.append [1432443, (-2709529),
  (-1381084), (-773509), (-130580), 384543, (-432292), (-1137600), (-2444327), 793992, 978116,
  3032379, 3249722, (-458084), (-824486), (-3750410), (-3643127), 904506, 724025, 3766630, 3240854,
  (-244523), 808846, (-1877237), (-490973), (-1881438), (-3201228), (-716166), (-1674307), 3600685,
  2873427, 1741961] [212097, (-1289132), (-2732774), 3835222, 1473018, 4393861, (-2381779),
  (-7628180), (-9909577), (-5794721), (-8021196), (-12172057), (-10287577), (-11240118), 5769495,
  (-5917270), 12621171, (-5779193), 20494470, (-635806), 36971064, 21432238, 101351104, 126626740,
  260034413, 325924488, 488227697, 493628272, 466544647, 276801968, 132360194, 40298044])
private def _ck64_450 : List ℤ := List.append (List.append [(-3283665), (-2781476), (-1154951),
  1371392, 459090, (-722005), (-1505547), (-2396206), 2784534, 3435895, 116672, (-1492981),
  (-4118652), 851732, 2694211, 289731, (-2866250), (-1895585), (-481700), 3373102, 2726454,
  (-3770223), (-4558043), 1000709, 3219215, 4468531, (-610145), (-4305791), (-4653583), 3811366,
  4597619, 1904092] [(-2758600), (-2761687), (-2560551), 8541646, 8870783, (-488724), (-2468474),
  (-7859203), (-6562301), 4405136, 6599440, 1391303, (-3121095), (-6021498), (-3915782), 5979843,
  6090786, 1070270, (-1160469), (-4813611), (-3378425), 3702849, 5349070, 1160458, (-1039655),
  (-6115528), (-5574062), 2748846, 2109761, 5460521, 4421422, (-2847236) ]) (List.append
  [(-1457478), (-2696147), (-1345477), 833918, 297718, 276198, (-1216456), 35125, 173524, 2564186,
  3148093, (-491475), (-242345), (-3272888), (-3727093), 924201, 1338833, 3506855, 3520882,
  (-1521547), (-1241955), (-3003409), (-2043953), 22534, (-1386950), 1362805, 1299700, 3011896,
  3792194, (-1177927), (-1004103), (-3206677) ] [(-909514), 937877, 4211861, (-2106464), 207786,
  (-4652954), (-860965), 3517280, 9805234, 2059568, 10315649, (-4416281), 1740105, (-4521870),
  (-1826561), (-7600735), (-9886933), (-21327342), (-13746728), (-32218547), (-14658595),
  (-28821677), 17850028, (-13254974), 36274488, 18933160, 132066976, 162910558, 448500187,
  516934693, 596798515, 341401341])
private theorem _cWkb64_0 : solFastCheckWkbSliceS2V solWkbSched_r64 0 30 solTrigIvs_r64 [swScale, 0]
  1 0 0 _ck64_30 17 400 30000000000 = true := by decide +kernel
private theorem _cWkb64_1 : solFastCheckWkbSliceS2V solWkbSched_r64 30 30 solTrigIvs_r64 _ck64_30 17
  400 30000000000 _ck64_60 26 958 60000000000 = true := by decide +kernel
private theorem _cWkb64_2 : solFastCheckWkbSliceS2V solWkbSched_r64 60 30 solTrigIvs_r64 _ck64_60 26
  958 60000000000 _ck64_90 33 1572 90000000000 = true := by decide +kernel
private theorem _cWkb64_3 : solFastCheckWkbSliceS2V solWkbSched_r64 90 30 solTrigIvs_r64 _ck64_90 33
  1572 90000000000 _ck64_120 39 2238 120000000000 = true := by decide +kernel
private theorem _cWkb64_4 : solFastCheckWkbSliceS2V solWkbSched_r64 120 30 solTrigIvs_r64 _ck64_120
  39 2238 120000000000 _ck64_150 44 2948 150000000000 = true := by decide +kernel
private theorem _cWkb64_5 : solFastCheckWkbSliceS2V solWkbSched_r64 150 30 solTrigIvs_r64 _ck64_150
  44 2948 150000000000 _ck64_180 49 3661 180000000000 = true := by decide +kernel
private theorem _cWkb64_6 : solFastCheckWkbSliceS2V solWkbSched_r64 180 30 solTrigIvs_r64 _ck64_180
  49 3661 180000000000 _ck64_210 53 4359 210000000000 = true := by decide +kernel
private theorem _cWkb64_7 : solFastCheckWkbSliceS2V solWkbSched_r64 210 30 solTrigIvs_r64 _ck64_210
  53 4359 210000000000 _ck64_240 56 5039 240000000000 = true := by decide +kernel
private theorem _cWkb64_8 : solFastCheckWkbSliceS2V solWkbSched_r64 240 30 solTrigIvs_r64 _ck64_240
  56 5039 240000000000 _ck64_270 60 5701 270000000000 = true := by decide +kernel
private theorem _cWkb64_9 : solFastCheckWkbSliceS2V solWkbSched_r64 270 30 solTrigIvs_r64 _ck64_270
  60 5701 270000000000 _ck64_300 62 6344 300000000000 = true := by decide +kernel
private theorem _cWkb64_10 : solFastCheckWkbSliceS2V solWkbSched_r64 300 30 solTrigIvs_r64 _ck64_300
  62 6344 300000000000 _ck64_330 63 6965 330000000000 = true := by decide +kernel
private theorem _cWkb64_11 : solFastCheckWkbSliceS2V solWkbSched_r64 330 30 solTrigIvs_r64 _ck64_330
  63 6965 330000000000 _ck64_360 64 7559 360000000000 = true := by decide +kernel
private theorem _cWkb64_12 : solFastCheckWkbSliceS2V solWkbSched_r64 360 30 solTrigIvs_r64 _ck64_360
  64 7559 360000000000 _ck64_390 64 8127 390000000000 = true := by decide +kernel
private theorem _cWkb64_13 : solFastCheckWkbSliceS2V solWkbSched_r64 390 30 solTrigIvs_r64 _ck64_390
  64 8127 390000000000 _ck64_420 64 8655 419999809003 = true := by decide +kernel
private theorem _cWkb64_14 : solFastCheckWkbSliceS2V solWkbSched_r64 420 30 solTrigIvs_r64 _ck64_420
  64 8655 419999809003 _ck64_450 64 9153 449939826252 = true := by decide +kernel
private theorem _cWkb64_15 : solFastCheckWkbSliceS2V solWkbSched_r64 450 30 solTrigIvs_r64 _ck64_450
  64 9153 449939826252 solCkptEnd_r64 64 9629 478807632485 = true := by decide +kernel
private def _wkbTerm32_64Ok : Bool :=
  (checkPulseWkbTerminalTable 32 solWkbSched_r32 solRatios_r32 solTrigIvs_r32 solCkptEnd_r32 4522
    258879974653 1417 solTailLbs_r32 258879974653 solM1VTable16 &&
  checkPulseWkbTerminalEnv 64 solWkbSched_r64 solRatios_r64 solTrigIvs_r64 solCkptEnd_r64 9629
    478807632485 2101 solTailLbs_r64 478807632485 solM1VTable16)
private theorem _cWkbTerm32_64 : _wkbTerm32_64Ok = true := by decide +kernel
theorem cert_solWkbTerm_r32 : checkPulseWkbTerminalTable 32 solWkbSched_r32 solRatios_r32
    solTrigIvs_r32 solCkptEnd_r32 4522 258879974653 1417 solTailLbs_r32 258879974653 solM1VTable16 =
    true := _bL _cWkbTerm32_64
theorem runPrefix_solWkb_r32 : SolWkbRunPrefix solWkbSched_r32 solTrigIvs_r32 260
    solCkptEnd_r32 32 4522 258879974653 := by
  have hp := solWkbRunPrefix_zero solWkbSched_r32 solTrigIvs_r32
  have hp := solFastWkbStepS2V_eq (tNext := 52) rfl hp _cWkb32_0
  have hp := solFastWkbStepS2V_eq (tNext := 104) rfl hp _cWkb32_1
  have hp := solFastWkbStepS2V_eq (tNext := 156) rfl hp _cWkb32_2
  have hp := solFastWkbStepS2V_eq (tNext := 208) rfl hp _cWkb32_3
  have hp := solFastWkbStepS2V_eq (tNext := 260) rfl hp _cWkb32_4
  exact hp
theorem cert_solWkbTerm_r64 : checkPulseWkbTerminalEnv 64 solWkbSched_r64 solRatios_r64
    solTrigIvs_r64 solCkptEnd_r64 9629 478807632485 2101 solTailLbs_r64 478807632485 solM1VTable16 =
    true := _bR _cWkbTerm32_64
theorem runPrefix_solWkb_r64 : SolWkbRunPrefix solWkbSched_r64 solTrigIvs_r64 480
    solCkptEnd_r64 64 9629 478807632485 := by
  have hp := solWkbRunPrefix_zero solWkbSched_r64 solTrigIvs_r64
  have hp := solFastWkbStepS2V_eq (tNext := 30) rfl hp _cWkb64_0
  have hp := solFastWkbStepS2V_eq (tNext := 60) rfl hp _cWkb64_1
  have hp := solFastWkbStepS2V_eq (tNext := 90) rfl hp _cWkb64_2
  have hp := solFastWkbStepS2V_eq (tNext := 120) rfl hp _cWkb64_3
  have hp := solFastWkbStepS2V_eq (tNext := 150) rfl hp _cWkb64_4
  have hp := solFastWkbStepS2V_eq (tNext := 180) rfl hp _cWkb64_5
  have hp := solFastWkbStepS2V_eq (tNext := 210) rfl hp _cWkb64_6
  have hp := solFastWkbStepS2V_eq (tNext := 240) rfl hp _cWkb64_7
  have hp := solFastWkbStepS2V_eq (tNext := 270) rfl hp _cWkb64_8
  have hp := solFastWkbStepS2V_eq (tNext := 300) rfl hp _cWkb64_9
  have hp := solFastWkbStepS2V_eq (tNext := 330) rfl hp _cWkb64_10
  have hp := solFastWkbStepS2V_eq (tNext := 360) rfl hp _cWkb64_11
  have hp := solFastWkbStepS2V_eq (tNext := 390) rfl hp _cWkb64_12
  have hp := solFastWkbStepS2V_eq (tNext := 420) rfl hp _cWkb64_13
  have hp := solFastWkbStepS2V_eq (tNext := 450) rfl hp _cWkb64_14
  have hp := solFastWkbStepS2V_eq (tNext := 480) rfl hp _cWkb64_15
  exact hp
end QuantumComputation.Specs.GroverFindAll.GroverM1PulsePt0
end
