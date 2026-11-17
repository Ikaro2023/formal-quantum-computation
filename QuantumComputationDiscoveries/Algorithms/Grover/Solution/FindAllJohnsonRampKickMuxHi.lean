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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxBridge
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampMuxWindowedQHL
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiWinCert1024
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiCert128
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiCert256
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiCert512
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RampKickMuxHiCert1024
/-
 # High-m Sparse Checkpointed & Windowed Router Arm (`FindAllJohnsonRampKickMuxHi`)
QHL-verified specialist module packaging all `40` `(m, k) in {128..1024} x {2..1024}` cells
via
`k <= 512` `RampKickMux` tables and `s = 0` windowed `r = 1024` batch renewal.
-/
namespace QuantumComputation.Specs.GroverFindAll.FindAllJohnsonRampKickMuxHi
@[expose] public section
open Operator ResourceCounting Real QProg QProg.Notation QuantumComputation.Specs
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
/-- Supported high-`m` `(m, k)` cells (`m in {128..1024}`, `k in {2..1024}`). -/
def isJohnsonRampKickMuxHiCell (m k : ℕ) : Bool :=
  ((m == 128) || (m == 256) || (m == 512) || (m == 1024)) && ((k == 2) || (k == 4) ||
    (k == 8) || (k == 16) || (k == 32) || (k == 64) || (k == 128) || (k == 256) ||
    (k == 512) || (k == 1024))
/-- Per-cell max block-multiplexing factor `L_{max}(m, k) >= 2` across `40` cells. -/
def johnsonRampKickMuxHiCellLMax (m k : ℕ) : ℕ :=
  if m == 128 && k == 2 then 2
  else if m == 128 && k == 4 then 2
  else if m == 128 && k == 8 then 2
  else if m == 128 && k == 16 then 2
  else if m == 128 && k == 32 then 2
  else if m == 128 && k == 64 then 2
  else if m == 128 && k == 128 then 2
  else if m == 128 && k == 256 then 3
  else if m == 128 && k == 512 then 7
  else if m == 128 && k == 1024 then 16
  else if m == 256 && k == 2 then 2
  else if m == 256 && k == 4 then 2
  else if m == 256 && k == 8 then 2
  else if m == 256 && k == 16 then 2
  else if m == 256 && k == 32 then 2
  else if m == 256 && k == 64 then 2
  else if m == 256 && k == 128 then 2
  else if m == 256 && k == 256 then 2
  else if m == 256 && k == 512 then 4
  else if m == 256 && k == 1024 then 8
  else if m == 512 && k == 2 then 2
  else if m == 512 && k == 4 then 2
  else if m == 512 && k == 8 then 2
  else if m == 512 && k == 16 then 2
  else if m == 512 && k == 32 then 2
  else if m == 512 && k == 64 then 2
  else if m == 512 && k == 128 then 2
  else if m == 512 && k == 256 then 2
  else if m == 512 && k == 512 then 2
  else if m == 512 && k == 1024 then 4
  else if m == 1024 && k == 2 then 2
  else if m == 1024 && k == 4 then 2
  else if m == 1024 && k == 8 then 2
  else if m == 1024 && k == 16 then 2
  else if m == 1024 && k == 32 then 2
  else if m == 1024 && k == 64 then 2
  else if m == 1024 && k == 128 then 2
  else if m == 1024 && k == 256 then 2
  else if m == 1024 && k == 512 then 2
  else if m == 1024 && k == 1024 then 2
  else 1
/-- Total register qubit budget `(L_{max}(m, k) * m) * (n + 1) + k * n`. -/
abbrev johnsonRampKickMuxHiQubits (n m k : ℕ) : ℕ :=
  (johnsonRampKickMuxHiCellLMax m k * m) * (n + 1) + k * n
/-- Certified asymptotic relative-cost profile `c(m, k): ℚ≥0` across `40` cells. -/
def relCostJohnsonRampKickMuxHi (m k : ℕ) : ℚ≥0 :=
  if m == 128 && k == 2 then NNRat.divNat 517005249363 1000000000000
  else if m == 128 && k == 4 then NNRat.divNat 17491896601 50000000000
  else if m == 128 && k == 8 then NNRat.divNat 228384397809 1000000000000
  else if m == 128 && k == 16 then NNRat.divNat 19213466223 125000000000
  else if m == 128 && k == 32 then NNRat.divNat 26894253763 250000000000
  else if m == 128 && k == 64 then NNRat.divNat 20314094501 250000000000
  else if m == 128 && k == 128 then NNRat.divNat 71222117181 1000000000000
  else if m == 128 && k == 256 then NNRat.divNat 67515303789 1000000000000
  else if m == 128 && k == 512 then NNRat.divNat 12679764911 200000000000
  else if m == 128 && k == 1024 then NNRat.divNat 62336347654 1000000000000
  else if m == 256 && k == 2 then NNRat.divNat 257046901743 500000000000
  else if m == 256 && k == 4 then NNRat.divNat 174409850017 500000000000
  else if m == 256 && k == 8 then NNRat.divNat 11071331 48828125
  else if m == 256 && k == 16 then NNRat.divNat 75590974927 500000000000
  else if m == 256 && k == 32 then NNRat.divNat 51772670317 500000000000
  else if m == 256 && k == 64 then NNRat.divNat 36721497027 500000000000
  else if m == 256 && k == 128 then NNRat.divNat 55938748033 1000000000000
  else if m == 256 && k == 256 then NNRat.divNat 48066079 976562500
  else if m == 256 && k == 512 then NNRat.divNat 9386381389 200000000000
  else if m == 256 && k == 1024 then NNRat.divNat 44279607682 1000000000000
  else if m == 512 && k == 2 then NNRat.divNat 255922289023 500000000000
  else if m == 512 && k == 4 then NNRat.divNat 43539968951 125000000000
  else if m == 512 && k == 8 then NNRat.divNat 225952548419 1000000000000
  else if m == 512 && k == 16 then NNRat.divNat 30001403651 200000000000
  else if m == 512 && k == 32 then NNRat.divNat 25448093779 250000000000
  else if m == 512 && k == 64 then NNRat.divNat 70667825813 1000000000000
  else if m == 512 && k == 128 then NNRat.divNat 2531723681 50000000000
  else if m == 512 && k == 256 then NNRat.divNat 19387951311 500000000000
  else if m == 512 && k == 512 then NNRat.divNat 17133448611 500000000000
  else if m == 512 && k == 1024 then NNRat.divNat 32269934052 1000000000000
  else if m == 1024 && k == 2 then NNRat.divNat 511663735229 1000000000000
  else if m == 1024 && k == 4 then NNRat.divNat 348072359161 1000000000000
  else if m == 1024 && k == 8 then NNRat.divNat 225566670669 1000000000000
  else if m == 1024 && k == 16 then NNRat.divNat 37360569541 250000000000
  else if m == 1024 && k == 32 then NNRat.divNat 12621936221 125000000000
  else if m == 1024 && k == 64 then NNRat.divNat 8683495609 125000000000
  else if m == 1024 && k == 128 then NNRat.divNat 24351613583 500000000000
  else if m == 1024 && k == 256 then NNRat.divNat 17563060499 500000000000
  else if m == 1024 && k == 512 then NNRat.divNat 6756116497 250000000000
  else if m == 1024 && k == 1024 then NNRat.divNat 24207754734 1000000000000
  else 1
/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def johnsonRampKickMuxHiProfile : FindAllCostProfile :=
  ⟨isJohnsonRampKickMuxHiCell, relCostJohnsonRampKickMuxHi, fun _ _ ↦ 80000⟩
end
public section
open Operator ResourceCounting Real QProg QProg.Notation QuantumComputation.Specs DickeSol
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
private lemma rkmHi_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold groverParallelMarkingOracle groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma rkmHi_targetSets_eq (n k : ℕ) :
    groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma rkmHi_vanilla_eq (n m k : ℕ) : vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl
private lemma rkmHi_one_le {x : ℕ} (h : 2 ≤ x) : 1 ≤ x := by omega
private theorem rkmHi_pow2_grid {i : ℕ} (hi : Nat.ble (i + 1) 11 = true) : 2 ^ i ∈ groverGrid :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.ble_eq.mp hi), rfl⟩
private def rkmHiMonoL : ℕ → List ℕ → Bool
  | _, [] => true
  | l0, l1 :: ls => Nat.ble l0 l1 && rkmHiMonoL l1 ls
private def rkmHiAnchorShape (lMaxCell : ℕ) (a : RampKickAnchor) : Bool :=
  (a.lSegs.length == a.tauSegs.length) && (a.lSegs.length == a.nsubSegs.length) &&
    (a.lSegs.length == a.masks.length) && Nat.ble 1 (rkmLastNat 0 a.lSegs) &&
    Nat.ble (rkmLastNat 0 a.lSegs) lMaxCell && rkmHiMonoL (a.lSegs.headD 1) a.lSegs.tail
private def rkmHiAnchorsShapeOk (lMaxCell : ℕ) (anchors : List RampKickAnchor) : Bool :=
  anchors.all (rkmHiAnchorShape lMaxCell)
private theorem rkmHi_findAnchor_mem {r : ℕ} :
    ∀ {anchors : List RampKickAnchor} {a : RampKickAnchor},
      rkmFindAnchor r anchors = some a → a ∈ anchors
  | [], _, h => by simp [rkmFindAnchor] at h
  | b :: rest, a, h => by
    unfold rkmFindAnchor at h; by_cases heq : b.rAct = r
    · rw [ite_eq_left heq] at h; cases Option.some.inj h; exact List.mem_cons_self
    · rw [ite_eq_right heq] at h; exact List.mem_cons_of_mem b (rkmHi_findAnchor_mem h)
private theorem rkmHiMono_build (n m r : ℕ) : ∀ (ls ts ss : List ℕ) (mks : List (List Bool))
      (l0 : ℕ), rkmHiMonoL l0 ls = true → rkmSegsMono l0 (rkmBuildTailSegs n m r ls ts ss mks)
  | [], _, _, _, _, _ | _ :: _, [], _, _, _, _ | _ :: _, _ :: _, [], _, _, _
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial
  | l1 :: ls, _ :: ts, _ :: ss, _ :: mks, l0, h => by
    unfold rkmHiMonoL at h; rw [Bool.and_eq_true, Nat.ble_eq] at h
    exact ⟨h.1, rkmHiMono_build n m r ls ts ss mks l1 h.2⟩
private theorem rkmHi_sum_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by simp
  | d + 1 => by rw [Finset.sum_range_succ, rkmHi_sum_shift f d, Finset.sum_range_succ, add_assoc]
private theorem rkmHi_sum_Icc_eq_range (f : ℕ → ℝ) :
    ∀ d : ℕ, (∑ w ∈ Finset.Icc 1 d, f w) = ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by rw [show Finset.Icc (1 : ℕ) 0 = ∅ by ext x; simp]; simp
  | d + 1 => by
    rw [show Finset.Icc 1 (d + 1) = insert (d + 1) (Finset.Icc 1 d) by ext x; simp; omega,
      Finset.sum_insert (by simp), rkmHi_sum_Icc_eq_range f d, Finset.sum_range_succ]; ring
private theorem rkmHi_altSum_eq_range :
    ∀ (d : ℕ) (xs : List ℕ), xs.length = d → altSumNat xs = ∑ j ∈ Finset.range d, xs.getD j 0
  | 0, [], _ => by simp [altSumNat]
  | 0, _ :: _, hlen | _ + 1, [], hlen => by simp at hlen
  | d + 1, x :: xs, hlen => by
    rw [rkmHi_sum_shift]
    simpa [altSumNat] using congrArg (Nat.add x) (rkmHi_altSum_eq_range d xs (by simpa using hlen))
private def rkmHiUseWalk (anchors : List RampKickAnchor) (r : ℕ) : Bool :=
  if r < 2 then false else (rkmFindAnchor r anchors).isSome
private def rkmHiAnchorAt (anchors : List RampKickAnchor) (r : ℕ) : RampKickAnchor :=
  match rkmFindAnchor r anchors with | some a => a | none => ⟨r, [1], [1], [1], [[]], []⟩
private theorem rkmHi_active_unpack {m lTableMax lMaxCell : ℕ} {vPot : List ℕ}
    {anchors : List RampKickAnchor} (htab : RampKickTableValid m 512 lTableMax true vPot anchors)
    (hshape : rkmHiAnchorsShapeOk lMaxCell anchors = true)
    {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ 512) (hwk : rkmHiUseWalk anchors r = true) :
    let a := rkmHiAnchorAt anchors r
    a.rAct = r ∧ rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks = a.rowLo12 ∧
      (a.lSegs.length = a.tauSegs.length ∧ a.lSegs.length = a.nsubSegs.length ∧
        a.lSegs.length = a.masks.length) ∧
      RampKickActiveValid m lTableMax r vPot a.lSegs a.tauSegs a.rowLo12 ∧
      1 ≤ rkmLastNat 0 a.lSegs ∧ rkmLastNat 0 a.lSegs ≤ lMaxCell ∧
      rkmHiMonoL (a.lSegs.headD 1) a.lSegs.tail = true := by
  intro a; unfold rkmHiUseWalk at hwk; rw [ite_eq_right (by omega : ¬ r < 2)] at hwk
  have hrow := htab.hrows r hr2 hrk; cases hfind : rkmFindAnchor r anchors with
  | none => simp [hfind] at hwk
  | some a0 =>
    rw [hfind] at hrow; have ha_eq : a = a0 := by simp [a, rkmHiAnchorAt, hfind]
    rw [← ha_eq] at hrow; obtain ⟨har, heval, hact⟩ := hrow
    have hsh := List.all_eq_true.mp hshape a (ha_eq ▸ rkmHi_findAnchor_mem hfind)
    unfold rkmHiAnchorShape at hsh
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, and_assoc] at hsh
    exact ⟨har, heval, ⟨hsh.1, hsh.2.1, hsh.2.2.1⟩, hact, hsh.2.2.2.1, hsh.2.2.2.2.1, hsh.2.2.2.2.2⟩
private theorem rkmHi_active_sum_and_drift {m lTableMax r : ℕ} {vPot lSegs tauSegs row : List ℕ}
    (hact : RampKickActiveValid m lTableMax r vPot lSegs tauSegs row) :
    let d := min (rkmLastNat 0 lSegs * m) r
    let pLo := fun w ↦ if 1 ≤ w ∧ w ≤ d then (row.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
    let c := ∑ w ∈ Finset.Icc 1 d, pLo w
    0 < c ∧ (rkmWeightedTau9 lSegs tauSegs : ℝ) / 1000000000 +
      (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) +
      (1 - c) * ((muxRunningCap vPot r : ℝ) / wdScaleR) < (vPot.getD r 0 : ℝ) / wdScaleR := by
  intro d pLo c; obtain ⟨_, _, _, hr_len, hsum_pos, htot_le, hlt_nat⟩ := hact
  have hc_eq : c = (altSumNat row : ℝ) / 1000000000000 := by
    dsimp only [c, pLo]; rw [rkmHi_sum_Icc_eq_range, rkmHi_altSum_eq_range d row hr_len,
      Nat.cast_sum, Finset.sum_div]; refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt := Finset.mem_range.mp hj; rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  have hc_pos : 0 < c := by rw [hc_eq]; exact div_pos (Nat.cast_pos.mpr hsum_pos) (by positivity)
  have hhit_eq : (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) =
      ((∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0 : ℕ) : ℝ) /
        (1000000000000 * wdScaleR) := by
    dsimp only [pLo]; rw [rkmHi_sum_Icc_eq_range, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_; have hj_lt := Finset.mem_range.mp hj
    rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel,
      show r - (j + 1) = r - 1 - j by omega, Nat.cast_mul]; ring
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  rw [hhit_eq, show 1 - c = ((1000000000000 - altSumNat row : ℕ) : ℝ) / 1000000000000 by
    rw [hc_eq, Nat.cast_sub htot_le]; ring]
  set W9 : ℕ := rkmWeightedTau9 lSegs tauSegs
  set H27 : ℕ := ∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0
  set D12 : ℕ := 1000000000000 - altSumNat row; set C15 : ℕ := muxRunningCap vPot r
  have hlt_R : (W9 : ℝ) * 1000000000000000000 + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) <
      1000000000000 * (vPot.getD r 0 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      (by exact_mod_cast hlt_nat : ((W9 * 1000000000000000000 + H27 + D12 * C15 : ℕ) : ℝ) <
        ((1000000000000 * vPot.getD r 0 : ℕ) : ℝ))
  have hS : (0 : ℝ) < 1000000000000 * wdScaleR := by rw [hB_eq]; positivity
  have hl : ((W9 : ℝ) / 1000000000 + (H27 : ℝ) / (1000000000000 * wdScaleR) +
      ((D12 : ℝ) / 1000000000000) * ((C15 : ℝ) / wdScaleR)) * (1000000000000 * wdScaleR) =
      (W9 : ℝ) * 1000000000000000000 + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) := by rw [hB_eq]; ring
  have hr : ((vPot.getD r 0 : ℝ) / wdScaleR) * (1000000000000 * wdScaleR) =
      1000000000000 * (vPot.getD r 0 : ℝ) := by rw [hB_eq]; ring
  exact ⟨hc_pos, lt_of_mul_lt_mul_right (by linarith) hS.le⟩
private theorem rkmHi_endL_eq (n m r : ℕ) (a : RampKickAnchor) (hlen1 : 1 ≤ a.lSegs.length)
    (hl : a.lSegs.length = a.tauSegs.length ∧ a.lSegs.length = a.nsubSegs.length ∧
      a.lSegs.length = a.masks.length) :
    rkmEndL (a.lSegs.headD 1)
      (rkmBuildTailSegs n m r a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail) =
      rkmLastNat 0 a.lSegs := by
  rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
  · simp [hl_cons] at hlen1
  · dsimp only [List.headD_cons, List.tail_cons, rkmLastNat]
    exact (rkmLastNat_eq_endL n m r lt lh a.tauSegs.tail a.nsubSegs.tail a.masks.tail
      (by simp [← hl.1, hl_cons]) (by simp [← hl.2.1, hl_cons]) (by simp [← hl.2.2, hl_cons])).symm
private noncomputable def rkmHiBuildSubSpec {m lTableMax lMaxCell : ℕ}
    (hm_grid : m ∈ groverGrid) (hm2 : 2 ≤ m) (hl2 : 2 ≤ lMaxCell) (hl_hi : lMaxCell * m ≤ 65536)
    (vPot : List ℕ) (anchors : List RampKickAnchor)
    (htab : RampKickTableValid m 512 lTableMax true vPot anchors)
    (hshape : rkmHiAnchorsShapeOk lMaxCell anchors = true)
    (hcold2 : rmsCheckColdR2Step m (vPot.getD 2 0) = true) :
    JohnsonRampMuxSparseWalkSpec m 512 lMaxCell where
  hL_max_pos := rkmHi_one_le hl2
  hL_max_hi := hl_hi
  useWalk := rkmHiUseWalk anchors
  useColdR2 := Bool.not (rkmHiUseWalk anchors 2)
  hColdM2 := fun _ ↦ hm2
  hColdL2 := fun _ ↦ hl2
  lInit := fun r ↦ (rkmHiAnchorAt anchors r).lSegs.headD 1
  lEnd := fun r ↦ rkmLastNat 0 (rkmHiAnchorAt anchors r).lSegs
  hlEnd_pos := fun r hr2 hrk hwk ↦ (rkmHi_active_unpack htab hshape hr2 hrk hwk).2.2.2.2.1
  hlEnd_le := fun r hr2 hrk hwk ↦ (rkmHi_active_unpack htab hshape hr2 hrk hwk).2.2.2.2.2.1
  n0 := altN0
  hn0 := by unfold altN0; norm_num
  ops0 := fun n r ↦ let a := rkmHiAnchorAt anchors r
    rkmSegOps n m r (a.lSegs.headD 1) (a.tauSegs.headD 0) (a.nsubSegs.headD 0) (a.masks.headD [])
  segsTail := fun n r ↦ let a := rkmHiAnchorAt anchors r
    rkmToRmsSegs (rkmBuildTailSegs n m r a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail)
  hsegs_mono := fun n r _ hr2 hrk hwk ↦ (rmsSegsMono_rkmToRmsSegs _ _).mpr
    (rkmHiMono_build n m r _ _ _ _ _ (rkmHi_active_unpack htab hshape hr2 hrk hwk).2.2.2.2.2.2)
  hlEnd_eq := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hl, hact, _, _, _⟩ := rkmHi_active_unpack htab hshape hr2 hrk hwk
    rw [rmsEndL_rkmToRmsSegs]; exact rkmHi_endL_eq n m r (rkmHiAnchorAt anchors r) hact.1 hl
  V := fun r ↦ (vPot.getD r 0 : ℝ) / wdScaleR
  hV0 := by rw [htab.hv0, Nat.cast_zero, zero_div]
  hV_nonneg := fun _ _ ↦ by unfold wdScaleR wdScale; positivity
  vCap := fun r ↦ (muxRunningCap vPot r : ℝ) / wdScaleR
  hvCap_ge := fun j r hjr _ ↦ div_le_div_of_nonneg_right
    (by exact_mod_cast muxRunningCap_ge_of_le vPot hjr) (by unfold wdScaleR wdScale; positivity)
  hV_cold2 := fun _ _ ↦ rmsCheckColdR2Step_sound hm_grid hm2 hcold2
  hV_eig := fun r hr1 hrk hor ↦ checkEigStep_sound (by
    rcases hor with rfl | ⟨huw, hncold⟩
    · exact htab.heig1
    · by_cases hr2 : r < 2
      · obtain rfl : r = 1 := by omega
        exact htab.heig1
      · have huw' := huw; unfold rkmHiUseWalk at huw'; rw [ite_eq_right hr2] at huw'
        have hrow := htab.hrows r (by omega) hrk; cases hfind : rkmFindAnchor r anchors with
        | some _ => simp [hfind] at huw'
        | none =>
          rw [hfind] at hrow; rcases hrow with ⟨rfl, _, _⟩ | heig
          · exact False.elim (hncold ⟨rfl, by rw [huw]; rfl⟩)
          · exact heig)
  pLo := fun r w ↦ let a := rkmHiAnchorAt anchors r; let d := min (rkmLastNat 0 a.lSegs * m) r
    if 1 ≤ w ∧ w ≤ d then (a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
  hpLo_nonneg := fun _ _ ↦ by dsimp only; split_ifs <;> positivity
  hpLo_sum_pos := fun r hr2 hrk hwk ↦
    (rkmHi_active_sum_and_drift (rkmHi_active_unpack htab hshape hr2 hrk hwk).2.2.2.1).1
  tauWeighted := fun r ↦ (rkmWeightedTau9 (rkmHiAnchorAt anchors r).lSegs
    (rkmHiAnchorAt anchors r).tauSegs : ℝ) / 1000000000
  C_step := 134348800
  hqcount_le := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, ⟨hl_t, _, _⟩, hact, _, _, _⟩ := rkmHi_active_unpack htab hshape hr2 hrk hwk
    obtain ⟨hlen1, hlen8, hsegB, _, _, _, _⟩ := hact
    dsimp only; set a := rkmHiAnchorAt anchors r; rw [rmsSegsQueryCount_rkmToRmsSegs]
    have hall_le := rkmCheckSegBounds_mem_le lTableMax a.lSegs a.tauSegs 1 hsegB
    have hlTab_hi : lTableMax ≤ 8192 := by
      have h1 := Nat.mul_le_mul_left lTableMax htab.hm1; have hhi := htab.hlMax_hi; omega
    have hC_nat : 2 * a.lSegs.length * lTableMax * (r + 1) ≤ 134348800 :=
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlen8) hlTab_hi)
        (by omega : r + 1 ≤ 513)).trans (by norm_num)
    have hC_real : 2 * (a.lSegs.length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) ≤ 134348800 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (by exact_mod_cast hC_nat :
        ((2 * a.lSegs.length * lTableMax * (r + 1) : ℕ) : ℝ) ≤ 134348800)
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · rcases ht_cons : a.tauSegs with _ | ⟨th, tt⟩
      · simp [hl_cons, ht_cons] at hl_t
      · rw [hl_cons] at hall_le hC_real; dsimp only [List.headD_cons, List.tail_cons]
        linarith [rkmSegsQueryCount_build_le n m r lTableMax lh th (a.nsubSegs.headD 0)
          (a.masks.headD []) lt tt a.nsubSegs.tail a.masks.tail (hall_le lh List.mem_cons_self).2
          (fun x hx ↦ (hall_le x (List.mem_cons_of_mem lh hx)).2)]
  hpLo_le := fun n r hn0 hr2 hrk hwk R hR w hw ↦ by
    obtain ⟨_, heval, hl, hact, _, _, _⟩ := rkmHi_active_unpack htab hshape hr2 hrk hwk
    dsimp only; set a := rkmHiAnchorAt anchors r; rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
    rw [ite_eq_left ⟨hw1, hwd⟩, symHitProb_evalRampMuxSegs_rkmToRmsSegs]
    have hne : rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks ≠ [] := by
      rw [heval]; intro hnil; have hpos := hact.2.2.2.2.1; rw [hnil] at hpos
      simp [altSumNat] at hpos
    have hsound := (rkmEvalT16Lo12_sound hn0 hne hR).2.2.2.2.2
    rw [heval] at hsound; exact hsound w (by rwa [rkmHi_endL_eq n m r a hact.1 hl])
  hdrift_ramp_lt := fun r hr2 hrk hwk ↦
    (rkmHi_active_sum_and_drift (rkmHi_active_unpack htab hshape hr2 hrk hwk).2.2.2.1).2
private def rkmHiLTableMax (m : ℕ) : ℕ :=
  if m == 128 then 64 else if m == 256 then 32 else if m == 512 then 16 else 8
private def rkmHiVPot (m : ℕ) : List ℕ := if m == 128 then rkmVPotHi_m128 else
  if m == 256 then rkmVPotHi_m256 else if m == 512 then rkmVPotHi_m512 else rkmVPotHi_m1024
private def rkmHiAnchors (m : ℕ) : List RampKickAnchor := if m == 128 then rkmAnchorsHi_m128 else
  if m == 256 then rkmAnchorsHi_m256 else if m == 512 then rkmAnchorsHi_m512 else rkmAnchorsHi_m1024
private def rkmHiWinWLo (m : ℕ) : ℕ := if m == 128 then 931 else
  if m == 256 then 979 else if m == 512 then 985 else 989
private def rkmHiWinVR (m : ℕ) : ℕ := if m == 128 then 270701178829027 else
  if m == 256 then 135968266483801 else if m == 512 then 70067540986927 else 37167068758554
private def rkmHiWinNum (m : ℕ) : ℕ := if m == 128 then 62336347654 else
  if m == 256 then 44279607682 else if m == 512 then 32269934052 else 24207754734
private def rkmHiWinDen (m : ℕ) : ℕ := if m == 128 then 1000000000000 else
  if m == 256 then 1000000000000 else if m == 512 then 1000000000000 else 1000000000000
private def rkmHiWinAnchor (m : ℕ) : RampKickAnchor := if m == 128 then rkmWinAnchorHi_m128 else
  if m == 256 then rkmWinAnchorHi_m256 else if m == 512 then rkmWinAnchorHi_m512 else
    rkmWinAnchorHi_m1024
private theorem rkmHi_glue_ok :
    let c := rkmCheckCapLe; let s := rkmHiAnchorsShapeOk; let r := rmsCheckColdR2Step
    (c rkmVPotHi_m128 rkmWinCap59_m128 = true ∧ c rkmVPotHi_m256 rkmWinCap59_m256 = true ∧
      c rkmVPotHi_m512 rkmWinCap59_m512 = true ∧ c rkmVPotHi_m1024 rkmWinCap59_m1024 = true) ∧
    (s 16 rkmAnchorsHi_m128 = true ∧ s 8 rkmAnchorsHi_m256 = true ∧
      s 4 rkmAnchorsHi_m512 = true ∧ s 2 rkmAnchorsHi_m1024 = true) ∧
    (r 128 (rkmVPotHi_m128.getD 2 0) = true ∧ r 256 (rkmVPotHi_m256.getD 2 0) = true ∧
      r 512 (rkmVPotHi_m512.getD 2 0) = true ∧ r 1024 (rkmVPotHi_m1024.getD 2 0) = true) := by
  decide +kernel
private lemma rkmHi_toWinSpec {m k kSub lTab lMax wLo vR num den : ℕ} {vPot : List ℕ}
    {topA : RampKickAnchor} (h : RkmWinTopStepValid m k kSub lTab lMax wLo vR num den vPot topA) :
    RkmWinAnchorSpec m k kSub lTab lMax wLo vR num den vPot topA :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17⟩
private abbrev rkmHiIsK512 (k : ℕ) : Prop :=
  k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128 ∨ k = 256 ∨ k = 512
private abbrev RkmHiCellCert (m k : ℕ) (vPot : List ℕ) (anchors : List RampKickAnchor) : Prop :=
  2 ≤ johnsonRampKickMuxHiCellLMax m k ∧ johnsonRampKickMuxHiCellLMax m k * m ≤ 65536 ∧
    rkmCheckAnchorsLMax k (johnsonRampKickMuxHiCellLMax m k) anchors = true ∧
    ∃ num den : ℕ, relCostJohnsonRampKickMuxHi m k = NNRat.divNat num den ∧
      checkAltBound12 m k (vPot.getD k 0) num den = true
private lemma hc {m k num den : ℕ} {vPot : List ℕ} {anc : List RampKickAnchor}
    (hb : checkAltBound12 m k (vPot.getD k 0) num den = true)
    (hl : rkmCheckAnchorsLMax k (johnsonRampKickMuxHiCellLMax m k) anc = true)
    (h13 : (Nat.ble 2 (johnsonRampKickMuxHiCellLMax m k) &&
      Nat.ble (johnsonRampKickMuxHiCellLMax m k * m) 65536) = true := by rfl)
    (hr : relCostJohnsonRampKickMuxHi m k = NNRat.divNat num den := by rfl) :
    RkmHiCellCert m k vPot anc := by
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h13
  exact ⟨h13.1, h13.2, hl, ⟨num, den, hr, hb⟩⟩
private lemma rkmHi_cases {m k : ℕ} (h : isJohnsonRampKickMuxHiCell m k = true) :
    (m = 128 ∨ m = 256 ∨ m = 512 ∨ m = 1024) ∧ (rkmHiIsK512 k ∨ k = 1024) := by
  unfold isJohnsonRampKickMuxHiCell at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ⟨hm, hk⟩; exact ⟨by tauto, by unfold rkmHiIsK512; tauto⟩
private lemma rkmHiK {i : ℕ} (h1 : Nat.ble (i + 1) 11 = true) (h2 : Nat.ble (2 ^ i) 512 = true) :
    2 ^ i ∈ groverGrid ∧ 2 ^ i ≤ 512 := ⟨rkmHi_pow2_grid h1, Nat.ble_eq.mp h2⟩
private lemma rkmHi_k512_props {k : ℕ} (hk : rkmHiIsK512 k) : k ∈ groverGrid ∧ k ≤ 512 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [rkmHiK (i := 1) rfl rfl, rkmHiK (i := 2) rfl rfl, rkmHiK (i := 3) rfl rfl,
    rkmHiK (i := 4) rfl rfl, rkmHiK (i := 5) rfl rfl, rkmHiK (i := 6) rfl rfl,
    rkmHiK (i := 7) rfl rfl, rkmHiK (i := 8) rfl rfl, rkmHiK (i := 9) rfl rfl]
private lemma rkmHi_sub512_props {m k : ℕ} (h : isJohnsonRampKickMuxHiCell m k = true)
    (hk_ne : ¬ k = 1024) : m ∈ groverGrid ∧ k ∈ groverGrid ∧ k ≤ 512 ∧ 2 ≤ m ∧
      RampKickTableValid m 512 (rkmHiLTableMax m) true (rkmHiVPot m) (rkmHiAnchors m) ∧
      RkmHiCellCert m k (rkmHiVPot m) (rkmHiAnchors m) := by
  obtain ⟨hm, hk_or⟩ := rkmHi_cases h; have hk := hk_or.resolve_right hk_ne
  obtain ⟨hk_g, hk_hi⟩ := rkmHi_k512_props hk; rcases hm with rfl | rfl | rfl | rfl
  · refine ⟨rkmHi_pow2_grid (i := 7) rfl, hk_g, hk_hi, Nat.ble_eq.mp rfl, rkmValidHi_m128, ?_⟩
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hc rkmBoundHi_m128_k2 rkmCellLMax2Hi_m128_k2
      , hc rkmBoundHi_m128_k4 rkmCellLMax2Hi_m128_k4, hc rkmBoundHi_m128_k8 rkmCellLMax2Hi_m128_k8
      , hc rkmBoundHi_m128_k16 rkmCellLMax2Hi_m128_k16
      , hc rkmBoundHi_m128_k32 rkmCellLMax2Hi_m128_k32
      , hc rkmBoundHi_m128_k64 rkmCellLMax2Hi_m128_k64
      , hc rkmBoundHi_m128_k128 rkmCellLMax2Hi_m128_k128
      , hc rkmBoundHi_m128_k256 rkmCellLMax2Hi_m128_k256
      , hc rkmBoundHi_m128_k512 rkmCellLMax2Hi_m128_k512]
  · refine ⟨rkmHi_pow2_grid (i := 8) rfl, hk_g, hk_hi, Nat.ble_eq.mp rfl, rkmValidHi_m256, ?_⟩
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hc rkmBoundHi_m256_k2 rkmCellLMax2Hi_m256_k2
      , hc rkmBoundHi_m256_k4 rkmCellLMax2Hi_m256_k4, hc rkmBoundHi_m256_k8 rkmCellLMax2Hi_m256_k8
      , hc rkmBoundHi_m256_k16 rkmCellLMax2Hi_m256_k16
      , hc rkmBoundHi_m256_k32 rkmCellLMax2Hi_m256_k32
      , hc rkmBoundHi_m256_k64 rkmCellLMax2Hi_m256_k64
      , hc rkmBoundHi_m256_k128 rkmCellLMax2Hi_m256_k128
      , hc rkmBoundHi_m256_k256 rkmCellLMax2Hi_m256_k256
      , hc rkmBoundHi_m256_k512 rkmCellLMax2Hi_m256_k512]
  · refine ⟨rkmHi_pow2_grid (i := 9) rfl, hk_g, hk_hi, Nat.ble_eq.mp rfl, rkmValidHi_m512, ?_⟩
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hc rkmBoundHi_m512_k2 rkmCellLMax2Hi_m512_k2
      , hc rkmBoundHi_m512_k4 rkmCellLMax2Hi_m512_k4, hc rkmBoundHi_m512_k8 rkmCellLMax2Hi_m512_k8
      , hc rkmBoundHi_m512_k16 rkmCellLMax2Hi_m512_k16
      , hc rkmBoundHi_m512_k32 rkmCellLMax2Hi_m512_k32
      , hc rkmBoundHi_m512_k64 rkmCellLMax2Hi_m512_k64
      , hc rkmBoundHi_m512_k128 rkmCellLMax2Hi_m512_k128
      , hc rkmBoundHi_m512_k256 rkmCellLMax2Hi_m512_k256
      , hc rkmBoundHi_m512_k512 rkmCellLMax2Hi_m512_k512]
  · refine ⟨rkmHi_pow2_grid (i := 10) rfl, hk_g, hk_hi, Nat.ble_eq.mp rfl, rkmValidHi_m1024, ?_⟩
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hc rkmBoundHi_m1024_k2 rkmCellLMax2Hi_m1024_k2
      , hc rkmBoundHi_m1024_k4 rkmCellLMax2Hi_m1024_k4
      , hc rkmBoundHi_m1024_k8 rkmCellLMax2Hi_m1024_k8
      , hc rkmBoundHi_m1024_k16 rkmCellLMax2Hi_m1024_k16
      , hc rkmBoundHi_m1024_k32 rkmCellLMax2Hi_m1024_k32
      , hc rkmBoundHi_m1024_k64 rkmCellLMax2Hi_m1024_k64
      , hc rkmBoundHi_m1024_k128 rkmCellLMax2Hi_m1024_k128
      , hc rkmBoundHi_m1024_k256 rkmCellLMax2Hi_m1024_k256
      , hc rkmBoundHi_m1024_k512 rkmCellLMax2Hi_m1024_k512]
private abbrev RkmHiWinTuple (m k : ℕ) : Prop :=
  m ∈ groverGrid ∧ k ∈ groverGrid ∧ 2 ≤ k ∧ rkmHiLTableMax m ≤ 8192 ∧ 2 ≤ m ∧
    2 ≤ johnsonRampKickMuxHiCellLMax m k ∧ johnsonRampKickMuxHiCellLMax m k * m ≤ 65536 ∧
    RampKickTableValid m 512 (rkmHiLTableMax m) true (rkmHiVPot m) (rkmHiAnchors m) ∧
    rkmHiAnchorsShapeOk (johnsonRampKickMuxHiCellLMax m k) (rkmHiAnchors m) = true ∧
    rmsCheckColdR2Step m ((rkmHiVPot m).getD 2 0) = true ∧
    RkmWinAnchorSpec m k 512 (rkmHiLTableMax m) (johnsonRampKickMuxHiCellLMax m k)
      (rkmHiWinWLo m) (rkmHiWinVR m) (rkmHiWinNum m) (rkmHiWinDen m) (rkmHiVPot m) (rkmHiWinAnchor
        m)
    ∧ relCostJohnsonRampKickMuxHi m k = NNRat.divNat (rkmHiWinNum m) (rkmHiWinDen m)
private lemma rkmHi_win_props {m k : ℕ} (h : isJohnsonRampKickMuxHiCell m k = true)
    (hk : k = 1024) : RkmHiWinTuple m k := by
  subst hk; obtain ⟨hm, _⟩ := rkmHi_cases h; obtain ⟨gc, gs, gd⟩ := rkmHi_glue_ok
  have hk_g : 1024 ∈ groverGrid := rkmHi_pow2_grid (i := 10) rfl
  have b : ∀ {a c : ℕ}, Nat.ble a c = true → a ≤ c := fun h0 ↦ Nat.ble_eq.mp h0
  rcases hm with rfl | rfl | rfl | rfl
  exacts [⟨rkmHi_pow2_grid (i := 7) rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, rkmValidHi_m128,
      gs.1, gd.1, rkmHi_toWinSpec (rkmWinTopOfCapHi_m128 gc.1), rfl⟩,
    ⟨rkmHi_pow2_grid (i := 8) rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, rkmValidHi_m256,
      gs.2.1, gd.2.1, rkmHi_toWinSpec (rkmWinTopOfCapHi_m256 gc.2.1), rfl⟩,
    ⟨rkmHi_pow2_grid (i := 9) rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, rkmValidHi_m512,
      gs.2.2.1, gd.2.2.1, rkmHi_toWinSpec (rkmWinTopOfCapHi_m512 gc.2.2.1), rfl⟩,
    ⟨rkmHi_pow2_grid (i := 10) rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, rkmValidHi_m1024,
      gs.2.2.2, gd.2.2.2, rkmHi_toWinSpec (rkmWinTopOfCapHi_m1024 gc.2.2.2), rfl⟩]
private noncomputable def rkmHiWinSubSpec {m k : ℕ} (h : isJohnsonRampKickMuxHiCell m k = true)
    (hk : k = 1024) : JohnsonRampMuxSparseWalkSpec m 512 (johnsonRampKickMuxHiCellLMax m k) :=
  let pw := rkmHi_win_props h hk
  rkmHiBuildSubSpec pw.1 pw.2.2.2.2.1 pw.2.2.2.2.2.1 pw.2.2.2.2.2.2.1 (rkmHiVPot m) (rkmHiAnchors m)
    pw.2.2.2.2.2.2.2.1 pw.2.2.2.2.2.2.2.2.1 pw.2.2.2.2.2.2.2.2.2.1
private theorem rkmHi_n0_le {m k : ℕ} (h : isJohnsonRampKickMuxHiCell m k = true)
    (hk : k = 1024) : (rkmHiWinSubSpec h hk).n0 ≤ altN0 := Nat.le_refl altN0
private theorem rkmHi_hv_sub {m k : ℕ} (h : isJohnsonRampKickMuxHiCell m k = true)
    (hk : k = 1024) :
    ∀ j ≤ 512, (rkmHiWinSubSpec h hk).V j = ((rkmHiVPot m).getD j 0 : ℝ) / wdScaleR := fun _ _ ↦ rfl
private noncomputable def rkmHiWinArm {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ) {m k : ℕ}
    (h : isJohnsonRampKickMuxHiCell m k = true) (hk : k = 1024) :
    OracleDynamicCircuit (Unitary (2 ^ johnsonRampKickMuxHiQubits n m k)) Var
      (johnsonRampKickMuxHiQubits n m k) ((n + 1) * m) :=
  let pw := rkmHi_win_props h hk
  rkmWinCellCircuit res pw.1 pw.2.1 pw.2.2.1 pw.2.2.2.1 (rkmHiWinSubSpec h hk)
    (rkmHi_n0_le h hk) (rkmHiVPot m) (rkmHi_hv_sub h hk) (rkmHiWinAnchor m)
    pw.2.2.2.2.2.2.2.2.2.2.1 n
private noncomputable def rkmHiSubArm {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ) {m k : ℕ}
    (h : isJohnsonRampKickMuxHiCell m k = true) (hk : ¬ k = 1024) :
    OracleDynamicCircuit (Unitary (2 ^ johnsonRampKickMuxHiQubits n m k)) Var
      (johnsonRampKickMuxHiQubits n m k) ((n + 1) * m) :=
  let p := rkmHi_sub512_props h hk
  rkmCellCircuit res p.1 p.2.1 (rkmHiVPot m) (rkmHiAnchors m) p.2.2.1 (fun _ ↦ p.2.2.2.1)
    (fun _ ↦ p.2.2.2.2.2.1) (rkmHi_one_le p.2.2.2.2.2.1) p.2.2.2.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.2.2.1 n
/-- Dynamic circuit dispatching all `40` `RampKickMuxHi` cells. -/
noncomputable def findAllJohnsonRampKickMuxHiCircuit {Var : Type} [DecidableEq Var] (res : Var)
    (n m k : ℕ) : OracleDynamicCircuit (Unitary (2 ^ johnsonRampKickMuxHiQubits n m k)) Var
      (johnsonRampKickMuxHiQubits n m k) ((n + 1) * m) :=
  if h : isJohnsonRampKickMuxHiCell m k = true then
    if hk : k = 1024 then rkmHiWinArm res n h hk else rkmHiSubArm res n h hk
  else .skip
/-- Exact probability-`1` recovery of `S` across all `40` supported cells. -/
theorem johnsonRampKickMuxHi_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n) (hcell : isJohnsonRampKickMuxHiCell m k = true)
    (hkN : k ≤ 2 ^ n) (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃(⊤ : CQAssertion (Store Var) (2 ^ johnsonRampKickMuxHiQubits n m k))⦄
    (QProg.qSet ;; (findAllJohnsonRampKickMuxHiCircuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S)⦄ := by
  have hS' : S ∈ groverTargetSets n k := by rwa [rkmHi_targetSets_eq]
  unfold findAllJohnsonRampKickMuxHiCircuit; rw [dite_eq_left hcell, ← rkmHi_oracle_eq]
  by_cases hk : k = 1024
  · have pw := rkmHi_win_props hcell hk; rw [dite_eq_left hk]
    exact rkmWinCell_correctness res pw.1 pw.2.1 pw.2.2.1 pw.2.2.2.1 (rkmHiWinSubSpec hcell hk)
      (rkmHi_n0_le hcell hk) (rkmHiVPot m) (rkmHi_hv_sub hcell hk) (rkmHiWinAnchor m)
      pw.2.2.2.2.2.2.2.2.2.2.1 hn hkN hS'
  · have hp := rkmHi_sub512_props hcell hk; rw [dite_eq_right hk]
    exact rkmCell_correctness res hp.1 hp.2.1 (rkmHiVPot m) (rkmHiAnchors m) hp.2.2.1
      (fun _ ↦ hp.2.2.2.1) (fun _ ↦ hp.2.2.2.2.2.1) (rkmHi_one_le hp.2.2.2.2.2.1) hp.2.2.2.2.2.2.1
      hp.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hn hkN hS'
/-- Asymptotic uniform-average relative-cost bound across all `40` supported cells. -/
theorem johnsonRampKickMuxHi_relCost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hcell : isJohnsonRampKickMuxHiCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
        CostBound (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
          (QProg.qSet ;; (findAllJohnsonRampKickMuxHiCircuit res n m k).compile QProg.qAssign
            (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
        ((relCostJohnsonRampKickMuxHi m k : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  by_cases hk : k = 1024
  · have pw := rkmHi_win_props hcell hk
    obtain ⟨n₁, hn₁⟩ := rkmWinCell_rel_cost (Var := Var) res pw.1 pw.2.1 pw.2.2.1 pw.2.2.2.1
      (rkmHiWinSubSpec hcell hk) (rkmHi_n0_le hcell hk) (rkmHiVPot m) (rkmHi_hv_sub hcell hk)
      (rkmHiWinAnchor m) pw.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
    refine ⟨q, fun S hS ↦ ?_,
      by rw [← rkmHi_targetSets_eq, ← rkmHi_vanilla_eq, pw.2.2.2.2.2.2.2.2.2.2.2]; exact hsum⟩
    unfold findAllJohnsonRampKickMuxHiCircuit
    rw [dite_eq_left hcell, dite_eq_left hk, ← rkmHi_oracle_eq]
    exact hq S (by rwa [rkmHi_targetSets_eq])
  · have hp := rkmHi_sub512_props hcell hk
    obtain ⟨n₁, hn₁⟩ := rkmCell_rel_cost (Var := Var) res hp.1 hp.2.1 (rkmHiVPot m) (rkmHiAnchors m)
      hp.2.2.1 (fun _ ↦ hp.2.2.2.1) (fun _ ↦ hp.2.2.2.2.2.1) (rkmHi_one_le hp.2.2.2.2.2.1)
      hp.2.2.2.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2
    refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
    refine ⟨q, fun S hS ↦ ?_, by rw [← rkmHi_targetSets_eq, ← rkmHi_vanilla_eq]; exact hsum⟩
    unfold findAllJohnsonRampKickMuxHiCircuit
    rw [dite_eq_left hcell, dite_eq_right hk, ← rkmHi_oracle_eq]
    exact hq S (by rwa [rkmHi_targetSets_eq])
end
end QuantumComputation.Specs.GroverFindAll.FindAllJohnsonRampKickMuxHi
