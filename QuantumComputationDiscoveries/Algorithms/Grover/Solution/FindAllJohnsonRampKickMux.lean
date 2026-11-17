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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampMuxWindowedQHL
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxCert0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxCert1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxCert2

/-
# Multi-Segment Width-Ramped + Prefix-Kick Router Arm (`FindAllJohnsonRampKickMux`)

QHL-verified specialist module packaging all `100` `(m, k) ∈ {2..1024} × {2..1024}` cells
of the width-ramped + prefix-kick `RampKickMux` family.
-/

namespace QuantumComputation.Specs.GroverFindAll.FindAllJohnsonRampKickMux

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m ∈ {2..1024}`, `k ∈ {2..1024}`). -/
def isJohnsonRampKickMuxCell (m k : ℕ) : Bool :=
  (((m == 2) || (m == 4) || (m == 8) || (m == 16) || (m == 32) || (m == 64)) &&
   ((k == 2) || (k == 4) || (k == 8) || (k == 16) || (k == 32) ||
    (k == 64) || (k == 128) || (k == 256) || (k == 512) || (k == 1024))) ||
  (((m == 512) || (m == 1024)) && ((k == 64) || (k == 128)))

/-- Per-cell max block-multiplexing factor `L_{\max}(m, k) ≥ 2` across `100` cells. -/
def johnsonRampKickMuxCellLMax (m k : ℕ) : ℕ :=
  if m == 2 && k == 2 then 2
  else if m == 2 && k == 4 then 3
  else if m == 2 && k == 8 then 6
  else if m == 2 && k == 16 then 12
  else if m == 2 && k == 32 then 30
  else if m == 2 && k == 64 then 58
  else if m == 2 && k == 128 then 112
  else if m == 2 && k == 256 then 224
  else if m == 2 && k == 512 then 448
  else if m == 2 && k == 1024 then 992
  else if m == 4 && k == 2 then 2
  else if m == 4 && k == 4 then 2
  else if m == 4 && k == 8 then 3
  else if m == 4 && k == 16 then 7
  else if m == 4 && k == 32 then 14
  else if m == 4 && k == 64 then 29
  else if m == 4 && k == 128 then 59
  else if m == 4 && k == 256 then 112
  else if m == 4 && k == 512 then 224
  else if m == 4 && k == 1024 then 496
  else if m == 8 && k == 2 then 2
  else if m == 8 && k == 4 then 2
  else if m == 8 && k == 8 then 2
  else if m == 8 && k == 16 then 3
  else if m == 8 && k == 32 then 7
  else if m == 8 && k == 64 then 15
  else if m == 8 && k == 128 then 30
  else if m == 8 && k == 256 then 56
  else if m == 8 && k == 512 then 112
  else if m == 8 && k == 1024 then 248
  else if m == 16 && k == 2 then 2
  else if m == 16 && k == 4 then 2
  else if m == 16 && k == 8 then 2
  else if m == 16 && k == 16 then 2
  else if m == 16 && k == 32 then 4
  else if m == 16 && k == 64 then 7
  else if m == 16 && k == 128 then 15
  else if m == 16 && k == 256 then 28
  else if m == 16 && k == 512 then 56
  else if m == 16 && k == 1024 then 124
  else if m == 32 && k == 2 then 2
  else if m == 32 && k == 4 then 2
  else if m == 32 && k == 8 then 2
  else if m == 32 && k == 16 then 2
  else if m == 32 && k == 32 then 2
  else if m == 32 && k == 64 then 4
  else if m == 32 && k == 128 then 7
  else if m == 32 && k == 256 then 14
  else if m == 32 && k == 512 then 28
  else if m == 32 && k == 1024 then 62
  else if m == 64 && k == 2 then 2
  else if m == 64 && k == 4 then 2
  else if m == 64 && k == 8 then 2
  else if m == 64 && k == 16 then 2
  else if m == 64 && k == 32 then 2
  else if m == 64 && k == 64 then 2
  else if m == 64 && k == 128 then 4
  else if m == 64 && k == 256 then 7
  else if m == 64 && k == 512 then 14
  else if m == 64 && k == 1024 then 31
  else if m == 512 && k == 64 then 2
  else if m == 512 && k == 128 then 2
  else if m == 1024 && k == 64 then 2
  else if m == 1024 && k == 128 then 2
  else 2

/-- Total register qubit budget `(L_{\max}(m, k) * m) * (n + 1) + k * n`. -/
abbrev johnsonRampKickMuxQubits (n m k : ℕ) : ℕ :=
  (johnsonRampKickMuxCellLMax m k * m) * (n + 1) + k * n

/-- Certified asymptotic relative-cost profile `c(m, k): ℚ≥0`. -/
def relCostJohnsonRampKickMux (m k : ℕ) : ℚ≥0 :=
  if m == 2 && k == 2 then NNRat.divNat 666702408099 1000000000000
  else if m == 2 && k == 4 then NNRat.divNat 12742745421 20000000000
  else if m == 2 && k == 8 then NNRat.divNat 5934481171 10000000000
  else if m == 2 && k == 16 then NNRat.divNat 560403550241 1000000000000
  else if m == 2 && k == 32 then NNRat.divNat 134002742703 250000000000
  else if m == 2 && k == 64 then NNRat.divNat 129340941427 250000000000
  else if m == 2 && k == 128 then NNRat.divNat 502541605787 1000000000000
  else if m == 2 && k == 256 then NNRat.divNat 246149564199 500000000000
  else if m == 2 && k == 512 then NNRat.divNat 484442444873 1000000000000
  else if m == 2 && k == 1024 then NNRat.divNat 480439805247 1000000000000
  else if m == 4 && k == 2 then NNRat.divNat 591373727057 1000000000000
  else if m == 4 && k == 4 then NNRat.divNat 491273441057 1000000000000
  else if m == 4 && k == 8 then NNRat.divNat 440660813793 1000000000000
  else if m == 4 && k == 16 then NNRat.divNat 204695797907 500000000000
  else if m == 4 && k == 32 then NNRat.divNat 194097160037 500000000000
  else if m == 4 && k == 64 then NNRat.divNat 371419408541 1000000000000
  else if m == 4 && k == 128 then NNRat.divNat 180231023263 500000000000
  else if m == 4 && k == 256 then NNRat.divNat 352233957183 1000000000000
  else if m == 4 && k == 512 then NNRat.divNat 68983620361 200000000000
  else if m == 4 && k == 1024 then NNRat.divNat 340912357990 1000000000000
  else if m == 8 && k == 2 then NNRat.divNat 56675931859 100000000000
  else if m == 8 && k == 4 then NNRat.divNat 78905457981 200000000000
  else if m == 8 && k == 8 then NNRat.divNat 165989567461 500000000000
  else if m == 8 && k == 16 then NNRat.divNat 301027449913 1000000000000
  else if m == 8 && k == 32 then NNRat.divNat 139822325663 500000000000
  else if m == 8 && k == 64 then NNRat.divNat 3328719563 12500000000
  else if m == 8 && k == 128 then NNRat.divNat 10298420831 40000000000
  else if m == 8 && k == 256 then NNRat.divNat 12577459999 50000000000
  else if m == 8 && k == 512 then NNRat.divNat 123027425577 500000000000
  else if m == 8 && k == 1024 then NNRat.divNat 242252100412 1000000000000
  else if m == 16 && k == 2 then NNRat.divNat 270343292017 500000000000
  else if m == 16 && k == 4 then NNRat.divNat 183493293 500000000
  else if m == 16 && k == 8 then NNRat.divNat 52472775503 200000000000
  else if m == 16 && k == 16 then NNRat.divNat 223938727833 1000000000000
  else if m == 16 && k == 32 then NNRat.divNat 40792364523 200000000000
  else if m == 16 && k == 64 then NNRat.divNat 191391236909 1000000000000
  else if m == 16 && k == 128 then NNRat.divNat 183768529881 1000000000000
  else if m == 16 && k == 256 then NNRat.divNat 89491185061 500000000000
  else if m == 16 && k == 512 then NNRat.divNat 875624521 5000000000
  else if m == 16 && k == 1024 then NNRat.divNat 172398243679 1000000000000
  else if m == 32 && k == 2 then NNRat.divNat 263145564179 500000000000
  else if m == 32 && k == 4 then NNRat.divNat 356512540337 1000000000000
  else if m == 32 && k == 8 then NNRat.divNat 240115760559 1000000000000
  else if m == 32 && k == 16 then NNRat.divNat 175687348881 1000000000000
  else if m == 32 && k == 32 then NNRat.divNat 151676589829 1000000000000
  else if m == 32 && k == 64 then NNRat.divNat 34907374341 250000000000
  else if m == 32 && k == 128 then NNRat.divNat 131921117037 1000000000000
  else if m == 32 && k == 256 then NNRat.divNat 63704651089 500000000000
  else if m == 32 && k == 512 then NNRat.divNat 124479706879 1000000000000
  else if m == 32 && k == 1024 then NNRat.divNat 122445401453 1000000000000
  else if m == 64 && k == 2 then NNRat.divNat 129914572989 250000000000
  else if m == 64 && k == 4 then NNRat.divNat 351952643087 1000000000000
  else if m == 64 && k == 8 then NNRat.divNat 1159644599 5000000000
  else if m == 64 && k == 16 then NNRat.divNat 39883149469 250000000000
  else if m == 64 && k == 32 then NNRat.divNat 29690956683 250000000000
  else if m == 64 && k == 64 then NNRat.divNat 51657779091 500000000000
  else if m == 64 && k == 128 then NNRat.divNat 9591647319 100000000000
  else if m == 64 && k == 256 then NNRat.divNat 91283152009 1000000000000
  else if m == 64 && k == 512 then NNRat.divNat 88634562849 1000000000000
  else if m == 64 && k == 1024 then NNRat.divNat 87123384706 1000000000000
  else if m == 512 && k == 64 then NNRat.divNat 220836407 3125000000
  else if m == 512 && k == 128 then NNRat.divNat 25317169393 500000000000
  else if m == 1024 && k == 64 then NNRat.divNat 17364085169 250000000000
  else if m == 1024 && k == 128 then NNRat.divNat 48701150809 1000000000000
  else 1

/-- Cost profile metadata (`n₀ = 80000` with `0` `Classical.choose`). -/
def johnsonRampKickMuxProfile : FindAllCostProfile where
  validCell := isJohnsonRampKickMuxCell
  relCost := relCostJohnsonRampKickMux
  n0 _ _ := 80000

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

section RkmSubSpec
open DickeSol
private theorem rkmb2_ble_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkmb2_ble_true]
private theorem rkmb2_primBlt_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  unfold primNatBlt; rw [← Bool.not_eq_true, rkmb2_ble_true, Nat.add_eq]; omega
private theorem rkmb2_checkListLMax_iff (lMaxCell : ℕ) :
    ∀ xs : List ℕ, rkmCheckListLMax lMaxCell xs = true ↔ ∀ x ∈ xs, 1 ≤ x ∧ x ≤ lMaxCell
  | [] => by simp [rkmCheckListLMax]
  | x :: xs => by
    unfold rkmCheckListLMax
    cases hg : Bool.or (primNatBlt x 1) (primNatBlt lMaxCell x) with
    | true =>
      simp only [Bool.cond_true, Bool.false_eq_true, false_iff, List.mem_cons, not_forall]
      simp only [Bool.or_eq_true, primNatBlt, rkmb2_ble_true, Nat.add_eq] at hg
      exact ⟨x, Or.inl rfl, fun ⟨h1, h2⟩ ↦ by omega⟩
    | false =>
      simp only [Bool.cond_false, rkmb2_checkListLMax_iff lMaxCell xs, List.mem_cons]
      simp only [Bool.or_eq_false_iff, rkmb2_primBlt_false] at hg
      exact ⟨fun hall y hy ↦ hy.elim (fun h ↦ h ▸ hg) (hall y), fun hall y hy ↦ hall y (Or.inr hy)⟩
private theorem rkmb2_findAnchor_mem {r : ℕ} :
    ∀ {anchors : List RampKickAnchor} {a : RampKickAnchor},
      rkmFindAnchor r anchors = some a → a ∈ anchors ∧ a.rAct = r
  | [], _, h => by simp [rkmFindAnchor] at h
  | b :: rest, a, h => by
    unfold rkmFindAnchor at h
    by_cases heq : b.rAct = r
    · rw [ite_eq_left heq] at h; cases Option.some.inj h; exact ⟨List.mem_cons_self, heq⟩
    · rw [ite_eq_right heq] at h; obtain ⟨hm, hr⟩ := rkmb2_findAnchor_mem h
      exact ⟨List.mem_cons_of_mem b hm, hr⟩
private theorem rkmb2_checkAnchorsLMax_mem {k lMaxCell : ℕ} :
    ∀ {anchors : List RampKickAnchor} {a : RampKickAnchor},
      rkmCheckAnchorsLMax k lMaxCell anchors = true →
      a ∈ anchors → a.rAct ≤ k → ∀ x ∈ a.lSegs, 1 ≤ x ∧ x ≤ lMaxCell
  | [], _, _, hm, _ => absurd hm List.not_mem_nil
  | b :: rest, a, h, hm, hrk => by
    unfold rkmCheckAnchorsLMax at h; dsimp only at h
    cases hok : (cond (Nat.ble b.rAct k) (rkmCheckListLMax lMaxCell b.lSegs) true) with
    | false => rw [hok] at h; cases h
    | true =>
      rw [hok, Bool.cond_true] at h
      rcases List.mem_cons.mp hm with rfl | hmem
      · rw [rkmb2_ble_true.mpr hrk, Bool.cond_true] at hok
        exact (rkmb2_checkListLMax_iff lMaxCell a.lSegs).mp hok
      · exact rkmb2_checkAnchorsLMax_mem h hmem hrk
private theorem rkmb2_lastNat_mem : ∀ (xs : List ℕ) (x : ℕ), rkmLastNat x xs ∈ x :: xs
  | [], _ => List.mem_cons_self
  | y :: ys, _ => List.mem_cons_of_mem _ (rkmb2_lastNat_mem ys y)
private theorem rkmb2_cond_fst_ne_zero {b : Bool} {x : ℕ × ℕ × List ℤ}
    (h : (cond b (0, 0, []) x).1 ≠ 0) : x.1 ≠ 0 := by cases b <;> simp_all
private theorem rkmb2_evalSegsLoop_lengths (m lTableMax r : ℕ) :
    ∀ (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool))
      (lPrev dEnd accPad : ℕ) (vec : List ℤ),
      (rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks lPrev dEnd accPad vec).1 ≠ 0 →
      lSegs.length = tauSegs.length ∧ lSegs.length = nsubSegs.length ∧ lSegs.length = masks.length
  | [], [], [], [], _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | [], [], _ :: _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | [], [], [], _ :: _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | lS :: lRest, _ :: tauRest, _ :: nsubRest, _ :: maskRest, _, _, _, _, h => by
    unfold rkmEvalSegsLoop at h; dsimp only at h
    simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h
    have hrec := rkmb2_cond_fst_ne_zero
      (rkmb2_cond_fst_ne_zero (rkmb2_cond_fst_ne_zero (rkmb2_cond_fst_ne_zero h)))
    obtain ⟨h1, h2, h3⟩ :=
      rkmb2_evalSegsLoop_lengths m lTableMax r lRest tauRest nsubRest maskRest lS _ _ _ hrec
    exact ⟨congrArg Nat.succ h1, congrArg Nat.succ h2, congrArg Nat.succ h3⟩
private theorem rkmb2_cond_ne_nil {α : Type} {b : Bool} {xs : List α}
    (h : cond b [] xs ≠ []) : b = false ∧ xs ≠ [] := by cases b <;> simp_all
private theorem rkmb2_evalT16Lo12_ne_nil_lengths {m lTableMax r : ℕ}
    {lSegs tauSegs nsubSegs : List ℕ} {masks : List (List Bool)}
    (hne : rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks ≠ []) :
    lSegs.length = tauSegs.length ∧ lSegs.length = nsubSegs.length ∧
      lSegs.length = masks.length := by
  unfold rkmEvalT16Lo12 at hne; dsimp only at hne
  obtain ⟨_, hne1⟩ := rkmb2_cond_ne_nil hne
  rcases hres : rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks
      1 0 0 [Int.ofNat wdScale] with ⟨dEnd, accPad, vecFinal⟩
  rw [hres] at hne1; dsimp only at hne1
  obtain ⟨hb, _⟩ := rkmb2_cond_ne_nil hne1
  have hd_ne : dEnd ≠ 0 := by
    intro hd0; subst hd0; rw [Bool.or_eq_false_iff] at hb; exact Bool.noConfusion hb.1
  exact rkmb2_evalSegsLoop_lengths m lTableMax r lSegs tauSegs nsubSegs masks
    1 0 0 [Int.ofNat wdScale] (by rw [hres]; exact hd_ne)
private theorem rkmb2_endL_buildTailSegs (n m r : ℕ) :
    ∀ (ls ts ss : List ℕ) (mks : List (List Bool)) (l0 : ℕ),
      ls.length = ts.length → ls.length = ss.length → ls.length = mks.length →
      rkmEndL l0 (rkmBuildTailSegs n m r ls ts ss mks) = rkmLastNat l0 ls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, h2, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h3 => by simp at h3
  | l1 :: ls, _ :: ts, _ :: ss, _ :: mks, _, h1, h2, h3 =>
      rkmb2_endL_buildTailSegs n m r ls ts ss mks l1
        (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3)
private theorem rkmb2_segsMono_buildTailSegs (n m r lTableMax : ℕ) :
    ∀ (ls ts ss : List ℕ) (mks : List (List Bool)) (l0 : ℕ),
      rkmCheckSegBounds lTableMax ls ts l0 = true →
      rkmSegsMono l0 (rkmBuildTailSegs n m r ls ts ss mks)
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, h => by simp [rkmCheckSegBounds] at h
  | _ :: _, _ :: _, [], _, _, _ => by simp [rkmBuildTailSegs, rkmSegsMono]
  | _ :: _, _ :: _, _ :: _, [], _, _ => by simp [rkmBuildTailSegs, rkmSegsMono]
  | l1 :: ls, t1 :: ts, s1 :: ss, mk1 :: mks, l0, h => by
    unfold rkmCheckSegBounds at h
    cases hg : Bool.or (primNatBlt l1 1)
        (Bool.or (primNatBlt l1 l0)
        (Bool.or (primNatBlt lTableMax l1)
        (Bool.or (primNatBlt t1 1) (primNatBlt 4000000000 t1)))) with
    | true => simp [hg] at h
    | false =>
      simp only [hg, Bool.cond_false] at h
      simp only [Bool.or_eq_false_iff, rkmb2_primBlt_false] at hg
      exact ⟨hg.2.1, rkmb2_segsMono_buildTailSegs n m r lTableMax ls ts ss mks l1 h⟩
private theorem rkmb2_checkSegBounds_le (lTableMax : ℕ) : ∀ (ls ts : List ℕ) (lPrev : ℕ),
      rkmCheckSegBounds lTableMax ls ts lPrev = true → ∀ x ∈ ls, x ≤ lTableMax
  | [], [], _, _, _, hx => absurd hx List.not_mem_nil
  | [], _ :: _, _, h, _, _ => by simp [rkmCheckSegBounds] at h
  | _ :: _, [], _, h, _, _ => by simp [rkmCheckSegBounds] at h
  | lS :: lRest, tS :: tRest, lPrev, h, x, hx => by
    unfold rkmCheckSegBounds at h
    cases hg : Bool.or (primNatBlt lS 1)
        (Bool.or (primNatBlt lS lPrev)
        (Bool.or (primNatBlt lTableMax lS)
        (Bool.or (primNatBlt tS 1) (primNatBlt 4000000000 tS)))) with
    | true => simp [hg] at h
    | false =>
      simp only [hg, Bool.cond_false] at h
      simp only [Bool.or_eq_false_iff, rkmb2_primBlt_false] at hg
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hg.2.2.1
      · exact rkmb2_checkSegBounds_le lTableMax lRest tRest lS h x hmem
private theorem rkmb2_sum_range_succ_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ, rkmb2_sum_range_succ_shift f d, Finset.sum_range_succ, add_assoc]
private theorem rkmb2_sum_Icc_one_eq_range (f : ℕ → ℝ) :
    ∀ d : ℕ, (∑ w ∈ Finset.Icc 1 d, f w) = ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by have hset : Finset.Icc (1 : ℕ) 0 = ∅ := by ext x; simp
            rw [hset]; simp
  | d + 1 => by
    have hset : Finset.Icc 1 (d + 1) = insert (d + 1) (Finset.Icc 1 d) := by ext x; simp; omega
    rw [hset, Finset.sum_insert (by simp), rkmb2_sum_Icc_one_eq_range f d, Finset.sum_range_succ]
    ring
private theorem rkmb2_altSumNat_eq_sum_range :
    ∀ (d : ℕ) (xs : List ℕ), xs.length = d → altSumNat xs = ∑ j ∈ Finset.range d, xs.getD j 0
  | 0, [], _ => by simp [altSumNat]
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen
  | d + 1, x :: xs, hlen => by
    rw [rkmb2_sum_range_succ_shift]
    simpa [altSumNat] using congrArg (Nat.add x)
      (rkmb2_altSumNat_eq_sum_range d xs (by simpa using hlen))
private theorem rkmb2_checkColdR2_eq (m v2 : ℕ) :
    rkmCheckColdR2Step m v2 = rmsCheckColdR2Step m v2 := rfl
private def rkmUseWalk (anchors : List RampKickAnchor) (r : ℕ) : Bool :=
  if r < 2 then false else (rkmFindAnchor r anchors).isSome
private def rkmAnchorAt (anchors : List RampKickAnchor) (r : ℕ) : RampKickAnchor :=
  match rkmFindAnchor r anchors with | some a => a | none => ⟨r, [1], [1], [1], [[]], []⟩
private theorem rkmb2_active_unpack {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    {vPot : List ℕ} {anchors : List RampKickAnchor} (hk_le : k ≤ kMax)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true)
    {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k) (hwk : rkmUseWalk anchors r = true) :
    let a := rkmAnchorAt anchors r
    a.rAct = r ∧ rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks = a.rowLo12 ∧
      rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks ≠ [] ∧
      RampKickActiveValid m lTableMax r vPot a.lSegs a.tauSegs a.rowLo12 ∧
      1 ≤ rkmLastNat 0 a.lSegs ∧ rkmLastNat 0 a.lSegs ≤ lMaxCell := by
  intro a; have hnr2 : ¬ r < 2 := by omega
  unfold rkmUseWalk at hwk; rw [ite_eq_right hnr2] at hwk
  have hrow_r := htab.hrows r hr2 (hrk.trans hk_le)
  cases hfind : rkmFindAnchor r anchors with
  | none => simp [hfind] at hwk
  | some a0 =>
    rw [hfind] at hrow_r
    have ha_eq : a = a0 := by simp [a, rkmAnchorAt, hfind]
    rw [← ha_eq] at hrow_r; obtain ⟨har, heval, hact⟩ := hrow_r
    have hne : rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks ≠ [] := by
      rw [heval]; intro hnil; have hpos := hact.2.2.2.2.1
      rw [hnil] at hpos; simp [altSumNat] at hpos
    have hlast : 1 ≤ rkmLastNat 0 a.lSegs ∧ rkmLastNat 0 a.lSegs ≤ lMaxCell := by
      have hlen1 := hact.1
      rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
      · simp [hl_cons] at hlen1
      · have hmem_anc := (rkmb2_findAnchor_mem hfind).1; rw [← ha_eq] at hmem_anc
        have hall_l := rkmb2_checkAnchorsLMax_mem hlcell hmem_anc (har ▸ hrk)
        exact hall_l _ (by rw [hl_cons]; exact rkmb2_lastNat_mem lt lh)
    exact ⟨har, heval, hne, hact, hlast.1, hlast.2⟩
private theorem rkmb2_active_drift_lt {m lTableMax r : ℕ} {vPot lSegs tauSegs row : List ℕ}
    (hact : RampKickActiveValid m lTableMax r vPot lSegs tauSegs row) :
    let d := min (rkmLastNat 0 lSegs * m) r
    let pLo := fun w ↦ if 1 ≤ w ∧ w ≤ d then (row.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
    let c := ∑ w ∈ Finset.Icc 1 d, pLo w
    (rkmWeightedTau9 lSegs tauSegs : ℝ) / 1000000000 +
        (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) +
        (1 - c) * ((muxRunningCap vPot r : ℝ) / wdScaleR) <
      (vPot.getD r 0 : ℝ) / wdScaleR := by
  intro d pLo c
  obtain ⟨_, _, _, hr_len, _, htot_le, hlt_nat⟩ := hact
  have hc_eq : c = (altSumNat row : ℝ) / 1000000000000 := by
    dsimp only [c, pLo]
    rw [rkmb2_sum_Icc_one_eq_range, rkmb2_altSumNat_eq_sum_range d row hr_len,
      Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt : j < d := Finset.mem_range.mp hj
    have hcond : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
    rw [ite_eq_left hcond, Nat.add_sub_cancel]
  have hhit_eq : (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) =
        ((∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0 : ℕ) : ℝ) /
          (1000000000000 * wdScaleR) := by
    dsimp only [pLo]; rw [rkmb2_sum_Icc_one_eq_range, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt : j < d := Finset.mem_range.mp hj
    have hcond : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
    have hsub_idx : r - (j + 1) = r - 1 - j := by omega
    rw [ite_eq_left hcond, Nat.add_sub_cancel, hsub_idx, Nat.cast_mul]; ring
  have hdef_eq : 1 - c = ((1000000000000 - altSumNat row : ℕ) : ℝ) / 1000000000000 := by
    rw [hc_eq, Nat.cast_sub htot_le]; ring
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  rw [hhit_eq, hdef_eq]; set W9 : ℕ := rkmWeightedTau9 lSegs tauSegs
  set H27 : ℕ := ∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0
  set D12 : ℕ := 1000000000000 - altSumNat row; set C15 : ℕ := muxRunningCap vPot r
  set VPot : ℕ := vPot.getD r 0
  have hlt_R : (W9 : ℝ) * (1000000000 * 1000000000) + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) <
        1000000000000 * (VPot : ℝ) := by
    have hlt_n : W9 * (1000000000 * 1000000000) + H27 + D12 * C15 < 1000000000000 * VPot := hlt_nat
    have hc_lt : ((W9 * (1000000000 * 1000000000) + H27 + D12 * C15 : ℕ) : ℝ) <
          ((1000000000000 * VPot : ℕ) : ℝ) := by exact_mod_cast hlt_n
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hc_lt
  set S27 : ℝ := 1000000000000 * wdScaleR
  have hS27_pos : 0 < S27 := by rw [show S27 = 1000000000000 * wdScaleR from rfl, hB_eq]; positivity
  have hlhs_mul : ((W9 : ℝ) / 1000000000 + (H27 : ℝ) / (1000000000000 * wdScaleR) +
        ((D12 : ℝ) / 1000000000000) * ((C15 : ℝ) / wdScaleR)) * S27 =
      (W9 : ℝ) * (1000000000 * 1000000000) + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) := by
    dsimp only [S27]; rw [hB_eq]; ring
  have hrhs_mul : ((VPot : ℝ) / wdScaleR) * S27 = 1000000000000 * (VPot : ℝ) := by
    dsimp only [S27]; rw [hB_eq]; ring
  exact lt_of_mul_lt_mul_right (by linarith) hS27_pos.le
private noncomputable def rkmSubSpecOf {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKickAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true) :
    JohnsonRampMuxSparseWalkSpec m k lMaxCell where
  hL_max_pos := hlcell_pos
  hL_max_hi := hlcell_hi
  useWalk := rkmUseWalk anchors
  useColdR2 := useColdR2 && Bool.not (rkmUseWalk anchors 2) && rkmCheckColdR2Step m (vPot.getD 2 0)
  hColdM2 := fun hc ↦ by
    simp only [Bool.and_eq_true] at hc
    exact hm2_cold hc.1.1
  hColdL2 := fun hc ↦ by
    simp only [Bool.and_eq_true] at hc
    exact hl2_cold hc.1.1
  lInit := fun r ↦ (rkmAnchorAt anchors r).lSegs.headD 1
  lEnd := fun r ↦ rkmLastNat 0 (rkmAnchorAt anchors r).lSegs
  hlEnd_pos := fun r hr2 hrk hwk ↦ (rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk).2.2.2.2.1
  hlEnd_le := fun r hr2 hrk hwk ↦ (rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk).2.2.2.2.2
  n0 := altN0
  hn0 := by unfold altN0; norm_num
  ops0 := fun n r ↦
    let a := rkmAnchorAt anchors r
    rkmSegOps n m r (a.lSegs.headD 1) (a.tauSegs.headD 0) (a.nsubSegs.headD 0) (a.masks.headD [])
  segsTail := fun n r ↦
    let a := rkmAnchorAt anchors r
    rkmToRmsSegs (rkmBuildTailSegs n m r a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail)
  hsegs_mono := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, _, _⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    have hlen1 := hact.1; have hsegB := hact.2.2.1; set a := rkmAnchorAt anchors r
    rw [rmsSegsMono_rkmToRmsSegs]
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · rcases ht_cons : a.tauSegs with _ | ⟨th, tt⟩
      · simp [hl_cons, ht_cons] at hl_t
      · rw [hl_cons, ht_cons] at hsegB; unfold rkmCheckSegBounds at hsegB
        cases hg : Bool.or (primNatBlt lh 1) (Bool.or (primNatBlt lh 1)
            (Bool.or (primNatBlt lTableMax lh)
            (Bool.or (primNatBlt th 1) (primNatBlt 4000000000 th)))) with
        | true => simp [hg] at hsegB
        | false =>
          simp only [hg, Bool.cond_false] at hsegB; dsimp only [List.headD_cons, List.tail_cons]
          exact rkmb2_segsMono_buildTailSegs n m r lTableMax lt tt
            a.nsubSegs.tail a.masks.tail lh hsegB
  hlEnd_eq := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, hl_s, hl_m⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    have hlen1 := hact.1; set a := rkmAnchorAt anchors r; rw [rmsEndL_rkmToRmsSegs]
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · dsimp only [List.headD_cons, List.tail_cons, rkmLastNat]
      exact rkmb2_endL_buildTailSegs n m r lt a.tauSegs.tail a.nsubSegs.tail a.masks.tail lh
        (by simp [← hl_t, hl_cons]) (by simp [← hl_s, hl_cons]) (by simp [← hl_m, hl_cons])
  V := fun r ↦ (vPot.getD r 0 : ℝ) / wdScaleR
  hV0 := by rw [htab.hv0, Nat.cast_zero, zero_div]
  hV_nonneg := fun r _ ↦ by unfold wdScaleR wdScale; positivity
  vCap := fun r ↦ (muxRunningCap vPot r : ℝ) / wdScaleR
  hvCap_ge := fun j r hjr _ ↦ by
    have hB : (0 : ℝ) ≤ wdScaleR := by unfold wdScaleR wdScale; positivity
    exact div_le_div_of_nonneg_right (by exact_mod_cast muxRunningCap_ge_of_le vPot hjr) hB
  hV_cold2 := fun hc _ ↦ by
    simp only [Bool.and_eq_true] at hc
    exact rmsCheckColdR2Step_sound hm_grid (hm2_cold hc.1.1)
      (rkmb2_checkColdR2_eq m (vPot.getD 2 0) ▸ hc.2)
  hV_eig := fun r hr1 hrk hor ↦ by
    refine checkEigStep_sound ?_
    rcases hor with rfl | ⟨huw, hncold⟩
    · exact htab.heig1
    · by_cases hr2 : r < 2
      · have hr_eq1 : r = 1 := by omega
        subst hr_eq1; exact htab.heig1
      · have hr2_ge : 2 ≤ r := by omega
        have huw' := huw; unfold rkmUseWalk at huw'; rw [ite_eq_right hr2] at huw'
        have hrow_r := htab.hrows r hr2_ge (hrk.trans hk_le)
        cases hfind : rkmFindAnchor r anchors with
        | some _ => simp [hfind] at huw'
        | none =>
          rw [hfind] at hrow_r
          rcases hrow_r with ⟨rfl, hc_true, hchk_c⟩ | heig
          · exfalso; apply hncold; refine ⟨rfl, ?_⟩; rw [hc_true, huw, hchk_c]; rfl
          · exact heig
  pLo := fun r w ↦
    let a := rkmAnchorAt anchors r; let d := min (rkmLastNat 0 a.lSegs * m) r
    if 1 ≤ w ∧ w ≤ d then (a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
  hpLo_nonneg := fun r w ↦ by dsimp only; split_ifs <;> positivity
  hpLo_sum_pos := fun r hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨_, _, _, hr_len, hsum_pos, _, _⟩ := hact
    set a := rkmAnchorAt anchors r; set d := min (rkmLastNat 0 a.lSegs * m) r
    rw [rkmb2_sum_Icc_one_eq_range]
    have hcongr : (∑ j ∈ Finset.range d,
          (if 1 ≤ j + 1 ∧ j + 1 ≤ d then (a.rowLo12.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000
           else 0)) = ((altSumNat a.rowLo12 : ℕ) : ℝ) / 1000000000000 := by
      rw [rkmb2_altSumNat_eq_sum_range d a.rowLo12 hr_len, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj_lt : j < d := Finset.mem_range.mp hj
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    rw [hcongr]; have hsumR : (0 : ℝ) < (altSumNat a.rowLo12 : ℝ) := by exact_mod_cast hsum_pos
    positivity
  tauWeighted := fun r ↦ (rkmWeightedTau9 (rkmAnchorAt anchors r).lSegs
    (rkmAnchorAt anchors r).tauSegs : ℝ) / 1000000000
  C_step := 134348800
  hqcount_le := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, _, _⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    obtain ⟨hlen1, hlen8, hsegB, _, _, _, _⟩ := hact
    dsimp only; set a := rkmAnchorAt anchors r; rw [rmsSegsQueryCount_rkmToRmsSegs]
    have hall_le := rkmb2_checkSegBounds_le lTableMax a.lSegs a.tauSegs 1 hsegB
    have hlTab_hi : lTableMax ≤ 8192 := by
      have h1 := Nat.mul_le_mul_left lTableMax htab.hm1; have hhi := htab.hlMax_hi; omega
    have hr1024 : r ≤ 1024 := (hrk.trans hk_le).trans htab.hkMax_hi
    have hC_nat : 2 * a.lSegs.length * lTableMax * (r + 1) ≤ 134348800 :=
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlen8) hlTab_hi)
        (Nat.succ_le_succ hr1024)).trans (by norm_num)
    have hC_real : 2 * (a.lSegs.length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) ≤ 134348800 := by
      have hc : ((2 * a.lSegs.length * lTableMax * (r + 1) : ℕ) : ℝ) ≤ (134348800 : ℝ) := by
        exact_mod_cast hC_nat
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · rcases ht_cons : a.tauSegs with _ | ⟨th, tt⟩
      · simp [hl_cons, ht_cons] at hl_t
      · rw [hl_cons] at hall_le hC_real
        dsimp only [List.headD_cons, List.tail_cons]
        have hbd := rkmSegsQueryCount_build_le n m r lTableMax lh th
          (a.nsubSegs.headD 0) (a.masks.headD []) lt tt a.nsubSegs.tail a.masks.tail
          (hall_le lh List.mem_cons_self)
          (fun x hx ↦ hall_le x (List.mem_cons_of_mem lh hx))
        linarith
  hpLo_le := fun n r hn0 hr2 hrk hwk R hR w hw ↦ by
    obtain ⟨_, heval, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, hl_s, hl_m⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    have hlen1 := hact.1
    dsimp only; set a := rkmAnchorAt anchors r
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
    have hc : 1 ≤ w ∧ w ≤ min (rkmLastNat 0 a.lSegs * m) r := ⟨hw1, hwd⟩
    rw [ite_eq_left hc, symHitProb_evalRampMuxSegs_rkmToRmsSegs]
    have hsound := (rkmEvalT16Lo12_sound hn0 hne hR).2.2.2.2.2
    have hend_eq : rkmEndL (a.lSegs.headD 1)
          (rkmBuildTailSegs n m r a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail) =
        rkmLastNat 0 a.lSegs := by
      rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
      · simp [hl_cons] at hlen1
      · dsimp only [List.headD_cons, List.tail_cons, rkmLastNat]
        exact rkmb2_endL_buildTailSegs n m r lt a.tauSegs.tail a.nsubSegs.tail a.masks.tail lh
          (by simp [← hl_t, hl_cons])
          (by simp [← hl_s, hl_cons])
          (by simp [← hl_m, hl_cons])
    rw [heval] at hsound
    exact hsound w (by rwa [hend_eq])
  hdrift_ramp_lt := fun r hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    exact rkmb2_active_drift_lt hact
end RkmSubSpec

private theorem rkm_lanes_closed : True :=
  (And.intro DickeSol.rkmTrajLanesClosed
    (And.intro DickeSol.laneWitness_FindAllJohnsonRampKickMuxCert0
      (And.intro DickeSol.laneWitness_FindAllJohnsonRampKickMuxCert1
        (And.intro DickeSol.laneWitness_FindAllJohnsonRampKickMuxCert2 trivial)))).2.2.2.2

private lemma rkm_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S =
      GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma rkm_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma rkm_vanilla_eq (n m k : ℕ) :
    DickeSol.vanillaFindAllCost n m k =
      (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

section RkmCert4S32
open DickeSol
private theorem rkm_anc_app_s32 {m0 lMax : ℕ} :
    ∀ {xs ys : List RampKickAnchor}, RampKickAnchorsSound m0 lMax xs →
      RampKickAnchorsSound m0 lMax ys → RampKickAnchorsSound m0 lMax (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, ⟨hx0, hxs⟩, hy => ⟨hx0, rkm_anc_app_s32 hxs hy⟩
private def rkmVPot_m512_s32 : List ℕ := [
  0,28403554933222,30328693038726,33275405693496,33664610634198,33903136539184,
  34067146586095,34188895196749,34284384053687,34362454651251,34428387826731,34485533428441,
  34536116221575,34581680050792,34623316609017,34661805264297,34697789285587,34731656515280,
  34763825945729,34794601990849,34824155782495,34852668126455,34880573571348,34907153788570,
  34933022115135,34959260676497,34983836629322,35010044306945,35032249593357,35058780948461,
  35079661564783,35102975588450,35125513478221,40069937741805,44941107225870,49742184286116,
  54476110108320,59145625775214,63753290821647,68301499634606,35312601220533,39748491245464,
  44131254922493,48462756442173,52744753461525,56978905437081,61166781138189,65309865437034,
  35477879662915,39535530367661,43552399628279,47529692857138,51468557230876,55370085554651,
  59235319802846,63065254368735,66860839051826,70622981808299,74352551287116,78050379171857,
  81717262346173,85353964898826,88961219982602,92539731539910,35817049134973,39340076532506,
  42836312458350,46306358982286,49750795956778,53170182148083,56565056294382,59935938096607,
  63283329147122,66607713800955,69909559993873,73189320011201,76447431210970,79684316704663,
  82900385998559,86096035598425,89271649580092,92427600128228,95564248045455,98681943233777,
  101781025150142,104861823237813,107924657335099,110969838062886,113997667192291,117008437993677,
  120002435568167,122979937162717,125941212469737,128886523912175,131816126914916,134730270163291,
  137629195849437,140513139907198,143382332236211,146236996915779,149077352409102,151903611758375,
  154715982771269,157514668199235,160299865908080,163071769041213,165830566175946,168576441473202,
  171309574820975,174030141971852,176738314674893,179434260802160,182118144470141,184790126156338,
  187450362811232,190099007965867,192736211835245,195362121417737,197976880590698,200580630202453,
  203173508160831,205755649518397,208327186554536,210888248854526,213438963385734,215979454571068,
  218509844359795,221030252295851,37279137336392 ]
private def rkmAncP0_m512_s32 : List RampKickAnchor := [
  ⟨3, [1, 1, 1], [21584876, 5713644, 4435946], [4, 2, 2], rkmMasks_m512_r3, rkmRow_m512_r3⟩,
  ⟨4, [1], [32533060], [6], rkmMasks_m512_r4, rkmRow_m512_r4⟩,
  ⟨5, [1, 1, 1], [11553700, 13860840, 7586665], [4, 4, 3], rkmMasks_m512_r5, rkmRow_m512_r5⟩,
  ⟨6, [1, 1, 1], [22659237, 5998033, 4662805], [6, 3, 2], rkmMasks_m512_r6, rkmRow_m512_r6⟩,
  ⟨7, [1], [33552601], [10], rkmMasks_m512_r7, rkmRow_m512_r7⟩,
  ⟨8, [1, 1], [26657373, 7071068], [9, 3], rkmMasks_m512_r8, rkmRow_m512_r8⟩,
  ⟨9, [1, 1], [25401646, 8467211], [10, 4], rkmMasks_m512_r9, rkmRow_m512_r9⟩,
  ⟨10, [1, 1, 1], [23091279, 6128312, 4764132], [10, 3, 2], rkmMasks_m512_r10, rkmRow_m512_r10⟩,
  ⟨11, [1], [34081402], [14], rkmMasks_m512_r11, rkmRow_m512_r11⟩,
  ⟨12, [1, 1, 1], [392924, 33610389, 161997], [2, 15, 2], rkmMasks_m512_r12, rkmRow_m512_r12⟩,
  ⟨13, [1, 1], [33544007, 694966], [17, 1], rkmMasks_m512_r13, rkmRow_m512_r13⟩,
  ⟨14, [1, 1], [33608007, 696413], [17, 2], rkmMasks_m512_r14, rkmRow_m512_r14⟩,
  ⟨15, [1, 1, 1], [33394223, 891005, 78734], [18, 2, 2], rkmMasks_m512_r15, rkmRow_m512_r15⟩,
  ⟨16, [1, 1, 1, 1], [33587572, 639291, 144227, 50000], [18, 1, 1, 1], rkmMasks_m512_r16,
      rkmRow_m512_r16⟩,
  ⟨17, [1, 1, 1], [33394223, 992702, 81052], [19, 2, 2], rkmMasks_m512_r17, rkmRow_m512_r17⟩,
  ⟨18, [1, 1, 1], [33393723, 1026616, 93470], [20, 2, 2], rkmMasks_m512_r18, rkmRow_m512_r18⟩,
  ⟨19, [1, 1, 1], [33394223, 1077834, 84594], [21, 2, 2], rkmMasks_m512_r19, rkmRow_m512_r19⟩,
  ⟨20, [1, 1, 1], [33393723, 1116356, 87749], [23, 2, 2], rkmMasks_m512_r20, rkmRow_m512_r20⟩,
  ⟨21, [1, 1, 1], [33393723, 1146428, 95734], [24, 2, 2], rkmMasks_m512_r21, rkmRow_m512_r21⟩,
  ⟨22, [1, 1], [33967692, 704465], [26, 2], rkmMasks_m512_r22, rkmRow_m512_r22⟩,
  ⟨23, [1, 1, 1], [33393723, 1199982, 114262], [26, 2, 2], rkmMasks_m512_r23, rkmRow_m512_r23⟩,
  ⟨24, [1, 1, 1], [33587572, 893925, 260729], [26, 1, 1], rkmMasks_m512_r24, rkmRow_m512_r24⟩,
  ⟨25, [1, 1, 1], [33393723, 1281832, 97586], [28, 2, 2], rkmMasks_m512_r25, rkmRow_m512_r25⟩,
  ⟨26, [1, 1, 1, 1], [33393723, 1021183, 222478, 168754], [29, 2, 2, 2], rkmMasks_m512_r26,
      rkmRow_m512_r26⟩
  ]
private def rkmAncP1_m512_s32 : List RampKickAnchor := [
  ⟨27, [1], [34833724], [32], rkmMasks_m512_r27, rkmRow_m512_r27⟩,
  ⟨28, [1, 1, 1, 1], [33394223, 1181122, 214520, 79032], [31, 3, 2, 2], rkmMasks_m512_r28,
      rkmRow_m512_r28⟩,
  ⟨29, [1, 1, 1], [17445650, 8722825, 8722825], [17, 9, 9], rkmMasks_m512_r29, rkmRow_m512_r29⟩,
  ⟨30, [1, 1, 1, 1], [33398723, 1209885, 230985, 87678], [33, 3, 2, 2], rkmMasks_m512_r30,
      rkmRow_m512_r30⟩,
  ⟨31, [1, 1, 1], [33394723, 1257830, 302329], [34, 3, 2], rkmMasks_m512_r31, rkmRow_m512_r31⟩,
  ⟨32, [1, 1, 1, 1, 1, 1, 1, 1],
      [16353637, 16330495, 743524, 722004, 254567, 225787, 175344, 176358],
      [18, 18, 1, 1, 1, 1, 1, 1], rkmMasks_m512_r32, rkmRow_m512_r32⟩,
  ⟨40, [1], [35174751], [52], rkmMasks_m512_r40, rkmRow_m512_r40⟩,
  ⟨48, [1, 1, 1], [33587572, 1484924, 303173], [51, 3, 1], rkmMasks_m512_r48, rkmRow_m512_r48⟩,
  ⟨64, [1, 1, 1, 1], [34000000, 1303137, 342379, 91212], [67, 3, 1, 1], rkmMasks_m512_r64,
      rkmRow_m512_r64⟩,
  ⟨128, [1, 1, 1, 1], [35200000, 1489509, 408816, 115125], [129, 6, 2, 1], rkmMasks_m512_r128,
      rkmRow_m512_r128⟩
  ]
private def rkmAnchors_m512_s32 : List RampKickAnchor := rkmAncP0_m512_s32 ++ rkmAncP1_m512_s32
private theorem rkmAncSnd0_m512_s32 : RampKickAnchorsSound 512 16 rkmAncP0_m512_s32 :=
  ⟨rkmTraj_m512_r3, ⟨rkmTraj_m512_r4, ⟨rkmTraj_m512_r5, ⟨rkmTraj_m512_r6, ⟨rkmTraj_m512_r7,
  ⟨rkmTraj_m512_r8, ⟨rkmTraj_m512_r9, ⟨rkmTraj_m512_r10, ⟨rkmTraj_m512_r11, ⟨rkmTraj_m512_r12,
  ⟨rkmTraj_m512_r13, ⟨rkmTraj_m512_r14, ⟨rkmTraj_m512_r15, ⟨rkmTraj_m512_r16, ⟨rkmTraj_m512_r17,
  ⟨rkmTraj_m512_r18, ⟨rkmTraj_m512_r19, ⟨rkmTraj_m512_r20, ⟨rkmTraj_m512_r21, ⟨rkmTraj_m512_r22,
  ⟨rkmTraj_m512_r23, ⟨rkmTraj_m512_r24, ⟨rkmTraj_m512_r25, ⟨rkmTraj_m512_r26,
  trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSnd1_m512_s32 : RampKickAnchorsSound 512 16 rkmAncP1_m512_s32 :=
  ⟨rkmTraj_m512_r27, ⟨rkmTraj_m512_r28, ⟨rkmTraj_m512_r29, ⟨rkmTraj_m512_r30, ⟨rkmTraj_m512_r31,
  ⟨rkmTraj_m512_r32, ⟨rkmTraj_m512_r40, ⟨rkmTraj_m512_r48, ⟨rkmTraj_m512_r64,
  ⟨rkmTraj_m512_r128, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSnd_m512_s32 :
    RampKickAnchorsSound 512 16 rkmAnchors_m512_s32 :=
  rkm_anc_app_s32 rkmAncSnd0_m512_s32 rkmAncSnd1_m512_s32
private theorem rkmTableOk_m512_s32 :
    rkmCheckTable 512 128 16 true rkmVPot_m512_s32 rkmAnchors_m512_s32 = true := by
  decide +kernel
private theorem rkmValid_m512_s32 :
    RampKickTableValid 512 128 16 true rkmVPot_m512_s32 rkmAnchors_m512_s32 :=
  rkmCheckTable_sound rkmTableOk_m512_s32 rkmAncSnd_m512_s32
private theorem rkmCellLMax_m512_k64_s32 :
    rkmCheckAnchorsLMax 64 2 rkmAnchors_m512_s32 = true := rfl
private theorem rkmBound_m512_k64_s32 :
    checkAltBound12 512 64 (rkmVPot_m512_s32.getD 64 0) 220836407 3125000000 = true := by
  decide +kernel
private theorem rkmCellLMax_m512_k128_s32 :
    rkmCheckAnchorsLMax 128 2 rkmAnchors_m512_s32 = true := rfl
private theorem rkmBound_m512_k128_s32 :
    checkAltBound12 512 128 (rkmVPot_m512_s32.getD 128 0) 25317169393 500000000000 = true := by
  decide +kernel
private def rkmVPot_m1024_s32 : List ℕ := [
  0,20084346303087,21438047432514,23518312123120,23787563661611,23950191560091,
  24060060858308,24139996310714,24201319393262,24250283135788,24290624148769,24324711347723,
  24354120094589,24379938523567,24402942269808,24423699249768,24442634888239,24460074044769,
  24476269152720,24491419277117,24505683594266,24519190827344,24532046256961,24544336332780,
  24556134883010,24567500189273,24578487106451,24589136525997,24599486933881,24609570638585,
  24619415670567,24629046393074,24638162845157,28134398771001,31578835745493,34973709891792,
  38321100942307,41622947135225,44881058334994,48097127628890,51272741610557,54409389527784,
  57508471444149,60571305541435,63599134670840,66593132245330,69554407552350,72484010555091,
  75382936241237,78252128570250,81092484063573,83904855076467,86690052785312,89448849920045,
  92181983267818,94890155970859,97574039638840,100234276293734,102871480163112,105486239336073,
  108079117294451,110650654330590,113201368861798,115731758650525,24892358819364,27383515382465,
  29855727514257,32309420942365,34745005684398,37162876847765,39563415377888,41946988758820,
  44313951669922,46664646601920,48999404435367,51318544984284,53622377507501,55911201190016,
  58185305596496,60444971098857,62690469279725,64922063313402,67140008325868,69344551735203,
  71535933573718,73714386792977,75880137552817,78033405495374,80174404005050,82303340455309,
  84420416443087,86525828011587,88619765862141,90702415555795,92773957705218,94834568157493,
  96884418168323,98923674568129,100952499920502,102971052673439,104979487303748,106977954455011,
  108966601069441,110945570513964,112915002700833,114875034203064,116825798364952,118767425407935,
  120700042532033,122623774013091,124538741296036,126445063084340,128342855425886,130232231795402,
  132113303173639,133986178123439,135850962862848,137707761335411,139556675277782,141397804284766,
  143231245871924,145057095535841,146875446812168,148686391331532,150490018873420,152286417418114,
  154075673196768,155857870739710,25353909556349 ]
private def rkmAncP0_m1024_s32 : List RampKickAnchor := [
  ⟨3, [1], [22427643], [5], rkmMasks_m1024_r3, rkmRow_m1024_r3⟩,
  ⟨4, [1, 1], [16092275, 6893241], [5, 3], rkmMasks_m1024_r4, rkmRow_m1024_r4⟩,
  ⟨5, [1], [23317052], [7], rkmMasks_m1024_r5, rkmRow_m1024_r5⟩,
  ⟨6, [1, 1], [16474801, 7060629], [6, 3], rkmMasks_m1024_r6, rkmRow_m1024_r6⟩,
  ⟨7, [1, 1, 1, 1], [7109689, 7106689, 5685352, 3788339], [4, 4, 3, 3], rkmMasks_m1024_r7,
      rkmRow_m1024_r7⟩,
  ⟨8, [1], [23810432], [11], rkmMasks_m1024_r8, rkmRow_m1024_r8⟩,
  ⟨9, [1, 1, 1, 1], [11950125, 5259375, 3825000, 2868750], [7, 3, 2, 2], rkmMasks_m1024_r9,
      rkmRow_m1024_r9⟩,
  ⟨10, [1], [23978903], [13], rkmMasks_m1024_r10, rkmRow_m1024_r10⟩,
  ⟨11, [1, 1], [20435323, 3606233], [12, 3], rkmMasks_m1024_r11, rkmRow_m1024_r11⟩,
  ⟨12, [1, 1], [18793801, 5300816], [13, 4], rkmMasks_m1024_r12, rkmRow_m1024_r12⟩,
  ⟨13, [1], [24140564], [18], rkmMasks_m1024_r13, rkmRow_m1024_r13⟩,
  ⟨14, [1, 1], [20553616, 3627109], [16, 3], rkmMasks_m1024_r14, rkmRow_m1024_r14⟩,
  ⟨15, [1], [24216172], [18], rkmMasks_m1024_r15, rkmRow_m1024_r15⟩,
  ⟨16, [1], [24247995], [19], rkmMasks_m1024_r16, rkmRow_m1024_r16⟩,
  ⟨17, [1], [24276827], [20], rkmMasks_m1024_r17, rkmRow_m1024_r17⟩,
  ⟨18, [1], [24302985], [21], rkmMasks_m1024_r18, rkmRow_m1024_r18⟩,
  ⟨19, [1], [24327295], [22], rkmMasks_m1024_r19, rkmRow_m1024_r19⟩,
  ⟨20, [1], [24349636], [23], rkmMasks_m1024_r20, rkmRow_m1024_r20⟩,
  ⟨21, [1], [24370369], [28], rkmMasks_m1024_r21, rkmRow_m1024_r21⟩,
  ⟨22, [1], [24389797], [25], rkmMasks_m1024_r22, rkmRow_m1024_r22⟩,
  ⟨23, [1, 1], [23912511, 495463], [27, 2], rkmMasks_m1024_r23, rkmRow_m1024_r23⟩,
  ⟨24, [1], [24425176], [32], rkmMasks_m1024_r24, rkmRow_m1024_r24⟩,
  ⟨25, [1, 1], [23945420, 496437], [29, 2], rkmMasks_m1024_r25, rkmRow_m1024_r25⟩,
  ⟨26, [1], [24457258], [30], rkmMasks_m1024_r26, rkmRow_m1024_r26⟩
  ]
private def rkmAncP1_m1024_s32 : List RampKickAnchor := [
  ⟨27, [1], [24472289], [35], rkmMasks_m1024_r27, rkmRow_m1024_r27⟩,
  ⟨28, [1], [24486601], [33], rkmMasks_m1024_r28, rkmRow_m1024_r28⟩,
  ⟨29, [1], [24500227], [34], rkmMasks_m1024_r29, rkmRow_m1024_r29⟩,
  ⟨30, [1], [24513437], [39], rkmMasks_m1024_r30, rkmRow_m1024_r30⟩,
  ⟨31, [1], [24526307], [36], rkmMasks_m1024_r31, rkmRow_m1024_r31⟩,
  ⟨32, [1, 1, 1, 1, 1, 1, 1, 1],
      [11808428, 11807788, 391437, 391438, 32137, 32337, 38286, 37859],
      [18, 18, 1, 1, 1, 1, 1, 1], rkmMasks_m1024_r32, rkmRow_m1024_r32⟩,
  ⟨64, [1, 1, 1, 1], [23750000, 735000, 214375, 142187], [68, 3, 1, 1], rkmMasks_m1024_r64,
      rkmRow_m1024_r64⟩,
  ⟨128, [1, 1, 1, 1], [23750000, 1050000, 286250, 231562], [132, 6, 2, 2], rkmMasks_m1024_r128,
      rkmRow_m1024_r128⟩
  ]
private def rkmAnchors_m1024_s32 : List RampKickAnchor := rkmAncP0_m1024_s32 ++ rkmAncP1_m1024_s32
private theorem rkmAncSnd0_m1024_s32 : RampKickAnchorsSound 1024 8 rkmAncP0_m1024_s32 :=
  ⟨rkmTraj_m1024_r3, ⟨rkmTraj_m1024_r4, ⟨rkmTraj_m1024_r5, ⟨rkmTraj_m1024_r6, ⟨rkmTraj_m1024_r7,
  ⟨rkmTraj_m1024_r8, ⟨rkmTraj_m1024_r9, ⟨rkmTraj_m1024_r10, ⟨rkmTraj_m1024_r11,
  ⟨rkmTraj_m1024_r12, ⟨rkmTraj_m1024_r13, ⟨rkmTraj_m1024_r14, ⟨rkmTraj_m1024_r15,
  ⟨rkmTraj_m1024_r16, ⟨rkmTraj_m1024_r17, ⟨rkmTraj_m1024_r18, ⟨rkmTraj_m1024_r19,
  ⟨rkmTraj_m1024_r20, ⟨rkmTraj_m1024_r21, ⟨rkmTraj_m1024_r22, ⟨rkmTraj_m1024_r23,
  ⟨rkmTraj_m1024_r24, ⟨rkmTraj_m1024_r25, ⟨rkmTraj_m1024_r26, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSnd1_m1024_s32 : RampKickAnchorsSound 1024 8 rkmAncP1_m1024_s32 :=
  ⟨rkmTraj_m1024_r27, ⟨rkmTraj_m1024_r28, ⟨rkmTraj_m1024_r29, ⟨rkmTraj_m1024_r30,
  ⟨rkmTraj_m1024_r31, ⟨rkmTraj_m1024_r32, ⟨rkmTraj_m1024_r64, ⟨rkmTraj_m1024_r128,
  trivial⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSnd_m1024_s32 :
    RampKickAnchorsSound 1024 8 rkmAnchors_m1024_s32 :=
  rkm_anc_app_s32 rkmAncSnd0_m1024_s32 rkmAncSnd1_m1024_s32
private theorem rkmTableOk_m1024_s32 :
    rkmCheckTable 1024 128 8 true rkmVPot_m1024_s32 rkmAnchors_m1024_s32 = true := by
  decide +kernel
private theorem rkmValid_m1024_s32 :
    RampKickTableValid 1024 128 8 true rkmVPot_m1024_s32 rkmAnchors_m1024_s32 :=
  rkmCheckTable_sound rkmTableOk_m1024_s32 rkmAncSnd_m1024_s32
private theorem rkmCellLMax_m1024_k64_s32 :
    rkmCheckAnchorsLMax 64 2 rkmAnchors_m1024_s32 = true := rfl
private theorem rkmBound_m1024_k64_s32 :
    checkAltBound12 1024 64 (rkmVPot_m1024_s32.getD 64 0) 17364085169 250000000000 = true := by
  decide +kernel
private theorem rkmCellLMax_m1024_k128_s32 :
    rkmCheckAnchorsLMax 128 2 rkmAnchors_m1024_s32 = true := rfl
private theorem rkmBound_m1024_k128_s32 :
    checkAltBound12 1024 128 (rkmVPot_m1024_s32.getD 128 0) 48701150809 1000000000000 = true := by
  decide +kernel
private theorem rkmTrajClosed_s32 : rkmTrajLaneProp_09 ∧ rkmTrajLaneProp_10 :=
  ⟨rkmTrajLaneOk_09, rkmTrajLaneOk_10⟩
end RkmCert4S32

private def rkmKMax (m : ℕ) : ℕ := if m == 512 || m == 1024 then 128 else 1024

private def rkmLTableMax (m : ℕ) : ℕ :=
  if m == 2 then 4096
  else if m == 4 then 2048
  else if m == 8 then 1024
  else if m == 16 then 512
  else if m == 32 then 256
  else if m == 64 then 128
  else if m == 512 then 16
  else 8

private def rkmVPot (m : ℕ) : List ℕ :=
  if m == 2 then DickeSol.rkmVPot_m2
  else if m == 4 then DickeSol.rkmVPot_m4
  else if m == 8 then DickeSol.rkmVPot_m8
  else if m == 16 then DickeSol.rkmVPot_m16
  else if m == 32 then DickeSol.rkmVPot_m32
  else if m == 64 then DickeSol.rkmVPot_m64
  else if m == 512 then rkmVPot_m512_s32
  else rkmVPot_m1024_s32

private def rkmAnchors (m : ℕ) : List DickeSol.RampKickAnchor :=
  if m == 2 then DickeSol.rkmAnchors_m2
  else if m == 4 then DickeSol.rkmAnchors_m4
  else if m == 8 then DickeSol.rkmAnchors_m8
  else if m == 16 then DickeSol.rkmAnchors_m16
  else if m == 32 then DickeSol.rkmAnchors_m32
  else if m == 64 then DickeSol.rkmAnchors_m64
  else if m == 512 then rkmAnchors_m512_s32
  else rkmAnchors_m1024_s32

private def rkmWinWLo (m : ℕ) : ℕ :=
  if m == 2 then 920
  else if m == 4 then 918
  else if m == 8 then 920
  else if m == 16 then 785
  else if m == 32 then 820
  else 845
private def rkmWinVR (m : ℕ) : ℕ :=
  if m == 2 then 16690823448180281
  else if m == 4 then 8374647340518534
  else if m == 8 then 4208005866470537
  else if m == 16 then 2117515629891086
  else if m == 32 then 1063460268786042
  else 535055128480452
private def rkmWinNum (m : ℕ) : ℕ :=
  if m == 2 then 480439805247
  else if m == 4 then 340912357990
  else if m == 8 then 242252100412
  else if m == 16 then 172398243679
  else if m == 32 then 122445401453
  else 87123384706
private def rkmWinAnchor (m : ℕ) : DickeSol.RampKickAnchor :=
  if m == 2 then DickeSol.rkmWinAnchor_m2
  else if m == 4 then DickeSol.rkmWinAnchor_m4
  else if m == 8 then DickeSol.rkmWinAnchor_m8
  else if m == 16 then DickeSol.rkmWinAnchor_m16
  else if m == 32 then DickeSol.rkmWinAnchor_m32
  else DickeSol.rkmWinAnchor_m64

private abbrev rkmIsK512 (k : ℕ) : Prop :=
  k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128 ∨ k = 256 ∨ k = 512

private abbrev RkmCellCert (m k : ℕ) (vPot : List ℕ)
    (anchors : List DickeSol.RampKickAnchor) : Prop :=
  2 ≤ johnsonRampKickMuxCellLMax m k ∧ 1 ≤ johnsonRampKickMuxCellLMax m k ∧
    johnsonRampKickMuxCellLMax m k * m ≤ 65536 ∧
    DickeSol.rkmCheckAnchorsLMax k (johnsonRampKickMuxCellLMax m k) anchors = true ∧
    ∃ num den : ℕ, relCostJohnsonRampKickMux m k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 m k (vPot.getD k 0) num den = true

private lemma rkm_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b :=
  h ▸ Nat.le_add_right a d

private lemma rkm_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) :
    2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (rkm_le_of_add h), rfl⟩

private lemma rkm_mk_cell {m k d2 dm num den : ℕ} {vPot : List ℕ}
    {anchors : List DickeSol.RampKickAnchor}
    (h2 : 2 + d2 = johnsonRampKickMuxCellLMax m k)
    (hm : johnsonRampKickMuxCellLMax m k * m + dm = 65536)
    (hl : DickeSol.rkmCheckAnchorsLMax k (johnsonRampKickMuxCellLMax m k) anchors = true)
    (hrc : relCostJohnsonRampKickMux m k = NNRat.divNat num den)
    (hb : DickeSol.checkAltBound12 m k (vPot.getD k 0) num den = true) :
    RkmCellCert m k vPot anchors :=
  have hle2 : 2 ≤ johnsonRampKickMuxCellLMax m k := rkm_le_of_add h2
  ⟨hle2, Nat.le_trans (rkm_le_of_add (d := 1) rfl) hle2, rkm_le_of_add hm,
    hl, ⟨num, den, hrc, hb⟩⟩

private lemma rkm_cell_m2 {k : ℕ} (hk : rkmIsK512 k) :
    RkmCellCert 2 k DickeSol.rkmVPot_m2 DickeSol.rkmAnchors_m2 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 65532) rfl rfl
      DickeSol.rkmCellLMax_m2_k2 rfl DickeSol.rkmBound_m2_k2
  · exact rkm_mk_cell (d2 := 1) (dm := 65530) rfl rfl
      DickeSol.rkmCellLMax_m2_k4 rfl DickeSol.rkmBound_m2_k4
  · exact rkm_mk_cell (d2 := 4) (dm := 65524) rfl rfl
      DickeSol.rkmCellLMax_m2_k8 rfl DickeSol.rkmBound_m2_k8
  · exact rkm_mk_cell (d2 := 10) (dm := 65512) rfl rfl
      DickeSol.rkmCellLMax_m2_k16 rfl DickeSol.rkmBound_m2_k16
  · exact rkm_mk_cell (d2 := 28) (dm := 65476) rfl rfl
      DickeSol.rkmCellLMax_m2_k32 rfl DickeSol.rkmBound_m2_k32
  · exact rkm_mk_cell (d2 := 56) (dm := 65420) rfl rfl
      DickeSol.rkmCellLMax_m2_k64 rfl DickeSol.rkmBound_m2_k64
  · exact rkm_mk_cell (d2 := 110) (dm := 65312) rfl rfl
      DickeSol.rkmCellLMax_m2_k128 rfl DickeSol.rkmBound_m2_k128
  · exact rkm_mk_cell (d2 := 222) (dm := 65088) rfl rfl
      DickeSol.rkmCellLMax_m2_k256 rfl DickeSol.rkmBound_m2_k256
  · exact rkm_mk_cell (d2 := 446) (dm := 64640) rfl rfl
      DickeSol.rkmCellLMax_m2_k512 rfl DickeSol.rkmBound_m2_k512
private lemma rkm_cell_m4 {k : ℕ} (hk : rkmIsK512 k) :
    RkmCellCert 4 k DickeSol.rkmVPot_m4 DickeSol.rkmAnchors_m4 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 65528) rfl rfl
      DickeSol.rkmCellLMax_m4_k2 rfl DickeSol.rkmBound_m4_k2
  · exact rkm_mk_cell (d2 := 0) (dm := 65528) rfl rfl
      DickeSol.rkmCellLMax_m4_k4 rfl DickeSol.rkmBound_m4_k4
  · exact rkm_mk_cell (d2 := 1) (dm := 65524) rfl rfl
      DickeSol.rkmCellLMax_m4_k8 rfl DickeSol.rkmBound_m4_k8
  · exact rkm_mk_cell (d2 := 5) (dm := 65508) rfl rfl
      DickeSol.rkmCellLMax_m4_k16 rfl DickeSol.rkmBound_m4_k16
  · exact rkm_mk_cell (d2 := 12) (dm := 65480) rfl rfl
      DickeSol.rkmCellLMax_m4_k32 rfl DickeSol.rkmBound_m4_k32
  · exact rkm_mk_cell (d2 := 27) (dm := 65420) rfl rfl
      DickeSol.rkmCellLMax_m4_k64 rfl DickeSol.rkmBound_m4_k64
  · exact rkm_mk_cell (d2 := 57) (dm := 65300) rfl rfl
      DickeSol.rkmCellLMax_m4_k128 rfl DickeSol.rkmBound_m4_k128
  · exact rkm_mk_cell (d2 := 110) (dm := 65088) rfl rfl
      DickeSol.rkmCellLMax_m4_k256 rfl DickeSol.rkmBound_m4_k256
  · exact rkm_mk_cell (d2 := 222) (dm := 64640) rfl rfl
      DickeSol.rkmCellLMax_m4_k512 rfl DickeSol.rkmBound_m4_k512
private lemma rkm_cell_m8 {k : ℕ} (hk : rkmIsK512 k) :
    RkmCellCert 8 k DickeSol.rkmVPot_m8 DickeSol.rkmAnchors_m8 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 65520) rfl rfl
      DickeSol.rkmCellLMax_m8_k2 rfl DickeSol.rkmBound_m8_k2
  · exact rkm_mk_cell (d2 := 0) (dm := 65520) rfl rfl
      DickeSol.rkmCellLMax_m8_k4 rfl DickeSol.rkmBound_m8_k4
  · exact rkm_mk_cell (d2 := 0) (dm := 65520) rfl rfl
      DickeSol.rkmCellLMax_m8_k8 rfl DickeSol.rkmBound_m8_k8
  · exact rkm_mk_cell (d2 := 1) (dm := 65512) rfl rfl
      DickeSol.rkmCellLMax_m8_k16 rfl DickeSol.rkmBound_m8_k16
  · exact rkm_mk_cell (d2 := 5) (dm := 65480) rfl rfl
      DickeSol.rkmCellLMax_m8_k32 rfl DickeSol.rkmBound_m8_k32
  · exact rkm_mk_cell (d2 := 13) (dm := 65416) rfl rfl
      DickeSol.rkmCellLMax_m8_k64 rfl DickeSol.rkmBound_m8_k64
  · exact rkm_mk_cell (d2 := 28) (dm := 65296) rfl rfl
      DickeSol.rkmCellLMax_m8_k128 rfl DickeSol.rkmBound_m8_k128
  · exact rkm_mk_cell (d2 := 54) (dm := 65088) rfl rfl
      DickeSol.rkmCellLMax_m8_k256 rfl DickeSol.rkmBound_m8_k256
  · exact rkm_mk_cell (d2 := 110) (dm := 64640) rfl rfl
      DickeSol.rkmCellLMax_m8_k512 rfl DickeSol.rkmBound_m8_k512
private lemma rkm_cell_m16 {k : ℕ} (hk : rkmIsK512 k) :
    RkmCellCert 16 k DickeSol.rkmVPot_m16 DickeSol.rkmAnchors_m16 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 65504) rfl rfl
      DickeSol.rkmCellLMax_m16_k2 rfl DickeSol.rkmBound_m16_k2
  · exact rkm_mk_cell (d2 := 0) (dm := 65504) rfl rfl
      DickeSol.rkmCellLMax_m16_k4 rfl DickeSol.rkmBound_m16_k4
  · exact rkm_mk_cell (d2 := 0) (dm := 65504) rfl rfl
      DickeSol.rkmCellLMax_m16_k8 rfl DickeSol.rkmBound_m16_k8
  · exact rkm_mk_cell (d2 := 0) (dm := 65504) rfl rfl
      DickeSol.rkmCellLMax_m16_k16 rfl DickeSol.rkmBound_m16_k16
  · exact rkm_mk_cell (d2 := 2) (dm := 65472) rfl rfl
      DickeSol.rkmCellLMax_m16_k32 rfl DickeSol.rkmBound_m16_k32
  · exact rkm_mk_cell (d2 := 5) (dm := 65424) rfl rfl
      DickeSol.rkmCellLMax_m16_k64 rfl DickeSol.rkmBound_m16_k64
  · exact rkm_mk_cell (d2 := 13) (dm := 65296) rfl rfl
      DickeSol.rkmCellLMax_m16_k128 rfl DickeSol.rkmBound_m16_k128
  · exact rkm_mk_cell (d2 := 26) (dm := 65088) rfl rfl
      DickeSol.rkmCellLMax_m16_k256 rfl DickeSol.rkmBound_m16_k256
  · exact rkm_mk_cell (d2 := 54) (dm := 64640) rfl rfl
      DickeSol.rkmCellLMax_m16_k512 rfl DickeSol.rkmBound_m16_k512
private lemma rkm_cell_m32 {k : ℕ} (hk : rkmIsK512 k) :
    RkmCellCert 32 k DickeSol.rkmVPot_m32 DickeSol.rkmAnchors_m32 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 65472) rfl rfl
      DickeSol.rkmCellLMax_m32_k2 rfl DickeSol.rkmBound_m32_k2
  · exact rkm_mk_cell (d2 := 0) (dm := 65472) rfl rfl
      DickeSol.rkmCellLMax_m32_k4 rfl DickeSol.rkmBound_m32_k4
  · exact rkm_mk_cell (d2 := 0) (dm := 65472) rfl rfl
      DickeSol.rkmCellLMax_m32_k8 rfl DickeSol.rkmBound_m32_k8
  · exact rkm_mk_cell (d2 := 0) (dm := 65472) rfl rfl
      DickeSol.rkmCellLMax_m32_k16 rfl DickeSol.rkmBound_m32_k16
  · exact rkm_mk_cell (d2 := 0) (dm := 65472) rfl rfl
      DickeSol.rkmCellLMax_m32_k32 rfl DickeSol.rkmBound_m32_k32
  · exact rkm_mk_cell (d2 := 2) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m32_k64 rfl DickeSol.rkmBound_m32_k64
  · exact rkm_mk_cell (d2 := 5) (dm := 65312) rfl rfl
      DickeSol.rkmCellLMax_m32_k128 rfl DickeSol.rkmBound_m32_k128
  · exact rkm_mk_cell (d2 := 12) (dm := 65088) rfl rfl
      DickeSol.rkmCellLMax_m32_k256 rfl DickeSol.rkmBound_m32_k256
  · exact rkm_mk_cell (d2 := 26) (dm := 64640) rfl rfl
      DickeSol.rkmCellLMax_m32_k512 rfl DickeSol.rkmBound_m32_k512
private lemma rkm_cell_m64 {k : ℕ} (hk : rkmIsK512 k) :
    RkmCellCert 64 k DickeSol.rkmVPot_m64 DickeSol.rkmAnchors_m64 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m64_k2 rfl DickeSol.rkmBound_m64_k2
  · exact rkm_mk_cell (d2 := 0) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m64_k4 rfl DickeSol.rkmBound_m64_k4
  · exact rkm_mk_cell (d2 := 0) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m64_k8 rfl DickeSol.rkmBound_m64_k8
  · exact rkm_mk_cell (d2 := 0) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m64_k16 rfl DickeSol.rkmBound_m64_k16
  · exact rkm_mk_cell (d2 := 0) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m64_k32 rfl DickeSol.rkmBound_m64_k32
  · exact rkm_mk_cell (d2 := 0) (dm := 65408) rfl rfl
      DickeSol.rkmCellLMax_m64_k64 rfl DickeSol.rkmBound_m64_k64
  · exact rkm_mk_cell (d2 := 2) (dm := 65280) rfl rfl
      DickeSol.rkmCellLMax_m64_k128 rfl DickeSol.rkmBound_m64_k128
  · exact rkm_mk_cell (d2 := 5) (dm := 65088) rfl rfl
      DickeSol.rkmCellLMax_m64_k256 rfl DickeSol.rkmBound_m64_k256
  · exact rkm_mk_cell (d2 := 12) (dm := 64640) rfl rfl
      DickeSol.rkmCellLMax_m64_k512 rfl DickeSol.rkmBound_m64_k512

private lemma rkm_cell_m512_s32 {k : ℕ} (hk : k = 64 ∨ k = 128) :
    RkmCellCert 512 k rkmVPot_m512_s32 rkmAnchors_m512_s32 := by
  rcases hk with rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 64512) rfl rfl
      rkmCellLMax_m512_k64_s32 rfl rkmBound_m512_k64_s32
  · exact rkm_mk_cell (d2 := 0) (dm := 64512) rfl rfl
      rkmCellLMax_m512_k128_s32 rfl rkmBound_m512_k128_s32

private lemma rkm_cell_m1024_s32 {k : ℕ} (hk : k = 64 ∨ k = 128) :
    RkmCellCert 1024 k rkmVPot_m1024_s32 rkmAnchors_m1024_s32 := by
  rcases hk with rfl | rfl
  · exact rkm_mk_cell (d2 := 0) (dm := 63488) rfl rfl
      rkmCellLMax_m1024_k64_s32 rfl rkmBound_m1024_k64_s32
  · exact rkm_mk_cell (d2 := 0) (dm := 63488) rfl rfl
      rkmCellLMax_m1024_k128_s32 rfl rkmBound_m1024_k128_s32

private lemma rkm_cases {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true) :
    ((m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64) ∧ (rkmIsK512 k ∨ k = 1024)) ∨
      ((m = 512 ∨ m = 1024) ∧ (k = 64 ∨ k = 128)) := by
  unfold isJohnsonRampKickMuxCell at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  unfold rkmIsK512; tauto

private lemma rkm_k512_props {k : ℕ} (hk : rkmIsK512 k) :
    k ∈ DickeSol.groverGrid ∧ k ≤ 1024 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨rkm_mem_grid 1 9 rfl, rkm_le_of_add (d := 1022) rfl⟩,
    ⟨rkm_mem_grid 2 8 rfl, rkm_le_of_add (d := 1020) rfl⟩,
    ⟨rkm_mem_grid 3 7 rfl, rkm_le_of_add (d := 1016) rfl⟩,
    ⟨rkm_mem_grid 4 6 rfl, rkm_le_of_add (d := 1008) rfl⟩,
    ⟨rkm_mem_grid 5 5 rfl, rkm_le_of_add (d := 992) rfl⟩,
    ⟨rkm_mem_grid 6 4 rfl, rkm_le_of_add (d := 960) rfl⟩,
    ⟨rkm_mem_grid 7 3 rfl, rkm_le_of_add (d := 896) rfl⟩,
    ⟨rkm_mem_grid 8 2 rfl, rkm_le_of_add (d := 768) rfl⟩,
    ⟨rkm_mem_grid 9 1 rfl, rkm_le_of_add (d := 512) rfl⟩]

private lemma rkm_sub512_props {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true)
    (hk_ne : ¬ k = 1024) :
    m ∈ DickeSol.groverGrid ∧ k ∈ DickeSol.groverGrid ∧ k ≤ rkmKMax m ∧ 2 ≤ m ∧
      DickeSol.RampKickTableValid m (rkmKMax m) (rkmLTableMax m) true
        (rkmVPot m) (rkmAnchors m) ∧
      RkmCellCert m k (rkmVPot m) (rkmAnchors m) := by
  cases rkm_cases h with
  | inl hlow =>
    obtain ⟨hm, hk_or⟩ := hlow; have hk := hk_or.resolve_right hk_ne
    obtain ⟨hk_g, hk_hi⟩ := rkm_k512_props hk
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨rkm_mem_grid 1 9 rfl, hk_g, hk_hi, rkm_le_of_add (d := 0) rfl,
        DickeSol.rkmValid_m2, rkm_cell_m2 hk⟩
    · exact ⟨rkm_mem_grid 2 8 rfl, hk_g, hk_hi, rkm_le_of_add (d := 2) rfl,
        DickeSol.rkmValid_m4, rkm_cell_m4 hk⟩
    · exact ⟨rkm_mem_grid 3 7 rfl, hk_g, hk_hi, rkm_le_of_add (d := 6) rfl,
        DickeSol.rkmValid_m8, rkm_cell_m8 hk⟩
    · exact ⟨rkm_mem_grid 4 6 rfl, hk_g, hk_hi, rkm_le_of_add (d := 14) rfl,
        DickeSol.rkmValid_m16, rkm_cell_m16 hk⟩
    · exact ⟨rkm_mem_grid 5 5 rfl, hk_g, hk_hi, rkm_le_of_add (d := 30) rfl,
        DickeSol.rkmValid_m32, rkm_cell_m32 hk⟩
    · exact ⟨rkm_mem_grid 6 4 rfl, hk_g, hk_hi, rkm_le_of_add (d := 62) rfl,
        DickeSol.rkmValid_m64, rkm_cell_m64 hk⟩
  | inr hhi =>
    rcases hhi with ⟨rfl | rfl, rfl | rfl⟩
    · exact ⟨rkm_mem_grid 9 1 rfl, rkm_mem_grid 6 4 rfl, rkm_le_of_add (d := 64) rfl,
        rkm_le_of_add (d := 510) rfl, rkmValid_m512_s32, rkm_cell_m512_s32 (Or.inl rfl)⟩
    · exact ⟨rkm_mem_grid 9 1 rfl, rkm_mem_grid 7 3 rfl, rkm_le_of_add (d := 0) rfl,
        rkm_le_of_add (d := 510) rfl, rkmValid_m512_s32, rkm_cell_m512_s32 (Or.inr rfl)⟩
    · exact ⟨rkm_mem_grid 10 0 rfl, rkm_mem_grid 6 4 rfl, rkm_le_of_add (d := 64) rfl,
        rkm_le_of_add (d := 1022) rfl, rkmValid_m1024_s32, rkm_cell_m1024_s32 (Or.inl rfl)⟩
    · exact ⟨rkm_mem_grid 10 0 rfl, rkm_mem_grid 7 3 rfl, rkm_le_of_add (d := 0) rfl,
        rkm_le_of_add (d := 1022) rfl, rkmValid_m1024_s32, rkm_cell_m1024_s32 (Or.inr rfl)⟩

private lemma rkm_tbl17 {P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 Q : Prop}
    (mk : P1 → P2 → P3 → P4 → P5 → P6 → P7 → P8 → P9 → P10 → P11 → P12 → P13 → P14 → P15 → P16 →
      P17 → Q)
    (h : P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5 ∧ P6 ∧ P7 ∧ P8 ∧ P9 ∧ P10 ∧ P11 ∧ P12 ∧ P13 ∧ P14 ∧ P15 ∧ P16 ∧
      P17) : Q :=
  mk h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private abbrev RkmWinTuple (m k : ℕ) : Prop :=
  m ∈ DickeSol.groverGrid ∧ k ∈ DickeSol.groverGrid ∧ 2 ≤ k ∧ rkmLTableMax m ≤ 8192 ∧
    2 ≤ m ∧ 2 ≤ johnsonRampKickMuxCellLMax m k ∧ 1 ≤ johnsonRampKickMuxCellLMax m k ∧
    johnsonRampKickMuxCellLMax m k * m ≤ 65536 ∧
    DickeSol.RampKickTableValid m 1024 (rkmLTableMax m) true (rkmVPot m) (rkmAnchors m) ∧
    DickeSol.rkmCheckAnchorsLMax 512 (johnsonRampKickMuxCellLMax m k) (rkmAnchors m) = true ∧
    DickeSol.RkmWinAnchorSpec m k 512 (rkmLTableMax m) (johnsonRampKickMuxCellLMax m k)
      (rkmWinWLo m) (rkmWinVR m) (rkmWinNum m) 1000000000000 (rkmVPot m) (rkmWinAnchor m) ∧
    relCostJohnsonRampKickMux m k = NNRat.divNat (rkmWinNum m) 1000000000000

private lemma rkm_win_props {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true)
    (hk : k = 1024) : RkmWinTuple m k := by
  subst hk; have hm : m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 :=
    (rkm_cases h).elim And.left (fun h1 ↦ by omega)
  have hk_g : 1024 ∈ DickeSol.groverGrid := rkm_mem_grid 10 0 rfl
  have b : ∀ {a c : ℕ}, Nat.ble a c = true → a ≤ c := fun h0 ↦ Nat.ble_eq.mp h0
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [
    ⟨rkm_mem_grid 1 9 rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
      DickeSol.rkmValid_m2, DickeSol.rkmSubLMax_m2_k1024,
      rkm_tbl17 (@DickeSol.RkmWinAnchorSpec.mk 2 1024 512 4096 992 920 16690823448180281
        480439805247 1000000000000 DickeSol.rkmVPot_m2 DickeSol.rkmWinAnchor_m2)
        DickeSol.rkmWinSpec_m2, rfl⟩,
    ⟨rkm_mem_grid 2 8 rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
      DickeSol.rkmValid_m4, DickeSol.rkmSubLMax_m4_k1024,
      rkm_tbl17 (@DickeSol.RkmWinAnchorSpec.mk 4 1024 512 2048 496 918 8374647340518534
        340912357990 1000000000000 DickeSol.rkmVPot_m4 DickeSol.rkmWinAnchor_m4)
        DickeSol.rkmWinSpec_m4, rfl⟩,
    ⟨rkm_mem_grid 3 7 rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
      DickeSol.rkmValid_m8, DickeSol.rkmSubLMax_m8_k1024,
      rkm_tbl17 (@DickeSol.RkmWinAnchorSpec.mk 8 1024 512 1024 248 920 4208005866470537
        242252100412 1000000000000 DickeSol.rkmVPot_m8 DickeSol.rkmWinAnchor_m8)
        DickeSol.rkmWinSpec_m8, rfl⟩,
    ⟨rkm_mem_grid 4 6 rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
      DickeSol.rkmValid_m16, DickeSol.rkmSubLMax_m16_k1024,
      rkm_tbl17 (@DickeSol.RkmWinAnchorSpec.mk 16 1024 512 512 124 785 2117515629891086
        172398243679 1000000000000 DickeSol.rkmVPot_m16 DickeSol.rkmWinAnchor_m16)
        DickeSol.rkmWinSpec_m16, rfl⟩,
    ⟨rkm_mem_grid 5 5 rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
      DickeSol.rkmValid_m32, DickeSol.rkmSubLMax_m32_k1024,
      rkm_tbl17 (@DickeSol.RkmWinAnchorSpec.mk 32 1024 512 256 62 820 1063460268786042
        122445401453 1000000000000 DickeSol.rkmVPot_m32 DickeSol.rkmWinAnchor_m32)
        DickeSol.rkmWinSpec_m32, rfl⟩,
    ⟨rkm_mem_grid 6 4 rfl, hk_g, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
      DickeSol.rkmValid_m64, DickeSol.rkmSubLMax_m64_k1024,
      rkm_tbl17 (@DickeSol.RkmWinAnchorSpec.mk 64 1024 512 128 31 845 535055128480452
        87123384706 1000000000000 DickeSol.rkmVPot_m64 DickeSol.rkmWinAnchor_m64)
        DickeSol.rkmWinSpec_m64, rfl⟩]

private noncomputable def rkmWinSubSpec {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true)
    (hk : k = 1024) :
    DickeSol.JohnsonRampMuxSparseWalkSpec m 512 (johnsonRampKickMuxCellLMax m k) :=
  let pw := rkm_win_props h hk
  rkmSubSpecOf pw.1 (rkmVPot m) (rkmAnchors m) (rkm_le_of_add (d := 512) rfl)
    (fun _ ↦ pw.2.2.2.2.1) (fun _ ↦ pw.2.2.2.2.2.1) pw.2.2.2.2.2.2.1 pw.2.2.2.2.2.2.2.1
    pw.2.2.2.2.2.2.2.2.1 pw.2.2.2.2.2.2.2.2.2.1

private theorem rkm_n0_le {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true)
    (hk : k = 1024) : (rkmWinSubSpec h hk).n0 ≤ DickeSol.altN0 := Nat.le_refl DickeSol.altN0
private theorem rkm_hv_sub {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true)
    (hk : k = 1024) :
    ∀ j ≤ 512, (rkmWinSubSpec h hk).V j = ((rkmVPot m).getD j 0 : ℝ) / DickeSol.wdScaleR :=
  fun _ _ ↦ rfl

private noncomputable def rkmWinArm {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true) (hk : k = 1024) :
    OracleDynamicCircuit (Unitary (2 ^ johnsonRampKickMuxQubits n m k)) Var
      (johnsonRampKickMuxQubits n m k) ((n + 1) * m) :=
  let pw := rkm_win_props h hk
  DickeSol.rkmWinCellCircuit res pw.1 pw.2.1 pw.2.2.1 pw.2.2.2.1 (rkmWinSubSpec h hk)
    (rkm_n0_le h hk) (rkmVPot m) (rkm_hv_sub h hk) (rkmWinAnchor m)
    pw.2.2.2.2.2.2.2.2.2.2.1 n

private noncomputable def rkmSubArm {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isJohnsonRampKickMuxCell m k = true) (hk : ¬ k = 1024) :
    OracleDynamicCircuit (Unitary (2 ^ johnsonRampKickMuxQubits n m k)) Var
      (johnsonRampKickMuxQubits n m k) ((n + 1) * m) :=
  let p := rkm_sub512_props h hk
  DickeSol.rkmCellCircuit res p.1 p.2.1 (rkmVPot m) (rkmAnchors m) p.2.2.1
    (fun _ ↦ p.2.2.2.1) (fun _ ↦ p.2.2.2.2.2.1) p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
    p.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 n

/-- Dynamic circuit dispatching all `100` `RampKickMux` cells (`public section`). -/
noncomputable def findAllJohnsonRampKickMuxCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ johnsonRampKickMuxQubits n m k)) Var
      (johnsonRampKickMuxQubits n m k) ((n + 1) * m) :=
  if h : isJohnsonRampKickMuxCell m k = true then
    if hk : k = 1024 then rkmWinArm res n h hk else rkmSubArm res n h hk
  else .skip

/-- Exact probability-`1` recovery of `S` across all `100` supported cells. -/
theorem johnsonRampKickMux_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isJohnsonRampKickMuxCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ johnsonRampKickMuxQubits n m k)) ⦄
    (QProg.qSet ;; (findAllJohnsonRampKickMuxCircuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [rkm_targetSets_eq]
  unfold findAllJohnsonRampKickMuxCircuit; rw [dite_eq_left hcell, ← rkm_oracle_eq]
  by_cases hk : k = 1024
  · have pw := rkm_win_props hcell hk; rw [dite_eq_left hk]
    exact DickeSol.rkmWinCell_correctness res pw.1 pw.2.1 pw.2.2.1 pw.2.2.2.1
      (rkmWinSubSpec hcell hk) (rkm_n0_le hcell hk) (rkmVPot m) (rkm_hv_sub hcell hk)
      (rkmWinAnchor m) pw.2.2.2.2.2.2.2.2.2.2.1 hn hkN hS'
  · have hp := rkm_sub512_props hcell hk; rw [dite_eq_right hk]
    exact DickeSol.rkmCell_correctness res hp.1 hp.2.1 (rkmVPot m) (rkmAnchors m) hp.2.2.1
      (fun _ ↦ hp.2.2.2.1) (fun _ ↦ hp.2.2.2.2.2.1) hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
      hp.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1 hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across all `100` supported cells. -/
theorem johnsonRampKickMux_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isJohnsonRampKickMuxCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKickMuxCircuit res n m k).compile QProg.qAssign
                (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostJohnsonRampKickMux m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  by_cases hk : k = 1024
  · have pw := rkm_win_props hcell hk
    obtain ⟨n₁, hn₁⟩ := DickeSol.rkmWinCell_rel_cost (Var := Var) res pw.1 pw.2.1 pw.2.2.1
      pw.2.2.2.1 (rkmWinSubSpec hcell hk) (rkm_n0_le hcell hk) (rkmVPot m)
      (rkm_hv_sub hcell hk) (rkmWinAnchor m) pw.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
    refine ⟨q, fun S hS ↦ ?_,
      by rw [← rkm_targetSets_eq, ← rkm_vanilla_eq, pw.2.2.2.2.2.2.2.2.2.2.2]; exact hsum⟩
    unfold findAllJohnsonRampKickMuxCircuit
    rw [dite_eq_left hcell, dite_eq_left hk, ← rkm_oracle_eq]
    exact hq S (by rwa [rkm_targetSets_eq])
  · have hp := rkm_sub512_props hcell hk
    obtain ⟨n₁, hn₁⟩ := DickeSol.rkmCell_rel_cost (Var := Var) res hp.1 hp.2.1
      (rkmVPot m) (rkmAnchors m) hp.2.2.1 (fun _ ↦ hp.2.2.2.1) (fun _ ↦ hp.2.2.2.2.2.1)
      hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.2
    refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
    refine ⟨q, fun S hS ↦ ?_, by rw [← rkm_targetSets_eq, ← rkm_vanilla_eq]; exact hsum⟩
    unfold findAllJohnsonRampKickMuxCircuit
    rw [dite_eq_left hcell, dite_eq_right hk, ← rkm_oracle_eq]
    exact hq S (by rwa [rkm_targetSets_eq])

end
end QuantumComputation.Specs.GroverFindAll.FindAllJohnsonRampKickMux
