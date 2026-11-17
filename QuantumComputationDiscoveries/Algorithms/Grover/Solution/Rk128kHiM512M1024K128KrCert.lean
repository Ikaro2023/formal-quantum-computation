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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM512F256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM8K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM128K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM2K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256CoPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM8K128KrCert

/-
# Krotov `m ∈ {512, 1024}`, `k ∈ {16..128}` Certificate (`Rk128kHiM512M1024K128KrCert`)

QHL-verified module packaging all `8` cells `m ∈ {512, 1024}, k ∈ {16, 32, 64, 128}`
over `30` anchors (`16 + 14`; `397,960` F1272 / `405,145` Horner coord-ops at
`lTableMax = 2`, `useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll
namespace Rk128kHiM512M1024K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported (m, k) cells (m in {512, 1024}, k in {16, 32, 64, 128}, 8 cells). -/
def isHiTailM512M1024K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 512 then
    if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else if m == 1024 then
    if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor L_max(m, k) = 2 (2 * m <= 2048 <= 65536). -/
def hiTailM512M1024K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if isHiTailM512M1024K128KrotovCertCell m k then 2 else 1

/-- Total register qubit budget (CellLMax m k * m) * (n + 1) + k * n. -/
abbrev hiTailM512M1024K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (hiTailM512M1024K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified coprime relative-cost profile c(m, k): ℚ≥0 across all 8 supported cells. -/
def relCostHiTailM512M1024K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 512 then
    if k == 16 then NNRat.divNat 3750175009181 25000000000000
    else if k == 32 then NNRat.divNat 101792234239951 1000000000000000
    else if k == 64 then NNRat.divNat 70660484805033 1000000000000000
    else if k == 128 then NNRat.divNat 12650158017091 250000000000000
    else 1
  else if m == 1024 then
    if k == 16 then NNRat.divNat 74721135940909 500000000000000
    else if k == 32 then NNRat.divNat 12621924588223 125000000000000
    else if k == 64 then NNRat.divNat 34727173440933 500000000000000
    else if k == 128 then NNRat.divNat 2434837676117 50000000000000
    else 1
  else 1

/-- Cost profile metadata (n0 = 80000, constructive threshold). -/
def hiTailM512M1024K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isHiTailM512M1024K128KrotovCertCell, relCostHiTailM512M1024K128KrotovCert, fun _ _ ↦ 80000⟩

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private theorem hmk_cases {m k : ℕ}
    (h : isHiTailM512M1024K128KrotovCertCell m k = true) :
    (m = 512 ∨ m = 1024) ∧ (k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128) := by
  unfold isHiTailM512M1024K128KrotovCertCell at h
  by_cases hm5 : m = 512
  · subst hm5; refine ⟨Or.inl rfl, ?_⟩
    by_cases h1 : k = 16; · exact Or.inl h1
    by_cases h2 : k = 32; · exact Or.inr (Or.inl h2)
    by_cases h3 : k = 64; · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : k = 128; · exact Or.inr (Or.inr (Or.inr h4))
    simp [h1, h2, h3, h4] at h
  · by_cases hm10 : m = 1024
    · subst hm10; refine ⟨Or.inr rfl, ?_⟩
      by_cases h1 : k = 16; · exact Or.inl h1
      by_cases h2 : k = 32; · exact Or.inr (Or.inl h2)
      by_cases h3 : k = 64; · exact Or.inr (Or.inr (Or.inl h3))
      by_cases h4 : k = 128; · exact Or.inr (Or.inr (Or.inr h4))
      simp [h1, h2, h3, h4] at h
    · simp [hm5, hm10] at h

/-- Every supported `Rk128kHiM512M1024K128KrCert` cell lies on groverGrid × groverGrid. -/
theorem isHiTailM512M1024K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isHiTailM512M1024K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  rcases hmk_cases h with ⟨rfl | rfl, rfl | rfl | rfl | rfl⟩ <;> rfl

private lemma hmk_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma hmk_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma hmk_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private def hmkNatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem hmkNatEq_eq {x y : ℕ} (h : hmkNatEq x y = true) : x = y := by
  unfold hmkNatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def hmkIntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => hmkNatEq m n
  | Int.negSucc m, Int.negSucc n => hmkNatEq m n
  | _, _ => false
private theorem hmkIntEq_eq {a b : ℤ} (h : hmkIntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [hmkIntEq] at h; exact congrArg Int.ofNat (hmkNatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => dsimp only [hmkIntEq] at h; exact congrArg Int.negSucc (hmkNatEq_eq h)
private def hmkListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (hmkListEq eqF xr yr) false
  | _, _ => false
private theorem hmkListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : hmkListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [hmkListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev HmkSt := ℕ × ℕ × ℕ × List ℤ
private def hmkStEq (a b : HmkSt) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (hmkNatEq a1 b1)
      (cond (hmkNatEq a2 b2) (cond (hmkNatEq a3 b3) (hmkListEq hmkIntEq av bv) false) false) false
private theorem hmkStEq_eq {a b : HmkSt} (h : hmkStEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [hmkStEq] at h
  cases h1 : hmkNatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : hmkNatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : hmkNatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h
        exact Prod.ext (hmkNatEq_eq h1)
          (Prod.ext (hmkNatEq_eq h2) (Prod.ext (hmkNatEq_eq h3) (hmkListEq_eq (@hmkIntEq_eq) h)))
private def hmkAtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (hmkAtF rest) false
private theorem hmk_hd {b : Bool} {bs : List Bool} (h : hmkAtF (b :: bs) = true) : b = true := by
  unfold hmkAtF at h; cases b with
  | false => cases h
  | true => rfl
private theorem hmk_tl1 {b : Bool} {s : List Bool} (h : hmkAtF (b :: s) = true) :
    hmkAtF s = true := by
  unfold hmkAtF at h; cases b with
  | false => cases h
  | true => exact h
private theorem hmk_tl2 {a b : Bool} {s : List Bool} (h : hmkAtF (a :: b :: s) = true) :
    hmkAtF s = true := hmk_tl1 (hmk_tl1 h)
private theorem hmk_tl3 {a b c : Bool} {s : List Bool} (h : hmkAtF (a :: b :: c :: s) = true) :
    hmkAtF s = true := hmk_tl1 (hmk_tl2 h)
private theorem hmk_tl4 {a b c d : Bool} {s : List Bool}
    (h : hmkAtF (a :: b :: c :: d :: s) = true) : hmkAtF s = true := hmk_tl2 (hmk_tl2 h)
private theorem hmk_tl5 {a b c d e : Bool} {s : List Bool}
    (h : hmkAtF (a :: b :: c :: d :: e :: s) = true) : hmkAtF s = true := hmk_tl1 (hmk_tl4 h)
private theorem hmk_tl6 {a b c d e f : Bool} {s : List Bool}
    (h : hmkAtF (a :: b :: c :: d :: e :: f :: s) = true) : hmkAtF s = true := hmk_tl2 (hmk_tl4 h)
private theorem hmk_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem hmk_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev hmkM (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def hmkChkRow (m r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  hmkListEq hmkNatEq (DickeSol.rkm128kEvalRowLo12 m 2 r s) ro
private def hmkChkAnchors (m : ℕ) (xs : List DickeSol.RampKick128kAnchor) : Bool :=
  match xs with
  | [] => true
  | a :: rest =>
    match a with
    | ⟨rAct, segs, row⟩ => cond (hmkChkRow m rAct segs row) (hmkChkAnchors m rest) false
private theorem hmkChkAnchors_append {m : ℕ} {xs rest : List DickeSol.RampKick128kAnchor}
    (hxs : hmkChkAnchors m xs = true) (hrest : DickeSol.RampKick128kAnchorsSound m 2 rest) :
    DickeSol.RampKick128kAnchorsSound m 2 (xs ++ rest) := by
  induction xs with
  | nil => exact hrest
  | cons a tl ih =>
    rcases a with ⟨rAct, segs, row⟩; rw [List.cons_append]
    dsimp only [hmkChkAnchors, DickeSol.RampKick128kAnchorsSound] at hxs ⊢
    cases ha : hmkChkRow m rAct segs row with
    | false => rw [ha] at hxs; cases hxs
    | true =>
      rw [ha] at hxs; dsimp only [cond] at hxs; exact ⟨hmkListEq_eq (@hmkNatEq_eq) ha, ih hxs⟩
private def hmkChkSeg (m r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (st1 : HmkSt) : Bool := hmkStEq (DickeSol.rkm128kRunSegs m 2 r s l0 d0 p0 v0) st1
private def hmkChkFin (m r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Bool :=
  hmkListEq hmkNatEq (DickeSol.rkm128kFinalizeState
    (DickeSol.rkm128kRunSegs m 2 r s l0 d0 p0 v0)) ro
private def hmkSegBds (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def hmkTailOk (m r : ℕ) (rest : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Prop :=
  ∃ st, DickeSol.rkm128kRunSegs m 2 r rest l0 d0 p0 v0 = st ∧
    DickeSol.rkm128kFinalizeState st = ro
private theorem hmkTailEnd {m r : ℕ} {cLast : List DickeSol.Rkm128kSeg} {l0 d0 p0 : ℕ}
    {v0 : List ℤ} {ro : List ℕ} (h : hmkChkFin m r cLast l0 d0 p0 v0 ro = true) :
    hmkTailOk m r cLast l0 d0 p0 v0 ro := ⟨_, rfl, hmkListEq_eq (@hmkNatEq_eq) h⟩
private theorem hmkTailStep {m r : ℕ} {cCur rest : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {ro : List ℕ}
    (h1 : hmkChkSeg m r cCur l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : hmkTailOk m r rest l1 d1 p1 v1 ro) : hmkTailOk m r (cCur ++ rest) l0 d0 p0 v0 ro := by
  rcases h2 with ⟨st, hr, hf⟩; refine ⟨st, ?_, hf⟩
  unfold hmkChkSeg at h1; rw [DickeSol.rkm128kRunSegs_append, hmkStEq_eq h1]; exact hr
private theorem hmkCertSplit {m r : ℕ} {segs : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (hb : hmkSegBds r segs = true) (ht : hmkTailOk m r segs 1 0 1 [Int.ofNat DickeSol.wdScale] ro) :
    DickeSol.rkm128kEvalRowLo12 m 2 r segs = ro := by
  rcases ht with ⟨st, hr, hf⟩; exact DickeSol.rkm128kCertRow_of_runSegs hb hr hf
private def hmkChkCell (m k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) :
    Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 m k (v.getD k 0) n d)
private lemma hmk_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d
private lemma hmk_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (hmk_le_of_add h), rfl⟩

private def hmk512VPotP0 : List ℕ := [
  0, 28403554933221, 30328693038725, 33275405665413, 33664605244980, 33903136249625,
  34067146469266, 34188894594159, 34284383839878, 34362454473752, 34428387846239,
  34485549345996, 34536112542929, 42413841290405, 50005010656586, 34661808751886,
  34697730109736, 41586604058719, 48281386159748, 54797608559286, 61148836522620,
  67347000355350, 73402658614159, 34907513997684, 40705365369976, 46386076356621,
  51956471774310, 57422738469856, 62790505805818, 68064913544573, 73250669461328,
  78352098523744, 35125458052282, 40069882315866, 44941051799931, 49742128860177,
  54476054682381, 59145570349275, 63753235395708, 68301444208667, 72792440570402,
  77228330595333, 81611094272362, 85942595792042, 90224592811394, 94458744786950,
  98646620488058, 102789704786903 ]
private def hmk512VPotP1 : List ℕ := [
  106889404808563, 110947055513309, 114963924773927, 118941218002786, 122880082376524,
  126781610700299, 130646844948494, 134476779514383, 138272364197474, 142034506953947,
  145764076432764, 149461904317505, 153128787491821, 156765490044474, 160372745128250,
  163951256685558, 35813417420889, 39336444818422, 42832680744266, 46302727268202,
  49747164242694, 53166550433999, 56561424580298, 59932306382523, 63279697433038,
  66604082086871, 69905928279789, 73185688297117, 76443799496886, 79680684990579,
  82896754284475, 86092403884341, 89268017866008, 92423968414144, 95560616331371,
  98678311519693, 101777393436058, 104858191523729, 107921025621015, 110966206348802,
  113994035478207, 117004806279593, 119998803854083, 122976305448633, 125937580755653,
  128882892198091, 131812495200832, 134726638449207 ]
private def hmk512VPotP2 : List ℕ := [
  137625564135353, 140509508193114, 143378700522127, 146233365201695, 149073720695018,
  151899980044291, 154712351057185, 157511036485151, 160296234193996, 163068137327129,
  165826934461862, 168572809759118, 171305943106891, 174026510257768, 176734682960809,
  179430629088076, 182114512756057, 184786494442254, 187446731097148, 190095376251783,
  192732580121161, 195358489703653, 197973248876614, 200576998488369, 203169876446747,
  205752017804313, 208323554840452, 210884617140442, 213435331671650, 215975822856984,
  218506212645711, 221026620581767, 37254321028668 ]
private def hmk512VPot : List ℕ :=
  hmk512VPotP0 ++ (hmk512VPotP1 ++ hmk512VPotP2)
private def hmk512SegsR3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 19739112, 1, 26, []⟩, ⟨1, 10637785, 1, 20, []⟩, hmkM 1 614027 1 9 4 [15],
  ⟨1, 743963, 1, 10, []⟩ ]
private def hmk512RowR3 : List ℕ := [
  896804358, 53274040911, 945824718608 ]
private def hmk512SegsR4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 32527969, 3, 22, []⟩ ]
private def hmk512RowR4 : List ℕ := [
  2127672, 497341820, 39483847838, 960016680371 ]
private def hmk512SegsR5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 11554224, 1, 25, []⟩, ⟨1, 13861365, 2, 20, []⟩, ⟨1, 7586665, 1, 21, []⟩ ]
private def hmk512RowR5 : List ℕ := [
  271, 796058, 292801157, 31403656205, 968302746285 ]
private def hmk512SegsR6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 21160335, 3, 22, []⟩, ⟨1, 7497533, 1, 22, []⟩, ⟨1, 4662805, 1, 19, []⟩ ]
private def hmk512RowR6 : List ℕ := [
  1, 115, 208914, 176837058, 26091919745, 973731034137 ]
private def hmk512SegsR7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 33551342, 5, 23, []⟩ ]
private def hmk512RowR7 : List ℕ := [
  0, 2, 889, 14094, 106465526, 22332526165, 977560993289 ]
private def hmk512SegsR8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 33727744, 5, 24, []⟩ ]
private def hmk512RowR8 : List ℕ := [
  0, 0, 1, 1754, 23150, 62067636, 19531237553, 980406669864 ]
private def hmk512SegsR9 : List DickeSol.Rkm128kSeg := [
  ⟨1, 25873064, 2, 31, []⟩, hmkM 1 7125296 1 21 5 [28], ⟨1, 869887, 1, 9, []⟩ ]
private def hmk512RowR9 : List ℕ := [
  0, 0, 0, 39, 2221, 140769, 33723399, 17363316653, 982602816671 ]
private def hmk512SegsR10 : List DickeSol.Rkm128kSeg := [
  ⟨1, 18310284, 2, 26, []⟩, ⟨1, 15673720, 2, 24, []⟩ ]
private def hmk512RowR10 : List ℕ := [
  0, 0, 0, 0, 1, 2549, 318151, 15945474, 15627957971, 984355775689 ]
private def hmk512SegsR11 : List DickeSol.Rkm128kSeg := [
  hmkM 1 336 1 4 5 [24], hmkM 1 1579823 1 12 11 [1311], ⟨1, 3619820, 1, 17, []⟩,
  hmkM 1 8910903 1 27 12 [2307], hmkM 1 10 1 4 11 [1040], hmkM 1 10 1 4 10 [748],
  ⟨1, 7442029, 1, 24, []⟩, hmkM 1 9628396 1 28 1 [1], hmkM 1 1466375 1 11 12 [4077],
  hmkM 1 1433014 1 11 9 [404] ]
private def hmk512RowR11 : List ℕ := [
  0, 16, 214, 1202, 472, 2706, 8306, 505930, 5728595, 14246185744, 985747566398 ]
private def hmk512SegsR12 : List DickeSol.Rkm128kSeg := [
  hmkM 1 26798832 3 29 1 [1], hmkM 1 202442 1 6 1 [1], hmkM 1 6819997 1 24 10 [896],
  ⟨1, 344050, 1, 7, []⟩ ]
private def hmk512RowR12 : List ℕ := [
  0, 0, 0, 0, 0, 0, 44, 10535, 9321, 953328, 13053364452, 986945662055 ]
private def hmk512SegsR15 : List DickeSol.Rkm128kSeg := [
  ⟨1, 25620624, 4, 27, []⟩, hmkM 1 8281544 1 30 13 [8129], ⟨1, 461500, 1, 8, []⟩ ]
private def hmk512RowR15 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 364, 20178, 17386, 7480590, 10488567157, 989503914089 ]
private def hmk512SegsR16P0 : List DickeSol.Rkm128kSeg := [
  hmkM 1 1117476 1 12 14 [8192], hmkM 1 1117476 1 12 16 [49152], hmkM 1 1117476 1 12 17 [65536],
  hmkM 1 558738 1 10 17 [65536], ⟨1, 558739, 1, 10, []⟩, ⟨1, 1117476, 1, 12, []⟩,
  ⟨1, 1117477, 1, 12, []⟩, ⟨1, 1117476, 1, 12, []⟩, ⟨1, 1117477, 1, 13, []⟩,
  ⟨1, 1015122, 1, 12, []⟩, ⟨1, 1015123, 1, 12, []⟩, ⟨1, 1015122, 1, 12, []⟩,
  ⟨1, 1015123, 1, 12, []⟩, ⟨1, 852700, 1, 11, []⟩, ⟨1, 852701, 1, 11, []⟩,
  ⟨1, 852701, 1, 11, []⟩, ⟨1, 852701, 1, 11, []⟩, ⟨1, 716268, 1, 11, []⟩,
  ⟨1, 716268, 1, 11, []⟩, ⟨1, 716268, 1, 11, []⟩, ⟨1, 716268, 1, 11, []⟩,
  ⟨1, 649809, 1, 10, []⟩, ⟨1, 649810, 1, 10, []⟩, ⟨1, 649810, 1, 10, []⟩,
  ⟨1, 649810, 1, 10, []⟩, ⟨1, 929926, 1, 12, []⟩, ⟨1, 929927, 1, 12, []⟩,
  ⟨1, 917011, 1, 12, []⟩, ⟨1, 917012, 1, 12, []⟩, ⟨1, 656189, 1, 10, []⟩,
  ⟨1, 656189, 1, 10, []⟩, ⟨1, 647043, 1, 10, []⟩, ⟨1, 647043, 1, 10, []⟩,
  ⟨1, 1006487, 1, 12, []⟩, ⟨1, 777852, 1, 11, []⟩, hmkM 1 710195 1 11 1 [1],
  hmkM 1 644273 1 10 4 [12], hmkM 1 501126 1 9 7 [116], hmkM 1 387251 1 9 9 [404],
  hmkM 1 353585 1 8 10 [836], hmkM 1 320773 1 8 11 [1092], hmkM 1 223792 1 7 12 [2324],
  hmkM 1 226343 1 7 12 [2884], hmkM 1 178780 1 7 13 [4672], hmkM 1 133884 1 7 7 [71],
  hmkM 1 123893 1 6 10 [599], hmkM 1 113127 1 6 14 [10839], hmkM 1 98527 1 6 12 [2647] ]
private def hmk512SegsR16P1 : List DickeSol.Rkm128kSeg := [
  hmkM 1 85355 1 6 14 [10839], hmkM 1 74328 1 6 14 [10775], hmkM 1 64666 1 5 14 [10835],
  hmkM 1 56282 1 5 14 [10775], hmkM 1 48991 1 5 15 [19015], hmkM 1 43476 1 5 15 [19031],
  hmkM 1 36961 1 5 15 [19027], ⟨1, 32553, 1, 5, []⟩ ]
private def hmk512SegsR16 : List DickeSol.Rkm128kSeg :=
  hmk512SegsR16P0 ++ hmk512SegsR16P1
private def hmk512RowR16 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 1550, 31, 45380, 9839390171, 990160562445 ]
private def hmk512SegsR23 : List DickeSol.Rkm128kSeg := [
  hmkM 1 2125514 1 16 24 [8388608], ⟨1, 2125118, 1, 17, []⟩, ⟨1, 4250236, 1, 24, []⟩,
  ⟨1, 4250236, 1, 24, []⟩, ⟨1, 4250236, 1, 24, []⟩, ⟨1, 4250236, 1, 24, []⟩,
  ⟨1, 4250236, 1, 24, []⟩, hmkM 1 4250236 1 24 3 [5], hmkM 1 4250236 1 24 21 [1835281],
  hmkM 1 704691 1 10 8 [128] ]
private def hmk512RowR23 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 399, 12487, 204093, 118064, 110185307,
  6942297014, 992947181673 ]
private def hmk512SegsR32 : List DickeSol.Rkm128kSeg := [
  hmkM 1 8766917 2 29 33 [5427429376], hmkM 1 3641600 1 25 33 [8053063680],
  ⟨1, 3321498, 1, 24, []⟩, ⟨1, 3084061, 1, 23, []⟩, ⟨1, 2167302, 1, 19, []⟩,
  hmkM 1 2060974 1 18 4 [10], hmkM 1 1756358 1 17 6 [42], hmkM 1 1745872 1 17 10 [522],
  hmkM 1 1023158 1 13 8 [153], hmkM 1 1082736 1 13 12 [2078], hmkM 1 919926 1 12 15 [18453],
  hmkM 1 1030724 1 13 14 [13225], hmkM 1 448513 1 9 19 [270369], hmkM 1 599946 1 10 10 [849],
  hmkM 1 512940 1 10 23 [4990208], hmkM 1 361087 1 9 25 [28190212],
  hmkM 1 471450 1 10 27 [103678981], hmkM 1 365565 1 9 28 [212338438],
  hmkM 1 196180 1 7 28 [151922692], hmkM 1 200282 1 7 29 [286138442],
  hmkM 1 266893 1 8 26 [33849345], hmkM 1 152916 1 7 30 [577479169],
  hmkM 1 146754 1 7 22 [2852868], hmkM 1 121879 1 6 30 [537626754],
  hmkM 1 108349 1 6 30 [610502656], hmkM 1 93504 1 6 31 [1080721408],
  hmkM 1 5634 1 4 27 [72058881], hmkM 1 138289 1 7 31 [1078888450],
  hmkM 1 63343 1 5 31 [1147308292], hmkM 1 33948 1 5 31 [1112145920],
  hmkM 1 43586 1 5 31 [1143114753], hmkM 1 49521 1 5 26 [33555456] ]
private def hmk512RowR32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 9, 0, 1231, 512, 436,
  3557, 389462, 5060666451, 994938936676 ]
private def hmk512SegsR64 : List DickeSol.Rkm128kSeg := [
  ⟨1, 2342267, 1, 27, []⟩, ⟨1, 2092307, 1, 26, []⟩, ⟨1, 2092102, 1, 26, []⟩,
  ⟨1, 2092102, 1, 26, []⟩, ⟨1, 2066907, 1, 26, []⟩, ⟨1, 1816908, 1, 25, []⟩,
  ⟨1, 1888207, 1, 25, []⟩, ⟨1, 1888198, 1, 25, []⟩, ⟨1, 1712098, 1, 24, []⟩,
  ⟨1, 1712098, 1, 24, []⟩, ⟨1, 1475624, 1, 23, []⟩, hmkM 1 975623 1 19 4 [11],
  hmkM 1 2666799 1 29 7 [72], hmkM 1 1479337 1 23 19 [262274],
  hmkM 1 1705231 1 24 26 [51515392], ⟨1, 609791, 1, 17, []⟩, hmkM 1 859792 1 19 27 [67110016],
  hmkM 1 953147 1 19 42 [4260607690785], hmkM 1 935009 1 19 45 [17648020619776],
  hmkM 1 768829 1 18 52 [4033713025319936], hmkM 1 678192 1 17 56 [64226666066477058],
  hmkM 1 538770 1 16 58 [10998758410297376, 3], hmkM 1 504000 1 16 59 [48504474423263232, 4],
  hmkM 1 107366 1 11 60 [11277278449238016, 8], hmkM 1 379987 1 15 61 [11895070840586240, 18],
  hmkM 1 446287 1 15 62 [11895208279015424, 36], hmkM 1 3632 1 7 59 [11893004961841152, 5],
  hmkM 1 443741 1 15 63 [11330055024148480, 65], hmkM 1 149487 1 12 63 [2956045601210368, 73],
  hmkM 1 139378 1 12 63 [11400423751548928, 73], hmkM 1 113462 1 11 63 [2973088033538048, 73],
  ⟨1, 99920, 1, 11, []⟩ ]
private def hmk512RowR64P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]
private def hmk512RowR64P1 : List ℕ := [
  0, 0, 2, 18, 43, 105, 12, 2792, 70162, 3262, 108511, 15529, 2521, 1255161, 2702980824,
  997295559888 ]
private def hmk512RowR64 : List ℕ :=
  hmk512RowR64P0 ++ hmk512RowR64P1
private def hmk512R128C0 : List DickeSol.Rkm128kSeg := [
  hmkM 1 8742134 6 30 48 [263882790666240], hmkM 1 4263372 3 29 72 [12, 61440],
  hmkM 1 3632828 3 27 91 [1048595, 30064771072],
  hmkM 1 3317362 3 26 127 [175307340555, 1970324836974592, 28672],
  hmkM 1 2914146 2 30 129 [38390646639207494, 0, 98312],
  hmkM 1 2335199 2 27 123 [22217666165483766, 59456, 1536],
  hmkM 1 1694503 2 23 126 [4503599895811088, 2098336, 8192],
  hmkM 1 2185633 2 26 129 [1416789791785344, 139616116880, 65536] ]
private def hmk512R128C1 : List DickeSol.Rkm128kSeg := [
  hmkM 1 1329957 1 28 85 [1799368516702976, 268440132],
  hmkM 1 877637 1 24 103 [18014442336821888, 124016383934464],
  hmkM 1 971918 1 25 112 [25403391526568192, 36029071896936448],
  hmkM 1 848052 1 23 116 [35261717545280, 19656421584928768, 15],
  hmkM 1 658014 1 21 119 [11347509759201600, 57791539872530564, 114],
  hmkM 1 514930 1 19 121 [567348268630048, 50196101822676992, 501],
  hmkM 1 588046 1 20 123 [65870745776030736, 52580059257503753, 1589],
  hmkM 1 372864 1 18 124 [22894602411311136, 30000541087303170, 2337] ]
private def hmk512R128C2 : List DickeSol.Rkm128kSeg := [
  hmkM 1 348624 1 17 125 [36349854558003296, 41809295836188680, 6602],
  hmkM 1 180620 1 14 125 [37717716739555336, 1311739117371392, 4232],
  hmkM 1 312678 1 17 126 [34359738368, 5639761354031361, 8380],
  hmkM 1 201299 1 15 126 [1048576, 37480517775409152, 8917],
  hmkM 1 111868 1 13 126 [562949953421312, 4796435935526914, 8837],
  hmkM 1 201388 1 15 127 [567485438885888, 1416262580174848, 18949],
  hmkM 1 127594 1 13 127 [2076427709318152, 24006828484476928, 19333],
  hmkM 1 94372 1 12 127 [562949953421312, 1487094039969796, 19073] ]
private def hmk512R128C3 : List DickeSol.Rkm128kSeg := [
  hmkM 1 84019 1 12 127 [18682901579169792, 24006828484986112, 20100],
  hmkM 1 64629 1 11 127 [9889557336031745, 131072, 16384],
  hmkM 1 61389 1 11 127 [20829285715544064, 24007309520797700, 20133],
  hmkM 1 48100 1 11 127 [1407374883553280, 0, 16384],
  hmkM 1 37895 1 10 127 [4505944679587840, 23997963336425480, 17069],
  hmkM 1 36139 1 10 127 [1, 0, 16384], hmkM 1 30887 1 10 127 [71468255805953, 0, 16384],
  ⟨1, 21368, 1, 9, []⟩ ]
private def hmk512SegsR128 : List DickeSol.Rkm128kSeg :=
  hmk512R128C0 ++ (hmk512R128C1 ++ (hmk512R128C2 ++ hmk512R128C3))
private def hmk512RowR128P0 : List ℕ := [
  88, 112, 105, 174, 462, 185, 21, 480, 95, 36, 554, 0, 65, 112, 120, 3, 392, 10, 870, 215, 108,
  252, 137, 275, 223, 5, 0, 15, 34, 38, 223, 465, 168, 16, 91, 505, 2, 0, 3, 137, 40, 47, 49,
  47, 0, 85, 383, 62 ]
private def hmk512RowR128P1 : List ℕ := [
  447, 25, 59, 23, 52, 21, 220, 264, 17, 18, 13, 72, 5, 1076, 131, 88, 98, 86, 120, 42, 0, 1,
  1583, 27, 97, 949, 48, 20, 10, 42, 259, 111, 787, 61, 767, 1627, 543, 1161, 440, 389, 0, 1508,
  189, 26, 24, 834, 81, 921 ]
private def hmk512RowR128P2 : List ℕ := [
  1635, 1091, 2659, 1078, 1379, 6777, 7865, 2953, 2094, 785, 2988, 8435, 3, 2006, 345, 302,
  8382, 3283, 3160, 5453, 94, 16377, 62561, 37569, 314215, 1244063, 350472, 94648, 66370, 8709,
  1575867132, 998421777804 ]
private def hmk512RowR128 : List ℕ :=
  hmk512RowR128P0 ++ (hmk512RowR128P1 ++ hmk512RowR128P2)
private def hmk512R128V1P0 : List ℤ := [
  Int.negSucc 12193283208, Int.negSucc 4223880580, Int.ofNat 20171070309,
  Int.negSucc 9268826215, Int.negSucc 15860979523, Int.negSucc 4824744695,
  Int.negSucc 13009196569, Int.ofNat 10561581422, Int.negSucc 5247088655, Int.ofNat 25942269610,
  Int.ofNat 6667658708, Int.negSucc 17968882856, Int.negSucc 21179772775,
  Int.negSucc 2891831164, Int.negSucc 5538948175, Int.ofNat 5216316780, Int.ofNat 19657926155,
  Int.negSucc 15163405444, Int.negSucc 13693398028, Int.negSucc 4199868767,
  Int.ofNat 1708233989, Int.negSucc 10886076116, Int.ofNat 1561486815, Int.ofNat 7074567467,
  Int.ofNat 16155732938, Int.negSucc 11723824228, Int.ofNat 14495059433, Int.ofNat 27138322693,
  Int.ofNat 16316677791, Int.negSucc 3388786040, Int.negSucc 4903438296, Int.negSucc 847690555,
  Int.negSucc 5026849576, Int.ofNat 31875283749, Int.negSucc 21868852355, Int.ofNat 5868880789,
  Int.negSucc 171202170, Int.ofNat 5512109938, Int.negSucc 418424851, Int.ofNat 9961772928,
  Int.negSucc 1890591024, Int.negSucc 11145346190, Int.ofNat 1628864813, Int.ofNat 3560500849,
  Int.ofNat 8201841681, Int.ofNat 6279276905, Int.negSucc 2863713831, Int.ofNat 12948882826 ]
private def hmk512R128V1P1 : List ℤ := [
  Int.ofNat 8312127239, Int.ofNat 10222766234, Int.ofNat 6509718416, Int.negSucc 14176735100,
  Int.ofNat 10197051686, Int.ofNat 5372607376, Int.negSucc 10123796160, Int.negSucc 25844001707,
  Int.negSucc 8768439027, Int.ofNat 5229488225, Int.ofNat 13247977143, Int.negSucc 240017947,
  Int.ofNat 28989899216, Int.ofNat 17630409841, Int.negSucc 1729660267, Int.ofNat 6220569039,
  Int.negSucc 4751914494, Int.ofNat 9766060055, Int.negSucc 12386382577,
  Int.negSucc 39800403074, Int.negSucc 1498736703, Int.ofNat 10008453680, Int.ofNat 18326514042,
  Int.ofNat 8073804124, Int.ofNat 8938555551, Int.ofNat 14458658864, Int.ofNat 1651549578,
  Int.ofNat 15124080506, Int.ofNat 9744400197, Int.negSucc 12645618945, Int.negSucc 1857024664,
  Int.negSucc 1642349012, Int.negSucc 5241183856, Int.ofNat 11761718914,
  Int.negSucc 11351035583, Int.negSucc 808093317, Int.ofNat 33933259746, Int.ofNat 10635733090,
  Int.negSucc 20625414023, Int.ofNat 29156721572, Int.ofNat 26273565304, Int.ofNat 22225615179,
  Int.ofNat 189676784, Int.negSucc 48868354042, Int.ofNat 39520144494, Int.negSucc 4214695525,
  Int.ofNat 18925775687, Int.ofNat 2808776206 ]
private def hmk512R128V1P2 : List ℤ := [
  Int.ofNat 48816001481, Int.ofNat 128861254202, Int.ofNat 288841635023, Int.ofNat 645781087474,
  Int.ofNat 1240733755566, Int.ofNat 2517967384311, Int.ofNat 4839383049899,
  Int.ofNat 8735196547633, Int.ofNat 15223318152429, Int.ofNat 25363721809867,
  Int.ofNat 40566144489617, Int.ofNat 62111421454751, Int.ofNat 91049617311148,
  Int.ofNat 127488468524834, Int.ofNat 171018019183055, Int.ofNat 218790316597894,
  Int.ofNat 267465015561943, Int.ofNat 311248197868003, Int.ofNat 344699325827849,
  Int.ofNat 362641859760093, Int.ofNat 361375729864833, Int.ofNat 340586202703492,
  Int.ofNat 302301299461398, Int.ofNat 251633338823180, Int.ofNat 195928268569321,
  Int.ofNat 141492162146318, Int.ofNat 94236695843822, Int.ofNat 57221495664956,
  Int.ofNat 31444851488392, Int.ofNat 15106802619712, Int.ofNat 5871490787249,
  Int.ofNat 1672475458487, Int.negSucc 299074292291 ]
private def hmk512R128V1 : List ℤ :=
  hmk512R128V1P0 ++ (hmk512R128V1P1 ++ hmk512R128V1P2)
private def hmk512R128V2P0 : List ℤ := [
  Int.negSucc 17786737767, Int.negSucc 2983694017, Int.ofNat 2815486161, Int.ofNat 15150673415,
  Int.negSucc 2371734415, Int.negSucc 23315378670, Int.ofNat 16430216527,
  Int.negSucc 11167005588, Int.ofNat 571185194, Int.negSucc 1453673990, Int.ofNat 5589990672,
  Int.negSucc 8610729391, Int.ofNat 20556743324, Int.ofNat 21424364983, Int.negSucc 11922785466,
  Int.negSucc 6307520966, Int.ofNat 23176041760, Int.ofNat 22675897719, Int.negSucc 890419289,
  Int.negSucc 6187273555, Int.ofNat 24256220917, Int.negSucc 14302224116, Int.ofNat 199114718,
  Int.negSucc 21758589202, Int.ofNat 1209250327, Int.negSucc 12360376948,
  Int.negSucc 29101815105, Int.negSucc 6037625293, Int.ofNat 15579353306,
  Int.negSucc 1314111790, Int.ofNat 3880149598, Int.ofNat 12221053320, Int.negSucc 6604378068,
  Int.ofNat 9514322247, Int.ofNat 2894832812, Int.negSucc 3371249893, Int.ofNat 3271760139,
  Int.ofNat 5416640716, Int.negSucc 5602829708, Int.negSucc 4453189637, Int.negSucc 13736262473,
  Int.ofNat 6035100505, Int.negSucc 18327321871, Int.negSucc 20152069591, Int.ofNat 1090257534,
  Int.ofNat 2985409890, Int.negSucc 3086113193, Int.ofNat 2094447398 ]
private def hmk512R128V2P1 : List ℤ := [
  Int.negSucc 13116417904, Int.negSucc 25336460159, Int.negSucc 2870582185,
  Int.negSucc 5240773568, Int.negSucc 14538827889, Int.ofNat 6072296598, Int.ofNat 463440546,
  Int.ofNat 6086064526, Int.ofNat 10152007045, Int.ofNat 9797579906, Int.negSucc 6718131442,
  Int.negSucc 28673223755, Int.negSucc 6140409278, Int.negSucc 15123168665,
  Int.ofNat 4159634179, Int.ofNat 6980688777, Int.ofNat 7564395914, Int.ofNat 20869707006,
  Int.ofNat 12115025799, Int.ofNat 996558706, Int.negSucc 5329957620, Int.negSucc 20251749809,
  Int.ofNat 28445264182, Int.ofNat 5346540911, Int.ofNat 2866239960, Int.negSucc 763960416,
  Int.negSucc 17617493175, Int.ofNat 27099706729, Int.ofNat 21708156186, Int.ofNat 1256224548,
  Int.ofNat 15594195590, Int.ofNat 184121440, Int.negSucc 16571559956, Int.negSucc 23244907901,
  Int.negSucc 14538450362, Int.negSucc 8282019323, Int.ofNat 14306407675,
  Int.negSucc 15991964212, Int.ofNat 55804242822, Int.negSucc 19652735643,
  Int.ofNat 27831769906, Int.ofNat 10453520118, Int.ofNat 20015995370, Int.negSucc 30390432029,
  Int.ofNat 2216231695, Int.ofNat 29816690893, Int.negSucc 55728132, Int.negSucc 27660785279 ]
private def hmk512R128V2P2 : List ℤ := [
  Int.ofNat 25320237919, Int.negSucc 23262664505, Int.ofNat 40266443843, Int.ofNat 71075468484,
  Int.negSucc 25046058983, Int.negSucc 64709119838, Int.negSucc 37245304766,
  Int.ofNat 107409131562, Int.negSucc 19054672104, Int.negSucc 5495833079,
  Int.negSucc 14696890238, Int.ofNat 66595129092, Int.ofNat 83438899157,
  Int.negSucc 70492757738, Int.negSucc 169123394, Int.negSucc 1354946287,
  Int.negSucc 46849612031, Int.ofNat 82212209785, Int.negSucc 60015189773,
  Int.negSucc 37911123215, Int.ofNat 113185696227, Int.ofNat 11281565505,
  Int.negSucc 202452181926, Int.negSucc 393544346281, Int.ofNat 94952328657,
  Int.ofNat 1414685096300, Int.ofNat 417124311380, Int.ofNat 2623800540363,
  Int.ofNat 27638534621463, Int.ofNat 150093088600953, Int.ofNat 390171832669250,
  Int.ofNat 644636098139442, Int.ofNat 639459976250603 ]
private def hmk512R128V2 : List ℤ :=
  hmk512R128V2P0 ++ (hmk512R128V2P1 ++ hmk512R128V2P2)
private def hmk512R128V3P0 : List ℤ := [
  Int.negSucc 11247261018, Int.negSucc 11695730254, Int.negSucc 4718281514,
  Int.ofNat 5651494727, Int.negSucc 22452657393, Int.negSucc 4556437613, Int.ofNat 23220348070,
  Int.ofNat 6553978501, Int.ofNat 19203957269, Int.negSucc 8692182192, Int.negSucc 7814358479,
  Int.negSucc 22044799372, Int.ofNat 5488299386, Int.ofNat 9186517347, Int.negSucc 2700827929,
  Int.negSucc 15404564419, Int.negSucc 811354886, Int.negSucc 7242392236, Int.ofNat 32110552186,
  Int.ofNat 23007957330, Int.ofNat 1202313241, Int.ofNat 14427548313, Int.ofNat 3210668652,
  Int.negSucc 15995834217, Int.negSucc 17624045539, Int.ofNat 6919203530, Int.ofNat 1942452127,
  Int.negSucc 7362689082, Int.ofNat 1457549782, Int.ofNat 10361279532, Int.ofNat 20465827307,
  Int.ofNat 15215109622, Int.ofNat 12006746047, Int.ofNat 9766837109, Int.ofNat 6585041411,
  Int.ofNat 21023973585, Int.ofNat 2436288489, Int.negSucc 7274636969, Int.ofNat 2871487235,
  Int.negSucc 1210516687, Int.negSucc 10697418647, Int.ofNat 10112664172, Int.ofNat 10122217093,
  Int.ofNat 909196644, Int.ofNat 1311831025, Int.negSucc 88553600, Int.ofNat 747506036,
  Int.negSucc 20312557979 ]
private def hmk512R128V3P1 : List ℤ := [
  Int.ofNat 7664190518, Int.negSucc 18326554061, Int.ofNat 15396815001, Int.negSucc 4635907758,
  Int.negSucc 3993878162, Int.ofNat 6640390213, Int.ofNat 11862216742, Int.ofNat 15151932244,
  Int.negSucc 10899687584, Int.negSucc 7401142858, Int.ofNat 3259478694, Int.negSucc 6688100983,
  Int.negSucc 5477477633, Int.negSucc 19401986068, Int.ofNat 11096353746, Int.ofNat 29669972093,
  Int.ofNat 427220440, Int.ofNat 1770715168, Int.ofNat 5140723722, Int.ofNat 2736803046,
  Int.negSucc 18172077175, Int.negSucc 6231983308, Int.negSucc 28768955681,
  Int.negSucc 7049756159, Int.ofNat 25414585961, Int.negSucc 5423287690,
  Int.negSucc 31054540673, Int.negSucc 9220181591, Int.ofNat 3585244881, Int.ofNat 13625727723,
  Int.ofNat 6532989498, Int.ofNat 4802973411, Int.ofNat 7211618394, Int.ofNat 24833393395,
  Int.negSucc 27804872938, Int.negSucc 34444564917, Int.negSucc 33804522346,
  Int.negSucc 6908415052, Int.negSucc 34055169176, Int.negSucc 26799155542,
  Int.ofNat 16823642133, Int.ofNat 5875023911, Int.negSucc 36924101157, Int.negSucc 13068353785,
  Int.negSucc 12420987359, Int.ofNat 15872230680, Int.ofNat 23982869846, Int.negSucc 14639687952
  ]
private def hmk512R128V3P2 : List ℤ := [
  Int.negSucc 33441106668, Int.ofNat 40485242866, Int.negSucc 11477719273,
  Int.ofNat 67057406144, Int.ofNat 43023622388, Int.ofNat 14896152169, Int.negSucc 68296558897,
  Int.negSucc 100316214719, Int.ofNat 41501415974, Int.ofNat 47666685201, Int.ofNat 27702757560,
  Int.ofNat 49109184670, Int.ofNat 96276423468, Int.ofNat 2363615471, Int.ofNat 46169103600,
  Int.negSucc 13515106000, Int.negSucc 9469131426, Int.negSucc 88409590651,
  Int.negSucc 51342232478, Int.ofNat 86622456959, Int.ofNat 35107318713,
  Int.negSucc 72768765712, Int.negSucc 130514430580, Int.ofNat 251529291929,
  Int.negSucc 139779569530, Int.negSucc 346533637390, Int.ofNat 910207335398,
  Int.negSucc 951808271018, Int.ofNat 467043535238, Int.ofNat 257074157592,
  Int.ofNat 6482822694972, Int.ofNat 208726112020779, Int.ofNat 977951458295477 ]
private def hmk512R128V3 : List ℤ :=
  hmk512R128V3P0 ++ (hmk512R128V3P1 ++ hmk512R128V3P2)
private def hmk512AncLo : List DickeSol.RampKick128kAnchor := [
  ⟨3, hmk512SegsR3, hmk512RowR3⟩, ⟨4, hmk512SegsR4, hmk512RowR4⟩,
  ⟨5, hmk512SegsR5, hmk512RowR5⟩, ⟨6, hmk512SegsR6, hmk512RowR6⟩,
  ⟨7, hmk512SegsR7, hmk512RowR7⟩, ⟨8, hmk512SegsR8, hmk512RowR8⟩,
  ⟨9, hmk512SegsR9, hmk512RowR9⟩, ⟨10, hmk512SegsR10, hmk512RowR10⟩,
  ⟨11, hmk512SegsR11, hmk512RowR11⟩, ⟨12, hmk512SegsR12, hmk512RowR12⟩,
  ⟨15, hmk512SegsR15, hmk512RowR15⟩, ⟨16, hmk512SegsR16, hmk512RowR16⟩,
  ⟨23, hmk512SegsR23, hmk512RowR23⟩, ⟨32, hmk512SegsR32, hmk512RowR32⟩ ]
private def hmk512Anc : List DickeSol.RampKick128kAnchor :=
  hmk512AncLo ++
    [⟨64, hmk512SegsR64, hmk512RowR64⟩, ⟨128, hmk512SegsR128, hmk512RowR128⟩]
private theorem hmk512B0 : hmkAtF [
    DickeSol.rkm128kCheckTable 512 128 2 true hmk512VPot hmk512Anc,
    hmkChkCell 512 16 2 3750175009181 25000000000000 hmk512VPot hmk512Anc,
    hmkChkCell 512 32 2 101792234239951 1000000000000000 hmk512VPot hmk512Anc,
    hmkChkCell 512 64 2 70660484805033 1000000000000000 hmk512VPot hmk512Anc,
    hmkChkCell 512 128 2 12650158017091 250000000000000 hmk512VPot hmk512Anc,
    hmkSegBds 128 hmk512SegsR128, hmkChkAnchors 512 hmk512AncLo
  ] = true := by decide +kernel
private theorem hmk512B1 :
    hmkChkRow 512 64 hmk512SegsR64 hmk512RowR64 = true := by decide +kernel
private theorem hmk512B2 :
    hmkChkSeg 512 128 hmk512R128C0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (1, 128, 30379456, hmk512R128V1) = true := by
  decide +kernel
private theorem hmk512B3 :
    hmkChkSeg 512 128 hmk512R128C1 1 128 30379456 hmk512R128V1
      (1, 128, 35398084, hmk512R128V2) = true := by
  decide +kernel
private theorem hmk512B4 :
    hmkChkSeg 512 128 hmk512R128C2 1 128 35398084 hmk512R128V2
      (1, 128, 35476594, hmk512R128V3) = true := by
  decide +kernel
private theorem hmk512B5 :
    hmkChkFin 512 128 hmk512R128C3 1 128 35476594 hmk512R128V3
      hmk512RowR128 = true := by decide +kernel
private theorem hmk512Row128Sound :
    DickeSol.rkm128kEvalRowLo12 512 2 128 hmk512SegsR128 = hmk512RowR128 := by
  apply hmkCertSplit (hmk_hd (hmk_tl5 hmk512B0)); unfold hmk512SegsR128
  exact hmkTailStep hmk512B2
    (hmkTailStep hmk512B3 (hmkTailStep hmk512B4 (hmkTailEnd hmk512B5)))
private theorem hmk512Valid :
    DickeSol.RampKick128kTableValid 512 128 2 true hmk512VPot hmk512Anc :=
  DickeSol.rkm128kCheckTable_sound
    (hmkChkAnchors_append (hmk_hd (hmk_tl6 hmk512B0))
      ⟨hmkListEq_eq (@hmkNatEq_eq) hmk512B1, ⟨hmk512Row128Sound, trivial⟩⟩)
    (hmk_hd hmk512B0)

private def hmk1024VPotP0 : List ℕ := [
  0, 20084346303086, 21438047432513, 23518310662050, 23787563642206, 23950189506352,
  24060059781270, 24139995858361, 24201319014096, 24277315055627, 24290624015176,
  30346282273985, 24354120092353, 29924515510042, 24402942252763, 29588698169518,
  24442633806153, 29313803290218, 34047729112422, 38655394158855, 43146390520590,
  47529154197619, 51811151216971, 55999026918079, 60098726939739, 64115596200357,
  68054460574095, 71919694822290, 75715279505381, 79444848984198, 83111732158514,
  86718987242290, 24638140063757, 28134375989601, 31578812964093, 34973687110392,
  38321078160907, 41622924353825, 44881035553594, 48097104847490, 51272718829157,
  54409366746384, 57508448662749, 60571282760035, 63599111889440, 66593109463930,
  69554384770950, 72483987773691 ]
private def hmk1024VPotP1 : List ℕ := [
  75382913459837, 78252105788850, 81092461282173, 83904832295067, 86690030003912,
  89448827138645, 92181960486418, 94890133189459, 97574016857440, 100234253512334,
  102871457381712, 105486216554673, 108079094513051, 110650631549190, 113201346080398,
  115731735869125, 24891644266667, 27382800829768, 29855012961560, 32308706389668,
  34744291131701, 37162162295068, 39562700825191, 41946274206123, 44313237117225,
  46663932049223, 48998689882670, 51317830431587, 53621662954804, 55910486637319,
  58184591043799, 60444256546160, 62689754727028, 64921348760705, 67139293773171,
  69343837182506, 71535219021021, 73713672240280, 75879423000120, 78032690942677,
  80173689452353, 82302625902612, 84419701890390, 86525113458890, 88619051309444,
  90701701003098, 92773243152521, 94833853604796 ]
private def hmk1024VPotP2 : List ℕ := [
  96883703615626, 98922960015432, 100951785367805, 102970338120742, 104978772751051,
  106977239902314, 108965886516744, 110944855961267, 112914288148136, 114874319650367,
  116825083812255, 118766710855238, 120699327979336, 122623059460394, 124538026743339,
  126444348531643, 128342140873189, 130231517242705, 132112588620942, 133985463570742,
  135850248310151, 137707046782714, 139555960725085, 141397089732069, 143230531319227,
  145056380983144, 146874732259471, 148685676778835, 150489304320723, 152285702865417,
  154074958644071, 155857156187013, 25351620321019 ]
private def hmk1024VPot : List ℕ :=
  hmk1024VPotP0 ++ (hmk1024VPotP1 ++ hmk1024VPotP2)
private def hmk1024SegsR3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 22430263, 2, 23, []⟩ ]
private def hmk1024RowR3 : List ℕ := [
  943656408, 53160483997, 945890589617 ]
private def hmk1024SegsR4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 22985270, 3, 22, []⟩ ]
private def hmk1024RowR4 : List ℕ := [
  3029300, 548092334, 39357628350, 960091244497 ]
private def hmk1024SegsR5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23314714, 4, 22, []⟩ ]
private def hmk1024RowR5 : List ℕ := [
  2692, 1557045, 344651368, 31270630403, 968383158461 ]
private def hmk1024SegsR6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 16172786, 3, 22, []⟩, ⟨1, 7361113, 2, 19, []⟩ ]
private def hmk1024RowR6 : List ℕ := [
  0, 829, 766780, 227914273, 25953380928, 973817937153 ]
private def hmk1024SegsR7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 15801366, 3, 24, []⟩, ⟨1, 7889613, 2, 21, []⟩ ]
private def hmk1024RowR7 : List ℕ := [
  0, 0, 115, 351770, 155377595, 22190295991, 977653974484 ]
private def hmk1024SegsR8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23809654, 5, 24, []⟩ ]
private def hmk1024RowR8 : List ℕ := [
  0, 0, 0, 6, 138897, 107637541, 19385953687, 980506269813 ]
private def hmk1024SegsR9 : List DickeSol.Rkm128kSeg := [
  ⟨1, 15469774, 2, 28, []⟩, hmkM 1 6220482 1 24 9 [341], hmkM 1 13516 1 4 9 [341],
  hmkM 1 2226153 1 15 10 [966] ]
private def hmk1024RowR9 : List ℕ := [
  0, 0, 0, 0, 150, 38383, 74921019, 17216541665, 982708498616 ]
private def hmk1024SegsR10 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23978494, 4, 26, []⟩ ]
private def hmk1024RowR10 : List ℕ := [
  0, 0, 0, 0, 0, 364, 2534, 51824041, 15485639076, 984462533872 ]
private def hmk1024SegsR12 : List DickeSol.Rkm128kSeg := [
  ⟨1, 18793801, 4, 25, []⟩, ⟨1, 5300816, 1, 25, []⟩ ]
private def hmk1024RowR12 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 713, 31426, 23222312, 12895838675, 987080906694 ]
private def hmk1024SegsR14 : List DickeSol.Rkm128kSeg := [
  hmkM 1 10150967 2 27 15 [32767], ⟨1, 14029716, 3, 26, []⟩ ]
private def hmk1024RowR14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 826, 122216, 8459978, 11057117989, 988934298774 ]
private def hmk1024SegsR16 : List DickeSol.Rkm128kSeg := [
  ⟨1, 2173062, 1, 22, []⟩, ⟨1, 1086610, 1, 16, []⟩, ⟨1, 1086535, 1, 16, []⟩,
  ⟨1, 1086528, 1, 16, []⟩, ⟨1, 1086529, 1, 16, []⟩, ⟨1, 2173057, 1, 22, []⟩,
  ⟨1, 2173057, 1, 22, []⟩, ⟨1, 2173057, 1, 22, []⟩, ⟨1, 2173057, 1, 21, []⟩,
  hmkM 1 2173057 1 22 1 [1], hmkM 1 940680 1 16 2 [3], ⟨1, 1441710, 1, 18, []⟩,
  ⟨1, 1441710, 1, 18, []⟩, ⟨1, 1441710, 1, 18, []⟩, hmkM 1 1441710 1 18 14 [14337],
  ⟨1, 155929, 1, 10, []⟩ ]
private def hmk1024RowR16 : List ℕ := [
  7, 4, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2689, 4980, 1754218, 9689038872, 990309199041 ]
private def hmk1024SegsR32 : List DickeSol.Rkm128kSeg := [
  ⟨1, 5864457, 2, 29, []⟩, ⟨1, 3271285, 1, 30, []⟩, ⟨1, 2334892, 1, 24, []⟩,
  ⟨1, 2552406, 1, 26, []⟩, ⟨1, 1147520, 1, 16, []⟩, ⟨1, 2124599, 1, 23, []⟩,
  ⟨1, 912512, 1, 15, []⟩, ⟨1, 1061431, 1, 16, []⟩, hmkM 1 963178 1 15 2 [3],
  hmkM 1 748779 1 13 2 [2], hmkM 1 578962 1 12 8 [161], hmkM 1 528360 1 11 12 [3459],
  hmkM 1 479575 1 11 17 [115971], hmkM 1 372872 1 10 21 [1883393],
  hmkM 1 288279 1 9 24 [15501444], hmkM 1 263288 1 9 26 [52986368],
  hmkM 1 160626 1 8 27 [77996033], hmkM 1 191464 1 8 28 [178820097],
  hmkM 1 142107 1 7 29 [311197986], hmkM 1 203238 1 8 30 [581476618],
  hmkM 1 118866 1 7 30 [612794890], hmkM 1 102275 1 7 31 [1143513666],
  hmkM 1 61056 1 6 31 [1216741920], hmkM 1 67682 1 6 15 [16928] ]
private def hmk1024RowR32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 539, 38, 397,
  1001967, 4899808414, 995099187349 ]
private def hmk1024SegsR64 : List DickeSol.Rkm128kSeg := [
  hmkM 1 1454055 1 23 65 [43356252349143040, 306],
  hmkM 1 1454055 1 23 63 [30680927156174848, 100],
  hmkM 1 1454055 1 25 65 [66760129357283328, 308],
  hmkM 1 1454056 1 26 61 [42820484101832704, 18],
  hmkM 1 1443252 1 27 65 [47432313146966016, 373],
  hmkM 1 1443253 1 27 65 [1191870604509184, 358],
  hmkM 1 1182663 1 23 65 [71213169107795968, 346],
  hmkM 1 1182664 1 24 64 [9007199254740993, 144], hmkM 1 1162189 1 23 60 [45, 10],
  hmkM 1 1162189 1 23 10 [645], hmkM 1 884417 1 20 11 [1664], hmkM 1 884417 1 19 13 [7018],
  hmkM 1 768685 1 18 7 [97], hmkM 1 768686 1 18 24 [13148224],
  hmkM 1 1395890 1 26 30 [579499271], hmkM 1 1082009 1 22 36 [34395193347],
  hmkM 1 786123 1 18 37 [79591129237], hmkM 1 909868 1 19 42 [2891131781761],
  hmkM 1 583110 1 15 45 [17671645560832], hmkM 1 613845 1 16 48 [164157968660565],
  hmkM 1 589975 1 15 50 [769675629895989], hmkM 1 234215 1 10 52 [4385195969110273],
  hmkM 1 244894 1 10 54 [16510336999959137], hmkM 1 226122 1 10 56 [59312761787695649],
  hmkM 1 360690 1 12 58 [23258287306825729, 3], hmkM 1 106483 1 8 59 [59155933187801600, 5],
  hmkM 1 352030 1 12 60 [23406442187128838, 9], hmkM 1 562 1 4 61 [571746046705664, 18],
  hmkM 1 212270 1 9 50 [564101006821506], hmkM 1 6734 1 4 62 [642114792980480, 32],
  hmkM 1 189079 1 9 59 [23760768401410061, 4], hmkM 1 35605 1 6 59 [24534502462195721, 4],
  hmkM 1 3437 1 4 63 [22808269206587392, 68], hmkM 1 45534 1 6 62 [36028840237074441, 32],
  hmkM 1 37124 1 6 63 [24004606853908992, 68], hmkM 1 10024 1 4 59 [77577881600, 4],
  hmkM 1 51280 1 6 63 [24004548603445896, 68], hmkM 1 27336 1 5 59 [19421773401423874, 4],
  hmkM 1 13241 1 4 63 [24004537857640450, 68], hmkM 1 24794 1 5 34 [8589967888] ]
private def hmk1024RowR64P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 4, 9, 0, 0, 0, 1, 0, 1, 0, 8, 0, 19, 32, 28, 28, 0, 48,
  113, 3, 1, 0, 0, 0, 0, 3, 7, 1, 14, 3, 7, 0, 3, 0, 0, 2, 10 ]
private def hmk1024RowR64P1 : List ℕ := [
  0, 2, 0, 28, 2, 36, 1, 3, 55, 29, 12876, 23710, 2239, 76124, 2525916391, 997473965464 ]
private def hmk1024RowR64 : List ℕ :=
  hmk1024RowR64P0 ++ hmk1024RowR64P1
private def hmk1024R128C0 : List DickeSol.Rkm128kSeg := [
  hmkM 1 5995697 6 30 71 [36020000925941760, 32640], hmkM 1 2942452 3 29 97 [58, 1648985425920],
  hmkM 1 2661421 3 28 115 [126467, 71988316215443456, 7],
  hmkM 1 2256345 3 26 126 [17149989582, 16888498602639360, 16380],
  hmkM 1 1664654 2 27 128 [1125427049492498, 0, 64544],
  hmkM 1 1633076 2 27 128 [40683004002368, 0, 63488],
  hmkM 1 1420953 2 26 128 [11258999068951104, 0, 32768],
  hmkM 1 1000398 2 22 68 [68719485056, 2304] ]
private def hmk1024R128C1 : List DickeSol.Rkm128kSeg := [
  hmkM 1 927983 1 29 95 [19439365579112721, 274877907337],
  hmkM 1 856221 1 28 98 [1408096310274180, 4352233968078],
  hmkM 1 540034 1 23 96 [68669265415241776, 917937436955],
  hmkM 1 544343 1 23 84 [9857122019901568, 218136578],
  hmkM 1 279792 1 18 60 [1143629817315330, 11],
  hmkM 1 577511 1 23 88 [43285882999949440, 2861945771],
  hmkM 1 370292 1 20 119 [1374389534720, 38654430786093568, 114],
  hmkM 1 316150 1 19 121 [536870912, 38935974482280448, 401] ]
private def hmk1024R128C2 : List DickeSol.Rkm128kSeg := [
  hmkM 1 114080 1 14 122 [68719476736, 47873835785003040, 598],
  hmkM 1 302374 1 19 124 [4398583382016, 48002483477282849, 3412],
  hmkM 1 150780 1 15 125 [4194304, 11868128510216192, 6481],
  hmkM 1 66390 1 12 125 [0, 2964559434416136, 4436],
  hmkM 1 179841 1 16 126 [1024, 20312377811535874, 9041],
  hmkM 1 104750 1 14 126 [0, 3000017476386818, 8789],
  hmkM 1 138283 1 15 124 [263168, 18061127753662466, 2113],
  hmkM 1 10038 1 9 127 [0, 20453665055703042, 19028] ]
private def hmk1024R128C3 : List DickeSol.Rkm128kSeg := [
  hmkM 1 59485 1 12 127 [8796093022208, 20453115568324608, 19029],
  hmkM 1 43402 1 11 127 [0, 4679521521369090, 16980],
  hmkM 1 43916 1 11 127 [0, 22704915113574400, 19029],
  hmkM 1 32348 1 11 127 [0, 22693919997296642, 16916],
  hmkM 1 28313 1 10 127 [0, 22564177625219072, 19029],
  hmkM 1 27248 1 10 127 [0, 4653133208748032, 19029],
  hmkM 1 32911 1 11 86 [562949953421824, 536870912], ⟨1, 2904, 1, 8, []⟩ ]
private def hmk1024SegsR128 : List DickeSol.Rkm128kSeg :=
  hmk1024R128C0 ++ (hmk1024R128C1 ++ (hmk1024R128C2 ++ hmk1024R128C3))
private def hmk1024RowR128P0 : List ℕ := [
  108, 130, 1299, 58, 10, 3, 222, 1, 67, 12, 91, 5, 7, 209, 16, 27, 125, 55, 129, 259, 422, 30,
  12, 184, 270, 81, 359, 450, 225, 17, 83, 48, 0, 405, 76, 20, 184, 314, 241, 1, 9, 20, 1, 8, 2,
  203, 77, 120 ]
private def hmk1024RowR128P1 : List ℕ := [
  1, 0, 335, 25, 53, 55, 213, 427, 12, 0, 58, 129, 46, 1151, 38, 872, 21, 4, 180, 20, 45, 45,
  25, 227, 48, 0, 750, 205, 35, 30, 202, 260, 817, 135, 97, 248, 74, 44, 51, 2, 74, 83, 360,
  253, 922, 87, 23, 165 ]
private def hmk1024RowR128P2 : List ℕ := [
  1815, 16, 17, 212, 408, 5, 1, 1002, 255, 66, 1615, 614, 252, 28, 514, 682, 591, 197, 37, 2538,
  408, 6, 62, 796, 13092, 232788, 99840, 3514, 5083, 531873, 1354527293, 998644502270 ]
private def hmk1024RowR128 : List ℕ :=
  hmk1024RowR128P0 ++ (hmk1024RowR128P1 ++ hmk1024RowR128P2)
private def hmk1024R128V1P0 : List ℤ := [
  Int.negSucc 2592533562, Int.ofNat 5508337531, Int.negSucc 20169223842,
  Int.negSucc 11569633761, Int.negSucc 14799630201, Int.ofNat 16255965891,
  Int.negSucc 11324938941, Int.negSucc 21399529914, Int.ofNat 7573485625, Int.ofNat 28974664585,
  Int.negSucc 12080694204, Int.negSucc 10310116435, Int.ofNat 4564069837, Int.ofNat 4543094507,
  Int.ofNat 13437175917, Int.negSucc 7369901076, Int.ofNat 5315626375, Int.negSucc 503723374,
  Int.negSucc 11950769394, Int.ofNat 16170332979, Int.negSucc 3089524263,
  Int.negSucc 15189378810, Int.negSucc 7896751907, Int.negSucc 966179313, Int.ofNat 640647710,
  Int.ofNat 2756334845, Int.ofNat 19791563812, Int.negSucc 15901963047, Int.ofNat 10288739964,
  Int.negSucc 8574142502, Int.negSucc 14071094244, Int.negSucc 15176903669,
  Int.negSucc 12501994040, Int.negSucc 37353414848, Int.negSucc 6119688799,
  Int.ofNat 10221178103, Int.ofNat 10953351291, Int.ofNat 1783084964, Int.ofNat 469454748,
  Int.ofNat 7539813641, Int.ofNat 10673464316, Int.negSucc 1615345871, Int.negSucc 196950255,
  Int.negSucc 2679804962, Int.ofNat 19121326820, Int.ofNat 13320230573, Int.negSucc 10124961329,
  Int.negSucc 9617798910 ]
private def hmk1024R128V1P1 : List ℤ := [
  Int.ofNat 7044825705, Int.negSucc 4510701748, Int.negSucc 8469153532, Int.negSucc 7060669646,
  Int.negSucc 733542780, Int.ofNat 10963394451, Int.ofNat 5872804441, Int.ofNat 4771455265,
  Int.ofNat 4246018383, Int.negSucc 8366033305, Int.ofNat 572006983, Int.ofNat 10392817564,
  Int.negSucc 10387717877, Int.negSucc 13501028950, Int.negSucc 5603438052,
  Int.negSucc 20330527043, Int.ofNat 30248471327, Int.negSucc 2858443473, Int.ofNat 16712641172,
  Int.negSucc 25774373822, Int.ofNat 921922478, Int.negSucc 17091682804, Int.negSucc 2143802297,
  Int.ofNat 27145605372, Int.ofNat 11378173865, Int.negSucc 14680232339, Int.negSucc 8282279491,
  Int.negSucc 9810970191, Int.negSucc 6393264796, Int.ofNat 4334003149, Int.negSucc 5271603747,
  Int.negSucc 23850015267, Int.negSucc 15297108361, Int.ofNat 16592464482,
  Int.ofNat 14946597434, Int.negSucc 12828110358, Int.negSucc 17352745379,
  Int.negSucc 2529731989, Int.ofNat 19473312756, Int.ofNat 23236040393, Int.negSucc 6635453987,
  Int.negSucc 8598830390, Int.ofNat 50450476746, Int.ofNat 111714987707, Int.ofNat 160804645759,
  Int.ofNat 277084580549, Int.ofNat 557522381860, Int.ofNat 1045956775636 ]
private def hmk1024R128V1P2 : List ℤ := [
  Int.ofNat 1829864679533, Int.ofNat 3119502982457, Int.ofNat 5237730682025,
  Int.ofNat 8554557701636, Int.ofNat 13591018284263, Int.ofNat 21011678184277,
  Int.ofNat 31538699822012, Int.ofNat 45958354390482, Int.ofNat 65062134590125,
  Int.ofNat 89411989335761, Int.ofNat 119078699443235, Int.ofNat 153538636217129,
  Int.ofNat 191574751234440, Int.ofNat 231108030782174, Int.ofNat 269217019212906,
  Int.ofNat 302379915058951, Int.ofNat 326980485387104, Int.ofNat 339856271599919,
  Int.ofNat 338970970785653, Int.ofNat 323699428841038, Int.ofNat 295254467543224,
  Int.ofNat 256412109866368, Int.ofNat 211302328992257, Int.ofNat 164577801760539,
  Int.ofNat 120568697326606, Int.ofNat 82624853448394, Int.ofNat 52545627335057,
  Int.ofNat 30637283556420, Int.ofNat 16134609196027, Int.ofNat 7465803852556,
  Int.ofNat 2958931184036, Int.ofNat 880641557575, Int.ofNat 159084472724 ]
private def hmk1024R128V1 : List ℤ :=
  hmk1024R128V1P0 ++ (hmk1024R128V1P1 ++ hmk1024R128V1P2)
private def hmk1024R128V2P0 : List ℤ := [
  Int.ofNat 333023722, Int.negSucc 13574028333, Int.negSucc 20300777716, Int.ofNat 20556515892,
  Int.ofNat 12909651952, Int.negSucc 10314343338, Int.ofNat 15164800085,
  Int.negSucc 10754076735, Int.ofNat 9551878277, Int.negSucc 6971538141, Int.negSucc 2459599774,
  Int.negSucc 171003156, Int.negSucc 21498629356, Int.ofNat 1342024341, Int.ofNat 2814740477,
  Int.ofNat 1210926768, Int.ofNat 4785995419, Int.ofNat 10828933103, Int.ofNat 22349679997,
  Int.ofNat 11401269010, Int.ofNat 18631671848, Int.negSucc 2613657859, Int.ofNat 18772637442,
  Int.ofNat 12241419749, Int.negSucc 26122763370, Int.ofNat 5325281653, Int.negSucc 5940213153,
  Int.ofNat 1621399941, Int.ofNat 12638232476, Int.negSucc 14144545373, Int.ofNat 5603133768,
  Int.ofNat 1919774601, Int.negSucc 7119281579, Int.ofNat 7200440773, Int.ofNat 3375637109,
  Int.ofNat 1289125610, Int.ofNat 1178484692, Int.ofNat 2248751105, Int.negSucc 3247529622,
  Int.ofNat 208632352, Int.ofNat 7096988964, Int.ofNat 12497941821, Int.negSucc 4784924253,
  Int.ofNat 26318413114, Int.negSucc 11914316585, Int.ofNat 11082996834, Int.ofNat 18418038498,
  Int.negSucc 8602754290 ]
private def hmk1024R128V2P1 : List ℤ := [
  Int.ofNat 10878092096, Int.ofNat 3593730068, Int.negSucc 3445551089, Int.negSucc 30947230280,
  Int.negSucc 8828773069, Int.ofNat 6230969578, Int.ofNat 2189147997, Int.ofNat 4304163110,
  Int.negSucc 10805586851, Int.negSucc 311738227, Int.ofNat 6213737486, Int.negSucc 33254378751,
  Int.negSucc 6662193065, Int.negSucc 8719364891, Int.negSucc 28569140887, Int.ofNat 706512286,
  Int.negSucc 6219306660, Int.ofNat 957186518, Int.negSucc 4809653113, Int.negSucc 14034361135,
  Int.negSucc 12251738881, Int.negSucc 9370515508, Int.negSucc 4983048134,
  Int.negSucc 11995004352, Int.negSucc 19133792586, Int.ofNat 793693682, Int.negSucc 2520198408,
  Int.ofNat 3397899694, Int.ofNat 12685927930, Int.negSucc 39376428687, Int.negSucc 3271069372,
  Int.negSucc 10156823878, Int.negSucc 6367658881, Int.negSucc 158083390, Int.ofNat 1467862194,
  Int.ofNat 13053506239, Int.ofNat 11365023189, Int.negSucc 14674437283, Int.ofNat 754060474,
  Int.ofNat 10896704011, Int.ofNat 15370859435, Int.ofNat 12394321046, Int.ofNat 31793334550,
  Int.negSucc 2713240226, Int.ofNat 2423652063, Int.ofNat 17497580525, Int.negSucc 2031682541,
  Int.negSucc 9346863753 ]
private def hmk1024R128V2P2 : List ℤ := [
  Int.negSucc 23265090644, Int.ofNat 33242183273, Int.ofNat 15591404740, Int.ofNat 17167426144,
  Int.ofNat 6040812387, Int.ofNat 6029988115, Int.negSucc 30831273741, Int.negSucc 17018259624,
  Int.negSucc 17886365215, Int.negSucc 10074332887, Int.negSucc 21330305622,
  Int.negSucc 28235949974, Int.ofNat 17020619210, Int.ofNat 26069273766, Int.ofNat 16492047231,
  Int.negSucc 3164333854, Int.negSucc 40904285591, Int.ofNat 19984241677,
  Int.negSucc 1069111250, Int.ofNat 5421100465, Int.ofNat 47579694094, Int.negSucc 26728688537,
  Int.ofNat 518901575, Int.negSucc 2912985006, Int.ofNat 46170052919, Int.ofNat 339683329361,
  Int.ofNat 4241658418370, Int.ofNat 21562217351250, Int.ofNat 74919005722445,
  Int.ofNat 199628555937720, Int.ofNat 409226031810120, Int.ofNat 626083901304460,
  Int.ofNat 628176344808436 ]
private def hmk1024R128V2 : List ℤ :=
  hmk1024R128V2P0 ++ (hmk1024R128V2P1 ++ hmk1024R128V2P2)
private def hmk1024R128V3P0 : List ℤ := [
  Int.negSucc 179721777, Int.ofNat 11713284801, Int.negSucc 4402991508, Int.negSucc 37671646553,
  Int.ofNat 5906398125, Int.negSucc 1738548105, Int.ofNat 6174036470, Int.ofNat 12123357143,
  Int.negSucc 4922729305, Int.ofNat 5286521982, Int.negSucc 11468677881, Int.negSucc 1555739512,
  Int.ofNat 6660130909, Int.ofNat 1996146499, Int.ofNat 6486355401, Int.negSucc 16696301837,
  Int.negSucc 4271408793, Int.negSucc 5045750672, Int.ofNat 11032892040, Int.ofNat 11359698056,
  Int.negSucc 10198417775, Int.negSucc 9009141686, Int.ofNat 25111987592, Int.ofNat 5395714034,
  Int.ofNat 21264823844, Int.ofNat 11673257609, Int.ofNat 16750131831, Int.ofNat 22557538500,
  Int.ofNat 8168221778, Int.ofNat 2190333788, Int.negSucc 73293344, Int.negSucc 3002468703,
  Int.negSucc 13042279360, Int.negSucc 2661580276, Int.negSucc 6171252432, Int.ofNat 9280274227,
  Int.negSucc 16925326603, Int.ofNat 10170092307, Int.ofNat 463176889, Int.negSucc 14853158142,
  Int.ofNat 20475455307, Int.negSucc 6033060557, Int.ofNat 3082036469, Int.ofNat 1110035497,
  Int.negSucc 701507748, Int.negSucc 5514897163, Int.ofNat 7643925885, Int.ofNat 17078597120 ]
private def hmk1024R128V3P1 : List ℤ := [
  Int.negSucc 5218152136, Int.ofNat 7097174031, Int.ofNat 14649285252, Int.ofNat 7848706740,
  Int.negSucc 5319745815, Int.ofNat 9905607627, Int.ofNat 10455807650, Int.ofNat 22204255756,
  Int.negSucc 6413263199, Int.negSucc 6275759101, Int.ofNat 235042382, Int.negSucc 15286189593,
  Int.negSucc 24398260328, Int.negSucc 17629811362, Int.negSucc 20415019696,
  Int.ofNat 2603173697, Int.negSucc 11944056557, Int.ofNat 15015914025, Int.negSucc 24421608593,
  Int.negSucc 1067946227, Int.ofNat 3181984709, Int.negSucc 3633973080, Int.negSucc 2832816948,
  Int.negSucc 14262244735, Int.ofNat 3301503323, Int.negSucc 6754630463,
  Int.negSucc 30849726836, Int.negSucc 11433073806, Int.ofNat 3102672435,
  Int.negSucc 14550921103, Int.negSucc 16713758735, Int.negSucc 17988535983,
  Int.negSucc 4226464655, Int.ofNat 14599801795, Int.negSucc 2105708030,
  Int.negSucc 25551174349, Int.negSucc 919641574, Int.ofNat 15560510565, Int.negSucc 3984875346,
  Int.negSucc 454770358, Int.negSucc 9341643935, Int.negSucc 2697464134, Int.ofNat 4871237509,
  Int.negSucc 11085522925, Int.negSucc 32019558490, Int.ofNat 13791729682,
  Int.ofNat 16164824716, Int.negSucc 1088084427 ]
private def hmk1024R128V3P2 : List ℤ := [
  Int.ofNat 19992123137, Int.negSucc 40532821415, Int.negSucc 8894108207,
  Int.negSucc 5062878629, Int.negSucc 13509076238, Int.negSucc 20662940589,
  Int.ofNat 1330862323, Int.negSucc 5940849448, Int.negSucc 33023157742, Int.ofNat 8527449486,
  Int.negSucc 8821374736, Int.ofNat 44907955259, Int.ofNat 19060967516, Int.ofNat 13028346496,
  Int.ofNat 1465070935, Int.negSucc 25928282504, Int.negSucc 26018502182,
  Int.negSucc 23637215299, Int.negSucc 11672847076, Int.negSucc 11901730428,
  Int.negSucc 51441393935, Int.negSucc 12760767381, Int.negSucc 4091086552,
  Int.negSucc 4350974920, Int.negSucc 11619979005, Int.ofNat 172164255823,
  Int.ofNat 486617451875, Int.ofNat 286889672261, Int.ofNat 68087027871, Int.ofNat 251051474429,
  Int.ofNat 8271645364625, Int.ofNat 218206538890629, Int.ofNat 975867328402002 ]
private def hmk1024R128V3 : List ℤ :=
  hmk1024R128V3P0 ++ (hmk1024R128V3P1 ++ hmk1024R128V3P2)
private def hmk1024AncLo : List DickeSol.RampKick128kAnchor := [
  ⟨3, hmk1024SegsR3, hmk1024RowR3⟩, ⟨4, hmk1024SegsR4, hmk1024RowR4⟩,
  ⟨5, hmk1024SegsR5, hmk1024RowR5⟩, ⟨6, hmk1024SegsR6, hmk1024RowR6⟩,
  ⟨7, hmk1024SegsR7, hmk1024RowR7⟩, ⟨8, hmk1024SegsR8, hmk1024RowR8⟩,
  ⟨9, hmk1024SegsR9, hmk1024RowR9⟩, ⟨10, hmk1024SegsR10, hmk1024RowR10⟩,
  ⟨12, hmk1024SegsR12, hmk1024RowR12⟩, ⟨14, hmk1024SegsR14, hmk1024RowR14⟩,
  ⟨16, hmk1024SegsR16, hmk1024RowR16⟩, ⟨32, hmk1024SegsR32, hmk1024RowR32⟩ ]
private def hmk1024Anc : List DickeSol.RampKick128kAnchor :=
  hmk1024AncLo ++
    [⟨64, hmk1024SegsR64, hmk1024RowR64⟩, ⟨128, hmk1024SegsR128, hmk1024RowR128⟩]
private theorem hmk1024B0 : hmkAtF [
    DickeSol.rkm128kCheckTable 1024 128 2 true hmk1024VPot hmk1024Anc,
    hmkChkCell 1024 16 2 74721135940909 500000000000000 hmk1024VPot hmk1024Anc,
    hmkChkCell 1024 32 2 12621924588223 125000000000000 hmk1024VPot hmk1024Anc,
    hmkChkCell 1024 64 2 34727173440933 500000000000000 hmk1024VPot hmk1024Anc,
    hmkChkCell 1024 128 2 2434837676117 50000000000000 hmk1024VPot hmk1024Anc,
    hmkSegBds 128 hmk1024SegsR128, hmkChkAnchors 1024 hmk1024AncLo
  ] = true := by decide +kernel
private theorem hmk1024B1 :
    hmkChkRow 1024 64 hmk1024SegsR64 hmk1024RowR64 = true := by decide +kernel
private theorem hmk1024B2 :
    hmkChkSeg 1024 128 hmk1024R128C0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (1, 128, 25174748, hmk1024R128V1) = true := by
  decide +kernel
private theorem hmk1024B3 :
    hmkChkSeg 1024 128 hmk1024R128C1 1 128 25174748 hmk1024R128V1
      (1, 128, 26939213, hmk1024R128V2) = true := by
  decide +kernel
private theorem hmk1024B4 :
    hmkChkSeg 1024 128 hmk1024R128C2 1 128 26939213 hmk1024R128V2
      (1, 128, 27056640, hmk1024R128V3) = true := by
  decide +kernel
private theorem hmk1024B5 :
    hmkChkFin 1024 128 hmk1024R128C3 1 128 27056640 hmk1024R128V3
      hmk1024RowR128 = true := by decide +kernel
private theorem hmk1024Row128Sound :
    DickeSol.rkm128kEvalRowLo12 1024 2 128 hmk1024SegsR128 = hmk1024RowR128 := by
  apply hmkCertSplit (hmk_hd (hmk_tl5 hmk1024B0)); unfold hmk1024SegsR128
  exact hmkTailStep hmk1024B2
    (hmkTailStep hmk1024B3 (hmkTailStep hmk1024B4 (hmkTailEnd hmk1024B5)))
private theorem hmk1024Valid :
    DickeSol.RampKick128kTableValid 1024 128 2 true hmk1024VPot hmk1024Anc :=
  DickeSol.rkm128kCheckTable_sound
    (hmkChkAnchors_append (hmk_hd (hmk_tl6 hmk1024B0))
      ⟨hmkListEq_eq (@hmkNatEq_eq) hmk1024B1, ⟨hmk1024Row128Sound, trivial⟩⟩)
    (hmk_hd hmk1024B0)

private def hmkVPotOf (m : ℕ) : List ℕ := cond (Nat.ble m 512) hmk512VPot hmk1024VPot
private def hmkAnchorsOf (m : ℕ) : List DickeSol.RampKick128kAnchor :=
  cond (Nat.ble m 512) hmk512Anc hmk1024Anc

private structure HmkCellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ hiTailM512M1024K128KrotovCertCellLMax m k
  hl1 : 1 ≤ hiTailM512M1024K128KrotovCertCellLMax m k
  hlm : hiTailM512M1024K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 2 true (hmkVPotOf m) (hmkAnchorsOf m)
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (hiTailM512M1024K128KrotovCertCellLMax m k)
    (hmkAnchorsOf m) = true
  hcost : ∃ num den : ℕ, relCostHiTailM512M1024K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k ((hmkVPotOf m).getD k 0) num den = true

private lemma hmk_mk {m k : ℕ} (jm dm jk dk d128 dm2 dl2 dl1 dlm : ℕ)
    (hjm : (jm + 1) + dm = 11) (hm : 2 ^ jm = m)
    (hjk : (jk + 1) + dk = 11) (hk : 2 ^ jk = k)
    (h128 : k + d128 = 128) (hm2 : 2 + dm2 = m)
    (hl2 : 2 + dl2 = hiTailM512M1024K128KrotovCertCellLMax m k)
    (hl1 : 1 + dl1 = hiTailM512M1024K128KrotovCertCellLMax m k)
    (hlm : hiTailM512M1024K128KrotovCertCellLMax m k * m + dlm = 65536)
    (htab : DickeSol.RampKick128kTableValid m 128 2 true (hmkVPotOf m) (hmkAnchorsOf m))
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k
      (hiTailM512M1024K128KrotovCertCellLMax m k) (hmkAnchorsOf m) = true)
    (hcost : ∃ num den : ℕ,
      relCostHiTailM512M1024K128KrotovCert m k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 m k ((hmkVPotOf m).getD k 0) num den = true) :
    HmkCellProps m k :=
  ⟨hm ▸ hmk_mem_grid jm dm hjm, hk ▸ hmk_mem_grid jk dk hjk, hmk_le_of_add h128,
    hmk_le_of_add hm2, hmk_le_of_add hl2, hmk_le_of_add hl1, hmk_le_of_add hlm,
    htab, hlmax, hcost⟩

private theorem hmk_props_512 {k : ℕ}
    (hk : k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128) : HmkCellProps 512 k := by
  rcases hk with rfl | rfl | rfl | rfl
  · have hc := hmk_hd (hmk_tl1 hmk512B0)
    exact hmk_mk 9 1 4 6 112 510 0 1 64512 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk512Valid (hmk_and_l hc) ⟨3750175009181, 25000000000000, rfl, hmk_and_r hc⟩
  · have hc := hmk_hd (hmk_tl2 hmk512B0)
    exact hmk_mk 9 1 5 5 96 510 0 1 64512 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk512Valid (hmk_and_l hc) ⟨101792234239951, 1000000000000000, rfl, hmk_and_r hc⟩
  · have hc := hmk_hd (hmk_tl3 hmk512B0)
    exact hmk_mk 9 1 6 4 64 510 0 1 64512 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk512Valid (hmk_and_l hc) ⟨70660484805033, 1000000000000000, rfl, hmk_and_r hc⟩
  · have hc := hmk_hd (hmk_tl4 hmk512B0)
    exact hmk_mk 9 1 7 3 0 510 0 1 64512 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk512Valid (hmk_and_l hc) ⟨12650158017091, 250000000000000, rfl, hmk_and_r hc⟩

private theorem hmk_props_1024 {k : ℕ}
    (hk : k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128) : HmkCellProps 1024 k := by
  rcases hk with rfl | rfl | rfl | rfl
  · have hc := hmk_hd (hmk_tl1 hmk1024B0)
    exact hmk_mk 10 0 4 6 112 1022 0 1 63488 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk1024Valid (hmk_and_l hc) ⟨74721135940909, 500000000000000, rfl, hmk_and_r hc⟩
  · have hc := hmk_hd (hmk_tl2 hmk1024B0)
    exact hmk_mk 10 0 5 5 96 1022 0 1 63488 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk1024Valid (hmk_and_l hc) ⟨12621924588223, 125000000000000, rfl, hmk_and_r hc⟩
  · have hc := hmk_hd (hmk_tl3 hmk1024B0)
    exact hmk_mk 10 0 6 4 64 1022 0 1 63488 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk1024Valid (hmk_and_l hc) ⟨34727173440933, 500000000000000, rfl, hmk_and_r hc⟩
  · have hc := hmk_hd (hmk_tl4 hmk1024B0)
    exact hmk_mk 10 0 7 3 0 1022 0 1 63488 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hmk1024Valid (hmk_and_l hc) ⟨2434837676117, 50000000000000, rfl, hmk_and_r hc⟩

private theorem hmk_all_props {m k : ℕ} (h : isHiTailM512M1024K128KrotovCertCell m k = true) :
    HmkCellProps m k := by
  rcases hmk_cases h with ⟨rfl | rfl, hk⟩
  · exact hmk_props_512 hk
  · exact hmk_props_1024 hk

private noncomputable def hiTailM512M1024K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM512M1024K128KrotovCertQubits n m k)) Var
      (hiTailM512M1024K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isHiTailM512M1024K128KrotovCertCell m k = true then
    let p := hmk_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG (hmkVPotOf m) (hmkAnchorsOf m) p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across all 8 supported m in {512, 1024} cells. -/
noncomputable def findAllJohnsonRampKick128kHiTailM512M1024K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM512M1024K128KrotovCertQubits n m k)) Var
      (hiTailM512M1024K128KrotovCertQubits n m k) ((n + 1) * m) :=
  hiTailM512M1024K128KrotovCertCircuitImpl res n m k

private lemma hmk_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isHiTailM512M1024K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kHiTailM512M1024K128KrotovCertCircuit res n m k =
      let p := hmk_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG (hmkVPotOf m) (hmkAnchorsOf m) p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kHiTailM512M1024K128KrotovCertCircuit
    hiTailM512M1024K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-1 recovery of S across all 8 supported m in {512, 1024} cells. -/
theorem hiTailM512M1024K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isHiTailM512M1024K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kHiTailM512M1024K128KrotovCertCircuit res n m k).compile
        QProg.qAssign (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [hmk_targetSets_eq]
  have hp := hmk_all_props hcell
  rw [hmk_circuit_eq res n hcell, ← hmk_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG (hmkVPotOf m) (hmkAnchorsOf m)
    hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across all 8 supported cells. -/
theorem hiTailM512M1024K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isHiTailM512M1024K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kHiTailM512M1024K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostHiTailM512M1024K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := hmk_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG (hmkVPotOf m)
    (hmkAnchorsOf m) hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab
    hp.hlmax hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [hmk_circuit_eq res n hcell, ← hmk_oracle_eq]
    exact hq S (by rwa [hmk_targetSets_eq])
  · rw [← hmk_targetSets_eq, ← hmk_vanilla_eq]; exact hsum

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_0 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrCert.isMidM16K512KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_1 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrCert.isMidM32K512KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_2 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM512F256KrCert.isHiTailM512Full256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_3 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt2.hm256k512krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_4 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K256KrCert.isHiTailM256K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_5 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K256KrCert.isLowM4K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_6 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM8K256KrCert.isLowM8K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_7 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K128KrCert.isMidM32K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_8 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt0.lm4k512l248krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_9 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM128K256KrCert.isHiTailM128K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_10 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM2K256KrCert.isLowM2K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_11 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256CoPt0.hm256cs0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_12 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM8K128KrCert.isLowM8K128KrotovCertCell)
    trivial).right

end

end Rk128kHiM512M1024K128KrCert
end QuantumComputation.Specs.GroverFindAll
