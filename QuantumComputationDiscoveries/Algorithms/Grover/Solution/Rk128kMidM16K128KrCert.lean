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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kEngine

/-
# Krotov `m = 16` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kMidM16K128KrCert`)

QHL-verified module packaging all `6` `m = 16, 4 ≤ k ≤ 128` cells
(`(16, 4), (16, 8), (16, 16), (16, 32), (16, 64), (16, 128)`) over `17` anchors
(`559` segments, `435,532` F1272 / `445,554` Horner coord-ops at `lTableMax = 16`,
`useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM16K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported (m, k) cells (m = 16, k ∈ {4, 8, 16, 32, 64, 128}, 6 cells). -/
def isMidM16K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 16 then
    if k == 4 then true
    else if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor L_max(16, k) across k ∈ {4..128}. -/
def midM16K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 16 then
    if k == 4 then 2
    else if k == 8 then 2
    else if k == 16 then 2
    else if k == 32 then 4
    else if k == 64 then 8
    else if k == 128 then 16
    else 1
  else 1

/-- Total register qubit budget (midM16K128KrotovCertCellLMax m k * m) * (n + 1) + k * n. -/
abbrev midM16K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (midM16K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile c(16, k): ℚ≥0 across k ∈ {4..128}. -/
def relCostMidM16K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 16 then
    if k == 4 then NNRat.divNat 366972263893023 1000000000000000
    else if k == 8 then NNRat.divNat 131157306716427 500000000000000
    else if k == 16 then NNRat.divNat 55574575590339 250000000000000
    else if k == 32 then NNRat.divNat 39978056717363 200000000000000
    else if k == 64 then NNRat.divNat 93291456077201 500000000000000
    else if k == 128 then NNRat.divNat 89292582836643 500000000000000
    else 1
  else 1

/-- Cost profile metadata (n0 = 80000, constructive threshold). -/
def midM16K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isMidM16K128KrotovCertCell, relCostMidM16K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kMidM16K128KrCert` cell lies on groverGrid × groverGrid. -/
theorem isMidM16K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isMidM16K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isMidM16K128KrotovCertCell at h
  split_ifs at h with hm16 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm16 hk4; rfl
  · subst hm16 hk8; rfl
  · subst hm16 hk16; rfl
  · subst hm16 hk32; rfl
  · subst hm16 hk64; rfl
  · subst hm16 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def mm16NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem mm16NatEq_eq {x y : ℕ} (h : mm16NatEq x y = true) : x = y := by
  unfold mm16NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def mm16IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => mm16NatEq m n
  | Int.negSucc m, Int.negSucc n => mm16NatEq m n
  | _, _ => false
private theorem mm16IntEq_eq {a b : ℤ} (h : mm16IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact congrArg Int.ofNat (mm16NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => exact congrArg Int.negSucc (mm16NatEq_eq h)
private def mm16ListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (mm16ListEq eqF xr yr) false
  | _, _ => false
private theorem mm16ListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : mm16ListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [mm16ListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev Mm16St := ℕ × ℕ × ℕ × List ℤ
private def mm16StEq (a b : Mm16St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (mm16NatEq a1 b1)
      (cond (mm16NatEq a2 b2)
        (cond (mm16NatEq a3 b3) (mm16ListEq mm16IntEq av bv) false) false) false
private theorem mm16StEq_eq {a b : Mm16St} (h : mm16StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [mm16StEq] at h
  cases h1 : mm16NatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : mm16NatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : mm16NatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h
        have e1 := mm16NatEq_eq h1; have e2 := mm16NatEq_eq h2
        have e3 := mm16NatEq_eq h3; have ev := mm16ListEq_eq (@mm16IntEq_eq) h
        subst e1 e2 e3 ev; rfl
private def mm16AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (mm16AtF rest) false
private theorem mm16_hd {b : Bool} {bs : List Bool} (h : mm16AtF (b :: bs) = true) : b = true := by
  cases b with
  | false => cases h
  | true => rfl
private theorem mm16_tl1 {b : Bool} {s : List Bool} (h : mm16AtF (b :: s) = true) :
    mm16AtF s = true := by
  cases b with
  | false => cases h
  | true => exact h
private theorem mm16_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : mm16AtF (b1 :: b2 :: bs) = true) : mm16AtF bs = true := mm16_tl1 (mm16_tl1 h)
private theorem mm16_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : mm16AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : mm16AtF bs = true := mm16_tl2 (mm16_tl2 h)
private theorem mm16_tl8 {b1 b2 b3 b4 b5 b6 b7 b8 : Bool} {bs : List Bool}
    (h : mm16AtF (b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bs) = true) :
    mm16AtF bs = true := mm16_tl4 (mm16_tl4 h)
private theorem mm16_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem mm16_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev mm16M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def mm16ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  mm16ListEq mm16NatEq (DickeSol.rkm128kEvalRowLo12 16 16 r s) ro
private def mm16ChkAnchors (xs : List DickeSol.RampKick128kAnchor) : Bool :=
  match xs with
  | [] => true
  | a :: rest =>
    match a with
    | ⟨rAct, segs, row⟩ => cond (mm16ChkRow rAct segs row) (mm16ChkAnchors rest) false
private theorem mm16ChkAnchors_append {xs rest : List DickeSol.RampKick128kAnchor}
    (hxs : mm16ChkAnchors xs = true) (hrest : DickeSol.RampKick128kAnchorsSound 16 16 rest) :
    DickeSol.RampKick128kAnchorsSound 16 16 (xs ++ rest) := by
  induction xs with
  | nil => exact hrest
  | cons a tl ih =>
    rcases a with ⟨rAct, segs, row⟩; rw [List.cons_append]
    dsimp only [mm16ChkAnchors, DickeSol.RampKick128kAnchorsSound] at hxs ⊢
    cases ha : mm16ChkRow rAct segs row with
    | false => rw [ha] at hxs; cases hxs
    | true =>
      rw [ha] at hxs; dsimp only [cond] at hxs; exact ⟨mm16ListEq_eq (@mm16NatEq_eq) ha, ih hxs⟩
private def mm16ChkSeg (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (st1 : Mm16St) : Bool := mm16StEq (DickeSol.rkm128kRunSegs 16 16 r s l0 d0 p0 v0) st1
private def mm16ChkFin (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Bool :=
  mm16ListEq mm16NatEq (DickeSol.rkm128kFinalizeState
    (DickeSol.rkm128kRunSegs 16 16 r s l0 d0 p0 v0)) ro
private def mm16SegBds (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def mm16TailOk (r : ℕ) (rest : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Prop :=
  ∃ st, DickeSol.rkm128kRunSegs 16 16 r rest l0 d0 p0 v0 = st ∧
    DickeSol.rkm128kFinalizeState st = ro
private theorem mm16TailEnd {r : ℕ} {cLast : List DickeSol.Rkm128kSeg} {l0 d0 p0 : ℕ} {v0 : List ℤ}
    {ro : List ℕ} (h : mm16ChkFin r cLast l0 d0 p0 v0 ro = true) :
    mm16TailOk r cLast l0 d0 p0 v0 ro := ⟨_, rfl, mm16ListEq_eq (@mm16NatEq_eq) h⟩
private theorem mm16TailStep {r : ℕ} {cCur rest : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {ro : List ℕ}
    (h1 : mm16ChkSeg r cCur l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : mm16TailOk r rest l1 d1 p1 v1 ro) : mm16TailOk r (cCur ++ rest) l0 d0 p0 v0 ro := by
  rcases h2 with ⟨st, hr, hf⟩; refine ⟨st, ?_, hf⟩
  unfold mm16ChkSeg at h1; rw [DickeSol.rkm128kRunSegs_append, mm16StEq_eq h1]; exact hr
private theorem mm16CertSplit {r : ℕ} {segs : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (hb : mm16SegBds r segs = true) (ht : mm16TailOk r segs 1 0 1 [Int.ofNat DickeSol.wdScale] ro) :
    DickeSol.rkm128kEvalRowLo12 16 16 r segs = ro := by
  rcases ht with ⟨st, hr, hf⟩; exact DickeSol.rkm128kCertRow_of_runSegs hb hr hf
private def mm16ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) : Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 16 k (v.getD k 0) n d)

private def mm16k128VPotP0 : List ℕ := [
  0, 160674770424682, 181232537490197, 194480946241769, 200633594776930, 206386626286256,
  212219381310976, 218402071181975, 225152399457083, 232750180421334, 241429708899364,
  251504959696159, 297887770674495, 342450934016003, 277678721274806, 319164768608839,
  290871166875464, 329840522747984, 305388322482225, 342249642853688, 319761279697809,
  354823389114036, 389079365268852, 422582370877710, 344582387294106, 376717341379043,
  408228256368947, 439150130354504, 469514807819226, 499351363649758, 528686429044279,
  557544469714487, 390188102453987, 418157989860736, 445713485656667, 472872478827057,
  499651607231171, 526066376774510, 552131266372661, 577859820723822, 603264732577155,
  628357915914966, 653150571245885, 677653244024169, 701875877059404, 725827857655322,
  749518060111476, 772954884133399 ]
private def mm16k128VPotP1 : List ℕ := [
  796146289622567, 819099828254665, 841822672201242, 864321640304388, 886603221975142,
  908673599053003, 930538665835187, 952204047459514, 973675116803361, 994957010042510,
  1016054640997530, 1036972714381214, 1057715738048231, 1078288034337342, 1098693750587003,
  1118936868896818, 534953469044718, 554882721549526, 574660418603862, 594289966028723,
  613774643964983, 633117613271919, 652321921512901, 671390508560353, 690326211849167,
  709131771305147, 727809833972722, 746362958364057, 764793618549789, 783104208009906,
  801297043261739, 819374367280627, 837338352727565, 855191104996975, 872934665096699,
  890571012371378, 908102067079492, 925529692833559, 942855698912279, 960081842452728,
  977209830530136, 994241322132204, 1011177930034426, 1028021222582423, 1044772725386852,
  1061433922936082, 1078006260131460, 1094491143749658 ]
private def mm16k128VPotP2 : List ℕ := [
  1110889943836296, 1127203995034739, 1143434597853723, 1159583019877213, 1175650496919682,
  1191638234129783, 1207547407045217, 1223379162601394, 1239134620096346, 1254814872114190,
  1270420985409290, 1285954001753148, 1301414938745927, 1316804790594391, 1332124528857947,
  1347375103164376, 1362557441896737, 1377672452852862, 1392721023878753, 1407704023477146,
  1422622301392412, 1437476689172915, 1452268000711876, 1466997032767742, 1481664565465003,
  1496271362776338, 1510818172986947, 1525305729141857, 1539734749476961, 1554105937834512,
  1568419984063744, 1582677564407273, 743774151274951 ]
private def mm16k128VPot : List ℕ :=
  mm16k128VPotP0 ++ (mm16k128VPotP1 ++ mm16k128VPotP2)
private def mm16SegsR3 : List DickeSol.Rkm128kSeg := [
  mm16M 1 165049811 1 30 1 [1], mm16M 1 614097 1 8 1 [1], mm16M 1 636653 1 8 1 [1],
  mm16M 1 656945 1 8 1 [1], mm16M 1 675677 1 8 1 [1], mm16M 1 700231 1 8 1 [1],
  mm16M 1 724992 1 8 1 [1], mm16M 1 752486 1 8 1 [1], mm16M 1 788381 1 8 1 [1],
  mm16M 1 843247 1 8 1 [1], mm16M 1 907892 1 8 1 [1], mm16M 1 980868 1 8 1 [1],
  mm16M 1 1086527 1 8 1 [1], mm16M 1 1301414 1 8 1 [1], mm16M 1 1707721 1 8 1 [1],
  mm16M 1 1840760 1 8 1 [1], mm16M 1 1033691 1 8 2 [3], mm16M 1 571601 1 8 2 [2],
  mm16M 1 572408 1 8 2 [3], mm16M 1 152046 1 8 1 [1], mm16M 1 420898 1 8 2 [2],
  mm16M 1 572458 1 8 2 [2], mm16M 1 572724 1 8 2 [2], mm16M 1 572790 1 8 2 [3],
  mm16M 1 572467 1 8 2 [2], ⟨1, 304421, 1, 8, []⟩ ]
private def mm16RowR3 : List ℕ := [
  3832, 61414368390, 938585627750 ]
private def mm16SegsR4 : List DickeSol.Rkm128kSeg := [
  mm16M 1 157432882 2 24 1 [1], mm16M 1 4193345 1 10 1 [1], mm16M 1 6677337 1 10 2 [3],
  mm16M 1 1661540 1 8 2 [2], mm16M 1 1805758 1 8 2 [3], mm16M 1 2012902 1 8 2 [2],
  mm16M 1 2355637 1 8 2 [3], mm16M 1 3065457 1 8 2 [2], mm16M 1 4543681 1 10 3 [5],
  mm16M 1 781529 1 8 3 [6], mm16M 1 781596 1 8 3 [4], mm16M 1 389222 1 8 2 [2],
  mm16M 1 390997 1 8 3 [4], mm16M 1 780607 1 8 3 [4], mm16M 1 781171 1 8 3 [7],
  mm16M 1 781193 1 8 3 [5], mm16M 1 412626 1 8 2 [2], mm16M 1 368327 1 8 3 [6],
  mm16M 1 780382 1 8 3 [4], mm16M 1 779243 1 8 3 [6], mm16M 1 779512 1 8 3 [4],
  mm16M 1 780200 1 8 3 [7], ⟨1, 432521, 1, 8, []⟩ ]
private def mm16RowR4 : List ℕ := [
  175, 23040, 48955573669, 951044403081 ]
private def mm16SegsR5 : List DickeSol.Rkm128kSeg := [
  mm16M 1 151134511 2 24 1 [1], mm16M 1 8872601 1 10 2 [2], mm16M 1 4294236 1 8 1 [1],
  mm16M 1 22755 1 8 2 [2], mm16M 1 7007301 1 10 3 [4], mm16M 1 102987 1 8 2 [2],
  mm16M 1 1630499 1 8 3 [4], mm16M 1 1888155 1 8 3 [5], mm16M 1 165862 1 8 1 [1],
  mm16M 1 1942819 1 8 3 [5], mm16M 1 2460873 1 8 3 [5], mm16M 1 3209054 1 8 3 [5],
  mm16M 1 4778004 1 10 4 [10], mm16M 1 1044890 1 8 4 [8], mm16M 1 1046748 1 8 4 [15],
  mm16M 1 1047821 1 8 4 [11], mm16M 1 1045030 1 8 4 [9], mm16M 1 1042820 1 8 4 [13],
  mm16M 1 1043336 1 8 4 [8], mm16M 1 1045303 1 8 4 [9], mm16M 1 1045162 1 8 4 [9],
  mm16M 1 1046578 1 8 4 [15], mm16M 1 1046354 1 8 4 [9], mm16M 1 1044996 1 8 4 [9],
  ⟨1, 608954, 1, 8, []⟩ ]
private def mm16RowR5 : List ℕ := [
  40, 291, 102896, 42128322626, 957871574112 ]
private def mm16SegsR6 : List DickeSol.Rkm128kSeg := [
  mm16M 1 145144188 2 26 1 [1], mm16M 1 8460865 1 10 2 [2], mm16M 1 9211747 1 12 3 [6],
  mm16M 1 4506058 1 10 3 [4], mm16M 1 7453305 1 10 4 [13], mm16M 1 2209460 1 8 4 [11],
  mm16M 1 173292 1 8 3 [6], mm16M 1 90 1 8 3 [6], mm16M 1 2308457 1 8 4 [11],
  mm16M 1 2880597 1 8 4 [11], mm16M 1 1779942 1 8 3 [4], mm16M 1 1919799 1 8 4 [11],
  mm16M 1 5444195 1 10 5 [18], mm16M 1 1079255 1 8 5 [24], mm16M 1 1074051 1 8 5 [25],
  mm16M 1 1068555 1 8 5 [20], mm16M 1 1072810 1 8 5 [20], mm16M 1 1072533 1 8 5 [17],
  mm16M 1 1072716 1 8 5 [17], mm16M 1 1075286 1 8 5 [30], mm16M 1 1076332 1 8 5 [23],
  mm16M 1 1074501 1 8 5 [23], mm16M 1 1074406 1 8 5 [17], mm16M 1 1073972 1 8 5 [23],
  mm16M 1 1073907 1 8 5 [23], mm16M 1 1073902 1 8 5 [17], ⟨1, 636901, 1, 8, []⟩ ]
private def mm16RowR6 : List ℕ := [
  2, 59, 1251, 143792, 38140605216, 961859249639 ]
private def mm16SegsR7 : List DickeSol.Rkm128kSeg := [
  mm16M 1 139755938 2 26 1 [1], mm16M 1 7306671 1 10 2 [2], mm16M 1 9191244 1 12 3 [6],
  mm16M 1 9581994 1 12 4 [14], mm16M 1 4636885 1 10 4 [9], mm16M 1 8143928 1 12 5 [21],
  mm16M 1 2870153 1 8 2 [3], mm16M 1 82036 1 8 5 [16], mm16M 1 3445248 1 8 5 [22],
  mm16M 1 4438924 1 10 5 [30], mm16M 1 6406333 1 10 6 [34], mm16M 1 1073616 1 8 6 [33],
  mm16M 1 1082035 1 8 6 [63], mm16M 1 1083402 1 8 6 [33], mm16M 1 1074985 1 8 6 [43],
  mm16M 1 1075048 1 8 6 [43], mm16M 1 1075056 1 8 6 [39], mm16M 1 1075100 1 8 6 [32],
  mm16M 1 1075078 1 8 6 [46], mm16M 1 1074880 1 8 6 [34], mm16M 1 1074824 1 8 6 [43],
  mm16M 1 1074788 1 8 6 [39], mm16M 1 1074678 1 8 6 [33], mm16M 1 1074717 1 8 6 [33],
  mm16M 1 1072542 1 8 6 [48], mm16M 1 1072561 1 8 6 [63], ⟨1, 644830, 1, 8, []⟩ ]
private def mm16RowR7 : List ℕ := [
  10, 13, 25, 4843, 167351, 35877106746, 964122720962 ]
private def mm16SegsR8 : List DickeSol.Rkm128kSeg := [
  mm16M 1 134775635 2 28 1 [1], mm16M 1 7327951 1 12 2 [3], mm16M 1 7271043 1 12 3 [7],
  mm16M 1 10039817 1 14 4 [15], mm16M 1 11505352 1 14 5 [21], mm16M 1 11638200 1 14 6 [32],
  mm16M 1 3039940 1 10 6 [44], mm16M 1 3547590 1 10 3 [6], mm16M 1 37097 1 8 6 [60],
  mm16M 1 2832224 1 10 5 [27], mm16M 1 1908100 1 8 5 [18], mm16M 1 60 1 8 6 [45],
  mm16M 1 6895322 1 12 7 [120], mm16M 1 1293531 1 8 7 [78], mm16M 1 1273174 1 8 7 [102],
  mm16M 1 1270359 1 8 7 [68], mm16M 1 1279349 1 8 7 [78], mm16M 1 1279413 1 8 7 [90],
  mm16M 1 1286008 1 8 7 [116], mm16M 1 1281998 1 8 7 [101], mm16M 1 1279613 1 8 7 [120],
  mm16M 1 1287665 1 8 7 [68], mm16M 1 1282620 1 8 7 [90], mm16M 1 1282487 1 8 7 [92],
  mm16M 1 1282279 1 8 7 [66], mm16M 1 1282076 1 8 7 [66], mm16M 1 1281428 1 8 7 [66],
  ⟨1, 793178, 1, 8, []⟩ ]
private def mm16RowR8 : List ℕ := [
  0, 7, 10, 238, 4520, 357375, 34845699387, 965153938421 ]
private def mm16SegsR9 : List DickeSol.Rkm128kSeg := [
  mm16M 1 9682315 1 17 10 [512], mm16M 1 127182809 1 56 2 [2], mm16M 1 9347833 1 17 3 [6],
  mm16M 1 14805283 1 20 5 [20], mm16M 1 13738960 1 19 6 [62], mm16M 1 8291528 1 16 3 [4],
  mm16M 1 8206239 1 16 7 [68], mm16M 1 9372049 1 17 3 [7], mm16M 1 9371838 1 17 8 [132],
  mm16M 1 9142897 1 17 8 [142], ⟨1, 7943902, 1, 16, []⟩ ]
private def mm16RowR9 : List ℕ := [
  28149, 6520, 33846, 2949, 6163386, 9079188, 152977011, 35063283927, 964768424811 ]
private def mm16SegsR10 : List DickeSol.Rkm128kSeg := [
  ⟨1, 57789683, 1, 37, []⟩, ⟨1, 31843373, 1, 28, []⟩, ⟨1, 23520992, 1, 24, []⟩,
  mm16M 1 19749516 1 23 2 [3], mm16M 1 16465868 1 21 4 [14], mm16M 1 14358378 1 20 6 [39],
  mm16M 1 14412557 1 20 7 [102], mm16M 1 9787353 1 18 3 [7], mm16M 1 8859622 1 17 8 [129],
  mm16M 1 9192545 1 17 7 [123], mm16M 1 6484020 1 16 9 [381], mm16M 1 6074113 1 15 9 [260],
  mm16M 1 5895837 1 15 8 [247], mm16M 1 5151731 1 15 9 [494], mm16M 1 3913013 1 14 5 [30],
  ⟨1, 2058403, 1, 12, []⟩ ]
private def mm16RowR10 : List ℕ := [
  669812, 18767, 54404273, 5058361, 7387246, 22084745, 12507167, 2694747, 36413389036,
  963481785800 ]
private def mm16SegsR11 : List DickeSol.Rkm128kSeg := [
  mm16M 1 126026040 2 23 1 [1], mm16M 1 4200874 1 16 2 [2], mm16M 1 4200882 1 16 3 [4],
  mm16M 1 4879072 1 16 2 [2], mm16M 1 4879068 1 16 2 [2], mm16M 1 4879067 1 16 5 [20],
  mm16M 1 4872128 1 16 5 [25], mm16M 1 3797776 1 16 6 [33], mm16M 1 3748767 1 16 3 [4],
  mm16M 1 3748759 1 16 2 [3], mm16M 1 3748756 1 16 7 [102], mm16M 1 7222054 1 16 4 [11],
  mm16M 1 3608621 1 16 4 [8], mm16M 1 3608944 1 16 8 [251], mm16M 1 7613574 1 16 8 [136],
  mm16M 1 2541529 1 16 8 [226], mm16M 1 2387647 1 16 9 [281], mm16M 1 2358020 1 16 4 [9],
  mm16M 1 2358045 1 16 3 [5], mm16M 1 2358027 1 16 9 [270], mm16M 1 4541506 1 16 5 [24],
  mm16M 1 4541520 1 16 4 [10], mm16M 1 6212044 1 16 9 [488], mm16M 1 5675074 1 16 10 [1020],
  mm16M 1 3451804 1 16 6 [33], mm16M 1 3364911 1 16 10 [592], mm16M 1 3322490 1 16 10 [853],
  mm16M 1 3125298 1 16 10 [808], mm16M 1 3134713 1 16 10 [807], ⟨1, 4864050, 1, 16, []⟩ ]
private def mm16RowR11 : List ℕ := [
  1093, 18742, 674098, 6926, 226189, 369518, 4703575, 1353238, 129729863, 38642059366,
  961220478260 ]
private def mm16SegsR14 : List DickeSol.Rkm128kSeg := [
  mm16M 1 17982030 1 24 15 [16384], mm16M 1 8858144 1 19 15 [16384],
  mm16M 1 8858144 1 19 15 [16384], mm16M 1 17716300 1 24 15 [16384],
  mm16M 1 8858155 1 19 15 [16384], mm16M 1 8858183 1 19 15 [16384], mm16M 1 53150007 1 40 3 [6],
  mm16M 1 8858837 1 19 2 [2], mm16M 1 8861417 1 19 6 [53], mm16M 2 8338201 1 21 6 [57],
  mm16M 2 8659249 1 22 9 [393], mm16M 2 7784023 1 21 9 [423], mm16M 2 7559875 1 20 11 [2038],
  mm16M 2 5725157 1 19 9 [490], mm16M 2 5897348 1 19 12 [2434], mm16M 2 12655199 1 25 13 [4696],
  ⟨2, 7935342, 1, 21, []⟩ ]
private def mm16RowR14 : List ℕ := [
  61624, 37775, 1247501, 497610, 2432031, 4137101, 2730759, 66814474, 19962474, 177985396,
  705073458, 579083850, 39023333887, 959416574246 ]
private def mm16SegsR16 : List DickeSol.Rkm128kSeg := [
  mm16M 1 113805870 2 44 1 [1], mm16M 1 3079031 1 14 2 [2], mm16M 1 3025444 1 14 3 [4],
  mm16M 1 3023649 1 14 3 [4], mm16M 1 3023666 1 14 4 [10], mm16M 2 1905514 1 14 5 [21],
  mm16M 2 2101423 1 14 4 [8], mm16M 2 2101048 1 14 6 [61], mm16M 2 2110661 1 14 3 [6],
  mm16M 2 2073002 1 14 7 [65], mm16M 2 2090804 1 14 3 [5], mm16M 2 2083801 1 14 8 [185],
  mm16M 2 2095738 1 14 7 [69], mm16M 2 1854611 1 14 9 [508], mm16M 2 1820103 1 14 9 [262],
  mm16M 2 3699983 1 17 10 [969], mm16M 2 1728291 1 13 10 [933], mm16M 2 1679729 1 13 8 [128],
  mm16M 2 1689043 1 13 6 [58], mm16M 2 1691750 1 13 11 [1319], mm16M 2 2033253 1 14 11 [1159],
  mm16M 2 2035453 1 14 7 [126], mm16M 2 2144398 1 14 10 [760], mm16M 2 2148017 1 14 12 [3977],
  mm16M 2 2194308 1 14 11 [1393], mm16M 2 2190264 1 14 10 [799], mm16M 2 2151220 1 14 11 [1952],
  mm16M 2 2149782 1 14 13 [5844], mm16M 2 2280305 1 15 11 [1098],
  mm16M 2 2203292 1 14 12 [2132], mm16M 2 2316378 1 15 14 [13075],
  mm16M 2 2063427 1 14 14 [9280], mm16M 2 1963343 1 14 12 [2898],
  mm16M 2 2022681 1 14 14 [10050], mm16M 2 2197744 1 14 14 [8242], mm16M 2 1490987 1 13 7 [76],
  mm16M 2 1604126 1 13 14 [16128], mm16M 2 1748867 1 14 13 [7178],
  mm16M 2 1726097 1 13 15 [16705], mm16M 2 1549164 1 13 11 [1598],
  mm16M 2 2324497 1 15 15 [20520], mm16M 2 2337653 1 15 15 [22442],
  mm16M 2 1731290 1 13 15 [21376], mm16M 2 2138822 1 14 13 [5166] ]
private def mm16RowR16 : List ℕ := [
  0, 70, 2, 2, 29, 44166, 84088, 52370, 199756, 106, 12, 2935, 1191044, 68823823, 37087202733,
  962842398734 ]
private def mm16SegsR18 : List DickeSol.Rkm128kSeg := [
  mm16M 1 46581889 1 41 16 [32768], mm16M 1 59891033 1 48 1 [1],
  mm16M 2 7922992 1 23 19 [262147], mm16M 2 7922590 1 23 6 [49], mm16M 2 7924191 1 23 8 [250],
  mm16M 2 7956410 1 23 10 [941], mm16M 2 8005065 1 23 11 [2016], mm16M 2 8094439 1 23 13 [5285],
  mm16M 2 7755564 1 22 10 [857], mm16M 2 7756772 1 22 15 [27320],
  mm16M 2 12004177 1 27 16 [38763], mm16M 2 12310539 1 27 17 [74901], ⟨2, 8367797, 1, 23, []⟩ ]
private def mm16RowR18 : List ℕ := [
  4, 2341, 0, 27115, 4688042, 62339, 17570, 1356042, 239858194, 326018646, 5953482, 519970732,
  3096644, 207594004, 1442110664, 1047575989, 38082382401, 958119285667 ]
private def mm16SegsR20 : List DickeSol.Rkm128kSeg := [
  mm16M 1 33337205 1 36 17 [65536], ⟨1, 32017470, 1, 35, []⟩, ⟨1, 20361609, 1, 28, []⟩,
  ⟨1, 18030047, 1, 27, []⟩, mm16M 2 11657833 1 27 2 [3], mm16M 2 11987720 1 28 9 [474],
  mm16M 2 10790614 1 26 11 [1877], mm16M 2 7282365 1 22 13 [6153],
  mm16M 2 6627278 1 22 14 [8758], mm16M 2 7296283 1 23 15 [16806],
  mm16M 2 7025012 1 22 16 [45402], mm16M 2 8989271 1 24 17 [65729],
  mm16M 2 3957748 1 18 13 [7505], mm16M 2 4228174 1 18 18 [234693],
  mm16M 2 4028092 1 18 18 [191095], mm16M 3 3154657 1 18 17 [73026],
  mm16M 3 2817922 1 18 19 [309215], mm16M 3 1669863 1 15 19 [454619],
  mm16M 3 880485 1 13 19 [398243], mm16M 3 1159374 1 14 19 [372777],
  mm16M 3 1041750 1 13 16 [42972], mm16M 3 1031606 1 13 19 [311371],
  mm16M 3 1271392 1 14 19 [365960], ⟨3, 884067, 1, 13, []⟩ ]
private def mm16RowR20 : List ℕ := [
  1427, 3542, 19672, 2635, 292103, 3451303, 2575243, 9072187, 3638585, 1124348, 94474114,
  500018799, 70991289, 120193573, 864795, 290931107, 3019329, 607438, 39210646470, 959688071941
  ]
private def mm16SegsR24 : List DickeSol.Rkm128kSeg := [
  mm16M 1 29068272 1 36 17 [65536], ⟨1, 64176444, 1, 56, []⟩, mm16M 2 4076943 1 19 23 [4194304],
  mm16M 2 4076926 1 19 3 [4], mm16M 2 4076927 1 19 5 [26], mm16M 2 4076837 1 19 6 [59],
  mm16M 2 2261743 1 16 5 [28], mm16M 2 2261733 1 16 8 [206], mm16M 2 4373766 1 20 9 [474],
  mm16M 2 4378972 1 20 11 [1397], mm16M 2 4361297 1 20 12 [3600],
  mm16M 2 3194053 1 18 13 [4128], mm16M 2 2963186 1 17 13 [4436],
  mm16M 2 3034692 1 17 14 [10598], mm16M 2 3264233 1 18 15 [25885],
  mm16M 2 2597482 1 17 13 [5650], mm16M 2 2596730 1 17 16 [41676],
  mm16M 2 2664084 1 17 16 [49284], mm16M 2 2665190 1 17 17 [73962],
  mm16M 3 2383601 1 17 13 [4118], mm16M 3 2383721 1 18 18 [211120],
  mm16M 3 2452735 1 18 17 [65696], mm16M 3 2446136 1 18 19 [348582],
  mm16M 3 2605192 1 18 19 [280707], mm16M 3 2599177 1 18 20 [755071],
  mm16M 3 2471945 1 18 20 [558664], mm16M 3 2505682 1 18 21 [1170261],
  mm16M 3 1950291 1 16 21 [1800565], mm16M 3 1973344 1 16 11 [1669],
  mm16M 3 1973335 1 16 21 [1932228], mm16M 3 3038110 1 19 22 [2429392],
  mm16M 3 2203348 1 17 13 [6309], mm16M 3 2204853 1 17 22 [3965739],
  mm16M 3 3199775 1 19 23 [4764018], mm16M 3 1468448 1 15 23 [4325646],
  mm16M 3 1528274 1 15 24 [10762631], mm16M 3 1000 1 6 20 [955962],
  mm16M 3 1000 1 6 24 [14255923], mm16M 3 948864 1 13 21 [1591147],
  mm16M 3 1091965 1 14 23 [8126854], mm16M 3 1240046 1 14 23 [4316483], ⟨3, 1042378, 1, 14, []⟩
  ]
private def mm16RowR24 : List ℕ := [
  411, 28, 140, 5087, 7157, 31077, 9037, 22288, 1647377, 48408, 2737060, 18740286, 2779492,
  267205479, 36424713, 53760512, 3100855, 758389, 2007369, 3543892, 11562, 74594558,
  38836611196, 960695953308 ]
private def mm16SegsR32P0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 74155703, 2, 45, []⟩, ⟨2, 9310412, 1, 29, []⟩, mm16M 2 8233442 1 27 4 [13],
  mm16M 2 2744991 1 18 5 [18], mm16M 2 1361357 1 15 6 [45], mm16M 2 1360350 1 15 7 [69],
  mm16M 2 1359623 1 15 8 [133], mm16M 2 1359184 1 15 8 [149], mm16M 2 1359732 1 15 8 [132],
  mm16M 2 1359475 1 15 27 [67109567], mm16M 2 1346264 1 15 27 [67109027],
  mm16M 2 1367724 1 15 11 [1957], mm16M 2 2662986 1 18 12 [2312],
  mm16M 2 2664127 1 18 13 [6499], mm16M 3 2369278 1 19 14 [13234],
  mm16M 3 2286145 1 19 15 [16602], mm16M 3 2399431 1 19 16 [39538],
  mm16M 3 2475459 1 19 17 [105548], mm16M 3 2469849 1 19 18 [220196],
  mm16M 3 2533273 1 19 19 [393256], mm16M 3 1468913 1 16 18 [149842],
  mm16M 3 1605332 1 17 20 [940285], mm16M 3 1627012 1 17 20 [579655],
  mm16M 3 1594819 1 17 33 [4296832240], mm16M 3 1691557 1 17 33 [4296038266],
  mm16M 3 1651587 1 17 22 [3172730], mm16M 3 1721684 1 17 22 [2190927],
  mm16M 3 1668419 1 17 23 [7630680], mm16M 3 1861381 1 17 22 [3373482],
  mm16M 3 1881563 1 17 24 [14682411], mm16M 4 1572481 1 18 22 [2228856],
  mm16M 4 1467263 1 17 25 [33322112], mm16M 4 1608272 1 18 24 [14743384],
  mm16M 4 1928938 1 19 26 [58359066], mm16M 4 1913601 1 19 25 [32048109],
  mm16M 4 1958588 1 19 27 [68099838], mm16M 4 2058512 1 19 26 [63094128],
  mm16M 4 2049547 1 19 28 [145624906], mm16M 4 1262445 1 16 23 [5633980],
  mm16M 4 1254988 1 16 21 [1182218], mm16M 4 1238326 1 16 29 [303349939],
  mm16M 4 1117219 1 16 29 [323258056], mm16M 4 1207369 1 16 29 [276852432],
  mm16M 4 1170302 1 16 29 [285631522], mm16M 4 1169413 1 16 29 [320469264],
  mm16M 4 1167913 1 16 30 [593917482], mm16M 4 1989652 1 19 30 [973404108],
  mm16M 4 1381171 1 17 30 [621150492] ]
private def mm16SegsR32P1 : List DickeSol.Rkm128kSeg := [
  mm16M 4 1440520 1 17 31 [2023566172], mm16M 4 905887 1 15 31 [1132492057],
  mm16M 4 431932 1 12 26 [36732994], mm16M 4 1019623 1 15 30 [620847839],
  mm16M 4 888020 1 15 29 [396081967], mm16M 4 590757 1 13 31 [1506729720],
  mm16M 4 1425019 1 17 30 [773872917], mm16M 4 699775 1 14 31 [1605905413],
  mm16M 4 832637 1 14 31 [1644242952] ]
private def mm16SegsR32 : List DickeSol.Rkm128kSeg :=
  mm16SegsR32P0 ++ mm16SegsR32P1
private def mm16RowR32 : List ℕ := [
  0, 0, 0, 2, 1, 0, 5, 31, 83, 1387, 1214, 842, 590, 6098, 51639, 534161, 612242, 655429,
  616523, 423411, 875420, 10278655, 8149231, 3232884, 63, 46568, 21606, 423494, 13702, 2068051,
  38142800521, 961829185861 ]
private def mm16R64C0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 45610725, 2, 43, []⟩, ⟨2, 18663357, 1, 54, []⟩, mm16M 3 7245002 1 38 8 [157],
  mm16M 3 1189657 1 18 8 [139], mm16M 3 1193959 1 18 7 [82], mm16M 3 1182916 1 18 12 [3734],
  mm16M 3 1143288 1 18 13 [7423], mm16M 3 1132300 1 18 14 [11413],
  mm16M 3 1240417 1 18 15 [30400], mm16M 4 957897 1 18 59 [59467, 4],
  mm16M 4 968204 1 18 64 [103538, 236] ]
private def mm16R64C1 : List DickeSol.Rkm128kSeg := [
  mm16M 4 971097 1 18 65 [219316, 492], mm16M 4 971123 1 18 65 [520175, 352],
  mm16M 4 978732 1 18 65 [998229, 256], mm16M 4 979257 1 18 21 [1193989],
  mm16M 4 980879 1 18 65 [3245700, 256], mm16M 4 983050 1 18 23 [7789482],
  mm16M 4 982919 1 18 65 [11306765, 256], mm16M 4 986146 1 18 25 [26995215],
  mm16M 4 977507 1 18 65 [42643563, 256], mm16M 5 863566 1 18 65 [78766042, 264],
  mm16M 5 861352 1 18 65 [172766148, 264], mm16M 5 808970 1 18 65 [234375454, 264],
  mm16M 5 888452 1 18 65 [472789908, 272], mm16M 5 907630 1 18 65 [918217325, 272],
  mm16M 5 897321 1 18 65 [2052160099, 272], mm16M 5 915834 1 19 65 [3130185139, 272],
  mm16M 5 834402 1 18 32 [4090717763], mm16M 5 825673 1 18 65 [6015219563, 256],
  mm16M 5 1386857 1 21 35 [29450787710], mm16M 5 1338540 1 21 65 [56476489142, 288],
  mm16M 6 1105171 1 21 65 [128380991122, 288], mm16M 6 1107139 1 21 65 [263664311713, 256],
  mm16M 6 1116203 1 21 65 [502609813521, 256], mm16M 6 1141695 1 21 65 [1050303457817, 256],
  mm16M 6 1143423 1 21 65 [1273909101607, 256], mm16M 6 1139557 1 21 65 [2609532623845, 320],
  mm16M 6 1165492 1 21 65 [4398643343020, 256], mm16M 6 1189995 1 21 65 [12605409042966, 320],
  mm16M 6 1231055 1 22 65 [23115543776549, 320], mm16M 7 1107008 1 21 65 [53130594906390, 320],
  mm16M 7 1120212 1 22 65 [139333054272809, 320],
  mm16M 7 1169832 1 22 65 [241790260507432, 320], mm16M 7 1216442 1 22 65 [354927119670546, 256]
  ]
private def mm16R64C2 : List DickeSol.Rkm128kSeg := [
  mm16M 7 1275467 1 23 50 [1063801786592358], mm16M 7 1335705 1 23 51 [1348714014657469],
  mm16M 7 1378808 1 23 52 [2403231326810051], mm16M 7 1411014 1 24 53 [4952581919984673],
  mm16M 7 1429048 1 24 54 [11623865982824210], mm16M 7 1535705 1 24 55 [33504404184574325],
  mm16M 7 1127672 1 22 55 [24559273836844931], mm16M 8 1014613 1 21 54 [14372268804182393],
  mm16M 8 1000056 1 21 57 [15800817029586440, 1], mm16M 8 1052037 1 22 57 [8449335644463142, 1],
  mm16M 8 1058329 1 22 58 [41661174837386611, 3], mm16M 8 1291267 1 24 59 [19243596865766, 5],
  mm16M 8 975748 1 21 59 [7322784993653203, 4], mm16M 8 1092408 1 22 60 [1208440743037423, 9],
  mm16M 8 857682 1 20 59 [1286412634278206, 4], mm16M 8 828951 1 20 51 [1319490173436021],
  mm16M 8 860610 1 20 61 [57410149688536341, 30], mm16M 8 747163 1 19 53 [5805441167037986],
  mm16M 8 734211 1 19 61 [3950121034218537, 25], mm16M 8 710638 1 19 54 [10583049190706775],
  mm16M 8 701683 1 19 62 [31892818725366455, 60], mm16M 8 1394239 1 24 58 [105672053224768, 2],
  mm16M 8 1334671 1 24 63 [22800682787673533, 121],
  mm16M 8 1060799 1 22 63 [121496748506173, 112],
  mm16M 8 756378 1 19 60 [13590115663909485, 11], mm16M 8 742233 1 19 63 [18741533471812, 72] ]
private def mm16SegsR64 : List DickeSol.Rkm128kSeg :=
  mm16R64C0 ++ (mm16R64C1 ++ mm16R64C2)
private def mm16RowR64P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 8, 6, 147, 291, 2624, 5437, 37, 0, 4, 1952, 24464, 359379,
  4452, 0, 2720904, 229978, 280344, 88878, 123020, 31134, 62279, 12240, 294099, 4920640, 792673,
  903375, 6798873, 49933, 7336785, 1770886, 108603231, 199886251, 2242754, 25336590, 10810370,
  1932474 ]
private def mm16RowR64P1 : List ℕ := [
  8146273, 3756898, 21352693, 45929521, 33338893, 2928225, 168669790, 759949008, 702759005,
  67822374, 45602021, 24782336, 38389421, 557648682, 39116967413, 958026329797 ]
private def mm16RowR64 : List ℕ :=
  mm16RowR64P0 ++ mm16RowR64P1
private def mm16R64V1P0 : List ℤ := [
  Int.negSucc 58361872, Int.negSucc 96636162, Int.ofNat 935954876, Int.negSucc 3491495875,
  Int.ofNat 805109605, Int.negSucc 4453323734, Int.negSucc 18016081127, Int.negSucc 2246681363,
  Int.negSucc 18113560686, Int.ofNat 34483221777, Int.ofNat 18112760430, Int.negSucc 5342639642,
  Int.ofNat 5880406679, Int.ofNat 189492328894, Int.negSucc 224833762566,
  Int.negSucc 294249227911, Int.ofNat 458169336554, Int.ofNat 386129224634,
  Int.ofNat 6942937913732, Int.ofNat 26389499105598, Int.ofNat 67422039262048,
  Int.ofNat 135211336486047, Int.ofNat 225377781329212, Int.ofNat 321504900608675,
  Int.ofNat 399515049973249, Int.ofNat 437618607175209, Int.ofNat 426133650129392,
  Int.ofNat 371205460130133, Int.ofNat 290665766617143, Int.ofNat 205360487945996,
  Int.ofNat 131300313566151, Int.ofNat 76145181514901, Int.ofNat 40124827569690,
  Int.ofNat 19237029402914, Int.ofNat 8398266967449, Int.ofNat 3340148298919,
  Int.ofNat 1210306583657, Int.ofNat 399431139716, Int.ofNat 119977978347,
  Int.ofNat 32764124110, Int.ofNat 8122259875, Int.ofNat 1824263464, Int.ofNat 370315692,
  Int.ofNat 67739342, Int.ofNat 11126178, Int.ofNat 1633967, Int.ofNat 213463, Int.ofNat 24645 ]
private def mm16R64V1P1 : List ℤ := [
  Int.ofNat 2489, Int.ofNat 211, Int.ofNat 12, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm16R64V1 : List ℤ :=
  mm16R64V1P0 ++ mm16R64V1P1
private def mm16R64V2P0 : List ℤ := [
  Int.ofNat 31322864, Int.ofNat 190421175, Int.ofNat 323363637, Int.ofNat 87806222,
  Int.ofNat 309430401, Int.negSucc 458079365, Int.negSucc 1220010343, Int.negSucc 4321873593,
  Int.negSucc 1360964960, Int.negSucc 3078159986, Int.negSucc 5196183802, Int.ofNat 12304979603,
  Int.negSucc 21362224203, Int.negSucc 17027391960, Int.ofNat 37245856202,
  Int.ofNat 122320769341, Int.ofNat 291262953907, Int.ofNat 288117704972,
  Int.negSucc 256565997985, Int.negSucc 383148156860, Int.negSucc 503092110676,
  Int.negSucc 496672149898, Int.negSucc 935245079645, Int.negSucc 1323634009452,
  Int.negSucc 234792428037, Int.negSucc 145290704061, Int.negSucc 2845077072986,
  Int.negSucc 3536492420955, Int.ofNat 2628689876726, Int.ofNat 1583013485450,
  Int.negSucc 10919502604395, Int.ofNat 10641347803137, Int.negSucc 6785280351932,
  Int.ofNat 611541691653, Int.ofNat 1223134892856, Int.ofNat 40743876862,
  Int.negSucc 6020672217263, Int.negSucc 3475847714659, Int.negSucc 756887960114,
  Int.negSucc 6398388142486, Int.ofNat 2343712665772, Int.ofNat 1282986857095,
  Int.negSucc 603188519239, Int.ofNat 749179954476, Int.negSucc 1073251633608,
  Int.negSucc 199167065342, Int.negSucc 1166088736571, Int.negSucc 1523342148349 ]
private def mm16R64V2P1 : List ℤ := [
  Int.ofNat 11453142863320, Int.ofNat 74460559493751, Int.ofNat 245844518856283,
  Int.ofNat 416079473331407, Int.ofNat 505884584599876, Int.ofNat 489777116106133,
  Int.ofNat 395115451169812, Int.ofNat 271797689779881, Int.ofNat 161355497762658,
  Int.ofNat 83112467152136, Int.ofNat 37159934114475, Int.ofNat 14367098472699,
  Int.ofNat 4743020401533, Int.ofNat 1378428589473, Int.ofNat 153978290315,
  Int.ofNat 9630669956, Int.negSucc 322427164 ]
private def mm16R64V2 : List ℤ :=
  mm16R64V2P0 ++ mm16R64V2P1
private def mm16R128C0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 28541111, 1, 62, []⟩, mm16M 2 11731014 1 53 33 [8589934591], mm16M 3 5083339 1 40 1 [1],
  mm16M 4 6497698 1 53 8 [131], mm16M 4 2312383 1 30 13 [6747] ]
private def mm16R128C1 : List DickeSol.Rkm128kSeg := [
  mm16M 5 1919560 1 30 18 [234754], mm16M 5 1910532 1 30 22 [3351330],
  mm16M 5 979417 1 23 78 [14070576, 2097152], mm16M 5 1040236 1 23 27 [73143410],
  mm16M 6 877661 1 23 97 [505858118, 1099511627776],
  mm16M 6 895498 1 23 79 [2067715905, 4194304],
  mm16M 6 893354 1 23 97 [7219531915, 1099511627776],
  mm16M 6 884422 1 23 97 [27220094483, 1099511627776],
  mm16M 6 921508 1 24 72 [109493282239, 32768], mm16M 6 922011 1 24 38 [148291900306],
  mm16M 7 808100 1 23 40 [550399681798], mm16M 7 812746 1 23 42 [2292649251076],
  mm16M 7 815324 1 24 76 [9601442250372, 524288],
  mm16M 7 818673 1 24 76 [66399722530023, 524288],
  mm16M 7 815055 1 24 106 [102323149065760, 562949953421312],
  mm16M 8 722206 1 23 126 [347971372353334, 562949953421312, 12548],
  mm16M 8 729943 1 23 129 [1886560396358466, 0, 78848],
  mm16M 8 722801 1 23 126 [3801324867712901, 0, 13568],
  mm16M 8 729376 1 23 129 [15424219212962056, 0, 78848] ]
private def mm16R128C2 : List DickeSol.Rkm128kSeg := [
  mm16M 8 735265 1 23 128 [70384664506979890, 0, 50432],
  mm16M 8 713665 1 23 127 [44373222398431456, 140737488355329, 29968],
  mm16M 9 658904 1 23 127 [63768280319345411, 6, 17680],
  mm16M 9 649945 1 23 127 [18326033498664080, 8796093022223, 29968],
  mm16M 9 657393 1 23 129 [22453873501098528, 52, 91136],
  mm16M 9 684675 1 24 128 [13958753222419477, 116, 53248],
  mm16M 9 695155 1 24 129 [7846663511252377, 1125899906843135, 74752],
  mm16M 10 636364 1 24 126 [16020418582530565, 70403103916865, 8192],
  mm16M 10 655743 1 24 129 [62493901873781953, 34359741763, 107588],
  mm16M 10 691142 1 24 129 [65409489399884294, 4785074604094236, 98368],
  mm16M 10 653479 1 24 129 [40136601677836022, 29567, 91136],
  mm16M 10 689299 1 24 129 [4454768532607474, 117342, 65536],
  mm16M 11 628837 1 24 128 [36809689104237281, 1125899906991824, 51200],
  mm16M 11 654483 1 25 129 [14206990894137453, 892181, 114960],
  mm16M 11 680735 1 25 129 [26207954576707621, 3170842, 114688] ]
private def mm16R128C3 : List DickeSol.Rkm128kSeg := [
  mm16M 11 902007 1 28 129 [49672273084278905, 4503599640143661, 118788],
  mm16M 12 874680 1 29 129 [423299843525281, 35187253, 82500],
  mm16M 12 928064 1 29 127 [55278508297325731, 136233600, 20480],
  mm16M 12 962220 1 30 120 [17256034555887799, 1723865659, 129],
  mm16M 12 894144 1 29 125 [50807266981376990, 6498296191, 5120],
  mm16M 12 918702 1 29 129 [51922825674848520, 29535167802, 111648],
  mm16M 13 849001 1 29 129 [50541270035747862, 103759893508, 66592],
  mm16M 13 869564 1 29 128 [44263675119349316, 417812003872, 42248],
  mm16M 13 896785 1 30 126 [38897965251270452, 1733199733287, 8512],
  mm16M 13 892689 1 30 129 [72021452116143104, 4487436996117, 122878],
  mm16M 14 912518 1 31 128 [34828153566467287, 26817921828369, 32776],
  mm16M 14 749251 1 28 129 [68945148389319068, 6907960281688, 131040],
  mm16M 14 773692 1 28 128 [415385985517731, 39719939411719, 32768] ]
private def mm16R128C4 : List DickeSol.Rkm128kSeg := [
  mm16M 14 775482 1 28 128 [1697236901318445, 88515488593512, 32768],
  mm16M 14 773626 1 28 104 [68510572294303737, 140836339898747],
  mm16M 14 776900 1 28 129 [63727837169673887, 8017763343227987, 65536],
  mm16M 14 805027 1 29 129 [61897159417943428, 1267737460363993, 65536],
  mm16M 15 721956 1 28 129 [24259658591218514, 565888249862214, 65536],
  mm16M 15 724429 1 28 129 [27349052753347548, 40540171723554626, 65537],
  mm16M 15 647238 1 27 129 [35881505106678295, 2315454969274225, 65538],
  mm16M 15 628887 1 26 129 [54246554498804203, 361812371376681, 65536],
  mm16M 15 630464 1 26 129 [70399327022686468, 9335612845456081, 65548],
  mm16M 15 757925 1 29 129 [71573376163673617, 295253334194766, 65552],
  mm16M 15 736066 1 28 118 [28089864177277958, 2540112571055206, 34],
  mm16M 15 792284 1 29 119 [17884342848639705, 19211354398177447, 65],
  mm16M 15 808677 1 29 120 [24198446624714945, 140737591338776, 128] ]
private def mm16R128C5 : List DickeSol.Rkm128kSeg := [
  mm16M 16 796512 1 30 121 [57036743302734959, 1131682015198499, 292],
  mm16M 16 808259 1 30 122 [26548295267647793, 43991465946478818, 576],
  mm16M 16 795011 1 30 123 [70321940588758308, 4654750218878534, 1024],
  mm16M 16 641463 1 27 123 [62919606891209956, 4558856574337992, 1538],
  mm16M 16 666261 1 28 115 [67526972455672831, 5211754792692404, 4],
  mm16M 16 695614 1 28 125 [49162861968681944, 71389517632655250, 7297],
  mm16M 16 431012 1 23 108 [26567379720730248, 3471658279100493],
  mm16M 16 453952 1 23 112 [62817443431803541, 61964146342141513],
  mm16M 16 449474 1 23 126 [59448821071567934, 71760351441676, 8193],
  mm16M 16 471554 1 24 126 [15226561309607801, 15797788623428303, 10468],
  mm16M 16 583935 1 26 126 [70887132042132617, 844427237676664, 8192],
  mm16M 16 594559 1 26 127 [4092629938571183, 19001546798554376, 18608],
  mm16M 16 625979 1 27 127 [34726221721485829, 7714696493128, 16512],
  mm16M 16 572795 1 26 118 [47954457677624428, 567931369835043, 33] ]
private def mm16SegsR128 : List DickeSol.Rkm128kSeg :=
  mm16R128C0 ++ (mm16R128C1 ++ (mm16R128C2 ++ (mm16R128C3 ++ (mm16R128C4 ++ mm16R128C5))))
private def mm16RowR128P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 30, 0, 0, 0, 0, 3, 9, 0, 0, 13,
  0, 10, 2, 3, 252, 0, 150, 22, 2, 746, 270, 1277, 5778, 10, 2, 12, 212 ]
private def mm16RowR128P1 : List ℕ := [
  31, 2, 976, 9, 296, 233, 942, 210, 20303, 7336, 93473, 1916, 26098, 493306, 442135, 4024495,
  2812, 16592, 5102, 30229, 93, 2729, 18600, 32154, 46030, 678, 38929, 336433, 79657, 551008,
  31411, 51942, 358638, 41755002, 15310, 12848, 236128, 4922099, 91, 21248968, 427877, 1120353,
  37489746, 3932926, 9927250, 52778199, 31214226, 58688787 ]
private def mm16RowR128P2 : List ℕ := [
  9860712, 784570, 10108985, 16916718, 2550109, 151956349, 398722713, 297928589, 18, 45175621,
  41196664, 237021365, 6527679, 496095869, 64470731, 28517922, 12034807, 672884118, 123563958,
  668118, 1848891438, 587313383, 90855115, 1866764945, 73031537, 833073651, 281650950,
  644600928, 409360882, 188553970, 39446816747, 950841602039 ]
private def mm16RowR128 : List ℕ :=
  mm16RowR128P0 ++ (mm16RowR128P1 ++ mm16RowR128P2)
private def mm16R128V1P0 : List ℤ := [
  Int.negSucc 1559661068, Int.negSucc 839477037, Int.negSucc 5800032396, Int.ofNat 2182368729,
  Int.negSucc 3577192735, Int.negSucc 1832737590, Int.ofNat 1415308494, Int.ofNat 1613488891,
  Int.ofNat 680985751, Int.ofNat 3356744144, Int.negSucc 1860884965, Int.negSucc 2481600186,
  Int.negSucc 1116959319, Int.negSucc 5376803150, Int.negSucc 21694585055,
  Int.negSucc 95454754160, Int.negSucc 370623759679, Int.negSucc 1198260895881,
  Int.negSucc 3345486411684, Int.negSucc 8263854609211, Int.negSucc 18276194984557,
  Int.negSucc 36464476117275, Int.negSucc 66035637189528, Int.negSucc 109093085646753,
  Int.negSucc 165088568425651, Int.negSucc 229625411464856, Int.negSucc 294419819468168,
  Int.negSucc 348867279316873, Int.negSucc 382895379068639, Int.negSucc 390038793265551,
  Int.negSucc 369435414439983, Int.negSucc 325905151165401, Int.negSucc 268173407424808,
  Int.negSucc 206109541379741, Int.negSucc 148137417851534, Int.negSucc 99674732800806,
  Int.negSucc 62845328663097, Int.negSucc 37161050662777, Int.negSucc 20622208091437,
  Int.negSucc 10746451114418, Int.negSucc 5261055009592, Int.negSucc 2420455170544,
  Int.negSucc 1046689531587, Int.negSucc 425456206991, Int.negSucc 162541282234,
  Int.negSucc 58348827035, Int.negSucc 19673192941, Int.negSucc 6226249912 ]
private def mm16R128V1P1 : List ℤ := [
  Int.negSucc 1848133160, Int.negSucc 513973938, Int.negSucc 133746267, Int.negSucc 32512696,
  Int.negSucc 7368755, Int.negSucc 1553278, Int.negSucc 303610, Int.negSucc 54819,
  Int.negSucc 9092, Int.negSucc 1369, Int.negSucc 177, Int.negSucc 17, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm16R128V1 : List ℤ :=
  mm16R128V1P0 ++ mm16R128V1P1
private def mm16R128V2P0 : List ℤ := [
  Int.negSucc 327417359, Int.ofNat 152525187, Int.ofNat 1920974596, Int.ofNat 825910121,
  Int.ofNat 317383639, Int.ofNat 3275910344, Int.ofNat 3144516334, Int.ofNat 2648987277,
  Int.negSucc 60670026, Int.ofNat 5278056321, Int.ofNat 420647324, Int.ofNat 679247805,
  Int.ofNat 599587065, Int.ofNat 3984120304, Int.ofNat 273531408, Int.ofNat 549895929,
  Int.ofNat 1691291416, Int.ofNat 2330420494, Int.ofNat 10593034830, Int.ofNat 11280391445,
  Int.ofNat 14116704637, Int.ofNat 55198341488, Int.negSucc 5313602188, Int.negSucc 1257785148,
  Int.negSucc 34998623662, Int.negSucc 26750236419, Int.ofNat 1479736351,
  Int.negSucc 87007290606, Int.ofNat 25077426366, Int.ofNat 337634514, Int.negSucc 22088280186,
  Int.negSucc 159191725063, Int.ofNat 175086816816, Int.ofNat 716541705688,
  Int.negSucc 1230664010778, Int.ofNat 478871277459, Int.negSucc 540236357679,
  Int.negSucc 981366585432, Int.ofNat 144855060334, Int.negSucc 1806008175427,
  Int.ofNat 301343975724, Int.ofNat 304057203183, Int.negSucc 3416022172701,
  Int.negSucc 2469405130068, Int.negSucc 3314701069182, Int.ofNat 635174521229,
  Int.ofNat 2433741645778, Int.ofNat 4319551115090 ]
private def mm16R128V2P1 : List ℤ := [
  Int.ofNat 3038522200218, Int.ofNat 2986276796412, Int.negSucc 2170675588353,
  Int.negSucc 3810350963628, Int.negSucc 1602364307471, Int.negSucc 4839623444890,
  Int.negSucc 11032997819560, Int.negSucc 52782613335165, Int.negSucc 118559867182778,
  Int.negSucc 199415219726822, Int.negSucc 281417929095063, Int.negSucc 349424035477230,
  Int.negSucc 391372692559619, Int.negSucc 401406806981261, Int.negSucc 380751066611716,
  Int.negSucc 336353178767696, Int.negSucc 278158887431421, Int.negSucc 216198720157797,
  Int.negSucc 158427246188922, Int.negSucc 109725718161529, Int.negSucc 71974504162445,
  Int.negSucc 44788005831033, Int.negSucc 26477987462311, Int.negSucc 14887587589047,
  Int.negSucc 7969475936174, Int.negSucc 4065293918284, Int.negSucc 1976917983107,
  Int.negSucc 916990988680, Int.negSucc 406270221492, Int.negSucc 172046450607,
  Int.negSucc 69449055423, Int.negSucc 26533539597, Int.negSucc 9507948311,
  Int.negSucc 3172314985, Int.negSucc 983024575, Int.negSucc 283980979, Int.negSucc 77291009,
  Int.negSucc 20148136, Int.negSucc 5127248, Int.negSucc 1293373, Int.negSucc 325045,
  Int.negSucc 80839, Int.negSucc 19611, Int.negSucc 4565, Int.negSucc 999, Int.negSucc 198,
  Int.negSucc 30, Int.negSucc 2 ]
private def mm16R128V2P2 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm16R128V2 : List ℤ :=
  mm16R128V2P0 ++ (mm16R128V2P1 ++ mm16R128V2P2)
private def mm16R128V3P0 : List ℤ := [
  Int.negSucc 214640808, Int.negSucc 172415718, Int.negSucc 33791795, Int.negSucc 215738438,
  Int.ofNat 53669604, Int.ofNat 243796553, Int.ofNat 235958787, Int.ofNat 1675831107,
  Int.ofNat 965969543, Int.ofNat 2825088598, Int.ofNat 2433741428, Int.ofNat 585067216,
  Int.ofNat 479052838, Int.negSucc 2937509183, Int.negSucc 7033153168, Int.negSucc 2633257874,
  Int.negSucc 461051362, Int.ofNat 139088074, Int.negSucc 566521805, Int.ofNat 2440378210,
  Int.negSucc 1061067728, Int.negSucc 4535075499, Int.negSucc 9906935079,
  Int.negSucc 7365690507, Int.negSucc 12434168716, Int.negSucc 12486639837,
  Int.negSucc 8802787830, Int.negSucc 5033125065, Int.ofNat 2616518978, Int.negSucc 22101614079,
  Int.negSucc 63898777786, Int.negSucc 103495730533, Int.negSucc 60642006359,
  Int.ofNat 229927124290, Int.negSucc 28136303177, Int.negSucc 466581864590,
  Int.ofNat 357689391410, Int.negSucc 381270026084, Int.ofNat 869006355411,
  Int.negSucc 327068963792, Int.ofNat 156365002823, Int.negSucc 475863577417,
  Int.negSucc 490550184170, Int.negSucc 429933476804, Int.negSucc 24715102208,
  Int.negSucc 1531897331553, Int.negSucc 3062326666786, Int.negSucc 4683584268331 ]
private def mm16R128V3P1 : List ℤ := [
  Int.negSucc 3583215985723, Int.negSucc 1696713549229, Int.ofNat 1619108503122,
  Int.ofNat 3068164544487, Int.ofNat 2113885856791, Int.negSucc 2418128118954,
  Int.ofNat 832182370923, Int.negSucc 1656620369716, Int.negSucc 4682946194554,
  Int.negSucc 3967738928596, Int.negSucc 2683025314696, Int.negSucc 9851620012077,
  Int.ofNat 873297228975, Int.ofNat 2382860730451, Int.ofNat 3826110819654,
  Int.ofNat 4832623264010, Int.ofNat 4380829562215, Int.ofNat 1981196865389,
  Int.ofNat 8768677236959, Int.ofNat 8860134790489, Int.negSucc 246508491110,
  Int.negSucc 11395120934493, Int.negSucc 1561440593972, Int.negSucc 1613543605880,
  Int.ofNat 3378286894554, Int.negSucc 7775541929659, Int.negSucc 734660664034,
  Int.negSucc 11459392413100, Int.negSucc 2097285234613, Int.negSucc 4374382033656,
  Int.negSucc 35540002046287, Int.negSucc 116436068590931, Int.negSucc 218534721791795,
  Int.negSucc 316243057440235, Int.negSucc 387565465824815, Int.negSucc 419564874149852,
  Int.negSucc 410983439786802, Int.negSucc 369280376762309, Int.negSucc 307476799635107,
  Int.negSucc 238796903378558, Int.negSucc 173764799033941, Int.negSucc 119006359489735,
  Int.negSucc 76930165632570, Int.negSucc 46986671285603, Int.negSucc 27175798578585,
  Int.negSucc 14946840028229, Int.negSucc 7831372736264, Int.negSucc 3888754318781 ]
private def mm16R128V3P2 : List ℤ := [
  Int.negSucc 1810156929091, Int.negSucc 781109285977, Int.negSucc 310589614070,
  Int.negSucc 114047663777, Int.negSucc 39127779572, Int.negSucc 12807044874,
  Int.negSucc 4103819578, Int.negSucc 1315114421, Int.negSucc 422279770, Int.negSucc 136616587,
  Int.negSucc 41785143, Int.negSucc 11111924, Int.negSucc 2538720, Int.negSucc 535732,
  Int.negSucc 115952, Int.negSucc 26483, Int.negSucc 5961, Int.negSucc 1225, Int.negSucc 215,
  Int.negSucc 28, Int.negSucc 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0 ]
private def mm16R128V3 : List ℤ :=
  mm16R128V3P0 ++ (mm16R128V3P1 ++ mm16R128V3P2)
private def mm16R128V4P0 : List ℤ := [
  Int.negSucc 9001674, Int.negSucc 118448914, Int.negSucc 124152566, Int.negSucc 143754341,
  Int.ofNat 356857764, Int.negSucc 332615753, Int.ofNat 134351576, Int.negSucc 166128915,
  Int.negSucc 158235121, Int.ofNat 746664233, Int.negSucc 579023039, Int.ofNat 895458411,
  Int.ofNat 992226339, Int.ofNat 244886581, Int.negSucc 1249914580, Int.negSucc 755521030,
  Int.ofNat 226308968, Int.ofNat 134321388, Int.ofNat 2521687255, Int.ofNat 5148537356,
  Int.negSucc 1875800154, Int.negSucc 2901044340, Int.ofNat 1373626408, Int.negSucc 10477036384,
  Int.negSucc 14004880366, Int.negSucc 786713595, Int.ofNat 10280810566, Int.ofNat 21243341264,
  Int.negSucc 13812182696, Int.negSucc 44878109878, Int.negSucc 16331879252,
  Int.negSucc 49157344940, Int.negSucc 59256410406, Int.negSucc 138618772353,
  Int.negSucc 51477286591, Int.negSucc 28601947607, Int.ofNat 87677955212, Int.negSucc 33333572,
  Int.negSucc 155158296495, Int.negSucc 51227035444, Int.negSucc 195477697327,
  Int.negSucc 218930495649, Int.negSucc 79073476943, Int.negSucc 157696698528,
  Int.negSucc 150924227168, Int.ofNat 420457688443, Int.ofNat 77169416507,
  Int.ofNat 433186020597 ]
private def mm16R128V4P1 : List ℤ := [
  Int.ofNat 31164361412, Int.ofNat 521440025097, Int.ofNat 721515123055, Int.ofNat 316194561036,
  Int.negSucc 100310322187, Int.negSucc 113552486307, Int.ofNat 624382008391,
  Int.ofNat 321605078583, Int.ofNat 370145052123, Int.negSucc 328535812196,
  Int.negSucc 454196316011, Int.ofNat 792334944537, Int.ofNat 1926462553072,
  Int.negSucc 238503833974, Int.ofNat 4067349858990, Int.ofNat 939386755382,
  Int.negSucc 770123083768, Int.negSucc 1494441932671, Int.ofNat 2346146908107,
  Int.ofNat 6628355584601, Int.ofNat 3223924937630, Int.negSucc 835819087533,
  Int.negSucc 2553822742503, Int.negSucc 8365786032678, Int.negSucc 11883576788627,
  Int.negSucc 7885224711921, Int.negSucc 4835748300953, Int.negSucc 5377609502906,
  Int.ofNat 2262549596751, Int.ofNat 11041690587330, Int.ofNat 7863374159340,
  Int.negSucc 6062174664260, Int.ofNat 7838230801744, Int.negSucc 6419096639721,
  Int.negSucc 3641062670059, Int.negSucc 2835841836297, Int.ofNat 10463340402968,
  Int.ofNat 2372785702960, Int.negSucc 2301274648741, Int.negSucc 1017888585590,
  Int.negSucc 4513774455809, Int.negSucc 6716761715093, Int.negSucc 13564587161940,
  Int.negSucc 17726595087330, Int.negSucc 10563536328179, Int.ofNat 1519646793501,
  Int.ofNat 10120567369823, Int.ofNat 5130664266114 ]
private def mm16R128V4P2 : List ℤ := [
  Int.ofNat 11356294896318, Int.ofNat 5194198912990, Int.negSucc 3642950600591,
  Int.ofNat 11777896827735, Int.negSucc 9439052267189, Int.ofNat 18399171613621,
  Int.ofNat 8433710541166, Int.ofNat 22671812947059, Int.negSucc 27866640419883,
  Int.negSucc 145291819784962, Int.negSucc 289616466231554, Int.negSucc 405516268655710,
  Int.negSucc 465322351612479, Int.negSucc 447501333675258, Int.negSucc 391281008287497,
  Int.negSucc 297427446637466, Int.negSucc 203759676576671, Int.negSucc 137622482436473,
  Int.negSucc 79044876049922, Int.negSucc 38538732836109, Int.negSucc 14693508538184,
  Int.negSucc 4312038853510, Int.negSucc 1454272568862, Int.negSucc 678084698753,
  Int.negSucc 301592569764, Int.negSucc 107187994016, Int.negSucc 30194982431,
  Int.negSucc 6858362547, Int.negSucc 1269535324, Int.negSucc 191702693, Int.negSucc 23329920,
  Int.ofNat 2181309, Int.negSucc 135282 ]
private def mm16R128V4 : List ℤ :=
  mm16R128V4P0 ++ (mm16R128V4P1 ++ mm16R128V4P2)
private def mm16R128V5P0 : List ℤ := [
  Int.ofNat 1296906, Int.ofNat 9203372, Int.ofNat 5547879, Int.ofNat 11753870,
  Int.ofNat 29423583, Int.negSucc 89883606, Int.negSucc 17060976, Int.negSucc 253504105,
  Int.negSucc 118509896, Int.ofNat 37393220, Int.ofNat 285578910, Int.negSucc 765701034,
  Int.ofNat 942855321, Int.ofNat 467243891, Int.ofNat 779399486, Int.ofNat 826910095,
  Int.negSucc 933322263, Int.ofNat 516451262, Int.ofNat 533988917, Int.ofNat 947794168,
  Int.ofNat 1061285196, Int.ofNat 1298574244, Int.ofNat 4148132108, Int.ofNat 1303475327,
  Int.ofNat 3501886695, Int.negSucc 2084708733, Int.ofNat 4105119091, Int.ofNat 1945020799,
  Int.ofNat 6705368478, Int.ofNat 10783765849, Int.ofNat 10454590987, Int.ofNat 24647366636,
  Int.ofNat 3021444162, Int.ofNat 23945511772, Int.ofNat 18801965356, Int.negSucc 13960141221,
  Int.ofNat 9989004871, Int.ofNat 43835591205, Int.ofNat 35209830828, Int.ofNat 4038213276,
  Int.ofNat 24821982132, Int.ofNat 109463453479, Int.ofNat 42295425729, Int.negSucc 12938422960,
  Int.negSucc 68789371718, Int.ofNat 32723594619, Int.ofNat 140472955491, Int.ofNat 12465286977
  ]
private def mm16R128V5P1 : List ℤ := [
  Int.ofNat 169722586892, Int.ofNat 159442403602, Int.negSucc 206895053713,
  Int.ofNat 109980293774, Int.negSucc 219093531315, Int.ofNat 306310902622,
  Int.ofNat 142984091430, Int.negSucc 28518230389, Int.negSucc 178348023677,
  Int.ofNat 28822307264, Int.negSucc 220375810033, Int.negSucc 651287628105,
  Int.negSucc 1214280864290, Int.negSucc 924166334516, Int.negSucc 40431125227,
  Int.ofNat 2189397186474, Int.ofNat 156750805143, Int.negSucc 646255500614,
  Int.ofNat 747707902993, Int.ofNat 1037184940691, Int.negSucc 450430625140,
  Int.ofNat 2588560159867, Int.ofNat 1652902203686, Int.negSucc 1452940458587,
  Int.negSucc 969626546528, Int.negSucc 1000027001672, Int.ofNat 272411594981,
  Int.negSucc 1483364398826, Int.negSucc 2309253116019, Int.ofNat 795312346417,
  Int.ofNat 3654458119216, Int.ofNat 5684544976072, Int.ofNat 3235966965612,
  Int.ofNat 2398483113020, Int.ofNat 773650702553, Int.ofNat 1760070813553,
  Int.ofNat 1094386893113, Int.ofNat 253334631246, Int.ofNat 9212939105852,
  Int.ofNat 4087053249443, Int.negSucc 8200956076332, Int.negSucc 17208374883014,
  Int.negSucc 9792039015829, Int.negSucc 10312879839077, Int.ofNat 5155353411155,
  Int.ofNat 5381651361042, Int.ofNat 8603528289197, Int.negSucc 5634849734235 ]
private def mm16R128V5P2 : List ℤ := [
  Int.negSucc 4359395453422, Int.ofNat 4397552140303, Int.ofNat 15189665646379,
  Int.ofNat 6172660392012, Int.ofNat 1441552315350, Int.ofNat 11932883982160,
  Int.ofNat 18659320803831, Int.negSucc 9193271126441, Int.negSucc 769297863654,
  Int.negSucc 17278105186591, Int.negSucc 10174888970794, Int.negSucc 21042420581550,
  Int.negSucc 22429139089224, Int.ofNat 3054764033350, Int.ofNat 29211498042802,
  Int.negSucc 4088503029020, Int.negSucc 16954547875865, Int.ofNat 2219992881921,
  Int.ofNat 26237982784317, Int.ofNat 9750821020192, Int.negSucc 18772037592719,
  Int.negSucc 30634100144817, Int.negSucc 28783185824370, Int.negSucc 19480019049373,
  Int.negSucc 65874437495283, Int.negSucc 288678110320160, Int.negSucc 499693273147536,
  Int.negSucc 565671759383008, Int.negSucc 470998953348822, Int.negSucc 299204766481807,
  Int.negSucc 144443432270542, Int.negSucc 51832633886526, Int.negSucc 10926159239212 ]
private def mm16R128V5 : List ℤ :=
  mm16R128V5P0 ++ (mm16R128V5P1 ++ mm16R128V5P2)
private def mm16Anc0 : List DickeSol.RampKick128kAnchor := [
  ⟨3, mm16SegsR3, mm16RowR3⟩, ⟨4, mm16SegsR4, mm16RowR4⟩, ⟨5, mm16SegsR5, mm16RowR5⟩,
  ⟨6, mm16SegsR6, mm16RowR6⟩, ⟨7, mm16SegsR7, mm16RowR7⟩, ⟨8, mm16SegsR8, mm16RowR8⟩,
  ⟨9, mm16SegsR9, mm16RowR9⟩, ⟨10, mm16SegsR10, mm16RowR10⟩, ⟨11, mm16SegsR11, mm16RowR11⟩,
  ⟨14, mm16SegsR14, mm16RowR14⟩, ⟨16, mm16SegsR16, mm16RowR16⟩ ]
private def mm16Anc1 : List DickeSol.RampKick128kAnchor := [
  ⟨18, mm16SegsR18, mm16RowR18⟩, ⟨20, mm16SegsR20, mm16RowR20⟩, ⟨24, mm16SegsR24, mm16RowR24⟩ ]
private def mm16k128Anchors : List DickeSol.RampKick128kAnchor :=
  mm16Anc0 ++ (mm16Anc1 ++ [⟨32, mm16SegsR32, mm16RowR32⟩,
    ⟨64, mm16SegsR64, mm16RowR64⟩, ⟨128, mm16SegsR128, mm16RowR128⟩])

private theorem mm16Batch0 : mm16AtF [
    DickeSol.rkm128kCheckTable 16 128 16 true mm16k128VPot mm16k128Anchors,
    mm16ChkCell 4 2 366972263893023 1000000000000000 mm16k128VPot mm16k128Anchors,
    mm16ChkCell 8 2 131157306716427 500000000000000 mm16k128VPot mm16k128Anchors,
    mm16ChkCell 16 2 55574575590339 250000000000000 mm16k128VPot mm16k128Anchors,
    mm16ChkCell 32 4 39978056717363 200000000000000 mm16k128VPot mm16k128Anchors,
    mm16ChkCell 64 8 93291456077201 500000000000000 mm16k128VPot mm16k128Anchors,
    mm16ChkCell 128 16 89292582836643 500000000000000 mm16k128VPot mm16k128Anchors,
    mm16SegBds 64 mm16SegsR64, mm16SegBds 128 mm16SegsR128, mm16ChkAnchors mm16Anc0
  ] = true := by decide +kernel
private theorem mm16Batch1 : mm16ChkAnchors mm16Anc1 = true := by decide +kernel
private theorem mm16Batch2 :
    Bool.and (mm16ChkRow 32 mm16SegsR32 mm16RowR32)
      (mm16ChkSeg 64 mm16R64C0 1 0 1 [Int.ofNat DickeSol.wdScale]
        (4, 64, 126675, mm16R64V1)) = true := by decide +kernel
private theorem mm16Batch3 :
    mm16ChkSeg 64 mm16R64C1 4 64 126675 mm16R64V1
      (7, 64, 281252, mm16R64V2) = true := by decide +kernel
private theorem mm16Batch4 :
    Bool.and (mm16ChkFin 64 mm16R64C2 7 64 281252 mm16R64V2 mm16RowR64)
      (mm16ChkSeg 128 mm16R128C0 1 0 1 [Int.ofNat DickeSol.wdScale]
        (4, 64, 383088, mm16R128V1)) = true := by
  decide +kernel
private theorem mm16Batch5 :
    mm16ChkSeg 128 mm16R128C1 4 64 383088 mm16R128V1
      (8, 128, 596966, mm16R128V2) = true := by decide +kernel
private theorem mm16Batch6 :
    mm16ChkSeg 128 mm16R128C2 8 128 596966 mm16R128V2
      (11, 128, 818052, mm16R128V3) = true := by decide +kernel
private theorem mm16Batch7 :
    mm16ChkSeg 128 mm16R128C3 11 128 818052 mm16R128V3
      (14, 128, 1133297, mm16R128V4) = true := by decide +kernel
private theorem mm16Batch8 :
    mm16ChkSeg 128 mm16R128C4 14 128 1133297 mm16R128V4
      (15, 128, 1419283, mm16R128V5) = true := by decide +kernel
private theorem mm16Batch9 :
    mm16ChkFin 128 mm16R128C5 15 128 1419283 mm16R128V5 mm16RowR128 = true := by decide +kernel

private theorem mm16Row64Sound :
    DickeSol.rkm128kEvalRowLo12 16 16 64 mm16SegsR64 = mm16RowR64 := by
  apply mm16CertSplit (mm16_hd (mm16_tl1 (mm16_tl2 (mm16_tl4 mm16Batch0))))
  unfold mm16SegsR64; exact mm16TailStep (mm16_and_r mm16Batch2)
    (mm16TailStep mm16Batch3 (mm16TailEnd (mm16_and_l mm16Batch4)))
private theorem mm16Row128Sound :
    DickeSol.rkm128kEvalRowLo12 16 16 128 mm16SegsR128 = mm16RowR128 := by
  apply mm16CertSplit (mm16_hd (mm16_tl8 mm16Batch0)); unfold mm16SegsR128
  exact mm16TailStep (mm16_and_r mm16Batch4) (mm16TailStep mm16Batch5
    (mm16TailStep mm16Batch6 (mm16TailStep mm16Batch7
      (mm16TailStep mm16Batch8 (mm16TailEnd mm16Batch9)))))
private theorem mm16AncSound :
    DickeSol.RampKick128kAnchorsSound 16 16 mm16k128Anchors :=
  mm16ChkAnchors_append (mm16_hd (mm16_tl1 (mm16_tl8 mm16Batch0)))
    (mm16ChkAnchors_append mm16Batch1
      ⟨mm16ListEq_eq (@mm16NatEq_eq) (mm16_and_l mm16Batch2),
        ⟨mm16Row64Sound, ⟨mm16Row128Sound, trivial⟩⟩⟩)
private theorem mm16k128Valid :
    DickeSol.RampKick128kTableValid 16 128 16 true mm16k128VPot mm16k128Anchors :=
  DickeSol.rkm128kCheckTable_sound mm16AncSound (mm16_hd mm16Batch0)
private theorem mm16k128CellChecks {m k : ℕ}
    (h : isMidM16K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (midM16K128KrotovCertCellLMax m k)
        mm16k128Anchors = true ∧
      ∃ num den : ℕ, relCostMidM16K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (mm16k128VPot.getD k 0) num den = true := by
  unfold isMidM16K128KrotovCertCell at h
  split_ifs at h with hm16 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm16 hk4; have hm := mm16_hd (mm16_tl1 mm16Batch0)
    exact ⟨mm16_and_l hm, 366972263893023, 1000000000000000, rfl, mm16_and_r hm⟩
  · subst hm16 hk8; have hm := mm16_hd (mm16_tl2 mm16Batch0)
    exact ⟨mm16_and_l hm, 131157306716427, 500000000000000, rfl, mm16_and_r hm⟩
  · subst hm16 hk16; have hm := mm16_hd (mm16_tl1 (mm16_tl2 mm16Batch0))
    exact ⟨mm16_and_l hm, 55574575590339, 250000000000000, rfl, mm16_and_r hm⟩
  · subst hm16 hk32; have hm := mm16_hd (mm16_tl4 mm16Batch0)
    exact ⟨mm16_and_l hm, 39978056717363, 200000000000000, rfl, mm16_and_r hm⟩
  · subst hm16 hk64; have hm := mm16_hd (mm16_tl1 (mm16_tl4 mm16Batch0))
    exact ⟨mm16_and_l hm, 93291456077201, 500000000000000, rfl, mm16_and_r hm⟩
  · subst hm16 hk128; have hm := mm16_hd (mm16_tl2 (mm16_tl4 mm16Batch0))
    exact ⟨mm16_and_l hm, 89292582836643, 500000000000000, rfl, mm16_and_r hm⟩

private lemma mm16k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma mm16k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma mm16k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl
private lemma mm16k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d
private lemma mm16k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (mm16k128_le_of_add h), rfl⟩

private structure Mm16k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ midM16K128KrotovCertCellLMax m k
  hl1 : 1 ≤ midM16K128KrotovCertCellLMax m k
  hlm : midM16K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 16 true mm16k128VPot mm16k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (midM16K128KrotovCertCellLMax m k)
    mm16k128Anchors = true
  hcost : ∃ num den : ℕ, relCostMidM16K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (mm16k128VPot.getD k 0) num den = true

private lemma mm16k128_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hj : (j + 1) + d1 = 11)
    (h128 : k + dk = 128) (hl2 : 2 + dl2 = midM16K128KrotovCertCellLMax 16 k)
    (hl1 : 1 + dl1 = midM16K128KrotovCertCellLMax 16 k)
    (hlm : midM16K128KrotovCertCellLMax 16 k * 16 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (midM16K128KrotovCertCellLMax 16 k)
      mm16k128Anchors = true)
    (hcost : ∃ num den : ℕ, relCostMidM16K128KrotovCert 16 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 16 k (mm16k128VPot.getD k 0) num den = true) :
    Mm16k128CellProps 16 k :=
  ⟨mm16k128_mem_grid 4 6 rfl, hk ▸ mm16k128_mem_grid j d1 hj, mm16k128_le_of_add h128,
    mm16k128_le_of_add (d := 14) rfl, mm16k128_le_of_add hl2, mm16k128_le_of_add hl1,
    mm16k128_le_of_add hlm, mm16k128Valid, hlmax, hcost⟩

private theorem mm16k128_all_props {m k : ℕ} (h : isMidM16K128KrotovCertCell m k = true) :
    Mm16k128CellProps m k := by
  rcases mm16k128CellChecks h with ⟨hlmax, hcost⟩; unfold isMidM16K128KrotovCertCell at h
  split_ifs at h with hm16 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm16 hk4; exact mm16k128_mk 2 8 124 0 1 65504 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm16 hk8; exact mm16k128_mk 3 7 120 0 1 65504 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm16 hk16; exact mm16k128_mk 4 6 112 0 1 65504 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm16 hk32; exact mm16k128_mk 5 5 96 2 3 65472 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm16 hk64; exact mm16k128_mk 6 4 64 6 7 65408 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm16 hk128; exact mm16k128_mk 7 3 0 14 15 65280 rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def midM16K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ midM16K128KrotovCertQubits n m k)) Var
      (midM16K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isMidM16K128KrotovCertCell m k = true then
    let p := mm16k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG mm16k128VPot mm16k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the 6 m = 16, 4 ≤ k ≤ 128 cells. -/
noncomputable def findAllJohnsonRampKick128kMidM16K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ midM16K128KrotovCertQubits n m k)) Var
      (midM16K128KrotovCertQubits n m k) ((n + 1) * m) :=
  midM16K128KrotovCertCircuitImpl res n m k

private lemma mm16k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isMidM16K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kMidM16K128KrotovCertCircuit res n m k =
      let p := mm16k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG mm16k128VPot mm16k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kMidM16K128KrotovCertCircuit midM16K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-1 recovery of S across the 6 m = 16, 4 ≤ k ≤ 128 cells. -/
theorem midM16K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isMidM16K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kMidM16K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [mm16k128_targetSets_eq]
  have hp := mm16k128_all_props hcell
  rw [mm16k128_circuit_eq res n hcell, ← mm16k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG mm16k128VPot mm16k128Anchors hp.hk128
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across m = 16, 4 ≤ k ≤ 128. -/
theorem midM16K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isMidM16K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kMidM16K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostMidM16K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := mm16k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG mm16k128VPot
    mm16k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [mm16k128_circuit_eq res n hcell, ← mm16k128_oracle_eq]
    exact hq S (by rwa [mm16k128_targetSets_eq])
  · rw [← mm16k128_targetSets_eq, ← mm16k128_vanilla_eq]; exact hsum
end
end QuantumComputation.Specs.GroverFindAll.Rk128kMidM16K128KrCert
