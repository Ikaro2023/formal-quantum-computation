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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM128K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM1024F256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt2

/-
# Krotov `m = 8` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kLowM8K128KrCert`)

QHL-verified module packaging all `6` `m = 8, 4 ≤ k ≤ 128` cells
(`(8, 4), (8, 8), (8, 16), (8, 32), (8, 64), (8, 128)`) over `18` anchors (`588` segments,
`438,396` F1272 / `449,015` Horner coord-ops at `lTableMax = 32`, `useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM8K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m = 8, k ∈ {4, 8, 16, 32, 64, 128}`, `6` cells). -/
def isLowM8K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 8 then
    if k == 4 then true
    else if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor `L_{\max}(8, k)` across `k ∈ {4..128}`. -/
def lowM8K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 8 then
    if k == 4 then 2
    else if k == 8 then 2
    else if k == 16 then 4
    else if k == 32 then 8
    else if k == 64 then 16
    else if k == 128 then 32
    else 1
  else 1

/-- Total register qubit budget `(lowM8K128KrotovCertCellLMax m k * m) * (n + 1) + k * n`. -/
abbrev lowM8K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (lowM8K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile `c(8, k): ℚ≥0` across `k ∈ {4..128}`. -/
def relCostLowM8K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 8 then
    if k == 4 then NNRat.divNat 394478990346047 1000000000000000
    else if k == 8 then NNRat.divNat 165617643496611 500000000000000
    else if k == 16 then NNRat.divNat 295827281048903 1000000000000000
    else if k == 32 then NNRat.divNat 273808992547581 1000000000000000
    else if k == 64 then NNRat.divNat 129786223141919 500000000000000
    else if k == 128 then NNRat.divNat 50073041844323 200000000000000
    else 1
  else 1

/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def lowM8K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isLowM8K128KrotovCertCell, relCostLowM8K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kLowM8K128KrCert` cell lies on `groverGrid × groverGrid`. -/
theorem isLowM8K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isLowM8K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isLowM8K128KrotovCertCell at h
  split_ifs at h with hm8 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm8 hk4; rfl
  · subst hm8 hk8; rfl
  · subst hm8 hk16; rfl
  · subst hm8 hk32; rfl
  · subst hm8 hk64; rfl
  · subst hm8 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def lm8NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem lm8NatEq_eq {x y : ℕ} (h : lm8NatEq x y = true) : x = y := by
  unfold lm8NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def lm8IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => lm8NatEq m n
  | Int.negSucc m, Int.negSucc n => lm8NatEq m n
  | _, _ => false
private theorem lm8IntEq_eq {a b : ℤ} (h : lm8IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [lm8IntEq] at h; exact congrArg Int.ofNat (lm8NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => dsimp only [lm8IntEq] at h; exact congrArg Int.negSucc (lm8NatEq_eq h)
private def lm8ListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (lm8ListEq eqF xr yr) false
  | _, _ => false
private theorem lm8ListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : lm8ListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [lm8ListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev Lm8St := ℕ × ℕ × ℕ × List ℤ
private def lm8StEq (a b : Lm8St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (lm8NatEq a1 b1) (cond (lm8NatEq a2 b2)
      (cond (lm8NatEq a3 b3) (lm8ListEq lm8IntEq av bv) false) false) false
private theorem lm8StEq_eq {a b : Lm8St} (h : lm8StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [lm8StEq] at h
  cases h1 : lm8NatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : lm8NatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : lm8NatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h
        exact Prod.ext (lm8NatEq_eq h1) (Prod.ext (lm8NatEq_eq h2)
          (Prod.ext (lm8NatEq_eq h3) (lm8ListEq_eq (@lm8IntEq_eq) h)))
private def lm8AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (lm8AtF rest) false
private theorem lm8_hd {b : Bool} {bs : List Bool} (h : lm8AtF (b :: bs) = true) :
    b = true := by unfold lm8AtF at h; cases b with | false => cases h | true => rfl
private theorem lm8_tl1 {b : Bool} {s : List Bool} (h : lm8AtF (b :: s) = true) :
    lm8AtF s = true := by
  unfold lm8AtF at h; cases b with | false => cases h | true => exact h
private theorem lm8_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : lm8AtF (b1 :: b2 :: bs) = true) : lm8AtF bs = true := lm8_tl1 (lm8_tl1 h)
private theorem lm8_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : lm8AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : lm8AtF bs = true :=
  lm8_tl2 (lm8_tl2 h)
private theorem lm8_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with | false => cases h | true => rfl
private theorem lm8_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with | false => cases h | true => cases b with | false => cases h | true => rfl
private abbrev lm8M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def lm8ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  lm8ListEq lm8NatEq (DickeSol.rkm128kEvalRowLo12 8 32 r s) ro
private theorem lm8_row_eq {r : ℕ} {s : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (h : lm8ChkRow r s ro = true) : DickeSol.rkm128kEvalRowLo12 8 32 r s = ro :=
  lm8ListEq_eq (@lm8NatEq_eq) h
private def lm8ChkSlice (r : ℕ) (s : List DickeSol.Rkm128kSeg)
    (l0 d0 p0 : ℕ) (v0 : List ℤ) (st1 : Lm8St) : Bool :=
  lm8StEq (DickeSol.rkm128kRunSegs 8 32 r s l0 d0 p0 v0) st1
private theorem lm8_sl_end {r : ℕ} {s : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 : ℕ} {v0 : List ℤ} {st1 : Lm8St}
    (h : lm8ChkSlice r s l0 d0 p0 v0 st1 = true) :
    DickeSol.rkm128kRunSegs 8 32 r s l0 d0 p0 v0 = st1 := lm8StEq_eq h
private theorem lm8_sl_step {r : ℕ} {s1 s2 : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {st2 : Lm8St}
    (h1 : lm8ChkSlice r s1 l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : DickeSol.rkm128kRunSegs 8 32 r s2 l1 d1 p1 v1 = st2) :
    DickeSol.rkm128kRunSegs 8 32 r (s1 ++ s2) l0 d0 p0 v0 = st2 := by
  unfold lm8ChkSlice at h1; rw [DickeSol.rkm128kRunSegs_append, lm8StEq_eq h1]; exact h2
private def lm8LenGuard (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def lm8FinGuard (st : Lm8St) (ro : List ℕ) : Bool :=
  lm8ListEq lm8NatEq (DickeSol.rkm128kFinalizeState st) ro
private theorem lm8_cert_row {r : ℕ} (s : List DickeSol.Rkm128kSeg)
    (st : Lm8St) (ro : List ℕ) (hsegs : lm8LenGuard r s = true)
    (hrun : DickeSol.rkm128kRunSegs 8 32 r s 1 0 1 [Int.ofNat DickeSol.wdScale] = st)
    (hfin : lm8FinGuard st ro = true) : DickeSol.rkm128kEvalRowLo12 8 32 r s = ro :=
  DickeSol.rkm128kCertRow_of_runSegs hsegs hrun (lm8ListEq_eq (@lm8NatEq_eq) hfin)
private def lm8ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 8 k (v.getD k 0) n d)
private lemma lm8ChkCell_l {k lm n d : ℕ} {v : List ℕ} {a : List DickeSol.RampKick128kAnchor}
    (h : lm8ChkCell k lm n d v a = true) : DickeSol.rkm128kCheckAnchorsLMax k lm a = true :=
  lm8_and_l h
private lemma lm8ChkCell_r {k lm n d : ℕ} {v : List ℕ} {a : List DickeSol.RampKick128kAnchor}
    (h : lm8ChkCell k lm n d v a = true) :
    DickeSol.checkAltBound12 8 k (v.getD k 0) n d = true :=
  lm8_and_r h

private def lm8k128VPot : List ℕ :=
  [ 0, 227228439465768, 268660763640004, 286768324820459, 305006636607108, 326462275411011,
    354466944743780, 381928303701106, 402073720373687, 422276237490046, 494132179277798,
    463519090919321, 480778484926533, 543800314906340, 515606429370796, 574276560159838,
    547416327600859, 602527319192720, 656085576000948, 708215355197250, 608233313009110,
    657818623670947, 706263889741417, 753644294653725, 666910192636035, 712355880529189,
    756919043870697, 800649177435064, 843591316122758, 723512097451155, 764998144785188,
    805809577284510, 755866406028290, 795421800136962, 834391156009482, 872799772491445,
    910671179069073, 948027304404222, 984888624775685, 1021274295279350, 1057202266173226,
    908831003768443, 943893113184670, 978545125342109, 1012801101496925, 1046674317301369,
    1080177322910227, 1113321997300982, 1146119597474257, 1178580803112224, 1210715757197161,
    1242534103028029, 1274045018017933, 1305257244608132, 1336179118593689, 1366818595120801,
    1397183272585523, 1427280414637304, 1457116970467836, 1486699593545757, 1516034658940278,
    1545128279361496, 1573986320031704, 1602614412490167, 1052489395777519, 1080673614957776,
    1108643502364525, 1136403874556009, 1163959370351940, 1191314459882375, 1218473453052765,
    1245440507470564, 1272219635874678, 1298814713105338, 1325229482648677, 1351467562787297,
    1377532452385448, 1403427536334991, 1429156090686152, 1454721287485076, 1480126199338409,
    1505373803723495, 1530466987061306, 1555408548567879, 1580201203898798, 1604847588600162,
    1629350261378446, 1653711707200735, 1677934340235970, 1702020506647057, 1725972487242975,
    1749792499999370, 1773482702455524, 1797045193995022, 1820482018016945, 1843795164003942,
    1866986569493110, 1890058121955197, 1913011660587295, 1935848978023839, 1958571821970416,
    1981181896764598, 2003680864867744, 2026070348291465, 2048351929962219, 2070527155027282,
    2092597532105143, 2114564534483190, 2136429601265374, 2158194138472384, 2179859520096711,
    2201427089114841, 2222898158458688, 2244274011948257, 2265555905187406, 2286745066424484,
    2307842697379504, 2328849974039440, 2349768047423124, 2370598044317158, 2391341067984175,
    2411998198844700, 2432570495133811, 2453058993533726, 2473464709783387, 2493788639266054,
    2514031757575869, 2534195021064311, 1474635473509539 ]
private def lm8Row_r3 : List ℕ :=
  [ 11623, 72509456687, 927490531661 ]
private def lm8Sgs_r3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 71278804, 1, 16, []⟩,
  ⟨1, 30680647, 1, 14, []⟩,
  ⟨1, 7654964, 1, 10, []⟩,
  ⟨1, 10, 1, 8, []⟩,
  lm8M 1 111860330 1 20 1 [1],
  lm8M 1 6425450 1 10 1 [1],
  lm8M 1 7510817 1 10 1 [1],
  lm8M 1 6325144 1 10 1 [1],
  lm8M 1 1519285 1 8 1 [1],
  lm8M 1 1493948 1 8 1 [1],
  lm8M 1 5454834 1 10 2 [3],
  lm8M 1 337265 1 8 1 [1],
  lm8M 1 948481 1 8 2 [2],
  lm8M 1 1333414 1 8 2 [2],
  lm8M 1 1258656 1 8 1 [1],
  lm8M 1 79841 1 8 2 [2],
  lm8M 1 1338830 1 8 2 [2],
  lm8M 1 1345319 1 8 2 [3],
  lm8M 1 1341266 1 8 2 [2],
  lm8M 1 1256136 1 8 1 [1],
  lm8M 1 72840 1 8 2 [3],
  lm8M 1 1328923 1 8 2 [2],
  lm8M 1 1349320 1 8 2 [3],
  lm8M 1 1332426 1 8 2 [2],
  lm8M 1 1232245 1 8 2 [2],
  lm8M 1 1131185 1 8 2 [2],
  lm8M 1 1138456 1 8 2 [2],
  lm8M 1 1231273 1 8 2 [3],
  ⟨1, 403404, 1, 8, []⟩,
  lm8M 1 911811 1 8 2 [2],
  ⟨1, 716787, 1, 8, []⟩]
private def lm8Anc_r3 : DickeSol.RampKick128kAnchor :=
  ⟨3, lm8Sgs_r3, lm8Row_r3⟩
private def lm8Row_r4 : List ℕ :=
  [ 2205, 31374, 64717372370, 935282593999 ]
private def lm8Sgs_r4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 76413939, 1, 18, []⟩,
  ⟨1, 35209816, 1, 14, []⟩,
  ⟨1, 29582651, 1, 14, []⟩,
  ⟨1, 27039317, 1, 14, []⟩,
  ⟨1, 19174759, 1, 12, []⟩,
  lm8M 1 19047594 1 12 1 [1],
  lm8M 1 8464454 1 10 1 [1],
  lm8M 1 13473809 1 10 2 [2],
  lm8M 1 4331594 1 8 2 [2],
  lm8M 1 4835413 1 8 2 [2],
  lm8M 1 5644632 1 8 2 [2],
  lm8M 1 7323938 1 10 2 [2],
  lm8M 1 10383857 1 10 3 [4],
  lm8M 1 1583774 1 6 3 [4],
  lm8M 1 1593210 1 6 3 [7],
  lm8M 1 1593959 1 6 3 [4],
  lm8M 1 1575805 1 6 3 [7],
  lm8M 1 1574641 1 6 3 [4],
  lm8M 1 1590527 1 6 3 [7],
  lm8M 1 1584572 1 6 3 [6],
  lm8M 1 1575907 1 6 3 [4],
  lm8M 1 1582864 1 6 3 [5],
  lm8M 1 1588574 1 6 3 [7],
  lm8M 1 1589472 1 6 3 [4],
  lm8M 1 1583982 1 6 3 [5],
  lm8M 1 1579590 1 6 3 [6],
  lm8M 1 1578638 1 6 3 [4],
  lm8M 1 1583281 1 6 3 [4],
  lm8M 1 1586021 1 6 3 [6],
  lm8M 1 1584837 1 6 3 [6],
  lm8M 1 1582984 1 6 3 [7],
  ⟨1, 862589, 1, 6, []⟩]
private def lm8Anc_r4 : DickeSol.RampKick128kAnchor :=
  ⟨4, lm8Sgs_r4, lm8Row_r4⟩
private def lm8Row_r5 : List ℕ :=
  [ 57, 10578, 436217, 64732993750, 935266559355 ]
private def lm8Sgs_r5 : List DickeSol.Rkm128kSeg := [
  lm8M 1 195620163 1 43 1 [1],
  lm8M 1 21134789 1 17 2 [3],
  lm8M 1 5780261 1 12 1 [1],
  lm8M 1 15628539 1 15 3 [4],
  lm8M 1 2102347 1 10 1 [1],
  lm8M 1 3926835 1 11 3 [4],
  lm8M 1 7107346 1 12 3 [7],
  lm8M 1 9337044 1 13 3 [4],
  lm8M 1 11538002 1 14 2 [2],
  lm8M 1 2213724 1 10 4 [8],
  lm8M 1 560426 1 8 1 [1],
  lm8M 1 1064002 1 8 1 [1],
  lm8M 1 1254815 1 9 4 [9],
  lm8M 1 2951843 1 10 4 [9],
  lm8M 1 3000489 1 10 4 [14],
  lm8M 1 2991111 1 10 4 [8],
  lm8M 1 2971667 1 10 4 [9],
  lm8M 1 1086305 1 8 2 [3],
  lm8M 1 1905848 1 9 4 [11],
  lm8M 1 2724265 1 10 4 [8],
  lm8M 1 2110833 1 10 4 [9],
  lm8M 1 2008978 1 9 4 [10],
  lm8M 1 2452088 1 10 4 [10],
  lm8M 1 2725416 1 10 4 [8],
  lm8M 1 2855367 1 10 4 [9],
  lm8M 1 2959244 1 10 4 [9],
  lm8M 1 1741125 1 9 4 [10],
  ⟨1, 106, 1, 6, []⟩]
private def lm8Anc_r5 : DickeSol.RampKick128kAnchor :=
  ⟨5, lm8Sgs_r5, lm8Row_r5⟩
private def lm8Row_r6 : List ℕ :=
  [ 443, 0, 25805, 1224540, 72554721522, 927444027504 ]
private def lm8Sgs_r6 : List DickeSol.Rkm128kSeg := [
  lm8M 1 184990593 1 45 1 [1],
  lm8M 1 18198674 1 17 2 [3],
  lm8M 1 18823935 1 17 3 [5],
  lm8M 1 10413695 1 14 3 [4],
  lm8M 1 5893808 1 12 1 [1],
  lm8M 1 6831210 1 13 2 [2],
  lm8M 1 4270315 1 11 4 [9],
  lm8M 1 1742333 1 9 2 [2],
  lm8M 1 5105542 1 12 1 [1],
  lm8M 1 144568 1 6 4 [10],
  lm8M 1 819241 1 8 1 [1],
  lm8M 1 278674 1 7 2 [3],
  lm8M 1 7047176 1 13 4 [10],
  lm8M 1 10518878 1 14 3 [7],
  lm8M 1 20 1 6 4 [15],
  lm8M 1 16155011 1 16 5 [29],
  lm8M 1 4066711 1 11 5 [17],
  lm8M 1 4028149 1 11 5 [23],
  lm8M 1 4028146 1 11 5 [22],
  lm8M 1 4028090 1 11 5 [17],
  lm8M 1 4028202 1 11 5 [22],
  lm8M 1 3574594 1 11 3 [6],
  lm8M 1 453462 1 7 5 [18],
  lm8M 1 4028144 1 11 5 [20],
  lm8M 1 4028140 1 11 5 [23],
  lm8M 1 4028084 1 11 5 [17],
  lm8M 1 4028214 1 11 5 [20],
  lm8M 1 4028096 1 11 5 [20],
  ⟨1, 2398407, 1, 10, []⟩]
private def lm8Anc_r6 : DickeSol.RampKick128kAnchor :=
  ⟨6, lm8Sgs_r6, lm8Row_r6⟩
private def lm8Row_r7 : List ℕ :=
  [ 751, 1196826, 13732129, 6850783, 633602, 74793531201, 925184051730 ]
private def lm8Sgs_r7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 211128101, 1, 52, []⟩,
  lm8M 2 355694 1 8 3 [6],
  lm8M 2 4997952 1 13 1 [1],
  lm8M 2 2881745 1 12 1 [1],
  lm8M 2 2378912 1 11 3 [6],
  lm8M 2 5233169 1 14 4 [14],
  lm8M 2 4923643 1 13 1 [1],
  lm8M 2 8848945 1 16 3 [7],
  lm8M 2 1 1 6 4 [9],
  lm8M 2 2621934 1 11 5 [31],
  lm8M 2 5620054 1 14 1 [1],
  lm8M 2 201544 1 7 5 [17],
  lm8M 2 6485851 1 14 1 [1],
  lm8M 2 601475 1 9 5 [16],
  lm8M 2 10709090 1 17 6 [33],
  lm8M 2 1814503 1 11 6 [32],
  lm8M 2 1815713 1 11 6 [32],
  lm8M 2 1815944 1 11 6 [32],
  lm8M 2 1816394 1 11 6 [32],
  lm8M 2 1816665 1 11 6 [32],
  lm8M 2 1816488 1 11 6 [32],
  lm8M 2 1816150 1 11 6 [32],
  lm8M 2 832645 1 9 1 [1],
  lm8M 2 983036 1 9 6 [34],
  lm8M 2 1816935 1 11 6 [34],
  lm8M 2 1817181 1 11 6 [32],
  lm8M 2 1816768 1 11 6 [32],
  ⟨2, 1060704, 1, 9, []⟩]
private def lm8Anc_r7 : DickeSol.RampKick128kAnchor :=
  ⟨7, lm8Sgs_r7, lm8Row_r7⟩
private def lm8Row_r8 : List ℕ :=
  [ 2002, 108416, 151817, 353745, 32191, 1910589, 72563118637, 927434315192 ]
private def lm8Sgs_r8 : List DickeSol.Rkm128kSeg := [
  lm8M 1 175009638 2 42 1 [1],
  lm8M 2 6098384 1 12 2 [2],
  lm8M 2 10169628 1 14 3 [4],
  lm8M 2 12074945 1 14 4 [15],
  lm8M 2 16621605 1 16 5 [31],
  lm8M 2 14902677 1 14 6 [40],
  lm8M 2 1795915 1 8 6 [55],
  lm8M 2 1112810 1 8 5 [16],
  lm8M 2 1134095 1 8 6 [48],
  lm8M 2 1858409 1 8 6 [48],
  lm8M 2 1951196 1 8 6 [63],
  lm8M 2 2476254 1 8 6 [32],
  lm8M 2 1964907 1 8 6 [63],
  lm8M 2 2719438 1 8 6 [63],
  lm8M 2 4395901 1 10 6 [47],
  lm8M 2 5856648 1 10 7 [112],
  lm8M 2 2339329 1 8 7 [126],
  lm8M 2 2343716 1 8 7 [65],
  lm8M 2 1718126 1 8 6 [63],
  lm8M 2 624186 1 6 7 [95],
  lm8M 2 2334274 1 8 7 [96],
  lm8M 2 2338668 1 8 7 [64],
  lm8M 2 2342536 1 8 7 [64],
  lm8M 2 2342574 1 8 7 [64],
  lm8M 2 2343125 1 8 7 [64],
  ⟨2, 1428132, 1, 8, []⟩]
private def lm8Anc_r8 : DickeSol.RampKick128kAnchor :=
  ⟨8, lm8Sgs_r8, lm8Row_r8⟩
private def lm8Row_r9 : List ℕ :=
  [ 1779063, 3178595, 7469778, 6066323, 87320927, 131579967, 974076313, 73379274619,
    925409191922 ]
private def lm8Sgs_r9 : List DickeSol.Rkm128kSeg := [
  lm8M 1 161709457 1 49 1 [1],
  lm8M 2 26928432 1 25 4 [9],
  lm8M 2 15885324 1 20 5 [29],
  lm8M 2 17932678 1 21 6 [37],
  lm8M 2 20408579 1 22 7 [65],
  lm8M 2 15428688 1 20 7 [79],
  lm8M 2 10766373 1 18 8 [143],
  lm8M 2 7246814 1 16 1 [1],
  ⟨2, 7183250, 1, 16, []⟩]
private def lm8Anc_r9 : DickeSol.RampKick128kAnchor :=
  ⟨9, lm8Sgs_r9, lm8Row_r9⟩
private def lm8Row_r11 : List ℕ :=
  [ 138815, 4656772, 4029674, 1201175, 219044, 30545505, 137783310, 104935001, 96877686,
    76612798052, 923006799467 ]
private def lm8Sgs_r11 : List DickeSol.Rkm128kSeg := [
  ⟨1, 126307881, 1, 45, []⟩,
  lm8M 2 23812191 1 25 1 [1],
  lm8M 2 20138963 1 23 4 [15],
  lm8M 2 20127254 1 23 6 [55],
  lm8M 2 14930665 1 21 7 [69],
  lm8M 2 15684953 1 21 8 [129],
  lm8M 2 9562030 1 18 8 [128],
  lm8M 2 9356190 1 18 9 [284],
  lm8M 3 5155952 1 16 9 [271],
  lm8M 3 4514630 1 15 9 [275],
  lm8M 3 6084420 1 17 10 [827],
  lm8M 3 2382700 1 13 10 [630],
  lm8M 3 4768097 1 16 10 [595],
  lm8M 3 4544992 1 15 10 [567],
  ⟨3, 3371141, 1, 14, []⟩]
private def lm8Anc_r11 : DickeSol.RampKick128kAnchor :=
  ⟨11, lm8Sgs_r11, lm8Row_r11⟩
private def lm8Row_r12 : List ℕ :=
  [ 68565, 234635, 1828, 7769501, 7020038, 6848741, 222937, 3766202, 1429333, 63076330,
    76600983934, 923308577639 ]
private def lm8Sgs_r12 : List DickeSol.Rkm128kSeg := [
  ⟨1, 119428456, 1, 45, []⟩,
  lm8M 2 23647603 1 26 1 [1],
  lm8M 2 3378481 1 13 2 [2],
  lm8M 2 3024778 1 13 2 [2],
  lm8M 2 6056318 1 16 3 [5],
  lm8M 2 6068008 1 16 4 [9],
  lm8M 2 3025998 1 13 2 [3],
  lm8M 2 3025959 1 13 5 [21],
  lm8M 2 2653987 1 13 5 [29],
  lm8M 2 5624588 1 16 3 [4],
  lm8M 2 5624438 1 16 6 [44],
  lm8M 2 5611070 1 16 6 [35],
  lm8M 2 5611738 1 16 7 [100],
  lm8M 2 3175369 1 13 7 [106],
  lm8M 2 3170978 1 13 7 [68],
  lm8M 3 2676579 1 14 7 [104],
  lm8M 3 2712807 1 14 8 [245],
  lm8M 3 3015080 1 14 8 [163],
  lm8M 3 2986061 1 14 7 [67],
  lm8M 3 2987362 1 14 9 [336],
  lm8M 3 2983164 1 14 9 [421],
  lm8M 3 3867919 1 15 4 [12],
  lm8M 3 3868112 1 15 9 [258],
  lm8M 3 4415265 1 16 9 [349],
  lm8M 3 4408448 1 16 10 [595],
  lm8M 3 4169524 1 15 5 [31],
  lm8M 3 4168597 1 15 10 [920],
  lm8M 3 4146739 1 15 8 [129],
  lm8M 3 4146787 1 15 11 [1958],
  lm8M 3 4718346 1 16 10 [875],
  lm8M 3 1936697 1 12 11 [1369],
  lm8M 3 2194968 1 13 6 [36],
  ⟨3, 2103719, 1, 13, []⟩]
private def lm8Anc_r12 : DickeSol.RampKick128kAnchor :=
  ⟨12, lm8Sgs_r12, lm8Row_r12⟩
private def lm8Row_r14 : List ℕ :=
  [ 21345, 27443, 699696, 107349, 3604090, 7272593, 2649805, 80714626, 43976966, 2141336,
    6305961, 59046042, 76065618583, 923727810477 ]
private def lm8Sgs_r14 : List DickeSol.Rkm128kSeg := [
  ⟨1, 91131366, 1, 41, []⟩,
  lm8M 2 50494965 1 39 3 [7],
  lm8M 2 13020864 1 21 5 [30],
  lm8M 3 7526030 1 19 6 [58],
  lm8M 3 7501511 1 19 7 [82],
  lm8M 3 7521527 1 19 8 [139],
  lm8M 3 8080847 1 20 9 [282],
  lm8M 3 5024872 1 17 9 [449],
  lm8M 3 5141164 1 17 10 [837],
  lm8M 3 5978391 1 18 8 [253],
  lm8M 3 5732332 1 18 11 [1318],
  lm8M 3 6134076 1 18 10 [668],
  lm8M 3 6010227 1 18 12 [2858],
  lm8M 3 4805285 1 17 12 [2088],
  lm8M 3 4674339 1 16 12 [4053],
  lm8M 3 4406380 1 16 12 [4011],
  lm8M 3 4390670 1 16 13 [5176],
  lm8M 3 2855868 1 14 12 [2939],
  lm8M 3 2841505 1 14 13 [4767],
  lm8M 3 2718320 1 14 13 [5101],
  ⟨3, 2020649, 1, 13, []⟩]
private def lm8Anc_r14 : DickeSol.RampKick128kAnchor :=
  ⟨14, lm8Sgs_r14, lm8Row_r14⟩
private def lm8Row_r16 : List ℕ :=
  [ 28, 219, 189285, 51239, 741292, 1979578, 1238749, 4378722, 201498, 649769, 57771, 129414,
    1276137, 80820807, 77576726232, 922331559126 ]
private def lm8Sgs_r16 : List DickeSol.Rkm128kSeg := [
  ⟨1, 97054134, 1, 45, []⟩,
  lm8M 2 29818615 1 31 1 [1],
  lm8M 2 5296608 1 16 2 [3],
  lm8M 2 3314606 1 14 3 [5],
  lm8M 2 3287086 1 14 3 [4],
  lm8M 2 3315121 1 14 4 [10],
  lm8M 2 2976331 1 14 2 [3],
  lm8M 2 2966517 1 14 5 [26],
  lm8M 3 2562245 1 14 4 [8],
  lm8M 3 2476958 1 14 6 [58],
  lm8M 3 2475426 1 14 6 [40],
  lm8M 3 2519292 1 14 3 [6],
  lm8M 3 2521078 1 14 7 [66],
  lm8M 3 2615374 1 14 5 [18],
  lm8M 3 2659866 1 14 8 [131],
  lm8M 3 2477709 1 14 8 [165],
  lm8M 3 2584709 1 14 4 [8],
  lm8M 3 2574631 1 14 9 [373],
  lm8M 3 2390460 1 14 9 [297],
  lm8M 3 2148535 1 14 9 [385],
  lm8M 3 2273834 1 14 10 [936],
  lm8M 3 2322449 1 14 10 [698],
  lm8M 3 2175180 1 14 9 [257],
  lm8M 3 2264047 1 14 10 [522],
  lm8M 3 2267910 1 14 4 [11],
  lm8M 3 2258146 1 14 11 [2035],
  lm8M 3 2508578 1 14 6 [33],
  lm8M 3 2516920 1 14 11 [1046],
  lm8M 4 2113845 1 14 12 [2170],
  lm8M 4 2135846 1 14 12 [2250],
  lm8M 4 2143139 1 14 4 [12],
  lm8M 4 2279961 1 15 5 [25],
  lm8M 4 2234621 1 14 11 [1799],
  lm8M 4 2293365 1 15 13 [7833],
  lm8M 4 2014630 1 14 9 [317],
  lm8M 4 1963724 1 14 13 [4109],
  lm8M 4 2329564 1 15 11 [1243],
  lm8M 4 2371268 1 15 11 [1576],
  lm8M 4 2162741 1 14 14 [10065],
  lm8M 4 2170427 1 14 11 [1555],
  lm8M 4 2220565 1 14 14 [10150],
  lm8M 4 1780768 1 14 11 [1578],
  lm8M 4 1837254 1 14 10 [989],
  lm8M 4 2186262 1 14 14 [10718],
  lm8M 4 2223707 1 14 15 [31779],
  lm8M 4 1777905 1 14 15 [24525],
  lm8M 4 2347050 1 15 15 [18845],
  lm8M 4 1730677 1 13 15 [22022],
  lm8M 4 1827873 1 14 15 [31088],
  lm8M 4 2099450 1 14 6 [38]]
private def lm8Anc_r16 : DickeSol.RampKick128kAnchor :=
  ⟨16, lm8Sgs_r16, lm8Row_r16⟩
private def lm8Row_r20 : List ℕ :=
  [ 1045, 601917, 41979, 1108, 1160491, 3235, 35841, 223002, 373520, 5972047, 54478, 105790031,
    10483195, 10541526, 248383502, 414164707, 33530055, 183371343, 76534559466, 922450707089 ]
private def lm8Sgs_r20 : List DickeSol.Rkm128kSeg := [
  ⟨1, 89390072, 1, 46, []⟩,
  ⟨2, 37105641, 1, 38, []⟩,
  lm8M 3 13050584 1 26 6 [58],
  lm8M 3 13439340 1 27 9 [404],
  lm8M 3 12141122 1 26 11 [1540],
  lm8M 3 7760242 1 21 12 [3947],
  lm8M 4 6540980 1 22 13 [7909],
  lm8M 4 7191517 1 22 14 [15930],
  lm8M 4 7026066 1 22 15 [16802],
  lm8M 4 8698809 1 24 16 [65438],
  lm8M 4 4773842 1 19 12 [2298],
  lm8M 4 5109293 1 20 17 [70087],
  lm8M 4 4699442 1 19 16 [57970],
  lm8M 5 4568612 1 20 18 [203972],
  lm8M 5 4108653 1 19 18 [223080],
  lm8M 5 3166126 1 18 18 [229355],
  lm8M 5 1628776 1 14 19 [463325],
  lm8M 5 1811359 1 15 19 [364555],
  lm8M 5 1788584 1 15 14 [11692],
  lm8M 5 1773949 1 15 19 [377547],
  lm8M 5 2021461 1 15 19 [263608],
  ⟨5, 1449788, 1, 14, []⟩]
private def lm8Anc_r20 : DickeSol.RampKick128kAnchor :=
  ⟨20, lm8Sgs_r20, lm8Row_r20⟩
private def lm8Row_r24 : List ℕ :=
  [ 1377, 8489, 19769, 39262, 1666920, 3593, 9305, 1186288, 160050, 182509, 13895730, 3114833,
    3512972, 82185198, 38789359, 21284158, 3747251, 656456291, 1692083318, 1536665202, 157093265,
    642936741, 65215130710, 929929827234 ]
private def lm8Sgs_r24 : List DickeSol.Rkm128kSeg := [
  ⟨1, 78787390, 1, 45, []⟩,
  lm8M 2 38180205 1 41 3 [5],
  lm8M 3 17953637 1 33 8 [229],
  lm8M 3 19293868 1 34 12 [3874],
  lm8M 3 13012634 1 28 14 [14045],
  lm8M 4 11564376 1 29 16 [49829],
  lm8M 5 6111240 1 24 17 [78194],
  lm8M 5 5638629 1 23 18 [135321],
  lm8M 5 5466070 1 23 19 [426962],
  lm8M 5 5809783 1 23 18 [253808],
  lm8M 5 1768901 1 15 20 [1040227],
  lm8M 5 4506555 1 21 20 [818938],
  lm8M 5 3704122 1 20 21 [2072018],
  lm8M 5 5227764 1 22 21 [2066466],
  lm8M 5 3837104 1 20 22 [3191145],
  lm8M 6 5177070 1 23 22 [4094081],
  lm8M 6 1997702 1 17 22 [2430236],
  lm8M 6 808790 1 13 23 [4589346],
  lm8M 6 1354919 1 15 23 [7996501],
  lm8M 6 1756660 1 16 23 [4832663],
  lm8M 6 1901082 1 16 23 [7453993],
  ⟨6, 1671044, 1, 16, []⟩]
private def lm8Anc_r24 : DickeSol.RampKick128kAnchor :=
  ⟨24, lm8Sgs_r24, lm8Row_r24⟩
private def lm8Row_r29 : List ℕ :=
  [ 19, 1349, 498, 2870, 39595, 396, 2436, 11030, 351251, 23569, 199996, 1787640, 3628045, 1560,
    4321395, 15997773, 25072380, 16228417, 2963883, 62927293, 4157060, 235043556, 984893168,
    819813943, 197246196, 3138540, 2290346, 80538948960, 917080906654 ]
private def lm8Sgs_r29 : List DickeSol.Rkm128kSeg := [
  ⟨1, 50791734, 1, 38, []⟩,
  ⟨2, 34402604, 1, 42, []⟩,
  lm8M 3 13258989 1 30 1 [1],
  lm8M 3 13171817 1 30 6 [57],
  lm8M 4 10300171 1 29 30 [536871702],
  lm8M 4 10102746 1 29 13 [4761],
  lm8M 5 8238222 1 28 16 [58074],
  lm8M 5 7547829 1 27 18 [203787],
  lm8M 5 4738235 1 23 19 [327133],
  lm8M 6 6892416 1 28 21 [1547946],
  lm8M 6 4370997 1 23 22 [4017910],
  lm8M 6 4629677 1 23 23 [7868801],
  lm8M 6 4735702 1 24 24 [16111290],
  lm8M 7 4922320 1 25 25 [24665459],
  lm8M 7 5370738 1 26 26 [67035730],
  lm8M 7 3208765 1 21 26 [35740676],
  lm8M 7 3051835 1 21 27 [94200002],
  lm8M 7 3285183 1 21 27 [133706030],
  lm8M 7 3472810 1 22 28 [251006940],
  lm8M 7 1631890 1 17 28 [235530109],
  lm8M 7 857160 1 14 27 [68087441],
  lm8M 7 681017 1 13 28 [266401487],
  lm8M 7 1086857 1 15 28 [138399488],
  ⟨7, 643464, 1, 13, []⟩]
private def lm8Anc_r29 : DickeSol.RampKick128kAnchor :=
  ⟨29, lm8Sgs_r29, lm8Row_r29⟩
private def lm8Row_r32 : List ℕ :=
  [ 8, 0, 57, 0, 102, 6, 225, 1714, 43, 12836, 19196, 25908, 28103, 326384, 155264, 38111,
    9591869, 879700, 292560, 112282614, 5252720, 34748739, 275003222, 503506379, 141913859,
    200837563, 109213392, 48059136, 121349, 20301221, 80312964248, 918224423192 ]
private def lm8Sgs_r32 : List DickeSol.Rkm128kSeg := [
  ⟨1, 57922332, 1, 42, []⟩,
  ⟨2, 29356812, 1, 39, []⟩,
  lm8M 3 9823411 1 27 2 [2],
  ⟨3, 3043409, 1, 17, []⟩,
  lm8M 3 2908722 1 17 4 [10],
  lm8M 3 2850159 1 17 5 [16],
  lm8M 4 2448865 1 17 6 [34],
  lm8M 4 2461284 1 17 29 [268435528],
  lm8M 4 2473297 1 17 31 [1342177429],
  lm8M 4 2559667 1 18 31 [1342177652],
  lm8M 4 2588483 1 18 29 [268436004],
  lm8M 4 2697822 1 18 29 [268436868],
  lm8M 5 2417283 1 18 12 [3930],
  lm8M 5 2476606 1 18 13 [4261],
  lm8M 5 2592031 1 19 14 [15396],
  lm8M 5 2667728 1 19 15 [26219],
  lm8M 5 1816715 1 17 15 [16940],
  lm8M 5 2380485 1 18 16 [39983],
  lm8M 6 2583326 1 19 17 [81979],
  lm8M 6 2744126 1 20 14 [8597],
  lm8M 6 2665376 1 20 19 [473836],
  lm8M 6 3280313 1 21 20 [786543],
  lm8M 6 3652204 1 22 33 [4296954011],
  lm8M 6 1558301 1 16 33 [4295565616],
  lm8M 6 1653001 1 17 21 [1057057],
  lm8M 7 2924327 1 21 23 [8274388],
  lm8M 7 1898916 1 18 11 [1714],
  lm8M 7 1884829 1 18 24 [10519045],
  lm8M 7 1782426 1 18 19 [268927],
  lm8M 7 1769336 1 18 25 [19784853],
  lm8M 7 1953238 1 18 22 [2204959],
  lm8M 7 1898746 1 18 26 [45134446],
  lm8M 7 2097259 1 19 26 [58721176],
  lm8M 7 2062360 1 19 27 [98407301],
  lm8M 7 2250663 1 19 23 [5258773],
  lm8M 8 2063262 1 19 28 [208268332],
  lm8M 8 2277272 1 20 28 [184565083],
  lm8M 8 2266347 1 20 29 [315006993],
  lm8M 8 2284621 1 20 29 [503391285],
  lm8M 8 2257172 1 20 28 [141425503],
  lm8M 8 1694403 1 18 30 [543193064],
  lm8M 8 3159091 1 22 31 [1468740695],
  lm8M 8 246849 1 11 31 [1470028968],
  lm8M 8 1874527 1 19 27 [88135859],
  lm8M 8 727360 1 14 30 [646156896],
  lm8M 8 550401 1 13 31 [1240426552],
  lm8M 8 1490491 1 17 31 [1260428851],
  lm8M 8 687078 1 14 31 [1608459687],
  lm8M 8 843326 1 15 31 [1074333202]]
private def lm8Anc_r32 : DickeSol.RampKick128kAnchor :=
  ⟨32, lm8Sgs_r32, lm8Row_r32⟩
private def lm8Row_r41 : List ℕ :=
  [ 435510, 4263242, 23514891, 42691753, 50407416, 498890174, 8454351636, 50729485491,
    179989257143, 316984305288, 277329001082, 128500158054, 32613631673, 4467781868, 303904534,
    7901341 ]
private def lm8Sgs_r41 : List DickeSol.Rkm128kSeg := [
  lm8M 1 6962653 1 18 9 [256],
  ⟨1, 63468445, 1, 48, []⟩,
  lm8M 2 8301670 1 23 16 [40960],
  ⟨2, 22955707, 1, 37, []⟩]
private def lm8Anc_r41 : DickeSol.RampKick128kAnchor :=
  ⟨41, lm8Sgs_r41, lm8Row_r41⟩
private def lm8Row_r64 : List ℕ :=
  [ 0, 0, 0, 6, 13, 4, 0, 3, 7, 22, 731, 15, 1533, 2734, 24, 857, 1009, 12, 1553, 167, 228, 7889,
    18969, 267, 25790, 17314, 81826, 2045, 87235, 107909, 44527, 488353, 3307, 143211, 3202332,
    475959, 36626, 963553, 2900138, 26326471, 4713582, 13067446, 108205798, 21845692, 11668620,
    6207867, 131455276, 15884622, 214811091, 475839016, 7592950, 194279163, 197597397, 31728358,
    207760215, 607647543, 1250202963, 1268700713, 1160594865, 897638787, 316092531, 253910135,
    80841712441, 911725899142 ]
private def lm8Ch_r64_0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 37170348, 1, 40, []⟩,
  ⟨2, 16544870, 1, 36, []⟩,
  ⟨3, 12672270, 1, 38, []⟩,
  lm8M 4 1530192 1 17 2 [2],
  lm8M 4 1554108 1 17 2 [2],
  lm8M 4 2938157 1 22 2 [2],
  lm8M 4 3075305 1 22 5 [18],
  lm8M 5 2541707 1 22 7 [96],
  lm8M 5 2528236 1 22 9 [421],
  lm8M 5 1263929 1 17 10 [808],
  lm8M 5 1261813 1 17 11 [1376],
  lm8M 6 1122504 1 17 47 [70368744181640],
  lm8M 6 1110792 1 17 47 [70368744182944],
  lm8M 6 1108272 1 17 48 [140737488364836],
  lm8M 6 1143582 1 18 48 [140737488385442],
  lm8M 6 1140523 1 18 48 [140737488393690],
  lm8M 6 1145563 1 18 48 [140737488476845],
  lm8M 7 956022 1 17 17 [95556],
  lm8M 7 1024870 1 18 18 [258698],
  lm8M 7 1038406 1 18 19 [484494],
  lm8M 7 1058428 1 18 45 [17592186664770],
  lm8M 7 1055908 1 18 45 [17592188048050],
  lm8M 7 977090 1 17 21 [1482722],
  lm8M 8 906835 1 18 63 [3096598, 64],
  lm8M 8 955609 1 18 63 [35184379658767, 64],
  lm8M 8 957644 1 18 63 [15188416, 64],
  lm8M 8 872547 1 17 63 [8504768, 64],
  lm8M 8 923452 1 18 53 [4503599649110480],
  lm8M 8 1010558 1 18 63 [4503599667537258, 64],
  lm8M 9 893383 1 18 63 [78945378, 64],
  lm8M 9 787613 1 17 63 [9007199341443378, 64],
  lm8M 9 932128 1 18 63 [120076196, 64],
  lm8M 9 898135 1 18 63 [9007199665798963, 64],
  lm8M 9 1006410 1 19 30 [682042907],
  lm8M 9 810979 1 17 63 [690124419, 64],
  lm8M 10 866197 1 18 63 [1563622520, 64],
  lm8M 10 910357 1 18 63 [2431494764, 64],
  lm8M 10 914452 1 19 33 [5387401716],
  lm8M 10 713524 1 17 63 [36028801542561988, 64],
  lm8M 10 855436 1 18 63 [9223673032, 64],
  lm8M 10 931395 1 19 63 [31910337544, 64],
  lm8M 11 1358601 1 22 63 [57472270120, 64],
  lm8M 11 1573475 1 23 63 [73284894272, 65],
  lm8M 11 1604627 1 23 39 [508440961817],
  lm8M 12 1324663 1 22 64 [979746273949, 144],
  lm8M 12 1423431 1 23 61 [1388891606235, 16]]
private def lm8Vec_r64_0 : List ℤ :=
  [ Int.negSucc 7586467218, Int.negSucc 29926911662, Int.negSucc 40944206133,
    Int.ofNat 41351727826, Int.negSucc 1751465084, Int.negSucc 22995999658, Int.ofNat 467297965,
    Int.ofNat 15166611233, Int.ofNat 52900436676, Int.ofNat 12959861961, Int.negSucc 22963244772,
    Int.ofNat 14807920224, Int.ofNat 195038434296, Int.ofNat 198589039217,
    Int.ofNat 326226307570, Int.ofNat 492764239513, Int.ofNat 749678802001,
    Int.ofNat 518967989804, Int.negSucc 100602242434, Int.ofNat 176724965122,
    Int.ofNat 402567412782, Int.negSucc 2006349164294, Int.negSucc 4026058605938,
    Int.negSucc 3993964718355, Int.negSucc 5298039057501, Int.negSucc 3130531536409,
    Int.negSucc 6245015777269, Int.negSucc 8136791981514, Int.negSucc 6322240887178,
    Int.ofNat 5284284292601, Int.ofNat 4574623258605, Int.negSucc 2787445959598,
    Int.ofNat 5233124170161, Int.ofNat 7896957878338, Int.negSucc 22960586599528,
    Int.ofNat 12450747257628, Int.negSucc 2786918669336, Int.negSucc 6726326607265,
    Int.ofNat 428127180233, Int.ofNat 4948618542313, Int.ofNat 13802959481334,
    Int.ofNat 35778706810632, Int.ofNat 169933369151188, Int.ofNat 331738450380662,
    Int.ofNat 451583282462031, Int.ofNat 489233786976653, Int.ofNat 445998565659019,
    Int.ofNat 352168144283376, Int.ofNat 244948430800845, Int.ofNat 151647784626962,
    Int.ofNat 84121402381224, Int.ofNat 41982357153590, Int.ofNat 18892454529626,
    Int.ofNat 7674449557393, Int.ofNat 2808027464700, Int.ofNat 930706203274,
    Int.ofNat 274399651534, Int.ofNat 69079524989, Int.ofNat 14465682808, Int.ofNat 2581449445,
    Int.negSucc 284210806, Int.ofNat 24553261, Int.ofNat 3300638, Int.ofNat 270268,
    Int.ofNat 12581 ]
private def lm8Ch_r64_1 : List DickeSol.Rkm128kSeg := [
  lm8M 12 1554371 1 24 64 [2876324192057, 144],
  lm8M 12 1595503 1 24 64 [14985529424899, 144],
  lm8M 13 1280332 1 22 64 [18417485849165, 128],
  lm8M 13 1280489 1 22 64 [35734137083469, 128],
  lm8M 13 1291584 1 22 64 [74786149500203, 128],
  lm8M 13 1346440 1 23 64 [141259452418742, 128],
  lm8M 14 1271333 1 23 49 [355005587420197],
  lm8M 14 1227006 1 22 38 [146705404712],
  lm8M 14 1247722 1 22 50 [684480796992299],
  lm8M 14 1231998 1 22 50 [569823010326452],
  lm8M 14 1309206 1 23 53 [8300014652515411],
  lm8M 14 1110761 1 22 49 [426954144609181],
  lm8M 15 1097960 1 22 54 [11831599627923325],
  lm8M 15 1215059 1 23 55 [20918394635292933],
  lm8M 15 1295222 1 23 56 [36840291522613803],
  lm8M 15 1072390 1 22 56 [38712158389799926],
  lm8M 15 1131672 1 22 51 [1428167641265067],
  lm8M 15 1131272 1 22 58 [9033810945126547, 2],
  lm8M 15 1154794 1 22 55 [31578053464885266],
  lm8M 15 1053122 1 21 59 [9662949912965692, 6],
  lm8M 15 1079108 1 22 54 [9265309530766336],
  lm8M 16 1005271 1 21 60 [46286710237949839, 8],
  lm8M 16 1051043 1 22 59 [922530737918193, 4],
  lm8M 16 1012153 1 21 61 [3729543701994490, 20],
  lm8M 16 830654 1 20 49 [302786730148916],
  lm8M 16 867864 1 20 62 [36138752300633058, 34],
  lm8M 16 663103 1 18 62 [4114698160520288, 51],
  lm8M 16 995200 1 21 54 [14478403548483630],
  lm8M 16 982660 1 21 47 [70530882104865],
  lm8M 16 1003055 1 21 62 [1148462321720960, 32],
  lm8M 16 1033488 1 22 63 [2314533411439169, 64],
  lm8M 16 1055324 1 22 63 [2470611964351487, 64],
  lm8M 16 439247 1 16 52 [2287198937580044]]
private def lm8Vec_r64_1 : List ℤ :=
  [ Int.negSucc 57368775, Int.ofNat 745747343, Int.negSucc 363656693, Int.ofNat 52584919,
    Int.ofNat 2553303883, Int.ofNat 3739761403, Int.ofNat 2050200040, Int.ofNat 572462944,
    Int.ofNat 1746185777, Int.ofNat 2790943841, Int.negSucc 4721192029, Int.negSucc 27041004982,
    Int.negSucc 3957345146, Int.negSucc 39164048445, Int.ofNat 52289801449,
    Int.negSucc 4934203459, Int.negSucc 29279449254, Int.negSucc 31768708539,
    Int.negSucc 3544254455, Int.negSucc 39413445479, Int.ofNat 12926721991,
    Int.negSucc 15125886093, Int.ofNat 88824555333, Int.ofNat 137730104821,
    Int.ofNat 16342385109, Int.ofNat 160594915109, Int.ofNat 131584835055,
    Int.ofNat 286053135373, Int.negSucc 45228701121, Int.ofNat 295356996940,
    Int.ofNat 328496190247, Int.negSucc 211015242066, Int.ofNat 698823626049,
    Int.ofNat 57515028794, Int.negSucc 378432739387, Int.negSucc 1789506549828,
    Int.negSucc 689898607691, Int.ofNat 191380307784, Int.ofNat 981608134100,
    Int.ofNat 1702979519796, Int.ofNat 5130933126399, Int.ofNat 2171079058600,
    Int.negSucc 3614892687862, Int.negSucc 10402201969585, Int.negSucc 4673937887192,
    Int.ofNat 3415936567267, Int.negSucc 2491559650948, Int.negSucc 11465395074011,
    Int.ofNat 3985552077978, Int.ofNat 14656435524862, Int.ofNat 21813734945108,
    Int.negSucc 2755531218917, Int.ofNat 13938406404595, Int.ofNat 14056934507289,
    Int.ofNat 5632793493954, Int.ofNat 14413890042998, Int.ofNat 24650508338336,
    Int.ofNat 35358209636432, Int.ofNat 35618825630036, Int.ofNat 34067504890503,
    Int.ofNat 29960620966387, Int.ofNat 17778991637841, Int.negSucc 15934558271263,
    Int.ofNat 284326770887762, Int.ofNat 954843390205823 ]
private def lm8St_r64_fin : Lm8St :=
  (16, 64, 354677, lm8Vec_r64_1)
private def lm8Sgs_r64 : List DickeSol.Rkm128kSeg :=
  lm8Ch_r64_0 ++ lm8Ch_r64_1
private def lm8Anc_r64 : DickeSol.RampKick128kAnchor :=
  ⟨64, lm8Sgs_r64, lm8Row_r64⟩
private def lm8Row_r128 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 6, 1, 1, 7, 0, 5, 21, 99, 468, 19, 4, 27, 3, 38,
    20, 358, 340, 429, 418, 977, 15, 127, 1503, 1446, 299, 1433, 232, 13301, 24353, 1222, 5992,
    1023, 9486, 10219, 8864, 1267, 8222, 74113, 304, 62229, 607350, 316164, 154449, 297182,
    517200, 2075368, 5503, 919724, 1470383, 162316, 281018, 77650, 30903, 345448, 4180536,
    383051, 1469015, 561384, 3604218, 7693003, 17419382, 216446, 3041002, 2911406, 27087503,
    10978239, 14571329, 606, 125514, 3945263, 83490585, 61255932, 10311084, 56841166, 1211482,
    41206734, 385497, 23800579, 68688060, 40828918, 198671342, 2091716, 75385604, 318309674,
    4741378, 3401080, 64081171, 122993046, 644058400, 8538924, 260518110, 264836481, 471160391,
    60520042, 180670425, 138099327, 937868306, 207742568, 648146497, 14348641, 182570698,
    249619470, 32455790, 2238252558, 50375445, 1907696974, 4427152, 869191484, 3975917216,
    6420406376, 1338616283, 80371397412, 897239186903 ]
private def lm8Ch_r128_0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23962245, 1, 38, []⟩,
  ⟨2, 9492116, 1, 33, []⟩,
  ⟨3, 7808656, 1, 36, []⟩,
  lm8M 4 6712943 1 38 2 [2],
  ⟨5, 1983673, 1, 24, []⟩,
  ⟨5, 1969629, 1, 24, []⟩,
  lm8M 5 1618139 1 22 3 [4],
  lm8M 6 1436344 1 22 4 [8],
  lm8M 6 1435384 1 22 9 [404],
  lm8M 6 1435182 1 22 10 [664],
  lm8M 7 1297444 1 23 10 [692],
  lm8M 7 1288171 1 23 9 [456],
  lm8M 8 1193482 1 23 17 [118761],
  lm8M 8 1180543 1 23 19 [433260],
  lm8M 9 1100743 1 23 67 [1685701, 1024],
  lm8M 9 1095195 1 23 23 [6303793],
  lm8M 9 1117398 1 23 24 [8473799],
  lm8M 10 1031129 1 23 26 [55880273],
  lm8M 10 1035936 1 23 76 [229904290, 589824],
  lm8M 10 1023712 1 23 79 [832491410, 4194304],
  lm8M 11 960423 1 23 88 [1160094610, 2583691264],
  lm8M 11 963370 1 23 88 [8167038588, 3187671040],
  lm8M 12 846235 1 23 94 [28963568105, 165691785216],
  lm8M 12 841601 1 23 95 [43963665975, 304942678016],
  lm8M 12 857375 1 23 97 [208183450335, 1746776621056],
  lm8M 13 781621 1 23 104 [411441577921, 163689860694016],
  lm8M 13 804491 1 23 104 [1780252555572, 247115775213568],
  lm8M 13 801444 1 23 105 [3362274509353, 299019918114816],
  lm8M 14 755878 1 23 112 [13897755457691, 38738875748712448]]
private def lm8Vec_r128_0 : List ℤ :=
  [ Int.negSucc 1171784690, Int.negSucc 8668854176, Int.ofNat 4518130879, Int.ofNat 8436563938,
    Int.ofNat 27523485826, Int.ofNat 54105570198, Int.ofNat 42235107185, Int.ofNat 112049346054,
    Int.negSucc 13871746089, Int.negSucc 70529322514, Int.ofNat 89727849747,
    Int.ofNat 108911759194, Int.negSucc 99908777240, Int.ofNat 59437139845,
    Int.negSucc 40209882331, Int.ofNat 65885408002, Int.ofNat 63913296457,
    Int.negSucc 34813481385, Int.ofNat 75720961673, Int.ofNat 410767316591,
    Int.negSucc 380359496444, Int.negSucc 993334041735, Int.ofNat 1453512977066,
    Int.negSucc 2087916524527, Int.ofNat 233761432435, Int.negSucc 362702905151,
    Int.ofNat 2520966750893, Int.negSucc 466277152706, Int.negSucc 2717065619873,
    Int.negSucc 3355841041414, Int.ofNat 8248176693715, Int.ofNat 713441582650,
    Int.ofNat 1350768438074, Int.negSucc 2785216184980, Int.negSucc 3173719372290,
    Int.negSucc 3871245519124, Int.ofNat 2083850396875, Int.ofNat 1671449027009,
    Int.negSucc 6806139394648, Int.negSucc 3071889011583, Int.negSucc 3811482046453,
    Int.ofNat 4298969474749, Int.ofNat 3829853613107, Int.ofNat 5180621167415,
    Int.ofNat 23349495595626, Int.ofNat 86105197752406, Int.ofNat 173498282528706,
    Int.ofNat 267723589952437, Int.ofNat 348720360237552, Int.ofNat 400305888853747,
    Int.ofNat 414532207297096, Int.ofNat 392804531262867, Int.ofNat 343858679773078,
    Int.ofNat 279961518190586, Int.ofNat 213060929538191, Int.ofNat 152146741234381,
    Int.ofNat 102255358291546, Int.ofNat 64837480535257, Int.ofNat 38863263530229,
    Int.ofNat 22056167441509, Int.ofNat 11868126847093, Int.ofNat 6061513343850,
    Int.ofNat 2941240997995, Int.ofNat 1356956469020, Int.ofNat 595611450660,
    Int.ofNat 248855122243, Int.ofNat 99013783875, Int.ofNat 37527407131, Int.ofNat 13552096986,
    Int.ofNat 4663763776, Int.ofNat 1529586005, Int.ofNat 478105456, Int.ofNat 142417143,
    Int.ofNat 40423878, Int.ofNat 10931282, Int.ofNat 2815477, Int.ofNat 690451,
    Int.ofNat 161138, Int.ofNat 35754, Int.ofNat 7526, Int.ofNat 1490, Int.ofNat 271,
    Int.ofNat 41, Int.ofNat 3, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm8Ch_r128_1 : List DickeSol.Rkm128kSeg := [
  lm8M 14 751083 1 23 108 [27404796387583, 2430048472662016],
  lm8M 15 715117 1 23 121 [124898161449002, 55844964373889024, 429],
  lm8M 15 715240 1 23 119 [243099189741668, 67399873804107776, 71],
  lm8M 15 730278 1 23 121 [963211784161748, 64754869734473728, 475],
  lm8M 16 682392 1 23 126 [1340598202105910, 31776641956970496, 12992],
  lm8M 16 688769 1 23 129 [7025619987032084, 17439972403445760, 106568],
  lm8M 16 689763 1 23 128 [15414641094279228, 17319507160727552, 62109],
  lm8M 17 667557 1 23 127 [60842533278785737, 61968475341455360, 30389],
  lm8M 17 653520 1 23 128 [11175315266828907, 4047852057657345, 47128],
  lm8M 17 680755 1 23 127 [42822899065254440, 1715238139330567, 17891],
  lm8M 18 616425 1 23 129 [2910109921692090, 48466472552366093, 84958],
  lm8M 18 648573 1 23 128 [38289204926495734, 49258120924364822, 55860],
  lm8M 18 646133 1 23 128 [30313175102383662, 9007199254741099, 36082],
  lm8M 20 1254064 1 32 129 [16010556908774734, 18014398509482873, 129515],
  lm8M 21 1243109 1 32 128 [46255977308149118, 1125899906849166, 50768]]
private def lm8Vec_r128_1 : List ℤ :=
  [ Int.ofNat 1318457308, Int.ofNat 2285860713, Int.ofNat 3979691396, Int.ofNat 6777526093,
    Int.ofNat 4719025120, Int.negSucc 1783150320, Int.negSucc 4173199815, Int.ofNat 364483622,
    Int.ofNat 2552435801, Int.ofNat 7780645395, Int.ofNat 8376677279, Int.ofNat 173586863,
    Int.ofNat 30425329021, Int.negSucc 72320995584, Int.ofNat 9055579919, Int.ofNat 964477194,
    Int.ofNat 11617260951, Int.ofNat 120166508939, Int.ofNat 240590243526,
    Int.ofNat 168410726439, Int.ofNat 338472242945, Int.ofNat 93843239866,
    Int.negSucc 148704083250, Int.negSucc 46752422823, Int.negSucc 505181950383,
    Int.ofNat 98471461878, Int.negSucc 229230234545, Int.ofNat 236534227882,
    Int.negSucc 1010967884062, Int.negSucc 380936514574, Int.ofNat 449544746486,
    Int.ofNat 49978860771, Int.ofNat 33786719534, Int.negSucc 289459185666,
    Int.negSucc 3900916245385, Int.negSucc 6370265331353, Int.ofNat 2804910468990,
    Int.ofNat 3108038071824, Int.ofNat 1360482832072, Int.ofNat 2357728637998,
    Int.ofNat 4274241321053, Int.negSucc 2669208072228, Int.ofNat 1887804688532,
    Int.ofNat 7941977253281, Int.negSucc 9116624666369, Int.ofNat 5808752508614,
    Int.negSucc 1856862154021, Int.negSucc 439764546342, Int.negSucc 498122191068,
    Int.negSucc 8886492872724, Int.ofNat 3938642783977, Int.negSucc 4154612557261,
    Int.ofNat 3335246338788, Int.negSucc 1715186588403, Int.ofNat 8010465654836,
    Int.ofNat 2249910269752, Int.negSucc 6753751244938, Int.negSucc 3917216615860,
    Int.ofNat 7213589174751, Int.ofNat 1977720116491, Int.negSucc 9966541787800,
    Int.ofNat 8953458603192, Int.ofNat 7108733563822, Int.negSucc 6713956102353,
    Int.ofNat 6146323938116, Int.ofNat 6346744378778, Int.ofNat 12398871306911,
    Int.ofNat 4045834164144, Int.ofNat 12305834997819, Int.ofNat 18507996158904,
    Int.ofNat 93400353985884, Int.ofNat 195342598935897, Int.ofNat 297978426797511,
    Int.ofNat 376995246127703, Int.ofNat 417404051572962, Int.ofNat 415985913205232,
    Int.ofNat 379502010077132, Int.ofNat 320428456324811, Int.ofNat 252312336058531,
    Int.ofNat 186312378877770, Int.ofNat 129554449811176, Int.ofNat 85108374867706,
    Int.ofNat 52955298182435, Int.ofNat 31271810161388, Int.ofNat 17555988917552,
    Int.ofNat 9382471388906, Int.ofNat 4778752072645, Int.ofNat 2321754269985,
    Int.ofNat 1076835723085, Int.ofNat 477067176032, Int.ofNat 201984789573,
    Int.ofNat 81758351034, Int.ofNat 31647780147, Int.ofNat 11717563423, Int.ofNat 4150156192,
    Int.ofNat 1406183013, Int.ofNat 455780165, Int.ofNat 141306174, Int.ofNat 41897292,
    Int.ofNat 11877518, Int.ofNat 3218349, Int.ofNat 833084, Int.ofNat 205847, Int.ofNat 48482,
    Int.ofNat 10858, Int.ofNat 2298, Int.negSucc 449, Int.ofNat 77, Int.ofNat 9, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm8Ch_r128_2 : List DickeSol.Rkm128kSeg := [
  lm8M 21 597503 1 23 129 [68366150724197477, 1125899906858936, 114917],
  lm8M 21 589107 1 23 129 [40221497761920282, 63234, 91856],
  lm8M 22 1220994 1 33 128 [63554014294417030, 406754, 51456],
  lm8M 23 1209007 1 33 129 [10480590652796064, 3363380, 125568],
  lm8M 23 577977 1 24 128 [40457237375599177, 7366157, 52928],
  lm8M 23 581753 1 24 128 [36526088478810618, 30439807, 59712],
  lm8M 23 862381 1 28 129 [10537520205368157, 114963468, 100353],
  lm8M 24 828970 1 28 127 [39387165486955081, 404930653, 20480],
  lm8M 24 856727 1 28 129 [49272837671918603, 1619441012, 98816],
  lm8M 25 858755 1 29 129 [8994595259676090, 6518222888, 122896],
  lm8M 25 880557 1 29 129 [38358675067540364, 25840189640, 73856],
  lm8M 26 875007 1 29 123 [6790200627808349, 108180307156, 1184],
  lm8M 26 890860 1 30 129 [71559231220802674, 425212667171, 66560]]
private def lm8Vec_r128_2 : List ℤ :=
  [ Int.ofNat 283890258, Int.negSucc 1331768915, Int.ofNat 899879100, Int.negSucc 1193982141,
    Int.negSucc 644954671, Int.negSucc 2528905212, Int.ofNat 50993029, Int.ofNat 4015251256,
    Int.negSucc 1449910867, Int.ofNat 2655838642, Int.ofNat 12800241162, Int.negSucc 5767736316,
    Int.ofNat 571546294, Int.ofNat 531003017, Int.negSucc 6779536437, Int.ofNat 2536447984,
    Int.negSucc 9937202905, Int.negSucc 27778095240, Int.negSucc 1028270495,
    Int.negSucc 2393909520, Int.ofNat 45460961800, Int.ofNat 117535700108, Int.ofNat 35905269989,
    Int.ofNat 172617304263, Int.negSucc 73144040982, Int.negSucc 43092442610,
    Int.ofNat 79595488109, Int.ofNat 138188213604, Int.ofNat 532550016188,
    Int.negSucc 115773688286, Int.negSucc 1133641270618, Int.ofNat 313041008490,
    Int.ofNat 230968390381, Int.negSucc 1117723355604, Int.ofNat 579879329440,
    Int.ofNat 60029194011, Int.ofNat 701549129489, Int.negSucc 206719068343,
    Int.ofNat 245185240148, Int.ofNat 1312149875695, Int.ofNat 253953452382,
    Int.negSucc 1011521127553, Int.ofNat 777864393764, Int.negSucc 310491318818,
    Int.negSucc 1529160117168, Int.negSucc 1900135991418, Int.negSucc 1514023023309,
    Int.negSucc 1476632638806, Int.ofNat 1136953994359, Int.negSucc 4453083235639,
    Int.ofNat 158977622440, Int.negSucc 780626144205, Int.ofNat 2235044602613,
    Int.ofNat 3775979162019, Int.ofNat 7348190589803, Int.negSucc 833547286625,
    Int.negSucc 7433762426005, Int.negSucc 10809016624737, Int.ofNat 2750477811293,
    Int.ofNat 7986085791664, Int.ofNat 7497622900108, Int.negSucc 1078501176500,
    Int.negSucc 751871853672, Int.ofNat 3259489327707, Int.ofNat 3245927183358,
    Int.ofNat 282138593, Int.negSucc 8728257600006, Int.negSucc 578883647913,
    Int.negSucc 7460823262171, Int.negSucc 7270870040220, Int.ofNat 7823206361994,
    Int.negSucc 12031119948450, Int.negSucc 17589515520056, Int.negSucc 257095082899,
    Int.negSucc 6388057177777, Int.ofNat 1606585483706, Int.ofNat 1135006208010,
    Int.ofNat 545814964655, Int.negSucc 2380073152782, Int.ofNat 2853670803178,
    Int.negSucc 1625117119906, Int.negSucc 11714896534733, Int.negSucc 13630159897384,
    Int.negSucc 7383438354861, Int.negSucc 13218859971483, Int.negSucc 3433537400105,
    Int.negSucc 2835100727038, Int.ofNat 9572798451579, Int.ofNat 751597858245,
    Int.ofNat 18882637326327, Int.ofNat 3977046251489, Int.ofNat 5189660598649,
    Int.ofNat 17013898413813, Int.ofNat 795485247310, Int.ofNat 13070853296633,
    Int.ofNat 29796271124702, Int.ofNat 131596512528503, Int.ofNat 259361588025299,
    Int.ofNat 371018300446202, Int.ofNat 436038721313739, Int.ofNat 444132326133657,
    Int.ofNat 403387152281113, Int.ofNat 332337053540641, Int.ofNat 251130073810277,
    Int.ofNat 175376408468091, Int.ofNat 113793842973376, Int.ofNat 68867115986320,
    Int.ofNat 38981307714357, Int.ofNat 20678068546074, Int.ofNat 10293345454731,
    Int.ofNat 4812326397154, Int.ofNat 2113840385410, Int.ofNat 872335614195,
    Int.ofNat 338095370864, Int.ofNat 122983608085, Int.ofNat 41735003651, Int.ofNat 13877154082,
    Int.ofNat 3355275752, Int.ofNat 623424947, Int.ofNat 86767850, Int.ofNat 9070340,
    Int.ofNat 1438652, Int.negSucc 282640, Int.ofNat 48587, Int.ofNat 10863, Int.ofNat 2559,
    Int.ofNat 434, Int.ofNat 44, Int.ofNat 0 ]
private def lm8Ch_r128_3 : List DickeSol.Rkm128kSeg := [
  lm8M 26 904311 1 30 127 [14877369737985498, 2073580025580, 18688],
  lm8M 27 910302 1 30 129 [53147590978887219, 7557417837126, 81920],
  lm8M 27 921311 1 30 129 [36060881487087145, 33845434322215, 65536],
  lm8M 27 987793 1 31 103 [18022918882812985, 111094433382632],
  lm8M 28 816360 1 29 129 [2907629562838886, 318947052799169, 65536],
  lm8M 28 789601 1 29 106 [41735339001884566, 703756778377585],
  lm8M 29 834295 1 30 129 [69152776153413568, 2639242721100774, 65536],
  lm8M 29 779352 1 29 108 [13901001666740674, 4119339127067394],
  lm8M 29 809577 1 29 129 [31811245595705251, 34936367078977598, 65536],
  lm8M 30 865922 1 30 109 [32635731714489247, 8456628907771701],
  lm8M 30 872985 1 31 129 [63489336889238026, 6800897538220655, 65539],
  lm8M 30 825387 1 30 129 [55740180928886645, 12477481417058715, 65540]]
private def lm8Vec_r128_3 : List ℤ :=
  [ Int.ofNat 38799951, Int.ofNat 217905657, Int.negSucc 229884394, Int.negSucc 218465483,
    Int.ofNat 987516190, Int.negSucc 1641877398, Int.negSucc 1192519899, Int.negSucc 737547039,
    Int.negSucc 3276155485, Int.negSucc 1162729102, Int.negSucc 807116230, Int.ofNat 1743255122,
    Int.ofNat 5895607669, Int.ofNat 2155238443, Int.ofNat 3304105601, Int.ofNat 2805522743,
    Int.negSucc 8511276635, Int.negSucc 2975268846, Int.ofNat 1006127309, Int.ofNat 24472289449,
    Int.negSucc 14605469150, Int.ofNat 14870592515, Int.negSucc 11751309156,
    Int.negSucc 40745515830, Int.negSucc 20024779185, Int.ofNat 31538351283,
    Int.negSucc 16803188953, Int.negSucc 5133011529, Int.negSucc 111646649146,
    Int.negSucc 135509328631, Int.negSucc 111303250166, Int.ofNat 16005428951,
    Int.ofNat 246674793385, Int.ofNat 131632285109, Int.ofNat 143683898799,
    Int.ofNat 187783358727, Int.negSucc 442009438151, Int.negSucc 250350049869,
    Int.negSucc 326746715222, Int.negSucc 110429437807, Int.negSucc 34662271552,
    Int.ofNat 301605747930, Int.ofNat 29858532712, Int.ofNat 138114737830,
    Int.ofNat 670079869654, Int.ofNat 651629970134, Int.negSucc 76635760239,
    Int.ofNat 35023811874, Int.ofNat 67629319997, Int.ofNat 144525811335, Int.ofNat 563528872142,
    Int.ofNat 1437033285762, Int.ofNat 1962136539837, Int.ofNat 1343151434388,
    Int.negSucc 141181335681, Int.negSucc 1745533410677, Int.negSucc 1131206424510,
    Int.negSucc 131405471550, Int.negSucc 2342223821323, Int.negSucc 1669845865762,
    Int.negSucc 2442646230252, Int.negSucc 1355406588211, Int.negSucc 2392818520149,
    Int.ofNat 1784967998511, Int.negSucc 399569956385, Int.negSucc 4353329690579,
    Int.negSucc 3567106753941, Int.negSucc 1349019879826, Int.negSucc 8836540547008,
    Int.ofNat 6028086678031, Int.negSucc 4872480735749, Int.ofNat 3930668237157,
    Int.negSucc 70312559326, Int.negSucc 4938820393714, Int.negSucc 2654746127464,
    Int.ofNat 739552857485, Int.ofNat 1972097274689, Int.ofNat 368116799242,
    Int.ofNat 7356390523234, Int.ofNat 6142432550025, Int.negSucc 3509458889185,
    Int.negSucc 19042193179453, Int.negSucc 10095786940765, Int.negSucc 14135239727445,
    Int.negSucc 14763723293789, Int.negSucc 11816434756821, Int.negSucc 12853231995460,
    Int.negSucc 14509164038629, Int.negSucc 10362201078021, Int.negSucc 2827030242857,
    Int.ofNat 3043831630230, Int.ofNat 11601439866646, Int.ofNat 478429727494,
    Int.negSucc 4132318149744, Int.negSucc 8694602678226, Int.ofNat 2951956025089,
    Int.ofNat 3747288103612, Int.negSucc 12116247924536, Int.ofNat 407008435225,
    Int.negSucc 28515619667534, Int.negSucc 12761577561828, Int.negSucc 8831460442212,
    Int.negSucc 6844582241139, Int.ofNat 13979729985590, Int.ofNat 15702116627946,
    Int.negSucc 11338706487363, Int.ofNat 13728409021733, Int.ofNat 10333046338817,
    Int.ofNat 12426155233062, Int.ofNat 6448979973246, Int.negSucc 30472686243820,
    Int.ofNat 13227211145271, Int.ofNat 11069792130827, Int.ofNat 26592044211393,
    Int.ofNat 13281328046470, Int.ofNat 24833123524705, Int.ofNat 180818199175618,
    Int.ofNat 371883593151818, Int.ofNat 497022925715693, Int.ofNat 509224571169010,
    Int.ofNat 426366568060192, Int.ofNat 300568551586009, Int.ofNat 180876046474210,
    Int.ofNat 93289652196665, Int.ofNat 41073925571488, Int.ofNat 15239627024056,
    Int.ofNat 4635736862321, Int.ofNat 1116347105104, Int.negSucc 85373414729 ]
private def lm8Ch_r128_4 : List DickeSol.Rkm128kSeg := [
  lm8M 31 872189 1 31 129 [69836862258462486, 1408732141485050, 65557],
  lm8M 31 833388 1 30 129 [55097187203505759, 66995816573442152, 65596],
  lm8M 31 788243 1 29 119 [878940452746357, 11260185142577827, 64],
  lm8M 31 728638 1 28 120 [51127956041583371, 41357314070414074, 140],
  lm8M 31 768992 1 29 121 [57583356544147930, 47295313893656017, 348],
  lm8M 31 776332 1 29 121 [29819076408631460, 9017666100557711, 389],
  lm8M 31 858081 1 31 123 [703413279381794, 13626801634791394, 1676],
  lm8M 31 660716 1 27 119 [41706412662872259, 51552819499784239, 85],
  lm8M 32 698869 1 28 123 [51998161597299849, 58573326930459907, 1033],
  lm8M 32 706202 1 28 125 [64248749214899901, 53744507530930686, 5280],
  lm8M 32 492495 1 24 120 [39907148579118943, 63156502357808911, 160],
  lm8M 32 697030 1 28 119 [70082712342577916, 141859554373027, 101]]
private def lm8Vec_r128_4 : List ℤ :=
  [ Int.ofNat 8354894, Int.negSucc 45528990, Int.negSucc 358374563, Int.negSucc 622699644,
    Int.negSucc 583769570, Int.negSucc 664704180, Int.negSucc 567470841, Int.negSucc 342830507,
    Int.negSucc 253578750, Int.negSucc 274434018, Int.negSucc 369515955, Int.negSucc 657612060,
    Int.negSucc 2925771810, Int.negSucc 1670789330, Int.negSucc 3374469143,
    Int.negSucc 1664219507, Int.negSucc 3546710141, Int.negSucc 5992638420,
    Int.negSucc 7110317208, Int.negSucc 4435644660, Int.ofNat 5159793231, Int.ofNat 2410805016,
    Int.negSucc 2218914879, Int.negSucc 1601155495, Int.negSucc 6064039836, Int.ofNat 4791268480,
    Int.ofNat 26924103442, Int.negSucc 7375096061, Int.negSucc 16253875056,
    Int.negSucc 24077254666, Int.negSucc 5308640141, Int.negSucc 11449949571,
    Int.negSucc 49129747916, Int.negSucc 8416409582, Int.ofNat 6407759100, Int.ofNat 29213001916,
    Int.ofNat 82943592430, Int.ofNat 93512399102, Int.negSucc 12674854271,
    Int.negSucc 64922931805, Int.negSucc 114760410216, Int.negSucc 502202145,
    Int.negSucc 59343186870, Int.negSucc 49426631831, Int.ofNat 133304128385,
    Int.ofNat 33121099794, Int.ofNat 142918523118, Int.ofNat 284882174323,
    Int.ofNat 192318774136, Int.ofNat 88270622119, Int.negSucc 122674139646,
    Int.negSucc 477813723771, Int.negSucc 401321766707, Int.negSucc 320423805469,
    Int.negSucc 513955788992, Int.negSucc 214563254340, Int.negSucc 738037921074,
    Int.negSucc 377284801032, Int.negSucc 1318148794591, Int.negSucc 339048446033,
    Int.ofNat 402023283420, Int.ofNat 178253753110, Int.ofNat 1076713995050,
    Int.ofNat 430357588858, Int.ofNat 216589631110, Int.ofNat 840012485698,
    Int.ofNat 455739665602, Int.ofNat 1121669496563, Int.ofNat 3250595130342,
    Int.ofNat 2220805526119, Int.negSucc 2896343242184, Int.negSucc 2475392455237,
    Int.ofNat 2335799500797, Int.negSucc 1206751869656, Int.ofNat 916300813754,
    Int.ofNat 839485443154, Int.ofNat 3917658758325, Int.ofNat 4067894534206,
    Int.ofNat 51212527785, Int.negSucc 201785702512, Int.ofNat 2349698321389,
    Int.ofNat 4507623790004, Int.ofNat 7981266476633, Int.ofNat 9018481735359,
    Int.ofNat 4902109256842, Int.negSucc 1881701550227, Int.negSucc 2874550078413,
    Int.ofNat 414669926074, Int.ofNat 1762814926836, Int.ofNat 5792177471119,
    Int.ofNat 5453777755725, Int.negSucc 4852858172304, Int.negSucc 8054923050302,
    Int.negSucc 9094885335479, Int.negSucc 13969819870898, Int.negSucc 8108422468020,
    Int.negSucc 550030955611, Int.negSucc 7371036966561, Int.negSucc 8915653994819,
    Int.negSucc 20075864202798, Int.negSucc 17846518657776, Int.negSucc 28134473456669,
    Int.negSucc 1431841123920, Int.negSucc 6538920195837, Int.negSucc 11959131237362,
    Int.negSucc 5013657280861, Int.negSucc 2438114399701, Int.ofNat 5550364065980,
    Int.ofNat 17863964102370, Int.ofNat 29370383861513, Int.ofNat 30879366219420,
    Int.ofNat 6759009107667, Int.ofNat 1351499611115, Int.ofNat 5427749301067,
    Int.negSucc 958162044764, Int.negSucc 22539675062669, Int.negSucc 37489569291008,
    Int.negSucc 18312977416656, Int.negSucc 6690076105198, Int.ofNat 22149771475257,
    Int.negSucc 26656245661257, Int.negSucc 12475180312808, Int.ofNat 31911693303323,
    Int.negSucc 22872677726370, Int.negSucc 78690572083921, Int.negSucc 15876191302581,
    Int.ofNat 393466182357161, Int.ofNat 725656218909102, Int.ofNat 549616282584864 ]
private def lm8Ch_r128_5 : List DickeSol.Rkm128kSeg := [
  lm8M 32 721999 1 29 126 [22404617310506739, 15218485629314802, 14190],
  lm8M 32 725357 1 29 127 [31502884890081284, 2304619831107732, 20544],
  lm8M 32 210197 1 18 127 [29972791881651809, 48452885700150946, 17776],
  lm8M 32 512240 1 25 123 [10467891752116357, 22975490277008505, 1033],
  lm8M 32 584834 1 26 121 [18240898375140416, 36626931479229120, 296]]
private def lm8Vec_r128_5 : List ℤ :=
  [ Int.ofNat 5780902, Int.negSucc 30168592, Int.ofNat 25739299, Int.negSucc 322468116,
    Int.negSucc 421958578, Int.negSucc 24331976, Int.ofNat 388464354, Int.negSucc 740296253,
    Int.negSucc 284329511, Int.ofNat 678986583, Int.negSucc 778979009, Int.ofNat 794478343,
    Int.negSucc 742664174, Int.negSucc 1173024508, Int.negSucc 213459833, Int.ofNat 1743917183,
    Int.ofNat 2574852317, Int.ofNat 1074578406, Int.negSucc 1227672166, Int.ofNat 2798855229,
    Int.negSucc 517705342, Int.negSucc 2252936826, Int.negSucc 4637382484,
    Int.negSucc 9965896353, Int.negSucc 21651520896, Int.negSucc 4435422613,
    Int.ofNat 2181582587, Int.negSucc 5202322057, Int.ofNat 1779844302, Int.negSucc 6194614791,
    Int.ofNat 4553247624, Int.ofNat 18925286307, Int.ofNat 18445684506, Int.ofNat 20735435198,
    Int.ofNat 20450911813, Int.negSucc 31264700264, Int.negSucc 3886519961,
    Int.negSucc 11287302930, Int.negSucc 38775534517, Int.negSucc 38039277827,
    Int.ofNat 17295749134, Int.negSucc 37857503706, Int.ofNat 15243116617,
    Int.negSucc 115334319433, Int.ofNat 156057025404, Int.ofNat 34967344359,
    Int.negSucc 77412480338, Int.negSucc 32001184419, Int.ofNat 97401176125,
    Int.ofNat 101091689649, Int.negSucc 94154268228, Int.negSucc 35598319121,
    Int.negSucc 90681908520, Int.negSucc 272238476636, Int.ofNat 17451335159,
    Int.negSucc 249460189505, Int.negSucc 779328689419, Int.negSucc 562286699981,
    Int.ofNat 393002362855, Int.ofNat 545145619760, Int.ofNat 719167908531,
    Int.ofNat 1440615220037, Int.ofNat 74184861955, Int.ofNat 959024051387,
    Int.ofNat 1212595317415, Int.ofNat 402886123749, Int.ofNat 530113183720,
    Int.negSucc 278659293689, Int.ofNat 175794072494, Int.negSucc 587750052171,
    Int.ofNat 2044637477618, Int.ofNat 618912668487, Int.ofNat 1212030952168,
    Int.negSucc 749257343729, Int.negSucc 1898479328349, Int.ofNat 2773627779557,
    Int.negSucc 4173654770371, Int.negSucc 465239267377, Int.negSucc 1743848551527,
    Int.negSucc 1706285734079, Int.negSucc 5204567129878, Int.negSucc 3313344091977,
    Int.negSucc 3817242529130, Int.negSucc 24629938754, Int.negSucc 354281461274,
    Int.ofNat 1986270102780, Int.ofNat 9137319719910, Int.ofNat 7826618372529,
    Int.ofNat 3211089262687, Int.ofNat 7539309557537, Int.ofNat 1100675246415,
    Int.negSucc 6419248644036, Int.negSucc 620885966389, Int.negSucc 4878585249514,
    Int.negSucc 8287827475699, Int.ofNat 6389752476609, Int.ofNat 14095083671676,
    Int.ofNat 1446278060394, Int.ofNat 8682489844462, Int.ofNat 17841236663376,
    Int.ofNat 2177472034294, Int.negSucc 1844203424709, Int.negSucc 8005073067776,
    Int.negSucc 11090224463007, Int.ofNat 25378307142454, Int.negSucc 2922145325745,
    Int.negSucc 16140574885348, Int.negSucc 16273798830613, Int.negSucc 21706230768018,
    Int.ofNat 7779464300134, Int.ofNat 13441371383184, Int.ofNat 11751568455513,
    Int.negSucc 30624637067415, Int.ofNat 14413278953386, Int.ofNat 25458722888552,
    Int.ofNat 3787961529275, Int.ofNat 13511873938530, Int.negSucc 15799351761926,
    Int.ofNat 5696999807432, Int.ofNat 47310175389763, Int.negSucc 7097567591080,
    Int.ofNat 43677192001597, Int.negSucc 2104081520380, Int.ofNat 29482055039118,
    Int.negSucc 63054876089238, Int.ofNat 80127439796393, Int.negSucc 36587106867758,
    Int.ofNat 283498497759882, Int.ofNat 947227105630673 ]
private def lm8St_r128_fin : Lm8St :=
  (32, 128, 1445476, lm8Vec_r128_5)
private def lm8Sgs_r128 : List DickeSol.Rkm128kSeg :=
  lm8Ch_r128_0 ++ (lm8Ch_r128_1 ++ (lm8Ch_r128_2 ++
    (lm8Ch_r128_3 ++ (lm8Ch_r128_4 ++ lm8Ch_r128_5))))
private def lm8Anc_r128 : DickeSol.RampKick128kAnchor :=
  ⟨128, lm8Sgs_r128, lm8Row_r128⟩
private def lm8k128Anchors : List DickeSol.RampKick128kAnchor :=
  [ lm8Anc_r3, lm8Anc_r4, lm8Anc_r5, lm8Anc_r6, lm8Anc_r7, lm8Anc_r8, lm8Anc_r9, lm8Anc_r11,
    lm8Anc_r12, lm8Anc_r14, lm8Anc_r16, lm8Anc_r20, lm8Anc_r24, lm8Anc_r29, lm8Anc_r32,
    lm8Anc_r41, lm8Anc_r64, lm8Anc_r128 ]

private theorem lm8Batch0_ok : lm8AtF
    [ lm8ChkRow 3 lm8Sgs_r3 lm8Row_r3, lm8ChkRow 4 lm8Sgs_r4 lm8Row_r4,
      lm8ChkRow 5 lm8Sgs_r5 lm8Row_r5, lm8ChkRow 6 lm8Sgs_r6 lm8Row_r6,
      lm8ChkRow 7 lm8Sgs_r7 lm8Row_r7, lm8ChkRow 8 lm8Sgs_r8 lm8Row_r8,
      lm8ChkRow 9 lm8Sgs_r9 lm8Row_r9, lm8ChkRow 11 lm8Sgs_r11 lm8Row_r11,
      lm8ChkRow 12 lm8Sgs_r12 lm8Row_r12, lm8ChkRow 14 lm8Sgs_r14 lm8Row_r14,
      lm8ChkRow 16 lm8Sgs_r16 lm8Row_r16, lm8ChkRow 41 lm8Sgs_r41 lm8Row_r41 ]
    = true := by decide +kernel

private theorem lm8Batch1_ok : lm8AtF
    [ lm8ChkRow 20 lm8Sgs_r20 lm8Row_r20, lm8ChkRow 24 lm8Sgs_r24 lm8Row_r24,
      lm8ChkRow 29 lm8Sgs_r29 lm8Row_r29, lm8LenGuard 64 lm8Sgs_r64,
      lm8FinGuard lm8St_r64_fin lm8Row_r64, lm8LenGuard 128 lm8Sgs_r128,
      lm8FinGuard lm8St_r128_fin lm8Row_r128,
      DickeSol.rkm128kCheckTable 8 128 32 true lm8k128VPot lm8k128Anchors,
      lm8ChkCell 4 2 394478990346047 1000000000000000 lm8k128VPot lm8k128Anchors,
      lm8ChkCell 8 2 165617643496611 500000000000000 lm8k128VPot lm8k128Anchors,
      lm8ChkCell 16 4 295827281048903 1000000000000000 lm8k128VPot lm8k128Anchors,
      lm8ChkCell 32 8 273808992547581 1000000000000000 lm8k128VPot lm8k128Anchors,
      lm8ChkCell 64 16 129786223141919 500000000000000 lm8k128VPot lm8k128Anchors,
      lm8ChkCell 128 32 50073041844323 200000000000000 lm8k128VPot lm8k128Anchors ]
    = true := by decide +kernel

private theorem lm8Batch2_ok : lm8AtF
    [ lm8ChkRow 32 lm8Sgs_r32 lm8Row_r32,
      lm8ChkSlice 128 lm8Ch_r128_5 32 128 1378286 lm8Vec_r128_4 lm8St_r128_fin ]
    = true := by decide +kernel

private theorem lm8Batch3_ok :
    lm8ChkSlice 64 lm8Ch_r64_0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (12, 64, 182074, lm8Vec_r64_0) = true := by decide +kernel

private theorem lm8Batch4_ok :
    lm8ChkSlice 64 lm8Ch_r64_1 12 64 182074 lm8Vec_r64_0
      lm8St_r64_fin = true := by decide +kernel

private theorem lm8Batch5_ok :
    lm8ChkSlice 128 lm8Ch_r128_0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (14, 112, 235508, lm8Vec_r128_0) = true := by decide +kernel

private theorem lm8Batch6_ok :
    lm8ChkSlice 128 lm8Ch_r128_1 14 112 235508 lm8Vec_r128_0
      (21, 128, 466621, lm8Vec_r128_1) = true := by decide +kernel

private theorem lm8Batch7_ok :
    lm8ChkSlice 128 lm8Ch_r128_2 21 128 466621 lm8Vec_r128_1
      (26, 128, 785946, lm8Vec_r128_2) = true := by decide +kernel

private theorem lm8Batch8_ok :
    lm8ChkSlice 128 lm8Ch_r128_3 26 128 785946 lm8Vec_r128_2
      (30, 128, 1120367, lm8Vec_r128_3) = true := by decide +kernel

private theorem lm8Batch9_ok :
    lm8ChkSlice 128 lm8Ch_r128_4 30 128 1120367 lm8Vec_r128_3
      (32, 128, 1378286, lm8Vec_r128_4) = true := by decide +kernel

private theorem lm8RowOk_r3 :
    DickeSol.rkm128kEvalRowLo12 8 32 3 lm8Sgs_r3 = lm8Row_r3 :=
  lm8_row_eq (lm8_hd lm8Batch0_ok)
private theorem lm8RowOk_r4 :
    DickeSol.rkm128kEvalRowLo12 8 32 4 lm8Sgs_r4 = lm8Row_r4 :=
  lm8_row_eq (lm8_hd (lm8_tl1 lm8Batch0_ok))
private theorem lm8RowOk_r5 :
    DickeSol.rkm128kEvalRowLo12 8 32 5 lm8Sgs_r5 = lm8Row_r5 :=
  lm8_row_eq (lm8_hd (lm8_tl2 lm8Batch0_ok))
private theorem lm8RowOk_r6 :
    DickeSol.rkm128kEvalRowLo12 8 32 6 lm8Sgs_r6 = lm8Row_r6 :=
  lm8_row_eq (lm8_hd (lm8_tl1 (lm8_tl2 lm8Batch0_ok)))
private theorem lm8RowOk_r7 :
    DickeSol.rkm128kEvalRowLo12 8 32 7 lm8Sgs_r7 = lm8Row_r7 :=
  lm8_row_eq (lm8_hd (lm8_tl4 lm8Batch0_ok))
private theorem lm8RowOk_r8 :
    DickeSol.rkm128kEvalRowLo12 8 32 8 lm8Sgs_r8 = lm8Row_r8 :=
  lm8_row_eq (lm8_hd (lm8_tl1 (lm8_tl4 lm8Batch0_ok)))
private theorem lm8RowOk_r9 :
    DickeSol.rkm128kEvalRowLo12 8 32 9 lm8Sgs_r9 = lm8Row_r9 :=
  lm8_row_eq (lm8_hd (lm8_tl2 (lm8_tl4 lm8Batch0_ok)))
private theorem lm8RowOk_r11 :
    DickeSol.rkm128kEvalRowLo12 8 32 11 lm8Sgs_r11 = lm8Row_r11 :=
  lm8_row_eq (lm8_hd (lm8_tl1 (lm8_tl2 (lm8_tl4 lm8Batch0_ok))))
private theorem lm8RowOk_r12 :
    DickeSol.rkm128kEvalRowLo12 8 32 12 lm8Sgs_r12 = lm8Row_r12 :=
  lm8_row_eq (lm8_hd (lm8_tl4 (lm8_tl4 lm8Batch0_ok)))
private theorem lm8RowOk_r14 :
    DickeSol.rkm128kEvalRowLo12 8 32 14 lm8Sgs_r14 = lm8Row_r14 :=
  lm8_row_eq (lm8_hd (lm8_tl1 (lm8_tl4 (lm8_tl4 lm8Batch0_ok))))
private theorem lm8RowOk_r16 :
    DickeSol.rkm128kEvalRowLo12 8 32 16 lm8Sgs_r16 = lm8Row_r16 :=
  lm8_row_eq (lm8_hd (lm8_tl2 (lm8_tl4 (lm8_tl4 lm8Batch0_ok))))
private theorem lm8RowOk_r41 :
    DickeSol.rkm128kEvalRowLo12 8 32 41 lm8Sgs_r41 = lm8Row_r41 :=
  lm8_row_eq (lm8_hd (lm8_tl1 (lm8_tl2 (lm8_tl4 (lm8_tl4 lm8Batch0_ok)))))
private theorem lm8RowOk_r20 :
    DickeSol.rkm128kEvalRowLo12 8 32 20 lm8Sgs_r20 = lm8Row_r20 :=
  lm8_row_eq (lm8_hd lm8Batch1_ok)
private theorem lm8RowOk_r24 :
    DickeSol.rkm128kEvalRowLo12 8 32 24 lm8Sgs_r24 = lm8Row_r24 :=
  lm8_row_eq (lm8_hd (lm8_tl1 lm8Batch1_ok))
private theorem lm8RowOk_r29 :
    DickeSol.rkm128kEvalRowLo12 8 32 29 lm8Sgs_r29 = lm8Row_r29 :=
  lm8_row_eq (lm8_hd (lm8_tl2 lm8Batch1_ok))
private theorem lm8RowOk_r32 :
    DickeSol.rkm128kEvalRowLo12 8 32 32 lm8Sgs_r32 = lm8Row_r32 :=
  lm8_row_eq (lm8_hd lm8Batch2_ok)

private theorem lm8RowOk_r64 :
    DickeSol.rkm128kEvalRowLo12 8 32 64 lm8Sgs_r64 = lm8Row_r64 := by
  have h1 := lm8_sl_end lm8Batch4_ok
  have h0 : DickeSol.rkm128kRunSegs 8 32 64 lm8Sgs_r64 1 0 1 [Int.ofNat DickeSol.wdScale] =
      lm8St_r64_fin := by unfold lm8Sgs_r64; exact lm8_sl_step lm8Batch3_ok h1
  exact lm8_cert_row lm8Sgs_r64 lm8St_r64_fin lm8Row_r64
    (lm8_hd (lm8_tl1 (lm8_tl2 lm8Batch1_ok))) h0 (lm8_hd (lm8_tl4 lm8Batch1_ok))

private theorem lm8RowOk_r128 :
    DickeSol.rkm128kEvalRowLo12 8 32 128 lm8Sgs_r128 = lm8Row_r128 := by
  have h5 := lm8_sl_end (lm8_hd (lm8_tl1 lm8Batch2_ok))
  have h4 := lm8_sl_step lm8Batch9_ok h5
  have h3 := lm8_sl_step lm8Batch8_ok h4
  have h2 := lm8_sl_step lm8Batch7_ok h3
  have h1 := lm8_sl_step lm8Batch6_ok h2
  have h0 : DickeSol.rkm128kRunSegs 8 32 128 lm8Sgs_r128 1 0 1 [Int.ofNat DickeSol.wdScale] =
      lm8St_r128_fin := by unfold lm8Sgs_r128; exact lm8_sl_step lm8Batch5_ok h1
  exact lm8_cert_row lm8Sgs_r128 lm8St_r128_fin lm8Row_r128
    (lm8_hd (lm8_tl1 (lm8_tl4 lm8Batch1_ok))) h0 (lm8_hd (lm8_tl2 (lm8_tl4 lm8Batch1_ok)))

private theorem lm8AnchorsSound :
    DickeSol.RampKick128kAnchorsSound 8 32 lm8k128Anchors :=
  ⟨lm8RowOk_r3, ⟨lm8RowOk_r4, ⟨lm8RowOk_r5, ⟨lm8RowOk_r6, ⟨lm8RowOk_r7, ⟨lm8RowOk_r8,
    ⟨lm8RowOk_r9, ⟨lm8RowOk_r11, ⟨lm8RowOk_r12, ⟨lm8RowOk_r14, ⟨lm8RowOk_r16, ⟨lm8RowOk_r20,
    ⟨lm8RowOk_r24, ⟨lm8RowOk_r29, ⟨lm8RowOk_r32, ⟨lm8RowOk_r41, ⟨lm8RowOk_r64, ⟨lm8RowOk_r128,
    trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem lm8k128Valid :
    DickeSol.RampKick128kTableValid 8 128 32 true lm8k128VPot lm8k128Anchors :=
  DickeSol.rkm128kCheckTable_sound lm8AnchorsSound
    (lm8_hd (lm8_tl1 (lm8_tl2 (lm8_tl4 lm8Batch1_ok))))

private theorem lm8k128CellChecks {m k : ℕ}
    (h : isLowM8K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (lowM8K128KrotovCertCellLMax m k) lm8k128Anchors = true ∧
      ∃ num den : ℕ, relCostLowM8K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (lm8k128VPot.getD k 0) num den = true := by
  unfold isLowM8K128KrotovCertCell at h
  split_ifs at h with hm8 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm8 hk4; have hc := lm8_hd (lm8_tl4 (lm8_tl4 lm8Batch1_ok))
    exact ⟨lm8ChkCell_l hc, 394478990346047, 1000000000000000, rfl, lm8ChkCell_r hc⟩
  · subst hm8 hk8; have hc := lm8_hd (lm8_tl1 (lm8_tl4 (lm8_tl4 lm8Batch1_ok)))
    exact ⟨lm8ChkCell_l hc, 165617643496611, 500000000000000, rfl, lm8ChkCell_r hc⟩
  · subst hm8 hk16; have hc := lm8_hd (lm8_tl2 (lm8_tl4 (lm8_tl4 lm8Batch1_ok)))
    exact ⟨lm8ChkCell_l hc, 295827281048903, 1000000000000000, rfl, lm8ChkCell_r hc⟩
  · subst hm8 hk32; have hc := lm8_hd (lm8_tl1 (lm8_tl2 (lm8_tl4 (lm8_tl4 lm8Batch1_ok))))
    exact ⟨lm8ChkCell_l hc, 273808992547581, 1000000000000000, rfl, lm8ChkCell_r hc⟩
  · subst hm8 hk64; have hc := lm8_hd (lm8_tl4 (lm8_tl4 (lm8_tl4 lm8Batch1_ok)))
    exact ⟨lm8ChkCell_l hc, 129786223141919, 500000000000000, rfl, lm8ChkCell_r hc⟩
  · subst hm8 hk128; have hc := lm8_hd (lm8_tl1 (lm8_tl4 (lm8_tl4 (lm8_tl4 lm8Batch1_ok))))
    exact ⟨lm8ChkCell_l hc, 50073041844323, 200000000000000, rfl, lm8ChkCell_r hc⟩

private lemma lm8k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma lm8k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma lm8k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private lemma lm8k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b :=
  h ▸ Nat.le_add_right a d

private lemma lm8k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) :
    2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lm8k128_le_of_add h), rfl⟩

private structure Lm8k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ lowM8K128KrotovCertCellLMax m k
  hl1 : 1 ≤ lowM8K128KrotovCertCellLMax m k
  hlm : lowM8K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 32 true lm8k128VPot lm8k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM8K128KrotovCertCellLMax m k)
    lm8k128Anchors = true
  hcost : ∃ num den : ℕ, relCostLowM8K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (lm8k128VPot.getD k 0) num den = true

private lemma lm8k128_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hm8 : 2 ^ 3 = 8)
    (hj : (j + 1) + d1 = 11) (h128 : k + dk = 128)
    (hl2 : 2 + dl2 = lowM8K128KrotovCertCellLMax 8 k)
    (hl1 : 1 + dl1 = lowM8K128KrotovCertCellLMax 8 k)
    (hlm : lowM8K128KrotovCertCellLMax 8 k * 8 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM8K128KrotovCertCellLMax 8 k)
      lm8k128Anchors = true)
    (hcost : ∃ num den : ℕ, relCostLowM8K128KrotovCert 8 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 8 k (lm8k128VPot.getD k 0) num den = true) :
    Lm8k128CellProps 8 k :=
  ⟨hm8 ▸ lm8k128_mem_grid 3 7 rfl, hk ▸ lm8k128_mem_grid j d1 hj, lm8k128_le_of_add h128,
    lm8k128_le_of_add (d := 6) rfl, lm8k128_le_of_add hl2, lm8k128_le_of_add hl1,
    lm8k128_le_of_add hlm, lm8k128Valid, hlmax, hcost⟩

private theorem lm8k128_all_props {m k : ℕ} (h : isLowM8K128KrotovCertCell m k = true) :
    Lm8k128CellProps m k := by
  rcases lm8k128CellChecks h with ⟨hlmax, hcost⟩
  unfold isLowM8K128KrotovCertCell at h
  split_ifs at h with hm8 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm8 hk4; exact lm8k128_mk 2 8 124 0 1 65520 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm8 hk8; exact lm8k128_mk 3 7 120 0 1 65520 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm8 hk16
    exact lm8k128_mk 4 6 112 2 3 65504 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm8 hk32; exact lm8k128_mk 5 5 96 6 7 65472 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm8 hk64
    exact lm8k128_mk 6 4 64 14 15 65408 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm8 hk128
    exact lm8k128_mk 7 3 0 30 31 65280 rfl rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def lowM8K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM8K128KrotovCertQubits n m k)) Var
      (lowM8K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isLowM8K128KrotovCertCell m k = true then
    let p := lm8k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm8k128VPot lm8k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the `6` `m = 8, 4 ≤ k ≤ 128` cells. -/
noncomputable def findAllJohnsonRampKick128kLowM8K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM8K128KrotovCertQubits n m k)) Var
      (lowM8K128KrotovCertQubits n m k) ((n + 1) * m) :=
  lowM8K128KrotovCertCircuitImpl res n m k

private lemma lm8k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isLowM8K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kLowM8K128KrotovCertCircuit res n m k =
      let p := lm8k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm8k128VPot lm8k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kLowM8K128KrotovCertCircuit lowM8K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-`1` recovery of `S` across the `6` `m = 8, 4 ≤ k ≤ 128` cells. -/
theorem lowM8K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isLowM8K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kLowM8K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [lm8k128_targetSets_eq]
  have hp := lm8k128_all_props hcell
  rw [lm8k128_circuit_eq res n hcell, ← lm8k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG lm8k128VPot lm8k128Anchors hp.hk128
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across `m = 8, 4 ≤ k ≤ 128`. -/
theorem lowM8K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isLowM8K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kLowM8K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostLowM8K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := lm8k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG lm8k128VPot
    lm8k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [lm8k128_circuit_eq res n hcell, ← lm8k128_oracle_eq]
    exact hq S (by rwa [lm8k128_targetSets_eq])
  · rw [← lm8k128_targetSets_eq, ← lm8k128_vanilla_eq]; exact hsum

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_0 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM64K128KrCert.isMidM64K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_1 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K128KrCert.isMidM16K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_2 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM128K128KrCert.isHiTailM128K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_3 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt1.mm32k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_4 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt0.hm256k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_5 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt1.mm16k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_6 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt1.lm4k512l248krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_7 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K256KrCert.isMidM16K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_8 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt0.mm32k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_9 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt1.hm256k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_10 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt0.mm16k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_11 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM1024F256KrCert.isHiTailM1024Full256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_12 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM64K256KrCert.isMidM64K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_13 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt2.lm4k512l248krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_14 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt2.mm16k512krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_15 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt2.mm32k512krS2Segs)
    trivial).right

end

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM8K128KrCert
