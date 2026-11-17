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
# Krotov `m = 4` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kLowM4K128KrCert`)

QHL-verified module packaging all `6` `m = 4, 4 ≤ k ≤ 128` cells
(`(4, 4), (4, 8), (4, 16), (4, 32), (4, 64), (4, 128)`) over `22` anchors `r ∈ {3..128}`
(`521` segments, `437,254` F1272 / `447,889` Horner coord-ops at `lTableMax = 62`,
`useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m = 4, k ∈ {4, 8, 16, 32, 64, 128}`, `6` cells). -/
def isLowM4K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 4 then
    if k == 4 then true
    else if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor `L_{\max}(4, k)` across `k ∈ {4..128}`. -/
def lowM4K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 4 then
    if k == 4 then 2
    else if k == 8 then 4
    else if k == 16 then 8
    else if k == 32 then 16
    else if k == 64 then 31
    else if k == 128 then 62
    else 1
  else 1

/-- Total register qubit budget `(lowM4K128KrotovCertCellLMax m k * m) * (n + 1) + k * n`. -/
abbrev lowM4K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (lowM4K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile `c(4, k): ℚ≥0` across `k ∈ {4..128}`. -/
def relCostLowM4K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 4 then
    if k == 4 then NNRat.divNat 98193933431639 200000000000000
    else if k == 8 then NNRat.divNat 219351823974601 500000000000000
    else if k == 16 then NNRat.divNat 100885823733429 250000000000000
    else if k == 32 then NNRat.divNat 189624273570189 500000000000000
    else if k == 64 then NNRat.divNat 72666217410757 200000000000000
    else if k == 128 then NNRat.divNat 352006510827783 1000000000000000
    else 1
  else 1

/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def lowM4K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isLowM4K128KrotovCertCell, relCostLowM4K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kLowM4K128KrCert` cell lies on `groverGrid × groverGrid`. -/
theorem isLowM4K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isLowM4K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isLowM4K128KrotovCertCell at h
  split_ifs at h with hm4 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm4 hk4; rfl
  · subst hm4 hk8; rfl
  · subst hm4 hk16; rfl
  · subst hm4 hk32; rfl
  · subst hm4 hk64; rfl
  · subst hm4 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def lm4P (n : ℕ) : ℤ := Int.ofNat n
private def lm4N (n : ℕ) : ℤ := Int.negSucc n
private def lm4NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem lm4NatEq_eq {x y : ℕ} (h : lm4NatEq x y = true) : x = y := by
  unfold lm4NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def lm4ListNatEq (xs ys : List ℕ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (lm4NatEq x y) (lm4ListNatEq xr yr) false
  | _, _ => false
private theorem lm4ListNatEq_eq {xs ys : List ℕ}
    (h : lm4ListNatEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [lm4ListNatEq] at h
      cases hxy : lm4NatEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (lm4NatEq_eq hxy) (ih h)
private def lm4IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => lm4NatEq m n
  | Int.negSucc m, Int.negSucc n => lm4NatEq m n
  | _, _ => false
private theorem lm4IntEq_eq {a b : ℤ} (h : lm4IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact congrArg Int.ofNat (lm4NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => exact congrArg Int.negSucc (lm4NatEq_eq h)
private def lm4ListIntEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (lm4IntEq x y) (lm4ListIntEq xr yr) false
  | _, _ => false
private theorem lm4ListIntEq_eq {xs ys : List ℤ}
    (h : lm4ListIntEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [lm4ListIntEq] at h
      cases hxy : lm4IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (lm4IntEq_eq hxy) (ih h)
private abbrev Lm4St := ℕ × ℕ × ℕ × List ℤ
private def lm4StEq (a b : Lm4St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    Bool.and (lm4NatEq a1 b1) (Bool.and (lm4NatEq a2 b2)
      (Bool.and (lm4NatEq a3 b3) (lm4ListIntEq av bv)))
private theorem lm4StEq_eq {a b : Lm4St} (h : lm4StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩
  rcases b with ⟨b1, b2, b3, bv⟩
  dsimp only [lm4StEq] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2, h3, hv⟩
  exact Prod.ext (lm4NatEq_eq h1) (Prod.ext (lm4NatEq_eq h2)
    (Prod.ext (lm4NatEq_eq h3) (lm4ListIntEq_eq hv)))
private def lm4AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (lm4AtF rest) false
private theorem lm4_hd {b : Bool} {bs : List Bool} (h : lm4AtF (b :: bs) = true) :
    b = true := by
  unfold lm4AtF at h
  cases b with
  | false => cases h
  | true => rfl
private theorem lm4_tl1 {b : Bool} {s : List Bool} (h : lm4AtF (b :: s) = true) :
    lm4AtF s = true := by
  unfold lm4AtF at h
  cases b with
  | false => cases h
  | true => exact h
private theorem lm4_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : lm4AtF (b1 :: b2 :: bs) = true) : lm4AtF bs = true :=
  lm4_tl1 (lm4_tl1 h)
private theorem lm4_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : lm4AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : lm4AtF bs = true :=
  lm4_tl2 (lm4_tl2 h)
private theorem lm4_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem lm4_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev lm4M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private abbrev lm4ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  lm4ListNatEq (DickeSol.rkm128kEvalRowLo12 4 62 r s) ro
private def lm4InitSt : Lm4St := (1, 0, 1, [Int.ofNat DickeSol.wdScale])
private def lm4RunSt (r : ℕ) (s : List DickeSol.Rkm128kSeg) (st : Lm4St) : Lm4St :=
  match st with
  | (l0, d0, p0, v0) => DickeSol.rkm128kRunSegs 4 62 r s l0 d0 p0 v0
private abbrev lm4ChkSlice (r : ℕ) (s : List DickeSol.Rkm128kSeg)
    (st0 st1 : Lm4St) : Bool :=
  lm4StEq (lm4RunSt r s st0) st1
private theorem lm4_chain (r : ℕ) (s1 s2 : List DickeSol.Rkm128kSeg)
    (st0 st1 st2 : Lm4St)
    (h1 : lm4RunSt r s1 st0 = st1) (h2 : lm4RunSt r s2 st1 = st2) :
    lm4RunSt r (s1 ++ s2) st0 = st2 := by
  rcases st0 with ⟨l0, d0, p0, v0⟩
  rcases st1 with ⟨l1, d1, p1, v1⟩
  unfold lm4RunSt at *
  dsimp only at *
  rw [DickeSol.rkm128kRunSegs_append, h1]
  dsimp only
  exact h2
private abbrev lm4SegsGuard (r : ℕ) (segs : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen segs))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen segs) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private abbrev lm4FinGuard (st : Lm4St) (ro : List ℕ) : Bool :=
  lm4ListNatEq (DickeSol.rkm128kFinalizeState st) ro
private theorem lm4_cert_row (r : ℕ) (segs : List DickeSol.Rkm128kSeg)
    (st : Lm4St) (ro : List ℕ) (hsegs : lm4SegsGuard r segs = true)
    (hrun : lm4RunSt r segs lm4InitSt = st) (hfin : lm4FinGuard st ro = true) :
    DickeSol.rkm128kEvalRowLo12 4 62 r segs = ro := by
  unfold lm4RunSt lm4InitSt at hrun
  dsimp only at hrun
  exact @DickeSol.rkm128kCertRow_of_runSegs 4 62 r segs st ro
    hsegs hrun (lm4ListNatEq_eq hfin)
private abbrev lm4ChkCell (k lm n d : ℕ) (v : List ℕ)
    (a : List DickeSol.RampKick128kAnchor) : Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 4 k (v.getD k 0) n d)

private def lm4SgsR3 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 32197072, 1, 15, []⟩, ⟨1, 32309038, 1, 15, []⟩, ⟨1, 32950095, 1, 15, []⟩,
    ⟨1, 33277441, 1, 15, []⟩, ⟨1, 33182858, 1, 15, []⟩, ⟨1, 33182858, 1, 15, []⟩,
    ⟨1, 33182858, 1, 15, []⟩, ⟨1, 33182858, 1, 15, []⟩, ⟨1, 19469843, 1, 13, []⟩,
    lm4M 1 19469843 1 13 1 [1], ⟨1, 19047952, 1, 13, []⟩, ⟨1, 18966667, 1, 13, []⟩,
    lm4M 1 18572283 1 13 2 [3], lm4M 1 18250393 1 13 2 [2], lm4M 1 17618764 1 13 2 [2],
    lm4M 1 15837047 1 13 2 [2], ⟨1, 1912948, 1, 8, []⟩, ⟨1, 1912948, 1, 8, []⟩,
    ⟨1, 1912716, 1, 8, []⟩, ⟨1, 1912949, 1, 8, []⟩ ]
private def lm4RowR3 : List ℕ :=
  [ 263030, 114744933022, 885252970898 ]
private def lm4SgsR4 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 241450105, 1, 35, []⟩, ⟨1, 18549165, 1, 14, []⟩, lm4M 2 7597536 1 12 1 [1],
    ⟨2, 21601410, 1, 16, []⟩, lm4M 2 10953473 1 13 2 [2], lm4M 2 3460908 1 10 1 [1],
    lm4M 2 5967131 1 12 1 [1], lm4M 2 4981860 1 11 2 [2], lm4M 2 7819002 1 12 2 [3],
    ⟨2, 4589117, 1, 11, []⟩, lm4M 2 5277532 1 11 2 [2], lm4M 2 12033107 1 14 3 [4],
    lm4M 2 4920830 1 11 1 [1], lm4M 2 5094557 1 11 3 [5], lm4M 2 9392538 1 13 3 [4],
    lm4M 2 7893079 1 12 3 [4], lm4M 2 4163604 1 11 2 [2] ]
private def lm4RowR4 : List ℕ :=
  [ 1018962, 4840741, 141153131693, 858840827444 ]
private def lm4SgsR5 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 86520950, 1, 19, []⟩, ⟨1, 98757731, 1, 20, []⟩, lm4M 2 70185422 1 20 2 [2],
    lm4M 2 42361221 1 19 3 [7], lm4M 2 27886964 1 19 3 [6], lm4M 2 20004364 1 19 4 [14],
    lm4M 2 11643123 1 19 1 [1], ⟨2, 11135631, 1, 19, []⟩ ]
private def lm4RowR5 : List ℕ :=
  [ 2223650, 227020, 525993917, 137791922243, 861658463808 ]
private def lm4SgsR6 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 67087336, 1, 19, []⟩, ⟨1, 78257937, 1, 19, []⟩, lm4M 2 71017885 1 21 1 [1],
    lm4M 2 41791346 1 19 3 [5], lm4M 2 41124237 1 19 4 [14], lm4M 2 29513355 1 19 1 [1],
    lm4M 3 15860813 1 19 5 [16], ⟨3, 15245219, 1, 19, []⟩ ]
private def lm4RowR6 : List ℕ :=
  [ 392819, 116387933, 265739521, 896507136, 156713505873, 842002376906 ]
private def lm4SgsR7 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 125225276, 1, 30, []⟩, lm4M 2 113107360 1 36 3 [5], lm4M 3 49480269 1 28 5 [26],
    lm4M 3 35797624 1 24 6 [36], lm4M 3 8168624 1 15 6 [33], lm4M 3 1713130 1 10 1 [1],
    lm4M 3 3810038 1 12 6 [32], ⟨3, 2114757, 1, 11, []⟩ ]
private def lm4RowR7 : List ℕ :=
  [ 362651104, 5355111, 570188304, 3943287335, 365871, 154347319734, 840759798289 ]
private def lm4SgsR8 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 35379030, 1, 19, []⟩, ⟨1, 20531536, 1, 16, []⟩, ⟨1, 20540922, 1, 16, []⟩,
    ⟨1, 20463476, 1, 16, []⟩, ⟨1, 20459664, 1, 16, []⟩, ⟨2, 11899443, 1, 16, []⟩,
    ⟨2, 12410609, 1, 16, []⟩, ⟨2, 12217003, 1, 16, []⟩, ⟨2, 12131540, 1, 16, []⟩,
    ⟨2, 12330040, 1, 16, []⟩, lm4M 2 12238714 1 16 1 [1], ⟨3, 4593574, 1, 13, []⟩,
    lm4M 3 5709990 1 14 2 [3], lm4M 3 5765052 1 14 2 [3], lm4M 3 5952376 1 14 2 [2],
    lm4M 3 6498833 1 14 3 [4], lm4M 3 5633829 1 14 2 [2], lm4M 3 11784727 1 17 4 [8],
    ⟨3, 6839156, 1, 14, []⟩, lm4M 3 6197881 1 14 3 [4], lm4M 3 6245072 1 14 5 [16],
    lm4M 3 7590610 1 15 5 [30], lm4M 3 5833411 1 14 2 [2], ⟨3, 6041439, 1, 14, []⟩,
    lm4M 3 6185202 1 14 4 [9], lm4M 4 4835427 1 14 6 [52], lm4M 4 1196451 1 10 4 [9],
    lm4M 4 6989826 1 15 5 [17], lm4M 4 7304268 1 15 6 [32], lm4M 4 8914482 1 16 7 [117],
    lm4M 4 6913000 1 15 7 [111], lm4M 4 5029230 1 14 6 [60] ]
private def lm4RowR8 : List ℕ :=
  [ 63, 65969, 30219, 32602, 11277253, 83917855, 161483539919, 838421136034 ]
private def lm4SgsR9 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 15509383, 1, 19, []⟩, ⟨1, 15509387, 1, 19, []⟩, ⟨1, 39702997, 1, 19, []⟩,
    ⟨1, 39702997, 1, 19, []⟩, ⟨2, 16373824, 1, 19, []⟩, ⟨2, 16373824, 1, 19, []⟩,
    ⟨2, 27728244, 1, 19, []⟩, lm4M 3 20434758 1 19 2 [3], lm4M 3 28669242 1 19 4 [12],
    lm4M 3 20143759 1 19 5 [17], lm4M 4 19148656 1 19 6 [34], lm4M 4 21538710 1 19 7 [68],
    lm4M 4 12667613 1 19 7 [95], lm4M 4 13930074 1 19 8 [185], lm4M 4 4419758 1 19 4 [14],
    ⟨4, 4551550, 1, 19, []⟩ ]
private def lm4RowR9 : List ℕ :=
  [ 1145819, 1106336, 10650, 56517080, 1599369, 8978903, 486930976, 162957999635, 836485433917 ]
private def lm4SgsR10 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 14793648, 1, 19, []⟩, ⟨1, 14793652, 1, 19, []⟩, ⟨1, 37745726, 1, 19, []⟩,
    ⟨1, 37745726, 1, 19, []⟩, ⟨2, 17790535, 1, 19, []⟩, ⟨2, 17790535, 1, 19, []⟩,
    ⟨2, 28562283, 1, 19, []⟩, lm4M 3 25802985 1 19 3 [6], lm4M 3 30259626 1 20 5 [25],
    lm4M 4 18924281 1 19 6 [32], lm4M 4 19328006 1 19 7 [68], lm4M 4 22246080 1 19 8 [129],
    lm4M 4 12110865 1 19 8 [253], lm4M 4 13936008 1 19 9 [493], lm4M 5 3843763 1 19 6 [63],
    ⟨5, 3997071, 1, 19, []⟩ ]
private def lm4RowR10 : List ℕ :=
  [ 2674319, 8075678, 74686781, 9408265, 6288965, 215501246, 300678908, 354991790, 166525738900,
    832501953587 ]
private def lm4SgsR11 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 46709075, 1, 19, []⟩, ⟨1, 46709075, 1, 19, []⟩, ⟨2, 45568025, 1, 21, []⟩,
    lm4M 3 36259418 1 22 2 [2], lm4M 4 19254970 1 19 4 [11], lm4M 4 22342373 1 19 6 [52],
    lm4M 5 26410716 1 22 8 [189], lm4M 5 19643847 1 19 9 [488], lm4M 5 21334449 1 20 10 [626],
    ⟨5, 5640373, 1, 19, []⟩ ]
private def lm4RowR11 : List ℕ :=
  [ 41514481, 19109241, 4340495, 425738643, 242512081, 35066919, 853436178, 2868291229,
    166294226, 168514217148, 826828868043 ]
private def lm4SgsR12 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 44418369, 1, 19, []⟩, ⟨1, 44418369, 1, 19, []⟩, ⟨2, 46061710, 1, 22, []⟩,
    lm4M 3 37227833 1 22 2 [2], lm4M 4 22508864 1 20 5 [23], lm4M 4 26869897 1 21 7 [106],
    lm4M 5 26877234 1 23 9 [347], lm4M 5 19732156 1 20 10 [990], lm4M 5 21720568 1 21 11 [1030],
    ⟨6, 5162551, 1, 19, []⟩ ]
private def lm4RowR12 : List ℕ :=
  [ 3426398, 59755745, 57830483, 20244942, 271330336, 182492277, 17529291, 1298942512,
    3207646487, 167319754, 169945303375, 824757370456 ]
private def lm4SgsR14 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 37911251, 1, 19, []⟩, ⟨1, 37911251, 1, 19, []⟩, ⟨2, 26900516, 1, 19, []⟩,
    ⟨2, 26900516, 1, 19, []⟩, lm4M 3 32762845 1 22 1 [1], lm4M 5 25337955 1 23 6 [48],
    lm4M 5 19513244 1 21 8 [217], lm4M 6 20539963 1 22 10 [790], lm4M 6 14642195 1 19 11 [1072],
    lm4M 7 13153572 1 19 12 [2082], lm4M 7 8062010 1 19 10 [628], lm4M 7 4891551 1 19 13 [5118],
    lm4M 7 2568078 1 19 7 [106], lm4M 7 816304 1 19 13 [4134], lm4M 7 884359 1 19 5 [31],
    ⟨7, 875184, 1, 19, []⟩ ]
private def lm4RowR14 : List ℕ :=
  [ 4407951, 3547351, 459507, 1554448, 186550343, 56595, 79966023, 346783934, 1425713788,
    1534708553, 898123654, 1158172, 170273936099, 825242255869 ]
private def lm4SgsR15 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 36257070, 1, 19, []⟩, ⟨1, 36257070, 1, 19, []⟩, ⟨2, 25424401, 1, 19, []⟩,
    ⟨2, 25424401, 1, 19, []⟩, lm4M 3 35284571 1 23 3 [6], lm4M 5 30755185 1 26 7 [95],
    lm4M 6 17429816 1 21 9 [469], lm4M 6 20918237 1 23 11 [1787],
    lm4M 6 14196315 1 20 12 [2069], lm4M 7 13387684 1 20 13 [4234], lm4M 7 7604245 1 19 9 [320],
    lm4M 7 5026022 1 19 14 [8254], lm4M 7 3237170 1 19 14 [10191], lm4M 7 566672 1 19 11 [1488],
    lm4M 7 856472 1 19 5 [19], ⟨7, 855041, 1, 19, []⟩ ]
private def lm4RowR15 : List ℕ :=
  [ 1221413, 6490173, 2742387, 497256, 78033026, 46273667, 98697845, 52595227, 3937661,
    251444945, 3072974769, 2737167402, 46799939, 168058479898, 825532557495 ]
private def lm4SgsR16 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 39441961, 1, 23, []⟩, ⟨1, 34452603, 1, 21, []⟩, ⟨2, 9537944, 1, 17, []⟩,
    ⟨2, 11738110, 1, 18, []⟩, ⟨2, 11744678, 1, 18, []⟩, ⟨2, 11744679, 1, 18, []⟩,
    ⟨3, 10298507, 1, 19, []⟩, ⟨3, 9196571, 1, 18, []⟩, lm4M 3 9216246 1 18 2 [2],
    lm4M 4 7710210 1 18 3 [5], lm4M 4 5538448 1 16 4 [12], ⟨4, 5217383, 1, 16, []⟩,
    lm4M 5 4530304 1 16 5 [24], lm4M 5 5250943 1 17 6 [34], lm4M 5 3881957 1 15 5 [26],
    lm4M 5 4673511 1 16 7 [64], lm4M 5 4329825 1 16 5 [20], lm4M 6 3952717 1 16 8 [248],
    lm4M 6 4180641 1 16 8 [160], lm4M 6 4658951 1 17 9 [256], lm4M 6 4411322 1 17 9 [280],
    lm4M 6 4609368 1 17 10 [916], lm4M 7 4619759 1 17 10 [900], lm4M 7 4328247 1 17 4 [8],
    lm4M 7 4350460 1 17 10 [518], lm4M 7 4341564 1 17 12 [3795], lm4M 7 2394016 1 14 10 [548],
    lm4M 7 3247213 1 16 5 [17], lm4M 7 3274245 1 16 13 [4174], lm4M 7 3224523 1 16 13 [4689],
    lm4M 7 3899507 1 17 3 [6], lm4M 7 3151626 1 16 4 [8], lm4M 7 6292411 1 19 14 [12049],
    lm4M 7 3613560 1 16 9 [314], lm4M 8 3560068 1 17 14 [13906], lm4M 8 4236440 1 17 15 [17530],
    lm4M 8 2040985 1 14 15 [17394], lm4M 8 713257 1 11 10 [960], lm4M 8 1362476 1 13 15 [17698],
    lm4M 8 1137614 1 12 15 [16642] ]
private def lm4RowR16 : List ℕ :=
  [ 199, 76891, 19, 4164303, 9668, 2201990, 19930616, 12002, 220058565, 1238551, 1034505102,
    1010642656, 222067536, 6209075, 172425019044, 825053863149 ]
private def lm4SgsR18 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 31633204, 1, 21, []⟩, ⟨1, 31633204, 1, 21, []⟩, ⟨2, 19002892, 1, 21, []⟩,
    ⟨2, 19002892, 1, 21, []⟩, lm4M 3 34100222 1 31 2 [2], lm4M 5 39274205 1 41 8 [226],
    lm4M 6 22311473 1 33 11 [1965], lm4M 7 17050834 1 30 13 [6830],
    lm4M 8 17253304 1 31 15 [22337], lm4M 8 12383928 1 27 16 [65530],
    lm4M 8 6410915 1 21 14 [8326], lm4M 8 5554524 1 20 17 [78174], lm4M 8 2000 1 6 13 [6295],
    lm4M 8 2000 1 6 13 [4143], lm4M 8 2508724 1 15 17 [67359], ⟨9, 2063029, 1, 15, []⟩ ]
private def lm4RowR18 : List ℕ :=
  [ 4109387, 5196115, 20407920, 54930067, 42414576, 62031, 284729162, 20823226, 651151045,
    300115102, 157947045, 2382879572, 3272356376, 1159961870, 1821379684, 49038625,
    173780112572, 815992308092 ]
private def lm4SgsR20 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 30582256, 1, 19, []⟩, ⟨1, 30582256, 1, 19, []⟩, ⟨2, 18030611, 1, 19, []⟩,
    ⟨2, 18030611, 1, 19, []⟩, lm4M 3 33399547 1 25 2 [3], lm4M 5 42145567 1 36 9 [498],
    lm4M 6 29857083 1 31 13 [6741], lm4M 8 15507428 1 24 15 [28317],
    lm4M 9 15168164 1 25 17 [96218], lm4M 9 11482226 1 22 18 [252070],
    lm4M 9 5597189 1 19 14 [12787], lm4M 9 5163759 1 19 14 [13903],
    lm4M 9 92941 1 19 19 [264624], lm4M 9 304500 1 19 19 [277563],
    lm4M 9 1942185 1 19 19 [295000], ⟨9, 2235193, 1, 19, []⟩ ]
private def lm4RowR20 : List ℕ :=
  [ 8786, 4727578, 11242534, 3456071, 669249, 1264032, 103848483, 111253052, 292084529, 1387480,
    234994920, 797232018, 262358354, 138059999, 155386608, 3035101777, 10302353494, 11504186,
    174280666636, 810252345169 ]
private def lm4SgsR23 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 28333382, 1, 19, []⟩, ⟨1, 28333382, 1, 19, []⟩, ⟨2, 15237000, 1, 19, []⟩,
    ⟨2, 15237000, 1, 19, []⟩, lm4M 3 29397214 1 24 1 [1], lm4M 5 42174659 1 38 9 [472],
    lm4M 6 31031617 1 34 14 [13013], lm4M 8 20119614 1 29 17 [106143],
    lm4M 10 20062721 1 32 20 [728439], lm4M 10 10581778 1 23 21 [1966280],
    lm4M 10 5375611 1 19 18 [201666], lm4M 11 5635825 1 19 22 [2520726],
    lm4M 11 2000 1 19 22 [2232649], lm4M 11 36602 1 19 22 [2326379],
    lm4M 11 1537439 1 19 22 [2177804], ⟨11, 1180913, 1, 19, []⟩ ]
private def lm4RowR23 : List ℕ :=
  [ 1799, 2892, 4299, 199291, 23424905, 21841751, 12273190, 4576448, 213337017, 8142546,
    417172521, 240100015, 28099, 986108716, 2269261093, 1220402584, 811387013, 748853372,
    3394606566, 16677453499, 46519822, 166816150743, 806088081841 ]
private def lm4SgsR27 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 20934908, 1, 19, []⟩, ⟨1, 20934908, 1, 19, []⟩, ⟨2, 14048572, 1, 19, []⟩,
    ⟨2, 14048572, 1, 19, []⟩, ⟨3, 21038903, 1, 22, []⟩, lm4M 4 18105791 1 23 2 [3],
    lm4M 6 20360367 1 28 7 [124], lm4M 8 18425527 1 30 12 [3668],
    lm4M 10 27632105 1 43 19 [409173], lm4M 12 18833019 1 36 23 [5802500],
    lm4M 12 13650634 1 30 26 [61567139], lm4M 12 2000 1 19 26 [41251406],
    lm4M 13 5134549 1 19 23 [8129490], ⟨13, 4889766, 1, 19, []⟩ ]
private def lm4RowR27 : List ℕ :=
  [ 352266, 59237, 2468169, 2615221, 270323, 1394947, 5243541, 1157070, 2131987, 14271134,
    6960863, 125167201, 1095286, 39799076, 566122269, 1053039183, 1599956921, 336397830,
    90893801, 617950235, 938832074, 3154559516, 4724818087, 12182028845, 2128657358,
    192543827976, 779859876624 ]
private def lm4SgsR32 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 20114548, 1, 20, []⟩, ⟨1, 19234115, 1, 20, []⟩, ⟨2, 12029053, 1, 20, []⟩,
    ⟨2, 13611574, 1, 21, []⟩, ⟨3, 9203782, 1, 21, []⟩, ⟨3, 9515640, 1, 21, []⟩,
    ⟨4, 8659582, 1, 22, []⟩, ⟨5, 7265147, 1, 22, []⟩, lm4M 5 7750521 1 23 3 [7],
    lm4M 6 6816571 1 23 5 [20], lm4M 7 6007516 1 23 7 [96], lm4M 7 6088913 1 23 9 [346],
    lm4M 8 3182603 1 19 10 [772], lm4M 8 3068455 1 19 31 [1073742956],
    lm4M 9 2833161 1 19 31 [1073745064], lm4M 9 2916176 1 19 31 [1073749120],
    lm4M 9 2232766 1 17 31 [1073748996], lm4M 10 2436727 1 18 13 [5132],
    lm4M 10 2432765 1 18 13 [7232], lm4M 10 2410378 1 18 16 [59099],
    lm4M 11 2422275 1 19 14 [8192], lm4M 11 2102050 1 18 17 [65744],
    lm4M 11 2275072 1 18 18 [131104], lm4M 11 1865845 1 17 12 [2336],
    lm4M 12 1997906 1 18 10 [940], lm4M 12 1981249 1 18 20 [563533],
    lm4M 12 1691101 1 17 19 [264448], lm4M 12 1978319 1 18 21 [1611197],
    lm4M 13 1446221 1 16 7 [72], lm4M 13 1886459 1 18 22 [2097433],
    lm4M 13 1855367 1 18 22 [2122513], lm4M 13 1901530 1 18 23 [4473224],
    lm4M 13 1705058 1 17 23 [4456721], lm4M 14 1719093 1 18 24 [13373089],
    lm4M 14 1970183 1 18 21 [1321697], lm4M 14 1627486 1 17 25 [18406332],
    lm4M 14 1728927 1 18 12 [2209], lm4M 14 1779081 1 18 26 [33556739],
    lm4M 15 1564503 1 17 26 [33554946], lm4M 15 3135444 1 22 26 [33575937],
    lm4M 15 1472856 1 17 28 [142708746], lm4M 15 991520 1 15 28 [209757443],
    lm4M 15 4009449 1 24 16 [47120], lm4M 15 2898129 1 21 29 [285220911],
    lm4M 15 2359384 1 20 29 [302096465], lm4M 15 2871818 1 21 30 [916687140],
    lm4M 15 924908 1 15 29 [304363335], lm4M 15 1878145 1 18 30 [609628600],
    lm4M 16 1884937 1 19 27 [67766084], lm4M 16 1567269 1 18 31 [1201414132],
    lm4M 16 1147880 1 16 31 [1142423344], lm4M 16 893915 1 15 23 [4204556] ]
private def lm4RowR32 : List ℕ :=
  [ 3, 19, 1530, 14, 60422, 2379, 23433, 129504, 3339, 465540, 48624, 1073791, 10944, 1073112,
    1638109, 5802296, 3940755, 5745514, 506606, 51783794, 96676752, 44092227, 138093577,
    356312036, 980410901, 64320826, 123391260, 507070794, 391825921, 52418620, 179074859385,
    818098217665 ]
private def lm4SgsR35 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 18809558, 1, 19, []⟩, ⟨1, 18809404, 1, 19, []⟩, ⟨2, 12956313, 1, 19, []⟩,
    ⟨2, 12956313, 1, 19, []⟩, ⟨3, 19000516, 1, 22, []⟩, lm4M 5 15835688 1 25 1 [1],
    lm4M 7 23247745 1 37 27 [67109692], lm4M 9 20746915 1 39 33 [4295083214],
    lm4M 12 14579843 1 35 36 [34363344025], lm4M 14 15163570 1 38 27 [111793809],
    lm4M 15 11029789 1 32 30 [995151882], lm4M 16 9144459 1 29 32 [3399537954],
    lm4M 17 6050568 1 24 31 [1425105850], lm4M 17 3013510 1 19 34 [13392824229],
    lm4M 17 897135 1 19 34 [10380786074], ⟨17, 2249896, 1, 19, []⟩ ]
private def lm4RowR35 : List ℕ :=
  [ 383710, 1669736, 464544, 286054, 14172204, 217129, 8935298, 1474509, 566909, 37903318,
    3172971, 83752865, 164149228, 181782616, 588573563, 428158497, 51654234, 1496739800,
    41857252, 131143472, 593600238, 9724462855, 563620436, 34014963, 257732930, 2721282909,
    1458459991, 833603812, 175421665, 943030811, 1878756680, 10535088292, 72634551,
    193777896646, 773193331942 ]
private def lm4SgsR43 : List DickeSol.Rkm128kSeg :=
  [ lm4M 1 1238968 1 10 5 [24], lm4M 1 1238968 1 10 5 [20], lm4M 1 1556024 1 10 5 [24],
    lm4M 1 2097021 1 11 5 [20], lm4M 1 6377394 1 15 4 [8], lm4M 1 15631103 1 19 5 [16],
    ⟨1, 15187962, 1, 19, []⟩, ⟨1, 15631103, 1, 19, []⟩, ⟨1, 15631103, 1, 19, []⟩,
    ⟨1, 15631103, 1, 19, []⟩ ]
private def lm4RowR43 : List ℕ :=
  [ 7737161501, 89250610554, 424096106824, 478899171918 ]
private def lm4SgsR64S0 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 15735573, 1, 21, []⟩, ⟨1, 11170345, 1, 19, []⟩, ⟨2, 9300760, 1, 21, []⟩,
    ⟨3, 7404528, 1, 22, []⟩, ⟨3, 8284503, 1, 23, []⟩, ⟨4, 6920670, 1, 24, []⟩,
    ⟨5, 6468998, 1, 25, []⟩, lm4M 6 5536985 1 25 1 [1], ⟨7, 2807341, 1, 21, []⟩,
    lm4M 7 2868950 1 21 4 [12], lm4M 8 2591392 1 21 5 [20], lm4M 8 2614738 1 21 6 [40],
    lm4M 9 2383280 1 21 8 [200], lm4M 9 2383365 1 21 9 [395], lm4M 10 2398765 1 22 11 [1720],
    lm4M 11 2218554 1 22 13 [6972], lm4M 11 2220102 1 22 14 [11337],
    lm4M 12 2087889 1 22 16 [59048], lm4M 13 1908690 1 21 17 [118048],
    lm4M 13 1959215 1 22 18 [158315], lm4M 14 2011568 1 22 20 [852138],
    lm4M 15 1906754 1 22 59 [79164838847378, 4], lm4M 15 1944509 1 23 59 [7980226, 4],
    lm4M 16 1836758 1 22 65 [14696896, 260], lm4M 16 1876548 1 23 65 [59281216, 320],
    lm4M 17 1684625 1 22 65 [85170048, 256], lm4M 18 1718400 1 23 63 [134499968, 64],
    lm4M 19 1657724 1 23 63 [709571208, 64], lm4M 19 1556020 1 22 63 [1083580929, 64],
    lm4M 20 1578670 1 23 64 [3222769601, 128], lm4M 20 1701038 1 23 61 [4503610970083328, 16] ]
private def lm4SgsR64S1 : List DickeSol.Rkm128kSeg :=
  [ lm4M 21 1581712 1 23 64 [18254250049, 144], lm4M 21 1634903 1 23 64 [85899407361, 128],
    lm4M 22 1438808 1 22 64 [137514316299, 128], lm4M 23 1444775 1 23 64 [19348496392, 128],
    lm4M 23 1451989 1 23 64 [555973408, 128], lm4M 24 1413113 1 23 64 [2611527942471, 128],
    lm4M 24 1295629 1 22 64 [4948096187465, 128], lm4M 25 1195823 1 22 64 [4706767043, 128],
    lm4M 26 1301270 1 22 64 [33259006931823, 128], lm4M 26 1486997 1 24 65 [412451090469, 256],
    lm4M 26 1345648 1 23 65 [70440685002788, 256], lm4M 27 1352373 1 23 48 [141568565362767],
    lm4M 27 1359435 1 23 49 [292521632661850], lm4M 28 1337001 1 23 45 [17695274086638],
    lm4M 28 1266594 1 23 51 [1125951497708829], lm4M 28 1359905 1 23 48 [211390190981637],
    lm4M 29 1157676 1 22 53 [4505876585779292], lm4M 29 1226178 1 23 54 [9326128517374288],
    lm4M 29 887031 1 20 50 [564326719091280], lm4M 30 1136868 1 22 54 [9673727113451024] ]
private def lm4SgsR64S2 : List DickeSol.Rkm128kSeg :=
  [ lm4M 30 1150118 1 22 56 [55053807905852385], lm4M 30 1262720 1 23 52 [2251802779189794],
    lm4M 30 1028599 1 21 57 [13104842274, 1], lm4M 30 1135507 1 22 58 [7881308610003281, 2],
    lm4M 31 813149 1 20 53 [4503807933351952], lm4M 31 1002587 1 21 59 [84020307587, 4],
    lm4M 31 970562 1 21 59 [922772539384, 4], lm4M 31 1030819 1 21 59 [1168550929922, 4],
    lm4M 31 956694 1 21 40 [619079915149], lm4M 31 1028634 1 21 55 [18014639036371085],
    lm4M 31 1062426 1 22 45 [18313826296501], lm4M 31 1027110 1 21 42 [2856180012194],
    lm4M 31 1030432 1 21 62 [67486074354132021, 51], lm4M 31 961764 1 21 38 [137473507832],
    lm4M 31 1052595 1 22 54 [9077705848161391], lm4M 31 995707 1 21 54 [9077569133480096],
    lm4M 31 983501 1 21 41 [1101997801942] ]
private abbrev lm4TlR64S1 : List DickeSol.Rkm128kSeg :=
  lm4SgsR64S1 ++ lm4SgsR64S2
private abbrev lm4SgsR64 : List DickeSol.Rkm128kSeg :=
  lm4SgsR64S0 ++ lm4TlR64S1
private def lm4StR64S1V0 : List ℤ :=
  [ lm4N 12960550747, lm4P 112271095034, lm4P 304319875703, lm4P 437352264375,
    lm4P 358608047578, lm4N 12235788524, lm4N 683792979882, lm4N 706496184630,
    lm4N 813505955594, lm4N 717098073733, lm4N 91980324331, lm4P 11253055888, lm4N 296730522335,
    lm4N 109271759451, lm4N 581106156936, lm4N 1010415579782, lm4N 1838838460625,
    lm4N 2714634551607, lm4P 3237533171727, lm4P 10548949865565, lm4P 2128092063020,
    lm4P 8129706799759, lm4P 1283057501033, lm4N 10060355257930, lm4N 11151904663531,
    lm4N 8332937142722, lm4P 3642335917795, lm4P 12367715456030, lm4P 14528787227061,
    lm4P 1203608936272, lm4N 23952771224069, lm4N 6990512068364, lm4N 9569817488838,
    lm4P 18219611931921, lm4P 42854501073683, lm4P 171595330121579, lm4P 320629161692631,
    lm4P 433981292105626, lm4P 476720501269798, lm4P 446343195715782, lm4P 365601376181411,
    lm4P 266109053948889, lm4P 173857679524478, lm4P 102648913324732, lm4P 55025880546551,
    lm4P 26867385649217, lm4P 11974559104340, lm4P 4877899856793, lm4P 1817152667912,
    lm4P 618986410116, lm4P 192641262599, lm4P 54694243124, lm4N 14135133650, lm4P 3315585189,
    lm4P 703303046, lm4P 134314189, lm4P 22970249, lm4P 3494756, lm4P 469115, lm4P 54951,
    lm4N 5519, lm4P 459, lm4P 26, lm4P 0 ]
private def lm4StR64S1V1 : List ℤ :=
  [ lm4P 0 ]
private def lm4StR64S1 : Lm4St :=
  (20, 64, 109375, lm4StR64S1V0 ++ lm4StR64S1V1)
private def lm4StR64S2V0 : List ℤ :=
  [ lm4P 4503395284, lm4P 15571221278, lm4P 19793117565, lm4P 5563735168, lm4P 6634549001,
    lm4P 17188799931, lm4P 31083296773, lm4P 6375400130, lm4P 29147038171, lm4N 6195526040,
    lm4N 64008318619, lm4P 104245331327, lm4N 211042788189, lm4P 111647757609,
    lm4P 439059518625, lm4P 28984586402, lm4N 483721719202, lm4N 456636939573,
    lm4N 474000831659, lm4N 911499092967, lm4N 343609307557, lm4N 495975806671,
    lm4N 832737042962, lm4N 311678604393, lm4N 829333026325, lm4P 306428170869,
    lm4P 422509604574, lm4P 405443940429, lm4P 502078662940, lm4P 1784818323527,
    lm4P 818748469917, lm4P 2132546916790, lm4N 2456774976901, lm4N 380223675781,
    lm4P 3715298738699, lm4N 14573144292339, lm4P 4667463814353, lm4P 125841316777,
    lm4N 18209574714495, lm4P 11509009023309, lm4P 19456750564547, lm4P 4326150143782,
    lm4N 538837557056, lm4N 9224930046470, lm4P 12545159678476, lm4N 38922912064202,
    lm4P 4086932646907, lm4P 10936521522302, lm4N 14427680178363, lm4P 2289964060128,
    lm4P 24381434402130, lm4P 32043681550241, lm4P 53083166144779, lm4N 22911320421699,
    lm4N 29976440269386, lm4P 57799669178478, lm4P 284913670367705, lm4P 496020440295105,
    lm4P 560389822153110, lm4P 470476420404125, lm4P 308132438841440, lm4P 159546660971435,
    lm4P 64557789388149, lm4P 19513275846371 ]
private def lm4StR64S2V1 : List ℤ :=
  [ lm4P 3851998783445 ]
private def lm4StR64S2 : Lm4St :=
  (30, 64, 233113, lm4StR64S2V0 ++ lm4StR64S2V1)
private def lm4StR64S3V0 : List ℤ :=
  [ lm4P 245220118, lm4N 1719660382, lm4N 383293979, lm4P 767210286, lm4N 15909235097,
    lm4N 1376118685, lm4N 5552359551, lm4P 5358424730, lm4N 17829346012, lm4P 5522529907,
    lm4P 26675129772, lm4N 12906705547, lm4P 3092059106, lm4N 21249816610, lm4N 67090898403,
    lm4N 78900848099, lm4N 93060075163, lm4N 19750577016, lm4P 27521032606, lm4N 49757223159,
    lm4P 33928515524, lm4P 330535492826, lm4N 152112625114, lm4P 70991807312, lm4P 246713907028,
    lm4N 220886645906, lm4P 203542924970, lm4P 31661224766, lm4N 505251058023,
    lm4P 516416927473, lm4P 623938213644, lm4P 165824412165, lm4N 411430564108,
    lm4N 472764823633, lm4N 601834838548, lm4N 3323917584230, lm4N 448854487169,
    lm4N 1681001270802, lm4P 1444702520232, lm4P 1669536495902, lm4P 201178863318,
    lm4P 3297392356649, lm4P 4146671810821, lm4P 2690280492819, lm4P 3180231126000,
    lm4P 6200767752180, lm4P 4159602806251, lm4P 3073741000950, lm4P 4634348648223,
    lm4P 4602118878868, lm4N 283408150939, lm4P 5314214584489, lm4P 23727234593990,
    lm4P 2723645225609, lm4P 4472972817142, lm4P 30268086958408, lm4P 22160397425311,
    lm4P 33669685611525, lm4P 16909844160898, lm4P 25090967300186, lm4P 92501432293208,
    lm4P 90054990381413, lm4N 51505676951990, lm4P 439014297135095 ]
private def lm4StR64S3V1 : List ℤ :=
  [ lm4P 885267080690851 ]
private def lm4StR64S3 : Lm4St :=
  (31, 64, 314418, lm4StR64S3V0 ++ lm4StR64S3V1)
private def lm4RowR64 : List ℕ :=
  [ 2, 0, 0, 253, 1, 30, 28, 317, 30, 711, 166, 9, 451, 4501, 6225, 8660, 390, 757, 2475, 1151,
    109253, 23138, 5039, 60867, 48790, 41429, 1002, 255278, 266686, 389298, 27497, 169274,
    223506, 362204, 11048426, 201470, 2825764, 2087164, 2787351, 40472, 10872794, 17194884,
    7237607, 10113868, 38449516, 17302292, 9447881, 21477184, 21179495, 80320, 28240873,
    562981646, 7418241, 20007483, 916157069, 491083200, 1133647708, 285942818, 629556624,
    8556514918, 8109901235, 2652834725, 192733552812, 783697803598 ]
private def lm4SgsR128S0 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 9484341, 1, 20, []⟩, ⟨1, 7669083, 1, 18, []⟩, ⟨2, 7249551, 1, 22, []⟩,
    ⟨3, 5948570, 1, 24, []⟩, ⟨4, 5091566, 1, 25, []⟩, ⟨5, 4469777, 1, 26, []⟩,
    ⟨6, 4549718, 1, 28, []⟩, ⟨7, 4112136, 1, 28, []⟩, ⟨8, 3274563, 1, 27, []⟩,
    ⟨9, 3014899, 1, 27, []⟩, lm4M 11 2579920 1 27 7 [65], lm4M 12 2390814 1 27 10 [778],
    lm4M 13 2216910 1 27 12 [3472], lm4M 14 2094840 1 28 16 [53505],
    lm4M 16 1871475 1 28 64 [562949953658002, 128], lm4M 16 1851048 1 27 64 [1757729, 128],
    lm4M 18 1669811 1 27 24 [13723656], lm4M 19 1561414 1 27 62 [57221575, 32],
    lm4M 20 1577538 1 28 76 [431180586, 524288],
    lm4M 22 1463388 1 28 89 [1679047184, 5369233408],
    lm4M 22 1493629 1 28 87 [16298715684, 1073742080],
    lm4M 24 1394216 1 28 96 [66648357121, 549755944960],
    lm4M 25 1367997 1 28 101 [309271236898, 26285199853568],
    lm4M 26 1313063 1 28 104 [1411654096163, 261134011596800] ]
private def lm4SgsR128S1 : List DickeSol.Rkm128kSeg :=
  [ lm4M 28 1268472 1 28 113 [12116120607872, 23303736633851904, 1],
    lm4M 29 1202689 1 28 117 [37601650467202, 4178693945556992, 25],
    lm4M 30 1214341 1 28 120 [356247815112201, 70063629700956160, 131],
    lm4M 31 1136151 1 28 125 [1238053052291074, 29466911624396800, 7538],
    lm4M 32 1161150 1 29 128 [11682311131693124, 55558872307335168, 33749],
    lm4M 33 1056646 1 28 128 [37229747458786726, 70368744177664, 64636],
    lm4M 34 1091205 1 28 129 [13836842870772864, 60367586411413504, 120997],
    lm4M 36 1031415 1 28 128 [38299314595709202, 52072870691471376, 47077],
    lm4M 37 998860 1 28 127 [514004218486645, 64739253233385594, 25632],
    lm4M 38 1003335 1 28 128 [2392709111275610, 70403928549753104, 50991] ]
private def lm4SgsR128S2 : List DickeSol.Rkm128kSeg :=
  [ lm4M 39 961905 1 28 129 [40598386961961300, 2392537302043718, 121656],
    lm4M 40 904436 1 27 129 [9102316477546880, 38280596832661569, 111881],
    lm4M 41 905840 1 28 129 [149843926434320, 6755399441106085, 123018],
    lm4M 42 915432 1 28 129 [4538783999527520, 13510798882312320, 68604],
    lm4M 43 890742 1 28 129 [38280637733420552, 36028797019514880, 123802],
    lm4M 44 879291 1 28 128 [18155548893534328, 54043195530584205, 51820],
    lm4M 45 875222 1 28 129 [3412885569090624, 6472456, 124766],
    lm4M 46 834349 1 28 129 [21392246675156162, 36028797032137728, 93088],
    lm4M 47 815661 1 28 127 [985184447374310, 331777, 18240] ]
private def lm4SgsR128S3 : List DickeSol.Rkm128kSeg :=
  [ lm4M 48 799916 1 27 128 [39963772534094381, 942906575, 57216],
    lm4M 48 518414 1 23 126 [9007250809201445, 9007199254741008, 10880],
    lm4M 49 429084 1 21 128 [2533281520165460, 9007201670660112, 47104],
    lm4M 49 446676 1 22 129 [36873291218305159, 4294967296, 124928],
    lm4M 50 435680 1 22 129 [2252489164857512, 8657043536, 108544],
    lm4M 50 439252 1 22 129 [10204572839609021, 603979792, 108544],
    lm4M 51 415826 1 21 129 [13512197255250944, 52814676116, 125440],
    lm4M 51 441029 1 22 129 [20412122563937, 68854218800, 83968],
    lm4M 51 433031 1 22 129 [18301371627347313, 141733921288, 114688],
    lm4M 52 429837 1 22 128 [1249062517740721, 412321055776, 32768],
    lm4M 52 410896 1 21 129 [107752496568569, 962072806464, 116736],
    lm4M 52 836320 1 29 125 [4646549317509390, 2748779130896, 4224] ]
private def lm4SgsR128S4 : List DickeSol.Rkm128kSeg :=
  [ lm4M 53 807432 1 28 125 [40741591769457548, 8798527888456, 4224],
    lm4M 54 330119 1 20 128 [9156862088294299, 137477030168, 36864],
    lm4M 54 396392 1 21 99 [760863600274726, 4536123787264],
    lm4M 55 399537 1 21 128 [5110831703517976, 9070976319520, 32768],
    lm4M 55 391084 1 21 84 [722020744822806, 151524357],
    lm4M 55 402992 1 22 128 [5790201104390959, 140737622573068, 32768],
    lm4M 56 370484 1 21 128 [15137165567613868, 1245184, 40960],
    lm4M 56 766514 1 28 128 [3519341341519379, 2199392486412, 32768],
    lm4M 57 762910 1 28 108 [22658776500274269, 2264996505600139],
    lm4M 57 260198 1 19 128 [46303217856546072, 26388446986386, 32768],
    lm4M 58 372744 1 21 128 [428037381292651, 9164570657, 32768],
    lm4M 58 373125 1 21 128 [2885118784998500, 70399413716099, 34816] ]
private def lm4SgsR128S5 : List DickeSol.Rkm128kSeg :=
  [ lm4M 58 359774 1 21 128 [6808193452839511, 231995355392, 34816],
    lm4M 58 396056 1 22 128 [1486613273200641, 70388210993158, 32768],
    lm4M 59 371012 1 21 128 [24331482637095299, 45014206217310843, 32768],
    lm4M 59 347009 1 21 128 [140741784011585, 563783328088065, 32768],
    lm4M 59 387296 1 22 128 [36890823006096005, 689476599809, 32768],
    lm4M 60 378695 1 21 106 [1125917636167689, 564223415550482],
    lm4M 60 387856 1 22 100 [13510833395338889, 8933934629936],
    lm4M 60 383163 1 22 101 [26177593939081359, 17598091624552],
    lm4M 60 382663 1 22 95 [18578091825971241, 416077065280],
    lm4M 61 377888 1 22 109 [45036521255960628, 6827975867648002],
    lm4M 61 378192 1 22 104 [4503655025838592, 180337088934404],
    lm4M 61 374758 1 21 104 [9086367350916657, 247948609064967] ]
private def lm4SgsR128S6 : List DickeSol.Rkm128kSeg :=
  [ lm4M 61 375529 1 22 118 [18433664558983035, 16519982606614778, 62],
    lm4M 61 817771 1 30 116 [1457971025020291, 36314687255610480, 8],
    lm4M 62 617365 1 26 105 [17612209945295, 352238925136192],
    lm4M 62 639532 1 27 111 [10427772505710789, 18014400677937408],
    lm4M 62 631749 1 27 108 [2851055543049232, 2253723959265345],
    lm4M 62 629280 1 27 122 [22061865366495753, 1554718569281682, 512],
    lm4M 62 581136 1 26 121 [70946926296025697, 16053864432641085, 410],
    lm4M 62 604168 1 26 99 [47296596501594177, 6873036095585],
    lm4M 62 567818 1 25 112 [31626515772081742, 36059585768874190],
    lm4M 62 565186 1 25 112 [54088759293410202, 36066189004242953] ]
private def lm4SgsR128S7 : List DickeSol.Rkm128kSeg :=
  [ lm4M 62 562701 1 25 125 [1583577797812762, 1134607957199967, 4337],
    lm4M 62 567259 1 25 109 [4627861123138565, 7351472991764482],
    lm4M 62 533252 1 25 102 [14206853512734469, 35459259064364],
    lm4M 62 532300 1 25 126 [37948651989336021, 204493188722142, 15780],
    lm4M 62 584296 1 26 119 [36734040916868521, 582741436418112, 97],
    lm4M 62 585246 1 26 120 [5639361467449657, 1140193558021632, 128],
    lm4M 62 578834 1 26 121 [12403917444291188, 2251816997756962, 256] ]
private abbrev lm4TlR128S6 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S6 ++ lm4SgsR128S7
private abbrev lm4TlR128S5 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S5 ++ lm4TlR128S6
private abbrev lm4TlR128S4 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S4 ++ lm4TlR128S5
private abbrev lm4TlR128S3 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S3 ++ lm4TlR128S4
private abbrev lm4TlR128S2 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S2 ++ lm4TlR128S3
private abbrev lm4TlR128S1 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S1 ++ lm4TlR128S2
private abbrev lm4SgsR128 : List DickeSol.Rkm128kSeg :=
  lm4SgsR128S0 ++ lm4TlR128S1
private def lm4StR128S1V0 : List ℤ :=
  [ lm4P 11735787213, lm4P 157521958464, lm4P 310489819588, lm4P 464224894328,
    lm4P 260487298019, lm4P 63134462246, lm4P 20340516594, lm4P 36991848189, lm4P 41929542899,
    lm4N 483793758428, lm4N 561249684195, lm4N 135362194661, lm4N 112294228923,
    lm4P 162238205929, lm4P 266356032194, lm4P 397065089568, lm4P 864028654717,
    lm4P 2004334416988, lm4P 507782954208, lm4N 859887978227, lm4P 1010360854200,
    lm4P 3724278883793, lm4N 3621499751909, lm4P 2760957010485, lm4P 136184446736,
    lm4N 2103116042070, lm4N 468845219585, lm4P 1481291575332, lm4P 5065350057801,
    lm4N 548622280140, lm4N 1536606799904, lm4N 2862557333871, lm4N 2878609125365,
    lm4P 1314781853960, lm4P 15271217407258, lm4P 816038838629, lm4P 3153317094145,
    lm4N 1346835983054, lm4N 1505528253696, lm4N 4145197833399, lm4P 10352962580084,
    lm4P 5280969647767, lm4P 54282090276626, lm4P 132889844265150, lm4P 226461828257451,
    lm4P 315366547395617, lm4P 381266616213196, lm4P 412391141847969, lm4P 406102200621698,
    lm4P 368182815993943, lm4P 309696215698510, lm4P 243038534388513, lm4P 178692743176825,
    lm4P 123494585747936, lm4P 80430733382327, lm4P 49469295524213, lm4P 28782526188191,
    lm4P 15863922647689, lm4P 8292466294523, lm4P 4114962445818, lm4P 1939984927317,
    lm4P 869491787049, lm4P 370680272749, lm4P 150358246902 ]
private def lm4StR128S1V1 : List ℤ :=
  [ lm4P 58094891239, lm4P 21262950024, lm4P 7605156319, lm4P 2448907778, lm4P 656939860,
    lm4P 152729451, lm4P 35810747, lm4P 9582453, lm4P 2757149, lm4P 760558, lm4P 191730,
    lm4P 44105, lm4P 9352, lm4P 1836, lm4P 329, lm4P 51, lm4P 4, lm4P 0, lm4P 0, lm4P 0, lm4P 0,
    lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0,
    lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0 ]
private def lm4StR128S1 : Lm4St :=
  (26, 104, 185938, lm4StR128S1V0 ++ lm4StR128S1V1)
private def lm4StR128S2V0 : List ℤ :=
  [ lm4N 25720947608, lm4N 3332191494, lm4P 5614381408, lm4N 5054181358, lm4P 19101571507,
    lm4N 98434827180, lm4N 26871854156, lm4N 10257363077, lm4N 311232040320, lm4N 508373705776,
    lm4N 5329837324, lm4N 84385962247, lm4P 134853333491, lm4P 108304761855, lm4N 72944510711,
    lm4N 244171689084, lm4P 51432355850, lm4N 681227066456, lm4N 419259028515,
    lm4P 340294747566, lm4N 597234025203, lm4N 142064056794, lm4N 276528437960,
    lm4P 44103087781, lm4P 1417589604471, lm4P 650632753577, lm4N 187630755957,
    lm4P 1937618185910, lm4P 5342789495296, lm4P 2171279790516, lm4N 5184797980916,
    lm4N 2020552277357, lm4P 1278017403281, lm4P 1111739953475, lm4P 4768985077297,
    lm4P 805373104589, lm4N 3075573143281, lm4N 622391471304, lm4P 1364692712109,
    lm4P 5236816362472, lm4P 1384769962150, lm4P 929983246650, lm4N 1482079128795,
    lm4N 6136479882192, lm4N 5844828740137, lm4N 12080705426255, lm4N 3516858467136,
    lm4N 7118629400514, lm4N 6618066558557, lm4N 5588701734052, lm4N 5649776023234,
    lm4N 8258773500581, lm4N 13889410365045, lm4N 15564348405449, lm4N 7167325106785,
    lm4N 5577752398689, lm4P 9851448295493, lm4P 6295348898431, lm4P 5864577266195,
    lm4P 9161546130137, lm4N 9998620404270, lm4P 4950189974593, lm4P 23638365536834,
    lm4P 13761079773557 ]
private def lm4StR128S2V1 : List ℤ :=
  [ lm4P 5503484500015, lm4P 9422625428530, lm4P 71777978958757, lm4P 167394096954397,
    lm4P 270756045709469, lm4P 356759602214755, lm4P 408059354127617, lm4P 418342954457103,
    lm4P 391635825307282, lm4P 338792596534021, lm4P 273033485134149, lm4P 206189537301210,
    lm4P 146548977487040, lm4P 98361218418104, lm4P 62508431842260, lm4P 37691804107444,
    lm4P 21602090158587, lm4P 11784125473886, lm4P 6125702422081, lm4P 3037281564545,
    lm4P 1437572792965, lm4P 649779776414, lm4P 281152644464, lm4P 114822727237,
    lm4P 47705185647, lm4P 16349225484, lm4P 4307551006, lm4P 1078249118, lm4P 353861512,
    lm4P 139527321, lm4P 51866554, lm4P 17005043, lm4P 4990732, lm4P 1344307, lm4P 338343,
    lm4P 80351, lm4P 18071, lm4N 3845, lm4P 765, lm4P 137, lm4P 19, lm4P 0, lm4P 0, lm4P 0,
    lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0,
    lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0, lm4P 0 ]
private def lm4StR128S2V2 : List ℤ :=
  [ lm4P 0 ]
private def lm4StR128S2 : Lm4St :=
  (38, 128, 375578, lm4StR128S2V0 ++ (lm4StR128S2V1 ++ lm4StR128S2V2))
private def lm4StR128S3V0 : List ℤ :=
  [ lm4N 2393923642, lm4N 2022704843, lm4P 18253714678, lm4P 1508884013, lm4N 19315688276,
    lm4P 9741149510, lm4P 28794783624, lm4P 2924090290, lm4N 28901780932, lm4P 23644588993,
    lm4P 331458559454, lm4N 9691733215, lm4P 29946282643, lm4P 32955603840, lm4P 102834828362,
    lm4P 258571994425, lm4N 12584373186, lm4P 357618703056, lm4P 114516812223, lm4P 53030438173,
    lm4P 46762375114, lm4N 171232459115, lm4N 402103180144, lm4N 240111234920,
    lm4P 307752734646, lm4N 420718202479, lm4N 1060937493380, lm4P 239362852594,
    lm4N 221124694923, lm4P 834870149, lm4N 689929230043, lm4N 734817031366, lm4N 536396498092,
    lm4P 479521890305, lm4N 1491256441070, lm4N 404612769678, lm4N 2233960419389,
    lm4N 1302568299185, lm4N 3259380029497, lm4P 4252050737013, lm4N 1353436933839,
    lm4N 4614659364692, lm4N 3208441817836, lm4N 12380755344188, lm4P 9745263765006,
    lm4P 3077126512867, lm4P 2260053005741, lm4N 2226919197087, lm4N 330129335226,
    lm4P 2774742495697, lm4P 6961311582493, lm4N 69294745339, lm4P 9483303667728,
    lm4P 3808229700081, lm4N 16150728964419, lm4N 2748220748412, lm4P 275145602358,
    lm4N 2853535156732, lm4P 9572711352094, lm4P 14623507042510, lm4P 4603138871240,
    lm4N 6547534936285, lm4N 2738386713931, lm4P 7728694897224 ]
private def lm4StR128S3V1 : List ℤ :=
  [ lm4P 1561365584749, lm4N 9954400518672, lm4N 6176392613252, lm4P 4808496797759,
    lm4P 3904092092512, lm4N 4413881547966, lm4N 20329249956378, lm4N 13172015495322,
    lm4P 4945749264186, lm4P 9386814083267, lm4P 991843251554, lm4N 12241827920746,
    lm4N 816479841314, lm4P 21123971918250, lm4P 13158270167513, lm4P 11294588958066,
    lm4P 12110376367276, lm4N 2082952035762, lm4N 26506818236053, lm4N 32573168285270,
    lm4P 6240216075076, lm4P 93441318297341, lm4P 208596144376904, lm4P 320039915740015,
    lm4P 399683745793330, lm4P 432462293993725, lm4P 418326701231278, lm4P 368465827017366,
    lm4P 299039435297518, lm4P 225440055839832, lm4P 158792097185915, lm4P 104950919040159,
    lm4P 65299853759668, lm4P 38343679056003, lm4P 21290379852650, lm4P 11195624052200,
    lm4P 5581960352682, lm4P 2640718152743, lm4P 1185744154589, lm4P 505294120524,
    lm4P 204253628736, lm4P 78260228475, lm4P 28397299285, lm4P 9750268346, lm4P 3166139892,
    lm4P 968515384, lm4P 289779558, lm4P 67476644, lm4P 12013437, lm4P 2151785, lm4P 491056,
    lm4P 116541, lm4P 23428, lm4P 3736, lm4N 467, lm4P 44, lm4N 1, lm4P 0, lm4P 0, lm4P 0,
    lm4P 0, lm4P 0, lm4P 0, lm4P 0 ]
private def lm4StR128S3V2 : List ℤ :=
  [ lm4P 0 ]
private def lm4StR128S3 : Lm4St :=
  (47, 128, 584877, lm4StR128S3V0 ++ (lm4StR128S3V1 ++ lm4StR128S3V2))
private def lm4StR128S4V0 : List ℤ :=
  [ lm4N 753192577, lm4N 3881754755, lm4N 3558114529, lm4P 4057213804, lm4P 8382515932,
    lm4P 12651697858, lm4P 15427418753, lm4P 17288036975, lm4N 14515292200, lm4N 8842424429,
    lm4N 8409563824, lm4N 22602859496, lm4N 10715028838, lm4N 21681944006, lm4P 17687457713,
    lm4P 67814148074, lm4P 189844588765, lm4P 181586557256, lm4P 229215008244,
    lm4P 167541197278, lm4N 22543121338, lm4N 379195820810, lm4N 342858920103,
    lm4P 157080966470, lm4P 169410821498, lm4N 12159661320, lm4P 272865720633,
    lm4N 196093425026, lm4P 215711043892, lm4N 104299720984, lm4N 255891324768,
    lm4N 337147131968, lm4N 191377762084, lm4P 111790926184, lm4P 894603035169,
    lm4P 904280777275, lm4P 901644105828, lm4N 463966069468, lm4N 723924838062,
    lm4P 1326607029622, lm4N 1099231305508, lm4P 388759346828, lm4N 982706623597,
    lm4N 471423394330, lm4P 123591632490, lm4N 1081165443635, lm4N 402629283342,
    lm4N 458648001980, lm4N 391196287611, lm4P 2693457604620, lm4P 3271283482785,
    lm4P 5340152446523, lm4P 3278552810961, lm4P 3683326928379, lm4P 923536667714,
    lm4P 11374631613442, lm4P 12988046149386, lm4N 2003237567022, lm4P 14422871153951,
    lm4P 9687279694861, lm4N 1664003191682, lm4N 6524042483458, lm4N 9126586253766,
    lm4N 1685580428907 ]
private def lm4StR128S4V1 : List ℤ :=
  [ lm4N 5281332944903, lm4N 248234933550, lm4P 4068200431905, lm4P 2007150059209,
    lm4P 2179501640444, lm4N 293782237246, lm4N 4494845521881, lm4P 3361487258762,
    lm4P 8133994283882, lm4P 14197984677244, lm4P 1235862823033, lm4P 7680384129414,
    lm4P 1723796536464, lm4P 11165636136551, lm4P 4239113888927, lm4P 5364824057904,
    lm4P 7731133432135, lm4P 16045295963409, lm4P 4333766696927, lm4P 9747745835217,
    lm4P 12329440045581, lm4P 15481584113080, lm4P 6150629681658, lm4P 12102919985548,
    lm4P 22791472145541, lm4N 5468641476135, lm4P 18931672405804, lm4P 11699091706133,
    lm4P 33197616832260, lm4P 50666596881046, lm4P 15249120761626, lm4N 20865200617327,
    lm4N 429183561311, lm4P 16205210676564, lm4P 29176855178478, lm4P 138153387604063,
    lm4P 272514005747479, lm4P 385712458661738, lm4P 446280118169756, lm4P 445744940439910,
    lm4P 395752913969262, lm4P 317715152765348, lm4P 233165218300603, lm4P 157660593666073,
    lm4P 98721952611705, lm4P 57417173545620, lm4P 31112098304390, lm4P 15756813160249,
    lm4P 7461446639664, lm4P 3286874228181, lm4P 1334449248864, lm4P 494761437352,
    lm4P 166735769306, lm4P 51190294454, lm4P 14455148639, lm4N 3807951344, lm4P 948765321,
    lm4P 224097050, lm4P 50281013, lm4P 7996342, lm4N 908503, lm4P 100658, lm4P 10422, lm4P 669 ]
private def lm4StR128S4V2 : List ℤ :=
  [ lm4P 17 ]
private def lm4StR128S4 : Lm4St :=
  (52, 128, 802293, lm4StR128S4V0 ++ (lm4StR128S4V1 ++ lm4StR128S4V2))
private def lm4StR128S5V0 : List ℤ :=
  [ lm4P 1401669, lm4P 1229945144, lm4P 1326256571, lm4N 4379612928, lm4P 3837021727,
    lm4P 2664193589, lm4N 3225975916, lm4N 14185060005, lm4P 1121027472, lm4P 9524696621,
    lm4N 6995149273, lm4P 16108734379, lm4N 22196862773, lm4N 19893289557, lm4P 3221625254,
    lm4N 1452235880, lm4N 693391006, lm4N 28604298279, lm4N 2062112968, lm4P 18159098527,
    lm4N 5833420636, lm4N 50403284277, lm4N 14379482267, lm4N 170345330396, lm4N 185109154306,
    lm4N 66886054617, lm4N 254418927973, lm4N 44796000573, lm4N 68194036888, lm4N 197108311657,
    lm4P 176818829919, lm4P 539305562218, lm4P 319566625747, lm4P 229904805997, lm4N 2029369256,
    lm4P 485785660288, lm4N 706499183949, lm4P 650021214383, lm4P 137190074657,
    lm4P 98062799272, lm4P 579169680339, lm4N 538015858170, lm4P 472072325285,
    lm4N 1183633664573, lm4P 180619522246, lm4N 1100806286413, lm4P 176032374997,
    lm4N 767954479601, lm4N 1613960195826, lm4P 107103919767, lm4P 2123345600044,
    lm4P 521154132119, lm4P 2517807713223, lm4P 1799407285422, lm4N 2492144549107,
    lm4P 4099411628606, lm4N 1027091962571, lm4N 2430671328433, lm4P 3304465412860,
    lm4N 5076381929534, lm4N 4452889376648, lm4N 1382861856971, lm4N 5924667249683,
    lm4N 2493535263623 ]
private def lm4StR128S5V1 : List ℤ :=
  [ lm4N 5834079775950, lm4N 11779317802249, lm4P 1001358366043, lm4P 15945288641439,
    lm4N 1646597533320, lm4P 14037599895999, lm4P 1591035313672, lm4N 3726331521806,
    lm4P 6908631102824, lm4P 12164057340473, lm4N 691135110715, lm4N 6030116785911,
    lm4P 13263294257174, lm4N 7029426604396, lm4N 8244381686710, lm4P 5100867986525,
    lm4P 3039186767315, lm4P 1120540683101, lm4P 3165276002020, lm4P 1687991391717,
    lm4P 5019801415564, lm4N 2949661529796, lm4P 1770546281745, lm4P 14941089404577,
    lm4P 3542056602677, lm4P 6195146357569, lm4N 4215533459212, lm4P 1009495297355,
    lm4P 7321088877153, lm4P 8536527369917, lm4P 14651244962372, lm4P 5945057775029,
    lm4P 8204763060487, lm4P 10132747084739, lm4P 14967557345888, lm4P 30798070088851,
    lm4P 25134058912131, lm4P 7564710662184, lm4N 28657828665058, lm4P 44426510202844,
    lm4P 32883088280889, lm4P 53366190338589, lm4P 2054936084210, lm4N 20444437602446,
    lm4N 39584677121115, lm4N 7949517253200, lm4P 109497715561303, lm4P 274207472446370,
    lm4P 415697884624258, lm4P 482781811693926, lm4P 465252818341255, lm4P 386226466518799,
    lm4P 281959504850831, lm4P 183234896012170, lm4P 106705005239017, lm4P 55866989573364,
    lm4P 26324372353001, lm4P 11133246114388, lm4P 4190015194611, lm4N 1381916141977,
    lm4P 391959829651, lm4P 92937143058, lm4P 17888976342, lm4N 1215093993 ]
private def lm4StR128S5V2 : List ℤ :=
  [ lm4P 46679390 ]
private def lm4StR128S5 : Lm4St :=
  (58, 128, 1027131, lm4StR128S5V0 ++ (lm4StR128S5V1 ++ lm4StR128S5V2))
private def lm4StR128S6V0 : List ℤ :=
  [ lm4N 239683967, lm4N 414903531, lm4P 218312316, lm4N 1153776914, lm4N 1944730628,
    lm4N 3688152424, lm4N 2869201069, lm4N 487472076, lm4N 7975557590, lm4N 9480789411,
    lm4N 649751348, lm4P 8742532597, lm4N 6645519157, lm4N 15949658019, lm4N 2079575078,
    lm4P 718052670, lm4N 6363144724, lm4N 4796498555, lm4N 23448581631, lm4N 15518856139,
    lm4N 25262275282, lm4N 70826810321, lm4N 15392273113, lm4N 26184092053, lm4N 34802458609,
    lm4N 11926230111, lm4N 12946331125, lm4N 49092372611, lm4N 31584116045, lm4N 55365469034,
    lm4N 72149016328, lm4P 28427828718, lm4P 212331017039, lm4P 466034266972, lm4P 440466338840,
    lm4N 49401184153, lm4N 166180844365, lm4P 483397348177, lm4N 168443373686, lm4P 9911334067,
    lm4P 258565926959, lm4N 72565526861, lm4N 30266637782, lm4N 31659175061, lm4N 752249232763,
    lm4N 287351469129, lm4P 399920778471, lm4N 604388087921, lm4N 303813491388,
    lm4N 697796724717, lm4N 1217190329810, lm4N 1100992838734, lm4N 1020602345188,
    lm4P 78811806494, lm4P 849768062813, lm4N 427018874541, lm4P 209172523176,
    lm4P 278758488089, lm4P 299571536804, lm4P 1581243349470, lm4P 3582570393840,
    lm4P 5646112676105, lm4P 4819300726565, lm4P 1091755157798 ]
private def lm4StR128S6V1 : List ℤ :=
  [ lm4N 1102727115817, lm4P 3839823472834, lm4N 1795922601657, lm4N 4140841874680,
    lm4P 220833635651, lm4P 1445309091920, lm4P 810338712897, lm4N 3075014559556,
    lm4P 3570305712000, lm4N 4805826488663, lm4P 947417146092, lm4N 6633389660350,
    lm4N 26433919752252, lm4N 4624061550304, lm4N 2939209041277, lm4P 1053272151974,
    lm4N 4777716320585, lm4N 13145704785298, lm4N 5034007650237, lm4N 838487877156,
    lm4N 8885954225376, lm4N 8843513168742, lm4N 6159227112092, lm4N 6287491662403,
    lm4N 5548758951849, lm4P 5768072504032, lm4N 1018429954956, lm4N 5214148378689,
    lm4P 8381139652590, lm4N 4737229001540, lm4P 28758271219003, lm4N 3289542052469,
    lm4P 1260926977666, lm4P 2114497672208, lm4P 2621625493315, lm4N 2545348670092,
    lm4P 4412630093027, lm4N 1826799154467, lm4N 9753022671456, lm4P 21770991396393,
    lm4N 8741765713685, lm4P 48215644831936, lm4N 25327881707225, lm4N 43830378870909,
    lm4N 12881464853224, lm4N 4336888768844, lm4N 13487190631051, lm4N 29864605257841,
    lm4N 25708593034983, lm4N 9046179428501, lm4N 33381037575982, lm4N 95159821920565,
    lm4N 102047028310051, lm4P 16757916541864, lm4P 233746876611723, lm4P 433779024661548,
    lm4P 527672761062115, lm4P 490523875224969, lm4P 368749443192983, lm4P 231452188799657,
    lm4P 121424660905171, lm4P 51759032979662, lm4P 17327601864671, lm4P 4256083543511 ]
private def lm4StR128S6V2 : List ℤ :=
  [ lm4P 652522826430 ]
private def lm4StR128S6 : Lm4St :=
  (61, 128, 1231154, lm4StR128S6V0 ++ (lm4StR128S6V1 ++ lm4StR128S6V2))
private def lm4StR128S7V0 : List ℤ :=
  [ lm4P 15640931, lm4P 98170563, lm4P 43609841, lm4P 395146637, lm4P 23442905, lm4P 490382816,
    lm4P 2629822793, lm4P 3412136566, lm4P 455355555, lm4N 2096597983, lm4N 2266338900,
    lm4P 1022494973, lm4P 745653642, lm4N 4263486044, lm4P 224925499, lm4P 4017148262,
    lm4P 13167609302, lm4N 8074500860, lm4N 520317710, lm4P 4598219353, lm4P 1513723441,
    lm4N 1690453619, lm4P 4300415891, lm4P 5505252232, lm4P 14651988005, lm4P 5681048012,
    lm4P 7195268658, lm4P 418730133, lm4N 11028129790, lm4N 22015464799, lm4N 26417028339,
    lm4N 12541600731, lm4N 62768933990, lm4N 98750628586, lm4N 60322657242, lm4N 72215099944,
    lm4N 47158623272, lm4P 25763913918, lm4N 53571119808, lm4N 139671395955, lm4N 10879177711,
    lm4P 45114706186, lm4P 34967265035, lm4N 284968547079, lm4P 82660001551, lm4N 161166894079,
    lm4N 154272556546, lm4N 288637325499, lm4P 194780624739, lm4P 308313904173,
    lm4P 12937827033, lm4P 759193741830, lm4P 821206424740, lm4P 546962366241,
    lm4P 158960528366, lm4P 340769988497, lm4P 175876634399, lm4N 405469496401,
    lm4N 267949368907, lm4P 405740059263, lm4P 424209455870, lm4N 360055989423,
    lm4N 530261281726, lm4N 240289126686 ]
private def lm4StR128S7V1 : List ℤ :=
  [ lm4N 543868250215, lm4P 415750917283, lm4N 232622250570, lm4N 1503090515301,
    lm4N 1264399495370, lm4N 867530136348, lm4N 29158913745, lm4N 43006106541,
    lm4N 2148663174542, lm4N 1926424847879, lm4N 2575051372301, lm4N 767596462956,
    lm4P 3684419171989, lm4P 4435814725611, lm4P 7400162005363, lm4P 4721238231987,
    lm4P 2645929747911, lm4P 2081095329296, lm4P 1193609233851, lm4P 4206090169431,
    lm4P 9656091335763, lm4P 1037423527623, lm4N 13525145631018, lm4N 22299902870803,
    lm4N 5854077957358, lm4N 1383625782707, lm4P 6722944281811, lm4N 5792813029018,
    lm4N 14627203076020, lm4N 11747688983878, lm4P 379797003942, lm4P 6885116985477,
    lm4P 3176139996509, lm4P 3716619768153, lm4N 4086410992560, lm4P 332806713974,
    lm4P 3965716678133, lm4P 5272914439472, lm4P 10144719183960, lm4P 3254521758403,
    lm4N 7405045506898, lm4N 18661931997651, lm4N 12743329538438, lm4N 18827547503649,
    lm4N 15271246141290, lm4N 25155789654147, lm4N 12341737870421, lm4N 2556149691143,
    lm4P 4891537878555, lm4N 37839750194273, lm4N 44481244164724, lm4N 46865989394028,
    lm4N 14810691780424, lm4N 6996691099801, lm4N 37689793515635, lm4N 24756425916746,
    lm4N 101835827708706, lm4N 45526774257861, lm4N 46327167573781, lm4N 95428900391614,
    lm4P 75337275834144, lm4P 434282836117958, lm4P 648988963970371, lm4P 536480242834255 ]
private def lm4StR128S7V2 : List ℤ :=
  [ lm4P 247992338540138 ]
private def lm4StR128S7 : Lm4St :=
  (62, 128, 1426994, lm4StR128S7V0 ++ (lm4StR128S7V1 ++ lm4StR128S7V2))
private def lm4StR128S8V0 : List ℤ :=
  [ lm4P 1712438, lm4N 81954861, lm4P 46688713, lm4N 69150312, lm4P 336779860, lm4P 122901156,
    lm4N 239264555, lm4P 474837169, lm4P 276942460, lm4N 1386114071, lm4P 1592165673,
    lm4P 3425234350, lm4N 147172416, lm4N 2572184036, lm4N 3725349574, lm4N 1635129899,
    lm4P 1051738164, lm4P 695057934, lm4N 4464857709, lm4P 2404934911, lm4P 6749069168,
    lm4N 5459000548, lm4N 6883927972, lm4P 9834010792, lm4N 5508330734, lm4N 4571357113,
    lm4N 1773010661, lm4P 12371253252, lm4N 3589127374, lm4P 2972967864, lm4N 2095050107,
    lm4N 17377391817, lm4N 36067495697, lm4P 5038334019, lm4N 22784620298, lm4P 27711276444,
    lm4N 10847596278, lm4P 86982942364, lm4N 7196505933, lm4N 84426047481, lm4P 194591720,
    lm4N 2279194658, lm4P 57169364250, lm4P 48485375972, lm4N 135542923027, lm4N 68870584374,
    lm4N 179021744592, lm4N 153567018528, lm4N 152269165670, lm4N 175950393067,
    lm4P 74929886993, lm4P 34284258662, lm4P 32906289669, lm4N 102590613654, lm4P 130352141159,
    lm4P 335339376895, lm4P 321170935916, lm4N 175801227784, lm4P 289478721522,
    lm4P 217130028408, lm4N 42768487350, lm4N 27320494375, lm4N 996765022077, lm4N 856115042714 ]
private def lm4StR128S8V1 : List ℤ :=
  [ lm4N 848172961898, lm4N 55973050237, lm4N 27512787510, lm4N 459422195094, lm4P 822732517254,
    lm4P 203917515686, lm4P 488341488026, lm4N 429982680096, lm4N 1360372119193,
    lm4P 271257446806, lm4N 95070225177, lm4P 1051563810814, lm4P 558723848271,
    lm4P 2269221707121, lm4P 112011209915, lm4P 2702233781403, lm4P 3206859621556,
    lm4N 122302278883, lm4N 521683527733, lm4P 754209543305, lm4N 1982178966883,
    lm4N 4553403528232, lm4N 2185459627707, lm4N 11767554893, lm4P 7788439248546,
    lm4P 7862262010649, lm4N 1769715127700, lm4P 3194811949835, lm4P 3499336489207,
    lm4P 16149636460534, lm4N 3375671053368, lm4N 26889619537828, lm4N 6530979352641,
    lm4N 6603882086386, lm4P 3747949238640, lm4N 11355028205949, lm4N 1613027626912,
    lm4P 8900159194227, lm4P 1280643697950, lm4N 7827009403187, lm4N 1866792862833,
    lm4P 9536685791465, lm4N 4037996568075, lm4P 2121143850016, lm4P 10133698862825,
    lm4N 2407968143332, lm4P 17937887852075, lm4P 15034522701350, lm4P 9996943527457,
    lm4P 14954682428188, lm4N 37969814094493, lm4N 6854286309074, lm4N 37975364398712,
    lm4N 57804925895958, lm4N 23977491505487, lm4P 900805438841, lm4N 13312500554532,
    lm4N 37726852675052, lm4N 83908761934543, lm4N 64804670719087, lm4P 48213256763849,
    lm4P 92754969934218, lm4N 30852073801626, lm4P 449924173055421 ]
private def lm4StR128S8V2 : List ℤ :=
  [ lm4P 873685526478545 ]
private def lm4StR128S8 : Lm4St :=
  (62, 128, 1527976, lm4StR128S8V0 ++ (lm4StR128S8V1 ++ lm4StR128S8V2))
private def lm4RowR128 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 11, 0, 6, 13, 2, 1, 0, 19, 5, 45, 29, 47, 96, 30, 20, 3, 153,
    12, 8, 4, 301, 1300, 25, 519, 767, 117, 7565, 51, 7127, 0, 5, 3268, 2350, 18371, 4742,
    32048, 23582, 23185, 30958, 5614, 1175, 1082, 10524, 16991, 112451, 103149, 30905, 83797,
    47144, 1829, 746, 993537, 732930, 719394, 3132, 756, 211067, 676886, 41581, 238475, 184883,
    1850608, 73579, 9038, 1105783, 312170, 5149360, 12546, 7302059, 10283938, 14957, 272152,
    568829, 3929027, 20733469, 4776227, 138, 60659762, 61815139, 3131886, 10206813, 12245345,
    260810708, 11395144, 723051556, 42653671, 43611238, 14047112, 128936630, 2601853, 79212806,
    1640044, 61262052, 3484909, 90948346, 16305403, 4499244, 102691821, 5798303, 321767765,
    226036826, 99938849, 223642480, 1441706666, 46981219, 1442128185, 3341409281, 574920025,
    811447, 177222630, 1423315297, 7040680072, 4199645148, 2324517980, 8603484164, 951850363,
    202431760124, 763326396508 ]
private theorem lm4_row_chunk_0 : lm4AtF [
    lm4ChkRow 3 lm4SgsR3 lm4RowR3,
    lm4ChkRow 4 lm4SgsR4 lm4RowR4,
    lm4ChkRow 5 lm4SgsR5 lm4RowR5,
    lm4ChkRow 6 lm4SgsR6 lm4RowR6,
    lm4ChkRow 7 lm4SgsR7 lm4RowR7,
    lm4ChkRow 8 lm4SgsR8 lm4RowR8,
    lm4ChkRow 9 lm4SgsR9 lm4RowR9,
    lm4ChkRow 10 lm4SgsR10 lm4RowR10,
    lm4ChkRow 11 lm4SgsR11 lm4RowR11,
    lm4ChkRow 12 lm4SgsR12 lm4RowR12,
    lm4ChkRow 14 lm4SgsR14 lm4RowR14,
    lm4ChkRow 15 lm4SgsR15 lm4RowR15,
    lm4ChkRow 16 lm4SgsR16 lm4RowR16
  ] = true := by
  decide +kernel
private theorem lm4_row_chunk_1 : lm4AtF [
    lm4ChkRow 18 lm4SgsR18 lm4RowR18,
    lm4ChkRow 20 lm4SgsR20 lm4RowR20,
    lm4ChkRow 23 lm4SgsR23 lm4RowR23,
    lm4ChkRow 27 lm4SgsR27 lm4RowR27,
    lm4ChkRow 35 lm4SgsR35 lm4RowR35,
    lm4ChkRow 43 lm4SgsR43 lm4RowR43
  ] = true := by
  decide +kernel
private theorem lm4_row_chunk_2 : lm4AtF [
    lm4ChkRow 32 lm4SgsR32 lm4RowR32
  ] = true := by
  decide +kernel
private theorem lm4_sl_r64_0 :
    lm4ChkSlice 64 lm4SgsR64S0 lm4InitSt lm4StR64S1 = true := by
  decide +kernel
private theorem lm4_sl_r64_1 :
    lm4ChkSlice 64 lm4SgsR64S1 lm4StR64S1 lm4StR64S2 = true := by
  decide +kernel
private theorem lm4_sl_r64_2 :
    lm4ChkSlice 64 lm4SgsR64S2 lm4StR64S2 lm4StR64S3 = true := by
  decide +kernel
private theorem lm4_sl_r128_0 :
    lm4ChkSlice 128 lm4SgsR128S0 lm4InitSt lm4StR128S1 = true := by
  decide +kernel
private theorem lm4_sl_r128_1 :
    lm4ChkSlice 128 lm4SgsR128S1 lm4StR128S1 lm4StR128S2 = true := by
  decide +kernel
private theorem lm4_sl_r128_2 :
    lm4ChkSlice 128 lm4SgsR128S2 lm4StR128S2 lm4StR128S3 = true := by
  decide +kernel
private theorem lm4_sl_r128_3 :
    lm4ChkSlice 128 lm4SgsR128S3 lm4StR128S3 lm4StR128S4 = true := by
  decide +kernel
private theorem lm4_sl_r128_4 :
    lm4ChkSlice 128 lm4SgsR128S4 lm4StR128S4 lm4StR128S5 = true := by
  decide +kernel
private theorem lm4_sl_r128_5 :
    lm4ChkSlice 128 lm4SgsR128S5 lm4StR128S5 lm4StR128S6 = true := by
  decide +kernel
private theorem lm4_sl_r128_6 :
    lm4ChkSlice 128 lm4SgsR128S6 lm4StR128S6 lm4StR128S7 = true := by
  decide +kernel
private theorem lm4_sl_r128_7 :
    lm4ChkSlice 128 lm4SgsR128S7 lm4StR128S7 lm4StR128S8 = true := by
  decide +kernel
private def lm4k128VPot : List ℕ :=
  [ 0, 321349540849363, 396444684681935, 455223601265879, 536852612256806, 596213948024178,
    656459273172097, 706643147667994, 753104660801694, 796745303510161, 840915610393536,
    881385422083990, 920066032244407, 1009192358927422, 993063192156421, 1027148126912071,
    1056050431652282, 1133989143397321, 1124749022300174, 1198471663043099, 1189265419428144,
    1259389638260597, 1327901590570228, 1284607936139259, 1350203136485809, 1414473044655682,
    1477494874635489, 1376712758372430, 1437442113301874, 1497115224962937, 1555785355751979,
    1613501437092395, 1480594937500967, 1536534712314464, 1591645703906325, 1569283284861132,
    1622841541669360, 1675671080756037, 1727800859952339, 1779257968654660, 1830067792361326,
    1880254159036948, 1929839469698785, 1901208563361389, 1949653829431859, 1997557790623694,
    2044938195536002, 2091811843579847, 2138194654558183, 2184101731822378, 2229547419715532,
    2274545355921823, 2319108519263331, 2363249273419052, 2406979406983419, 2450310170232073,
    2493252308919767, 2535816095398065, 2578011357308105, 2619847504075472, 2661333551409505,
    2702478143987727, 2743289576487049, 2783775813106678, 2083419356970575, 2123277861980190,
    2162833256088862, 2202092350938583, 2241061706811103, 2279747645424974, 2318156261906937,
    2356293436001841, 2394164842579469, 2431775961491429, 2469132086826578, 2506238335609247,
    2543099655980710, 2579720834900944, 2616106505404609, 2652261153442385, 2688189124336261,
    2723894628875080, 2759381749074527, 2794654443623885, 2829716553040112, 2864571804548246,
    2899223816705685, 2933676103786583, 2967932079941399, 3001995063145534, 3035868278949978,
    3069554864045972, 3103057869654830, 3136380264753290, 3169524939144045, 3202494706380440,
    3235292306553715, 3267920408950600, 3300381614588567, 3332678458635547, 3364813412720484,
    3396788887140686, 3428607232971554, 3460270744083907, 3491781659073811, 3523142163109499,
    3554354389699698, 3585420422387413, 3616342296372970, 3647122000069897, 3677761476597009,
    3708262625209866, 3738627302674588, 3768857324586837, 3798954466638618, 3828920465835403,
    3858757021665935, 3888465797226940, 3918048420304861, 3947506484416593, 3976841549811114,
    4006055144433784, 4035148764855002, 4064123877164822, 4092981917835030, 4121724294550131,
    4150352387008594, 4178867547695651, 2932083892266482 ]
private def lm4k128Anchors : List DickeSol.RampKick128kAnchor :=
  [ ⟨3, lm4SgsR3, lm4RowR3⟩, ⟨4, lm4SgsR4, lm4RowR4⟩, ⟨5, lm4SgsR5, lm4RowR5⟩,
    ⟨6, lm4SgsR6, lm4RowR6⟩, ⟨7, lm4SgsR7, lm4RowR7⟩, ⟨8, lm4SgsR8, lm4RowR8⟩,
    ⟨9, lm4SgsR9, lm4RowR9⟩, ⟨10, lm4SgsR10, lm4RowR10⟩, ⟨11, lm4SgsR11, lm4RowR11⟩,
    ⟨12, lm4SgsR12, lm4RowR12⟩, ⟨14, lm4SgsR14, lm4RowR14⟩, ⟨15, lm4SgsR15, lm4RowR15⟩,
    ⟨16, lm4SgsR16, lm4RowR16⟩, ⟨18, lm4SgsR18, lm4RowR18⟩, ⟨20, lm4SgsR20, lm4RowR20⟩,
    ⟨23, lm4SgsR23, lm4RowR23⟩, ⟨27, lm4SgsR27, lm4RowR27⟩, ⟨32, lm4SgsR32, lm4RowR32⟩,
    ⟨35, lm4SgsR35, lm4RowR35⟩, ⟨43, lm4SgsR43, lm4RowR43⟩, ⟨64, lm4SgsR64, lm4RowR64⟩,
    ⟨128, lm4SgsR128, lm4RowR128⟩ ]
private theorem lm4k128_meta : lm4AtF [
    DickeSol.rkm128kCheckTable 4 128 62 true lm4k128VPot lm4k128Anchors,
    lm4ChkCell 4 2 98193933431639 200000000000000 lm4k128VPot lm4k128Anchors,
    lm4ChkCell 8 4 219351823974601 500000000000000 lm4k128VPot lm4k128Anchors,
    lm4ChkCell 16 8 100885823733429 250000000000000 lm4k128VPot lm4k128Anchors,
    lm4ChkCell 32 16 189624273570189 500000000000000 lm4k128VPot lm4k128Anchors,
    lm4ChkCell 64 31 72666217410757 200000000000000 lm4k128VPot lm4k128Anchors,
    lm4ChkCell 128 62 352006510827783 1000000000000000 lm4k128VPot lm4k128Anchors,
    lm4SegsGuard 64 lm4SgsR64,
    lm4FinGuard lm4StR64S3 lm4RowR64,
    lm4SegsGuard 128 lm4SgsR128,
    lm4FinGuard lm4StR128S8 lm4RowR128
  ] = true := by
  decide +kernel
private theorem lm4_row_eq_r64 :
    DickeSol.rkm128kEvalRowLo12 4 62 64 lm4SgsR64 = lm4RowR64 :=
  lm4_cert_row 64 lm4SgsR64 lm4StR64S3 lm4RowR64
    (lm4_hd (lm4_tl1 (lm4_tl2 (lm4_tl4 lm4k128_meta))))
    (lm4_chain 64 lm4SgsR64S0 lm4TlR64S1
      lm4InitSt lm4StR64S1 lm4StR64S3
      (lm4StEq_eq lm4_sl_r64_0)
    (lm4_chain 64 lm4SgsR64S1 lm4SgsR64S2
      lm4StR64S1 lm4StR64S2 lm4StR64S3
      (lm4StEq_eq lm4_sl_r64_1)
      (lm4StEq_eq lm4_sl_r64_2)))
    (lm4_hd (lm4_tl4 (lm4_tl4 lm4k128_meta)))
private theorem lm4_row_eq_r128 :
    DickeSol.rkm128kEvalRowLo12 4 62 128 lm4SgsR128 = lm4RowR128 :=
  lm4_cert_row 128 lm4SgsR128 lm4StR128S8 lm4RowR128
    (lm4_hd (lm4_tl1 (lm4_tl4 (lm4_tl4 lm4k128_meta))))
    (lm4_chain 128 lm4SgsR128S0 lm4TlR128S1
      lm4InitSt lm4StR128S1 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_0)
    (lm4_chain 128 lm4SgsR128S1 lm4TlR128S2
      lm4StR128S1 lm4StR128S2 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_1)
    (lm4_chain 128 lm4SgsR128S2 lm4TlR128S3
      lm4StR128S2 lm4StR128S3 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_2)
    (lm4_chain 128 lm4SgsR128S3 lm4TlR128S4
      lm4StR128S3 lm4StR128S4 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_3)
    (lm4_chain 128 lm4SgsR128S4 lm4TlR128S5
      lm4StR128S4 lm4StR128S5 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_4)
    (lm4_chain 128 lm4SgsR128S5 lm4TlR128S6
      lm4StR128S5 lm4StR128S6 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_5)
    (lm4_chain 128 lm4SgsR128S6 lm4SgsR128S7
      lm4StR128S6 lm4StR128S7 lm4StR128S8
      (lm4StEq_eq lm4_sl_r128_6)
      (lm4StEq_eq lm4_sl_r128_7))))))))
    (lm4_hd (lm4_tl2 (lm4_tl4 (lm4_tl4 lm4k128_meta))))
private theorem lm4k128AnchorsSound : DickeSol.RampKick128kAnchorsSound 4 62 lm4k128Anchors :=
  ⟨lm4ListNatEq_eq (lm4_hd lm4_row_chunk_0),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 lm4_row_chunk_0)),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl2 lm4_row_chunk_0)),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl2 lm4_row_chunk_0))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl4 lm4_row_chunk_0)),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl4 lm4_row_chunk_0))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl2 (lm4_tl4 lm4_row_chunk_0))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl2 (lm4_tl4 lm4_row_chunk_0)))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl4 (lm4_tl4 lm4_row_chunk_0))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl4 (lm4_tl4 lm4_row_chunk_0)))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl2 (lm4_tl4 (lm4_tl4 lm4_row_chunk_0)))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl2 (lm4_tl4 (lm4_tl4 lm4_row_chunk_0))))),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl4 (lm4_tl4 (lm4_tl4 lm4_row_chunk_0)))),
    ⟨lm4ListNatEq_eq (lm4_hd lm4_row_chunk_1),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 lm4_row_chunk_1)),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl2 lm4_row_chunk_1)),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl2 lm4_row_chunk_1))),
    ⟨lm4ListNatEq_eq (lm4_hd lm4_row_chunk_2),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl4 lm4_row_chunk_1)),
    ⟨lm4ListNatEq_eq (lm4_hd (lm4_tl1 (lm4_tl4 lm4_row_chunk_1))),
    ⟨lm4_row_eq_r64,
    ⟨lm4_row_eq_r128,
    trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem lm4k128Valid :
    DickeSol.RampKick128kTableValid 4 128 62 true lm4k128VPot lm4k128Anchors :=
  DickeSol.rkm128kCheckTable_sound lm4k128AnchorsSound (lm4_hd lm4k128_meta)

private theorem lm4k128CellChecks {m k : ℕ}
    (h : isLowM4K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (lowM4K128KrotovCertCellLMax m k)
        lm4k128Anchors = true ∧
      ∃ num den : ℕ, relCostLowM4K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (lm4k128VPot.getD k 0) num den = true := by
  unfold isLowM4K128KrotovCertCell at h
  split_ifs at h with hm4 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm4 hk4; have hm := lm4_hd (lm4_tl1 lm4k128_meta)
    exact ⟨lm4_and_l hm, 98193933431639, 200000000000000, rfl, lm4_and_r hm⟩
  · subst hm4 hk8; have hm := lm4_hd (lm4_tl2 lm4k128_meta)
    exact ⟨lm4_and_l hm, 219351823974601, 500000000000000, rfl, lm4_and_r hm⟩
  · subst hm4 hk16; have hm := lm4_hd (lm4_tl1 (lm4_tl2 lm4k128_meta))
    exact ⟨lm4_and_l hm, 100885823733429, 250000000000000, rfl, lm4_and_r hm⟩
  · subst hm4 hk32; have hm := lm4_hd (lm4_tl4 lm4k128_meta)
    exact ⟨lm4_and_l hm, 189624273570189, 500000000000000, rfl, lm4_and_r hm⟩
  · subst hm4 hk64; have hm := lm4_hd (lm4_tl1 (lm4_tl4 lm4k128_meta))
    exact ⟨lm4_and_l hm, 72666217410757, 200000000000000, rfl, lm4_and_r hm⟩
  · subst hm4 hk128; have hm := lm4_hd (lm4_tl2 (lm4_tl4 lm4k128_meta))
    exact ⟨lm4_and_l hm, 352006510827783, 1000000000000000, rfl, lm4_and_r hm⟩

private lemma lm4k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma lm4k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma lm4k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private lemma lm4k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b :=
  h ▸ Nat.le_add_right a d

private lemma lm4k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lm4k128_le_of_add h), rfl⟩

private structure Lm4k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ lowM4K128KrotovCertCellLMax m k
  hl1 : 1 ≤ lowM4K128KrotovCertCellLMax m k
  hlm : lowM4K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 62 true lm4k128VPot lm4k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM4K128KrotovCertCellLMax m k)
    lm4k128Anchors = true
  hcost : ∃ num den : ℕ, relCostLowM4K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (lm4k128VPot.getD k 0) num den = true

private theorem lm4k128_all_props {m k : ℕ} (h : isLowM4K128KrotovCertCell m k = true) :
    Lm4k128CellProps m k := by
  rcases lm4k128CellChecks h with ⟨hlmax, hcost⟩
  unfold isLowM4K128KrotovCertCell at h
  split_ifs at h with hm4 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm4 hk4
    exact ⟨lm4k128_mem_grid 2 8 rfl, lm4k128_mem_grid 2 8 rfl,
      lm4k128_le_of_add (d := 124) rfl, lm4k128_le_of_add (d := 2) rfl,
      lm4k128_le_of_add (d := 0) rfl, lm4k128_le_of_add (d := 1) rfl,
      lm4k128_le_of_add (d := 65528) rfl, lm4k128Valid, hlmax, hcost⟩
  · subst hm4 hk8
    exact ⟨lm4k128_mem_grid 2 8 rfl, lm4k128_mem_grid 3 7 rfl,
      lm4k128_le_of_add (d := 120) rfl, lm4k128_le_of_add (d := 2) rfl,
      lm4k128_le_of_add (d := 2) rfl, lm4k128_le_of_add (d := 3) rfl,
      lm4k128_le_of_add (d := 65520) rfl, lm4k128Valid, hlmax, hcost⟩
  · subst hm4 hk16
    exact ⟨lm4k128_mem_grid 2 8 rfl, lm4k128_mem_grid 4 6 rfl,
      lm4k128_le_of_add (d := 112) rfl, lm4k128_le_of_add (d := 2) rfl,
      lm4k128_le_of_add (d := 6) rfl, lm4k128_le_of_add (d := 7) rfl,
      lm4k128_le_of_add (d := 65504) rfl, lm4k128Valid, hlmax, hcost⟩
  · subst hm4 hk32
    exact ⟨lm4k128_mem_grid 2 8 rfl, lm4k128_mem_grid 5 5 rfl,
      lm4k128_le_of_add (d := 96) rfl, lm4k128_le_of_add (d := 2) rfl,
      lm4k128_le_of_add (d := 14) rfl, lm4k128_le_of_add (d := 15) rfl,
      lm4k128_le_of_add (d := 65472) rfl, lm4k128Valid, hlmax, hcost⟩
  · subst hm4 hk64
    exact ⟨lm4k128_mem_grid 2 8 rfl, lm4k128_mem_grid 6 4 rfl,
      lm4k128_le_of_add (d := 64) rfl, lm4k128_le_of_add (d := 2) rfl,
      lm4k128_le_of_add (d := 29) rfl, lm4k128_le_of_add (d := 30) rfl,
      lm4k128_le_of_add (d := 65412) rfl, lm4k128Valid, hlmax, hcost⟩
  · subst hm4 hk128
    exact ⟨lm4k128_mem_grid 2 8 rfl, lm4k128_mem_grid 7 3 rfl,
      lm4k128_le_of_add (d := 0) rfl, lm4k128_le_of_add (d := 2) rfl,
      lm4k128_le_of_add (d := 60) rfl, lm4k128_le_of_add (d := 61) rfl,
      lm4k128_le_of_add (d := 65288) rfl, lm4k128Valid, hlmax, hcost⟩

private noncomputable def lowM4K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM4K128KrotovCertQubits n m k)) Var
      (lowM4K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isLowM4K128KrotovCertCell m k = true then
    let p := lm4k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm4k128VPot lm4k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the `6` `m = 4, 4 ≤ k ≤ 128` cells. -/
noncomputable def findAllJohnsonRampKick128kLowM4K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM4K128KrotovCertQubits n m k)) Var
      (lowM4K128KrotovCertQubits n m k) ((n + 1) * m) :=
  lowM4K128KrotovCertCircuitImpl res n m k

private lemma lm4k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isLowM4K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kLowM4K128KrotovCertCircuit res n m k =
      let p := lm4k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm4k128VPot lm4k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kLowM4K128KrotovCertCircuit lowM4K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-`1` recovery of `S` across the `6` `m = 4, 4 ≤ k ≤ 128` cells. -/
theorem lowM4K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isLowM4K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kLowM4K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [lm4k128_targetSets_eq]
  have hp := lm4k128_all_props hcell
  rw [lm4k128_circuit_eq res n hcell, ← lm4k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG lm4k128VPot lm4k128Anchors hp.hk128
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across `m = 4, 4 ≤ k ≤ 128`. -/
theorem lowM4K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isLowM4K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kLowM4K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostLowM4K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := lm4k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG lm4k128VPot
    lm4k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [lm4k128_circuit_eq res n hcell, ← lm4k128_oracle_eq]
    exact hq S (by rwa [lm4k128_targetSets_eq])
  · rw [← lm4k128_targetSets_eq, ← lm4k128_vanilla_eq]; exact hsum

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

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K128KrCert
