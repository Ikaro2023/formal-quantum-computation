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
# Krotov `m = 32` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kMidM32K128KrCert`)

QHL-verified module packaging all `6` `m = 32, 4 ≤ k ≤ 128` cells
(`(32, 4), (32, 8), (32, 16), (32, 32), (32, 64), (32, 128)`) over `10` anchors
`r ∈ {3..8, 16, 32, 64, 128}` (`492` segments, `444,643` Horner coord-ops at
`lTableMax = 8`, `useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM32K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m = 32, k ∈ {4, 8, 16, 32, 64, 128}`, `6` cells). -/
def isMidM32K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 32 then
    if k == 4 then true
    else if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor `L_{\max}(32, k)` across `k ∈ {4..128}`. -/
def midM32K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 32 then
    if k == 4 then 2
    else if k == 8 then 2
    else if k == 16 then 2
    else if k == 32 then 2
    else if k == 64 then 4
    else if k == 128 then 8
    else 1
  else 1

/-- Total register qubit budget `(midM32K128KrotovCertCellLMax m k * m) * (n + 1) + k * n`. -/
abbrev midM32K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (midM32K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile `c(32, k): ℚ≥0` across `k ∈ {4..128}`. -/
def relCostMidM32K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 32 then
    if k == 4 then NNRat.divNat 356512242573879 1000000000000000
    else if k == 8 then NNRat.divNat 240096513766043 1000000000000000
    else if k == 16 then NNRat.divNat 43893601346917 250000000000000
    else if k == 32 then NNRat.divNat 75118094154941 500000000000000
    else if k == 64 then NNRat.divNat 68317558069959 500000000000000
    else if k == 128 then NNRat.divNat 25702048974707 200000000000000
    else 1
  else 1

/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def midM32K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isMidM32K128KrotovCertCell, relCostMidM32K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kMidM32K128KrCert` cell lies on `groverGrid × groverGrid`. -/
theorem isMidM32K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isMidM32K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isMidM32K128KrotovCertCell at h
  split_ifs at h with hm32 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm32 hk4; rfl
  · subst hm32 hk8; rfl
  · subst hm32 hk16; rfl
  · subst hm32 hk32; rfl
  · subst hm32 hk64; rfl
  · subst hm32 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def mm32P (n : ℕ) : ℤ := Int.ofNat n
private def mm32N (n : ℕ) : ℤ := Int.negSucc n
private def mm32NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem mm32NatEq_eq {x y : ℕ} (h : mm32NatEq x y = true) : x = y := by
  unfold mm32NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def mm32ListNatEq (xs ys : List ℕ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (mm32NatEq x y) (mm32ListNatEq xr yr) false
  | _, _ => false
private theorem mm32ListNatEq_eq {xs ys : List ℕ} (h : mm32ListNatEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [mm32ListNatEq] at h
      cases hxy : mm32NatEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (mm32NatEq_eq hxy) (ih h)
private def mm32IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => mm32NatEq m n
  | Int.negSucc m, Int.negSucc n => mm32NatEq m n
  | _, _ => false
private theorem mm32IntEq_eq {a b : ℤ} (h : mm32IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact congrArg Int.ofNat (mm32NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => exact congrArg Int.negSucc (mm32NatEq_eq h)
private def mm32ListIntEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (mm32IntEq x y) (mm32ListIntEq xr yr) false
  | _, _ => false
private theorem mm32ListIntEq_eq {xs ys : List ℤ} (h : mm32ListIntEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [mm32ListIntEq] at h
      cases hxy : mm32IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (mm32IntEq_eq hxy) (ih h)
private abbrev Mm32St := ℕ × ℕ × ℕ × List ℤ
private def mm32StEq (a b : Mm32St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    Bool.and (mm32NatEq a1 b1) (Bool.and (mm32NatEq a2 b2)
      (Bool.and (mm32NatEq a3 b3) (mm32ListIntEq av bv)))
private theorem mm32StEq_eq {a b : Mm32St} (h : mm32StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩
  rcases b with ⟨b1, b2, b3, bv⟩
  dsimp only [mm32StEq] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2, h3, hv⟩
  exact Prod.ext (mm32NatEq_eq h1) (Prod.ext (mm32NatEq_eq h2)
    (Prod.ext (mm32NatEq_eq h3) (mm32ListIntEq_eq hv)))
private def mm32AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (mm32AtF rest) false
private theorem mm32_hd {b : Bool} {bs : List Bool} (h : mm32AtF (b :: bs) = true) : b = true := by
  unfold mm32AtF at h
  cases b with
  | false => cases h
  | true => rfl
private theorem mm32_tl1 {b : Bool} {s : List Bool} (h : mm32AtF (b :: s) = true) :
    mm32AtF s = true := by
  unfold mm32AtF at h
  cases b with
  | false => cases h
  | true => exact h
private theorem mm32_tl2 {b1 b2 : Bool} {bs : List Bool} (h : mm32AtF (b1 :: b2 :: bs) = true) :
    mm32AtF bs = true := mm32_tl1 (mm32_tl1 h)
private theorem mm32_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : mm32AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : mm32AtF bs = true :=
  mm32_tl2 (mm32_tl2 h)
private theorem mm32_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem mm32_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev mm32M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private abbrev mm32ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  mm32ListNatEq (DickeSol.rkm128kEvalRowLo12 32 8 r s) ro
private def mm32InitSt : Mm32St := (1, 0, 1, [Int.ofNat DickeSol.wdScale])
private def mm32RunSt (r : ℕ) (s : List DickeSol.Rkm128kSeg) (st : Mm32St) : Mm32St :=
  match st with
  | (l0, d0, p0, v0) => DickeSol.rkm128kRunSegs 32 8 r s l0 d0 p0 v0
private abbrev mm32ChkSlice (r : ℕ) (s : List DickeSol.Rkm128kSeg) (st0 st1 : Mm32St) : Bool :=
  mm32StEq (mm32RunSt r s st0) st1
private theorem mm32_chain (r : ℕ) (s1 s2 : List DickeSol.Rkm128kSeg) (st0 st1 st2 : Mm32St)
    (h1 : mm32RunSt r s1 st0 = st1) (h2 : mm32RunSt r s2 st1 = st2) :
    mm32RunSt r (s1 ++ s2) st0 = st2 := by
  rcases st0 with ⟨l0, d0, p0, v0⟩
  rcases st1 with ⟨l1, d1, p1, v1⟩
  unfold mm32RunSt at *
  dsimp only at *
  rw [DickeSol.rkm128kRunSegs_append, h1]
  dsimp only
  exact h2
private abbrev mm32SegsGuard (r : ℕ) (segs : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen segs))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen segs) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private abbrev mm32FinGuard (st : Mm32St) (ro : List ℕ) : Bool :=
  mm32ListNatEq (DickeSol.rkm128kFinalizeState st) ro
private theorem mm32_cert_row (r : ℕ) (segs : List DickeSol.Rkm128kSeg) (st : Mm32St) (ro : List ℕ)
    (hsegs : mm32SegsGuard r segs = true) (hrun : mm32RunSt r segs mm32InitSt = st)
    (hfin : mm32FinGuard st ro = true) : DickeSol.rkm128kEvalRowLo12 32 8 r segs = ro := by
  unfold mm32RunSt mm32InitSt at hrun
  dsimp only at hrun
  exact @DickeSol.rkm128kCertRow_of_runSegs 32 8 r segs st ro hsegs hrun (mm32ListNatEq_eq hfin)
private abbrev mm32ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) :
    Bool := Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 32 k (v.getD k 0) n d)

private def mm32SgsR3 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 85936192, 1, 34, []⟩, mm32M 1 36331183 1 23 1 [1], mm32M 1 180514 1 7 1 [1],
    mm32M 1 184760 1 7 1 [1], mm32M 1 184202 1 7 1 [1], mm32M 1 190601 1 7 1 [1],
    mm32M 1 191054 1 7 1 [1], mm32M 1 204204 1 7 1 [1], mm32M 1 197543 1 7 1 [1],
    mm32M 1 203758 1 7 1 [1], mm32M 1 217286 1 7 1 [1], mm32M 1 216434 1 7 1 [1],
    mm32M 1 223754 1 7 1 [1], mm32M 1 235327 1 7 1 [1], ⟨1, 195716, 1, 7, []⟩,
    mm32M 1 48929 1 6 1 [1], mm32M 1 254032 1 7 1 [1], mm32M 1 254869 1 7 1 [1],
    mm32M 1 276673 1 7 1 [1], mm32M 1 257092 1 7 1 [1], mm32M 1 252954 1 7 1 [1],
    mm32M 1 282051 1 7 1 [1], mm32M 1 252787 1 7 1 [1], mm32M 1 228474 1 7 1 [1],
    mm32M 1 195995 1 7 1 [1], mm32M 1 191468 1 7 1 [1], mm32M 1 257886 1 7 1 [1],
    mm32M 1 304315 1 7 1 [1], mm32M 1 231550 1 7 1 [1], mm32M 1 204538 1 7 1 [1],
    mm32M 1 183304 1 7 1 [1], ⟨1, 45810, 1, 6, []⟩ ]
private def mm32RowR3 : List ℕ :=
  [ 39674303, 56966006055, 942994319610 ]
private def mm32SgsR4 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 65563229, 1, 26, []⟩, mm32M 1 52447570 1 24 1 [1], mm32M 1 1959559 1 10 1 [1],
    ⟨1, 830181, 1, 8, []⟩, mm32M 1 686231 1 8 1 [1], mm32M 1 425457 1 8 1 [1],
    mm32M 1 1489188 1 8 2 [2], mm32M 1 433548 1 8 2 [3], mm32M 1 453451 1 8 2 [2],
    mm32M 1 473556 1 8 2 [2], mm32M 1 500525 1 8 2 [3], mm32M 1 529586 1 8 2 [2],
    mm32M 1 570548 1 8 2 [3], mm32M 1 628180 1 8 2 [2], mm32M 1 705607 1 8 2 [2],
    mm32M 1 807366 1 8 2 [2], mm32M 1 1046393 1 8 2 [2], ⟨1, 911524, 1, 8, []⟩,
    mm32M 1 681157 1 8 3 [5], mm32M 1 311453 1 8 3 [7], ⟨1, 139823, 1, 8, []⟩,
    ⟨1, 5999, 1, 8, []⟩, mm32M 1 142760 1 8 1 [1], ⟨1, 11139, 1, 8, []⟩,
    mm32M 1 11139 1 8 3 [5], mm32M 1 310184 1 8 3 [4], ⟨1, 143231, 1, 8, []⟩,
    mm32M 1 167348 1 8 3 [4], ⟨1, 60770, 1, 8, []⟩, ⟨1, 180440, 1, 8, []⟩,
    mm32M 1 70134 1 8 3 [5], ⟨1, 169494, 1, 8, []⟩ ]
private def mm32RowR4 : List ℕ :=
  [ 44, 4922, 43646125062, 956353869937 ]
private def mm32SgsR5 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 35044176, 1, 20, []⟩, ⟨1, 17134445, 1, 16, []⟩, ⟨1, 14335569, 1, 14, []⟩,
    ⟨1, 11984479, 1, 14, []⟩, ⟨1, 10009564, 1, 14, []⟩, ⟨1, 8350635, 1, 12, []⟩,
    ⟨1, 6957135, 1, 12, []⟩, ⟨1, 5786595, 1, 12, []⟩, mm32M 1 4816441 1 12 1 [1],
    mm32M 1 4507529 1 12 2 [3], mm32M 1 1786209 1 10 2 [2], mm32M 1 1811077 1 10 2 [2],
    mm32M 1 2049571 1 10 3 [5], mm32M 1 702119 1 8 3 [7], mm32M 1 762875 1 8 3 [4],
    mm32M 1 833369 1 8 3 [4], mm32M 1 924283 1 8 3 [4], mm32M 1 1088361 1 8 3 [4],
    mm32M 1 1402344 1 10 3 [4], mm32M 1 2031362 1 10 4 [15], mm32M 1 316531 1 8 4 [9],
    mm32M 1 313967 1 8 4 [9], mm32M 1 312414 1 8 4 [14], mm32M 1 313995 1 8 4 [9],
    mm32M 1 316037 1 8 4 [11], mm32M 1 313911 1 8 4 [11], mm32M 1 312886 1 8 4 [11],
    mm32M 1 317084 1 8 4 [15], mm32M 1 316294 1 8 4 [10], mm32M 1 312610 1 8 4 [8],
    mm32M 1 315359 1 8 4 [10], ⟨1, 176508, 1, 8, []⟩ ]
private def mm32RowR5 : List ℕ :=
  [ 0, 183, 8406, 35872465023, 964127526351 ]
private def mm32SgsR6 : List DickeSol.Rkm128kSeg :=
  [ mm32M 1 110923161 2 28 1 [1], mm32M 1 4413668 1 12 2 [2], mm32M 1 2787575 1 10 2 [2],
    mm32M 1 1587414 1 10 3 [4], mm32M 1 1268542 1 10 2 [2], mm32M 1 89428 1 8 3 [5],
    mm32M 1 1801210 1 10 3 [4], mm32M 1 2690707 1 10 4 [15], mm32M 1 494682 1 8 4 [10],
    mm32M 1 518209 1 8 4 [10], mm32M 1 546061 1 8 4 [9], mm32M 1 579628 1 8 4 [9],
    mm32M 1 621797 1 8 4 [9], ⟨1, 9549, 1, 8, []⟩, mm32M 1 671469 1 8 4 [8],
    mm32M 1 753372 1 8 4 [12], mm32M 1 875821 1 8 4 [11], ⟨1, 1001666, 1, 8, []⟩,
    mm32M 1 131526 1 8 4 [15], mm32M 1 1895908 1 10 5 [24], mm32M 1 563218 1 8 5 [18],
    mm32M 1 288780 1 8 5 [28], mm32M 1 274100 1 8 5 [27], mm32M 1 17503 1 8 4 [10],
    mm32M 1 541191 1 8 5 [30], mm32M 1 562902 1 8 5 [17], mm32M 1 563001 1 8 5 [16],
    mm32M 1 562882 1 8 5 [22], mm32M 1 562813 1 8 5 [20], mm32M 1 264834 1 8 2 [2],
    mm32M 1 298113 1 8 5 [16], ⟨1, 342067, 1, 8, []⟩ ]
private def mm32RowR6 : List ℕ :=
  [ 0, 5, 55, 158959, 30842923787, 969156917150 ]
private def mm32SgsR7 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 22011461, 1, 20, []⟩, ⟨1, 52417897, 2, 22, []⟩, ⟨1, 13573693, 1, 16, []⟩,
    mm32M 1 19201295 1 18 1 [1], mm32M 1 935893 1 8 1 [1], mm32M 1 3672176 1 12 2 [3],
    mm32M 1 4506100 1 12 3 [4], ⟨1, 4036815, 1, 12, []⟩, mm32M 1 635570 1 8 4 [10],
    mm32M 1 1841929 1 10 3 [5], ⟨1, 75627, 1, 8, []⟩, mm32M 1 289402 1 8 4 [9],
    mm32M 1 1584737 1 10 1 [1], mm32M 1 2267821 1 10 5 [19], mm32M 1 1337338 1 10 5 [26],
    mm32M 1 252541 1 8 2 [2], mm32M 1 1306019 1 10 5 [29], mm32M 1 2010263 1 10 5 [28],
    mm32M 1 1077965 1 8 4 [10], mm32M 1 1868544 1 10 6 [58], mm32M 1 507779 1 8 6 [36],
    mm32M 1 503954 1 8 6 [48], mm32M 1 503638 1 8 6 [34], mm32M 1 506791 1 8 6 [52],
    mm32M 1 507136 1 8 6 [36], mm32M 1 505783 1 8 6 [46], mm32M 1 505793 1 8 6 [46],
    mm32M 1 505831 1 8 6 [32], mm32M 1 505085 1 8 6 [48], mm32M 1 504759 1 8 6 [34],
    mm32M 1 505868 1 8 6 [52], ⟨1, 308191, 1, 8, []⟩ ]
private def mm32RowR7 : List ℕ :=
  [ 0, 2, 1, 1096, 88604, 27354109058, 972645801195 ]
private def mm32SgsR8 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 10135, 1, 8, []⟩, mm32M 1 112681324 3 26 3 [7], mm32M 1 2190405 1 10 1 [1],
    mm32M 1 1366877 1 10 1 [1], mm32M 1 1118342 1 10 4 [9], mm32M 1 1508911 1 10 1 [1],
    mm32M 1 3054521 1 12 5 [17], mm32M 1 1752058 1 10 1 [1], mm32M 1 142 1 8 5 [17],
    mm32M 1 1983059 1 10 3 [6], mm32M 1 6450 1 8 5 [16], mm32M 1 2294217 1 10 6 [41],
    mm32M 1 737785 1 8 6 [32], mm32M 1 793506 1 8 6 [62], mm32M 1 286194 1 8 1 [1],
    mm32M 1 586501 1 8 6 [33], mm32M 1 979088 1 10 6 [32], mm32M 1 1138286 1 10 6 [33],
    mm32M 1 1485212 1 10 6 [33], mm32M 1 2283647 1 10 7 [126], mm32M 1 571888 1 8 7 [97],
    mm32M 1 571184 1 8 7 [126], mm32M 1 571007 1 8 7 [64], mm32M 1 570751 1 8 7 [65],
    mm32M 1 571328 1 8 7 [81], mm32M 1 571524 1 8 7 [80], mm32M 1 570990 1 8 7 [65],
    mm32M 1 570701 1 8 7 [65], mm32M 1 571403 1 8 7 [65], mm32M 1 571586 1 8 7 [65],
    mm32M 1 571335 1 8 7 [65], ⟨1, 360692, 1, 8, []⟩ ]
private def mm32RowR8 : List ℕ :=
  [ 2481, 14976, 4837, 158, 235, 168862, 24828482649, 975171325750 ]
private def mm32SgsR16 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 2490296, 1, 15, []⟩, mm32M 1 2482882 1 15 17 [81920], ⟨1, 2478723, 1, 15, []⟩,
    mm32M 1 2478724 1 15 17 [81920], mm32M 1 2478723 1 15 15 [16384],
    mm32M 1 2478724 1 15 17 [98304], mm32M 1 2478723 1 15 17 [65536],
    mm32M 1 2478724 1 15 16 [32768], mm32M 1 2478723 1 15 16 [32768],
    mm32M 1 2478724 1 15 16 [32768], mm32M 1 2478723 1 15 16 [32768],
    mm32M 1 2478724 1 15 17 [65536], ⟨1, 2478723, 1, 15, []⟩, mm32M 1 2478724 1 15 17 [65536],
    ⟨1, 2478723, 1, 15, []⟩, mm32M 1 2478724 1 15 17 [65536], ⟨1, 2645092, 1, 15, []⟩,
    mm32M 1 2645093 1 15 17 [65536], ⟨1, 2645092, 1, 15, []⟩, mm32M 1 2645093 1 15 17 [65536],
    mm32M 1 2645084 1 15 17 [65536], ⟨1, 2645085, 1, 15, []⟩, ⟨1, 2646988, 1, 15, []⟩,
    ⟨1, 2646988, 1, 15, []⟩, ⟨1, 2067391, 1, 14, []⟩, ⟨1, 2065852, 1, 14, []⟩,
    ⟨1, 4131703, 1, 17, []⟩, ⟨1, 4131703, 1, 17, []⟩, ⟨1, 4131703, 1, 17, []⟩,
    ⟨1, 3542606, 1, 16, []⟩, ⟨1, 3542606, 1, 16, []⟩, ⟨1, 3542606, 1, 16, []⟩,
    mm32M 1 3542607 1 16 1 [1], mm32M 1 2921888 1 16 3 [6], mm32M 1 2921888 1 16 4 [12],
    mm32M 1 2921889 1 16 5 [18], mm32M 1 2921914 1 16 6 [45], mm32M 1 2381795 1 15 7 [78],
    mm32M 1 2381795 1 15 8 [142], mm32M 1 2358489 1 15 7 [90], mm32M 1 2365975 1 15 9 [434],
    mm32M 1 2121235 1 14 5 [17], mm32M 1 2109412 1 14 7 [122], mm32M 1 2109433 1 14 8 [224],
    mm32M 1 2109826 1 14 11 [1781], mm32M 1 2897609 1 16 7 [104],
    mm32M 1 2989534 1 16 12 [2178], mm32M 1 3158296 1 16 8 [194],
    mm32M 1 3109389 1 16 13 [4422], mm32M 1 3931888 1 17 13 [4201],
    mm32M 1 3700019 1 17 14 [8525], mm32M 1 3721529 1 17 14 [8317],
    mm32M 1 2840782 1 15 14 [8573], mm32M 1 2548473 1 15 15 [16946],
    mm32M 1 1749890 1 14 15 [17088], mm32M 1 1728364 1 13 15 [17170],
    mm32M 1 1448867 1 13 15 [16647], mm32M 1 1169874 1 12 15 [17080],
    mm32M 1 1004678 1 12 15 [17935], mm32M 1 876951 1 11 15 [16969],
    mm32M 1 739988 1 11 15 [16444], mm32M 1 610801 1 11 15 [17182],
    mm32M 1 563222 1 10 15 [18342], mm32M 1 430147 1 10 6 [32] ]
private def mm32RowR16 : List ℕ :=
  [ 0, 4, 2, 1, 0, 123, 125, 9588, 45288, 346, 893598, 8885351, 3923450, 579301, 18133661797,
    981852000884 ]
private def mm32SgsR32 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 4367807, 1, 21, []⟩, ⟨1, 3733164, 1, 20, []⟩, ⟨1, 3668741, 1, 20, []⟩,
    ⟨1, 3438953, 1, 19, []⟩, mm32M 1 3566998 1 20 26 [33554432],
    mm32M 1 1977991 1 16 26 [33554432], ⟨1, 1764052, 1, 16, []⟩, ⟨1, 3566998, 1, 20, []⟩,
    mm32M 1 1783499 1 16 33 [8522825728], mm32M 1 1783500 1 16 33 [8522825728],
    mm32M 1 3566998 1 20 27 [67108864], ⟨1, 1783499, 1, 16, []⟩, ⟨1, 1783500, 1, 16, []⟩,
    ⟨1, 1783499, 1, 16, []⟩, mm32M 1 1783500 1 16 28 [134217728],
    mm32M 1 1783500 1 16 31 [1073741824], mm32M 1 1783500 1 16 31 [1073741824],
    mm32M 1 2246873 1 17 28 [134217728], mm32M 1 2246874 1 17 28 [134217728],
    ⟨1, 2246873, 1, 17, []⟩, mm32M 1 2246874 1 17 31 [1073741824], ⟨1, 2246873, 1, 17, []⟩,
    ⟨1, 2246873, 1, 17, []⟩, ⟨1, 2246873, 1, 17, []⟩, ⟨1, 2246873, 1, 17, []⟩,
    mm32M 1 3409366 1 19 31 [1073741824], mm32M 1 3409366 1 19 31 [1073741824],
    mm32M 1 3409348 1 19 31 [1073741824], mm32M 1 3409349 1 19 31 [1073741824],
    mm32M 1 3409315 1 19 31 [1073741830], mm32M 1 3409316 1 19 31 [1073741882],
    mm32M 1 3409195 1 19 8 [222], mm32M 1 3409196 1 19 10 [821], mm32M 2 1934290 1 19 12 [3197],
    mm32M 2 2249305 1 20 32 [2147489484], mm32M 2 2242960 1 20 32 [2147515933],
    mm32M 2 2223423 1 20 32 [2147521922], mm32M 2 2259200 1 20 18 [132726],
    mm32M 2 2135883 1 19 19 [398965], mm32M 2 2296005 1 20 20 [808305],
    mm32M 2 2306003 1 20 21 [1098420], mm32M 2 2631654 1 21 22 [3283101],
    mm32M 2 1329443 1 17 23 [5374570], mm32M 2 1195770 1 16 23 [4262859],
    mm32M 2 1268491 1 16 24 [8392049], mm32M 2 1100894 1 16 24 [8715641],
    mm32M 2 1433360 1 17 25 [18891972], mm32M 2 939441 1 15 25 [19371381],
    mm32M 2 2484060 1 20 26 [39453429], mm32M 2 1929188 1 19 26 [34386564],
    mm32M 2 2479499 1 20 26 [61207189], mm32M 2 2469585 1 20 28 [203008116],
    mm32M 2 2836139 1 22 26 [33645749], mm32M 2 2180870 1 20 29 [274242959],
    mm32M 2 2665456 1 21 25 [30428113], mm32M 2 2199128 1 20 30 [559763269],
    mm32M 2 2440126 1 20 29 [268579976], mm32M 2 857135 1 15 26 [37925306],
    mm32M 2 1391447 1 17 31 [1116020532], mm32M 2 1531827 1 17 31 [2100128003],
    mm32M 2 561475 1 13 24 [8742503], mm32M 2 1036935 1 15 29 [312032288],
    mm32M 2 1266364 1 16 31 [1083528161], mm32M 2 2100165 1 19 13 [7596] ]
private def mm32RowR32 : List ℕ :=
  [ 0, 0, 0, 0, 0, 14, 24, 85, 781, 63, 2, 15569, 1246, 37012, 10176, 441783, 1483432, 2635075,
    754717, 1381826, 70226937, 1205886, 2806989, 9539480, 9527909, 361122544, 109310595,
    81209446, 21686336, 93894892, 18764460671, 980468246217 ]
private def mm32SgsR64S0 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 5037937, 1, 27, []⟩, ⟨1, 7678061, 1, 33, []⟩, ⟨1, 3952117, 1, 25, []⟩,
    ⟨1, 7371969, 1, 32, []⟩, ⟨1, 3540669, 1, 23, []⟩, ⟨1, 7340928, 1, 32, []⟩,
    ⟨1, 3670463, 1, 24, []⟩, ⟨1, 7340928, 1, 32, []⟩, ⟨1, 2556859, 1, 21, []⟩,
    ⟨1, 2557904, 1, 21, []⟩, ⟨2, 1387241, 1, 20, []⟩,
    mm32M 2 2082536 1 24 56 [36028797018963968], mm32M 2 1976256 1 23 57 [0, 1],
    mm32M 2 2060624 1 24 57 [0, 1], mm32M 2 2060624 1 24 63 [53, 64],
    mm32M 2 2060624 1 24 7 [104], mm32M 2 2076624 1 24 63 [51, 64],
    mm32M 2 2036692 1 23 63 [15415, 64], mm32M 2 2036692 1 23 63 [117366, 64],
    mm32M 2 2036693 1 23 63 [416453, 64], mm32M 2 2021000 1 23 63 [3312867, 64],
    mm32M 2 2021001 1 23 24 [13972779], mm32M 2 2021003 1 23 27 [105176167],
    mm32M 2 2019121 1 23 63 [411516548, 64], mm32M 3 1511126 1 23 63 [1691112623, 64],
    mm32M 3 1328092 1 22 63 [3353096543, 64], mm32M 3 1240971 1 22 63 [14876345860, 64],
    mm32M 3 1255882 1 22 63 [25664677594, 64], mm32M 3 1248012 1 22 63 [121509147028, 64],
    mm32M 3 1260584 1 22 38 [254931712889], mm32M 3 1285862 1 22 39 [375480719907],
    mm32M 3 1008083 1 20 64 [726462103225, 128], mm32M 3 1279391 1 22 41 [1157581495100],
    mm32M 3 1347366 1 22 64 [7115289731060, 128], mm32M 3 1238142 1 22 64 [8798260552750, 128] ]
private def mm32SgsR64S1 : List DickeSol.Rkm128kSeg :=
  [ mm32M 3 1204546 1 21 64 [23387215724363, 128],
    mm32M 3 1230614 1 22 64 [65988214556049, 128],
    mm32M 3 1273696 1 22 64 [72614610310348, 128],
    mm32M 3 1280620 1 22 64 [165004508930984, 128],
    mm32M 4 1032338 1 22 64 [318366162946317, 128],
    mm32M 4 1055440 1 22 64 [1061950284750160, 128],
    mm32M 4 1233987 1 23 65 [1993195947668640, 256],
    mm32M 4 1107752 1 22 65 [2012110710495417, 256],
    mm32M 4 1050336 1 22 65 [7109243320650748, 256], mm32M 4 1444764 1 25 54 [9044657804288167],
    mm32M 4 1388775 1 24 55 [22946621352007333], mm32M 4 1441793 1 25 56 [46408232378705385],
    mm32M 4 1011816 1 21 56 [41108860417631416], mm32M 4 999935 1 21 56 [36453274271556596],
    mm32M 4 1219556 1 23 58 [4242033575391048, 2], mm32M 4 870435 1 20 55 [27216235557553282],
    mm32M 4 947414 1 21 55 [31621102534880802], mm32M 4 870260 1 20 57 [32140929933791119, 1],
    mm32M 4 1005078 1 21 48 [144487376311960], mm32M 4 945345 1 21 59 [4583943590437162, 4],
    mm32M 4 975162 1 21 61 [59354247259020735, 24], mm32M 4 1492930 1 25 48 [260309984379209],
    mm32M 4 899487 1 21 49 [326094689929811], mm32M 4 992612 1 21 62 [281598354353262, 37],
    mm32M 4 1201379 1 23 53 [4574284782203632],
    mm32M 4 1337171 1 24 63 [26389607756284293, 105],
    mm32M 4 1114670 1 22 63 [3797050824493914, 96],
    mm32M 4 963996 1 21 58 [31957892293029754, 3], mm32M 4 873957 1 20 37 [95521396444] ]
private abbrev mm32SgsR64 : List DickeSol.Rkm128kSeg :=
  mm32SgsR64S0 ++ mm32SgsR64S1
private def mm32StR64S1V0 : List ℤ :=
  [ mm32P 2904003, mm32P 2065337, mm32N 11062037, mm32N 20388750, mm32N 2792416, mm32P 22254606,
    mm32N 83278632, mm32N 62108643, mm32N 13819632, mm32N 405104418, mm32N 1380859351,
    mm32N 1025553987, mm32N 1110310700, mm32P 1207867053, mm32P 1883528294, mm32P 1858635841,
    mm32P 5856797114, mm32P 10779004216, mm32N 2299793173, mm32N 12674933380, mm32N 16635327825,
    mm32P 50796012861, mm32N 83739044094, mm32P 98161895467, mm32P 22348211166,
    mm32N 29909842802, mm32P 291921165936, mm32P 1153550062560, mm32P 1382016615308,
    mm32P 388466544596, mm32N 1832735656310, mm32P 1191153835149, mm32P 4159575475643,
    mm32N 2250016313103, mm32N 3124087493897, mm32P 2881201600100, mm32P 1696885615353,
    mm32N 2366151878376, mm32P 3966141101230, mm32N 2331767950518, mm32P 6648883652525,
    mm32P 9378278367161, mm32P 2064719655621, mm32P 4828013238629, mm32P 38040456051775,
    mm32P 139497036383447, mm32P 273568791791067, mm32P 396000289876349, mm32P 465708708590333,
    mm32P 464143542312112, mm32P 400882268931483, mm32P 304001943741218, mm32P 204014593862390,
    mm32P 121725189854445, mm32P 64717284577620, mm32P 30671431993166, mm32P 12939155713888,
    mm32P 4843020264097, mm32P 1599564512391, mm32P 462346349087, mm32P 115514658530,
    mm32P 24471207465, mm32P 4320793344, mm32N 263119162 ]
private def mm32StR64S1V1 : List ℤ :=
  [ mm32P 11836368 ]
private def mm32StR64S1 : Mm32St :=
  (3, 64, 163892, mm32StR64S1V0 ++ mm32StR64S1V1)
private def mm32StR64S2V0 : List ℤ :=
  [ mm32N 41743, mm32P 759209, mm32N 924841, mm32P 690396, mm32N 7061191, mm32P 14566196,
    mm32N 8711699, mm32N 31543155, mm32P 98982822, mm32P 598838, mm32N 666918, mm32P 15496447,
    mm32P 45720378, mm32P 133531318, mm32P 52202145, mm32N 437292192, mm32N 169705276,
    mm32P 2022693178, mm32N 4307034868, mm32N 5252137297, mm32P 35936807787, mm32P 630186182,
    mm32P 1949274327, mm32P 943960313, mm32N 71196463, mm32P 3467291314, mm32P 2149769054,
    mm32P 5522759110, mm32P 2506456693, mm32P 11155733247, mm32N 6913608642, mm32P 88805542795,
    mm32N 828184804595, mm32N 47310131871, mm32N 78457653382, mm32P 59209067293,
    mm32P 249443205063, mm32N 1301721625317, mm32P 387368137794, mm32P 709344509359,
    mm32N 1126051575459, mm32N 2112575595199, mm32N 800241574928, mm32P 1115028511661,
    mm32P 2362282130333, mm32N 3860886812587, mm32N 11698752784575, mm32P 1255260605518,
    mm32N 4012676449289, mm32P 1301163458013, mm32P 8406417042758, mm32P 2652457084343,
    mm32N 5789643904083, mm32P 3468607625275, mm32N 7566033480153, mm32P 26288411813829,
    mm32P 26700452815188, mm32N 7576021757246, mm32P 32150712356523, mm32N 30792981404505,
    mm32P 46521192477229, mm32P 34730435386059, mm32N 13950217874864, mm32P 138628144144335 ]
private def mm32StR64S2V1 : List ℤ :=
  [ mm32P 986613393635545 ]
private def mm32StR64S2 : Mm32St :=
  (4, 64, 308224, mm32StR64S2V0 ++ mm32StR64S2V1)
private def mm32RowR64 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 18, 27, 1291, 0, 3, 0, 0, 12, 4, 30, 6,
    124, 47, 7886, 685889, 2238, 6155, 3505, 62221, 1694478, 150053, 503169, 1267991, 4462974,
    640386, 1243287, 5580375, 14906444, 136860809, 1575678, 16101569, 1693025, 70667842,
    7035526, 33519972, 12031236, 57244857, 691080579, 712914164, 57396100, 1033668285,
    948207684, 2164221320, 1206203120, 194608570, 19217762263, 973405987892 ]
private def mm32SgsR128S0 : List DickeSol.Rkm128kSeg :=
  [ ⟨1, 5249695, 1, 34, []⟩, ⟨1, 3595001, 1, 28, []⟩, ⟨1, 3806219, 1, 29, []⟩,
    ⟨1, 3807640, 1, 29, []⟩, ⟨1, 3807640, 1, 29, []⟩, ⟨1, 3807640, 1, 29, []⟩,
    ⟨1, 3807640, 1, 29, []⟩, mm32M 1 3807640 1 29 33 [8589934591], ⟨1, 1698198, 1, 21, []⟩,
    ⟨2, 793046, 1, 20, []⟩, mm32M 2 1075323 1 22 65 [0, 432], mm32M 2 1060966 1 22 63 [0, 96],
    mm32M 2 1060966 1 22 64 [0, 128], ⟨2, 1060966, 1, 22, []⟩, mm32M 2 1060966 1 22 1 [1],
    mm32M 2 1060966 1 22 2 [2], ⟨2, 1060966, 1, 22, []⟩, ⟨2, 1060966, 1, 22, []⟩,
    mm32M 2 1060966 1 22 4 [15], mm32M 2 1060966 1 22 9 [369], mm32M 2 1060966 1 22 10 [598],
    mm32M 2 1060966 1 22 8 [196], mm32M 2 1060966 1 22 9 [366], mm32M 2 1060966 1 22 16 [32903],
    mm32M 3 915831 1 24 95 [92200, 480802570244],
    mm32M 3 914977 1 24 97 [233674, 1223260241920],
    mm32M 3 884768 1 24 96 [660752, 591657304064],
    mm32M 3 955193 1 24 97 [8071729, 1716828241920],
    mm32M 3 955192 1 24 96 [17532505, 1010445582336],
    mm32M 3 939231 1 24 97 [25743321, 2100628029440],
    mm32M 3 940409 1 24 97 [1741836731, 2038716956672],
    mm32M 3 1015445 1 25 97 [14345461142, 1443205480448],
    mm32M 3 1000662 1 25 96 [47858468858, 709844008960],
    mm32M 3 992135 1 25 97 [493719605031, 1661481254912],
    mm32M 4 765803 1 24 127 [1819876555105, 43248103662288896, 16395],
    mm32M 4 766090 1 24 127 [8532376260802, 52825850936033280, 26620] ]
private def mm32SgsR128S1 : List DickeSol.Rkm128kSeg :=
  [ mm32M 4 758164 1 24 129 [12643459322499, 14367548220899328, 94708],
    mm32M 4 773873 1 24 126 [139072612473827, 36742038615490560, 14876],
    mm32M 4 766385 1 24 128 [386722163485803, 42411981709246464, 64182],
    mm32M 4 766814 1 24 129 [1822813003305186, 51252523348000768, 127347],
    mm32M 4 767977 1 24 129 [7810922504043287, 57417596714090496, 98949],
    mm32M 4 767262 1 24 128 [19685834790046027, 42966715390230528, 38824],
    mm32M 4 760775 1 24 129 [44089230635639168, 57447283528040449, 70156],
    mm32M 4 737008 1 24 127 [65315669370212335, 22940210601918466, 17561],
    mm32M 4 775590 1 24 127 [29381931670338459, 28182679895670798, 19953],
    mm32M 4 786927 1 25 129 [53384014309875028, 7670184525430842, 97620],
    mm32M 4 759567 1 24 129 [39444466888339769, 16184811160862921, 95606],
    mm32M 5 628662 1 24 129 [12507732649982021, 58546795155816869, 92844],
    mm32M 5 627945 1 24 125 [13882786993139709, 4503582447503253, 7111],
    mm32M 5 593171 1 23 128 [13384884187955555, 36028728299489308, 46809],
    mm32M 5 622404 1 24 129 [19214138868873482, 72057559678202200, 104789],
    mm32M 5 606714 1 24 128 [27504109028277504, 72057456599003147, 47095],
    mm32M 5 613946 1 24 127 [23008086676718562, 67140, 18440],
    mm32M 5 598899 1 23 127 [30394001284192421, 208830, 26632],
    mm32M 5 644278 1 24 127 [96995177216433, 524586, 18448] ]
private def mm32SgsR128S2 : List DickeSol.Rkm128kSeg :=
  [ mm32M 5 590050 1 23 128 [39172935120214052, 1617083, 59408],
    mm32M 5 674216 1 25 128 [30588648118860607, 6594888, 34848],
    mm32M 5 485669 1 22 127 [70570461006580009, 13660248, 18432],
    mm32M 6 449597 1 22 124 [23597397833428200, 25240769, 2048],
    mm32M 6 479311 1 23 125 [19720197567149163, 38143780, 4096],
    mm32M 6 527856 1 23 129 [35414370114293903, 67141987, 122880],
    mm32M 6 513252 1 23 129 [8054006710958514, 140737952157891, 70144],
    mm32M 6 459844 1 22 126 [13001429924327478, 823148680, 8192],
    mm32M 6 467088 1 22 127 [67862788704162626, 562951627332935, 29184],
    mm32M 6 514821 1 23 129 [18375059166170622, 562952445900867, 94208],
    mm32M 6 552957 1 24 128 [10850580288438513, 6010988546, 32768],
    mm32M 6 577490 1 24 129 [802288122187075, 19464997917, 65536],
    mm32M 6 480011 1 23 126 [70364211972617524, 54686939511, 8192],
    mm32M 6 462894 1 22 129 [64223959126229575, 121469174289, 90144],
    mm32M 6 475504 1 23 129 [41995899946926406, 244348817701, 123936],
    mm32M 6 478314 1 23 127 [27373800151843264, 274924555296, 24576],
    mm32M 7 418632 1 22 129 [16810092493925333, 36029379200639035, 106496],
    mm32M 7 826897 1 30 126 [25347113109952972, 3135359992393, 8448],
    mm32M 7 803309 1 29 126 [61037593135257866, 15668463266175, 8454] ]
private def mm32SgsR128S3 : List DickeSol.Rkm128kSeg :=
  [ mm32M 7 496232 1 24 129 [316160930331200, 17870625439887, 98316],
    mm32M 7 473789 1 23 129 [865328800726197, 57217722757386, 114688],
    mm32M 7 516006 1 24 129 [42925711824929129, 101184443396175, 66048],
    mm32M 7 473617 1 23 128 [11564765982139295, 195740266325140, 49152],
    mm32M 7 583986 1 25 128 [8103158876689028, 83606124691630, 32768],
    mm32M 7 376699 1 21 127 [35724800871183191, 800742652196502, 16384],
    mm32M 7 573299 1 25 127 [19964148003029890, 1169898810757127, 16384],
    mm32M 7 429486 1 23 127 [38181722016445466, 2859864179439231, 16384],
    mm32M 7 709472 1 28 127 [18781886255308324, 5749984434322120, 16384],
    mm32M 7 512213 1 24 110 [56440120380575975, 12493510647398601],
    mm32M 7 435740 1 23 111 [27611728456485003, 21467168384074646],
    mm32M 7 779408 1 29 128 [53818496902515655, 33849016626158054, 32768],
    mm32M 7 509599 1 24 110 [476908633488240, 9535103900770358],
    mm32M 8 431540 1 23 129 [10809581431667985, 392840361931483, 98307],
    mm32M 8 602736 1 27 129 [59551152988592337, 20834237318219831, 98304],
    mm32M 8 686653 1 28 128 [22226449662204865, 18139883630527447, 32776],
    mm32M 8 669305 1 28 117 [10945383736855807, 33682714220217110, 16],
    mm32M 8 779419 1 30 118 [51686273752052306, 18303683659113250, 38] ]
private def mm32SgsR128S4 : List DickeSol.Rkm128kSeg :=
  [ mm32M 8 655424 1 28 119 [41466178245657564, 10414915041013388, 64],
    mm32M 8 890945 1 32 117 [7607763134169877, 36046423795480065, 18],
    mm32M 8 671761 1 28 113 [10029666546307115, 19142755260197351, 1],
    mm32M 8 620581 1 27 122 [20327155373017723, 13546317576404398, 560],
    mm32M 8 589543 1 26 118 [18961357287970156, 175922407843341, 40],
    mm32M 8 374444 1 22 119 [32792633080032502, 3450596876479078, 100],
    mm32M 8 718323 1 29 124 [3956381315202856, 10984716126474942, 2576],
    mm32M 8 325958 1 21 118 [24937615109497589, 12658603748219, 48],
    mm32M 8 627124 1 27 125 [29113689701655086, 52236712687182374, 6309],
    mm32M 8 420711 1 23 125 [71076298474390070, 25229576368294260, 4128],
    mm32M 8 677328 1 28 117 [44064742160643939, 633537030186466, 20],
    mm32M 8 792925 1 30 126 [10441161811916233, 21226499503903807, 10343],
    mm32M 8 618079 1 27 120 [41000041029528230, 18876415911023280, 164],
    mm32M 8 834492 1 31 127 [23330320426334952, 10550736446331216, 18366],
    mm32M 8 724564 1 29 127 [41664282569790767, 174936790780930, 18737],
    mm32M 8 657195 1 28 126 [12138316756838304, 5418485256744105, 8210] ]
private abbrev mm32TlR128S3 : List DickeSol.Rkm128kSeg :=
  mm32SgsR128S3 ++ mm32SgsR128S4
private abbrev mm32TlR128S2 : List DickeSol.Rkm128kSeg :=
  mm32SgsR128S2 ++ mm32TlR128S3
private abbrev mm32TlR128S1 : List DickeSol.Rkm128kSeg :=
  mm32SgsR128S1 ++ mm32TlR128S2
private abbrev mm32SgsR128 : List DickeSol.Rkm128kSeg :=
  mm32SgsR128S0 ++ mm32TlR128S1
private def mm32StR128S1V0 : List ℤ :=
  [ mm32N 2196550, mm32P 2117806, mm32P 12929461, mm32N 27300619, mm32N 191692133,
    mm32N 483454613, mm32P 113407264, mm32P 74724904, mm32N 265572595, mm32N 162205522,
    mm32P 318501936, mm32P 4222008, mm32P 225505736, mm32P 569666926, mm32P 1325867368,
    mm32P 895600896, mm32N 544949432, mm32P 8022000, mm32P 4407281190, mm32P 1580727259,
    mm32P 2005727164, mm32N 239899865, mm32P 604248585, mm32N 1177495531, mm32P 3466860619,
    mm32P 5568796126, mm32N 9098954981, mm32N 15669339814, mm32P 5828488678, mm32N 2714467242,
    mm32N 17043782597, mm32N 40427909593, mm32N 37017033362, mm32N 36367149272,
    mm32N 8850598184, mm32N 59623357049, mm32N 44231152594, mm32P 87403206108,
    mm32N 141509487316, mm32P 7159635973, mm32P 210669194317, mm32N 111964886430,
    mm32N 278129400327, mm32N 850351476574, mm32N 5099551363328, mm32N 15275045110754,
    mm32N 34813298843453, mm32N 66775768105674, mm32N 112431163721619, mm32N 169943271668802,
    mm32N 233820497763201, mm32N 295588823994121, mm32N 345661924672315, mm32N 375826830845914,
    mm32N 381442098443606, mm32N 362546995789436, mm32N 323544484401917, mm32N 271697762336035,
    mm32N 215089568364796, mm32N 160772887547019, mm32N 113618129308844, mm32N 76001758537295,
    mm32N 48169394612942, mm32N 28950778889214 ]
private def mm32StR128S1V1 : List ℤ :=
  [ mm32N 16512333907171, mm32N 8943109797214, mm32N 4601867795350, mm32N 2250824589203,
    mm32N 1046809567630, mm32N 463043919266, mm32N 194832090734, mm32N 77979015581,
    mm32N 29683072127, mm32N 10743240338, mm32N 3695711899, mm32N 1207856878, mm32N 374885867,
    mm32N 110451247, mm32N 30880505, mm32N 8190769, mm32N 2060172, mm32N 490823, mm32N 110447,
    mm32N 23544, mm32N 4448, mm32P 701, mm32P 90, mm32P 8, mm32P 0, mm32P 0, mm32P 0, mm32P 0,
    mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0,
    mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0,
    mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0,
    mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0 ]
private def mm32StR128S1V2 : List ℤ :=
  [ mm32P 0 ]
private def mm32StR128S1 : Mm32St :=
  (4, 128, 280840, mm32StR128S1V0 ++ (mm32StR128S1V1 ++ mm32StR128S1V2))
private def mm32StR128S2V0 : List ℤ :=
  [ mm32P 2573674, mm32P 444016, mm32N 3532959, mm32N 20220458, mm32N 10382282, mm32P 7787271,
    mm32P 88064419, mm32N 74377922, mm32P 17050419, mm32P 119878252, mm32N 174256158,
    mm32P 7886914, mm32N 10064797, mm32P 149927285, mm32P 133373294, mm32P 772470392,
    mm32N 348087292, mm32N 1055824643, mm32P 456227387, mm32P 175473126, mm32N 1109241918,
    mm32N 3610705806, mm32P 3661910970, mm32P 3162251279, mm32P 7553136637, mm32N 4939485755,
    mm32P 16537300511, mm32N 10515544891, mm32N 14727556190, mm32P 7747687759,
    mm32N 33934027670, mm32N 36608409346, mm32N 65369965514, mm32N 32016484958,
    mm32P 71410416135, mm32N 5640625370, mm32N 83331812955, mm32N 87137172075,
    mm32N 66469274403, mm32N 295622550317, mm32P 279603786995, mm32P 227274627616,
    mm32N 358322971843, mm32P 789890799157, mm32P 428082666297, mm32N 851513886559,
    mm32P 144757559748, mm32P 409842222716, mm32N 921259975091, mm32N 602886517407,
    mm32N 597126370645, mm32N 639552349430, mm32N 1492527051157, mm32N 409156229220,
    mm32N 1123376175345, mm32N 1635861584858, mm32N 2551056176561, mm32P 720068927482,
    mm32P 2113291562069, mm32P 79422091309, mm32N 3716258873508, mm32N 266977015978,
    mm32N 1291485847813, mm32N 4335498648661 ]
private def mm32StR128S2V1 : List ℤ :=
  [ mm32N 5430197519578, mm32P 2452784709938, mm32P 3574332699427, mm32N 1551927859648,
    mm32N 929915783109, mm32N 3645640501240, mm32N 5928945342733, mm32N 1497608751017,
    mm32P 4858216110716, mm32N 4904609147892, mm32P 3174412673340, mm32N 3786219065218,
    mm32N 25974623965474, mm32N 89460018635478, mm32N 176673558748198, mm32N 269937619510723,
    mm32N 349556407178351, mm32N 399921551266296, mm32N 413292588380033, mm32N 391394242394745,
    mm32N 342626474564664, mm32N 279170664603234, mm32N 213045089641413, mm32N 151962958459813,
    mm32N 102910524341993, mm32N 65327728376602, mm32N 38867177125766, mm32N 22482527594479,
    mm32N 12425345656213, mm32N 6145782250586, mm32N 2622316719872, mm32N 979818790695,
    mm32N 340130232584, mm32N 119129971662, mm32N 44450039496, mm32N 17421126196,
    mm32N 6816819324, mm32N 2559729440, mm32N 906253518, mm32N 301304729, mm32N 94216917,
    mm32N 27782959, mm32N 7740525, mm32N 2038533, mm32N 507059, mm32N 118895, mm32N 26203,
    mm32N 5400, mm32N 1027, mm32N 171, mm32N 22, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0,
    mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0, mm32P 0 ]
private def mm32StR128S2V2 : List ℤ :=
  [ mm32P 0 ]
private def mm32StR128S2 : Mm32St :=
  (5, 128, 535233, mm32StR128S2V0 ++ (mm32StR128S2V1 ++ mm32StR128S2V2))
private def mm32StR128S3V0 : List ℤ :=
  [ mm32P 1191925, mm32N 866281, mm32P 1261147, mm32P 315146, mm32P 1122930, mm32N 1529593,
    mm32N 10158127, mm32N 18141464, mm32N 24115901, mm32P 23615501, mm32P 57429584,
    mm32P 40939488, mm32P 113987933, mm32P 70428851, mm32N 152873006, mm32N 87779571,
    mm32P 446231701, mm32P 830507677, mm32P 416278238, mm32P 165161922, mm32P 79859793,
    mm32N 659844074, mm32N 1484593724, mm32N 1753268363, mm32P 1063587462, mm32P 2905621662,
    mm32P 6344448831, mm32N 14321380194, mm32N 13324565323, mm32P 38154212839, mm32P 8927473014,
    mm32N 15702385895, mm32N 21710930248, mm32N 80001209831, mm32P 16026013277,
    mm32N 153893446293, mm32P 48471521909, mm32N 71655738318, mm32P 81634339363,
    mm32N 117019139795, mm32N 16972853875, mm32N 120057446463, mm32P 287623105955,
    mm32P 480983886769, mm32N 194632189386, mm32N 376098052039, mm32P 141861792297,
    mm32P 244066806704, mm32N 784758041159, mm32P 104681167685, mm32P 1053543325112,
    mm32P 574435210240, mm32N 431209298634, mm32N 958798717595, mm32N 1371108113693,
    mm32P 93803209315, mm32N 583493740499, mm32N 3121698378876, mm32N 312313578714,
    mm32P 1269669597564, mm32P 2520341482927, mm32P 2243348421954, mm32N 2078889143746,
    mm32N 2416763568556 ]
private def mm32StR128S3V1 : List ℤ :=
  [ mm32P 809122328021, mm32P 1484477659882, mm32P 1514220186339, mm32N 2318489615340,
    mm32N 370179943213, mm32P 2277396998299, mm32P 4592702504321, mm32N 1143352812658,
    mm32N 3015642564361, mm32P 1872264819883, mm32N 2413301361485, mm32P 707213544786,
    mm32P 815381998204, mm32N 2301992964375, mm32P 6647456614316, mm32P 5199224611787,
    mm32N 6867766663230, mm32P 3345478273743, mm32P 2234198929022, mm32P 887328585685,
    mm32N 4072984399452, mm32P 11770218740521, mm32P 3412374354778, mm32P 3482072764571,
    mm32N 954397989369, mm32P 3729569579320, mm32P 11625760861049, mm32P 3865428957136,
    mm32P 2046570735061, mm32N 2296831914284, mm32P 3506069774952, mm32N 6355575571248,
    mm32P 8690318554325, mm32N 2103019190653, mm32N 12907404249749, mm32N 7287039716596,
    mm32N 55840680471640, mm32N 173480230002713, mm32N 303399448404542, mm32N 403701694211094,
    mm32N 451526625642972, mm32N 440190283031578, mm32N 381856953155007, mm32N 298016267445481,
    mm32N 217882652705277, mm32N 140758544352260, mm32N 90048115849768, mm32N 50811873156612,
    mm32N 22360231813033, mm32P 7833712424981, mm32P 2498788680085, mm32N 857218897672,
    mm32N 325508791178, mm32N 124056201628, mm32N 43637148183, mm32N 14213789725,
    mm32P 3075243552, mm32N 481574354, mm32N 86778353, mm32N 21470596, mm32N 5103916,
    mm32P 758393, mm32N 71926, mm32N 5346 ]
private def mm32StR128S3V2 : List ℤ :=
  [ mm32N 328 ]
private def mm32StR128S3 : Mm32St :=
  (7, 128, 836100, mm32StR128S3V0 ++ (mm32StR128S3V1 ++ mm32StR128S3V2))
private def mm32StR128S4V0 : List ℤ :=
  [ mm32N 629727, mm32P 624604, mm32P 27466, mm32P 486942, mm32P 1170435, mm32P 2266427,
    mm32N 198322, mm32P 6700231, mm32P 656261, mm32P 728533, mm32P 12286110, mm32P 62636744,
    mm32P 70729788, mm32P 6828622, mm32P 12213066, mm32P 86346470, mm32P 70465613,
    mm32P 603980702, mm32P 294362404, mm32P 30190249, mm32P 145158231, mm32P 636273687,
    mm32P 96240442, mm32P 748590230, mm32P 1056842192, mm32P 1297205665, mm32P 2542110693,
    mm32P 4327849177, mm32P 2424186811, mm32N 218138228, mm32N 2687606458, mm32N 10183520845,
    mm32N 2518287382, mm32P 43307189574, mm32P 40607275013, mm32P 18430192171,
    mm32P 52503622355, mm32N 54418906114, mm32N 87880854410, mm32N 42186673970,
    mm32P 225965496713, mm32N 215538167643, mm32P 225596646739, mm32N 106985122776,
    mm32P 99050917919, mm32P 177484856966, mm32P 148435038685, mm32N 112439586759,
    mm32P 434996581497, mm32P 322138997139, mm32N 329316867713, mm32N 1326804155080,
    mm32N 39297703103, mm32N 198194574479, mm32N 1097258408254, mm32P 507379920474,
    mm32N 240305386982, mm32P 1870285247360, mm32P 102994153717, mm32N 4290969031887,
    mm32N 2521143539120, mm32P 407539208591, mm32P 225756965831, mm32P 4133043233285 ]
private def mm32StR128S4V1 : List ℤ :=
  [ mm32N 547815727541, mm32P 738548241370, mm32N 980720959570, mm32N 83162218136,
    mm32N 1525508153284, mm32N 1831281011085, mm32P 5113120178755, mm32N 2178974310651,
    mm32N 571274141897, mm32N 906262663801, mm32P 106161428499, mm32N 234364065006,
    mm32P 746779606595, mm32P 205732604892, mm32P 1342144402494, mm32N 471829704789,
    mm32P 4057913910324, mm32P 888320860120, mm32P 3907436796058, mm32P 3619970156135,
    mm32P 960806081298, mm32N 401501708523, mm32N 783183966626, mm32P 5194688381964,
    mm32P 13162421980599, mm32P 3545370271291, mm32P 6986614987285, mm32P 10001329069741,
    mm32P 9459330730682, mm32N 3812347403802, mm32P 5196854813583, mm32N 4518928335919,
    mm32N 3889464945598, mm32P 3153262988848, mm32N 4135611300983, mm32P 2768149856347,
    mm32P 7085210965274, mm32P 8098763809002, mm32P 5777239184321, mm32N 5955176452142,
    mm32N 5151535090924, mm32N 1526530253064, mm32P 5708373360122, mm32P 6130230412903,
    mm32N 3182339824447, mm32N 10187323946900, mm32N 16879118484821, mm32N 19775991631157,
    mm32P 12336119273998, mm32N 20668037847333, mm32N 3233240709221, mm32N 11081309516763,
    mm32N 15580186253559, mm32N 19513801733201, mm32N 43640218888970, mm32N 227012719300629,
    mm32N 430716059175400, mm32N 540437650952815, mm32N 509897815252371, mm32N 378119650771200,
    mm32N 223953653126370, mm32N 105112130016442, mm32N 40002525758303, mm32N 9189001740133 ]
private def mm32StR128S4V2 : List ℤ :=
  [ mm32N 1080401578379 ]
private def mm32StR128S4 : Mm32St :=
  (8, 128, 1148551, mm32StR128S4V0 ++ (mm32StR128S4V1 ++ mm32StR128S4V2))
private def mm32StR128S5V0 : List ℤ :=
  [ mm32P 273753, mm32N 15977, mm32P 508532, mm32P 590691, mm32N 66785, mm32N 143508,
    mm32N 532776, mm32P 489196, mm32P 3128665, mm32N 3269675, mm32P 12518829, mm32P 16703837,
    mm32P 16517896, mm32N 29412176, mm32P 37032924, mm32P 20747630, mm32N 106418135,
    mm32N 6480126, mm32N 97605163, mm32P 58093726, mm32N 231207276, mm32N 129590537,
    mm32P 101252275, mm32P 290071353, mm32N 345389149, mm32P 621919864, mm32N 580082260,
    mm32P 787183149, mm32N 382093683, mm32P 24270022, mm32P 1072098095, mm32P 212408530,
    mm32N 732970548, mm32P 1610299500, mm32N 3540178563, mm32N 1748495067, mm32N 1954611590,
    mm32P 4944289594, mm32P 6079227402, mm32P 8348111890, mm32N 20246254045, mm32P 14536734001,
    mm32N 26359059923, mm32P 19780878187, mm32P 16076581850, mm32P 2528893099,
    mm32N 52794406917, mm32N 87420256583, mm32N 32015648260, mm32P 7682199556,
    mm32P 136022430527, mm32N 54984283294, mm32N 128594803141, mm32P 144333182132,
    mm32P 281603310203, mm32N 61394135161, mm32P 16793745627, mm32P 576007815232,
    mm32P 430900892307, mm32N 720261916321, mm32P 1103705246390, mm32P 5705200201163,
    mm32N 2983882759393, mm32N 3693224066715 ]
private def mm32StR128S5V1 : List ℤ :=
  [ mm32N 5927583670038, mm32N 94011405812, mm32N 31475836994, mm32P 129593320993,
    mm32N 168722518569, mm32N 26393823123, mm32N 273437106614, mm32N 136026975196,
    mm32N 122906189926, mm32P 276565085719, mm32N 123314962236, mm32P 60384483886,
    mm32N 53858509112, mm32P 92837071289, mm32P 268832934506, mm32P 79924951000,
    mm32N 481096268825, mm32N 10831837701, mm32P 127077161987, mm32N 371174341500,
    mm32P 60993789293, mm32N 1028782428674, mm32N 396084944061, mm32P 2157011789772,
    mm32P 1970460878234, mm32P 1654919905334, mm32P 2137410425157, mm32P 4430718663926,
    mm32N 6346167584060, mm32P 7282571174656, mm32P 15704318423360, mm32P 9913044023733,
    mm32P 11235534509727, mm32N 346879227405, mm32P 645269098381, mm32N 301727300057,
    mm32P 713540307448, mm32P 399857554783, mm32N 1241251242615, mm32N 102185632783,
    mm32P 820509316424, mm32N 2553691103790, mm32P 4769280832934, mm32P 9765679642081,
    mm32N 7336258973788, mm32P 5555305764869, mm32N 12037373164872, mm32P 31321148561149,
    mm32P 6593807036896, mm32N 2671996825320, mm32P 3196206124902, mm32N 3935732825091,
    mm32P 3874274832331, mm32N 11654854297069, mm32N 27182047145305, mm32P 40663897750594,
    mm32P 51886963607911, mm32N 22185391005274, mm32N 44831600022495, mm32N 17111920208383,
    mm32P 10471472417250, mm32P 5414420915213, mm32P 12273301957258, mm32N 137588029215599 ]
private def mm32StR128S5V2 : List ℤ :=
  [ mm32N 985210611034030 ]
private def mm32StR128S5 : Mm32St :=
  (8, 128, 1401266, mm32StR128S5V0 ++ (mm32StR128S5V1 ++ mm32StR128S5V2))
private def mm32RowR128 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 2, 12, 3, 3, 24, 36, 69, 409, 211, 694, 391, 258, 6, 2787, 7642, 1024, 58, 18501, 3023,
    16536, 20831, 79299, 3769, 281, 331783, 185674, 518775, 1218162, 32549293, 8903547,
    13639893, 35136231, 8837, 990, 16794, 28466, 696, 74767, 18502, 15105, 76487, 15206, 3646,
    2900, 8618, 72270, 6387, 231452, 117, 16148, 137769, 3720, 1058390, 156882, 4652693,
    3882710, 2738755, 4568517, 19631255, 40273825, 53035822, 246625573, 98268414, 126237204,
    120324, 416370, 91038, 509137, 159884, 1540701, 10441, 673233, 6521331, 22746026, 95368471,
    53820675, 30861406, 144898318, 981014259, 43478272, 7139559, 10215724, 15489981, 15009994,
    135835596, 738863610, 1653552466, 2692256847, 492191511, 2009872234, 292817765, 109651705,
    29315938, 150633906, 18930465397, 970639945332 ]
private theorem mm32_row_chunk_0 : mm32AtF [
    mm32ChkRow 3 mm32SgsR3 mm32RowR3,
    mm32ChkRow 4 mm32SgsR4 mm32RowR4,
    mm32ChkRow 5 mm32SgsR5 mm32RowR5,
    mm32ChkRow 6 mm32SgsR6 mm32RowR6,
    mm32ChkRow 7 mm32SgsR7 mm32RowR7,
    mm32ChkRow 8 mm32SgsR8 mm32RowR8,
    mm32ChkRow 16 mm32SgsR16 mm32RowR16
  ] = true := by
  decide +kernel
private theorem mm32_row_chunk_1 : mm32AtF [
    mm32ChkRow 32 mm32SgsR32 mm32RowR32
  ] = true := by
  decide +kernel
private theorem mm32_sl_r64_0 :
    mm32ChkSlice 64 mm32SgsR64S0 mm32InitSt mm32StR64S1 = true := by
  decide +kernel
private theorem mm32_sl_r64_1 :
    mm32ChkSlice 64 mm32SgsR64S1 mm32StR64S1 mm32StR64S2 = true := by
  decide +kernel
private theorem mm32_sl_r128_0 :
    mm32ChkSlice 128 mm32SgsR128S0 mm32InitSt mm32StR128S1 = true := by
  decide +kernel
private theorem mm32_sl_r128_1 :
    mm32ChkSlice 128 mm32SgsR128S1 mm32StR128S1 mm32StR128S2 = true := by
  decide +kernel
private theorem mm32_sl_r128_2 :
    mm32ChkSlice 128 mm32SgsR128S2 mm32StR128S2 mm32StR128S3 = true := by
  decide +kernel
private theorem mm32_sl_r128_3 :
    mm32ChkSlice 128 mm32SgsR128S3 mm32StR128S3 mm32StR128S4 = true := by
  decide +kernel
private theorem mm32_sl_r128_4 :
    mm32ChkSlice 128 mm32SgsR128S4 mm32StR128S4 mm32StR128S5 = true := by
  decide +kernel
private def mm32k128VPot : List ℕ :=
  [ 0, 113614219732884, 124738819287016, 135092352259273, 137825591068016, 140031357201941,
    142007011563067, 143881520964282, 145721941969064, 183593348546692, 219521319440568,
    253777295595384, 286574895768659, 318085810758563, 348450488223285, 377785553617806,
    162446640954208, 190002136750139, 216781265154253, 242846154752404, 268251066605737,
    293043721936656, 317266354971891, 340956557428045, 364147962917213, 386870806863790,
    409152388534544, 431017455316728, 452488524660575, 473586155615595, 494329179282612,
    514734895532273, 207368075563564, 227145772617900, 246630450554160, 265834758795142,
    284770462083956, 303448524751531, 321879184937263, 340072020189096, 358036005636034,
    375779565735758, 393310620443872, 410636626522592, 427764614600000, 444701222502222,
    461452725306651, 478025062502029, 494423862588667, 510654465407651, 526721942450120,
    542631115365554, 558386572860506, 573992686155606, 589453623148385, 604773361411941,
    619955700144302, 635004271170193, 649922549085459, 664713860624420, 679381393321681,
    693928203532290, 708357223867394, 722671270096626, 277007465327892, 291099574918021,
    305084518621396, 318964704717138, 332742452615104, 346419997380322, 359999493965517,
    373483021174417, 386872585376474, 400170123991804, 413377508763474, 426496548832784,
    439528993631860, 452476535606632, 465340812782213, 478123411181675, 490825867108342,
    503449669300885, 515996260969791, 528467041723078, 540863369388538, 553186561739220,
    565437898128362, 577618621039507, 589729937557125, 601773020762669, 613749011060628,
    625659017438826, 637504118666903, 649285364436652, 661003776447614, 672660349441113,
    684256052185697, 695791828416741, 707268597732790, 718687256451062, 730048678424351,
    741353715821442, 752603199873015, 763797941584876, 774938732420253, 786026344952785,
    797061533491716, 808045034680740, 818977568071832, 829859836675337, 840692527487501,
    851476311996566, 862211846668490, 872899773413275, 883540720032850, 894135300651389,
    904684116128899, 915187754458867, 925646791150709, 936061789597726, 946433301431235,
    956761866861498, 967048015006054, 977292264206012, 987495122330843, 997657087072177,
    1007778646227085, 1017860277971306, 378458665221668 ]
private def mm32k128Anchors : List DickeSol.RampKick128kAnchor :=
  [ ⟨3, mm32SgsR3, mm32RowR3⟩, ⟨4, mm32SgsR4, mm32RowR4⟩, ⟨5, mm32SgsR5, mm32RowR5⟩,
    ⟨6, mm32SgsR6, mm32RowR6⟩, ⟨7, mm32SgsR7, mm32RowR7⟩, ⟨8, mm32SgsR8, mm32RowR8⟩,
    ⟨16, mm32SgsR16, mm32RowR16⟩, ⟨32, mm32SgsR32, mm32RowR32⟩, ⟨64, mm32SgsR64, mm32RowR64⟩,
    ⟨128, mm32SgsR128, mm32RowR128⟩ ]
private theorem mm32k128_meta : mm32AtF [
    DickeSol.rkm128kCheckTable 32 128 8 true mm32k128VPot mm32k128Anchors,
    mm32ChkCell 4 2 356512242573879 1000000000000000 mm32k128VPot mm32k128Anchors,
    mm32ChkCell 8 2 240096513766043 1000000000000000 mm32k128VPot mm32k128Anchors,
    mm32ChkCell 16 2 43893601346917 250000000000000 mm32k128VPot mm32k128Anchors,
    mm32ChkCell 32 2 75118094154941 500000000000000 mm32k128VPot mm32k128Anchors,
    mm32ChkCell 64 4 68317558069959 500000000000000 mm32k128VPot mm32k128Anchors,
    mm32ChkCell 128 8 25702048974707 200000000000000 mm32k128VPot mm32k128Anchors,
    mm32SegsGuard 64 mm32SgsR64,
    mm32FinGuard mm32StR64S2 mm32RowR64,
    mm32SegsGuard 128 mm32SgsR128,
    mm32FinGuard mm32StR128S5 mm32RowR128
  ] = true := by
  decide +kernel
private theorem mm32_row_eq_r64 :
    DickeSol.rkm128kEvalRowLo12 32 8 64 mm32SgsR64 = mm32RowR64 :=
  mm32_cert_row 64 mm32SgsR64 mm32StR64S2 mm32RowR64
    (mm32_hd (mm32_tl1 (mm32_tl2 (mm32_tl4 mm32k128_meta))))
    (mm32_chain 64 mm32SgsR64S0 mm32SgsR64S1
      mm32InitSt mm32StR64S1 mm32StR64S2
      (mm32StEq_eq mm32_sl_r64_0)
      (mm32StEq_eq mm32_sl_r64_1))
    (mm32_hd (mm32_tl4 (mm32_tl4 mm32k128_meta)))
private theorem mm32_row_eq_r128 :
    DickeSol.rkm128kEvalRowLo12 32 8 128 mm32SgsR128 = mm32RowR128 :=
  mm32_cert_row 128 mm32SgsR128 mm32StR128S5 mm32RowR128
    (mm32_hd (mm32_tl1 (mm32_tl4 (mm32_tl4 mm32k128_meta))))
    (mm32_chain 128 mm32SgsR128S0 mm32TlR128S1
      mm32InitSt mm32StR128S1 mm32StR128S5
      (mm32StEq_eq mm32_sl_r128_0)
    (mm32_chain 128 mm32SgsR128S1 mm32TlR128S2
      mm32StR128S1 mm32StR128S2 mm32StR128S5
      (mm32StEq_eq mm32_sl_r128_1)
    (mm32_chain 128 mm32SgsR128S2 mm32TlR128S3
      mm32StR128S2 mm32StR128S3 mm32StR128S5
      (mm32StEq_eq mm32_sl_r128_2)
    (mm32_chain 128 mm32SgsR128S3 mm32SgsR128S4
      mm32StR128S3 mm32StR128S4 mm32StR128S5
      (mm32StEq_eq mm32_sl_r128_3)
      (mm32StEq_eq mm32_sl_r128_4)))))
    (mm32_hd (mm32_tl2 (mm32_tl4 (mm32_tl4 mm32k128_meta))))
private theorem mm32k128AnchorsSound : DickeSol.RampKick128kAnchorsSound 32 8 mm32k128Anchors :=
  ⟨mm32ListNatEq_eq (mm32_hd mm32_row_chunk_0),
    ⟨mm32ListNatEq_eq (mm32_hd (mm32_tl1 mm32_row_chunk_0)),
    ⟨mm32ListNatEq_eq (mm32_hd (mm32_tl2 mm32_row_chunk_0)),
    ⟨mm32ListNatEq_eq (mm32_hd (mm32_tl1 (mm32_tl2 mm32_row_chunk_0))),
    ⟨mm32ListNatEq_eq (mm32_hd (mm32_tl4 mm32_row_chunk_0)),
    ⟨mm32ListNatEq_eq (mm32_hd (mm32_tl1 (mm32_tl4 mm32_row_chunk_0))),
    ⟨mm32ListNatEq_eq (mm32_hd (mm32_tl2 (mm32_tl4 mm32_row_chunk_0))),
    ⟨mm32ListNatEq_eq (mm32_hd mm32_row_chunk_1),
    ⟨mm32_row_eq_r64,
    ⟨mm32_row_eq_r128,
    trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem mm32k128Valid :
    DickeSol.RampKick128kTableValid 32 128 8 true mm32k128VPot mm32k128Anchors :=
  DickeSol.rkm128kCheckTable_sound mm32k128AnchorsSound (mm32_hd mm32k128_meta)

private theorem mm32k128CellChecks {m k : ℕ}
    (h : isMidM32K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (midM32K128KrotovCertCellLMax m k) mm32k128Anchors = true ∧
      ∃ num den : ℕ, relCostMidM32K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (mm32k128VPot.getD k 0) num den = true := by
  unfold isMidM32K128KrotovCertCell at h
  split_ifs at h with hm32 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm32 hk4; have hm := mm32_hd (mm32_tl1 mm32k128_meta)
    exact ⟨mm32_and_l hm, 356512242573879, 1000000000000000, rfl, mm32_and_r hm⟩
  · subst hm32 hk8; have hm := mm32_hd (mm32_tl2 mm32k128_meta)
    exact ⟨mm32_and_l hm, 240096513766043, 1000000000000000, rfl, mm32_and_r hm⟩
  · subst hm32 hk16; have hm := mm32_hd (mm32_tl1 (mm32_tl2 mm32k128_meta))
    exact ⟨mm32_and_l hm, 43893601346917, 250000000000000, rfl, mm32_and_r hm⟩
  · subst hm32 hk32; have hm := mm32_hd (mm32_tl4 mm32k128_meta)
    exact ⟨mm32_and_l hm, 75118094154941, 500000000000000, rfl, mm32_and_r hm⟩
  · subst hm32 hk64; have hm := mm32_hd (mm32_tl1 (mm32_tl4 mm32k128_meta))
    exact ⟨mm32_and_l hm, 68317558069959, 500000000000000, rfl, mm32_and_r hm⟩
  · subst hm32 hk128; have hm := mm32_hd (mm32_tl2 (mm32_tl4 mm32k128_meta))
    exact ⟨mm32_and_l hm, 25702048974707, 200000000000000, rfl, mm32_and_r hm⟩

private lemma mm32k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma mm32k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma mm32k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private lemma mm32k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b :=
  h ▸ Nat.le_add_right a d

private lemma mm32k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (mm32k128_le_of_add h), rfl⟩

private structure Mm32k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ midM32K128KrotovCertCellLMax m k
  hl1 : 1 ≤ midM32K128KrotovCertCellLMax m k
  hlm : midM32K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 8 true mm32k128VPot mm32k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (midM32K128KrotovCertCellLMax m k)
    mm32k128Anchors = true
  hcost : ∃ num den : ℕ, relCostMidM32K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (mm32k128VPot.getD k 0) num den = true

private theorem mm32k128_all_props {m k : ℕ} (h : isMidM32K128KrotovCertCell m k = true) :
    Mm32k128CellProps m k := by
  rcases mm32k128CellChecks h with ⟨hlmax, hcost⟩
  unfold isMidM32K128KrotovCertCell at h
  split_ifs at h with hm32 hk4 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm32 hk4
    exact ⟨mm32k128_mem_grid 5 5 rfl, mm32k128_mem_grid 2 8 rfl,
      mm32k128_le_of_add (d := 124) rfl, mm32k128_le_of_add (d := 30) rfl,
      mm32k128_le_of_add (d := 0) rfl, mm32k128_le_of_add (d := 1) rfl,
      mm32k128_le_of_add (d := 65472) rfl, mm32k128Valid, hlmax, hcost⟩
  · subst hm32 hk8
    exact ⟨mm32k128_mem_grid 5 5 rfl, mm32k128_mem_grid 3 7 rfl,
      mm32k128_le_of_add (d := 120) rfl, mm32k128_le_of_add (d := 30) rfl,
      mm32k128_le_of_add (d := 0) rfl, mm32k128_le_of_add (d := 1) rfl,
      mm32k128_le_of_add (d := 65472) rfl, mm32k128Valid, hlmax, hcost⟩
  · subst hm32 hk16
    exact ⟨mm32k128_mem_grid 5 5 rfl, mm32k128_mem_grid 4 6 rfl,
      mm32k128_le_of_add (d := 112) rfl, mm32k128_le_of_add (d := 30) rfl,
      mm32k128_le_of_add (d := 0) rfl, mm32k128_le_of_add (d := 1) rfl,
      mm32k128_le_of_add (d := 65472) rfl, mm32k128Valid, hlmax, hcost⟩
  · subst hm32 hk32
    exact ⟨mm32k128_mem_grid 5 5 rfl, mm32k128_mem_grid 5 5 rfl,
      mm32k128_le_of_add (d := 96) rfl, mm32k128_le_of_add (d := 30) rfl,
      mm32k128_le_of_add (d := 0) rfl, mm32k128_le_of_add (d := 1) rfl,
      mm32k128_le_of_add (d := 65472) rfl, mm32k128Valid, hlmax, hcost⟩
  · subst hm32 hk64
    exact ⟨mm32k128_mem_grid 5 5 rfl, mm32k128_mem_grid 6 4 rfl,
      mm32k128_le_of_add (d := 64) rfl, mm32k128_le_of_add (d := 30) rfl,
      mm32k128_le_of_add (d := 2) rfl, mm32k128_le_of_add (d := 3) rfl,
      mm32k128_le_of_add (d := 65408) rfl, mm32k128Valid, hlmax, hcost⟩
  · subst hm32 hk128
    exact ⟨mm32k128_mem_grid 5 5 rfl, mm32k128_mem_grid 7 3 rfl,
      mm32k128_le_of_add (d := 0) rfl, mm32k128_le_of_add (d := 30) rfl,
      mm32k128_le_of_add (d := 6) rfl, mm32k128_le_of_add (d := 7) rfl,
      mm32k128_le_of_add (d := 65280) rfl, mm32k128Valid, hlmax, hcost⟩

private noncomputable def midM32K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ midM32K128KrotovCertQubits n m k)) Var
      (midM32K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isMidM32K128KrotovCertCell m k = true then
    let p := mm32k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG mm32k128VPot mm32k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the `6` `m = 32, 4 ≤ k ≤ 128` cells. -/
noncomputable def findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ midM32K128KrotovCertQubits n m k)) Var
      (midM32K128KrotovCertQubits n m k) ((n + 1) * m) :=
  midM32K128KrotovCertCircuitImpl res n m k

private lemma mm32k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isMidM32K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit res n m k =
      let p := mm32k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG mm32k128VPot mm32k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit midM32K128KrotovCertCircuitImpl
  exact dite_eq_left h

private lemma mm32k128_corr_impl {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isMidM32K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [mm32k128_targetSets_eq]
  have hp := mm32k128_all_props hcell
  rw [mm32k128_circuit_eq res n hcell, ← mm32k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG mm32k128VPot mm32k128Anchors hp.hk128
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

private lemma mm32k128_cost_impl {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isMidM32K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostMidM32K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := mm32k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG mm32k128VPot
    mm32k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [mm32k128_circuit_eq res n hcell, ← mm32k128_oracle_eq]
    exact hq S (by rwa [mm32k128_targetSets_eq])
  · rw [← mm32k128_targetSets_eq, ← mm32k128_vanilla_eq]; exact hsum

/-- Exact probability-`1` recovery of `S` across the `6` `m = 32, 4 ≤ k ≤ 128` cells. -/
theorem midM32K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isMidM32K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ :=
  mm32k128_corr_impl res hn hcell hkN hS

/-- Asymptotic uniform-average relative-cost bound across `m = 32, 4 ≤ k ≤ 128`. -/
theorem midM32K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isMidM32K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostMidM32K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) :=
  mm32k128_cost_impl res hcell

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

end QuantumComputation.Specs.GroverFindAll.Rk128kMidM32K128KrCert
