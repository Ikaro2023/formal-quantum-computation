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
# Krotov `m = 128` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kHiM128K128KrCert`)

QHL-verified module packaging all `5` `m = 128, 8 ≤ k ≤ 128` cells
(`(128, 8), (128, 16), (128, 32), (128, 64), (128, 128)`) over `22` anchors
(`372` segments, `431,594` F1272 / `440,416` Horner coord-ops at `lTableMax = 2`,
`useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kHiM128K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m = 128, k ∈ {8, 16, 32, 64, 128}`, `5` cells). -/
def isHiTailM128K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 128 then
    if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor `L_{\max}(128, k) = 2` across `k ∈ {8..128}`. -/
def hiTailM128K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 128 then
    if k == 8 then 2
    else if k == 16 then 2
    else if k == 32 then 2
    else if k == 64 then 2
    else if k == 128 then 2
    else 1
  else 1

/-- Total register qubit budget `(hiTailM128K128KrotovCertCellLMax m k * m) * (n + 1) + k *
  n`. -/
abbrev hiTailM128K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (hiTailM128K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile `c(128, k): ℚ≥0` across `k ∈ {8..128}`. -/
def relCostHiTailM128K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 128 then
    if k == 8 then NNRat.divNat 11419214186997 50000000000000
    else if k == 16 then NNRat.divNat 38426409743409 250000000000000
    else if k == 32 then NNRat.divNat 107566698366869 1000000000000000
    else if k == 64 then NNRat.divNat 81067657171691 1000000000000000
    else if k == 128 then NNRat.divNat 14113582515393 200000000000000
    else 1
  else 1

/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def hiTailM128K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isHiTailM128K128KrotovCertCell, relCostHiTailM128K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kHiM128K128KrCert` cell lies on `groverGrid × groverGrid`. -/
theorem isHiTailM128K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isHiTailM128K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isHiTailM128K128KrotovCertCell at h
  split_ifs at h with hm128 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm128 hk8; rfl
  · subst hm128 hk16; rfl
  · subst hm128 hk32; rfl
  · subst hm128 hk64; rfl
  · subst hm128 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def hm128NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem hm128NatEq_eq {x y : ℕ} (h : hm128NatEq x y = true) : x = y := by
  unfold hm128NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def hm128IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => hm128NatEq m n
  | Int.negSucc m, Int.negSucc n => hm128NatEq m n
  | _, _ => false
private theorem hm128IntEq_eq {a b : ℤ} (h : hm128IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [hm128IntEq] at h; exact congrArg Int.ofNat (hm128NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => dsimp only [hm128IntEq] at h; exact congrArg Int.negSucc (hm128NatEq_eq h)
private def hm128ListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (hm128ListEq eqF xr yr) false
  | _, _ => false
private theorem hm128ListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : hm128ListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [hm128ListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev Hm128St := ℕ × ℕ × ℕ × List ℤ
private def hm128StEq (a b : Hm128St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (hm128NatEq a1 b1) (cond (hm128NatEq a2 b2)
      (cond (hm128NatEq a3 b3) (hm128ListEq hm128IntEq av bv) false) false) false
private theorem hm128StEq_eq {a b : Hm128St} (h : hm128StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [hm128StEq] at h
  cases h1 : hm128NatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : hm128NatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : hm128NatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h
        exact Prod.ext (hm128NatEq_eq h1) (Prod.ext (hm128NatEq_eq h2)
          (Prod.ext (hm128NatEq_eq h3) (hm128ListEq_eq (@hm128IntEq_eq) h)))
private def hm128AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (hm128AtF rest) false
private theorem hm128_hd {b : Bool} {bs : List Bool} (h : hm128AtF (b :: bs) = true) :
    b = true := by unfold hm128AtF at h; cases b with | false => cases h | true => rfl
private theorem hm128_tl1 {b : Bool} {s : List Bool} (h : hm128AtF (b :: s) = true) :
    hm128AtF s = true := by
  unfold hm128AtF at h; cases b with | false => cases h | true => exact h
private theorem hm128_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : hm128AtF (b1 :: b2 :: bs) = true) : hm128AtF bs = true := hm128_tl1 (hm128_tl1 h)
private theorem hm128_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : hm128AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : hm128AtF bs = true :=
  hm128_tl2 (hm128_tl2 h)
private theorem hm128_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with | false => cases h | true => rfl
private theorem hm128_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with | false => cases h | true => cases b with | false => cases h | true => rfl
private abbrev hm128M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def hm128ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  hm128ListEq hm128NatEq (DickeSol.rkm128kEvalRowLo12 128 2 r s) ro
private theorem hm128_row_eq {r : ℕ} {s : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (h : hm128ChkRow r s ro = true) : DickeSol.rkm128kEvalRowLo12 128 2 r s = ro :=
  hm128ListEq_eq (@hm128NatEq_eq) h
private def hm128ChkSlice (r : ℕ) (s : List DickeSol.Rkm128kSeg)
    (l0 d0 p0 : ℕ) (v0 : List ℤ) (st1 : Hm128St) : Bool :=
  hm128StEq (DickeSol.rkm128kRunSegs 128 2 r s l0 d0 p0 v0) st1
private theorem hm128_sl_end {r : ℕ} {s : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 : ℕ} {v0 : List ℤ} {st1 : Hm128St}
    (h : hm128ChkSlice r s l0 d0 p0 v0 st1 = true) :
    DickeSol.rkm128kRunSegs 128 2 r s l0 d0 p0 v0 = st1 := hm128StEq_eq h
private theorem hm128_sl_step {r : ℕ} {s1 s2 : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {st2 : Hm128St}
    (h1 : hm128ChkSlice r s1 l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : DickeSol.rkm128kRunSegs 128 2 r s2 l1 d1 p1 v1 = st2) :
    DickeSol.rkm128kRunSegs 128 2 r (s1 ++ s2) l0 d0 p0 v0 = st2 := by
  unfold hm128ChkSlice at h1; rw [DickeSol.rkm128kRunSegs_append, hm128StEq_eq h1]; exact h2
private def hm128LenGuard (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def hm128FinGuard (st : Hm128St) (ro : List ℕ) : Bool :=
  hm128ListEq hm128NatEq (DickeSol.rkm128kFinalizeState st) ro
private theorem hm128_cert_row {r : ℕ} (s : List DickeSol.Rkm128kSeg)
    (st : Hm128St) (ro : List ℕ) (hsegs : hm128LenGuard r s = true)
    (hrun : DickeSol.rkm128kRunSegs 128 2 r s 1 0 1 [Int.ofNat DickeSol.wdScale] = st)
    (hfin : hm128FinGuard st ro = true) : DickeSol.rkm128kEvalRowLo12 128 2 r s = ro :=
  DickeSol.rkm128kCertRow_of_runSegs hsegs hrun (hm128ListEq_eq (@hm128NatEq_eq) hfin)
private def hm128ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 128 k (v.getD k 0) n d)
private lemma hm128ChkCell_l {k lm n d : ℕ} {v : List ℕ}
    {a : List DickeSol.RampKick128kAnchor}
    (h : hm128ChkCell k lm n d v a = true) : DickeSol.rkm128kCheckAnchorsLMax k lm a = true :=
  hm128_and_l h
private lemma hm128ChkCell_r {k lm n d : ℕ} {v : List ℕ}
    {a : List DickeSol.RampKick128kAnchor} (h : hm128ChkCell k lm n d v a = true) :
    DickeSol.checkAltBound12 128 k (v.getD k 0) n d = true := hm128_and_r h

private def hm128k128VPot : List ℕ :=
  [ 0, 56807109866442, 61268963978103, 66739873854576, 67622670417205, 68207223253362,
    68645338029957, 69001296851568, 69306715078394, 69579087914375, 69828775213728,
    70062678200192, 70284638857573, 70498268775426, 85680607507787, 70908726239410,
    71106505221692, 84884253119658, 98273817321715, 111306262120791, 71885582962047,
    84281910627507, 72270195084067, 84115296312144, 72656181084218, 84017603057507,
    95158393892884, 73241292443749, 83976827115673, 94525642593183, 104897154426692,
    115100012551523, 74236106113978, 84124954641146, 93867293609276, 103469447729767,
    112937299374174, 122276330707962, 75499650498582, 84596068124499, 93578060847968,
    102449840897830, 111215368251887, 119878371291247, 128442365329951, 136910669281062,
    145286420683277, 153572589280966, 161771989324285, 169887290733777, 177921029255012,
    79936195256547, 87813924004023, 95616980651573, 103347449147963, 111007318279741,
    118598487645922, 126122773158868, 133581912116501, 140977567885982, 148311334234613,
    155584739339918, 162799249507470, 169956272622086, 82176335292183, 89222390087248,
    96214861938936, 103154954986807, 110043828935790, 116882601318399, 123672349610997,
    130414113215447, 137108895316476, 143757664624141, 150361357009976, 156920877044631,
    163437099444169, 169910870431555, 176343009019346, 182734308219077, 189085536182411,
    195397437278683, 201670733113136, 207906123489780, 214104287322510, 220265883497851,
    226391551692422, 232481913147995, 238537571406804, 244559113009576, 250547108158556,
    256502111347655, 262424661961694, 268315284846569, 274174490852050, 280002777348800,
    285800628721092, 291568516836614, 297306901494639, 303016230853775, 308696941840420,
    314349460538966, 319974202564753, 325571573420684, 331141968838373, 336685775104639,
    342203369374105, 347695119968617, 353161386664163, 358602520965916, 364018866371998,
    369410758626531, 374778525962493, 380122489334886, 385442962644674, 390740252953944,
    396014660692699, 401266479857683, 406495998203604, 411703497427113, 416889253343868,
    422053536059000, 427196610131278, 432318734731257, 437420163793673, 442501146164340,
    447561925741794, 452602741613905, 103910151395476 ]
private def hm128Row_r3 : List ℕ :=
  [ 638176058, 53938112169, 945422749759 ]
private def hm128Sgs_r3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 20372873, 1, 24, []⟩,
  ⟨1, 20760594, 1, 25, []⟩,
  ⟨1, 22503174, 1, 26, []⟩]
private def hm128Anc_r3 : DickeSol.RampKick128kAnchor :=
  ⟨3, hm128Sgs_r3, hm128Row_r3⟩
private def hm128Row_r4 : List ℕ :=
  [ 10, 242073169, 40246156626, 959511770149 ]
private def hm128Sgs_r4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 57092817, 1, 45, []⟩,
  hm128M 1 6833491 1 18 1 [1],
  ⟨1, 854452, 1, 10, []⟩,
  hm128M 1 423277 1 9 5 [28],
  ⟨1, 117534, 1, 7, []⟩]
private def hm128Anc_r4 : DickeSol.RampKick128kAnchor :=
  ⟨4, hm128Sgs_r4, hm128Row_r4⟩
private def hm128Row_r5 : List ℕ :=
  [ 1, 88, 69137484, 32226076407, 967704785985 ]
private def hm128Sgs_r5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 16081003, 1, 21, []⟩,
  ⟨1, 22865460, 1, 23, []⟩,
  ⟨1, 16414182, 1, 21, []⟩,
  hm128M 1 7263792 1 15 6 [62],
  hm128M 1 534224 1 8 6 [62],
  hm128M 1 558224 1 8 2 [2],
  hm128M 1 279384 1 8 6 [60],
  hm128M 1 380542 1 8 2 [2],
  hm128M 1 267180 1 8 2 [2],
  hm128M 1 324168 1 8 2 [2],
  hm128M 1 94253 1 8 2 [2],
  hm128M 1 236187 1 8 3 [6],
  hm128M 1 84106 1 8 3 [6],
  hm128M 1 78506 1 8 3 [4],
  ⟨1, 113433, 1, 8, []⟩,
  hm128M 1 45514 1 8 3 [4],
  hm128M 1 183830 1 8 3 [4],
  hm128M 1 117273 1 8 3 [6],
  hm128M 1 74448 1 8 3 [6],
  hm128M 1 115483 1 8 3 [6],
  hm128M 1 150169 1 8 3 [6],
  ⟨1, 110956, 1, 8, []⟩]
private def hm128Anc_r5 : DickeSol.RampKick128kAnchor :=
  ⟨5, hm128Sgs_r5, hm128Row_r5⟩
private def hm128Row_r6 : List ℕ :=
  [ 0, 5, 2, 6159868, 26956724621, 973037115452 ]
private def hm128Sgs_r6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 17702961, 1, 29, []⟩,
  ⟨1, 8749019, 1, 22, []⟩,
  ⟨1, 7368071, 1, 20, []⟩,
  ⟨1, 6158854, 1, 19, []⟩,
  ⟨1, 5199885, 1, 18, []⟩,
  ⟨1, 4346661, 1, 17, []⟩,
  ⟨1, 3660869, 1, 16, []⟩,
  ⟨1, 3083340, 1, 15, []⟩,
  ⟨1, 2584083, 1, 15, []⟩,
  ⟨1, 2165740, 1, 14, []⟩,
  hm128M 1 629909 1 10 7 [126],
  hm128M 1 1129839 1 12 2 [2],
  hm128M 1 1049989 1 12 3 [4],
  hm128M 1 303591 1 9 3 [6],
  hm128M 1 411234 1 10 3 [4],
  hm128M 1 242178 1 9 3 [4],
  hm128M 1 646592 1 10 4 [12],
  hm128M 1 161132 1 8 4 [10],
  hm128M 1 173755 1 8 4 [10],
  ⟨1, 174082, 1, 8, []⟩,
  hm128M 1 3265 1 6 4 [10],
  hm128M 1 205656 1 8 4 [10],
  hm128M 1 208635 1 8 4 [10],
  ⟨1, 175294, 1, 8, []⟩,
  hm128M 1 28654 1 6 4 [10],
  hm128M 1 215624 1 9 4 [10],
  hm128M 1 155503 1 8 4 [12],
  hm128M 1 37952 1 7 4 [10],
  hm128M 1 55736 1 7 4 [12],
  ⟨1, 85524, 1, 7, []⟩]
private def hm128Anc_r6 : DickeSol.RampKick128kAnchor :=
  ⟨6, hm128Sgs_r6, hm128Row_r6⟩
private def hm128Row_r7 : List ℕ :=
  [ 0, 0, 20, 0, 32, 23217760019, 976782239871 ]
private def hm128Sgs_r7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 26009, 1, 6, []⟩,
  ⟨1, 24004017, 1, 36, []⟩,
  ⟨1, 19975510, 1, 33, []⟩,
  ⟨1, 7570173, 1, 22, []⟩,
  ⟨1, 3712016, 1, 17, []⟩,
  ⟨1, 2340552, 1, 15, []⟩,
  hm128M 1 3033427 1 16 8 [254],
  hm128M 1 1014960 1 12 2 [2],
  hm128M 1 570603 1 11 2 [2],
  hm128M 1 555746 1 10 3 [6],
  hm128M 1 556170 1 10 4 [14],
  hm128M 1 186 1 6 4 [8],
  hm128M 1 973181 1 12 4 [10],
  ⟨1, 685511, 1, 11, []⟩,
  hm128M 1 569835 1 11 5 [24],
  hm128M 1 214137 1 9 5 [20],
  hm128M 1 278772 1 9 5 [20],
  hm128M 1 331811 1 9 5 [20],
  hm128M 1 326896 1 9 5 [24],
  hm128M 1 242757 1 9 5 [20],
  hm128M 1 140585 1 8 5 [24],
  ⟨1, 38978, 1, 7, []⟩,
  hm128M 1 74626 1 7 5 [24],
  hm128M 1 125558 1 8 5 [24],
  hm128M 1 129587 1 8 6 [48],
  hm128M 1 28805 1 6 6 [40],
  hm128M 1 29338 1 6 6 [40],
  hm128M 1 29659 1 6 6 [40],
  hm128M 1 29171 1 6 6 [40],
  hm128M 1 29772 1 6 6 [48],
  hm128M 1 29256 1 6 6 [48],
  ⟨1, 14759, 1, 6, []⟩]
private def hm128Anc_r7 : DickeSol.RampKick128kAnchor :=
  ⟨7, hm128Sgs_r7, hm128Row_r7⟩
private def hm128Row_r8 : List ℕ :=
  [ 3, 3, 0, 10, 1, 760, 20425137435, 979574861725 ]
private def hm128Sgs_r8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 1832712, 1, 10, []⟩,
  ⟨1, 42655464, 3, 24, []⟩,
  ⟨1, 7972363, 1, 18, []⟩,
  ⟨1, 6305906, 1, 16, []⟩,
  hm128M 1 2889979 1 12 3 [7],
  hm128M 1 328267 1 8 3 [7],
  hm128M 1 942371 1 10 4 [8],
  hm128M 1 407221 1 8 4 [8],
  hm128M 1 1120367 1 10 5 [31],
  hm128M 1 977693 1 10 5 [31],
  hm128M 1 17258 1 8 4 [15],
  hm128M 1 342901 1 8 6 [63],
  hm128M 1 342874 1 8 6 [56],
  hm128M 1 215930 1 8 6 [63],
  hm128M 1 120592 1 8 6 [48],
  hm128M 1 234812 1 8 6 [48],
  hm128M 1 259188 1 8 6 [48],
  hm128M 1 175203 1 8 6 [48],
  hm128M 1 87779 1 8 6 [48],
  hm128M 1 32282 1 8 5 [31],
  hm128M 1 35042 1 8 6 [48],
  hm128M 1 119002 1 8 6 [48],
  hm128M 1 230679 1 8 4 [8],
  hm128M 1 7258 1 8 7 [127],
  hm128M 1 65889 1 8 7 [127],
  hm128M 1 64609 1 8 7 [127],
  hm128M 1 67140 1 8 7 [127],
  hm128M 1 64679 1 8 7 [112],
  hm128M 1 64265 1 8 7 [120],
  hm128M 1 66916 1 8 7 [120],
  hm128M 1 65344 1 8 7 [96],
  ⟨1, 34437, 1, 8, []⟩]
private def hm128Anc_r8 : DickeSol.RampKick128kAnchor :=
  ⟨8, hm128Sgs_r8, hm128Row_r8⟩
private def hm128Row_r9 : List ℕ :=
  [ 0, 0, 155, 3769, 478974, 1056, 787938, 18269982427, 981728745515 ]
private def hm128Sgs_r9 : List DickeSol.Rkm128kSeg := [
  hm128M 1 66268405 2 49 7 [112],
  hm128M 1 1665546 1 14 10 [872],
  hm128M 1 351138 1 10 8 [128],
  ⟨1, 256053, 1, 9, []⟩]
private def hm128Anc_r9 : DickeSol.RampKick128kAnchor :=
  ⟨9, hm128Sgs_r9, hm128Row_r9⟩
private def hm128Row_r10 : List ℕ :=
  [ 0, 0, 3, 866, 435, 7, 22986, 4409566, 16549819384, 983445746577 ]
private def hm128Sgs_r10 : List DickeSol.Rkm128kSeg := [
  hm128M 1 61080436 2 49 4 [14],
  hm128M 1 2259545 1 16 6 [50],
  hm128M 1 1417847 1 14 7 [66],
  hm128M 1 1674884 1 15 8 [136],
  hm128M 1 1623537 1 15 9 [392],
  hm128M 1 396554 1 10 9 [264],
  ⟨1, 435553, 1, 11, []⟩]
private def hm128Anc_r10 : DickeSol.RampKick128kAnchor :=
  ⟨10, hm128Sgs_r10, hm128Row_r10⟩
private def hm128Row_r11 : List ℕ :=
  [ 0, 0, 0, 0, 1556, 975, 472, 256, 12780662, 15162677749, 984824538056 ]
private def hm128Sgs_r11 : List DickeSol.Rkm128kSeg := [
  hm128M 1 61180854 2 52 5 [28],
  hm128M 1 2292169 1 17 7 [100],
  hm128M 1 1426004 1 14 8 [138],
  hm128M 1 1693504 1 15 9 [276],
  hm128M 1 1815856 1 15 6 [48],
  hm128M 1 43324 1 7 10 [556],
  ⟨1, 748836, 1, 12, []⟩]
private def hm128Anc_r11 : DickeSol.RampKick128kAnchor :=
  ⟨11, hm128Sgs_r11, hm128Row_r11⟩
private def hm128Row_r12 : List ℕ :=
  [ 0, 0, 0, 0, 0, 1362, 10283, 1710233, 158927, 4262086, 13996744750, 985997111576 ]
private def hm128Sgs_r12 : List DickeSol.Rkm128kSeg := [
  hm128M 1 66690229 2 58 10 [896],
  hm128M 1 1777994 1 16 13 [7000],
  hm128M 1 557002 1 12 11 [1040],
  ⟨1, 463911, 1, 11, []⟩]
private def hm128Anc_r12 : DickeSol.RampKick128kAnchor :=
  ⟨12, hm128Sgs_r12, hm128Row_r12⟩
private def hm128Row_r13 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 2437, 13369, 2395603, 319906, 5607851, 13019392527, 986972215826 ]
private def hm128Sgs_r13 : List DickeSol.Rkm128kSeg := [
  hm128M 1 66831543 6 23 11 [1840],
  hm128M 1 1807185 1 9 14 [13984],
  hm128M 1 604435 1 5 12 [2048],
  ⟨1, 514980, 1, 5, []⟩]
private def hm128Anc_r13 : DickeSol.RampKick128kAnchor :=
  ⟨13, hm128Sgs_r13, hm128Row_r13⟩
private def hm128Row_r15 : List ℕ :=
  [ 0, 0, 0, 0, 0, 1, 47, 144, 4461, 267962, 82141, 69721, 31078806, 11471616349, 988496858208 ]
private def hm128Sgs_r15 : List DickeSol.Rkm128kSeg := [
  hm128M 1 61632265 3 34 9 [464],
  hm128M 1 1179495 1 8 10 [640],
  hm128M 1 2599731 1 10 12 [3488],
  hm128M 1 1375468 1 8 13 [5376],
  hm128M 1 664862 1 6 13 [5376],
  hm128M 1 1726307 1 8 14 [8768],
  ⟨1, 1076994, 1, 8, []⟩]
private def hm128Anc_r15 : DickeSol.RampKick128kAnchor :=
  ⟨15, hm128Sgs_r15, hm128Row_r15⟩
private def hm128Row_r16 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 3, 50, 6003, 166, 438, 10, 3796, 10286, 10829663202, 989170315918 ]
private def hm128Sgs_r16 : List DickeSol.Rkm128kSeg := [
  hm128M 1 18062351 1 47 17 [131071],
  ⟨1, 8391506, 1, 31, []⟩,
  ⟨1, 7052299, 1, 29, []⟩,
  ⟨1, 5928233, 1, 26, []⟩,
  ⟨1, 4982616, 1, 25, []⟩,
  ⟨1, 4186799, 1, 23, []⟩,
  ⟨1, 3516753, 1, 21, []⟩,
  hm128M 1 2956203 1 20 1 [1],
  hm128M 1 2484288 1 19 1 [1],
  hm128M 1 2086633 1 18 8 [241],
  hm128M 1 1752477 1 17 9 [351],
  hm128M 1 1462838 1 16 11 [1731],
  hm128M 1 1278224 1 15 12 [2158],
  hm128M 1 1386861 1 16 13 [4728],
  hm128M 1 795055 1 13 13 [7855],
  hm128M 1 715375 1 13 14 [13064],
  hm128M 1 583113 1 12 14 [8612],
  hm128M 1 518836 1 12 14 [13311],
  hm128M 1 441642 1 12 14 [13731],
  hm128M 1 354690 1 11 15 [23848],
  hm128M 1 283449 1 11 15 [19874],
  hm128M 1 268299 1 10 15 [20397],
  hm128M 1 216270 1 10 15 [27523],
  hm128M 1 179854 1 10 15 [29736],
  hm128M 1 132492 1 9 15 [19883],
  hm128M 1 108538 1 9 15 [32764],
  hm128M 1 97997 1 9 15 [18304],
  hm128M 1 80240 1 8 15 [26664],
  hm128M 1 58861 1 8 13 [6785],
  hm128M 1 51295 1 8 15 [32765],
  hm128M 1 43265 1 8 14 [15359],
  ⟨1, 33950, 1, 7, []⟩]
private def hm128Anc_r16 : DickeSol.RampKick128kAnchor :=
  ⟨16, hm128Sgs_r16, hm128Row_r16⟩
private def hm128Row_r20 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 166, 82, 33, 4, 2270, 2297, 415, 390, 425544, 11703960, 1505976, 877315,
    8995085406, 990990395913 ]
private def hm128Sgs_r20 : List DickeSol.Rkm128kSeg := [
  hm128M 1 30195613 2 47 21 [1048576],
  hm128M 1 32258798 2 49 14 [14956],
  hm128M 1 3277819 1 23 17 [108132],
  hm128M 1 2018045 1 19 18 [223476],
  hm128M 1 1010846 1 15 18 [139392],
  hm128M 1 1205147 1 16 19 [270432],
  hm128M 1 974598 1 15 19 [280544],
  ⟨1, 432757, 1, 12, []⟩]
private def hm128Anc_r20 : DickeSol.RampKick128kAnchor :=
  ⟨20, hm128Sgs_r20, hm128Row_r20⟩
private def hm128Row_r22 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 68, 9650, 44786, 25145, 15765, 13204173, 6499681,
    19433595, 8295511504, 991665254554 ]
private def hm128Sgs_r22 : List DickeSol.Rkm128kSeg := [
  hm128M 1 62627983 3 61 16 [56064],
  hm128M 1 2555535 1 21 18 [235008],
  hm128M 1 2992758 1 23 20 [894976],
  hm128M 1 1840509 1 19 15 [20480],
  hm128M 1 109610 1 9 21 [1095680],
  hm128M 1 825293 1 15 21 [1173504],
  ⟨1, 844739, 1, 15, []⟩]
private def hm128Anc_r22 : DickeSol.RampKick128kAnchor :=
  ⟨22, hm128Sgs_r22, hm128Row_r22⟩
private def hm128Row_r24 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 313, 1254, 1109, 82542, 31661, 13916581, 10892542,
    18974769, 7748773190, 992207325537 ]
private def hm128Sgs_r24 : List DickeSol.Rkm128kSeg := [
  ⟨1, 31793605, 2, 54, []⟩,
  hm128M 1 33539205 2 56 20 [930816],
  hm128M 1 2087493 1 20 20 [903168],
  hm128M 1 1067908 1 16 22 [4149248],
  hm128M 1 1183736 1 17 20 [626688],
  hm128M 1 822997 1 15 23 [4739072],
  hm128M 1 873350 1 15 23 [4816896],
  ⟨1, 844863, 1, 15, []⟩]
private def hm128Anc_r24 : DickeSol.RampKick128kAnchor :=
  ⟨24, hm128Sgs_r24, hm128Row_r24⟩
private def hm128Row_r27 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 247, 5433, 188226, 6723, 19730870,
    18167041, 11050636, 7111131032, 992839718989 ]
private def hm128Sgs_r27 : List DickeSol.Rkm128kSeg := [
  ⟨1, 32838572, 2, 59, []⟩,
  hm128M 1 32929376 2 59 23 [7512064],
  hm128M 1 2098735 1 21 23 [6930432],
  hm128M 1 1101293 1 17 25 [33259520],
  hm128M 1 1499891 1 19 23 [4882432],
  hm128M 1 615244 1 14 26 [33931264],
  hm128M 1 976173 1 16 26 [39256064],
  ⟨1, 774808, 1, 15, []⟩]
private def hm128Anc_r27 : DickeSol.RampKick128kAnchor :=
  ⟨27, hm128Sgs_r27, hm128Row_r27⟩
private def hm128Row_r32 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 2, 5, 15, 713, 936, 4162, 1364, 7873, 24241,
    64669, 22307, 24562, 84, 1699055, 6281689102, 993716460359 ]
private def hm128Sgs_r32 : List DickeSol.Rkm128kSeg := [
  hm128M 1 50921056 4 55 5 [18],
  hm128M 1 953021 1 17 7 [87],
  hm128M 1 958006 1 17 9 [332],
  hm128M 1 958185 1 17 11 [1281],
  hm128M 1 958185 1 17 13 [5158],
  hm128M 1 804425 1 16 15 [32722],
  hm128M 1 804576 1 16 16 [47587],
  hm128M 1 804655 1 16 18 [201130],
  hm128M 1 804656 1 16 19 [481144],
  hm128M 1 730343 1 16 20 [534570],
  hm128M 1 729802 1 16 21 [1309076],
  hm128M 1 729807 1 16 22 [4052787],
  hm128M 1 729841 1 16 23 [6818988],
  hm128M 1 1043342 1 18 24 [13631745],
  hm128M 1 1043893 1 18 25 [17500525],
  hm128M 1 1034538 1 17 26 [48300109],
  hm128M 1 1052599 1 18 27 [97550618],
  hm128M 1 700778 1 16 27 [102269118],
  hm128M 1 713303 1 16 28 [176423493],
  hm128M 1 735603 1 16 25 [18612482],
  hm128M 1 738672 1 16 29 [352846149],
  hm128M 1 807727 1 16 29 [536854514],
  hm128M 1 878145 1 17 30 [572915741],
  hm128M 1 806991 1 16 30 [608567322],
  hm128M 1 712032 1 16 28 [244518940],
  hm128M 1 550821 1 14 31 [2079191035],
  hm128M 1 457087 1 14 31 [1480658956],
  hm128M 1 448159 1 14 31 [1648429061],
  hm128M 1 410863 1 13 31 [2051610634],
  hm128M 1 328877 1 13 31 [1644791818],
  hm128M 1 276589 1 12 31 [1527316489],
  hm128M 1 252570 1 12 30 [536872960]]
private def hm128Anc_r32 : DickeSol.RampKick128kAnchor :=
  ⟨32, hm128Sgs_r32, hm128Row_r32⟩
private def hm128Row_r38 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 52, 421, 837, 32168, 545,
    9510, 56766, 171713, 290143, 2965915, 11876025, 2235049, 20525551, 54446714, 5810364031,
    994097024187 ]
private def hm128Sgs_r38 : List DickeSol.Rkm128kSeg := [
  ⟨1, 18158449, 2, 49, []⟩,
  ⟨1, 10535050, 1, 54, []⟩,
  ⟨1, 8195103, 1, 46, []⟩,
  ⟨1, 6901931, 1, 42, []⟩,
  hm128M 1 5784022 1 38 6 [48],
  hm128M 1 4459929 1 33 17 [128021],
  hm128M 1 4408960 1 33 24 [14718281],
  hm128M 1 3243212 1 29 29 [475354448],
  hm128M 1 3104573 1 28 32 [3844756817],
  hm128M 1 2426414 1 25 34 [13609604420],
  hm128M 1 1810908 1 22 35 [28090864977],
  hm128M 1 1828549 1 23 36 [37080009296],
  hm128M 1 1227053 1 19 36 [35069930128],
  hm128M 1 1126148 1 19 37 [68895910532],
  hm128M 1 1087231 1 19 37 [73721457280],
  ⟨1, 866139, 1, 17, []⟩]
private def hm128Anc_r38 : DickeSol.RampKick128kAnchor :=
  ⟨38, hm128Sgs_r38, hm128Row_r38⟩
private def hm128Row_r51 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
    7, 107, 375, 85, 20977, 2397, 360393, 185880, 53, 869070, 23459768, 1116672, 58567678,
    105692372, 516829195, 20799280, 7590313589, 7361132530, 29711921721, 954608726766 ]
private def hm128Sgs_r51 : List DickeSol.Rkm128kSeg := [
  ⟨1, 21037069, 2, 64, []⟩,
  ⟨1, 16989816, 2, 56, []⟩,
  hm128M 1 13622234 2 49 21 [1970322],
  hm128M 1 9803097 1 61 39 [518736521896],
  hm128M 1 4837961 1 40 44 [15851315012944],
  hm128M 1 4310654 1 38 47 [111783676258984],
  hm128M 1 4482304 1 38 49 [328524903305898],
  ⟨1, 2157861, 1, 27, []⟩]
private def hm128Anc_r51 : DickeSol.RampKick128kAnchor :=
  ⟨51, hm128Sgs_r51, hm128Row_r51⟩
private def hm128Row_r64 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 7, 3, 12, 256, 198, 890, 969, 237, 822, 2960, 1146, 10501, 20309, 779, 153, 480, 3879,
    120303, 700850, 129600, 762303, 87195, 1388126, 1106432, 1604454, 3935807, 35679632,
    44004730, 65799, 4678024601, 995232345899 ]
private def hm128Ch_r64_0 : List DickeSol.Rkm128kSeg := [
  hm128M 1 4688760 1 44 61 [412316860416, 24],
  hm128M 1 4688760 1 44 65 [54016807249379327, 511],
  hm128M 1 4775692 1 44 65 [844424930131968, 260],
  hm128M 1 4775693 1 44 61 [13510798882111488, 16],
  hm128M 1 4727873 1 44 65 [0, 323],
  hm128M 1 4727874 1 44 60 [0, 8],
  hm128M 1 4190766 1 41 63 [0, 96],
  hm128M 1 4190766 1 41 63 [0, 64],
  hm128M 1 3880330 1 39 65 [113, 384],
  hm128M 1 3880331 1 39 17 [126867],
  hm128M 1 2994719 1 34 22 [2124752],
  hm128M 1 2994720 1 34 65 [251778416, 256],
  hm128M 1 4969489 1 45 65 [549285505423, 256],
  hm128M 1 4332978 1 42 47 [130681149760846],
  hm128M 1 3713256 1 39 52 [4052480653677193],
  hm128M 1 2717749 1 33 55 [28310794102913552],
  hm128M 1 2244424 1 30 57 [37908429651020197, 1]]
private def hm128Vec_r64_0 : List ℤ :=
  [ Int.negSucc 2038, Int.negSucc 27971, Int.negSucc 58128, Int.negSucc 29553, Int.negSucc 53361,
    Int.negSucc 191492, Int.negSucc 453664, Int.negSucc 366580, Int.negSucc 25925,
    Int.negSucc 150545, Int.negSucc 204142, Int.ofNat 706783, Int.negSucc 1211094,
    Int.negSucc 842254, Int.negSucc 354413, Int.negSucc 3559700, Int.negSucc 3511370,
    Int.negSucc 1674270, Int.negSucc 2505097, Int.negSucc 2436635, Int.negSucc 2523946,
    Int.ofNat 1508016, Int.ofNat 15554459, Int.ofNat 7634026, Int.ofNat 367670,
    Int.ofNat 78861150, Int.ofNat 218539732, Int.negSucc 434966465, Int.negSucc 818527236,
    Int.negSucc 678869645, Int.negSucc 671698092, Int.ofNat 174612004, Int.negSucc 1191448720,
    Int.ofNat 660063439, Int.ofNat 1061295303, Int.ofNat 3292077744, Int.ofNat 1947917074,
    Int.negSucc 2018791769, Int.negSucc 9810139619, Int.negSucc 10143332817,
    Int.negSucc 4546477224, Int.negSucc 12257084388, Int.ofNat 18388193434,
    Int.negSucc 85755133525, Int.negSucc 86803938007, Int.negSucc 38269417888,
    Int.negSucc 122692976522, Int.negSucc 105752555147, Int.negSucc 121435794838,
    Int.ofNat 687779129305, Int.negSucc 581685838510, Int.negSucc 1077141212191,
    Int.negSucc 250736708510, Int.negSucc 1267570736047, Int.negSucc 4714941855538,
    Int.negSucc 3323870001747, Int.negSucc 5669168928141, Int.negSucc 30831379210141,
    Int.negSucc 134515431055028, Int.negSucc 301248879967656, Int.negSucc 470108761842517,
    Int.negSucc 552340161330529, Int.negSucc 491890263510332, Int.negSucc 322021934565110,
    Int.negSucc 135642766689807 ]
private def hm128Ch_r64_1 : List DickeSol.Rkm128kSeg := [
  hm128M 1 2605823 1 32 59 [12185126259585538, 6],
  hm128M 1 1714515 1 27 60 [41168289080749819, 8],
  hm128M 1 1672701 1 26 61 [54204345503731954, 17],
  hm128M 1 950346 1 21 61 [66469378419241597, 17],
  hm128M 1 1061755 1 22 62 [11401042260928530, 33],
  hm128M 1 958338 1 21 62 [4125544401133586, 35],
  hm128M 1 1020963 1 22 55 [36028795777414059],
  hm128M 1 431053 1 16 63 [7503352051120240, 64],
  hm128M 1 431396 1 16 63 [20444663922199428, 70],
  hm128M 1 451677 1 16 63 [10038885845526529, 70],
  hm128M 1 381191 1 16 63 [18190664279950853, 68],
  hm128M 1 303947 1 15 63 [16512485249197688, 64],
  hm128M 1 310515 1 15 63 [149621945008399, 66],
  hm128M 1 10 1 6 58 [43534081954193408, 2],
  hm128M 1 325633 1 15 63 [17594474492514568, 74],
  hm128M 1 210979 1 13 63 [6942952353587567, 72],
  hm128M 1 132747 1 12 63 [563585620664942, 72],
  hm128M 1 129835 1 12 63 [61549011656155746, 77],
  hm128M 1 111303 1 11 63 [39970082367700996, 71],
  hm128M 1 115896 1 11 63 [18764901122760776, 69],
  hm128M 1 89752 1 11 17 [83488]]
private def hm128Vec_r64_1 : List ℤ :=
  [ Int.negSucc 801, Int.negSucc 1188, Int.negSucc 646, Int.negSucc 1895, Int.ofNat 10227,
    Int.negSucc 712, Int.negSucc 36725, Int.ofNat 1124875, Int.ofNat 296460, Int.ofNat 30604,
    Int.negSucc 14224, Int.ofNat 44126, Int.ofNat 86726, Int.ofNat 1704749, Int.ofNat 57192,
    Int.negSucc 4553, Int.ofNat 13098, Int.ofNat 1956857, Int.ofNat 119333017,
    Int.ofNat 32294174, Int.ofNat 1077349, Int.negSucc 10094086, Int.ofNat 5907213,
    Int.negSucc 971777, Int.ofNat 608430, Int.negSucc 88048684, Int.ofNat 154521806,
    Int.negSucc 25638475, Int.negSucc 301447652, Int.ofNat 557087263, Int.ofNat 810845009,
    Int.negSucc 521451204, Int.negSucc 1221103194, Int.negSucc 779907604, Int.negSucc 2683820140,
    Int.ofNat 1751803985, Int.ofNat 3475602288, Int.negSucc 16017496637, Int.ofNat 14098548697,
    Int.ofNat 29834650762, Int.negSucc 31134153276, Int.ofNat 15407802064,
    Int.negSucc 28687566121, Int.ofNat 54408453171, Int.ofNat 33854154699,
    Int.negSucc 102477648801, Int.ofNat 142510204679, Int.negSucc 27921922081,
    Int.negSucc 12370757787, Int.ofNat 21911968135, Int.negSucc 62284185503,
    Int.ofNat 346848828661, Int.negSucc 837168620668, Int.ofNat 360001326213,
    Int.negSucc 873099971711, Int.negSucc 295289022236, Int.ofNat 1178188238527,
    Int.negSucc 1051871188905, Int.negSucc 1266671099337, Int.negSucc 1983887347183,
    Int.negSucc 5973243323301, Int.negSucc 6633606447232, Int.ofNat 256514339230,
    Int.negSucc 68396086457503, Int.negSucc 997613325139726 ]
private def hm128St_r64_fin : Hm128St :=
  (1, 64, 299162, hm128Vec_r64_1)
private def hm128Sgs_r64 : List DickeSol.Rkm128kSeg :=
  hm128Ch_r64_0 ++ hm128Ch_r64_1
private def hm128Anc_r64 : DickeSol.RampKick128kAnchor :=
  ⟨64, hm128Sgs_r64, hm128Row_r64⟩
private def hm128Row_r128 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 16, 0, 0, 4, 14, 10, 70, 29, 46,
    12, 442, 8222, 61922, 6835, 14866, 31775, 62356, 375683, 2010485, 575179, 1446667, 59660,
    15381, 341508, 885272, 2385214, 115647, 232173, 11821, 904064, 2790094, 148497, 56001, 3266,
    23898, 1164, 1794204, 3169, 9509771, 132327, 153779, 7031879, 5037993, 758963, 416130,
    4061983, 464576, 19710, 1697484, 5718730, 164078, 1644764, 11221399, 7778598, 16699283,
    736894, 4591070, 30349, 17144, 2492440, 320469, 20161246, 20008773, 1040982, 37817675,
    11228958, 98601597, 174934075, 833496105, 116420426, 23218173, 65508556, 196920691,
    748356451, 20229413, 4732249495, 992804739118 ]
private def hm128Ch_r128_0 : List DickeSol.Rkm128kSeg := [
  hm128M 1 2719266 1 44 76 [14759599278129152, 740548],
  hm128M 1 2701420 1 44 128 [964134258606080, 18901076471267332, 32804],
  hm128M 1 2723285 1 44 127 [33838569856434176, 3451404199263646, 16421],
  hm128M 1 2723286 1 44 116 [3940649673949184, 15890419294880542, 9],
  hm128M 1 2752545 1 44 128 [36028797018963968, 13792273960035057, 32768],
  hm128M 1 2752545 1 44 129 [72057594037927935, 50662196732209615, 131071],
  hm128M 1 2699911 1 44 111 [0, 24769797950562304],
  hm128M 1 2699911 1 44 128 [1, 5101871392555008, 32769]]
private def hm128Vec_r128_0 : List ℤ :=
  [ Int.ofNat 40411823, Int.negSucc 272872955, Int.negSucc 1290873830, Int.negSucc 4939953319,
    Int.negSucc 16219161463, Int.negSucc 47183360357, Int.negSucc 124120133617,
    Int.negSucc 299418648821, Int.negSucc 669188948760, Int.negSucc 1396509288645,
    Int.negSucc 2737998457275, Int.negSucc 5068394199251, Int.negSucc 8894632860628,
    Int.negSucc 14848732427444, Int.negSucc 23648991812419, Int.negSucc 36022794484703,
    Int.negSucc 52591946513712, Int.negSucc 73731956428671, Int.negSucc 99427540253884,
    Int.negSucc 129154560022151, Int.negSucc 161820315053378, Int.negSucc 195787631730418,
    Int.negSucc 228993817993698, Int.negSucc 259156071686257, Int.negSucc 284035095146904,
    Int.negSucc 301713791411587, Int.negSucc 310842247789915, Int.negSucc 310805555516577,
    Int.negSucc 301786138875945, Int.negSucc 284713298346634, Int.negSucc 261114307367835,
    Int.negSucc 232898507019644, Int.negSucc 202114874310609, Int.negSucc 170723355184495,
    Int.negSucc 140412120337946, Int.negSucc 112479814652834, Int.negSucc 87787489133808,
    Int.negSucc 66772497562941, Int.negSucc 49508348621643, Int.negSucc 35791060570275,
    Int.negSucc 25233453057880, Int.negSucc 17352705729627, Int.negSucc 11641815723810,
    Int.negSucc 7620868316642, Int.negSucc 4868314376403, Int.negSucc 3035265737030,
    Int.negSucc 1847165947032, Int.negSucc 1097355204867, Int.negSucc 636437577828,
    Int.negSucc 360380395050, Int.negSucc 199244919968, Int.negSucc 107560496306,
    Int.negSucc 56698462198, Int.negSucc 29184425778, Int.negSucc 14668844884,
    Int.negSucc 7199530785, Int.negSucc 3450403029, Int.negSucc 1614663204,
    Int.negSucc 737776633, Int.negSucc 329138229, Int.negSucc 143356574, Int.negSucc 60955566,
    Int.negSucc 25300528, Int.negSucc 10250016, Int.negSucc 4052841, Int.negSucc 1563865,
    Int.negSucc 588837, Int.negSucc 216257, Int.negSucc 77380, Int.negSucc 26923,
    Int.negSucc 9080, Int.negSucc 2949, Int.ofNat 916, Int.ofNat 266, Int.negSucc 70,
    Int.ofNat 16, Int.negSucc 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm128Ch_r128_1 : List DickeSol.Rkm128kSeg := [
  hm128M 1 1578007 1 33 129 [15, 70641423057680384, 131070],
  hm128M 1 1578596 1 33 129 [80, 71767322754252800, 98303],
  hm128M 1 1578595 1 33 108 [369, 3960442057654272],
  hm128M 1 1578596 1 33 128 [9536, 5704271022522368, 32768],
  hm128M 1 1578594 1 33 109 [17432, 4503617880981504],
  hm128M 1 1578594 1 33 129 [72057594037533775, 71775019549589503, 98303],
  hm128M 1 1578592 1 33 128 [1327776, 281887293571072, 32768],
  hm128M 1 1578593 1 33 128 [12690603, 549755813888, 32768],
  hm128M 1 1578594 1 33 128 [4093977696, 1099511627776, 32768],
  hm128M 1 1578594 1 33 128 [18616907452, 21990232555520, 32768]]
private def hm128Vec_r128_1 : List ℤ :=
  [ Int.ofNat 32143160, Int.ofNat 140136665, Int.ofNat 870053300, Int.ofNat 1196763546,
    Int.ofNat 738589011, Int.negSucc 428722153, Int.negSucc 976666670, Int.negSucc 628688255,
    Int.ofNat 998583737, Int.ofNat 888207611, Int.negSucc 2874154481, Int.negSucc 1087011571,
    Int.ofNat 2240739630, Int.ofNat 3139082224, Int.ofNat 2220850838, Int.ofNat 22825299,
    Int.negSucc 3408385559, Int.negSucc 4143036170, Int.negSucc 933165585, Int.negSucc 176466771,
    Int.negSucc 56430503, Int.negSucc 252639283, Int.ofNat 708028560, Int.negSucc 247474564,
    Int.negSucc 453639955, Int.negSucc 386051614, Int.negSucc 909070231, Int.negSucc 854632618,
    Int.negSucc 3129554425, Int.negSucc 5119337802, Int.negSucc 3773792306, Int.ofNat 3534866895,
    Int.negSucc 4938915767, Int.negSucc 7661880785, Int.ofNat 3314511487, Int.ofNat 4751457691,
    Int.ofNat 17274481820, Int.ofNat 40276058332, Int.ofNat 85689848147, Int.ofNat 174520691981,
    Int.ofNat 342997177502, Int.ofNat 651464705107, Int.ofNat 1196513221731,
    Int.ofNat 2125942843458, Int.ofNat 3655563715238, Int.ofNat 6085229486554,
    Int.ofNat 9809694251375, Int.ofNat 15318535552911, Int.ofNat 23178167574612,
    Int.ofNat 33989751761148, Int.ofNat 48319486956402, Int.ofNat 66602649855424,
    Int.ofNat 89030082709764, Int.ofNat 115433395375491, Int.ofNat 145191495655043,
    Int.ofNat 177183843746923, Int.ofNat 209812504125397, Int.ofNat 241105428116793,
    Int.ofNat 268898420866493, Int.ofNat 291075599713061, Int.ofNat 305832569081951,
    Int.ofNat 311917481715726, Int.ofNat 308805549396384, Int.ofNat 296773375702052,
    Int.ofNat 276858617419868, Int.ofNat 250713100780305, Int.ofNat 220378026735387,
    Int.ofNat 188023439025439, Int.ofNat 155697636902851, Int.ofNat 125125543315115,
    Int.ofNat 97580958295410, Int.ofNat 73840398262295, Int.ofNat 54210189140147,
    Int.ofNat 38607100101656, Int.ofNat 26667812319178, Int.ofNat 17863599237921,
    Int.ofNat 11601975512964, Int.ofNat 7304474808614, Int.ofNat 4457028256856,
    Int.ofNat 2635107443082, Int.ofNat 1509161853617, Int.ofNat 837020649056,
    Int.ofNat 449437630261, Int.ofNat 233560900719, Int.ofNat 117432379747,
    Int.ofNat 57105780644, Int.ofNat 26846855064, Int.ofNat 12195054819, Int.ofNat 5348282507,
    Int.ofNat 2262216382, Int.ofNat 921695884, Int.ofNat 361192585, Int.ofNat 135933280,
    Int.ofNat 49068693, Int.ofNat 16895917, Int.ofNat 5677436, Int.ofNat 1733314,
    Int.ofNat 443907, Int.negSucc 96439, Int.ofNat 19619, Int.negSucc 4160, Int.ofNat 917,
    Int.ofNat 191, Int.ofNat 32, Int.ofNat 4, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
    Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm128Ch_r128_2 : List DickeSol.Rkm128kSeg := [
  hm128M 1 1578594 1 33 128 [90622134659, 34359738368, 32772],
  hm128M 1 1578594 1 33 129 [1708248409981, 72057456598974464, 98303],
  hm128M 1 1579185 1 33 129 [208152842278443, 72056494526300160, 130815],
  hm128M 1 1578597 1 33 51 [1268647163050992],
  hm128M 1 1578606 1 33 54 [16050128816243037],
  hm128M 1 1578607 1 33 128 [1046316178717641, 4, 32832],
  hm128M 2 1220271 1 37 61 [60713196491319108, 26],
  hm128M 2 1219818 1 37 71 [41463095089149585, 30872],
  hm128M 2 1219823 1 37 76 [70145002182877629, 953990],
  hm128M 2 1219823 1 37 82 [58261306552648728, 64824038]]
private def hm128Vec_r128_2 : List ℤ :=
  [ Int.ofNat 17703012, Int.negSucc 28790489, Int.negSucc 53748885, Int.negSucc 38767172,
    Int.ofNat 44265465, Int.ofNat 41171752, Int.negSucc 52479152, Int.negSucc 208932951,
    Int.negSucc 785368573, Int.negSucc 709002123, Int.negSucc 724886632, Int.negSucc 537470370,
    Int.ofNat 313304614, Int.ofNat 1324492652, Int.ofNat 240035246, Int.negSucc 28579977,
    Int.ofNat 1449272603, Int.ofNat 384724313, Int.ofNat 1412779527, Int.negSucc 150949269,
    Int.negSucc 3273279200, Int.negSucc 608429573, Int.ofNat 2076996885, Int.ofNat 69152294,
    Int.negSucc 1418976249, Int.negSucc 1159799713, Int.ofNat 1414845517, Int.negSucc 3958855164,
    Int.negSucc 2226792167, Int.negSucc 3728054861, Int.negSucc 1224992547, Int.ofNat 312978367,
    Int.ofNat 3391181323, Int.negSucc 684900572, Int.ofNat 181549061, Int.ofNat 1342153420,
    Int.ofNat 2106575130, Int.negSucc 2259109943, Int.negSucc 5574232689, Int.ofNat 151318754,
    Int.negSucc 2396864566, Int.negSucc 1701058221, Int.negSucc 9863294927,
    Int.negSucc 2834460632, Int.negSucc 2382457243, Int.ofNat 5086098230, Int.negSucc 1648917571,
    Int.negSucc 8380121255, Int.ofNat 3562130548, Int.ofNat 6750202611, Int.ofNat 3313221439,
    Int.negSucc 1007997198, Int.negSucc 1247148111, Int.negSucc 1632467334,
    Int.negSucc 915393333, Int.negSucc 4816788219, Int.ofNat 1963396303, Int.negSucc 2587528454,
    Int.negSucc 3414277547, Int.ofNat 847409126, Int.negSucc 998926010, Int.ofNat 3968920514,
    Int.negSucc 5609440733, Int.ofNat 2929261832, Int.ofNat 10648686338, Int.ofNat 2744532608,
    Int.ofNat 7286741171, Int.negSucc 14291893104, Int.ofNat 9290995347, Int.ofNat 2599715800,
    Int.negSucc 5099970154, Int.ofNat 4433510256, Int.ofNat 22677703618, Int.ofNat 23186885632,
    Int.ofNat 22554174839, Int.ofNat 34626359509, Int.negSucc 32544424014, Int.ofNat 69970152556,
    Int.negSucc 16933111807, Int.ofNat 93545254130, Int.ofNat 174739231682, Int.ofNat 7001566762,
    Int.ofNat 940364231782, Int.ofNat 3667632416966, Int.ofNat 9757286015985,
    Int.ofNat 21328982648039, Int.ofNat 40697228381072, Int.ofNat 69760224954013,
    Int.ofNat 109229247702566, Int.ofNat 157885199277734, Int.ofNat 212197102907499,
    Int.ofNat 266574052075284, Int.ofNat 314265976808661, Int.ofNat 348727713019218,
    Int.ofNat 365096903489562, Int.ofNat 361313002518742, Int.ofNat 338506331690169,
    Int.ofNat 300584800314225, Int.ofNat 253210900643656, Int.ofNat 202502267077964,
    Int.ofNat 153833732500809, Int.ofNat 111046784579730, Int.ofNat 76185299690189,
    Int.ofNat 49678809219736, Int.ofNat 30789744857176, Int.ofNat 18136428795159,
    Int.ofNat 10151045708278, Int.ofNat 5395474945100, Int.ofNat 2720342499673,
    Int.ofNat 1298821286170, Int.ofNat 585929632594, Int.ofNat 249129088160,
    Int.ofNat 99583308167, Int.ofNat 37335312675, Int.ofNat 13102839971, Int.ofNat 4297742266,
    Int.ofNat 1315877265, Int.ofNat 375707277, Int.ofNat 99926050, Int.ofNat 24720240,
    Int.ofNat 5674394, Int.ofNat 1203791, Int.ofNat 234529, Int.ofNat 41545, Int.ofNat 6585,
    Int.ofNat 902, Int.ofNat 97, Int.ofNat 4, Int.ofNat 0 ]
private def hm128Ch_r128_3 : List DickeSol.Rkm128kSeg := [
  hm128M 2 1221403 1 37 127 [32204043229413255, 134472005, 16384],
  hm128M 2 1220947 1 37 91 [55824388493276156, 34356494613],
  hm128M 2 1239936 1 37 122 [126620252852891, 22688176810, 512],
  hm128M 2 1239706 1 37 99 [39511122444422917, 7769524147062],
  hm128M 2 853320 1 31 93 [58331894454524947, 68726948980],
  hm128M 2 850776 1 31 104 [37207013523305691, 218802824459276],
  hm128M 2 800786 1 30 92 [14597741333752026, 34396487783],
  hm128M 2 799446 1 30 126 [64391270501687583, 3910491560111972, 8192],
  hm128M 2 859763 1 31 126 [18025625840326256, 154629050427, 8192],
  hm128M 2 858164 1 31 112 [40778739064819266, 41324045018567041]]
private def hm128Vec_r128_3 : List ℤ :=
  [ Int.ofNat 2313967, Int.ofNat 2907382, Int.ofNat 11585679, Int.ofNat 30192840,
    Int.ofNat 18819299, Int.ofNat 39921357, Int.ofNat 19399101, Int.ofNat 29999529,
    Int.negSucc 8351561, Int.negSucc 64975669, Int.negSucc 73954304, Int.negSucc 328511679,
    Int.negSucc 213604670, Int.negSucc 95168127, Int.negSucc 54117199, Int.negSucc 216616937,
    Int.ofNat 287885240, Int.ofNat 205530528, Int.negSucc 164319463, Int.negSucc 215760496,
    Int.negSucc 100401246, Int.ofNat 179500798, Int.negSucc 315678641, Int.negSucc 82770910,
    Int.ofNat 269681445, Int.ofNat 500074095, Int.ofNat 181776564, Int.negSucc 502764646,
    Int.negSucc 139354978, Int.negSucc 209689242, Int.negSucc 892748248, Int.negSucc 1111480093,
    Int.negSucc 3355798858, Int.negSucc 2641537673, Int.ofNat 1388383336, Int.ofNat 3528795508,
    Int.ofNat 1407084987, Int.negSucc 3186657135, Int.ofNat 2629581032, Int.negSucc 3191556648,
    Int.ofNat 3634395125, Int.ofNat 2934606697, Int.negSucc 1104074650, Int.ofNat 4578514358,
    Int.ofNat 3487536280, Int.ofNat 2156035337, Int.ofNat 947662152, Int.ofNat 1480343351,
    Int.negSucc 3714302524, Int.negSucc 4830365144, Int.ofNat 2024109574, Int.ofNat 4441677303,
    Int.ofNat 1566526085, Int.ofNat 7496390780, Int.negSucc 7220422793, Int.negSucc 20822952597,
    Int.negSucc 7314933592, Int.negSucc 7121710358, Int.negSucc 907945814,
    Int.negSucc 12930468670, Int.ofNat 55883405309, Int.negSucc 22059753219,
    Int.negSucc 34009480830, Int.negSucc 3426913000, Int.negSucc 4362364067, Int.ofNat 853018144,
    Int.negSucc 35641922946, Int.ofNat 52188233119, Int.negSucc 34577265791,
    Int.ofNat 47084348855, Int.ofNat 103325575608, Int.ofNat 41909278287, Int.ofNat 14107456964,
    Int.ofNat 21997023763, Int.ofNat 99924601603, Int.negSucc 74201284865,
    Int.ofNat 305945485104, Int.negSucc 284262323999, Int.ofNat 136674140820,
    Int.negSucc 443600805297, Int.ofNat 487576139005, Int.negSucc 155921833230,
    Int.negSucc 58719869101, Int.ofNat 738496256347, Int.negSucc 83802891923,
    Int.ofNat 64344289238, Int.negSucc 452482617294, Int.negSucc 468973002833,
    Int.negSucc 481527379745, Int.ofNat 92371709058, Int.ofNat 312265391243,
    Int.negSucc 71071206862, Int.ofNat 1128589007077, Int.negSucc 1364809699825,
    Int.ofNat 930234085781, Int.ofNat 109032029510, Int.negSucc 381641815238,
    Int.negSucc 1018449438045, Int.ofNat 668614708339, Int.ofNat 1340349006219,
    Int.ofNat 247949438913, Int.ofNat 2794283402247, Int.ofNat 3754113198581,
    Int.ofNat 3927231833877, Int.ofNat 644428095181, Int.negSucc 2085681241287,
    Int.negSucc 8324467976619, Int.negSucc 4599002370729, Int.negSucc 5858627736227,
    Int.ofNat 1633364438414, Int.negSucc 11354336943785, Int.ofNat 7491633749447,
    Int.ofNat 35912397565676, Int.ofNat 124376013891446, Int.ofNat 242467545967317,
    Int.ofNat 358571415799008, Int.ofNat 438421852865343, Int.ofNat 460085057368161,
    Int.ofNat 422267531682754, Int.ofNat 342414509510268, Int.ofNat 246532171971770,
    Int.ofNat 157630905442667, Int.ofNat 89605110525555, Int.ofNat 44005431948875,
    Int.ofNat 21225471278177, Int.ofNat 4605342282133, Int.ofNat 614293525541,
    Int.ofNat 127914620805, Int.ofNat 33739717975 ]
private def hm128Ch_r128_4 : List DickeSol.Rkm128kSeg := [
  hm128M 2 783458 1 30 98 [58974030351153347, 2201170912977],
  hm128M 2 784626 1 30 128 [31243160746474084, 31809890055050881, 32775],
  hm128M 2 841909 1 31 100 [64765861682076548, 8796228399312],
  hm128M 2 839246 1 31 128 [61362196422075470, 1125903415396865, 32818],
  hm128M 2 1290345 1 38 120 [12426555210338519, 45178944372613544, 191],
  hm128M 2 796650 1 30 105 [259686516392925, 290271137892634],
  hm128M 2 800069 1 30 114 [35076138667554673, 35322918334455, 2],
  hm128M 2 836840 1 31 106 [41237735100472048, 567348135264770],
  hm128M 2 836997 1 31 124 [23327134948562648, 64749728759295892, 3798],
  hm128M 2 841408 1 31 111 [19229307349549557, 20266473205269190],
  hm128M 2 726404 1 29 120 [6897883299464328, 9289223991460652, 136]]
private def hm128Vec_r128_4 : List ℤ :=
  [ Int.negSucc 85707, Int.negSucc 2377545, Int.negSucc 5125155, Int.negSucc 4482769,
    Int.ofNat 5687392, Int.ofNat 12495354, Int.ofNat 6776311, Int.ofNat 7585946,
    Int.ofNat 21785009, Int.ofNat 13809469, Int.negSucc 8686643, Int.negSucc 13282310,
    Int.negSucc 62493493, Int.negSucc 60985499, Int.ofNat 61792776, Int.ofNat 52625815,
    Int.negSucc 8735293, Int.negSucc 13580484, Int.negSucc 38226086, Int.negSucc 237495554,
    Int.negSucc 125317817, Int.ofNat 40181551, Int.ofNat 10731165, Int.ofNat 28597868,
    Int.ofNat 114825365, Int.ofNat 84337655, Int.ofNat 43788620, Int.ofNat 343371199,
    Int.ofNat 325764721, Int.negSucc 251465840, Int.negSucc 394171880, Int.negSucc 156082648,
    Int.ofNat 26133182, Int.negSucc 217682635, Int.negSucc 37103879, Int.ofNat 34306013,
    Int.ofNat 219810956, Int.ofNat 184141192, Int.ofNat 177892316, Int.negSucc 772809863,
    Int.negSucc 218860378, Int.ofNat 661888258, Int.ofNat 456298987, Int.ofNat 844097300,
    Int.ofNat 461722539, Int.negSucc 78027591, Int.ofNat 1274682883, Int.negSucc 2215622244,
    Int.negSucc 1832367776, Int.negSucc 226452379, Int.negSucc 2896658404, Int.ofNat 2095542620,
    Int.ofNat 10864856620, Int.ofNat 6385761341, Int.negSucc 8758811701, Int.negSucc 2847351844,
    Int.ofNat 275496818, Int.negSucc 12151506612, Int.negSucc 12010954366, Int.ofNat 15424261713,
    Int.ofNat 5250019760, Int.negSucc 59024596154, Int.negSucc 145123560550,
    Int.negSucc 93276011277, Int.negSucc 34170126873, Int.negSucc 10899837642,
    Int.ofNat 68301663308, Int.ofNat 79380098126, Int.negSucc 107821158053,
    Int.ofNat 87479501402, Int.negSucc 168437378465, Int.ofNat 11271810569,
    Int.ofNat 594346066865, Int.negSucc 167876038014, Int.ofNat 100172427753,
    Int.negSucc 245732079795, Int.negSucc 29931378054, Int.ofNat 192729533630,
    Int.ofNat 40193805072, Int.ofNat 496451200526, Int.negSucc 1341883905840,
    Int.ofNat 1677538254431, Int.negSucc 684770902362, Int.ofNat 501025662037,
    Int.ofNat 358402477897, Int.negSucc 225193238267, Int.ofNat 746367331972,
    Int.ofNat 454004550538, Int.negSucc 1596699653089, Int.ofNat 1312102693402,
    Int.negSucc 1239529543940, Int.ofNat 1371991397010, Int.ofNat 3530341702025,
    Int.negSucc 255083050645, Int.negSucc 1928058759391, Int.negSucc 275579767226,
    Int.negSucc 950348164043, Int.negSucc 518191188829, Int.negSucc 1549354195652,
    Int.ofNat 2799716318223, Int.negSucc 1042700449464, Int.negSucc 740106435243,
    Int.negSucc 2612318527448, Int.ofNat 2118445538526, Int.negSucc 485653434072,
    Int.negSucc 3167011067490, Int.ofNat 537545531213, Int.ofNat 3870760827925,
    Int.negSucc 1878376137511, Int.ofNat 530186293530, Int.negSucc 1832518207256,
    Int.ofNat 2909954813857, Int.negSucc 3810466035895, Int.negSucc 3396395293625,
    Int.ofNat 3746408040295, Int.negSucc 459350921497, Int.negSucc 1781478782298,
    Int.ofNat 15483794456711, Int.ofNat 3342609315255, Int.ofNat 2031911065070,
    Int.ofNat 26667925465873, Int.negSucc 6226359445283, Int.ofNat 4107753901108,
    Int.ofNat 53394771720968, Int.ofNat 8484376330023, Int.ofNat 99074695841580,
    Int.ofNat 468826647807212, Int.ofNat 728938989147144, Int.ofNat 484715119515012 ]
private def hm128Ch_r128_5 : List DickeSol.Rkm128kSeg := [
  hm128M 2 733188 1 29 126 [46180297729547882, 704512075507784, 8192],
  hm128M 2 619150 1 27 125 [42623771439141627, 5577489661501770, 6999],
  hm128M 2 1110036 1 35 127 [1076426913635905, 12168297332085304, 31292],
  hm128M 2 593102 1 26 123 [35333914388141051, 26531803989033409, 1938],
  hm128M 2 963212 1 33 127 [1025047484177516, 9007233614479379, 20480]]
private def hm128Vec_r128_5 : List ℤ :=
  [ Int.ofNat 288405, Int.ofNat 539879, Int.ofNat 1585110, Int.negSucc 2600938, Int.ofNat 676319,
    Int.negSucc 5275305, Int.negSucc 1296426, Int.ofNat 11186933, Int.negSucc 1403548,
    Int.negSucc 3280011, Int.negSucc 2546035, Int.ofNat 10879282, Int.ofNat 22374709,
    Int.negSucc 13013763, Int.ofNat 9796668, Int.negSucc 46253833, Int.ofNat 6720699,
    Int.negSucc 30966221, Int.ofNat 12143070, Int.ofNat 88656576, Int.negSucc 64281778,
    Int.ofNat 49189800, Int.negSucc 23168097, Int.negSucc 90738353, Int.ofNat 50417814,
    Int.negSucc 866698, Int.ofNat 170526960, Int.negSucc 91219857, Int.ofNat 178981057,
    Int.ofNat 174377774, Int.negSucc 117005963, Int.negSucc 302027293, Int.negSucc 166800490,
    Int.negSucc 71736836, Int.negSucc 91221921, Int.ofNat 143675655, Int.ofNat 274851542,
    Int.ofNat 289334380, Int.ofNat 358472730, Int.negSucc 315867555, Int.ofNat 56167711,
    Int.negSucc 180133811, Int.ofNat 333330462, Int.negSucc 192456227, Int.negSucc 757126632,
    Int.ofNat 535912590, Int.negSucc 846962023, Int.ofNat 737762598, Int.ofNat 725805823,
    Int.ofNat 211174311, Int.negSucc 2291506355, Int.negSucc 1830752600, Int.negSucc 4056325061,
    Int.ofNat 892246856, Int.negSucc 685228075, Int.ofNat 2053796044, Int.ofNat 3852638883,
    Int.negSucc 3289402791, Int.ofNat 8407781544, Int.ofNat 5437984197, Int.ofNat 6794315399,
    Int.ofNat 3588197585, Int.negSucc 21046928687, Int.ofNat 90681163435,
    Int.negSucc 248842873942, Int.ofNat 82675954336, Int.negSucc 121930354696,
    Int.ofNat 178259082860, Int.negSucc 249714376002, Int.ofNat 612931227122,
    Int.negSucc 1417916934770, Int.ofNat 758407151720, Int.ofNat 1202776089737,
    Int.ofNat 244257099369, Int.ofNat 124022953809, Int.ofNat 584388177146,
    Int.negSucc 940890468374, Int.ofNat 1544414959954, Int.negSucc 340071054480,
    Int.ofNat 481844450319, Int.ofNat 108729664412, Int.negSucc 950824211416,
    Int.ofNat 1670358607680, Int.negSucc 385355304341, Int.negSucc 236648308501,
    Int.negSucc 57153248795, Int.ofNat 154591140782, Int.ofNat 34129465558,
    Int.ofNat 1339480200143, Int.negSucc 56298127313, Int.negSucc 3083792755543,
    Int.ofNat 363768872526, Int.negSucc 392148461081, Int.negSucc 2651770231952,
    Int.ofNat 2244548593849, Int.negSucc 871185957199, Int.ofNat 645082533622,
    Int.negSucc 2015437381167, Int.negSucc 681599883107, Int.ofNat 140394791436,
    Int.negSucc 1302876508404, Int.ofNat 2391387772834, Int.ofNat 405066847971,
    Int.negSucc 1282484678068, Int.ofNat 3349836849122, Int.negSucc 2789015015195,
    Int.ofNat 4086476786394, Int.ofNat 858426552140, Int.ofNat 2142679410493,
    Int.negSucc 174212861787, Int.ofNat 130938678235, Int.negSucc 1578747599473,
    Int.negSucc 566101764757, Int.ofNat 4490128809088, Int.ofNat 4473117792310,
    Int.negSucc 1020286619604, Int.ofNat 6149608812430, Int.negSucc 3350964951469,
    Int.negSucc 9929834821940, Int.negSucc 13226265703869, Int.ofNat 28870333714425,
    Int.negSucc 10789830862179, Int.ofNat 4818525132273, Int.ofNat 8093736698502,
    Int.negSucc 14032844419136, Int.ofNat 27356105558472, Int.ofNat 4497713131022,
    Int.ofNat 68791348621709, Int.ofNat 996395875789120 ]
private def hm128St_r128_fin : Hm128St :=
  (2, 128, 1089388, hm128Vec_r128_5)
private def hm128Sgs_r128 : List DickeSol.Rkm128kSeg :=
  hm128Ch_r128_0 ++ (hm128Ch_r128_1 ++ (hm128Ch_r128_2 ++
    (hm128Ch_r128_3 ++ (hm128Ch_r128_4 ++ hm128Ch_r128_5))))
private def hm128Anc_r128 : DickeSol.RampKick128kAnchor :=
  ⟨128, hm128Sgs_r128, hm128Row_r128⟩
private def hm128k128Anchors : List DickeSol.RampKick128kAnchor :=
  [ hm128Anc_r3, hm128Anc_r4, hm128Anc_r5, hm128Anc_r6, hm128Anc_r7, hm128Anc_r8, hm128Anc_r9,
    hm128Anc_r10, hm128Anc_r11, hm128Anc_r12, hm128Anc_r13, hm128Anc_r15, hm128Anc_r16,
    hm128Anc_r20, hm128Anc_r22, hm128Anc_r24, hm128Anc_r27, hm128Anc_r32, hm128Anc_r38,
    hm128Anc_r51, hm128Anc_r64, hm128Anc_r128 ]

private theorem hm128Batch0_ok : hm128AtF
    [ hm128ChkRow 3 hm128Sgs_r3 hm128Row_r3, hm128ChkRow 4 hm128Sgs_r4 hm128Row_r4,
      hm128ChkRow 5 hm128Sgs_r5 hm128Row_r5, hm128ChkRow 6 hm128Sgs_r6 hm128Row_r6,
      hm128ChkRow 7 hm128Sgs_r7 hm128Row_r7, hm128ChkRow 8 hm128Sgs_r8 hm128Row_r8,
      hm128ChkRow 9 hm128Sgs_r9 hm128Row_r9, hm128ChkRow 10 hm128Sgs_r10 hm128Row_r10,
      hm128ChkRow 11 hm128Sgs_r11 hm128Row_r11, hm128ChkRow 12 hm128Sgs_r12 hm128Row_r12,
      hm128ChkRow 13 hm128Sgs_r13 hm128Row_r13, hm128ChkRow 15 hm128Sgs_r15 hm128Row_r15,
      hm128ChkRow 16 hm128Sgs_r16 hm128Row_r16, hm128ChkRow 20 hm128Sgs_r20 hm128Row_r20,
      hm128ChkRow 27 hm128Sgs_r27 hm128Row_r27 ]
    = true := by decide +kernel

private theorem hm128Batch1_ok : hm128AtF
    [ hm128ChkRow 22 hm128Sgs_r22 hm128Row_r22, hm128ChkRow 24 hm128Sgs_r24 hm128Row_r24,
      hm128ChkRow 51 hm128Sgs_r51 hm128Row_r51, hm128LenGuard 64 hm128Sgs_r64,
      hm128FinGuard hm128St_r64_fin hm128Row_r64, hm128LenGuard 128 hm128Sgs_r128,
      hm128FinGuard hm128St_r128_fin hm128Row_r128,
      DickeSol.rkm128kCheckTable 128 128 2 true hm128k128VPot hm128k128Anchors,
      hm128ChkCell 8 2 11419214186997 50000000000000 hm128k128VPot hm128k128Anchors,
      hm128ChkCell 16 2 38426409743409 250000000000000 hm128k128VPot hm128k128Anchors,
      hm128ChkCell 32 2 107566698366869 1000000000000000 hm128k128VPot hm128k128Anchors,
      hm128ChkCell 64 2 81067657171691 1000000000000000 hm128k128VPot hm128k128Anchors,
      hm128ChkCell 128 2 14113582515393 200000000000000 hm128k128VPot hm128k128Anchors ]
    = true := by decide +kernel

private theorem hm128Batch2_ok : hm128AtF
    [ hm128ChkRow 32 hm128Sgs_r32 hm128Row_r32,
      hm128ChkSlice 64 hm128Ch_r64_1 1 64 239185 hm128Vec_r64_0 hm128St_r64_fin ]
    = true := by decide +kernel

private theorem hm128Batch3_ok : hm128AtF
    [ hm128ChkRow 38 hm128Sgs_r38 hm128Row_r38,
      hm128ChkSlice 128 hm128Ch_r128_5 2 128 1033211 hm128Vec_r128_4 hm128St_r128_fin ]
    = true := by decide +kernel

private theorem hm128Batch4_ok :
    hm128ChkSlice 64 hm128Ch_r64_0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (1, 64, 239185, hm128Vec_r64_0) = true := by decide +kernel

private theorem hm128Batch5_ok :
    hm128ChkSlice 128 hm128Ch_r128_0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (1, 128, 159782, hm128Vec_r128_0) = true := by decide +kernel

private theorem hm128Batch6_ok :
    hm128ChkSlice 128 hm128Ch_r128_1 1 128 159782 hm128Vec_r128_0
      (1, 128, 345938, hm128Vec_r128_1) = true := by decide +kernel

private theorem hm128Batch7_ok :
    hm128ChkSlice 128 hm128Ch_r128_2 1 128 345938 hm128Vec_r128_1
      (2, 128, 587467, hm128Vec_r128_2) = true := by decide +kernel

private theorem hm128Batch8_ok :
    hm128ChkSlice 128 hm128Ch_r128_3 2 128 587467 hm128Vec_r128_2
      (2, 128, 842338, hm128Vec_r128_3) = true := by decide +kernel

private theorem hm128Batch9_ok :
    hm128ChkSlice 128 hm128Ch_r128_4 2 128 842338 hm128Vec_r128_3
      (2, 128, 1033211, hm128Vec_r128_4) = true := by decide +kernel

private theorem hm128RowOk_r3 :
    DickeSol.rkm128kEvalRowLo12 128 2 3 hm128Sgs_r3 = hm128Row_r3 :=
  hm128_row_eq (hm128_hd hm128Batch0_ok)
private theorem hm128RowOk_r4 :
    DickeSol.rkm128kEvalRowLo12 128 2 4 hm128Sgs_r4 = hm128Row_r4 :=
  hm128_row_eq (hm128_hd (hm128_tl1 hm128Batch0_ok))
private theorem hm128RowOk_r5 :
    DickeSol.rkm128kEvalRowLo12 128 2 5 hm128Sgs_r5 = hm128Row_r5 :=
  hm128_row_eq (hm128_hd (hm128_tl2 hm128Batch0_ok))
private theorem hm128RowOk_r6 :
    DickeSol.rkm128kEvalRowLo12 128 2 6 hm128Sgs_r6 = hm128Row_r6 :=
  hm128_row_eq (hm128_hd (hm128_tl1 (hm128_tl2 hm128Batch0_ok)))
private theorem hm128RowOk_r7 :
    DickeSol.rkm128kEvalRowLo12 128 2 7 hm128Sgs_r7 = hm128Row_r7 :=
  hm128_row_eq (hm128_hd (hm128_tl4 hm128Batch0_ok))
private theorem hm128RowOk_r8 :
    DickeSol.rkm128kEvalRowLo12 128 2 8 hm128Sgs_r8 = hm128Row_r8 :=
  hm128_row_eq (hm128_hd (hm128_tl1 (hm128_tl4 hm128Batch0_ok)))
private theorem hm128RowOk_r9 :
    DickeSol.rkm128kEvalRowLo12 128 2 9 hm128Sgs_r9 = hm128Row_r9 :=
  hm128_row_eq (hm128_hd (hm128_tl2 (hm128_tl4 hm128Batch0_ok)))
private theorem hm128RowOk_r10 :
    DickeSol.rkm128kEvalRowLo12 128 2 10 hm128Sgs_r10 = hm128Row_r10 :=
  hm128_row_eq (hm128_hd (hm128_tl1 (hm128_tl2 (hm128_tl4 hm128Batch0_ok))))
private theorem hm128RowOk_r11 :
    DickeSol.rkm128kEvalRowLo12 128 2 11 hm128Sgs_r11 = hm128Row_r11 :=
  hm128_row_eq (hm128_hd (hm128_tl4 (hm128_tl4 hm128Batch0_ok)))
private theorem hm128RowOk_r12 :
    DickeSol.rkm128kEvalRowLo12 128 2 12 hm128Sgs_r12 = hm128Row_r12 :=
  hm128_row_eq (hm128_hd (hm128_tl1 (hm128_tl4 (hm128_tl4 hm128Batch0_ok))))
private theorem hm128RowOk_r13 :
    DickeSol.rkm128kEvalRowLo12 128 2 13 hm128Sgs_r13 = hm128Row_r13 :=
  hm128_row_eq (hm128_hd (hm128_tl2 (hm128_tl4 (hm128_tl4 hm128Batch0_ok))))
private theorem hm128RowOk_r15 :
    DickeSol.rkm128kEvalRowLo12 128 2 15 hm128Sgs_r15 = hm128Row_r15 :=
  hm128_row_eq (hm128_hd (hm128_tl1 (hm128_tl2 (hm128_tl4 (hm128_tl4 hm128Batch0_ok)))))
private theorem hm128RowOk_r16 :
    DickeSol.rkm128kEvalRowLo12 128 2 16 hm128Sgs_r16 = hm128Row_r16 :=
  hm128_row_eq (hm128_hd (hm128_tl4 (hm128_tl4 (hm128_tl4 hm128Batch0_ok))))
private theorem hm128RowOk_r20 :
    DickeSol.rkm128kEvalRowLo12 128 2 20 hm128Sgs_r20 = hm128Row_r20 :=
  hm128_row_eq (hm128_hd (hm128_tl1 (hm128_tl4 (hm128_tl4 (hm128_tl4 hm128Batch0_ok)))))
private theorem hm128RowOk_r27 :
    DickeSol.rkm128kEvalRowLo12 128 2 27 hm128Sgs_r27 = hm128Row_r27 :=
  hm128_row_eq (hm128_hd (hm128_tl2 (hm128_tl4 (hm128_tl4 (hm128_tl4 hm128Batch0_ok)))))
private theorem hm128RowOk_r22 :
    DickeSol.rkm128kEvalRowLo12 128 2 22 hm128Sgs_r22 = hm128Row_r22 :=
  hm128_row_eq (hm128_hd hm128Batch1_ok)
private theorem hm128RowOk_r24 :
    DickeSol.rkm128kEvalRowLo12 128 2 24 hm128Sgs_r24 = hm128Row_r24 :=
  hm128_row_eq (hm128_hd (hm128_tl1 hm128Batch1_ok))
private theorem hm128RowOk_r51 :
    DickeSol.rkm128kEvalRowLo12 128 2 51 hm128Sgs_r51 = hm128Row_r51 :=
  hm128_row_eq (hm128_hd (hm128_tl2 hm128Batch1_ok))
private theorem hm128RowOk_r32 :
    DickeSol.rkm128kEvalRowLo12 128 2 32 hm128Sgs_r32 = hm128Row_r32 :=
  hm128_row_eq (hm128_hd hm128Batch2_ok)
private theorem hm128RowOk_r38 :
    DickeSol.rkm128kEvalRowLo12 128 2 38 hm128Sgs_r38 = hm128Row_r38 :=
  hm128_row_eq (hm128_hd hm128Batch3_ok)

private theorem hm128RowOk_r64 :
    DickeSol.rkm128kEvalRowLo12 128 2 64 hm128Sgs_r64 = hm128Row_r64 := by
  have h1 := hm128_sl_end (hm128_hd (hm128_tl1 hm128Batch2_ok))
  have h0 : DickeSol.rkm128kRunSegs 128 2 64 hm128Sgs_r64 1 0 1 [Int.ofNat DickeSol.wdScale] =
      hm128St_r64_fin := by unfold hm128Sgs_r64; exact hm128_sl_step hm128Batch4_ok h1
  exact hm128_cert_row hm128Sgs_r64 hm128St_r64_fin hm128Row_r64
    (hm128_hd (hm128_tl1 (hm128_tl2 hm128Batch1_ok))) h0 (hm128_hd (hm128_tl4 hm128Batch1_ok))

private theorem hm128RowOk_r128 :
    DickeSol.rkm128kEvalRowLo12 128 2 128 hm128Sgs_r128 = hm128Row_r128 := by
  have h5 := hm128_sl_end (hm128_hd (hm128_tl1 hm128Batch3_ok))
  have h4 := hm128_sl_step hm128Batch9_ok h5
  have h3 := hm128_sl_step hm128Batch8_ok h4
  have h2 := hm128_sl_step hm128Batch7_ok h3
  have h1 := hm128_sl_step hm128Batch6_ok h2
  have h0 : DickeSol.rkm128kRunSegs 128 2 128 hm128Sgs_r128 1 0 1 [Int.ofNat DickeSol.wdScale] =
      hm128St_r128_fin := by unfold hm128Sgs_r128; exact hm128_sl_step hm128Batch5_ok h1
  exact hm128_cert_row hm128Sgs_r128 hm128St_r128_fin hm128Row_r128
    (hm128_hd (hm128_tl1 (hm128_tl4 hm128Batch1_ok)))
    h0 (hm128_hd (hm128_tl2 (hm128_tl4 hm128Batch1_ok)))

private theorem hm128AnchorsSound :
    DickeSol.RampKick128kAnchorsSound 128 2 hm128k128Anchors :=
  ⟨hm128RowOk_r3, ⟨hm128RowOk_r4, ⟨hm128RowOk_r5, ⟨hm128RowOk_r6, ⟨hm128RowOk_r7,
    ⟨hm128RowOk_r8, ⟨hm128RowOk_r9, ⟨hm128RowOk_r10, ⟨hm128RowOk_r11, ⟨hm128RowOk_r12,
    ⟨hm128RowOk_r13, ⟨hm128RowOk_r15, ⟨hm128RowOk_r16, ⟨hm128RowOk_r20, ⟨hm128RowOk_r22,
    ⟨hm128RowOk_r24, ⟨hm128RowOk_r27, ⟨hm128RowOk_r32, ⟨hm128RowOk_r38, ⟨hm128RowOk_r51,
    ⟨hm128RowOk_r64, ⟨hm128RowOk_r128, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem hm128k128Valid :
    DickeSol.RampKick128kTableValid 128 128 2 true hm128k128VPot hm128k128Anchors :=
  DickeSol.rkm128kCheckTable_sound hm128AnchorsSound
    (hm128_hd (hm128_tl1 (hm128_tl2 (hm128_tl4 hm128Batch1_ok))))

private theorem hm128k128CellChecks {m k : ℕ}
    (h : isHiTailM128K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (hiTailM128K128KrotovCertCellLMax m k)
      hm128k128Anchors = true ∧
      ∃ num den : ℕ, relCostHiTailM128K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (hm128k128VPot.getD k 0) num den = true := by
  unfold isHiTailM128K128KrotovCertCell at h
  split_ifs at h with hm128 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm128 hk8
    have hc := hm128_hd (hm128_tl4 (hm128_tl4 hm128Batch1_ok))
    exact ⟨hm128ChkCell_l hc, 11419214186997, 50000000000000, rfl, hm128ChkCell_r hc⟩
  · subst hm128 hk16
    have hc := hm128_hd (hm128_tl1 (hm128_tl4 (hm128_tl4 hm128Batch1_ok)))
    exact ⟨hm128ChkCell_l hc, 38426409743409, 250000000000000, rfl, hm128ChkCell_r hc⟩
  · subst hm128 hk32
    have hc := hm128_hd (hm128_tl2 (hm128_tl4 (hm128_tl4 hm128Batch1_ok)))
    exact ⟨hm128ChkCell_l hc, 107566698366869, 1000000000000000, rfl, hm128ChkCell_r hc⟩
  · subst hm128 hk64
    have hc := hm128_hd (hm128_tl1 (hm128_tl2 (hm128_tl4 (hm128_tl4 hm128Batch1_ok))))
    exact ⟨hm128ChkCell_l hc, 81067657171691, 1000000000000000, rfl, hm128ChkCell_r hc⟩
  · subst hm128 hk128
    have hc := hm128_hd (hm128_tl4 (hm128_tl4 (hm128_tl4 hm128Batch1_ok)))
    exact ⟨hm128ChkCell_l hc, 14113582515393, 200000000000000, rfl, hm128ChkCell_r hc⟩

private lemma hm128k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma hm128k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma hm128k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private lemma hm128k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b :=
  h ▸ Nat.le_add_right a d

private lemma hm128k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) :
    2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (hm128k128_le_of_add h), rfl⟩

private structure Hm128k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ hiTailM128K128KrotovCertCellLMax m k
  hl1 : 1 ≤ hiTailM128K128KrotovCertCellLMax m k
  hlm : hiTailM128K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 2 true hm128k128VPot hm128k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (hiTailM128K128KrotovCertCellLMax m k)
    hm128k128Anchors = true
  hcost : ∃ num den : ℕ, relCostHiTailM128K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (hm128k128VPot.getD k 0) num den = true

private lemma hm128k128_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hm128 : 2 ^ 7 = 128)
    (hj : (j + 1) + d1 = 11) (h128 : k + dk = 128)
    (hl2 : 2 + dl2 = hiTailM128K128KrotovCertCellLMax 128 k)
    (hl1 : 1 + dl1 = hiTailM128K128KrotovCertCellLMax 128 k)
    (hlm : hiTailM128K128KrotovCertCellLMax 128 k * 128 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (hiTailM128K128KrotovCertCellLMax 128 k)
      hm128k128Anchors = true)
    (hcost : ∃ num den : ℕ, relCostHiTailM128K128KrotovCert 128 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 128 k (hm128k128VPot.getD k 0) num den = true) :
    Hm128k128CellProps 128 k :=
  ⟨hm128 ▸ hm128k128_mem_grid 7 3 rfl, hk ▸ hm128k128_mem_grid j d1 hj,
    hm128k128_le_of_add h128, hm128k128_le_of_add (d := 126) rfl, hm128k128_le_of_add hl2,
    hm128k128_le_of_add hl1, hm128k128_le_of_add hlm, hm128k128Valid, hlmax, hcost⟩

private theorem hm128k128_all_props {m k : ℕ}
    (h : isHiTailM128K128KrotovCertCell m k = true) : Hm128k128CellProps m k := by
  rcases hm128k128CellChecks h with ⟨hlmax, hcost⟩
  unfold isHiTailM128K128KrotovCertCell at h
  split_ifs at h with hm128 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm128 hk8
    exact hm128k128_mk 3 7 120 0 1 65280 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm128 hk16
    exact hm128k128_mk 4 6 112 0 1 65280 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm128 hk32
    exact hm128k128_mk 5 5 96 0 1 65280 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm128 hk64
    exact hm128k128_mk 6 4 64 0 1 65280 rfl rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm128 hk128
    exact hm128k128_mk 7 3 0 0 1 65280 rfl rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def hiTailM128K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM128K128KrotovCertQubits n m k)) Var
      (hiTailM128K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isHiTailM128K128KrotovCertCell m k = true then
    let p := hm128k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG hm128k128VPot hm128k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the `5` `m = 128, 8 ≤ k ≤ 128` cells. -/
noncomputable def findAllJohnsonRampKick128kHiTailM128K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM128K128KrotovCertQubits n m k)) Var
      (hiTailM128K128KrotovCertQubits n m k) ((n + 1) * m) :=
  hiTailM128K128KrotovCertCircuitImpl res n m k

private lemma hm128k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isHiTailM128K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kHiTailM128K128KrotovCertCircuit res n m k =
      let p := hm128k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG hm128k128VPot hm128k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kHiTailM128K128KrotovCertCircuit
    hiTailM128K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-`1` recovery of `S` across the `5` `m = 128, 8 ≤ k ≤ 128` cells. -/
theorem hiTailM128K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isHiTailM128K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kHiTailM128K128KrotovCertCircuit res n m k).compile
        QProg.qAssign (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [hm128k128_targetSets_eq]
  have hp := hm128k128_all_props hcell
  rw [hm128k128_circuit_eq res n hcell, ← hm128k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG hm128k128VPot hm128k128Anchors
    hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across `m = 128, 8 ≤ k ≤ 128`. -/
theorem hiTailM128K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isHiTailM128K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kHiTailM128K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostHiTailM128K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := hm128k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG
    hm128k128VPot hm128k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm
    hp.htab hp.hlmax hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [hm128k128_circuit_eq res n hcell, ← hm128k128_oracle_eq]
    exact hq S (by rwa [hm128k128_targetSets_eq])
  · rw [← hm128k128_targetSets_eq, ← hm128k128_vanilla_eq]; exact hsum

end

end QuantumComputation.Specs.GroverFindAll.Rk128kHiM128K128KrCert
