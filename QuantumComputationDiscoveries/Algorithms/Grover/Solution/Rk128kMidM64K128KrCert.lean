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
# Krotov `m = 64` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kMidM64K128KrCert`)

QHL-verified module packaging all `5` `m = 64, 8 ≤ k ≤ 128` cells
(`(64, 8), (64, 16), (64, 32), (64, 64), (64, 128)`) over `16` anchors
`r ∈ {3..9, 11, 12, 15, 16, 19, 22, 32, 64, 128}` (`521` segments, `433,867` Horner
coord-ops at `lTableMax = 4`, `useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM64K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m = 64, k ∈ {8, 16, 32, 64, 128}`, `5` cells). -/
def isMidM64K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 64 then
    if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor `L_{\max}(64, k)` across `k ∈ {8..128}`. -/
def midM64K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 64 then
    if k == 8 then 2
    else if k == 16 then 2
    else if k == 32 then 2
    else if k == 64 then 2
    else if k == 128 then 4
    else 1
  else 1

/-- Total register qubit budget `(midM64K128KrotovCertCellLMax m k * m) * (n + 1) + k * n`. -/
abbrev midM64K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (midM64K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile `c(64, k): ℚ≥0` across `k ∈ {8..128}`. -/
def relCostMidM64K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 64 then
    if k == 8 then NNRat.divNat 28990925704537 125000000000000
    else if k == 16 then NNRat.divNat 159525410088939 1000000000000000
    else if k == 32 then NNRat.divNat 59353029202209 500000000000000
    else if k == 64 then NNRat.divNat 10235536019277 100000000000000
    else if k == 128 then NNRat.divNat 9384494941081 100000000000000
    else 1
  else 1

/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def midM64K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isMidM64K128KrotovCertCell, relCostMidM64K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kMidM64K128KrCert` cell lies on `groverGrid × groverGrid`. -/
theorem isMidM64K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isMidM64K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isMidM64K128KrotovCertCell at h
  split_ifs at h with hm64 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm64 hk8; rfl
  · subst hm64 hk16; rfl
  · subst hm64 hk32; rfl
  · subst hm64 hk64; rfl
  · subst hm64 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def mm64NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem mm64NatEq_eq {x y : ℕ} (h : mm64NatEq x y = true) : x = y := by
  unfold mm64NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def mm64IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => mm64NatEq m n
  | Int.negSucc m, Int.negSucc n => mm64NatEq m n
  | _, _ => false
private theorem mm64IntEq_eq {a b : ℤ} (h : mm64IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [mm64IntEq] at h; exact congrArg Int.ofNat (mm64NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => dsimp only [mm64IntEq] at h; exact congrArg Int.negSucc (mm64NatEq_eq h)
private def mm64ListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (mm64ListEq eqF xr yr) false
  | _, _ => false
private theorem mm64ListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : mm64ListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [mm64ListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev Mm64St := ℕ × ℕ × ℕ × List ℤ
private def mm64StEq (a b : Mm64St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (mm64NatEq a1 b1)
      (cond (mm64NatEq a2 b2) (cond (mm64NatEq a3 b3) (mm64ListEq mm64IntEq av bv) false) false)
      false
private theorem mm64StEq_eq {a b : Mm64St} (h : mm64StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [mm64StEq] at h
  cases h1 : mm64NatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : mm64NatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : mm64NatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h
        exact Prod.ext (mm64NatEq_eq h1) (Prod.ext (mm64NatEq_eq h2)
          (Prod.ext (mm64NatEq_eq h3) (mm64ListEq_eq (@mm64IntEq_eq) h)))
private def mm64AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (mm64AtF rest) false
private theorem mm64_hd {b : Bool} {bs : List Bool} (h : mm64AtF (b :: bs) = true) : b = true := by
  unfold mm64AtF at h; cases b with
  | false => cases h
  | true => rfl
private theorem mm64_tl1 {b : Bool} {s : List Bool} (h : mm64AtF (b :: s) = true) :
    mm64AtF s = true := by
  unfold mm64AtF at h; cases b with
  | false => cases h
  | true => exact h
private theorem mm64_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : mm64AtF (b1 :: b2 :: bs) = true) : mm64AtF bs = true := mm64_tl1 (mm64_tl1 h)
private theorem mm64_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : mm64AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : mm64AtF bs = true := mm64_tl2 (mm64_tl2 h)
private theorem mm64_tl8 {b1 b2 b3 b4 b5 b6 b7 b8 : Bool} {bs : List Bool}
    (h : mm64AtF (b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bs) = true) :
    mm64AtF bs = true := mm64_tl4 (mm64_tl4 h)
private theorem mm64_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem mm64_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev mm64M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def mm64ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  mm64ListEq mm64NatEq (DickeSol.rkm128kEvalRowLo12 64 4 r s) ro
private def mm64ChkAnchors (xs : List DickeSol.RampKick128kAnchor) : Bool :=
  match xs with
  | [] => true
  | a :: rest =>
    match a with
    | ⟨rAct, segs, row⟩ => cond (mm64ChkRow rAct segs row) (mm64ChkAnchors rest) false
private theorem mm64ChkAnchors_append {xs rest : List DickeSol.RampKick128kAnchor}
    (hxs : mm64ChkAnchors xs = true) (hrest : DickeSol.RampKick128kAnchorsSound 64 4 rest) :
    DickeSol.RampKick128kAnchorsSound 64 4 (xs ++ rest) := by
  induction xs with
  | nil => exact hrest
  | cons a tl ih =>
    rcases a with ⟨rAct, segs, row⟩; rw [List.cons_append]
    dsimp only [mm64ChkAnchors, DickeSol.RampKick128kAnchorsSound] at hxs ⊢
    cases ha : mm64ChkRow rAct segs row with
    | false => rw [ha] at hxs; cases hxs
    | true =>
      rw [ha] at hxs; dsimp only [cond] at hxs; exact ⟨mm64ListEq_eq (@mm64NatEq_eq) ha, ih hxs⟩
private def mm64ChkSeg (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (st1 : Mm64St) : Bool := mm64StEq (DickeSol.rkm128kRunSegs 64 4 r s l0 d0 p0 v0) st1
private def mm64ChkFin (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Bool :=
  mm64ListEq mm64NatEq (DickeSol.rkm128kFinalizeState
    (DickeSol.rkm128kRunSegs 64 4 r s l0 d0 p0 v0)) ro
private def mm64SegBds (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def mm64TailOk (r : ℕ) (rest : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Prop :=
  ∃ st, DickeSol.rkm128kRunSegs 64 4 r rest l0 d0 p0 v0 = st ∧
    DickeSol.rkm128kFinalizeState st = ro
private theorem mm64TailEnd {r : ℕ} {cLast : List DickeSol.Rkm128kSeg} {l0 d0 p0 : ℕ} {v0 : List ℤ}
    {ro : List ℕ} (h : mm64ChkFin r cLast l0 d0 p0 v0 ro = true) :
    mm64TailOk r cLast l0 d0 p0 v0 ro := ⟨_, rfl, mm64ListEq_eq (@mm64NatEq_eq) h⟩
private theorem mm64TailStep {r : ℕ} {cCur rest : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {ro : List ℕ}
    (h1 : mm64ChkSeg r cCur l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : mm64TailOk r rest l1 d1 p1 v1 ro) : mm64TailOk r (cCur ++ rest) l0 d0 p0 v0 ro := by
  rcases h2 with ⟨st, hr, hf⟩; refine ⟨st, ?_, hf⟩
  unfold mm64ChkSeg at h1; rw [DickeSol.rkm128kRunSegs_append, mm64StEq_eq h1]; exact hr
private theorem mm64CertSplit {r : ℕ} {segs : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (hb : mm64SegBds r segs = true) (ht : mm64TailOk r segs 1 0 1 [Int.ofNat DickeSol.wdScale] ro) :
    DickeSol.rkm128kEvalRowLo12 64 4 r segs = ro := by
  rcases ht with ⟨st, hr, hf⟩; exact DickeSol.rkm128kCertRow_of_runSegs hb hr hf
private def mm64ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) : Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 64 k (v.getD k 0) n d)

private def mm64k128VPotP0 : List ℕ := [
  0, 80337385212341, 87092035996403, 94751282529386, 96210977552193, 97260531570855,
  98112280975809, 98855594904755, 99535079642513, 100176727279049, 125581639132382,
  101396077526320, 101991663785009, 124273245455763, 145744314799610, 103770356143790,
  104367288652140, 123851966588400, 142787669877214, 106220289593088, 124184275040026,
  141715329748140, 108172927304905, 124924430109334, 141323230195972, 157390707238441,
  173146164733393, 188607101726172, 203789440458533, 218707718373799, 233375251071060,
  247804271406164, 115857786700511, 129842730403886, 143620478301852, 157199974887047,
  170589539089104, 183796923860774, 196829368659850, 209693645835431, 222396101762098,
  234942693431004, 247339021096464, 259590357485606, 271701674003224, 283677664301183,
  295522765529260, 307241177540222 ]
private def mm64k128VPotP1 : List ℕ := [
  318836880284806, 330313649600855, 341675071574144, 352924555625717, 364065346461094,
  375100535000025, 386033068391117, 396865759203281, 407601293875205, 418242240494780,
  428791055972290, 439250092664132, 449621604497641, 459907752642197, 470110610767028,
  480232169921936, 146731965907823, 156696592160227, 166585440687395, 176400214399826,
  186142553367956, 195814038021424, 205416192141915, 214950485665641, 224418337310048,
  233821117038038, 243160148371826, 252436710567494, 261652040660360, 270807335390419,
  279903753016336, 288942415025780, 297924407749249, 306850783883954, 315722563933816,
  324540737571156, 333306264925213, 342020077802247, 350683080841607, 359296152611832,
  367860146650536, 376375892451570, 384844196402681, 393265842676680, 401641594078895,
  409972192853510, 418258361451199, 426500803260298 ]
private def mm64k128VPotP2 : List ℕ := [
  434700203303617, 442857228902839, 450972530312331, 459046741324076, 467080479845311,
  475074348450362, 483028934908079, 490944812686168, 498822541433644, 506662667442566,
  514465724090116, 522232232262045, 529962700758435, 537657626682667, 545317495814445,
  552942782967660, 560533952333841, 568091457811904, 575615743324850, 583107243124047,
  590566382081680, 597993575971932, 605389231741413, 612753747769346, 620087514117977,
  627390912773645, 634664317878950, 641908095956405, 649122606123957, 656308200302733,
  663465223417349, 670594013589114, 195423419790535 ]
private def mm64k128VPot : List ℕ :=
  mm64k128VPotP0 ++ (mm64k128VPotP1 ++ mm64k128VPotP2)
private def mm64SegsR3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23103045, 1, 22, []⟩, ⟨1, 23103045, 1, 22, []⟩, ⟨1, 27394360, 1, 24, []⟩,
  mm64M 1 15984547 1 20 4 [14], mm64M 1 58042 1 6 4 [14], mm64M 1 73559 1 6 4 [14],
  ⟨1, 51102, 1, 6, []⟩, ⟨1, 51902, 1, 6, []⟩, ⟨1, 51902, 1, 6, []⟩, mm64M 1 51902 1 6 4 [14],
  mm64M 1 252621 1 8 4 [14], ⟨1, 16692, 1, 6, []⟩, ⟨1, 16692, 1, 6, []⟩, ⟨1, 16692, 1, 6, []⟩,
  ⟨1, 16692, 1, 6, []⟩, ⟨1, 16692, 1, 6, []⟩, ⟨1, 16692, 1, 6, []⟩, ⟨1, 16692, 1, 6, []⟩,
  ⟨1, 16692, 1, 6, []⟩ ]
private def mm64RowR3 : List ℕ := [
  359435742, 54898669217, 944741895017 ]
private def mm64SegsR4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 22960026, 1, 24, []⟩, ⟨1, 23063418, 1, 24, []⟩, ⟨1, 23093782, 1, 24, []⟩,
  mm64M 1 18261108 1 22 5 [30], mm64M 1 1187061 1 10 5 [30], ⟨1, 421546, 1, 8, []⟩,
  mm64M 1 374769 1 8 5 [30], mm64M 1 612395 1 9 2 [2], mm64M 1 171607 1 7 5 [28],
  mm64M 1 93846 1 7 2 [2], mm64M 1 97046 1 7 2 [2], mm64M 1 91385 1 7 2 [2],
  mm64M 1 97385 1 7 2 [2], mm64M 1 219597 1 8 5 [28], mm64M 1 241480 1 8 2 [2],
  mm64M 1 207138 1 8 2 [2], mm64M 1 211338 1 8 2 [2], mm64M 1 118990 1 7 2 [2],
  mm64M 1 39602 1 6 2 [2], mm64M 1 142793 1 7 2 [2], mm64M 1 101489 1 7 2 [2],
  mm64M 1 35179 1 6 2 [2], mm64M 1 106329 1 7 2 [2], mm64M 1 181161 1 7 2 [2],
  mm64M 1 191231 1 7 2 [2], mm64M 1 106397 1 7 2 [2], mm64M 1 106397 1 7 2 [2],
  mm64M 1 93826 1 7 2 [2], mm64M 1 60302 1 6 2 [2], ⟨1, 41453, 1, 6, []⟩,
  mm64M 1 77960 1 7 2 [2], ⟨1, 77759, 1, 7, []⟩ ]
private def mm64RowR4 : List ℕ := [
  0, 42959195, 41343655089, 958613385680 ]
private def mm64SegsR5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 77110390, 1, 49, []⟩, mm64M 1 8040213 1 18 6 [62], mm64M 1 1285248 1 11 6 [62],
  ⟨1, 350029, 1, 8, []⟩, mm64M 1 907168 1 10 2 [2], mm64M 1 1232943 1 11 2 [2],
  ⟨1, 415781, 1, 9, []⟩, ⟨1, 387087, 1, 9, []⟩, mm64M 1 650717 1 9 6 [56],
  mm64M 1 289696 1 8 3 [4], mm64M 1 360274 1 9 3 [6], mm64M 1 403404 1 9 3 [6],
  mm64M 1 387177 1 9 3 [6], mm64M 1 330092 1 8 3 [6], mm64M 1 148229 1 7 3 [4],
  mm64M 1 163471 1 8 3 [6], mm64M 1 411701 1 9 3 [4], mm64M 1 411132 1 9 3 [4],
  mm64M 1 259944 1 8 3 [4], mm64M 1 262402 1 8 3 [4], ⟨1, 102437, 1, 7, []⟩,
  ⟨1, 100345, 1, 7, []⟩, mm64M 1 74821 1 7 3 [6], mm64M 1 127257 1 7 4 [10],
  mm64M 1 58039 1 6 4 [12], mm64M 1 53529 1 6 4 [10], mm64M 1 58717 1 6 4 [12],
  mm64M 1 45746 1 6 4 [12], mm64M 1 33446 1 6 4 [10], mm64M 1 41737 1 6 4 [10],
  mm64M 1 48517 1 6 4 [12], ⟨1, 26000, 1, 6, []⟩ ]
private def mm64RowR5 : List ℕ := [
  1, 1, 38, 33394696037, 966605303843 ]
private def mm64SegsR6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 63271435, 1, 47, []⟩, mm64M 1 19466059 1 26 7 [126], mm64M 1 588762 1 10 7 [126],
  mm64M 1 2094368 1 13 2 [2], mm64M 1 968437 1 11 2 [2], mm64M 1 1717989 1 12 3 [6],
  mm64M 1 1327968 1 11 7 [122], mm64M 1 1416744 1 12 4 [14], mm64M 1 505440 1 9 4 [8],
  mm64M 1 578616 1 10 4 [14], mm64M 1 445983 1 9 4 [8], mm64M 1 215931 1 8 4 [12],
  mm64M 1 432860 1 9 4 [10], mm64M 1 776327 1 10 4 [12], ⟨1, 359900, 1, 9, []⟩,
  ⟨1, 187687, 1, 8, []⟩, mm64M 1 273677 1 8 5 [20], mm64M 1 83614 1 7 5 [20],
  mm64M 1 82803 1 7 5 [20], mm64M 1 84700 1 7 5 [20], mm64M 1 78425 1 7 5 [20],
  mm64M 1 86336 1 7 5 [20], mm64M 1 99638 1 7 5 [20], mm64M 1 93429 1 7 5 [20],
  mm64M 1 86138 1 7 5 [20], mm64M 1 78031 1 7 5 [20], mm64M 1 78775 1 7 5 [20],
  mm64M 1 85093 1 7 5 [20], mm64M 1 79653 1 7 5 [20], mm64M 1 80624 1 7 5 [20],
  mm64M 1 83311 1 7 5 [20], ⟨1, 42216, 1, 6, []⟩ ]
private def mm64RowR6 : List ℕ := [
  0, 0, 1, 235, 28147691662, 971852308027 ]
private def mm64SegsR7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 55028149, 1, 47, []⟩, ⟨1, 23309264, 1, 30, []⟩, mm64M 1 3131085 1 15 8 [254],
  mm64M 1 1770440 1 13 8 [252], mm64M 1 587867 1 10 8 [252], mm64M 1 2133392 1 13 8 [248],
  mm64M 1 2646366 1 14 4 [10], mm64M 1 1604773 1 12 4 [12], mm64M 1 1052989 1 11 5 [16],
  mm64M 1 569698 1 10 5 [16], mm64M 1 657410 1 10 5 [18], mm64M 1 710716 1 10 5 [20],
  mm64M 1 216079 1 8 3 [6], mm64M 1 527436 1 10 5 [20], mm64M 1 662088 1 10 5 [20],
  mm64M 1 447716 1 9 6 [36], mm64M 1 114651 1 7 6 [36], mm64M 1 119043 1 7 6 [36],
  mm64M 1 118230 1 7 6 [36], mm64M 1 116967 1 7 6 [36], mm64M 1 120144 1 7 6 [36],
  mm64M 1 117763 1 7 6 [36], mm64M 1 117546 1 7 6 [36], mm64M 1 117729 1 7 6 [36],
  mm64M 1 120041 1 7 6 [36], mm64M 1 118588 1 7 6 [36], mm64M 1 115929 1 7 6 [36],
  mm64M 1 118864 1 7 6 [36], mm64M 1 118179 1 7 6 [36], mm64M 1 117221 1 7 6 [36],
  mm64M 1 119206 1 7 6 [36], ⟨1, 65807, 1, 7, []⟩ ]
private def mm64RowR7 : List ℕ := [
  0, 0, 20, 3, 1940, 24449622312, 975550375648 ]
private def mm64SegsR8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 29183249, 1, 35, []⟩, ⟨1, 26992873, 1, 34, []⟩, ⟨1, 19639659, 1, 29, []⟩,
  mm64M 1 6248653 1 19 9 [508], mm64M 1 1926482 1 13 3 [4], mm64M 1 2348387 1 14 4 [8],
  mm64M 1 2739878 1 14 5 [16], mm64M 1 2550697 1 14 6 [46], mm64M 1 482307 1 10 6 [40],
  mm64M 1 542824 1 10 5 [30], mm64M 1 259 1 6 6 [40], mm64M 1 636716 1 10 6 [46],
  mm64M 1 787723 1 11 6 [46], ⟨1, 534544, 1, 10, []⟩, mm64M 1 298903 1 9 6 [40],
  mm64M 1 587726 1 10 7 [126], mm64M 1 166591 1 8 7 [96], mm64M 1 168910 1 8 7 [74],
  mm64M 1 60028 1 7 6 [50], mm64M 1 29260 1 6 5 [26], mm64M 1 79176 1 7 7 [74],
  mm64M 1 168327 1 8 7 [72], mm64M 1 168302 1 8 7 [120], mm64M 1 167645 1 8 7 [72],
  mm64M 1 167158 1 8 7 [72], mm64M 1 168442 1 8 7 [72], mm64M 1 169522 1 8 7 [96],
  mm64M 1 169407 1 8 7 [80], mm64M 1 169844 1 8 7 [72], mm64M 1 170126 1 8 7 [120],
  mm64M 1 169812 1 8 7 [72], ⟨1, 97678, 1, 7, []⟩ ]
private def mm64RowR8 : List ℕ := [
  13, 13, 1, 116, 79, 9947, 21708084534, 978291905242 ]
private def mm64SegsR9 : List DickeSol.Rkm128kSeg := [
  ⟨1, 26361877, 1, 35, []⟩, ⟨1, 13022632, 1, 25, []⟩, ⟨1, 10937987, 1, 24, []⟩,
  ⟨1, 9186886, 1, 22, []⟩, ⟨1, 7143934, 1, 20, []⟩, ⟨1, 5999881, 1, 19, []⟩,
  ⟨1, 5051489, 1, 18, []⟩, mm64M 1 4221037 1 17 3 [6], mm64M 1 3562415 1 16 4 [13],
  mm64M 1 2976673 1 15 5 [20], mm64M 1 2254262 1 14 6 [33], mm64M 1 2307010 1 14 7 [73],
  mm64M 1 1878136 1 13 4 [9], mm64M 1 1426598 1 13 8 [129], mm64M 1 1155564 1 12 8 [145],
  ⟨1, 1116844, 1, 12, []⟩ ]
private def mm64RowR9 : List ℕ := [
  102, 9, 2247, 79, 4100973, 2725804, 9951939, 19567259557, 980415959244 ]
private def mm64SegsR11 : List DickeSol.Rkm128kSeg := [
  ⟨1, 24606096, 1, 37, []⟩, ⟨1, 12540308, 1, 27, []⟩, ⟨1, 10654675, 1, 25, []⟩,
  ⟨1, 9070745, 1, 24, []⟩, ⟨1, 7222825, 1, 22, []⟩, ⟨1, 6187990, 1, 20, []⟩,
  ⟨1, 5330137, 1, 19, []⟩, mm64M 1 4578965 1 18 3 [7], mm64M 1 3983224 1 18 5 [21],
  mm64M 1 3453268 1 17 7 [108], mm64M 1 2802606 1 16 8 [131], mm64M 1 2875905 1 16 9 [275],
  mm64M 1 2159325 1 15 9 [282], mm64M 1 1854200 1 14 10 [905], mm64M 1 1304805 1 13 10 [899],
  ⟨1, 1428741, 1, 13, []⟩ ]
private def mm64RowR11 : List ℕ := [
  0, 87, 15, 13950, 1519, 47429, 23372, 9047247, 29360335, 16665215410, 983296290582 ]
private def mm64SegsR12 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23928266, 1, 38, []⟩, ⟨1, 12376153, 1, 28, []⟩, ⟨1, 10570798, 1, 26, []⟩,
  ⟨1, 9054300, 1, 24, []⟩, ⟨1, 7285051, 1, 22, []⟩, ⟨1, 6294272, 1, 21, []⟩,
  mm64M 1 5472941 1 20 1 [1], mm64M 1 4753748 1 19 4 [14], mm64M 1 4183369 1 18 6 [60],
  mm64M 1 3676082 1 18 8 [217], mm64M 1 3045212 1 17 9 [365], mm64M 1 3127207 1 17 10 [962],
  mm64M 1 2151871 1 15 10 [567], mm64M 1 1956413 1 15 11 [2001], mm64M 1 1384940 1 13 11 [1568],
  ⟨1, 1540308, 1, 14, []⟩ ]
private def mm64RowR12 : List ℕ := [
  1, 0, 256, 16, 12, 18257, 687564, 23060, 10506262, 50472307, 14753662264, 985184629942 ]
private def mm64SegsR15 : List DickeSol.Rkm128kSeg := [
  mm64M 1 18850172 1 37 14 [12288], mm64M 1 18850174 1 37 16 [32768], ⟨1, 8736681, 1, 26, []⟩,
  ⟨1, 8736734, 1, 26, []⟩, ⟨1, 9751703, 1, 27, []⟩, mm64M 1 9751703 1 27 3 [5],
  mm64M 1 6473090 1 23 7 [104], mm64M 1 6473105 1 23 10 [978], mm64M 1 3955321 1 19 12 [2633],
  mm64M 1 3936835 1 19 13 [8132], mm64M 1 3838693 1 19 14 [9079],
  mm64M 1 1641698 1 15 14 [8582], mm64M 1 766644 1 12 11 [1619], mm64M 1 804513 1 12 14 [9360],
  mm64M 1 70166 1 8 9 [499], ⟨1, 70160, 1, 8, []⟩ ]
private def mm64RowR15 : List ℕ := [
  0, 8, 15, 8, 988, 9995, 6518, 243067, 125777, 3261320, 4497922, 3036652, 16356660,
  13200128131, 986772332868 ]
private def mm64SegsR16 : List DickeSol.Rkm128kSeg := [
  mm64M 1 27046229 1 47 15 [16384], ⟨1, 12284102, 1, 31, []⟩, ⟨1, 9490542, 1, 28, []⟩,
  ⟨1, 9364266, 1, 27, []⟩, ⟨1, 6706840, 1, 24, []⟩, mm64M 1 6609072 1 24 3 [5],
  mm64M 1 4722836 1 21 5 [21], mm64M 1 4662908 1 21 8 [161], mm64M 1 3312945 1 18 10 [800],
  mm64M 1 3286460 1 18 11 [1738], mm64M 1 2344980 1 16 12 [2562],
  mm64M 1 2351224 1 16 13 [4738], mm64M 1 1798713 1 15 13 [4098],
  mm64M 1 1400875 1 14 14 [8362], mm64M 1 1250308 1 14 14 [9354],
  mm64M 1 1159198 1 13 14 [9379], mm64M 1 790866 1 12 14 [9380], mm64M 1 810127 1 12 15 [17570],
  mm64M 1 587259 1 11 15 [16401], mm64M 1 584774 1 11 15 [17571],
  mm64M 1 459159 1 11 15 [16513], mm64M 1 348632 1 10 15 [17569],
  mm64M 1 340097 1 10 15 [17572], mm64M 1 303641 1 10 15 [17572],
  mm64M 1 258482 1 10 15 [16544], mm64M 1 228860 1 9 15 [16512], mm64M 1 196722 1 9 15 [16416],
  mm64M 1 171394 1 9 15 [16512], mm64M 1 150518 1 9 15 [17569], mm64M 1 128492 1 8 15 [17572],
  mm64M 1 116354 1 8 15 [16391], ⟨1, 95034, 1, 8, []⟩ ]
private def mm64RowR16 : List ℕ := [
  0, 3, 0, 22, 0, 1537, 0, 17758, 109792, 25, 412504, 3313917, 771063, 68437, 12508856733,
  987486448100 ]
private def mm64SegsR19 : List DickeSol.Rkm128kSeg := [
  mm64M 1 25213385 1 50 17 [98304], mm64M 1 11666727 1 33 20 [524288], ⟨1, 9101540, 1, 29, []⟩,
  ⟨1, 8987313, 1, 29, []⟩, ⟨1, 6549838, 1, 25, []⟩, mm64M 1 6457844 1 25 2 [2],
  mm64M 1 4728852 1 22 4 [10], mm64M 1 4673051 1 22 8 [196], mm64M 1 3451853 1 20 10 [653],
  mm64M 1 3411561 1 20 12 [3812], mm64M 1 2531396 1 18 13 [5902],
  mm64M 1 2539573 1 18 14 [9916], mm64M 1 2068202 1 17 15 [20091],
  mm64M 1 1716795 1 16 16 [63607], mm64M 1 1575929 1 15 16 [59724],
  mm64M 1 1472417 1 15 17 [122967], mm64M 1 1154841 1 14 17 [122894],
  mm64M 1 1171895 1 14 12 [4057], mm64M 1 894714 1 13 14 [12737],
  mm64M 1 945400 1 13 18 [261390], mm64M 1 439880 1 11 18 [249582],
  mm64M 1 543958 1 12 10 [755], mm64M 1 523827 1 12 18 [258605],
  mm64M 1 458380 1 11 18 [257487], mm64M 1 495371 1 11 13 [6603],
  mm64M 1 402352 1 11 18 [147015], mm64M 1 415627 1 11 16 [59628],
  mm64M 1 367246 1 11 18 [221287], mm64M 1 324635 1 10 18 [237303],
  mm64M 1 374098 1 11 18 [135132], mm64M 1 329127 1 10 18 [147139], ⟨1, 321444, 1, 10, []⟩ ]
private def mm64RowR19 : List ℕ := [
  0, 0, 2, 0, 0, 64, 258, 0, 951, 1059, 33525, 766, 7010, 3580, 8663064, 837040, 2824856,
  11327914739, 988659712952 ]
private def mm64SegsR22 : List DickeSol.Rkm128kSeg := [
  mm64M 1 23812062 1 52 23 [6291456], ⟨1, 11223000, 1, 34, []⟩, ⟨1, 8839176, 1, 30, []⟩,
  ⟨1, 8733006, 1, 30, []⟩, ⟨1, 6467197, 1, 26, []⟩, ⟨1, 6381999, 1, 26, []⟩,
  mm64M 1 4775211 1 23 4 [15], mm64M 1 4723353 1 23 8 [149], mm64M 1 3588473 1 21 11 [1962],
  mm64M 1 3550795 1 21 13 [5179], mm64M 1 2729921 1 19 15 [28285],
  mm64M 1 2736964 1 19 16 [34038], mm64M 1 2272765 1 18 17 [66895],
  mm64M 1 1947001 1 17 18 [153830], mm64M 1 1789078 1 17 17 [126206],
  mm64M 1 1699517 1 16 19 [490853], mm64M 1 1458077 1 16 18 [228665],
  mm64M 1 1504495 1 16 20 [798073], mm64M 1 1307868 1 15 20 [1002606],
  mm64M 1 1330856 1 15 21 [1429824], mm64M 1 87614 1 8 21 [1188329],
  mm64M 1 826986 1 13 20 [661662], mm64M 1 616801 1 12 19 [387786],
  mm64M 1 536358 1 12 21 [2093394], mm64M 1 725905 1 13 21 [2094518],
  mm64M 1 512613 1 12 21 [2065762], mm64M 1 647325 1 12 21 [1702516],
  mm64M 1 472617 1 12 20 [741950], mm64M 1 509597 1 12 21 [1951833],
  mm64M 1 544515 1 12 21 [2044140], mm64M 1 504249 1 12 21 [2019688], ⟨1, 489535, 1, 12, []⟩ ]
private def mm64RowR22 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 1, 0, 332, 105, 2262, 693, 202937, 28618, 38571, 1714225, 3254290,
  554978, 128790, 10299407213, 989694666827 ]
private def mm64SegsR32 : List DickeSol.Rkm128kSeg := [
  mm64M 1 6531059 1 31 28 [201326592], mm64M 1 6554225 1 31 30 [805306368],
  mm64M 1 6555446 1 31 31 [1073741824], mm64M 1 6554226 1 31 32 [2147483648],
  ⟨1, 3873719, 1, 24, []⟩, mm64M 1 3873721 1 24 33 [4294967296],
  mm64M 1 3873721 1 24 33 [4294967296], mm64M 1 3873721 1 24 33 [4294967296],
  mm64M 1 5977517 1 29 33 [4294967296], ⟨1, 5977517, 1, 29, []⟩,
  mm64M 1 5019543 1 27 33 [4294967296], mm64M 1 5019544 1 27 33 [4294967303],
  mm64M 1 4108983 1 25 8 [253], mm64M 1 4108983 1 25 13 [6980], mm64M 1 3629518 1 24 16 [49927],
  mm64M 1 3627490 1 24 19 [494794], mm64M 1 5792706 1 29 23 [7368013],
  mm64M 1 4649789 1 26 25 [26571757], mm64M 1 4575169 1 26 27 [110717613],
  mm64M 1 3388895 1 23 28 [146490514], mm64M 1 3254393 1 23 29 [268877242],
  mm64M 1 2234496 1 20 29 [290391265], mm64M 1 2282272 1 20 30 [543735338],
  mm64M 1 1693780 1 18 19 [449760], mm64M 1 1515470 1 17 27 [88686141],
  mm64M 1 1239334 1 16 31 [1160277972], mm64M 1 1151658 1 16 31 [1078909689],
  mm64M 1 1012906 1 15 31 [1104385455], mm64M 1 598192 1 13 25 [21719972],
  mm64M 1 621002 1 13 31 [1091115935], mm64M 1 767577 1 14 31 [1078175946],
  mm64M 1 389868 1 12 31 [1103226198], mm64M 1 465139 1 12 31 [1204026478],
  mm64M 1 317677 1 11 28 [138412160] ]
private def mm64RowR32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 1, 49, 199, 13, 26, 31833, 57974, 27730, 29345, 24518,
  3102431, 1979479, 178643, 1002659, 2146676, 25569825, 15184772, 349202, 9257806398,
  990692508000 ]
private def mm64R64C0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 1511290, 1, 21, []⟩, mm64M 1 1648178 1 22 46 [70364549873664],
  mm64M 1 1648775 1 22 65 [2779556939300864, 447],
  mm64M 1 1649185 1 22 64 [30786309203165184, 142],
  mm64M 1 1634037 1 21 65 [56580834005614592, 395],
  mm64M 1 1633958 1 21 64 [20134188208357376, 156],
  mm64M 1 1633843 1 21 64 [14640959396511744, 216],
  mm64M 1 1633785 1 21 65 [12670497120583680, 306],
  mm64M 1 1676422 1 22 65 [68125190701187072, 336],
  mm64M 1 1678094 1 22 65 [28163990345482240, 364],
  mm64M 1 1678003 1 22 65 [65335179945705472, 331],
  mm64M 1 1677728 1 22 63 [2282586139262976, 99],
  mm64M 1 1704819 1 22 61 [22553182508941312, 25],
  mm64M 1 1704820 1 22 65 [64105925945851904, 446],
  mm64M 1 1704819 1 22 64 [64105925945851904, 203],
  mm64M 1 1704820 1 22 63 [54465407993511936, 109],
  mm64M 1 2447784 1 25 62 [44754521296994304, 51],
  mm64M 1 2447784 1 25 62 [39969446692913152, 59],
  mm64M 1 2462690 1 25 64 [7881299347898368, 243],
  mm64M 1 2462691 1 25 65 [14636698788954112, 326],
  mm64M 1 2428753 1 25 63 [27021597764222976, 120],
  mm64M 1 2478253 1 25 63 [65302194596872192, 67],
  mm64M 1 1368978 1 20 65 [2251799813685248, 384],
  mm64M 1 1368213 1 20 63 [18014398509481984, 80],
  mm64M 1 1368166 1 20 62 [36028797018963968, 32] ]
private def mm64R64C1 : List DickeSol.Rkm128kSeg := [
  mm64M 1 1368160 1 20 57 [40532396646334464, 1], mm64M 1 2429187 1 25 64 [3, 135],
  mm64M 1 2429188 1 25 65 [9007199254740994, 463], mm64M 1 1353823 1 20 65 [112, 385],
  mm64M 1 1354069 1 20 58 [18014398509482194, 3],
  mm64M 1 2832460 1 27 65 [18014398509489106, 263], mm64M 1 2414519 1 25 59 [36585, 6],
  mm64M 1 2414470 1 25 63 [901022, 101], mm64M 1 2386984 1 25 63 [14275851, 114],
  mm64M 1 2386987 1 25 62 [59359958, 50], mm64M 2 754182 1 19 63 [296773307, 112],
  mm64M 2 752855 1 19 65 [806990933, 356], mm64M 2 624277 1 18 65 [2930817783, 480],
  mm64M 2 623508 1 18 63 [8529912113, 64], mm64M 2 897090 1 21 65 [14945872312, 264],
  mm64M 2 909611 1 21 36 [60997464832], mm64M 2 887432 1 20 64 [106316494767, 240],
  mm64M 2 922423 1 21 64 [516911299340, 224], mm64M 2 761620 1 19 65 [970692245357, 256],
  mm64M 2 682741 1 19 65 [2193796259950, 288], mm64M 2 750633 1 19 62 [3367836147425, 32],
  mm64M 2 807527 1 20 65 [6369043066922, 256], mm64M 2 1419268 1 24 65 [19243973167622, 256],
  mm64M 2 883507 1 20 65 [52851784134977, 256], mm64M 2 854128 1 20 47 [88859662699153],
  mm64M 2 935851 1 21 65 [219586335582045, 256] ]
private def mm64R64C2 : List DickeSol.Rkm128kSeg := [
  mm64M 2 944294 1 21 49 [387050828827207], mm64M 2 996593 1 21 50 [778133555249510],
  mm64M 2 1020369 1 22 51 [1477812389754177], mm64M 2 1034033 1 22 52 [2397394373071714],
  mm64M 2 1094085 1 22 53 [5810094405885577], mm64M 2 1234991 1 23 54 [15257946036599129],
  mm64M 2 297107 1 14 53 [5422912844415142], mm64M 2 284348 1 14 55 [28710468185523881],
  mm64M 2 387771 1 16 56 [53764556770908240], mm64M 2 177143 1 13 56 [57465456928354413],
  mm64M 2 1245919 1 23 55 [29311058229047128], mm64M 2 1878019 1 28 57 [14074911869593187, 1],
  mm64M 2 1146941 1 22 57 [26001494813853140, 1],
  mm64M 2 1699930 1 26 59 [36030001107171986, 5], mm64M 2 897682 1 21 56 [68121377328160438],
  mm64M 2 986631 1 21 60 [27039893465618027, 8], mm64M 2 757298 1 19 57 [18032068353077970, 1],
  mm64M 2 1559043 1 25 61 [59090291353330273, 31], mm64M 2 815788 1 20 37 [77590528977],
  mm64M 2 881787 1 20 58 [40532947142102236, 3], mm64M 2 661637 1 18 62 [9024791451616553, 34],
  mm64M 2 799076 1 20 61 [1690647425913317, 26], mm64M 2 36532 1 9 62 [35185750221652, 37],
  mm64M 2 792892 1 20 57 [20358289787038, 1], mm64M 2 924495 1 21 59 [22834744138140231, 4],
  mm64M 2 980472 1 21 63 [38362774519965482, 117],
  mm64M 2 422415 1 16 60 [37875151424715663, 13], mm64M 2 1091144 1 22 61 [592122179036005, 28],
  mm64M 2 1085061 1 22 60 [20267023342044268, 8] ]
private def mm64SegsR64 : List DickeSol.Rkm128kSeg :=
  mm64R64C0 ++ (mm64R64C1 ++ mm64R64C2)
private def mm64RowR64P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12, 30, 0, 6, 14, 3, 289,
  33749, 2136, 977, 828, 293492, 1, 14817, 104030, 916, 20, 1477, 128239, 216974, 369002,
  106422, 98727, 131153, 4036323, 3463983 ]
private def mm64RowR64P1 : List ℕ := [
  720594, 3377795, 217666, 3693645, 227167, 23345, 2505737, 1793145, 628701, 559273, 5537989,
  149102933, 93698898, 237147680, 9446172191, 990045588743 ]
private def mm64RowR64 : List ℕ :=
  mm64RowR64P0 ++ mm64RowR64P1
private def mm64R64V1P0 : List ℤ := [
  Int.ofNat 417085, Int.ofNat 4318060, Int.ofNat 30682405, Int.ofNat 172819771,
  Int.ofNat 818574415, Int.ofNat 3367918438, Int.ofNat 12286140334, Int.ofNat 40305981184,
  Int.ofNat 120148739617, Int.ofNat 328011438599, Int.ofNat 825216738033,
  Int.ofNat 1922728528309, Int.ofNat 4165891796956, Int.ofNat 8421831512517,
  Int.ofNat 15931106027867, Int.ofNat 28266290199364, Int.ofNat 47137097041959,
  Int.ofNat 74009354916056, Int.ofNat 109569536152498, Int.ofNat 153154125560273,
  Int.ofNat 202338430774586, Int.ofNat 252896376325645, Int.ofNat 299268878017466,
  Int.ofNat 335519730725340, Int.ofNat 356568247225343, Int.ofNat 359349958279646,
  Int.ofNat 343542116694524, Int.ofNat 311619278513719, Int.ofNat 268228119785648,
  Int.ofNat 219095886832571, Int.ofNat 169820359498887, Int.ofNat 124884455323178,
  Int.ofNat 87114282904003, Int.ofNat 57622657165904, Int.ofNat 36127770068602,
  Int.ofNat 21459181443064, Int.ofNat 12068318981869, Int.ofNat 6421472342094,
  Int.ofNat 3230140667876, Int.ofNat 1534619514266, Int.ofNat 687876374547,
  Int.ofNat 290554593150, Int.ofNat 115495016198, Int.ofNat 43137320628, Int.ofNat 15112999907,
  Int.ofNat 4956956239, Int.ofNat 1518793087, Int.ofNat 433640050 ]
private def mm64R64V1P1 : List ℤ := [
  Int.ofNat 115059528, Int.ofNat 28248192, Int.ofNat 6489355, Int.ofNat 1238205,
  Int.ofNat 182291, Int.ofNat 21154, Int.ofNat 1758, Int.negSucc 78, Int.negSucc 3, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm64R64V1 : List ℤ :=
  mm64R64V1P0 ++ mm64R64V1P1
private def mm64R64V2P0 : List ℤ := [
  Int.negSucc 17126, Int.negSucc 138932, Int.negSucc 203938, Int.negSucc 178730,
  Int.negSucc 90462, Int.negSucc 209783, Int.ofNat 1456804, Int.ofNat 3620362,
  Int.ofNat 2225414, Int.negSucc 441955, Int.ofNat 588115, Int.negSucc 2399960,
  Int.ofNat 9986850, Int.negSucc 15451316, Int.negSucc 35360772, Int.negSucc 94532393,
  Int.negSucc 82965382, Int.negSucc 108056782, Int.ofNat 44427970, Int.ofNat 148885365,
  Int.negSucc 69638900, Int.negSucc 751999822, Int.ofNat 1695850852, Int.ofNat 1047313699,
  Int.negSucc 21243379372, Int.negSucc 27598517426, Int.negSucc 59623146227,
  Int.ofNat 87955065920, Int.ofNat 59942616740, Int.ofNat 60183205556, Int.negSucc 58052094695,
  Int.negSucc 69844438043, Int.ofNat 143309945081, Int.ofNat 146218552762,
  Int.ofNat 336540636853, Int.ofNat 482926242705, Int.negSucc 461728957091,
  Int.negSucc 371554761801, Int.ofNat 194184401463, Int.ofNat 964158932391,
  Int.negSucc 2467147364941, Int.ofNat 1237962688539, Int.negSucc 708125803887,
  Int.ofNat 332166649092, Int.ofNat 390568672928, Int.ofNat 241731776365,
  Int.negSucc 388573433412, Int.ofNat 3783115712963 ]
private def mm64R64V2P1 : List ℤ := [
  Int.ofNat 19905198637700, Int.ofNat 88352441027296, Int.ofNat 198084161634379,
  Int.ofNat 323707269582255, Int.ofNat 426128161482860, Int.ofNat 471262753609981,
  Int.ofNat 447241904069988, Int.ofNat 368369335081515, Int.ofNat 264802369034856,
  Int.ofNat 166375791888593, Int.ofNat 91228259435880, Int.ofNat 43300817066851,
  Int.ofNat 17757003332490, Int.ofNat 6106544208962, Int.ofNat 1648062678152,
  Int.ofNat 322435148970, Int.negSucc 32427796487 ]
private def mm64R64V2 : List ℤ :=
  mm64R64V2P0 ++ mm64R64V2P1
private def mm64R128C0 : List DickeSol.Rkm128kSeg := [
  mm64M 1 1889785 1 28 30 [939524096], mm64M 1 2279778 1 30 65 [11873746327437312, 487],
  mm64M 1 2284029 1 30 64 [32017778600837120, 214], ⟨1, 2284030, 1, 30, []⟩,
  ⟨1, 4508259, 1, 43, []⟩, ⟨1, 4508258, 1, 43, []⟩, ⟨1, 2730185, 1, 33, []⟩,
  ⟨1, 2730186, 1, 33, []⟩, ⟨1, 2830185, 1, 33, []⟩, ⟨1, 2830185, 1, 33, []⟩,
  ⟨1, 2810185, 1, 33, []⟩, mm64M 1 2810185 1 33 1 [1], mm64M 1 2327272 1 30 3 [7],
  mm64M 2 1326884 1 30 101 [2036, 17592186044416],
  mm64M 2 1361745 1 31 129 [7503, 29273397577908224, 90880],
  mm64M 2 1357440 1 31 127 [61771, 40673134134689792, 25356],
  mm64M 2 1356428 1 31 127 [383301, 63050394783186944, 30326],
  mm64M 2 1356429 1 31 129 [2556104, 0, 115728] ]
private def mm64R128C1 : List DickeSol.Rkm128kSeg := [
  mm64M 2 1356428 1 31 129 [57146045, 0, 114156],
  mm64M 2 1356429 1 31 129 [4247711445, 0, 108544],
  mm64M 2 1656885 1 34 129 [105905205573, 0, 106500],
  mm64M 2 1656886 1 34 128 [914953143466, 0, 34816],
  mm64M 2 1656883 1 34 128 [67936796395458, 0, 32768],
  mm64M 2 1657149 1 34 128 [6278421762662611, 0, 32768],
  mm64M 2 1656836 1 34 56 [68485134333421950],
  mm64M 2 1656634 1 34 128 [71601241741002410, 4503599627370527, 32770],
  mm64M 3 765213 1 27 128 [14272148933909011, 52, 32768],
  mm64M 3 764535 1 27 128 [71330544312336136, 816, 40960],
  mm64M 3 747384 1 27 128 [13625926723633312, 5705, 32768],
  mm64M 3 749549 1 27 128 [5143905987044991, 28689, 32768] ]
private def mm64R128C2 : List DickeSol.Rkm128kSeg := [
  mm64M 3 760706 1 27 74 [25751245685221078, 230045],
  mm64M 3 763624 1 27 128 [45712469257613387, 675639, 32768],
  mm64M 3 843468 1 28 128 [38160144595840032, 1225833, 32768],
  mm64M 3 847376 1 28 128 [49264560858242217, 28164024, 32768],
  mm64M 3 751821 1 27 129 [46458636185837624, 36028797065134192, 131071],
  mm64M 3 750333 1 27 129 [14753600348147519, 283740826, 98303],
  mm64M 3 724708 1 26 128 [18036485163624655, 2231952, 33280],
  mm64M 3 736627 1 26 128 [22281854611876145, 8146681233, 32768],
  mm64M 3 879917 1 29 91 [11344364306591767, 21976143651],
  mm64M 3 1254193 1 34 120 [30835021003628331, 237710519194, 128],
  mm64M 3 1452192 1 37 126 [1349258661501423, 576273808516, 8192],
  mm64M 4 926329 1 32 126 [38398186223623099, 16594429486489, 8192],
  mm64M 4 601450 1 26 126 [19151114799156754, 17600789159460, 8192] ]
private def mm64R128C3 : List DickeSol.Rkm128kSeg := [
  mm64M 4 571059 1 26 126 [40935129639210627, 105577309224024, 8192],
  mm64M 4 506476 1 24 104 [1663383421043988, 140768224888111],
  mm64M 4 802807 1 30 124 [32751152916988393, 283674002077728, 2048],
  mm64M 4 796912 1 30 124 [67822171284893459, 3564930852168607, 2048],
  mm64M 4 1047616 1 34 125 [62322397100515468, 9860856320608049, 4096],
  mm64M 4 923658 1 32 98 [21123915708653203, 2199308730931],
  mm64M 4 904481 1 32 129 [41635984300887470, 1129019472183938, 106496],
  mm64M 4 85078 1 14 127 [63722316035884860, 27876005309542130, 16387],
  mm64M 4 638190 1 27 107 [9362381579825505, 1276533009289233],
  mm64M 4 592115 1 26 128 [55001372347066840, 3900686548206, 49160],
  mm64M 4 619761 1 27 129 [3329622041583853, 37436315810666242, 65536],
  mm64M 4 584726 1 26 118 [41894961066807376, 28992355940, 32],
  mm64M 4 825236 1 30 119 [62005648289974871, 44104350641494260, 120] ]
private def mm64R128C4 : List DickeSol.Rkm128kSeg := [
  mm64M 4 909791 1 32 99 [68035993160815093, 6857259374715],
  mm64M 4 1075091 1 35 122 [63402507001066761, 17601808625804, 720],
  mm64M 4 1051576 1 34 123 [35644063566594794, 28749400794300574, 1956],
  mm64M 4 623428 1 27 121 [11578853955629618, 1690018294399968, 256],
  mm64M 4 597783 1 26 124 [57216992362119907, 18122221811124199, 2776],
  mm64M 4 1094329 1 35 124 [70126183212840835, 442699626950359, 3344],
  mm64M 4 1021351 1 34 126 [52711714049906714, 53755698284807510, 14011],
  mm64M 4 634004 1 27 124 [1396518280892544, 10168429947919292, 2081],
  mm64M 4 549721 1 25 127 [70018096442944705, 27247278898968, 18688],
  mm64M 4 523185 1 25 127 [5155991538910357, 22527344210429219, 19463],
  mm64M 4 649788 1 27 121 [24179604178858698, 18368287083602611, 472],
  mm64M 4 826432 1 30 123 [28071551307494584, 70403636869224, 1024] ]
private def mm64SegsR128 : List DickeSol.Rkm128kSeg :=
  mm64R128C0 ++ (mm64R128C1 ++ (mm64R128C2 ++ (mm64R128C3 ++ mm64R128C4)))
private def mm64RowR128P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 10, 63, 4, 0, 0, 0, 1, 1, 0, 4 ]
private def mm64RowR128P1 : List ℕ := [
  79, 4, 93, 0, 42, 73, 0, 580, 668, 1291, 378, 27, 1144, 72, 51, 73715, 73, 88, 185, 1439, 71,
  552, 348, 612, 2100, 710, 29187, 60698, 527440, 15, 6587, 16303, 5221, 12269, 7036, 1971,
  121780, 439563, 1158420, 13985, 158364, 3228, 219558, 1522585, 947913, 33356056, 3312916,
  10919632 ]
private def mm64RowR128P2 : List ℕ := [
  183514045, 5446900, 34739, 3273470, 19437052, 2341068, 4205482, 218225524, 142126103,
  655954626, 40420314, 222765132, 297016963, 3061658, 537388574, 252435478, 698249290, 3503275,
  18853, 258213740, 141479561, 85649234, 333171316, 268815583, 140468028, 13416933, 532065433,
  184034030, 886669444, 193757398, 9493054853, 984126857226 ]
private def mm64RowR128 : List ℕ :=
  mm64RowR128P0 ++ (mm64RowR128P1 ++ mm64RowR128P2)
private def mm64R128V1P0 : List ℤ := [
  Int.negSucc 21600, Int.ofNat 31644, Int.ofNat 82447, Int.negSucc 74987, Int.negSucc 11304,
  Int.ofNat 680173, Int.ofNat 6114081, Int.negSucc 26727058, Int.negSucc 76626845,
  Int.ofNat 86621840, Int.ofNat 168142539, Int.ofNat 58358377, Int.negSucc 78753931,
  Int.negSucc 279000889, Int.negSucc 203696264, Int.negSucc 203634651, Int.negSucc 91787025,
  Int.negSucc 248698868, Int.negSucc 80138177, Int.negSucc 69590752, Int.negSucc 78367676,
  Int.negSucc 13421239, Int.ofNat 244335523, Int.ofNat 882505317, Int.ofNat 2703873744,
  Int.ofNat 7696932591, Int.ofNat 20643581050, Int.ofNat 52361184761, Int.ofNat 125864648791,
  Int.ofNat 287209521930, Int.ofNat 623059941412, Int.ofNat 1286645535985,
  Int.ofNat 2532135097008, Int.ofNat 4754025146843, Int.ofNat 8522836779748,
  Int.ofNat 14602107096485, Int.ofNat 23926531406769, Int.ofNat 37520482403967,
  Int.ofNat 56343486736255, Int.ofNat 81066445382302, Int.ofNat 111807700702989,
  Int.ofNat 147885003789111, Int.ofNat 187657689313353, Int.ofNat 228532086440658,
  Int.ofNat 267176038825186, Int.ofNat 299938017189280, Int.ofNat 323405717343402,
  Int.ofNat 334988360483243 ]
private def mm64R128V1P1 : List ℤ := [
  Int.ofNat 333385934433710, Int.ofNat 318828236024563, Int.ofNat 293023215669732,
  Int.ofNat 258830124200668, Int.ofNat 219743212063060, Int.ofNat 179313644033759,
  Int.ofNat 140639498689342, Int.ofNat 106019621648019, Int.ofNat 76812063817269,
  Int.ofNat 53481918878368, Int.ofNat 35783290616059, Int.ofNat 23003948868964,
  Int.ofNat 14207528379113, Int.ofNat 8428813659866, Int.ofNat 4802605775138,
  Int.ofNat 2627690872991, Int.ofNat 1380310316507, Int.ofNat 695980579761,
  Int.ofNat 336777677765, Int.ofNat 156357514245, Int.ofNat 69634299635, Int.ofNat 29740837356,
  Int.ofNat 12178748286, Int.ofNat 4780392835, Int.ofNat 1798152793, Int.ofNat 648009604,
  Int.ofNat 223675057, Int.ofNat 73930630, Int.ofNat 23393313, Int.ofNat 7084507,
  Int.ofNat 2052894, Int.ofNat 569040, Int.ofNat 150830, Int.ofNat 38212, Int.ofNat 9236,
  Int.ofNat 2123, Int.ofNat 456, Int.ofNat 89, Int.ofNat 13, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm64R128V1P2 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm64R128V1 : List ℤ :=
  mm64R128V1P0 ++ (mm64R128V1P1 ++ mm64R128V1P2)
private def mm64R128V2P0 : List ℤ := [
  Int.negSucc 152350, Int.ofNat 533052, Int.negSucc 1353652, Int.ofNat 82274, Int.ofNat 6115342,
  Int.ofNat 1699886, Int.ofNat 753198, Int.ofNat 33874173, Int.negSucc 11758612,
  Int.ofNat 36144605, Int.negSucc 18125349, Int.negSucc 10631130, Int.negSucc 51356668,
  Int.negSucc 61196904, Int.negSucc 4351446, Int.negSucc 61633525, Int.negSucc 134030128,
  Int.negSucc 156536513, Int.ofNat 29175125, Int.ofNat 212110705, Int.ofNat 210988573,
  Int.ofNat 664042451, Int.negSucc 999879765, Int.ofNat 1083106903, Int.ofNat 356060120,
  Int.negSucc 830316269, Int.negSucc 960938172, Int.negSucc 33239413, Int.ofNat 476971963,
  Int.negSucc 205484803, Int.ofNat 1379603848, Int.ofNat 1260012387, Int.ofNat 1015739327,
  Int.ofNat 156358573, Int.ofNat 577499416, Int.ofNat 202090961, Int.negSucc 188968187,
  Int.negSucc 838813530, Int.negSucc 713350623, Int.negSucc 4623634137, Int.negSucc 7407145169,
  Int.ofNat 2508180689, Int.negSucc 28470051971, Int.negSucc 44011154789, Int.ofNat 21233975406,
  Int.ofNat 67071080534, Int.ofNat 29196400989, Int.ofNat 13693398159 ]
private def mm64R128V2P1 : List ℤ := [
  Int.negSucc 1237659942, Int.ofNat 213376559567, Int.ofNat 167234545742,
  Int.negSucc 28734420633, Int.negSucc 99873602446, Int.negSucc 34104038264,
  Int.negSucc 195052635803, Int.ofNat 141652315700, Int.ofNat 32443728870,
  Int.negSucc 160197704841, Int.ofNat 301382624489, Int.negSucc 106422896215,
  Int.ofNat 127019417275, Int.ofNat 305925247354, Int.ofNat 80309821652,
  Int.negSucc 35051572340, Int.ofNat 115327470581, Int.negSucc 187404390457,
  Int.negSucc 249520229381, Int.negSucc 349323796353, Int.ofNat 254446521392,
  Int.ofNat 684921880231, Int.ofNat 863547847834, Int.ofNat 1028872221399,
  Int.ofNat 7499684376062, Int.ofNat 21646301629955, Int.ofNat 46541481805657,
  Int.ofNat 84119015598073, Int.ofNat 133987637021420, Int.ofNat 192695707039011,
  Int.ofNat 253866277339997, Int.ofNat 309322514262462, Int.ofNat 350927349994841,
  Int.ofNat 372551741962480, Int.ofNat 371516557703960, Int.ofNat 349056962996910,
  Int.ofNat 309732696409743, Int.ofNat 260076732996844, Int.ofNat 206985157453513,
  Int.ofNat 156343176307549, Int.ofNat 112202097692428, Int.ofNat 76577943177313,
  Int.ofNat 49741167576860, Int.ofNat 30768528856020, Int.ofNat 18133943604140,
  Int.ofNat 10186896825768, Int.ofNat 5456101815853, Int.ofNat 2786772791705 ]
private def mm64R128V2P2 : List ℤ := [
  Int.ofNat 1357532425650, Int.ofNat 630731760877, Int.ofNat 279491026471,
  Int.ofNat 118105434989, Int.ofNat 47584831745, Int.ofNat 18274651354, Int.ofNat 6687498785,
  Int.ofNat 2330936163, Int.ofNat 773448366, Int.ofNat 244180623, Int.ofNat 73294906,
  Int.ofNat 20901528, Int.ofNat 5657670, Int.ofNat 1452146, Int.ofNat 352970, Int.ofNat 81089,
  Int.ofNat 17546, Int.ofNat 3552, Int.ofNat 660, Int.ofNat 107, Int.ofNat 13, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def mm64R128V2 : List ℤ :=
  mm64R128V2P0 ++ (mm64R128V2P1 ++ mm64R128V2P2)
private def mm64R128V3P0 : List ℤ := [
  Int.ofNat 26648, Int.ofNat 56357, Int.negSucc 705964, Int.negSucc 2462699,
  Int.negSucc 5215616, Int.negSucc 9132498, Int.negSucc 609652, Int.ofNat 6227893,
  Int.negSucc 6652250, Int.negSucc 12828175, Int.ofNat 21784662, Int.ofNat 19329026,
  Int.negSucc 31937314, Int.ofNat 34389754, Int.ofNat 44166983, Int.negSucc 18130223,
  Int.negSucc 1569826, Int.negSucc 47387269, Int.negSucc 148956969, Int.negSucc 440554784,
  Int.ofNat 375542502, Int.ofNat 702647291, Int.ofNat 522948824, Int.ofNat 351932215,
  Int.ofNat 145609131, Int.negSucc 82686136, Int.negSucc 206211925, Int.ofNat 1340858979,
  Int.negSucc 264697362, Int.ofNat 707886060, Int.ofNat 197193342, Int.negSucc 925753928,
  Int.negSucc 49017448, Int.negSucc 153840708, Int.negSucc 934007119, Int.ofNat 3956067731,
  Int.ofNat 5925193102, Int.ofNat 72074047, Int.negSucc 6947044169, Int.ofNat 5742019780,
  Int.negSucc 4682679297, Int.negSucc 211216360, Int.negSucc 4014002971, Int.ofNat 647763903,
  Int.ofNat 16079981199, Int.ofNat 23232599996, Int.negSucc 12346059416, Int.ofNat 56736313908 ]
private def mm64R128V3P1 : List ℤ := [
  Int.negSucc 44388511656, Int.ofNat 27808192486, Int.negSucc 91440757690,
  Int.negSucc 102018733806, Int.ofNat 194534915798, Int.ofNat 390478527987,
  Int.negSucc 234316153269, Int.ofNat 178645419491, Int.ofNat 98245779630,
  Int.negSucc 177094075804, Int.negSucc 23818842257, Int.negSucc 139440886916,
  Int.negSucc 198180859936, Int.negSucc 48705973908, Int.ofNat 137627812446,
  Int.ofNat 30117490836, Int.negSucc 319633725575, Int.negSucc 340835939104,
  Int.ofNat 76660705566, Int.negSucc 50749156973, Int.ofNat 204081791628,
  Int.negSucc 432612751869, Int.negSucc 481850082537, Int.ofNat 134206242822,
  Int.ofNat 242658067608, Int.ofNat 1351708652766, Int.ofNat 817238895076,
  Int.ofNat 903852996136, Int.ofNat 254371558179, Int.ofNat 1337699163233,
  Int.negSucc 142992661734, Int.negSucc 535902482392, Int.ofNat 134618203966,
  Int.ofNat 232151625942, Int.negSucc 4837564200083, Int.negSucc 3954831503368,
  Int.negSucc 1728533876241, Int.ofNat 3710087366683, Int.ofNat 1893493398417,
  Int.negSucc 4610363309718, Int.ofNat 4204347412927, Int.negSucc 2222138202673,
  Int.negSucc 2078927791207, Int.ofNat 4661093288194, Int.negSucc 2384169402096,
  Int.ofNat 2495207484983, Int.negSucc 8762600624725, Int.ofNat 5372903443213 ]
private def mm64R128V3P2 : List ℤ := [
  Int.ofNat 1644065461599, Int.negSucc 11174798219290, Int.ofNat 580390405461,
  Int.ofNat 12107738362975, Int.ofNat 1929227626097, Int.ofNat 7581738402127,
  Int.ofNat 64024619489368, Int.ofNat 158896417772587, Int.ofNat 268471593194905,
  Int.ofNat 364505822372093, Int.ofNat 423699896850141, Int.ofNat 434980045683729,
  Int.ofNat 401449904933998, Int.ofNat 336762660357011, Int.ofNat 258630591420335,
  Int.ofNat 182737766106226, Int.ofNat 119179277644017, Int.ofNat 71891496485973,
  Int.ofNat 40156057194764, Int.ofNat 20777048804830, Int.ofNat 9959514154748,
  Int.ofNat 4414389670407, Int.ofNat 1805196443421, Int.ofNat 678797444633,
  Int.ofNat 232076407366, Int.ofNat 70691723994, Int.ofNat 18791519248, Int.ofNat 4305449061,
  Int.ofNat 869227410, Int.negSucc 105111068, Int.ofNat 8714355, Int.ofNat 872716,
  Int.ofNat 98412 ]
private def mm64R128V3 : List ℤ :=
  mm64R128V3P0 ++ (mm64R128V3P1 ++ mm64R128V3P2)
private def mm64R128V4P0 : List ℤ := [
  Int.negSucc 82134, Int.negSucc 325282, Int.ofNat 603801, Int.negSucc 438118,
  Int.negSucc 153120, Int.ofNat 1313694, Int.ofNat 71924, Int.ofNat 2055866, Int.ofNat 8719598,
  Int.ofNat 11709453, Int.negSucc 39521, Int.negSucc 4875151, Int.ofNat 3093802,
  Int.ofNat 8308707, Int.negSucc 461740, Int.negSucc 21081599, Int.negSucc 12009074,
  Int.negSucc 65613277, Int.negSucc 131959138, Int.negSucc 83538816, Int.ofNat 159269058,
  Int.ofNat 586310727, Int.negSucc 39515336, Int.negSucc 391176839, Int.ofNat 686822322,
  Int.negSucc 539526165, Int.negSucc 442078038, Int.negSucc 323521910, Int.ofNat 625916210,
  Int.ofNat 573607103, Int.ofNat 1617501402, Int.ofNat 1092925390, Int.ofNat 72752879,
  Int.ofNat 71083805, Int.negSucc 338152199, Int.negSucc 1845565748, Int.negSucc 1539205536,
  Int.negSucc 701572141, Int.negSucc 562648835, Int.negSucc 1495937982, Int.negSucc 495646337,
  Int.ofNat 4374053764, Int.ofNat 3321722250, Int.ofNat 3266784053, Int.ofNat 12373567928,
  Int.ofNat 7856952771, Int.ofNat 18886550694, Int.ofNat 4024266086 ]
private def mm64R128V4P1 : List ℤ := [
  Int.negSucc 21418982579, Int.ofNat 24268190655, Int.ofNat 11400138098, Int.ofNat 140696788,
  Int.ofNat 4002282717, Int.ofNat 38681279603, Int.ofNat 66402526791, Int.ofNat 2298791094,
  Int.negSucc 52076147274, Int.negSucc 116717482048, Int.negSucc 100052772977,
  Int.negSucc 94091271475, Int.negSucc 92434756370, Int.ofNat 136206428063,
  Int.ofNat 68805633596, Int.ofNat 33792463796, Int.negSucc 122981725819,
  Int.ofNat 238401006560, Int.negSucc 191008323947, Int.negSucc 78830092838,
  Int.ofNat 102612395591, Int.negSucc 94063050481, Int.negSucc 71790587787,
  Int.negSucc 61067640926, Int.negSucc 438195671691, Int.negSucc 698638539567,
  Int.negSucc 448434185669, Int.ofNat 502512843463, Int.negSucc 447593104826,
  Int.negSucc 574186024764, Int.negSucc 379040990361, Int.negSucc 227346895849,
  Int.negSucc 283992353729, Int.ofNat 1902924432932, Int.ofNat 2380872408021,
  Int.ofNat 127426243158, Int.ofNat 1314901651902, Int.ofNat 856327292275,
  Int.negSucc 3174655872290, Int.ofNat 735237877512, Int.ofNat 1247660997552,
  Int.negSucc 1994310684226, Int.negSucc 1226568897858, Int.negSucc 1098091574578,
  Int.negSucc 5944151989514, Int.negSucc 1064734058767, Int.negSucc 2372556454669,
  Int.ofNat 170309740441 ]
private def mm64R128V4P2 : List ℤ := [
  Int.negSucc 235779199048, Int.ofNat 2692695661529, Int.ofNat 15411312032261,
  Int.ofNat 4272150093550, Int.negSucc 669664310243, Int.negSucc 14871360392227,
  Int.negSucc 12258292786144, Int.negSucc 3874574356775, Int.negSucc 5533127960213,
  Int.ofNat 18093406072, Int.negSucc 5490311997612, Int.negSucc 4104189884763,
  Int.negSucc 13311773367872, Int.ofNat 18403075556102, Int.negSucc 13647878667090,
  Int.negSucc 18099688461253, Int.ofNat 8303954740121, Int.negSucc 2636817941807,
  Int.negSucc 28230931026871, Int.negSucc 7764099478748, Int.ofNat 5522645036954,
  Int.negSucc 3836067787469, Int.ofNat 21629236908077, Int.ofNat 53485416610854,
  Int.ofNat 245245017007331, Int.ofNat 441476327249948, Int.ofNat 546766392948346,
  Int.ofNat 495822455719785, Int.ofNat 365460855550981, Int.ofNat 226563783455830,
  Int.ofNat 92760845538057, Int.ofNat 22674580237646, Int.ofNat 3087092711361 ]
private def mm64R128V4 : List ℤ :=
  mm64R128V4P0 ++ (mm64R128V4P1 ++ mm64R128V4P2)
private def mm64Anc0 : List DickeSol.RampKick128kAnchor := [
  ⟨3, mm64SegsR3, mm64RowR3⟩, ⟨4, mm64SegsR4, mm64RowR4⟩, ⟨5, mm64SegsR5, mm64RowR5⟩,
  ⟨6, mm64SegsR6, mm64RowR6⟩, ⟨7, mm64SegsR7, mm64RowR7⟩, ⟨8, mm64SegsR8, mm64RowR8⟩,
  ⟨9, mm64SegsR9, mm64RowR9⟩, ⟨11, mm64SegsR11, mm64RowR11⟩, ⟨12, mm64SegsR12, mm64RowR12⟩,
  ⟨15, mm64SegsR15, mm64RowR15⟩, ⟨16, mm64SegsR16, mm64RowR16⟩, ⟨19, mm64SegsR19, mm64RowR19⟩ ]
private def mm64Anc1 : List DickeSol.RampKick128kAnchor := [
  ⟨22, mm64SegsR22, mm64RowR22⟩, ⟨32, mm64SegsR32, mm64RowR32⟩ ]
private def mm64k128Anchors : List DickeSol.RampKick128kAnchor :=
  mm64Anc0 ++ (mm64Anc1 ++
    [⟨64, mm64SegsR64, mm64RowR64⟩, ⟨128, mm64SegsR128, mm64RowR128⟩])

private theorem mm64Batch0 : mm64AtF [
    DickeSol.rkm128kCheckTable 64 128 4 true mm64k128VPot mm64k128Anchors,
    mm64ChkCell 8 2 28990925704537 125000000000000 mm64k128VPot mm64k128Anchors,
    mm64ChkCell 16 2 159525410088939 1000000000000000 mm64k128VPot mm64k128Anchors,
    mm64ChkCell 32 2 59353029202209 500000000000000 mm64k128VPot mm64k128Anchors,
    mm64ChkCell 64 2 10235536019277 100000000000000 mm64k128VPot mm64k128Anchors,
    mm64ChkCell 128 4 9384494941081 100000000000000 mm64k128VPot mm64k128Anchors,
    mm64SegBds 64 mm64SegsR64, mm64SegBds 128 mm64SegsR128, mm64ChkAnchors mm64Anc0
  ] = true := by decide +kernel
private theorem mm64Batch1 : mm64ChkAnchors mm64Anc1 = true := by decide +kernel
private theorem mm64Batch2 :
    mm64ChkSeg 64 mm64R64C0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (1, 64, 99910, mm64R64V1) = true := by decide +kernel
private theorem mm64Batch3 :
    mm64ChkSeg 64 mm64R64C1 1 64 99910 mm64R64V1
      (2, 64, 248153, mm64R64V2) = true := by decide +kernel
private theorem mm64Batch4 :
    mm64ChkFin 64 mm64R64C2 2 64 248153 mm64R64V2 mm64RowR64 = true := by
  decide +kernel
private theorem mm64Batch5 :
    mm64ChkSeg 128 mm64R128C0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (2, 128, 211398, mm64R128V1) = true := by decide +kernel
private theorem mm64Batch6 :
    mm64ChkSeg 128 mm64R128C1 2 128 211398 mm64R128V1
      (3, 128, 437901, mm64R128V2) = true := by decide +kernel
private theorem mm64Batch7 :
    mm64ChkSeg 128 mm64R128C2 3 128 437901 mm64R128V2
      (4, 128, 704117, mm64R128V3) = true := by decide +kernel
private theorem mm64Batch8 :
    mm64ChkSeg 128 mm64R128C3 4 128 704117 mm64R128V3
      (4, 128, 973441, mm64R128V4) = true := by decide +kernel
private theorem mm64Batch9 :
    mm64ChkFin 128 mm64R128C4 4 128 973441 mm64R128V4
      mm64RowR128 = true := by decide +kernel

private theorem mm64Row64Sound :
    DickeSol.rkm128kEvalRowLo12 64 4 64 mm64SegsR64 = mm64RowR64 := by
  apply mm64CertSplit (mm64_hd (mm64_tl2 (mm64_tl4 mm64Batch0))); unfold mm64SegsR64
  exact mm64TailStep mm64Batch2 (mm64TailStep mm64Batch3 (mm64TailEnd mm64Batch4))
private theorem mm64Row128Sound :
    DickeSol.rkm128kEvalRowLo12 64 4 128 mm64SegsR128 = mm64RowR128 := by
  apply mm64CertSplit (mm64_hd (mm64_tl1 (mm64_tl2 (mm64_tl4 mm64Batch0))))
  unfold mm64SegsR128; exact mm64TailStep mm64Batch5
    (mm64TailStep mm64Batch6 (mm64TailStep mm64Batch7
      (mm64TailStep mm64Batch8 (mm64TailEnd mm64Batch9))))
private theorem mm64AncSound :
    DickeSol.RampKick128kAnchorsSound 64 4 mm64k128Anchors :=
  mm64ChkAnchors_append (mm64_hd (mm64_tl8 mm64Batch0))
    (mm64ChkAnchors_append mm64Batch1 ⟨mm64Row64Sound, ⟨mm64Row128Sound, trivial⟩⟩)
private theorem mm64k128Valid :
    DickeSol.RampKick128kTableValid 64 128 4 true mm64k128VPot mm64k128Anchors :=
  DickeSol.rkm128kCheckTable_sound mm64AncSound (mm64_hd mm64Batch0)
private theorem mm64k128CellChecks {m k : ℕ}
    (h : isMidM64K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (midM64K128KrotovCertCellLMax m k)
        mm64k128Anchors = true ∧
      ∃ num den : ℕ, relCostMidM64K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (mm64k128VPot.getD k 0) num den = true := by
  unfold isMidM64K128KrotovCertCell at h
  split_ifs at h with hm64 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm64 hk8; have hm := mm64_hd (mm64_tl1 mm64Batch0)
    exact ⟨mm64_and_l hm, 28990925704537, 125000000000000, rfl, mm64_and_r hm⟩
  · subst hm64 hk16; have hm := mm64_hd (mm64_tl2 mm64Batch0)
    exact ⟨mm64_and_l hm, 159525410088939, 1000000000000000, rfl, mm64_and_r hm⟩
  · subst hm64 hk32; have hm := mm64_hd (mm64_tl1 (mm64_tl2 mm64Batch0))
    exact ⟨mm64_and_l hm, 59353029202209, 500000000000000, rfl, mm64_and_r hm⟩
  · subst hm64 hk64; have hm := mm64_hd (mm64_tl4 mm64Batch0)
    exact ⟨mm64_and_l hm, 10235536019277, 100000000000000, rfl, mm64_and_r hm⟩
  · subst hm64 hk128; have hm := mm64_hd (mm64_tl1 (mm64_tl4 mm64Batch0))
    exact ⟨mm64_and_l hm, 9384494941081, 100000000000000, rfl, mm64_and_r hm⟩

private lemma mm64k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma mm64k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma mm64k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl
private lemma mm64k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d
private lemma mm64k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (mm64k128_le_of_add h), rfl⟩

private structure Mm64k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ midM64K128KrotovCertCellLMax m k
  hl1 : 1 ≤ midM64K128KrotovCertCellLMax m k
  hlm : midM64K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 4 true mm64k128VPot mm64k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (midM64K128KrotovCertCellLMax m k)
    mm64k128Anchors = true
  hcost : ∃ num den : ℕ, relCostMidM64K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (mm64k128VPot.getD k 0) num den = true

private lemma mm64k128_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hj : (j + 1) + d1 = 11)
    (h128 : k + dk = 128) (hl2 : 2 + dl2 = midM64K128KrotovCertCellLMax 64 k)
    (hl1 : 1 + dl1 = midM64K128KrotovCertCellLMax 64 k)
    (hlm : midM64K128KrotovCertCellLMax 64 k * 64 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (midM64K128KrotovCertCellLMax 64 k)
      mm64k128Anchors = true)
    (hcost : ∃ num den : ℕ, relCostMidM64K128KrotovCert 64 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 64 k (mm64k128VPot.getD k 0) num den = true) :
    Mm64k128CellProps 64 k :=
  ⟨mm64k128_mem_grid 6 4 rfl, hk ▸ mm64k128_mem_grid j d1 hj, mm64k128_le_of_add h128,
    @mm64k128_le_of_add 2 64 62 rfl, mm64k128_le_of_add hl2, mm64k128_le_of_add hl1,
    mm64k128_le_of_add hlm, mm64k128Valid, hlmax, hcost⟩

private theorem mm64k128_all_props {m k : ℕ} (h : isMidM64K128KrotovCertCell m k = true) :
    Mm64k128CellProps m k := by
  rcases mm64k128CellChecks h with ⟨hlmax, hcost⟩; unfold isMidM64K128KrotovCertCell at h
  split_ifs at h with hm64 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm64 hk8; exact mm64k128_mk 3 7 120 0 1 65408 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm64 hk16; exact mm64k128_mk 4 6 112 0 1 65408 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm64 hk32; exact mm64k128_mk 5 5 96 0 1 65408 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm64 hk64; exact mm64k128_mk 6 4 64 0 1 65408 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm64 hk128; exact mm64k128_mk 7 3 0 2 3 65280 rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def midM64K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ midM64K128KrotovCertQubits n m k)) Var
      (midM64K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isMidM64K128KrotovCertCell m k = true then
    let p := mm64k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG mm64k128VPot mm64k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the `5` `m = 64, 8 ≤ k ≤ 128` cells. -/
noncomputable def findAllJohnsonRampKick128kMidM64K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ midM64K128KrotovCertQubits n m k)) Var
      (midM64K128KrotovCertQubits n m k) ((n + 1) * m) :=
  midM64K128KrotovCertCircuitImpl res n m k

private lemma mm64k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isMidM64K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kMidM64K128KrotovCertCircuit res n m k =
      let p := mm64k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG mm64k128VPot mm64k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kMidM64K128KrotovCertCircuit midM64K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-`1` recovery of `S` across the `5` `m = 64, 8 ≤ k ≤ 128` cells. -/
theorem midM64K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isMidM64K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kMidM64K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [mm64k128_targetSets_eq]
  have hp := mm64k128_all_props hcell
  rw [mm64k128_circuit_eq res n hcell, ← mm64k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG mm64k128VPot mm64k128Anchors hp.hk128
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across `m = 64, 8 ≤ k ≤ 128`. -/
theorem midM64K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isMidM64K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kMidM64K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostMidM64K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := mm64k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG mm64k128VPot
    mm64k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [mm64k128_circuit_eq res n hcell, ← mm64k128_oracle_eq]
    exact hq S (by rwa [mm64k128_targetSets_eq])
  · rw [← mm64k128_targetSets_eq, ← mm64k128_vanilla_eq]; exact hsum

end

end QuantumComputation.Specs.GroverFindAll.Rk128kMidM64K128KrCert
