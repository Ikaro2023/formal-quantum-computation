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
# Krotov `m = 2` `degP ≤ 64` `k ≤ 128` Certificate (`Rk128kLowM2K128KrCert`)

QHL-verified module packaging all `5` `m = 2, 8 ≤ k ≤ 128` cells
(`(2, 8), (2, 16), (2, 32), (2, 64), (2, 128)`) over `27` anchors (`632` segments,
`436,852` F1272 / `449,219` Horner coord-ops at `lTableMax = 124`, `useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM2K128KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported (m, k) cells (m = 2, k ∈ {8, 16, 32, 64, 128}, 5 cells). -/
def isLowM2K128KrotovCertCell (m k : ℕ) : Bool :=
  if m == 2 then
    if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor L_max(2, k) across k ∈ {8..128}. -/
def lowM2K128KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 2 then
    if k == 8 then 7
    else if k == 16 then 15
    else if k == 32 then 31
    else if k == 64 then 62
    else if k == 128 then 124
    else 1
  else 1

/-- Total register qubit budget (lowM2K128KrotovCertCellLMax m k * m) * (n + 1) + k * n. -/
abbrev lowM2K128KrotovCertQubits (n m k : ℕ) : ℕ :=
  (lowM2K128KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile c(2, k): ℚ≥0 across k ∈ {8..128}. -/
def relCostLowM2K128KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 2 then
    if k == 8 then NNRat.divNat 29359515018607 50000000000000
    else if k == 16 then NNRat.divNat 138280842621027 250000000000000
    else if k == 32 then NNRat.divNat 524680560022403 1000000000000000
    else if k == 64 then NNRat.divNat 506001440881489 1000000000000000
    else if k == 128 then NNRat.divNat 98552131503687 200000000000000
    else 1
  else 1

/-- Cost profile metadata (n0 = 80000, constructive threshold). -/
def lowM2K128KrotovCertProfile : FindAllCostProfile :=
  ⟨isLowM2K128KrotovCertCell, relCostLowM2K128KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kLowM2K128KrCert` cell lies on groverGrid × groverGrid. -/
theorem isLowM2K128KrotovCertCell_isGridCell {m k : ℕ}
    (h : isLowM2K128KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isLowM2K128KrotovCertCell at h
  split_ifs at h with hm2 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm2 hk8; rfl
  · subst hm2 hk16; rfl
  · subst hm2 hk32; rfl
  · subst hm2 hk64; rfl
  · subst hm2 hk128; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def lm2NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem lm2NatEq_eq {x y : ℕ} (h : lm2NatEq x y = true) : x = y := by
  unfold lm2NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def lm2IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => lm2NatEq m n
  | Int.negSucc m, Int.negSucc n => lm2NatEq m n
  | _, _ => false
private theorem lm2IntEq_eq {a b : ℤ} (h : lm2IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [lm2IntEq] at h; exact congrArg Int.ofNat (lm2NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => dsimp only [lm2IntEq] at h; exact congrArg Int.negSucc (lm2NatEq_eq h)
private def lm2ListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (lm2ListEq eqF xr yr) false
  | _, _ => false
private theorem lm2ListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : lm2ListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [lm2ListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev Lm2St := ℕ × ℕ × ℕ × List ℤ
private def lm2StEq (a b : Lm2St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (lm2NatEq a1 b1)
      (cond (lm2NatEq a2 b2) (cond (lm2NatEq a3 b3) (lm2ListEq lm2IntEq av bv) false) false) false
private theorem lm2StEq_eq {a b : Lm2St} (h : lm2StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [lm2StEq] at h
  cases h1 : lm2NatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : lm2NatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : lm2NatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h
        exact Prod.ext (lm2NatEq_eq h1)
          (Prod.ext (lm2NatEq_eq h2) (Prod.ext (lm2NatEq_eq h3) (lm2ListEq_eq (@lm2IntEq_eq) h)))
private def lm2AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (lm2AtF rest) false
private theorem lm2_hd {b : Bool} {bs : List Bool} (h : lm2AtF (b :: bs) = true) : b = true := by
  unfold lm2AtF at h; cases b with
  | false => cases h
  | true => rfl
private theorem lm2_tl1 {b : Bool} {s : List Bool} (h : lm2AtF (b :: s) = true) :
    lm2AtF s = true := by
  unfold lm2AtF at h; cases b with
  | false => cases h
  | true => exact h
private theorem lm2_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : lm2AtF (b1 :: b2 :: bs) = true) : lm2AtF bs = true := lm2_tl1 (lm2_tl1 h)
private theorem lm2_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : lm2AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : lm2AtF bs = true := lm2_tl2 (lm2_tl2 h)
private theorem lm2_tl8 {b1 b2 b3 b4 b5 b6 b7 b8 : Bool} {bs : List Bool}
    (h : lm2AtF (b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bs) = true) :
    lm2AtF bs = true := lm2_tl4 (lm2_tl4 h)
private theorem lm2_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem lm2_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev lm2M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def lm2ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  lm2ListEq lm2NatEq (DickeSol.rkm128kEvalRowLo12 2 124 r s) ro
private def lm2ChkAnchors (xs : List DickeSol.RampKick128kAnchor) : Bool :=
  match xs with
  | [] => true
  | a :: rest =>
    match a with
    | ⟨rAct, segs, row⟩ => cond (lm2ChkRow rAct segs row) (lm2ChkAnchors rest) false
private theorem lm2ChkAnchors_append {xs rest : List DickeSol.RampKick128kAnchor}
    (hxs : lm2ChkAnchors xs = true) (hrest : DickeSol.RampKick128kAnchorsSound 2 124 rest) :
    DickeSol.RampKick128kAnchorsSound 2 124 (xs ++ rest) := by
  induction xs with
  | nil => exact hrest
  | cons a tl ih =>
    rcases a with ⟨rAct, segs, row⟩; rw [List.cons_append]
    dsimp only [lm2ChkAnchors, DickeSol.RampKick128kAnchorsSound] at hxs ⊢
    cases ha : lm2ChkRow rAct segs row with
    | false => rw [ha] at hxs; cases hxs
    | true =>
      rw [ha] at hxs; dsimp only [cond] at hxs; exact ⟨lm2ListEq_eq (@lm2NatEq_eq) ha, ih hxs⟩
private def lm2ChkSeg (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (st1 : Lm2St) : Bool := lm2StEq (DickeSol.rkm128kRunSegs 2 124 r s l0 d0 p0 v0) st1
private def lm2ChkFin (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Bool :=
  lm2ListEq lm2NatEq (DickeSol.rkm128kFinalizeState
    (DickeSol.rkm128kRunSegs 2 124 r s l0 d0 p0 v0)) ro
private def lm2SegBds (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def lm2TailOk (r : ℕ) (rest : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Prop :=
  ∃ st, DickeSol.rkm128kRunSegs 2 124 r rest l0 d0 p0 v0 = st ∧
    DickeSol.rkm128kFinalizeState st = ro
private theorem lm2TailEnd {r : ℕ} {cLast : List DickeSol.Rkm128kSeg} {l0 d0 p0 : ℕ} {v0 : List ℤ}
    {ro : List ℕ} (h : lm2ChkFin r cLast l0 d0 p0 v0 ro = true) :
    lm2TailOk r cLast l0 d0 p0 v0 ro := ⟨_, rfl, lm2ListEq_eq (@lm2NatEq_eq) h⟩
private theorem lm2TailStep {r : ℕ} {cCur rest : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {ro : List ℕ}
    (h1 : lm2ChkSeg r cCur l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : lm2TailOk r rest l1 d1 p1 v1 ro) : lm2TailOk r (cCur ++ rest) l0 d0 p0 v0 ro := by
  rcases h2 with ⟨st, hr, hf⟩; refine ⟨st, ?_, hf⟩
  unfold lm2ChkSeg at h1; rw [DickeSol.rkm128kRunSegs_append, lm2StEq_eq h1]; exact hr
private theorem lm2CertSplit {r : ℕ} {segs : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (hb : lm2SegBds r segs = true) (ht : lm2TailOk r segs 1 0 1 [Int.ofNat DickeSol.wdScale] ro) :
    DickeSol.rkm128kEvalRowLo12 2 124 r segs = ro := by
  rcases ht with ⟨st, hr, hf⟩; exact DickeSol.rkm128kCertRow_of_runSegs hb hr hf
private def lm2ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) : Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 2 k (v.getD k 0) n d)

private def lm2k128VPotP0 : List ℕ := [
  0, 454456878931536, 632073517648122, 835610706954352, 983656543543221, 1111887350020629,
  1225463756109172, 1329432986317661, 1425535248862540, 1516436893430245, 1604366777556465,
  1686232563698665, 1766480930330124, 1838525096266200, 1910485056911830, 1980396995955312,
  2047064510798553, 2117325054357626, 2180010026400043, 2243713145246587, 2345332792659918,
  2444503413983592, 2427423646780192, 2522184456604808, 2614950078561479, 2577059777955187,
  2666186104638202, 2678933491570692, 2764817768946080, 2849208292766159, 2932180387434225,
  3013803252432869, 2896825305312995, 2975936093530339, 3020075033969629, 3096892266933555,
  3172635080088811, 3247347330759109, 3185537247688864, 3258308588696193, 3330164530483945,
  3401138770882838, 3471262989715291, 3540567014030168, 3609078966339799, 3676825397948686,
  3743831409166401, 3810120757947910 ]
private def lm2k128VPotP1 : List ℕ := [
  3875715958294460, 3913745212272534, 3978015120442407, 4014942748912658, 4077964578892465,
  4140389032072862, 4202232780043976, 4263511733098200, 4324241088027644, 4384435372131205,
  4444108483792268, 4503273729948109, 4561943860737151, 4620131101579587, 4677847182920003,
  4735103367836929, 4103371974955812, 4159740413316325, 4215680188129822, 4271200932512789,
  4326311924104650, 4381022103165519, 4435340089506298, 4489274198341896, 4542832455150124,
  4596022609611444, 4648852148698121, 4701328308975361, 4753458088171663, 4805248256070749,
  4856705364773070, 4907835758370918, 4958645582077584, 5009140790847755, 5059327157523377,
  5109210280536522, 5158795591198359, 5208088360601087, 5257093706157654, 5305816597802231,
  5354261863872701, 5402434196694875, 5450338157886710, 5497978183399500, 5545358588311808,
  5592483571390804, 5639357219434649, 5685983511408643 ]
private def lm2k128VPotP2 : List ℕ := [
  5732366322386979, 5778509427311152, 5824416504575347, 5870091139448435, 5915536827341589,
  5960756976929953, 6005754913136244, 6050533879983685, 6095097043325193, 6139447493455318,
  6183588247611039, 6227522252367132, 6271252385931499, 6314781460345519, 6358112223594173,
  6401247361630433, 6444189500318127, 6486941207297265, 6529504993775563, 6571883316249718,
  6614078578159758, 6656093131479630, 6697929278246997, 6739589272035064, 6781075319369097,
  6822389581090146, 6863534173668368, 6904511170468198, 6945322602967520, 6985970461932853,
  7026456698552482, 7066783225529365, 5804659104080004 ]
private def lm2k128VPot : List ℕ :=
  lm2k128VPotP0 ++ (lm2k128VPotP1 ++ lm2k128VPotP2)
private def lm2SegsR3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 14585658, 1, 11, []⟩, ⟨1, 20315927, 1, 12, []⟩, ⟨1, 20316866, 1, 12, []⟩,
  ⟨1, 20315483, 1, 12, []⟩, ⟨1, 20315483, 1, 12, []⟩, ⟨1, 20315482, 1, 12, []⟩,
  ⟨1, 20312482, 1, 12, []⟩, lm2M 1 20309482 1 12 3 [7], ⟨1, 10267977, 1, 10, []⟩,
  ⟨2, 1746603, 1, 8, []⟩, ⟨2, 7443743, 1, 11, []⟩, ⟨2, 7620383, 1, 11, []⟩,
  ⟨2, 7642733, 1, 11, []⟩, ⟨2, 7642733, 1, 11, []⟩, ⟨2, 7642733, 1, 11, []⟩,
  ⟨2, 7642733, 1, 11, []⟩, ⟨2, 7646733, 1, 11, []⟩, ⟨2, 7651033, 1, 11, []⟩,
  ⟨2, 15337211, 1, 12, []⟩, ⟨2, 15340811, 1, 12, []⟩, ⟨2, 15341467, 1, 12, []⟩,
  ⟨2, 15341617, 1, 12, []⟩, ⟨2, 15341617, 1, 12, []⟩, lm2M 2 21333367 1 13 1 [1],
  lm2M 2 14444691 1 12 1 [1], lm2M 2 13623396 1 12 1 [1], lm2M 2 15564803 1 12 1 [1],
  ⟨2, 15431248, 1, 12, []⟩, lm2M 2 15507391 1 12 4 [12], lm2M 2 14747337 1 12 2 [3],
  lm2M 2 13361679 1 12 2 [2], lm2M 2 6910697 1 10 4 [12] ]
private def lm2RowR3 : List ℕ := [
  2441677, 281524580944, 718472949571 ]
private def lm2SegsR4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 128486614, 1, 22, []⟩, ⟨2, 130314157, 1, 26, []⟩, lm2M 3 21107910 1 15 1 [1],
  lm2M 3 6645397 1 11 1 [1], ⟨3, 6764143, 1, 11, []⟩, lm2M 3 7436244 1 12 1 [1],
  ⟨3, 13535654, 1, 13, []⟩, lm2M 3 7524685 1 12 2 [2], ⟨3, 6605301, 1, 11, []⟩,
  lm2M 3 6949171 1 11 2 [3], ⟨3, 17181522, 1, 14, []⟩, lm2M 3 10688993 1 13 2 [2],
  lm2M 3 14822276 1 14 1 [1], lm2M 3 13014471 1 13 3 [4], lm2M 3 5393821 1 11 3 [6],
  lm2M 3 4970364 1 11 3 [7], lm2M 3 2706793 1 9 2 [2] ]
private def lm2RowR4 : List ℕ := [
  1395913, 169444, 348768197260, 651230236768 ]
private def lm2SegsR5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 32158994, 1, 15, []⟩, ⟨1, 26699147, 1, 14, []⟩, ⟨1, 25379762, 1, 14, []⟩,
  ⟨1, 27322005, 1, 14, []⟩, ⟨2, 2874658, 1, 9, []⟩, ⟨2, 13288277, 1, 13, []⟩,
  ⟨2, 12482071, 1, 13, []⟩, ⟨2, 13863864, 1, 13, []⟩, ⟨2, 13527280, 1, 13, []⟩,
  ⟨2, 13487025, 1, 13, []⟩, ⟨2, 12640786, 1, 13, []⟩, ⟨3, 16224759, 1, 15, []⟩,
  ⟨3, 13691110, 1, 14, []⟩, ⟨3, 13435438, 1, 14, []⟩, ⟨3, 12132466, 1, 14, []⟩,
  lm2M 3 13459731 1 14 1 [1], ⟨3, 12565759, 1, 14, []⟩, lm2M 4 8940701 1 13 2 [2],
  lm2M 4 5582054 1 12 2 [2], lm2M 4 8834367 1 13 2 [2], lm2M 4 8392288 1 13 1 [1],
  ⟨4, 7454529, 1, 13, []⟩, ⟨4, 8553136, 1, 13, []⟩, lm2M 4 8393345 1 13 3 [7],
  lm2M 4 6908451 1 12 2 [2], ⟨4, 5586091, 1, 12, []⟩, lm2M 4 5479481 1 12 3 [4],
  lm2M 4 10065363 1 14 3 [4], ⟨4, 4520778, 1, 11, []⟩, lm2M 4 5890894 1 12 3 [4],
  lm2M 4 5141097 1 11 4 [8], ⟨4, 1286608, 1, 9, []⟩ ]
private def lm2RowR5 : List ℕ := [
  116083, 2495853, 62737, 412255926536, 587741202796 ]
private def lm2SegsR6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 24462223, 1, 14, []⟩, ⟨1, 23780086, 1, 14, []⟩, ⟨1, 25569642, 1, 14, []⟩,
  ⟨1, 26779168, 1, 14, []⟩, ⟨2, 22215928, 1, 15, []⟩, ⟨2, 20779373, 1, 15, []⟩,
  ⟨2, 22340006, 1, 15, []⟩, ⟨3, 15857284, 1, 15, []⟩, ⟨3, 12081715, 1, 14, []⟩,
  ⟨3, 10525456, 1, 14, []⟩, ⟨3, 12001816, 1, 14, []⟩, ⟨3, 11151583, 1, 14, []⟩,
  lm2M 4 11728375 1 15 1 [1], ⟨4, 9741337, 1, 14, []⟩, lm2M 4 9253111 1 14 2 [3],
  lm2M 4 11828557 1 15 2 [2], lm2M 4 9237335 1 14 2 [2], lm2M 4 11140865 1 14 3 [4],
  lm2M 5 5813479 1 13 3 [4], lm2M 5 7476718 1 13 3 [4], ⟨5, 6078722, 1, 13, []⟩,
  lm2M 5 4300972 1 12 1 [1], lm2M 5 4274568 1 12 3 [5], lm2M 5 4877206 1 12 4 [8],
  lm2M 5 9156679 1 14 4 [10], lm2M 5 6371402 1 13 1 [1], lm2M 5 3393221 1 11 2 [3],
  lm2M 5 3768941 1 11 4 [8], lm2M 5 6674777 1 13 3 [7], lm2M 5 4359623 1 12 4 [15],
  lm2M 5 4905303 1 12 4 [8], lm2M 5 213374 1 7 3 [4] ]
private def lm2RowR6 : List ℕ := [
  39105, 131154, 51776, 282269652, 438163865264, 561553640998 ]
private def lm2SegsR7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 45822585, 1, 17, []⟩, ⟨1, 45822585, 1, 17, []⟩, ⟨2, 29435474, 1, 17, []⟩,
  ⟨2, 29435474, 1, 17, []⟩, ⟨3, 48626944, 1, 23, []⟩, lm2M 4 41905147 1 23 2 [3],
  lm2M 5 26312976 1 20 3 [5], lm2M 5 27985465 1 21 4 [10], lm2M 6 13742427 1 17 3 [7],
  lm2M 6 14385564 1 17 5 [27], lm2M 6 7131859 1 14 4 [12], lm2M 6 7253440 1 14 5 [28],
  lm2M 6 2578340 1 11 4 [13], lm2M 6 4386316 1 12 4 [9], lm2M 6 2962116 1 11 4 [11],
  ⟨6, 2909840, 1, 11, []⟩ ]
private def lm2RowR7 : List ℕ := [
  2149845, 111477, 596213, 3976629, 1331327199, 444716869380, 553944910363 ]
private def lm2SegsR8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 44112828, 1, 17, []⟩, ⟨1, 42024564, 1, 17, []⟩, ⟨2, 19492052, 1, 16, []⟩,
  ⟨2, 16278819, 1, 15, []⟩, ⟨2, 16145144, 1, 15, []⟩, ⟨3, 10884078, 1, 14, []⟩,
  ⟨3, 14402597, 1, 15, []⟩, ⟨3, 14615540, 1, 16, []⟩, ⟨4, 11724755, 1, 15, []⟩,
  ⟨4, 12057523, 1, 16, []⟩, lm2M 4 12112515 1 16 1 [1], lm2M 5 10541275 1 16 2 [3],
  lm2M 5 11346718 1 16 2 [2], lm2M 5 10412201 1 16 3 [7], ⟨6, 5945631, 1, 14, []⟩,
  ⟨6, 5826438, 1, 14, []⟩, lm2M 6 7134882 1 14 4 [8], lm2M 6 5576372 1 14 4 [9],
  lm2M 6 5821281 1 14 4 [11], ⟨6, 5831671, 1, 14, []⟩, lm2M 6 4383826 1 13 5 [16],
  lm2M 6 6349945 1 14 5 [16], lm2M 7 3476254 1 12 2 [3], lm2M 7 3204326 1 12 4 [12],
  lm2M 7 3611246 1 12 5 [19], lm2M 7 4383862 1 13 5 [19], lm2M 7 8296475 1 16 6 [55],
  lm2M 7 8728391 1 16 6 [60], lm2M 7 8030792 1 15 6 [60], lm2M 7 6073138 1 14 5 [18],
  lm2M 7 20906 1 6 6 [34], lm2M 7 595403 1 9 5 [16] ]
private def lm2RowR8 : List ℕ := [
  134945, 193264, 28740, 424, 2253854, 2505738066, 446746500099, 550745115446 ]
private def lm2SegsR9 : List DickeSol.Rkm128kSeg := [
  ⟨1, 40775368, 1, 17, []⟩, ⟨1, 40775368, 1, 17, []⟩, ⟨2, 23845282, 1, 17, []⟩,
  ⟨2, 23845282, 1, 17, []⟩, ⟨3, 40776605, 1, 23, []⟩, lm2M 4 39529990 1 24 2 [3],
  lm2M 5 22396755 1 21 3 [6], lm2M 6 21155321 1 21 4 [9], lm2M 7 20140352 1 21 5 [16],
  lm2M 7 15779498 1 20 5 [29], lm2M 7 4242899 1 13 6 [60], lm2M 8 10357350 1 18 6 [56],
  lm2M 8 3416862 1 13 6 [33], lm2M 8 8520373 1 16 7 [119], lm2M 8 10641790 1 18 7 [77],
  ⟨8, 8294132, 1, 16, []⟩ ]
private def lm2RowR9 : List ℕ := [
  129156, 7179655, 31081242, 10941271, 13542566, 1317039, 4114244964, 454347493513, 541474070500
  ]
private def lm2SegsR10 : List DickeSol.Rkm128kSeg := [
  ⟨1, 36327635, 1, 17, []⟩, ⟨1, 36327635, 1, 17, []⟩, ⟨2, 21102985, 1, 17, []⟩,
  ⟨2, 21102985, 1, 17, []⟩, ⟨3, 36682414, 1, 22, []⟩, ⟨4, 38084377, 1, 24, []⟩,
  lm2M 6 23150767 1 22 3 [7], lm2M 6 19038717 1 21 4 [10], lm2M 8 31169013 1 27 6 [55],
  lm2M 8 14492149 1 20 7 [125], lm2M 8 5230748 1 15 7 [126], lm2M 9 7703007 1 17 4 [14],
  lm2M 9 3024236 1 13 4 [10], lm2M 9 6748126 1 16 8 [247], lm2M 9 6535448 1 16 8 [241],
  ⟨9, 10923385, 1, 19, []⟩ ]
private def lm2RowR10 : List ℕ := [
  26300912, 77537430, 96093129, 14390516, 289061393, 758127863, 101659648, 6352867751,
  450575930410, 541705465724 ]
private def lm2SegsR11 : List DickeSol.Rkm128kSeg := [
  ⟨1, 31063361, 1, 16, []⟩, ⟨1, 31063361, 1, 16, []⟩, ⟨2, 21962979, 1, 17, []⟩,
  ⟨2, 21962979, 1, 17, []⟩, ⟨3, 34437736, 1, 22, []⟩, ⟨4, 30997992, 1, 23, []⟩,
  lm2M 5 16757038 1 19 2 [3], lm2M 6 14503512 1 19 3 [6], lm2M 7 14411310 1 20 4 [10],
  lm2M 7 14863104 1 20 5 [16], lm2M 9 27253780 1 28 7 [110], lm2M 9 21969371 1 25 9 [386],
  lm2M 10 3004880 1 13 9 [273], lm2M 10 10503354 1 19 4 [10], lm2M 10 6733512 1 17 6 [52],
  ⟨10, 7256476, 1, 17, []⟩ ]
private def lm2RowR11 : List ℕ := [
  527431, 177042, 605616, 7605387, 11473560, 41304903, 1424726008, 102981724, 11034483312,
  454818344566, 532556874195 ]
private def lm2SegsR12 : List DickeSol.Rkm128kSeg := [
  ⟨1, 30394605, 1, 16, []⟩, ⟨1, 30394605, 1, 16, []⟩, ⟨2, 19714052, 1, 17, []⟩,
  ⟨2, 19714052, 1, 17, []⟩, ⟨3, 30809613, 1, 22, []⟩, ⟨4, 28088858, 1, 23, []⟩,
  ⟨5, 17210853, 1, 20, []⟩, lm2M 6 15430011 1 20 13 [4102], lm2M 7 13221850 1 20 4 [10],
  lm2M 8 13755060 1 21 5 [25], lm2M 9 24696900 1 27 7 [111], lm2M 10 20185628 1 26 10 [591],
  lm2M 10 91765 1 7 10 [563], lm2M 10 9267315 1 19 9 [510], lm2M 11 13191398 1 22 7 [94],
  ⟨11, 10665196, 1, 20, []⟩ ]
private def lm2RowR12 : List ℕ := [
  322135, 11294054, 51907216, 422727, 11845209, 46408620, 1780040, 8306997376, 6429777407,
  24315942124, 509609842181, 451213458981 ]
private def lm2SegsR13 : List DickeSol.Rkm128kSeg := [
  ⟨1, 30094764, 1, 17, []⟩, ⟨1, 30094764, 1, 17, []⟩, ⟨2, 18651724, 1, 17, []⟩,
  ⟨2, 18651724, 1, 17, []⟩, ⟨3, 28377861, 1, 21, []⟩, ⟨4, 25647289, 1, 22, []⟩,
  ⟨5, 16956066, 1, 20, []⟩, lm2M 6 16131416 1 21 3 [5], lm2M 7 13249531 1 20 14 [8204],
  lm2M 8 12665704 1 21 5 [16], lm2M 9 21764587 1 26 7 [110], lm2M 10 14288710 1 23 11 [1170],
  lm2M 10 2000 1 6 11 [1042], lm2M 11 12326905 1 22 9 [287], lm2M 11 15017040 1 24 10 [570],
  ⟨12, 17797459, 1, 26, []⟩ ]
private def lm2RowR13 : List ℕ := [
  9168812, 161828, 24442246, 9273474, 87261134, 3511912, 16830281, 226855144, 3891341457,
  8935775221, 46360122831, 541622790839, 398807015336 ]
private def lm2SegsR14 : List DickeSol.Rkm128kSeg := [
  ⟨1, 29401654, 1, 17, []⟩, ⟨1, 29401654, 1, 17, []⟩, ⟨2, 17508724, 1, 17, []⟩,
  ⟨2, 17508724, 1, 17, []⟩, ⟨3, 26377665, 1, 21, []⟩, ⟨4, 23656280, 1, 22, []⟩,
  ⟨5, 16611921, 1, 21, []⟩, lm2M 6 16879822 1 22 3 [6], lm2M 7 12051745 1 20 15 [16397],
  lm2M 8 11872031 1 21 15 [16405], lm2M 9 21211974 1 27 7 [104],
  lm2M 11 21403394 1 28 12 [2484], lm2M 11 2000 1 6 12 [2066], lm2M 12 12652720 1 23 10 [557],
  lm2M 12 13653908 1 24 11 [1037], ⟨13, 17246266, 1, 27, []⟩ ]
private def lm2RowR14 : List ℕ := [
  1529434, 5853273, 6196894, 125937164, 18943734, 64507589, 19569381, 436352155, 1026484543,
  5123470553, 9266242846, 37122224680, 527367029764, 419414104995 ]
private def lm2SegsR15 : List DickeSol.Rkm128kSeg := [
  ⟨1, 28772797, 1, 17, []⟩, ⟨1, 28772797, 1, 17, []⟩, ⟨2, 16700819, 1, 17, []⟩,
  ⟨2, 16700819, 1, 17, []⟩, ⟨3, 24817115, 1, 21, []⟩, ⟨4, 22079156, 1, 22, []⟩,
  ⟨5, 16164421, 1, 21, []⟩, lm2M 6 17329171 1 22 3 [5], lm2M 7 11260047 1 20 4 [15],
  lm2M 8 11351964 1 21 16 [32799], lm2M 10 18378388 1 26 7 [112],
  lm2M 11 19523583 1 28 13 [4517], lm2M 11 2000 1 6 13 [4114], lm2M 13 19844014 1 30 11 [1537],
  lm2M 13 14084794 1 25 12 [2217], ⟨14, 15876045, 1, 27, []⟩ ]
private def lm2RowR15 : List ℕ := [
  455781, 17268554, 169997, 26813271, 834186, 361566, 355067084, 18595231, 300897730,
  2240823264, 6694153133, 8158170326, 36877309433, 520974117602, 424334897233 ]
private def lm2SegsR16 : List DickeSol.Rkm128kSeg := [
  ⟨1, 26129902, 1, 16, []⟩, ⟨1, 27011642, 1, 17, []⟩, ⟨2, 16629576, 1, 17, []⟩,
  ⟨2, 15449158, 1, 16, []⟩, ⟨3, 22726871, 1, 21, []⟩, ⟨4, 10092149, 1, 17, []⟩,
  ⟨4, 10270563, 1, 17, []⟩, ⟨5, 8131444, 1, 17, []⟩, ⟨5, 7782516, 1, 16, []⟩,
  ⟨6, 9056941, 1, 18, []⟩, ⟨7, 7656009, 1, 18, []⟩, ⟨7, 6471611, 1, 17, []⟩,
  lm2M 8 5871095 1 17 16 [32783], ⟨8, 5202461, 1, 16, []⟩, lm2M 9 4930576 1 16 17 [65567],
  lm2M 9 4428339 1 16 17 [65536], lm2M 10 4377704 1 16 17 [65536],
  lm2M 10 4396703 1 16 17 [65536], lm2M 10 4407367 1 16 17 [65641], ⟨11, 6818644, 1, 19, []⟩,
  lm2M 11 6709029 1 19 5 [17], lm2M 12 6358263 1 19 8 [129], lm2M 12 6206221 1 19 14 [9011],
  lm2M 12 10 1 6 14 [8210], ⟨13, 5123591, 1, 18, []⟩, lm2M 13 5047897 1 18 4 [13],
  lm2M 14 4719499 1 18 1 [1], lm2M 14 4738007 1 18 12 [3081], lm2M 14 3840057 1 16 9 [256],
  lm2M 14 2504165 1 15 1 [1], lm2M 14 3151163 1 16 6 [33], lm2M 15 2959172 1 15 13 [4353],
  ⟨15, 3718115, 1, 17, []⟩, lm2M 15 3691138 1 17 3 [5], lm2M 15 3700090 1 17 5 [28],
  lm2M 15 3696645 1 17 8 [132] ]
private def lm2RowR16 : List ℕ := [
  3312, 19520, 545310, 8018120, 179140589, 69862441, 1820333, 167462784, 31298429, 1785077172,
  3146638081, 6401225380, 7914764080, 37858443892, 518924865388, 423510815001 ]
private def lm2SegsR17 : List DickeSol.Rkm128kSeg := [
  ⟨1, 25983762, 1, 19, []⟩, ⟨1, 25983762, 1, 19, []⟩, ⟨2, 15057326, 1, 19, []⟩,
  ⟨2, 15057326, 1, 19, []⟩, ⟨3, 22146215, 1, 19, []⟩, ⟨4, 19318483, 1, 19, []⟩,
  ⟨5, 14877900, 1, 19, []⟩, lm2M 6 17307153 1 19 2 [2], lm2M 8 12191269 1 19 16 [32779],
  lm2M 9 9115057 1 19 16 [32799], lm2M 10 16545027 1 21 7 [98],
  lm2M 12 23980563 1 26 15 [17207], lm2M 12 2000 1 19 15 [16402],
  lm2M 14 17296363 1 23 12 [2115], lm2M 15 10115523 1 19 13 [4479], ⟨15, 15587412, 1, 22, []⟩ ]
private def lm2RowR17 : List ℕ := [
  33356, 5875835, 23794825, 3035901, 136526, 3037381, 1559468, 46807674, 235133979, 1468063102,
  1679609196, 8277360132, 4423801687, 965121085, 255208803415, 533636135415, 194017034006 ]
private def lm2SegsR18 : List DickeSol.Rkm128kSeg := [
  ⟨1, 25088387, 1, 16, []⟩, ⟨1, 25088387, 1, 16, []⟩, ⟨2, 14500536, 1, 16, []⟩,
  ⟨2, 14500536, 1, 16, []⟩, ⟨3, 21200140, 1, 21, []⟩, ⟨4, 18359887, 1, 21, []⟩,
  ⟨5, 14295643, 1, 21, []⟩, lm2M 6 17004047 1 23 2 [2], lm2M 8 12688772 1 23 4 [11],
  lm2M 9 8514105 1 20 17 [65567], lm2M 10 15858497 1 26 7 [99],
  lm2M 12 22371712 1 33 16 [33593], lm2M 12 2000 1 6 16 [32786],
  lm2M 15 22183995 1 35 13 [6465], lm2M 16 10784645 1 25 14 [8957], ⟨16, 14861463, 1, 29, []⟩ ]
private def lm2RowR18 : List ℕ := [
  409857, 1953982, 17788799, 1824354, 37049289, 7969970, 97500298, 6255239, 28999357, 160543677,
  18038431, 1588622779, 13340184007, 2544412854, 264829202, 234221103534, 538695679419,
  208955504967 ]
private def lm2SegsR19 : List DickeSol.Rkm128kSeg := [
  ⟨1, 23988590, 1, 16, []⟩, ⟨1, 23988590, 1, 16, []⟩, ⟨2, 14290809, 1, 16, []⟩,
  ⟨2, 14290809, 1, 16, []⟩, ⟨3, 20322752, 1, 21, []⟩, ⟨4, 16986411, 1, 21, []⟩,
  ⟨5, 13360593, 1, 20, []⟩, ⟨6, 16530801, 1, 23, []⟩, lm2M 8 13671765 1 24 16 [32779],
  lm2M 9 8310896 1 20 17 [65567], lm2M 10 15102514 1 26 7 [98],
  lm2M 13 19933116 1 32 17 [66340], lm2M 13 2000 1 6 17 [65554],
  lm2M 15 20402205 1 34 13 [6416], lm2M 16 9710760 1 25 14 [8753], ⟨17, 16322404, 1, 32, []⟩ ]
private def lm2RowR19 : List ℕ := [
  40128, 6587304, 7771657, 27481067, 12762285, 64971977, 635829, 26131621, 10568134, 394476826,
  224698664, 100, 12301035367, 101873225, 7130834534, 47665170343, 401126843485, 426106996542,
  104790323363 ]
private def lm2SegsR22 : List DickeSol.Rkm128kSeg := [
  ⟨1, 22230983, 1, 16, []⟩, ⟨1, 22230983, 1, 16, []⟩, ⟨2, 13281850, 1, 16, []⟩,
  ⟨2, 13281850, 1, 16, []⟩, ⟨3, 18583826, 1, 20, []⟩, ⟨4, 15072321, 1, 21, []⟩,
  ⟨5, 11936398, 1, 20, []⟩, ⟨6, 15224918, 1, 23, []⟩, lm2M 8 14047601 1 25 16 [32779],
  lm2M 9 7558525 1 20 17 [98335], lm2M 11 12631358 1 26 23 [4784228],
  lm2M 13 17306825 1 32 20 [525092], lm2M 14 337046 1 10 20 [524306],
  lm2M 15 16593416 1 33 13 [6624], lm2M 17 7835199 1 24 14 [8896], ⟨19, 25091131, 1, 44, []⟩ ]
private def lm2RowR22 : List ℕ := [
  12828128, 6574258, 285656, 2808386, 2765971, 8525630, 62789281, 103794120, 77858100,
  383798323, 72698900, 152098262, 4464629404, 501299224, 12123885922, 385837518, 18303389086,
  9653431138, 263654555731, 445430612383, 214545741960, 30048991783 ]
private def lm2SegsR25 : List DickeSol.Rkm128kSeg := [
  ⟨1, 15018322, 1, 15, []⟩, ⟨1, 15018322, 1, 15, []⟩, ⟨2, 13520364, 1, 17, []⟩,
  ⟨2, 13520364, 1, 17, []⟩, ⟨3, 20590029, 1, 22, []⟩, ⟨5, 16449605, 1, 23, []⟩,
  ⟨7, 23516196, 1, 31, []⟩, lm2M 10 19371278 1 32 5 [24], lm2M 12 13295962 1 29 24 [10486008],
  lm2M 15 9419281 1 26 25 [25164900], lm2M 18 25206034 1 46 16 [61149],
  lm2M 21 19913665 1 43 20 [844630], lm2M 23 9962558 1 31 22 [3127576],
  lm2M 23 1920235 1 16 22 [3962609], lm2M 24 5019095 1 23 16 [57423], ⟨24, 5091443, 1, 23, []⟩ ]
private def lm2RowR25 : List ℕ := [
  26324, 11288731, 122661, 2978300, 6592295, 23902407, 6076710, 139385682, 1151147, 51571285,
  295208289, 772393619, 572184377, 114976609, 2208521477, 516577719, 984010280, 120441,
  1633501934, 3489744842, 6549715617, 1832839271, 66548413577, 520504476457, 393733802517 ]
private def lm2SegsR27 : List DickeSol.Rkm128kSeg := [
  ⟨1, 14859119, 1, 19, []⟩, ⟨1, 14859119, 1, 19, []⟩, ⟨2, 12765918, 1, 19, []⟩,
  ⟨2, 12765918, 1, 19, []⟩, ⟨3, 19967281, 1, 19, []⟩, ⟨5, 16459910, 1, 19, []⟩,
  ⟨7, 22105466, 1, 24, []⟩, lm2M 10 18354174 1 25 5 [26], lm2M 13 11754977 1 22 22 [2097344],
  lm2M 15 9088230 1 21 28 [234880278], lm2M 19 22318740 1 36 16 [59228],
  lm2M 22 16953838 1 33 20 [845682], lm2M 25 15267590 1 32 24 [10377135],
  lm2M 25 862300 1 19 24 [16346429], lm2M 25 6536788 1 21 20 [685469], ⟨26, 7028324, 1, 22, []⟩
  ]
private def lm2RowR27 : List ℕ := [
  8952, 186467, 1654, 9098, 75066, 72876013, 56698415, 60731858, 203592445, 32140221, 1123539,
  82065116, 37017298, 6728896, 980807771, 548775675, 2182473680, 41639575, 233376358, 1211583,
  3051470206, 7110011213, 2922456283, 4835709101, 45847496157, 499021858254, 432669448025 ]
private def lm2SegsR32 : List DickeSol.Rkm128kSeg := [
  ⟨1, 28741653, 1, 19, []⟩, ⟨2, 20145310, 1, 20, []⟩, ⟨3, 17601152, 1, 22, []⟩,
  ⟨4, 16545576, 1, 23, []⟩, ⟨6, 10805189, 1, 22, []⟩, ⟨7, 9434240, 1, 22, []⟩,
  ⟨8, 4723288, 1, 18, []⟩, ⟨9, 4294726, 1, 18, []⟩, ⟨10, 3975614, 1, 18, []⟩,
  lm2M 10 3998635 1 18 4 [8], lm2M 11 3668003 1 18 5 [16], lm2M 12 3476938 1 18 6 [33],
  ⟨12, 3587648, 1, 18, []⟩, lm2M 13 3245624 1 18 8 [200], lm2M 14 2710863 1 17 7 [82],
  lm2M 15 2781295 1 18 31 [1073741914], lm2M 15 2867740 1 18 30 [536870938],
  lm2M 16 2696776 1 18 33 [4294968528], lm2M 17 2652259 1 18 33 [4831839488],
  lm2M 17 2815488 1 18 31 [1073741832], lm2M 18 2693969 1 18 33 [5368709536],
  lm2M 19 2571125 1 18 33 [4294967304], lm2M 19 2572195 1 18 33 [5368711681],
  lm2M 20 2554453 1 19 31 [1073778817], lm2M 21 1658819 1 16 33 [4294968385],
  lm2M 21 2373842 1 18 17 [117136], lm2M 22 2848780 1 20 14 [8577], ⟨23, 2839422, 1, 20, []⟩,
  lm2M 23 2830422 1 20 19 [278547], lm2M 24 2991116 1 20 20 [555047],
  lm2M 25 2843607 1 20 6 [38], lm2M 25 2437328 1 19 22 [3145850],
  lm2M 26 1918619 1 18 22 [2375681], lm2M 26 2390802 1 19 23 [4718214],
  lm2M 27 3544620 1 22 24 [8422359], lm2M 28 3135814 1 22 25 [16778167],
  lm2M 28 1833044 1 18 25 [16916873], lm2M 29 2884518 1 21 26 [33670405],
  lm2M 29 3178184 1 22 27 [67139335], lm2M 29 1591249 1 17 27 [67143710],
  lm2M 30 2720736 1 21 28 [139460636], lm2M 30 1756100 1 18 28 [140505047],
  lm2M 30 3009332 1 22 29 [268435772], lm2M 30 2007805 1 19 29 [427870564],
  lm2M 31 1452723 1 17 28 [159948741], lm2M 31 2216161 1 20 30 [571625530],
  lm2M 31 1599448 1 18 30 [572103207], lm2M 31 2199255 1 19 27 [106990476] ]
private def lm2RowR32 : List ℕ := [
  88, 659, 5478, 4094, 4136, 69922, 39033, 709986, 5891, 42295, 281487, 10913649, 98034, 38591,
  2840822, 6474328, 91812702, 55215496, 43497576, 60686103, 596274, 65123039, 211274295,
  262845172, 137381014, 859020056, 6693682356, 2801620495, 38242909, 19657142389, 454172120465,
  514828210600 ]
private def lm2SegsR34 : List DickeSol.Rkm128kSeg := [
  ⟨1, 109829203, 1, 29, []⟩ ]
private def lm2RowR34 : List ℕ := [
  161252181006, 833362504781 ]
private def lm2SegsR38 : List DickeSol.Rkm128kSeg := [
  ⟨1, 24337067, 1, 18, []⟩, ⟨2, 17981889, 1, 20, []⟩, ⟨3, 16336743, 1, 22, []⟩,
  ⟨5, 13985099, 1, 24, []⟩, ⟨7, 17474955, 1, 30, []⟩, lm2M 10 15438355 1 33 1 [1],
  lm2M 15 21073589 1 46 29 [268436608], lm2M 21 15256762 1 44 34 [8590055511],
  lm2M 25 10126781 1 38 36 [51541536812], lm2M 27 7893430 1 34 24 [14370883],
  lm2M 32 12362809 1 46 29 [363581270], lm2M 34 8174520 1 37 32 [2462960750],
  lm2M 35 4153659 1 27 34 [17042006197], lm2M 35 936342 1 16 34 [8997558314],
  lm2M 36 7100594 1 35 33 [6894922991], ⟨37, 5689208, 1, 32, []⟩ ]
private def lm2RowR38 : List ℕ := [
  222961, 677, 60629, 284309, 500825, 2794460, 188013, 7742679, 125174, 35332, 27417564,
  2222098, 19740533, 536178, 20942613, 102352715, 18078236, 47619914, 386051542, 315154607,
  120861486, 323698937, 3009269341, 898706868, 312462717, 1408723212, 81131320, 46452579,
  8804436074, 336145, 576746811, 1241545848, 3282034290, 679734042, 4204701942, 64726396085,
  507328179738, 402002424874 ]
private def lm2SegsR49 : List DickeSol.Rkm128kSeg := [
  ⟨1, 82422921, 1, 29, []⟩ ]
private def lm2RowR49 : List ℕ := [
  282892944835, 691581092700 ]
private def lm2SegsR51 : List DickeSol.Rkm128kSeg := [
  ⟨1, 82181390, 1, 29, []⟩ ]
private def lm2RowR51 : List ℕ := [
  262652529367, 716245250480 ]
private def lm2R64C0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 16338685, 1, 18, []⟩, ⟨1, 8926631, 1, 15, []⟩, ⟨2, 15094534, 1, 21, []⟩,
  ⟨4, 9935239, 1, 22, []⟩, ⟨6, 12208150, 1, 28, []⟩, ⟨8, 10831248, 1, 29, []⟩,
  ⟨11, 7357569, 1, 28, []⟩, lm2M 13 6572833 1 28 6 [32], lm2M 15 3170423 1 22 7 [96],
  lm2M 16 3044547 1 22 9 [416], lm2M 17 2874499 1 22 10 [512], lm2M 19 2670154 1 22 12 [3190],
  lm2M 20 2312765 1 21 13 [6408], lm2M 21 2219173 1 21 14 [8993],
  lm2M 22 2182205 1 22 15 [16931], lm2M 24 2062470 1 22 49 [299067162885738],
  lm2M 25 1949886 1 21 45 [17592186256409], lm2M 26 1921645 1 22 19 [344210],
  lm2M 27 1829955 1 21 20 [557733], lm2M 28 1836032 1 22 46 [35184375511753],
  lm2M 30 1726936 1 22 59 [5262094, 4], lm2M 31 1680428 1 22 59 [70368753360448, 4],
  lm2M 32 1631730 1 21 65 [562949962433326, 260], lm2M 33 1627217 1 22 57 [562950020530770, 1] ]
private def lm2R64C1 : List DickeSol.Rkm128kSeg := [
  lm2M 34 1500843 1 21 65 [138545339, 256], lm2M 36 1505323 1 22 65 [285213869, 256],
  lm2M 37 1353304 1 21 65 [18434211, 256], lm2M 38 1399892 1 21 65 [2050085601, 257],
  lm2M 39 1940410 1 24 65 [4503604056756260, 273],
  lm2M 40 1628666 1 23 65 [4503608351785069, 272], lm2M 42 1672931 1 23 65 [17190372866, 256],
  lm2M 43 1635191 1 23 65 [105464729080, 256], lm2M 44 1633972 1 23 65 [148245644042, 256],
  lm2M 45 1640542 1 24 65 [550627971079, 260], lm2M 46 1541923 1 23 65 [1099596041235, 260],
  lm2M 48 1476412 1 23 65 [1202594519136, 260], lm2M 49 1522183 1 23 65 [139594842305, 320],
  lm2M 50 1489124 1 23 65 [22413585522444, 256], lm2M 51 1255767 1 22 61 [4362131860, 16],
  lm2M 52 1414729 1 23 61 [127022797255927, 16], lm2M 53 1431640 1 23 48 [143005472277525],
  lm2M 54 1245513 1 22 49 [281475388022930], lm2M 55 1190713 1 22 63 [567503566764223, 64],
  lm2M 55 1320914 1 23 63 [1698061525516606, 64], lm2M 56 1024055 1 21 51 [1135935434491024],
  lm2M 57 1270004 1 23 42 [2508263984504], lm2M 57 1184014 1 22 37 [70942277731],
  lm2M 58 1171622 1 22 54 [9290901864350780], lm2M 59 1310023 1 23 55 [18054672443446848],
  lm2M 59 922286 1 20 55 [19747228869723147], lm2M 59 1036807 1 21 51 [1196285832077418],
  lm2M 60 1015673 1 21 57 [1133876895777, 1], lm2M 60 709457 1 19 56 [37156895959073092],
  lm2M 61 1034586 1 21 40 [550330490881], lm2M 61 985009 1 21 47 [70507371283973] ]
private def lm2R64C2 : List DickeSol.Rkm128kSeg := [
  lm2M 61 1001040 1 21 59 [353222843975417, 6], lm2M 61 660049 1 18 43 [4406664006145],
  lm2M 62 754710 1 19 55 [18583945595586577], lm2M 62 739097 1 19 55 [18577351919011446],
  lm2M 62 780674 1 19 60 [8925278370414, 8], lm2M 62 1058925 1 22 29 [403990529],
  lm2M 62 839935 1 20 53 [4644474692567071], lm2M 62 841171 1 20 49 [282162982293509],
  lm2M 62 841173 1 20 54 [9009415491708364] ]
private def lm2SegsR64 : List DickeSol.Rkm128kSeg :=
  lm2R64C0 ++ (lm2R64C1 ++ lm2R64C2)
private def lm2RowR64P0 : List ℕ := [
  1, 5, 72, 66, 507, 12, 779, 324, 21, 6449, 11862, 3572, 30, 227, 693, 123048, 171999, 8889,
  51069, 13958, 14591, 42524, 5415, 184342, 1133209, 762748, 1518587, 2894656, 190149, 652493,
  752474, 3234004, 12070976, 6411041, 17736725, 54015615, 20538159, 14636377, 28736, 2352353,
  5051019, 176279791, 162353011, 134378215, 205421733, 23598119, 49025735, 556021589 ]
private def lm2RowR64P1 : List ℕ := [
  1651703, 253629335, 880137691, 143626063, 1053372, 946710448, 1865268599, 20269105, 360262006,
  2333360759, 12584100756, 1244110249, 349500274, 196206892112, 525793462968, 255564265215 ]
private def lm2RowR64 : List ℕ :=
  lm2RowR64P0 ++ lm2RowR64P1
private def lm2R64V1P0 : List ℤ := [
  Int.ofNat 12148722769, Int.negSucc 57640681558, Int.ofNat 512705440026,
  Int.ofNat 688338329323, Int.ofNat 1921501727329, Int.ofNat 102409580663,
  Int.negSucc 3334266947227, Int.ofNat 1195493810067, Int.negSucc 6988092902128,
  Int.negSucc 7247687438479, Int.negSucc 914614123550, Int.ofNat 446936340201,
  Int.negSucc 9196199730101, Int.ofNat 4777353368146, Int.ofNat 8796401073036,
  Int.ofNat 6248639978572, Int.ofNat 914165708596, Int.ofNat 1866440018389,
  Int.ofNat 23802393455363, Int.ofNat 13566405644394, Int.ofNat 4518629166523,
  Int.negSucc 2750970588110, Int.negSucc 11195915333070, Int.negSucc 9000789141638,
  Int.negSucc 7701027443468, Int.negSucc 25439814459112, Int.ofNat 8518328273475,
  Int.ofNat 79911126204789, Int.ofNat 221614206460560, Int.ofNat 364206425225738,
  Int.ofNat 456615621244944, Int.ofNat 474159044626746, Int.ofNat 423869246909312,
  Int.ofNat 333285720585399, Int.ofNat 233585239115525, Int.ofNat 147204080394248,
  Int.ofNat 83917510783951, Int.ofNat 43458938528362, Int.ofNat 20506598538577,
  Int.ofNat 8834694475890, Int.ofNat 3479838527255, Int.ofNat 1254096312019,
  Int.ofNat 413645375122, Int.ofNat 124853231432, Int.ofNat 34444227202, Int.ofNat 8730309234,
  Int.ofNat 1973684034, Int.ofNat 380858416 ]
private def lm2R64V1P1 : List ℤ := [
  Int.ofNat 62515495, Int.negSucc 7843871, Int.ofNat 777986, Int.ofNat 82748, Int.ofNat 11725,
  Int.ofNat 1694, Int.ofNat 198, Int.ofNat 16, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R64V1 : List ℤ :=
  lm2R64V1P0 ++ lm2R64V1P1
private def lm2R64V2P0 : List ℤ := [
  Int.negSucc 1271217350, Int.negSucc 9752431344, Int.negSucc 1380691154,
  Int.negSucc 21070132647, Int.negSucc 24474006255, Int.negSucc 60612995325,
  Int.negSucc 38488324699, Int.negSucc 54398907032, Int.ofNat 22528772322,
  Int.ofNat 83423847854, Int.negSucc 25801663882, Int.negSucc 269058916209,
  Int.negSucc 321327808202, Int.ofNat 55196358129, Int.ofNat 293173400623,
  Int.ofNat 324937943619, Int.ofNat 245910983923, Int.ofNat 274923010513,
  Int.ofNat 858801370575, Int.ofNat 1022877200238, Int.negSucc 52807235539,
  Int.ofNat 403896030025, Int.negSucc 606225213028, Int.ofNat 216875581387,
  Int.ofNat 211958708218, Int.ofNat 324992957360, Int.negSucc 201625554366,
  Int.ofNat 2857189266769, Int.ofNat 2861428931129, Int.ofNat 7247021335929,
  Int.ofNat 440544292602, Int.negSucc 5325097497293, Int.negSucc 4432467357617,
  Int.negSucc 7396733525480, Int.negSucc 7478828589218, Int.negSucc 11800332036475,
  Int.negSucc 11517866654167, Int.ofNat 2384280894242, Int.ofNat 6999803126977,
  Int.negSucc 13667606847463, Int.ofNat 4248789760207, Int.ofNat 5816182537028,
  Int.ofNat 9362555951381, Int.ofNat 18959924787611, Int.ofNat 13921277787839,
  Int.ofNat 6443198760516, Int.negSucc 16053613705530, Int.ofNat 26910585880856 ]
private def lm2R64V2P1 : List ℤ := [
  Int.negSucc 2110179283249, Int.ofNat 30801740837491, Int.ofNat 30374001390328,
  Int.ofNat 24091883139124, Int.ofNat 35469744322364, Int.ofNat 14102387245794,
  Int.ofNat 56719056607049, Int.ofNat 67231084906798, Int.ofNat 24831194505500,
  Int.negSucc 50071780334163, Int.ofNat 56287588533617, Int.ofNat 346697130166741,
  Int.ofNat 576310235899061, Int.ofNat 576369024800649, Int.ofNat 396298235407210,
  Int.ofNat 187361303580940, Int.ofNat 53917332914286 ]
private def lm2R64V2 : List ℤ :=
  lm2R64V2P0 ++ lm2R64V2P1
private def lm2R128C0 : List DickeSol.Rkm128kSeg := [
  ⟨1, 12678421, 1, 18, []⟩, ⟨2, 8299787, 1, 19, []⟩, ⟨4, 8159350, 1, 23, []⟩,
  ⟨6, 6818635, 1, 25, []⟩, ⟨8, 5868944, 1, 26, []⟩, ⟨10, 5114027, 1, 27, []⟩,
  ⟨12, 3511436, 1, 25, []⟩, ⟨14, 3187216, 1, 25, []⟩, lm2M 16 2899352 1 26 2 [2],
  ⟨18, 2895749, 1, 27, []⟩, lm2M 21 2591002 1 27 4 [8],
  lm2M 23 2410748 1 27 45 [17592186045440], lm2M 25 2240657 1 27 50 [562949953433816],
  lm2M 27 2174147 1 28 17 [103212], lm2M 30 2006720 1 28 19 [411808],
  lm2M 32 1928070 1 28 22 [3251105], lm2M 35 1779407 1 28 61 [16436929, 16],
  lm2M 37 1711957 1 28 55 [18014398624430841], lm2M 40 1511171 1 27 80 [409100552, 11567104],
  lm2M 42 1470911 1 27 78 [1132213924, 3145856],
  lm2M 44 1430889 1 28 87 [13666281276, 1705050624],
  lm2M 47 1341101 1 27 95 [38875457904, 538887585792],
  lm2M 49 1310600 1 27 99 [177081517494, 8491125178368],
  lm2M 51 1283411 1 28 102 [1378685567556, 40861144453120] ]
private def lm2R128C1 : List DickeSol.Rkm128kSeg := [
  lm2M 54 1169575 1 27 108 [4810434943000, 4165886516658176],
  lm2M 56 1164287 1 27 111 [18142320429648, 27820068557553664],
  lm2M 58 1153504 1 28 115 [220594969654839, 18682211163701248, 6],
  lm2M 61 1137288 1 28 123 [844429040600064, 66688637957308416, 1245],
  lm2M 63 1148475 1 28 127 [2367850638123280, 15535784696217600, 25678],
  lm2M 65 1131031 1 28 128 [27375726426754434, 11461962042966016, 36827],
  lm2M 67 1077549 1 28 129 [1425645736348164, 20374414319157249, 103865],
  lm2M 69 1068556 1 28 128 [11408541292176419, 22369290330046468, 62797],
  lm2M 72 1039455 1 28 129 [4649182385154049, 5361768452849704, 95107],
  lm2M 74 965704 1 28 128 [27039534891141249, 29836347531329682, 34629],
  lm2M 76 983448 1 28 128 [38061458454639065, 49609964645253946, 33341],
  lm2M 78 995859 1 28 124 [36741306861748739, 36099165763147802, 2711],
  lm2M 80 945495 1 28 128 [581091896397446, 67853061573337158, 44127] ]
private def lm2R128C2 : List DickeSol.Rkm128kSeg := [
  lm2M 82 911255 1 28 127 [41746257626011169, 4785074604147208, 29359],
  lm2M 85 897167 1 28 129 [5630633405579269, 63050394783465794, 120075],
  lm2M 87 873444 1 28 124 [34991581241127045, 54034399436800900, 3768],
  lm2M 89 873765 1 28 128 [22527071322473352, 31490013023978500, 59621],
  lm2M 91 851359 1 28 126 [618510502786, 12656642, 10533],
  lm2M 92 829259 1 28 129 [4503601778279951, 9007199273746500, 123364],
  lm2M 94 825255 1 28 129 [22597163581325860, 18014398559954336, 75908],
  lm2M 96 801154 1 27 129 [16640637023129182, 1885810460, 67188],
  lm2M 97 546223 1 23 129 [1196277247772710, 134250625, 90628],
  lm2M 98 444166 1 22 129 [36143180595365891, 5251337537, 98752],
  lm2M 99 446355 1 22 126 [422341353965571, 9429221391, 12808],
  lm2M 100 452240 1 22 129 [18014724939714705, 4503618485682696, 72224],
  lm2M 101 438773 1 22 118 [141287390969874, 35031239816, 40] ]
private def lm2R128C3 : List DickeSol.Rkm128kSeg := [
  lm2M 102 446376 1 22 122 [282368397279252, 69525016640, 520],
  lm2M 102 445197 1 22 127 [2815849313632849, 18014605742179169, 16384],
  lm2M 103 441696 1 22 120 [1125900948603685, 483192209408, 128],
  lm2M 104 435330 1 22 95 [4578367763907355, 274894688772],
  lm2M 104 430039 1 22 127 [45115161651970866, 1967166333312, 16384],
  lm2M 105 431691 1 22 84 [5387322400, 176166912],
  lm2M 106 422817 1 22 127 [1020360771773370, 6614384377856, 16384],
  lm2M 107 368011 1 21 127 [158492968114955, 8796246380548, 16384],
  lm2M 108 429753 1 22 127 [598453484802760, 17868308611232, 16384],
  lm2M 108 361407 1 21 129 [423356406968968, 144703632, 130816],
  lm2M 109 404187 1 22 129 [29414687246401718, 139921997888, 114176],
  lm2M 110 406524 1 22 121 [4793883599307432, 17592190239040, 256],
  lm2M 111 405674 1 22 121 [17611379213872, 22592639598656, 256],
  lm2M 111 406159 1 22 91 [4543201107143713, 26038304772],
  lm2M 112 405838 1 22 106 [27100800184176225, 571866322592896],
  lm2M 112 323011 1 20 104 [57244130491457, 158536374945799] ]
private def lm2R128C4 : List DickeSol.Rkm128kSeg := [
  lm2M 113 372661 1 21 128 [107203465066529, 35184640545280, 33792],
  lm2M 114 385764 1 21 105 [585352524862922, 290993717913116],
  lm2M 114 381548 1 21 128 [185823951606218, 581831703527464, 33792],
  lm2M 115 377030 1 21 104 [3396198162536911, 140738566490368],
  lm2M 116 377933 1 21 128 [1776553430129309, 274915664016, 32768],
  lm2M 116 381704 1 21 128 [3950683141537950, 550829574144, 32768],
  lm2M 117 383174 1 21 128 [23658192257222661, 41236634993168384, 32768],
  lm2M 117 360480 1 21 128 [30966656331957283, 2474186509824, 32768],
  lm2M 118 374919 1 21 128 [502007506928181, 55747730359912593, 32769],
  lm2M 118 328414 1 20 95 [63685913579952400, 279206461446],
  lm2M 119 376816 1 21 128 [2257300324614177, 73272175624240, 32768],
  lm2M 119 381820 1 22 111 [5101739326059043, 18155189685338128],
  lm2M 120 371807 1 21 128 [40567585598136513, 75316554924210, 32772],
  lm2M 120 375738 1 21 106 [38148329600, 633937172955216],
  lm2M 121 373838 1 21 116 [22588504881733642, 4574655566316032, 8],
  lm2M 121 395307 1 22 113 [27303353022777485, 40568165138171970, 1] ]
private def lm2R128C5 : List DickeSol.Rkm128kSeg := [
  lm2M 121 365750 1 21 117 [18295218696392969, 16121243237869688, 17],
  lm2M 123 709908 1 28 106 [6758749586849792, 565157566619656],
  lm2M 123 659421 1 27 100 [11064222025801, 8796697133152],
  lm2M 123 661853 1 27 119 [54064362505900032, 1125934267187721, 72],
  lm2M 124 559194 1 25 114 [36046095543959560, 28227770880698901, 2],
  lm2M 124 644485 1 27 122 [3201676370406429, 47127035471222770, 925],
  lm2M 124 594710 1 26 122 [10195675841040498, 17665284407808, 514],
  lm2M 124 591220 1 26 106 [366927931779289, 633387419173200],
  lm2M 124 556190 1 25 100 [36276706242971, 10042237788802],
  lm2M 124 562321 1 25 124 [39932062433477056, 66402722262282231, 2080],
  lm2M 124 362109 1 21 113 [10703867633486914, 143211391703297, 1],
  lm2M 124 342071 1 21 121 [10697825100761218, 43981004146945, 256],
  lm2M 124 338875 1 21 121 [308431013609472, 146570070598, 256],
  lm2M 124 335335 1 21 109 [18861423540264972, 4504976366252545] ]
private def lm2SegsR128 : List DickeSol.Rkm128kSeg :=
  lm2R128C0 ++ (lm2R128C1 ++ (lm2R128C2 ++ (lm2R128C3 ++ (lm2R128C4 ++ lm2R128C5))))
private def lm2RowR128P0 : List ℕ := [
  0, 0, 6, 0, 10, 4, 6, 1, 0, 35, 28, 5, 40, 12, 16, 0, 32, 16, 56, 23, 183, 132, 413, 125, 12,
  468, 1307, 431, 73, 216, 1739, 180, 805, 213, 46, 234, 5738, 9, 11, 5331, 393, 14477, 8161,
  2866, 4264, 16235, 73419, 812 ]
private def lm2RowR128P1 : List ℕ := [
  892, 15626, 418, 41045, 13112, 34367, 32595, 4465, 114416, 5644, 116746, 123522, 742008,
  1852228, 1580077, 2949942, 28774, 155401, 152920, 8646, 15653, 471, 20128, 134928, 798022,
  738990, 1176453, 26780836, 4940645, 5989635, 54, 4614940, 106361704, 1052, 1324001, 13190679,
  1409237, 5685175, 20187242, 116861329, 263937746, 314228624, 109385167, 499644435, 77864817,
  9749720, 6296724, 2049538 ]
private def lm2RowR128P2 : List ℕ := [
  89465965, 44471025, 98946579, 481584, 112374509, 7023817, 324391268, 2160537, 151011115,
  705484390, 18906792, 58065820, 564289541, 531311785, 771232666, 3639944856, 1454533007,
  321603541, 1435291797, 170939574, 2780918638, 3113509749, 2782341578, 17123215, 5161838235,
  1985222569, 1275231987, 2200502644, 28235338442, 318626802916, 460539956474, 161177775845 ]
private def lm2RowR128 : List ℕ :=
  lm2RowR128P0 ++ (lm2RowR128P1 ++ lm2RowR128P2)
private def lm2R128V1P0 : List ℤ := [
  Int.ofNat 1130180823417, Int.ofNat 622920821454, Int.ofNat 46030603943,
  Int.ofNat 576675607996, Int.ofNat 782905259430, Int.ofNat 286646855149,
  Int.negSucc 700855042646, Int.ofNat 1560380952696, Int.negSucc 215587052655,
  Int.negSucc 1091621766840, Int.ofNat 884361670799, Int.negSucc 887936728489,
  Int.negSucc 834184122898, Int.negSucc 2618020035077, Int.negSucc 998526880768,
  Int.negSucc 1730627468003, Int.ofNat 1060161620039, Int.negSucc 190892444649,
  Int.negSucc 7604098372291, Int.ofNat 1209939777684, Int.ofNat 2964080850400,
  Int.ofNat 3770824909420, Int.ofNat 1297174984766, Int.ofNat 4625324776573,
  Int.ofNat 9036920983990, Int.negSucc 1024311746025, Int.negSucc 3774433340577,
  Int.negSucc 1894422459040, Int.ofNat 2258544520539, Int.ofNat 10975328651383,
  Int.negSucc 6614644884866, Int.negSucc 5524319285653, Int.negSucc 4639878173684,
  Int.ofNat 3209566970637, Int.ofNat 8131387549106, Int.ofNat 5789385304228,
  Int.negSucc 12421664221734, Int.ofNat 2650908592581, Int.negSucc 4850324868961,
  Int.negSucc 9111701695589, Int.ofNat 7400740598096, Int.ofNat 30993051619466,
  Int.ofNat 106253122865158, Int.ofNat 203476126217315, Int.ofNat 300532852501961,
  Int.ofNat 375928808320808, Int.ofNat 415233725596929, Int.ofNat 414291102707370 ]
private def lm2R128V1P1 : List ℤ := [
  Int.ofNat 378596235156912, Int.ofNat 319825287480952, Int.ofNat 251386529742969,
  Int.ofNat 184734597886550, Int.ofNat 127385635947402, Int.ofNat 82661074747639,
  Int.ofNat 50591843729096, Int.ofNat 29259007309205, Int.ofNat 16013676535861,
  Int.ofNat 8304427202107, Int.ofNat 4084661688561, Int.ofNat 1907194160062,
  Int.ofNat 845911740416, Int.ofNat 356597060358, Int.ofNat 142924581166, Int.ofNat 54471683859,
  Int.ofNat 19738803279, Int.ofNat 6798660576, Int.ofNat 2224752357, Int.ofNat 691156244,
  Int.negSucc 203568344, Int.ofNat 56712252, Int.ofNat 14896981, Int.ofNat 3676851,
  Int.ofNat 850275, Int.ofNat 183937, Int.ofNat 37227, Int.ofNat 7057, Int.ofNat 1249,
  Int.ofNat 203, Int.ofNat 27, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R128V1P2 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R128V1 : List ℤ :=
  lm2R128V1P0 ++ (lm2R128V1P1 ++ lm2R128V1P2)
private def lm2R128V2P0 : List ℤ := [
  Int.negSucc 1264135666, Int.negSucc 91985487969, Int.negSucc 220660447530,
  Int.negSucc 282142705037, Int.negSucc 74588722705, Int.negSucc 373617100434,
  Int.negSucc 427908100212, Int.ofNat 50001006908, Int.ofNat 52718056081,
  Int.negSucc 63121920191, Int.negSucc 65471490318, Int.negSucc 238737627876,
  Int.negSucc 813179520364, Int.negSucc 2167704108525, Int.negSucc 2549907536312,
  Int.negSucc 2466300820712, Int.ofNat 56796488644, Int.ofNat 2612719305835,
  Int.ofNat 2895867782667, Int.ofNat 2017124263143, Int.ofNat 1153411987810,
  Int.ofNat 263236598327, Int.ofNat 1046631113985, Int.ofNat 2944281511434,
  Int.ofNat 4553363163981, Int.negSucc 494901887840, Int.ofNat 3935385589382,
  Int.ofNat 5555876589811, Int.ofNat 7111176117528, Int.ofNat 4142574716580,
  Int.ofNat 1030406918138, Int.ofNat 2303504406085, Int.negSucc 3160105232976,
  Int.negSucc 2968824602362, Int.negSucc 5393339043347, Int.negSucc 9904538004952,
  Int.negSucc 1662007550175, Int.ofNat 12379680536835, Int.ofNat 8936926819239,
  Int.negSucc 2953521470827, Int.ofNat 1687551729870, Int.ofNat 6846473490120,
  Int.ofNat 12418788610532, Int.negSucc 5936272290008, Int.ofNat 139115273571,
  Int.ofNat 2699758920301, Int.negSucc 9596617276026, Int.ofNat 8028348576768 ]
private def lm2R128V2P1 : List ℤ := [
  Int.ofNat 10891540509446, Int.ofNat 556937554150, Int.ofNat 3618171490141,
  Int.negSucc 6403612339109, Int.negSucc 1716545136020, Int.negSucc 2035643491016,
  Int.negSucc 3162466417896, Int.negSucc 15020391815021, Int.negSucc 10766301838184,
  Int.negSucc 1667797045471, Int.ofNat 1788136517175, Int.ofNat 2595396539286,
  Int.ofNat 3160161137787, Int.ofNat 14062010844008, Int.ofNat 6407093430840,
  Int.negSucc 3018761877041, Int.negSucc 19880338734150, Int.negSucc 15599986018100,
  Int.negSucc 17585850963704, Int.ofNat 9135790720566, Int.ofNat 9658020214354,
  Int.ofNat 11189609843901, Int.ofNat 8153755742059, Int.ofNat 43378063995835,
  Int.ofNat 136476529242873, Int.ofNat 246084815273893, Int.ofNat 343110526937860,
  Int.ofNat 405915420553139, Int.ofNat 424942272398538, Int.ofNat 402979474309914,
  Int.ofNat 351308212903263, Int.ofNat 284209500005753, Int.ofNat 214817839269491,
  Int.ofNat 152518161929803, Int.ofNat 102094335312797, Int.ofNat 64583521950354,
  Int.ofNat 38703036204029, Int.ofNat 22042114598288, Int.ofNat 11957778868110,
  Int.ofNat 6174273533843, Int.ofNat 3021331183795, Int.ofNat 1393127747735,
  Int.ofNat 602529525587, Int.ofNat 243990974855, Int.ofNat 92612112561, Int.ofNat 33062564976,
  Int.ofNat 11154914705, Int.ofNat 3576726086 ]
private def lm2R128V2P2 : List ℤ := [
  Int.ofNat 1096614578, Int.ofNat 323569420, Int.ofNat 92430088, Int.ofNat 25663357,
  Int.negSucc 6911183, Int.ofNat 1828458, Int.ofNat 430473, Int.ofNat 83806, Int.negSucc 14191,
  Int.ofNat 2414, Int.ofNat 443, Int.ofNat 80, Int.negSucc 10, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R128V2 : List ℤ :=
  lm2R128V2P0 ++ (lm2R128V2P1 ++ lm2R128V2P2)
private def lm2R128V3P0 : List ℤ := [
  Int.negSucc 2864860769, Int.negSucc 9623533866, Int.ofNat 384618539, Int.ofNat 6860545067,
  Int.negSucc 8380654526, Int.negSucc 25032473570, Int.negSucc 27254757063,
  Int.negSucc 5513300376, Int.negSucc 70468438104, Int.negSucc 218299896405,
  Int.negSucc 401425325425, Int.negSucc 375377547901, Int.negSucc 401028893781,
  Int.negSucc 7403989627, Int.ofNat 175682268786, Int.ofNat 287275269015,
  Int.ofNat 199898994435, Int.negSucc 29402965865, Int.ofNat 254044418397,
  Int.ofNat 524358057405, Int.ofNat 469125550926, Int.ofNat 813595238736, Int.ofNat 24797328396,
  Int.ofNat 293609001151, Int.ofNat 146014173670, Int.ofNat 971964618326,
  Int.negSucc 30617557399, Int.ofNat 503615299065, Int.ofNat 1484517524949,
  Int.ofNat 1904085388926, Int.ofNat 3051167069055, Int.ofNat 3966862081504,
  Int.ofNat 5845666399772, Int.ofNat 5976504194413, Int.ofNat 2482796670422,
  Int.negSucc 108727938015, Int.negSucc 2276972624655, Int.ofNat 1283468967817,
  Int.ofNat 1623511583221, Int.ofNat 55879987412, Int.ofNat 4168450924344,
  Int.ofNat 2319698505614, Int.ofNat 4624847735457, Int.ofNat 9338648967182,
  Int.ofNat 13178447717625, Int.ofNat 11604819391559, Int.ofNat 5734252855556,
  Int.negSucc 875850765584 ]
private def lm2R128V3P1 : List ℤ := [
  Int.negSucc 3431723667585, Int.negSucc 4444912660913, Int.ofNat 2558445825983,
  Int.ofNat 7848054887121, Int.ofNat 5947774911851, Int.ofNat 11380216387007,
  Int.negSucc 2871823948575, Int.ofNat 6715911032757, Int.ofNat 10808702677321,
  Int.ofNat 10007228787210, Int.negSucc 2676241288051, Int.negSucc 3285978882532,
  Int.ofNat 4370900400192, Int.ofNat 7118945818556, Int.negSucc 3261843509724,
  Int.ofNat 2546650842687, Int.negSucc 2720656225995, Int.negSucc 5675582378225,
  Int.negSucc 8096919481952, Int.ofNat 2298678916908, Int.ofNat 3689794526489,
  Int.ofNat 12988888467558, Int.ofNat 2839481036234, Int.negSucc 8296346698948,
  Int.negSucc 1678092676963, Int.negSucc 4316083301120, Int.negSucc 453499169874,
  Int.negSucc 4743864731756, Int.ofNat 4416704368362, Int.ofNat 15149882104927,
  Int.ofNat 13934647696113, Int.ofNat 17167053488032, Int.ofNat 21107363268004,
  Int.ofNat 22990079875240, Int.ofNat 17004302031655, Int.negSucc 952096241625,
  Int.negSucc 7280741066295, Int.ofNat 161375751142, Int.negSucc 4888519911711,
  Int.ofNat 8616475718621, Int.ofNat 29251442500612, Int.ofNat 37141254641061,
  Int.ofNat 25436676075081, Int.ofNat 6892368338654, Int.ofNat 11664519550799,
  Int.ofNat 97359106671889, Int.ofNat 221135206310244, Int.ofNat 340176040792511 ]
private def lm2R128V3P2 : List ℤ := [
  Int.ofNat 419941103990602, Int.ofNat 444708941242668, Int.ofNat 417797260315760,
  Int.ofNat 355147786305509, Int.ofNat 276647983587736, Int.ofNat 199163701885382,
  Int.ofNat 133279636991441, Int.ofNat 83259616979116, Int.ofNat 48717669137834,
  Int.ofNat 26808233542090, Int.ofNat 13602985114691, Int.ofNat 7779938348601,
  Int.ofNat 636076941923, Int.ofNat 244371138127, Int.ofNat 301043215938,
  Int.ofNat 160362383377, Int.ofNat 61145289691, Int.ofNat 19801017053, Int.ofNat 5852627888,
  Int.negSucc 1392068262, Int.ofNat 256607545, Int.negSucc 29528499, Int.ofNat 2880679,
  Int.ofNat 470817, Int.ofNat 98711, Int.ofNat 11429, Int.ofNat 829, Int.ofNat 47, Int.ofNat 1,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R128V3 : List ℤ :=
  lm2R128V3P0 ++ (lm2R128V3P1 ++ lm2R128V3P2)
private def lm2R128V4P0 : List ℤ := [
  Int.negSucc 267574951, Int.ofNat 7163452734, Int.ofNat 5585850314, Int.ofNat 6075022913,
  Int.ofNat 7065430539, Int.negSucc 8752469833, Int.negSucc 8380853607, Int.negSucc 13055097099,
  Int.negSucc 16227972045, Int.ofNat 1443034909, Int.ofNat 28358098502, Int.ofNat 10009911891,
  Int.negSucc 44530756847, Int.negSucc 3430812557, Int.ofNat 67934044686,
  Int.ofNat 102363970797, Int.ofNat 54063443088, Int.ofNat 5552654829, Int.negSucc 64989373621,
  Int.negSucc 51801721894, Int.negSucc 66509514622, Int.ofNat 66364501946,
  Int.negSucc 7628912657, Int.negSucc 217109674345, Int.negSucc 268133472905,
  Int.negSucc 663297007461, Int.negSucc 635758417515, Int.negSucc 530941713300,
  Int.negSucc 192061113265, Int.ofNat 119636219280, Int.negSucc 258561473073,
  Int.negSucc 286784977633, Int.ofNat 342532374307, Int.ofNat 1222686388105,
  Int.ofNat 1069625360207, Int.ofNat 245553146275, Int.ofNat 15447951904,
  Int.ofNat 903345025910, Int.ofNat 44582091077, Int.negSucc 66421705875,
  Int.ofNat 283633506184, Int.ofNat 516214163574, Int.negSucc 189055926282,
  Int.negSucc 298144625162, Int.ofNat 360317725092, Int.negSucc 577016174768,
  Int.ofNat 567748677340, Int.ofNat 119242593170 ]
private def lm2R128V4P1 : List ℤ := [
  Int.ofNat 2090696369792, Int.ofNat 4112308573691, Int.ofNat 6693921005713,
  Int.ofNat 5965405471547, Int.ofNat 7090404098259, Int.ofNat 4505589955363,
  Int.ofNat 3505439087451, Int.ofNat 605583292946, Int.negSucc 675884318159,
  Int.negSucc 1497796744392, Int.negSucc 2481541748850, Int.negSucc 5248569878239,
  Int.negSucc 3976059417186, Int.ofNat 8683784395795, Int.ofNat 22063095524440,
  Int.ofNat 7168242122466, Int.negSucc 223280440216, Int.ofNat 4924206338954,
  Int.ofNat 3128205310697, Int.ofNat 850895602524, Int.ofNat 1178770749672,
  Int.ofNat 4092783046050, Int.negSucc 6598554017656, Int.ofNat 9146243360268,
  Int.ofNat 17846876133661, Int.ofNat 7409916529248, Int.ofNat 5124678594779,
  Int.negSucc 1953411870852, Int.ofNat 1949945358571, Int.ofNat 12195757681395,
  Int.ofNat 2517658578815, Int.negSucc 1837985076840, Int.ofNat 7576465677733,
  Int.negSucc 2916776547927, Int.negSucc 10653542994586, Int.negSucc 902399044426,
  Int.ofNat 1514984658595, Int.ofNat 1914061457491, Int.ofNat 2788274896537,
  Int.ofNat 8052481795963, Int.negSucc 252550195039, Int.negSucc 7025129651549,
  Int.negSucc 4917147872935, Int.negSucc 2158640003761, Int.ofNat 1378151270720,
  Int.ofNat 3444791936720, Int.ofNat 12303782183824, Int.ofNat 44870977277516 ]
private def lm2R128V4P2 : List ℤ := [
  Int.ofNat 49426301801994, Int.ofNat 18900114821948, Int.negSucc 24666169659944,
  Int.negSucc 11188321048881, Int.negSucc 3538471507745, Int.ofNat 11352479520268,
  Int.ofNat 19774877943019, Int.negSucc 13002220307175, Int.negSucc 46466625372635,
  Int.negSucc 6119958310563, Int.ofNat 16984800600275, Int.ofNat 128868991657332,
  Int.ofNat 281654440691378, Int.ofNat 411497374121805, Int.ofNat 473680019911806,
  Int.ofNat 457197880415557, Int.ofNat 384492494412777, Int.ofNat 289206090203466,
  Int.ofNat 196781902354471, Int.ofNat 120848705775784, Int.ofNat 66386500917237,
  Int.ofNat 32465033640670, Int.ofNat 13928203075192, Int.ofNat 5586801960825,
  Int.ofNat 1778242338459, Int.ofNat 414844965258, Int.ofNat 77218675371, Int.ofNat 15185113717,
  Int.ofNat 3888579699, Int.ofNat 1032681834, Int.ofNat 218875368, Int.ofNat 32415236,
  Int.ofNat 2888721 ]
private def lm2R128V4 : List ℤ :=
  lm2R128V4P0 ++ (lm2R128V4P1 ++ lm2R128V4P2)
private def lm2R128V5P0 : List ℤ := [
  Int.negSucc 360734983, Int.negSucc 4489778531, Int.negSucc 36903883, Int.negSucc 11269540,
  Int.negSucc 4909158157, Int.negSucc 3404191604, Int.negSucc 7450319708,
  Int.negSucc 3628374806, Int.ofNat 5092135284, Int.ofNat 9412766714, Int.ofNat 22608160176,
  Int.ofNat 5294779914, Int.negSucc 27372113861, Int.ofNat 18543594845, Int.ofNat 10022915288,
  Int.ofNat 2593308921, Int.ofNat 16700387344, Int.negSucc 11641765447, Int.negSucc 51644415067,
  Int.negSucc 7623896920, Int.negSucc 13450736011, Int.ofNat 7679131932, Int.negSucc 1724473099,
  Int.ofNat 26939190327, Int.ofNat 12877501627, Int.ofNat 3609408546, Int.ofNat 29040261985,
  Int.ofNat 36965291006, Int.ofNat 196911829447, Int.ofNat 94957294008, Int.ofNat 5022573667,
  Int.negSucc 119749607558, Int.ofNat 98746024879, Int.ofNat 19805886431,
  Int.negSucc 4215029537, Int.negSucc 52884943629, Int.negSucc 54352596769,
  Int.negSucc 122411431219, Int.negSucc 12737821307, Int.negSucc 248553907107,
  Int.negSucc 746789283356, Int.negSucc 1044133862019, Int.negSucc 1088071492911,
  Int.negSucc 1209982917122, Int.negSucc 1092471109401, Int.negSucc 581332936595,
  Int.negSucc 79620764940, Int.ofNat 194524744270 ]
private def lm2R128V5P1 : List ℤ := [
  Int.negSucc 347125922128, Int.ofNat 233456331636, Int.ofNat 279821692011,
  Int.ofNat 505455523991, Int.ofNat 549045629927, Int.ofNat 156996088725,
  Int.negSucc 393917145354, Int.ofNat 1352378452261, Int.negSucc 259286702734,
  Int.negSucc 810286503239, Int.negSucc 1125085791833, Int.negSucc 2704761944719,
  Int.negSucc 3889089707118, Int.negSucc 1896171243918, Int.negSucc 1012656189545,
  Int.ofNat 884871263619, Int.negSucc 2757199685278, Int.negSucc 1536819121907,
  Int.ofNat 686585209693, Int.ofNat 1126597715921, Int.ofNat 1998002216961,
  Int.ofNat 6789867959555, Int.ofNat 13510404408356, Int.ofNat 16264904051132,
  Int.ofNat 16143434954231, Int.ofNat 11735019129283, Int.negSucc 2352217551188,
  Int.negSucc 15254434100107, Int.ofNat 2031580629785, Int.ofNat 1122445122199,
  Int.negSucc 244373572754, Int.negSucc 3700900126250, Int.negSucc 7411824361497,
  Int.negSucc 2872669519688, Int.ofNat 1868864291087, Int.ofNat 5097830981077,
  Int.ofNat 12655026530435, Int.ofNat 6930584492291, Int.ofNat 2413976203855,
  Int.ofNat 4122770623066, Int.ofNat 7885402137402, Int.ofNat 11853635974020,
  Int.ofNat 8640650555071, Int.negSucc 1193782568288, Int.negSucc 637391432238,
  Int.ofNat 5841038822037, Int.negSucc 10418028602395, Int.ofNat 627801909198 ]
private def lm2R128V5P2 : List ℤ := [
  Int.negSucc 8481426451738, Int.negSucc 19427046031066, Int.ofNat 10829830006541,
  Int.ofNat 25087324296754, Int.negSucc 7653416740835, Int.negSucc 1831048596873,
  Int.ofNat 16679292585726, Int.negSucc 17691977831401, Int.negSucc 1236749121572,
  Int.negSucc 41052510219301, Int.negSucc 23721498756845, Int.ofNat 45453209651468,
  Int.negSucc 3243406348001, Int.ofNat 6827759709473, Int.ofNat 46229374674369,
  Int.negSucc 1056776176313, Int.ofNat 334041919467, Int.ofNat 56405741060007,
  Int.ofNat 56545779001911, Int.ofNat 24705538680218, Int.negSucc 4454580439816,
  Int.ofNat 111995106666271, Int.ofNat 311704084412606, Int.ofNat 476793922373789,
  Int.ofNat 526952809206821, Int.ofNat 458693392052096, Int.ofNat 328371455323739,
  Int.ofNat 196466122168157, Int.ofNat 97355489045030, Int.ofNat 38802388849229,
  Int.ofNat 12348936304174, Int.ofNat 2173066434833, Int.ofNat 191782048995 ]
private def lm2R128V5 : List ℤ :=
  lm2R128V5P0 ++ (lm2R128V5P1 ++ lm2R128V5P2)
private def lm2Anc0 : List DickeSol.RampKick128kAnchor := [
  ⟨3, lm2SegsR3, lm2RowR3⟩, ⟨4, lm2SegsR4, lm2RowR4⟩, ⟨5, lm2SegsR5, lm2RowR5⟩,
  ⟨6, lm2SegsR6, lm2RowR6⟩, ⟨7, lm2SegsR7, lm2RowR7⟩, ⟨8, lm2SegsR8, lm2RowR8⟩,
  ⟨9, lm2SegsR9, lm2RowR9⟩, ⟨10, lm2SegsR10, lm2RowR10⟩, ⟨11, lm2SegsR11, lm2RowR11⟩,
  ⟨12, lm2SegsR12, lm2RowR12⟩, ⟨13, lm2SegsR13, lm2RowR13⟩, ⟨14, lm2SegsR14, lm2RowR14⟩,
  ⟨15, lm2SegsR15, lm2RowR15⟩, ⟨16, lm2SegsR16, lm2RowR16⟩, ⟨17, lm2SegsR17, lm2RowR17⟩ ]
private def lm2Anc1a : List DickeSol.RampKick128kAnchor := [
  ⟨18, lm2SegsR18, lm2RowR18⟩, ⟨19, lm2SegsR19, lm2RowR19⟩, ⟨22, lm2SegsR22, lm2RowR22⟩,
  ⟨25, lm2SegsR25, lm2RowR25⟩, ⟨27, lm2SegsR27, lm2RowR27⟩ ]
private def lm2Anc1b : List DickeSol.RampKick128kAnchor := [
  ⟨34, lm2SegsR34, lm2RowR34⟩, ⟨38, lm2SegsR38, lm2RowR38⟩, ⟨49, lm2SegsR49, lm2RowR49⟩,
  ⟨51, lm2SegsR51, lm2RowR51⟩ ]
private def lm2k128Anchors : List DickeSol.RampKick128kAnchor :=
  lm2Anc0 ++ (lm2Anc1a ++ (⟨32, lm2SegsR32, lm2RowR32⟩ ::
    (lm2Anc1b ++ [⟨64, lm2SegsR64, lm2RowR64⟩, ⟨128, lm2SegsR128, lm2RowR128⟩])))

private theorem lm2Batch0 : lm2AtF [
    DickeSol.rkm128kCheckTable 2 128 124 true lm2k128VPot lm2k128Anchors,
    lm2ChkCell 8 7 29359515018607 50000000000000 lm2k128VPot lm2k128Anchors,
    lm2ChkCell 16 15 138280842621027 250000000000000 lm2k128VPot lm2k128Anchors,
    lm2ChkCell 32 31 524680560022403 1000000000000000 lm2k128VPot lm2k128Anchors,
    lm2ChkCell 64 62 506001440881489 1000000000000000 lm2k128VPot lm2k128Anchors,
    lm2ChkCell 128 124 98552131503687 200000000000000 lm2k128VPot lm2k128Anchors,
    lm2SegBds 64 lm2SegsR64, lm2SegBds 128 lm2SegsR128, lm2ChkAnchors lm2Anc0
  ] = true := by decide +kernel
private theorem lm2Batch1 :
    Bool.and (lm2ChkAnchors lm2Anc1a) (lm2ChkAnchors lm2Anc1b) = true := by
  decide +kernel
private theorem lm2Batch2 :
    Bool.and (lm2ChkRow 32 lm2SegsR32 lm2RowR32)
      (lm2ChkSeg 64 lm2R64C0 1 0 1 [Int.ofNat DickeSol.wdScale]
        (33, 64, 78898, lm2R64V1)) = true := by decide +kernel
private theorem lm2Batch3 :
    lm2ChkSeg 64 lm2R64C1 33 64 78898 lm2R64V1
      (61, 64, 266880, lm2R64V2) = true := by decide +kernel
private theorem lm2Batch4 :
    Bool.and (lm2ChkFin 64 lm2R64C2 61 64 266880 lm2R64V2 lm2RowR64)
      (lm2ChkSeg 128 lm2R128C0 1 0 1 [Int.ofNat DickeSol.wdScale]
        (51, 102, 184251, lm2R128V1)) = true := by
  decide +kernel
private theorem lm2Batch5 :
    lm2ChkSeg 128 lm2R128C1 51 102 184251 lm2R128V1
      (80, 128, 442589, lm2R128V2) = true := by decide +kernel
private theorem lm2Batch6 :
    lm2ChkSeg 128 lm2R128C2 80 128 442589 lm2R128V2
      (101, 128, 726101, lm2R128V3) = true := by decide +kernel
private theorem lm2Batch7 :
    lm2ChkSeg 128 lm2R128C3 101 128 726101 lm2R128V3
      (112, 128, 1000829, lm2R128V4) = true := by decide +kernel
private theorem lm2Batch8 :
    lm2ChkSeg 128 lm2R128C4 112 128 1000829 lm2R128V4
      (121, 128, 1272515, lm2R128V5) = true := by decide +kernel
private theorem lm2Batch9 :
    lm2ChkFin 128 lm2R128C5 121 128 1272515 lm2R128V5 lm2RowR128 = true := by decide +kernel

private theorem lm2Row64Sound :
    DickeSol.rkm128kEvalRowLo12 2 124 64 lm2SegsR64 = lm2RowR64 := by
  apply lm2CertSplit (lm2_hd (lm2_tl2 (lm2_tl4 lm2Batch0))); unfold lm2SegsR64
  exact lm2TailStep (lm2_and_r lm2Batch2)
    (lm2TailStep lm2Batch3 (lm2TailEnd (lm2_and_l lm2Batch4)))
private theorem lm2Row128Sound :
    DickeSol.rkm128kEvalRowLo12 2 124 128 lm2SegsR128 = lm2RowR128 := by
  apply lm2CertSplit (lm2_hd (lm2_tl1 (lm2_tl2 (lm2_tl4 lm2Batch0)))); unfold lm2SegsR128
  exact lm2TailStep (lm2_and_r lm2Batch4)
    (lm2TailStep lm2Batch5 (lm2TailStep lm2Batch6
      (lm2TailStep lm2Batch7 (lm2TailStep lm2Batch8 (lm2TailEnd lm2Batch9)))))
private theorem lm2AncSound :
    DickeSol.RampKick128kAnchorsSound 2 124 lm2k128Anchors :=
  lm2ChkAnchors_append (lm2_hd (lm2_tl8 lm2Batch0))
    (lm2ChkAnchors_append (lm2_and_l lm2Batch1)
      ⟨lm2ListEq_eq (@lm2NatEq_eq) (lm2_and_l lm2Batch2),
        lm2ChkAnchors_append (lm2_and_r lm2Batch1)
          ⟨lm2Row64Sound, ⟨lm2Row128Sound, trivial⟩⟩⟩)
private theorem lm2k128Valid :
    DickeSol.RampKick128kTableValid 2 128 124 true lm2k128VPot lm2k128Anchors :=
  DickeSol.rkm128kCheckTable_sound lm2AncSound (lm2_hd lm2Batch0)
private theorem lm2k128CellChecks {m k : ℕ} (h : isLowM2K128KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (lowM2K128KrotovCertCellLMax m k)
        lm2k128Anchors = true ∧
      ∃ num den : ℕ, relCostLowM2K128KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (lm2k128VPot.getD k 0) num den = true := by
  unfold isLowM2K128KrotovCertCell at h
  split_ifs at h with hm2 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm2 hk8; have hm := lm2_hd (lm2_tl1 lm2Batch0)
    exact ⟨lm2_and_l hm, 29359515018607, 50000000000000, rfl, lm2_and_r hm⟩
  · subst hm2 hk16; have hm := lm2_hd (lm2_tl2 lm2Batch0)
    exact ⟨lm2_and_l hm, 138280842621027, 250000000000000, rfl, lm2_and_r hm⟩
  · subst hm2 hk32; have hm := lm2_hd (lm2_tl1 (lm2_tl2 lm2Batch0))
    exact ⟨lm2_and_l hm, 524680560022403, 1000000000000000, rfl, lm2_and_r hm⟩
  · subst hm2 hk64; have hm := lm2_hd (lm2_tl4 lm2Batch0)
    exact ⟨lm2_and_l hm, 506001440881489, 1000000000000000, rfl, lm2_and_r hm⟩
  · subst hm2 hk128; have hm := lm2_hd (lm2_tl1 (lm2_tl4 lm2Batch0))
    exact ⟨lm2_and_l hm, 98552131503687, 200000000000000, rfl, lm2_and_r hm⟩

private lemma lm2k128_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma lm2k128_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma lm2k128_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl
private lemma lm2k128_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d
private lemma lm2k128_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lm2k128_le_of_add h), rfl⟩

private structure Lm2k128CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk128 : k ≤ 128
  hm2 : 2 ≤ m
  hl2 : 2 ≤ lowM2K128KrotovCertCellLMax m k
  hl1 : 1 ≤ lowM2K128KrotovCertCellLMax m k
  hlm : lowM2K128KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 128 124 true lm2k128VPot lm2k128Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM2K128KrotovCertCellLMax m k) lm2k128Anchors = true
  hcost : ∃ num den : ℕ, relCostLowM2K128KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (lm2k128VPot.getD k 0) num den = true

private lemma lm2k128_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hj : (j + 1) + d1 = 11)
    (h128 : k + dk = 128) (hl2 : 2 + dl2 = lowM2K128KrotovCertCellLMax 2 k)
    (hl1 : 1 + dl1 = lowM2K128KrotovCertCellLMax 2 k)
    (hlm : lowM2K128KrotovCertCellLMax 2 k * 2 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM2K128KrotovCertCellLMax 2 k)
      lm2k128Anchors = true)
    (hcost : ∃ num den : ℕ, relCostLowM2K128KrotovCert 2 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 2 k (lm2k128VPot.getD k 0) num den = true) :
    Lm2k128CellProps 2 k :=
  ⟨lm2k128_mem_grid 1 9 rfl, hk ▸ lm2k128_mem_grid j d1 hj, lm2k128_le_of_add h128, le_rfl,
    lm2k128_le_of_add hl2, lm2k128_le_of_add hl1, lm2k128_le_of_add hlm, lm2k128Valid, hlmax,
    hcost⟩

private theorem lm2k128_all_props {m k : ℕ} (h : isLowM2K128KrotovCertCell m k = true) :
    Lm2k128CellProps m k := by
  rcases lm2k128CellChecks h with ⟨hlmax, hcost⟩; unfold isLowM2K128KrotovCertCell at h
  split_ifs at h with hm2 hk8 hk16 hk32 hk64 hk128
  all_goals simp only [beq_iff_eq] at *
  · subst hm2 hk8; exact lm2k128_mk 3 7 120 5 6 65522 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm2 hk16; exact lm2k128_mk 4 6 112 13 14 65506 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm2 hk32; exact lm2k128_mk 5 5 96 29 30 65474 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm2 hk64; exact lm2k128_mk 6 4 64 60 61 65412 rfl rfl rfl rfl rfl rfl hlmax hcost
  · subst hm2 hk128; exact lm2k128_mk 7 3 0 122 123 65288 rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def lowM2K128KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM2K128KrotovCertQubits n m k)) Var
      (lowM2K128KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isLowM2K128KrotovCertCell m k = true then
    let p := lm2k128_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm2k128VPot lm2k128Anchors p.hk128
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit across the 5 m = 2, 8 ≤ k ≤ 128 cells. -/
noncomputable def findAllJohnsonRampKick128kLowM2K128KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM2K128KrotovCertQubits n m k)) Var
      (lowM2K128KrotovCertQubits n m k) ((n + 1) * m) :=
  lowM2K128KrotovCertCircuitImpl res n m k

private lemma lm2k128_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isLowM2K128KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kLowM2K128KrotovCertCircuit res n m k =
      let p := lm2k128_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm2k128VPot lm2k128Anchors p.hk128
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kLowM2K128KrotovCertCircuit lowM2K128KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-1 recovery of S across the 5 m = 2, 8 ≤ k ≤ 128 cells. -/
theorem lowM2K128KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isLowM2K128KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kLowM2K128KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [lm2k128_targetSets_eq]
  have hp := lm2k128_all_props hcell
  rw [lm2k128_circuit_eq res n hcell, ← lm2k128_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG lm2k128VPot lm2k128Anchors hp.hk128
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across m = 2, 8 ≤ k ≤ 128. -/
theorem lowM2K128KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isLowM2K128KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kLowM2K128KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostLowM2K128KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := lm2k128_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG lm2k128VPot
    lm2k128Anchors hp.hk128 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [lm2k128_circuit_eq res n hcell, ← lm2k128_oracle_eq]
    exact hq S (by rwa [lm2k128_targetSets_eq])
  · rw [← lm2k128_targetSets_eq, ← lm2k128_vanilla_eq]; exact hsum

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

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM2K128KrCert
