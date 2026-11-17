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
# Krotov `(2, 256)` Certificate (`Rk128kLowM2K256KrCert`)

QHL-verified module packaging cell `(2, 256)` over `47` anchors (`413,865` F1272 /
`420,170` Horner coord-ops at `lTableMax = 250`, `useColdR2 = true`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM2K256KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported (m, k) cell (m = 2, k = 256, 1 cell). -/
def isLowM2K256KrotovCertCell (m k : ℕ) : Bool :=
  if m == 2 then
    if k == 256 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor L_max(2, 256) = 250 (250 * 2 = 500 <= 65536). -/
def lowM2K256KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 2 then
    if k == 256 then 250
    else 1
  else 1

/-- Total register qubit budget (lowM2K256KrotovCertCellLMax m k * m) * (n + 1) + k * n. -/
abbrev lowM2K256KrotovCertQubits (n m k : ℕ) : ℕ :=
  (lowM2K256KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified coprime relative-cost profile c(2, 256): ℚ≥0. -/
def relCostLowM2K256KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 2 then
    if k == 256 then NNRat.divNat 483770197151367 1000000000000000
    else 1
  else 1

/-- Cost profile metadata (n0 = 80000, constructive threshold). -/
def lowM2K256KrotovCertProfile : FindAllCostProfile :=
  ⟨isLowM2K256KrotovCertCell, relCostLowM2K256KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kLowM2K256KrCert` cell lies on groverGrid × groverGrid. -/
theorem isLowM2K256KrotovCertCell_isGridCell {m k : ℕ}
    (h : isLowM2K256KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isLowM2K256KrotovCertCell at h
  split_ifs at h with hm2 hk256
  simp only [beq_iff_eq] at hm2 hk256
  subst hm2 hk256; rfl

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
  lm2ListEq lm2NatEq (DickeSol.rkm128kEvalRowLo12 2 250 r s) ro
private def lm2ChkAnchors (xs : List DickeSol.RampKick128kAnchor) : Bool :=
  match xs with
  | [] => true
  | a :: rest =>
    match a with
    | ⟨rAct, segs, row⟩ => cond (lm2ChkRow rAct segs row) (lm2ChkAnchors rest) false
private theorem lm2ChkAnchors_append {xs rest : List DickeSol.RampKick128kAnchor}
    (hxs : lm2ChkAnchors xs = true) (hrest : DickeSol.RampKick128kAnchorsSound 2 250 rest) :
    DickeSol.RampKick128kAnchorsSound 2 250 (xs ++ rest) := by
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
    (st1 : Lm2St) : Bool := lm2StEq (DickeSol.rkm128kRunSegs 2 250 r s l0 d0 p0 v0) st1
private def lm2ChkFin (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Bool :=
  lm2ListEq lm2NatEq (DickeSol.rkm128kFinalizeState
    (DickeSol.rkm128kRunSegs 2 250 r s l0 d0 p0 v0)) ro
private def lm2SegBds (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def lm2TailOk (r : ℕ) (rest : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Prop :=
  ∃ st, DickeSol.rkm128kRunSegs 2 250 r rest l0 d0 p0 v0 = st ∧
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
    DickeSol.rkm128kEvalRowLo12 2 250 r segs = ro := by
  rcases ht with ⟨st, hr, hf⟩; exact DickeSol.rkm128kCertRow_of_runSegs hb hr hf
private def lm2ChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) : Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 2 k (v.getD k 0) n d)

private def lm2k256VPotP0 : List ℕ := [
  0, 454456878931536, 632073517648122, 835610713846806, 983656550701756, 1111887371417670,
  1225463774450551, 1329432998717003, 1425547282696040, 1516436907593003, 1604366794910879,
  1686232580022233, 1766480954839723, 1892524614799337, 2013983324658224, 1980398011343997,
  2048711290664218, 2158933273847939, 2180012267748538, 2284271826141142, 2385891473554473,
  2485062094878147, 2427439595568510, 2522200405393126, 2614966027349797, 2577139248893437,
  2666265575576452, 2753725842705185, 2839610120080573, 2779581151745304, 2862553246413370,
  2911619228597948, 2991956613810289, 3071067402027633, 3115206342491990, 3192023575455916,
  3097245875662178, 3171958126332476, 3245680767075401, 3318452108082730, 3359265143862827,
  3422805560019738, 3492929778852191, 3533169863482515, 3601681815792146, 3669428247401033,
  3707430186412915, 3546885354631434 ]
private def lm2k256VPotP1 : List ℕ := [
  3612480554977984, 3651962756424019, 3716232664593892, 3753160293104628, 3816182123084435,
  3878606576264832, 3913703063826161, 3974982016880385, 4009515066459417, 4069709350562978,
  4103773002898352, 4156906773487609, 4215576904276651, 4249199130159690, 4306915211500106,
  4364171396417032, 4420978506283474, 4477346944643987, 4509127028496109, 4564647772879076,
  4596001737782002, 4650711916842871, 4681727334883542, 4735661443719140, 4766340593008556,
  4819530747469876, 4849843603753364, 4902319764030604, 4932270700141791, 4984060868040877,
  5013640819489979, 5064771213087827, 5093978779595575, 5144473988365746, 5173321339403741,
  5223204462416886, 5251707125378090, 5300999894780818, 5329169939857244, 5377892831501821,
  5405741638878248, 5453913971700422, 5481452288096475, 5529092313609265, 5556017746726490,
  5603142729805486, 5650016377849331, 5696642669823325 ]
private def lm2k256VPotP2 : List ℕ := [
  5743025480801661, 5789168585725834, 5835075662990029, 5880750297863117, 5926195985756271,
  5971416135344635, 6016414071550926, 6061193038398367, 6105756201739875, 6150106651870000,
  6194247406025721, 6238181410781814, 6281911544346181, 6325440618760201, 6368771382008855,
  6411906520045115, 6454848658732809, 6497600365711947, 6540164152190245, 6582542474664400,
  6624737736574440, 6666752289894312, 6708588436661679, 6750248430449746, 6791734477783779,
  6833048739504828, 6856442660011220, 6897419656811050, 6938231089310372, 6978878948275705,
  7019365184895334, 7059691711872217, 7099860404478388, 7139873101572507, 7179731606582122,
  7219437688452122, 7258993082560794, 7298399491604830, 7337658586454551, 7376772006980579,
  7415741362853099, 7454568234314821, 7493254172928692, 7531800702301356, 7570209318783319,
  7608481492146728, 7646618666241632, 7684622259631558 ]
private def lm2k256VPotP3 : List ℕ := [
  7722493666209186, 7760234255792889, 7797845374704849, 7835328346331449, 7872684471666598,
  7909915029838616, 7947021278621285, 7984004454929650, 8020865775301113, 8057606436362354,
  8094227615282588, 8130730470213640, 8167116140717305, 8203385748180440, 8239540396218216,
  8275581171065934, 8311509141959810, 8347325361507099, 8383030866045918, 8418626675995122,
  8454113796194569, 8489493216236084, 8524765910785442, 8559932839895660, 8594994949311887,
  8629953170768159, 8664808422276293, 8699561608407161, 8734213620564600, 8768765337252182,
  8803217624333080, 8837571335283236, 8871827311438052, 8905986382232798, 8940049365436933,
  8974017067382528, 9007890283186972, 9041669796970129, 9075356382066123, 9108950801229905,
  9142453806838763, 9175866141088921, 9209188536187381, 9242421714539133, 9275566388929888,
  9308623262704446, 9341593029940841, 9374476375620373 ]
private def lm2k256VPotP4 : List ℕ := [
  9407273975793648, 9439986497742750, 9472614600139635, 9505158933200876, 9537620138838843,
  9569998850809428, 9602295694856408, 9634511288852540, 9666646242937477, 9698701159652592,
  9730676634072794, 9762573253935423, 9794391599766291, 9826132245002959, 9857795756115312,
  9889382692723518, 9920893607713422, 9952329047349460, 9983689551385148, 10014975653171209,
  10046187879761408, 10077326752016143, 10108392784703858, 10139386486600331, 10170308360585888,
  10201158903740604, 10231938607437531, 10262647957434012, 10293287433961124, 10323857511811296,
  10354358660424153, 10384791343970621, 10415156021435343, 10445453146697446, 10475683168609695,
  10505846531076078, 10535943673127859, 10565975028998132, 10595941028194917, 10625842095572830,
  10655678651403362, 10685451111443796, 10715159887004801, 10744805385016730, 10774388008094651,
  10803908154602140, 10833366218713872, 10862762590477028 ]
private def lm2k256VPotP5 : List ℕ := [
  10892097655871549, 10921371796869268, 10950585391491938, 10979738813868183, 11008832434289401,
  11037866619264639, 11066841731574459, 11095758130323826, 11124616170994034, 11153416205493693,
  11182158582208794, 11210843646051883, 11239471738510346, 11268043197693844, 11296558358380901,
  11325017552064669, 8213381759442617 ]
private def lm2k256VPot : List ℕ :=
  lm2k256VPotP0 ++ (lm2k256VPotP1 ++ (lm2k256VPotP2 ++
    (lm2k256VPotP3 ++ (lm2k256VPotP4 ++ lm2k256VPotP5))))
private def lm2SegsR3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 14585658, 1, 6, []⟩, ⟨1, 20315927, 1, 6, []⟩, ⟨1, 20316866, 1, 6, []⟩,
  ⟨1, 20315483, 1, 7, []⟩, ⟨1, 20315483, 1, 7, []⟩, ⟨1, 20315482, 1, 7, []⟩,
  ⟨1, 20312482, 1, 7, []⟩, lm2M 1 20309482 1 7 3 [7], ⟨1, 10267977, 1, 5, []⟩,
  ⟨2, 1746603, 1, 4, []⟩, ⟨2, 7443743, 1, 6, []⟩, ⟨2, 7620383, 1, 6, []⟩,
  ⟨2, 7642733, 1, 6, []⟩, ⟨2, 7642733, 1, 6, []⟩, ⟨2, 7642733, 1, 6, []⟩,
  ⟨2, 7642733, 1, 6, []⟩, ⟨2, 7646733, 1, 6, []⟩, ⟨2, 7651033, 1, 6, []⟩,
  ⟨2, 15337211, 1, 7, []⟩, ⟨2, 15340811, 1, 7, []⟩, ⟨2, 15341467, 1, 7, []⟩,
  ⟨2, 15341617, 1, 7, []⟩, ⟨2, 15341617, 1, 7, []⟩, lm2M 2 21333367 1 8 1 [1],
  lm2M 2 14444691 1 7 1 [1], lm2M 2 13623396 1 7 1 [1], lm2M 2 15564803 1 7 1 [1],
  ⟨2, 15431248, 1, 7, []⟩, lm2M 2 15507391 1 7 4 [12], lm2M 2 14747337 1 7 2 [3],
  lm2M 2 13361679 1 7 2 [2], lm2M 2 6910697 1 6 4 [12] ]
private def lm2RowR3 : List ℕ := [
  2441664, 281524576800, 718472943216 ]
private def lm2SegsR4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 128486614, 1, 13, []⟩, ⟨2, 130314157, 1, 16, []⟩, lm2M 3 21107910 1 9 1 [1],
  lm2M 3 6645397 1 6 1 [1], ⟨3, 6764143, 1, 6, []⟩, lm2M 3 7436244 1 7 1 [1],
  ⟨3, 13535654, 1, 8, []⟩, lm2M 3 7524685 1 7 2 [2], ⟨3, 6605301, 1, 6, []⟩,
  lm2M 3 6949171 1 6 2 [3], ⟨3, 17181522, 1, 8, []⟩, lm2M 3 10688993 1 7 2 [2],
  lm2M 3 14822276 1 8 1 [1], lm2M 3 13014471 1 8 3 [4], lm2M 3 5393821 1 6 3 [6],
  lm2M 3 4970364 1 6 3 [7], lm2M 3 2706793 1 5 2 [2] ]
private def lm2RowR4 : List ℕ := [
  1395905, 169441, 348768193399, 651230231570 ]
private def lm2SegsR5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 32158994, 1, 8, []⟩, ⟨1, 26699147, 1, 8, []⟩, ⟨1, 25379762, 1, 8, []⟩,
  ⟨1, 27322005, 1, 8, []⟩, ⟨2, 2874658, 1, 5, []⟩, ⟨2, 13288277, 1, 7, []⟩,
  ⟨2, 12482071, 1, 7, []⟩, ⟨2, 13863864, 1, 7, []⟩, ⟨2, 13527280, 1, 7, []⟩,
  ⟨2, 13487025, 1, 7, []⟩, ⟨2, 12640786, 1, 7, []⟩, ⟨3, 16224759, 1, 9, []⟩,
  ⟨3, 13691110, 1, 8, []⟩, ⟨3, 13435438, 1, 8, []⟩, ⟨3, 12132466, 1, 8, []⟩,
  lm2M 3 13459731 1 8 1 [1], ⟨3, 12565759, 1, 8, []⟩, lm2M 4 8940701 1 8 2 [2],
  lm2M 4 5582054 1 7 2 [2], lm2M 4 8834367 1 7 2 [2], lm2M 4 8392288 1 7 1 [1],
  ⟨4, 7454529, 1, 7, []⟩, ⟨4, 8553136, 1, 7, []⟩, lm2M 4 8393345 1 7 3 [7],
  lm2M 4 6908451 1 7 2 [2], ⟨4, 5586091, 1, 7, []⟩, lm2M 4 5479481 1 7 3 [4],
  lm2M 4 10065363 1 8 3 [4], ⟨4, 4520778, 1, 6, []⟩, lm2M 4 5890894 1 7 3 [4],
  lm2M 4 5141097 1 6 4 [8], ⟨4, 1286608, 1, 5, []⟩ ]
private def lm2RowR5 : List ℕ := [
  116077, 2495827, 62733, 412255915602, 587741190026 ]
private def lm2SegsR6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 24462223, 1, 8, []⟩, ⟨1, 23780086, 1, 8, []⟩, ⟨1, 25569642, 1, 8, []⟩,
  ⟨1, 26779168, 1, 8, []⟩, ⟨2, 22215928, 1, 9, []⟩, ⟨2, 20779373, 1, 9, []⟩,
  ⟨2, 22340006, 1, 9, []⟩, ⟨3, 15857284, 1, 9, []⟩, ⟨3, 12081715, 1, 8, []⟩,
  ⟨3, 10525456, 1, 8, []⟩, ⟨3, 12001816, 1, 8, []⟩, ⟨3, 11151583, 1, 8, []⟩,
  lm2M 4 11728375 1 9 1 [1], ⟨4, 9741337, 1, 8, []⟩, lm2M 4 9253111 1 8 2 [3],
  lm2M 4 11828557 1 9 2 [2], lm2M 4 9237335 1 8 2 [2], lm2M 4 11140865 1 8 3 [4],
  lm2M 5 5813479 1 7 3 [4], lm2M 5 7476718 1 8 3 [4], ⟨5, 6078722, 1, 7, []⟩,
  lm2M 5 4300972 1 7 1 [1], lm2M 5 4274568 1 7 3 [5], lm2M 5 4877206 1 7 4 [8],
  lm2M 5 9156679 1 8 4 [10], lm2M 5 6371402 1 7 1 [1], lm2M 5 3393221 1 6 2 [3],
  lm2M 5 3768941 1 6 4 [8], lm2M 5 6674777 1 7 3 [7], lm2M 5 4359623 1 6 4 [15],
  lm2M 5 4905303 1 7 4 [8], lm2M 5 213374 1 4 3 [4] ]
private def lm2RowR6 : List ℕ := [
  39103, 131149, 51773, 282269437, 438163856804, 561553631460 ]
private def lm2SegsR7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 45822585, 1, 10, []⟩, ⟨1, 45822585, 1, 10, []⟩, ⟨2, 29435474, 1, 10, []⟩,
  ⟨2, 29435474, 1, 10, []⟩, ⟨3, 48626944, 1, 14, []⟩, lm2M 4 41905147 1 15 2 [3],
  lm2M 5 26312976 1 13 3 [5], lm2M 5 27985465 1 13 4 [10], lm2M 6 13742427 1 10 3 [7],
  lm2M 6 14385564 1 10 5 [27], lm2M 6 7131859 1 8 4 [12], lm2M 6 7253440 1 8 5 [28],
  lm2M 6 2578340 1 6 4 [13], lm2M 6 4386316 1 7 4 [9], lm2M 6 2962116 1 6 4 [11],
  ⟨6, 2909840, 1, 6, []⟩ ]
private def lm2RowR7 : List ℕ := [
  2149833, 111474, 596207, 3976614, 1331326914, 444716864210, 553944904597 ]
private def lm2SegsR8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 44228073, 1, 10, []⟩, ⟨1, 42024567, 1, 10, []⟩, ⟨2, 18737514, 1, 9, []⟩,
  ⟨2, 16287927, 1, 9, []⟩, ⟨2, 16145144, 1, 9, []⟩, ⟨3, 11163843, 1, 8, []⟩,
  ⟨3, 14405284, 1, 9, []⟩, ⟨3, 14615540, 1, 9, []⟩, ⟨4, 12062842, 1, 9, []⟩,
  ⟨4, 12075512, 1, 9, []⟩, lm2M 4 12112515 1 9 1 [1], lm2M 5 10500111 1 9 2 [3],
  lm2M 5 11283471 1 10 2 [2], lm2M 5 10406383 1 9 3 [7], ⟨6, 6058312, 1, 8, []⟩,
  ⟨6, 5821014, 1, 8, []⟩, lm2M 6 7136212 1 9 4 [8], lm2M 6 5669919 1 8 4 [9],
  lm2M 6 5722104 1 8 4 [11], ⟨6, 5878276, 1, 8, []⟩, lm2M 6 4400195 1 7 5 [18],
  lm2M 6 6733346 1 8 5 [18], lm2M 7 3324385 1 7 1 [1], lm2M 7 3205521 1 7 4 [14],
  lm2M 7 3611246 1 7 5 [19], lm2M 7 4259882 1 7 2 [3], lm2M 7 8293385 1 9 6 [55],
  lm2M 7 8888447 1 9 6 [60], lm2M 7 7621563 1 9 6 [60], lm2M 7 6182198 1 8 2 [2],
  lm2M 7 15072 1 4 6 [34], ⟨7, 487582, 1, 4, []⟩ ]
private def lm2RowR8 : List ℕ := [
  74736, 105314, 38515, 606, 3020310, 2515616975, 446933350600, 550547688014 ]
private def lm2SegsR9 : List DickeSol.Rkm128kSeg := [
  ⟨1, 40775368, 1, 10, []⟩, ⟨1, 40775368, 1, 10, []⟩, ⟨2, 23845282, 1, 10, []⟩,
  ⟨2, 23845282, 1, 10, []⟩, ⟨3, 40776605, 1, 14, []⟩, lm2M 4 39529990 1 15 2 [3],
  lm2M 5 22396755 1 13 3 [6], lm2M 6 21155321 1 13 4 [9], lm2M 7 20140352 1 14 5 [16],
  lm2M 7 15779498 1 12 5 [29], lm2M 7 4242899 1 8 6 [60], lm2M 8 10357350 1 11 6 [56],
  lm2M 8 3416862 1 7 6 [33], lm2M 8 8520373 1 10 7 [119], lm2M 8 10641790 1 11 7 [77],
  ⟨8, 8294132, 1, 9, []⟩ ]
private def lm2RowR9 : List ℕ := [
  129153, 7179634, 31081200, 10941247, 13542538, 1317030, 4114244484, 454347488477, 541474065000
  ]
private def lm2SegsR10 : List DickeSol.Rkm128kSeg := [
  ⟨1, 36327635, 1, 10, []⟩, ⟨1, 36327635, 1, 10, []⟩, ⟨2, 21102985, 1, 10, []⟩,
  ⟨2, 21102985, 1, 10, []⟩, ⟨3, 36682414, 1, 14, []⟩, ⟨4, 38084377, 1, 16, []⟩,
  lm2M 6 23150767 1 14 3 [7], lm2M 6 19038717 1 13 4 [10], lm2M 8 31169013 1 18 6 [55],
  lm2M 8 14492149 1 12 7 [125], lm2M 8 5230748 1 9 7 [126], lm2M 9 7703007 1 10 4 [14],
  lm2M 9 3024236 1 7 4 [10], lm2M 9 6748126 1 9 8 [247], lm2M 9 6535448 1 9 8 [241],
  ⟨9, 10923385, 1, 11, []⟩ ]
private def lm2RowR10 : List ℕ := [
  26300871, 77537359, 96093051, 14390486, 289061257, 758127644, 101659569, 6352867119,
  450575925092, 541705459887 ]
private def lm2SegsR11 : List DickeSol.Rkm128kSeg := [
  ⟨1, 31063361, 1, 9, []⟩, ⟨1, 31063361, 1, 9, []⟩, ⟨2, 21962979, 1, 10, []⟩,
  ⟨2, 21962979, 1, 10, []⟩, ⟨3, 34437736, 1, 14, []⟩, ⟨4, 30997992, 1, 15, []⟩,
  lm2M 5 16757038 1 12 2 [3], lm2M 6 14503512 1 12 3 [6], lm2M 7 14411310 1 13 4 [10],
  lm2M 7 14863104 1 13 5 [16], lm2M 9 27253780 1 18 7 [110], lm2M 9 21969371 1 16 9 [386],
  lm2M 10 3004880 1 8 9 [273], lm2M 10 10503354 1 11 4 [10], lm2M 10 6733512 1 10 6 [52],
  ⟨10, 7256476, 1, 10, []⟩ ]
private def lm2RowR11 : List ℕ := [
  527426, 177038, 605610, 7605366, 11473535, 41304855, 1424725729, 102981649, 11034482535,
  454818339605, 532556868819 ]
private def lm2SegsR12 : List DickeSol.Rkm128kSeg := [
  ⟨1, 30394605, 1, 9, []⟩, ⟨1, 30394605, 1, 9, []⟩, ⟨2, 19714052, 1, 10, []⟩,
  ⟨2, 19714052, 1, 10, []⟩, ⟨3, 30809613, 1, 14, []⟩, ⟨4, 28088858, 1, 14, []⟩,
  ⟨5, 17210853, 1, 13, []⟩, lm2M 6 15430011 1 13 13 [4102], lm2M 7 13221850 1 12 4 [10],
  lm2M 8 13755060 1 13 5 [25], lm2M 9 24696900 1 18 7 [111], lm2M 10 20185628 1 16 10 [591],
  lm2M 10 91765 1 4 10 [563], lm2M 10 9267315 1 12 9 [510], lm2M 11 13191398 1 13 7 [94],
  ⟨11, 10665196, 1, 12, []⟩ ]
private def lm2RowR12 : List ℕ := [
  322130, 11294021, 51907144, 422720, 11845174, 46408552, 1780027, 8306996461, 6429776609,
  24315940572, 509609835100, 451213452300 ]
private def lm2SegsR15 : List DickeSol.Rkm128kSeg := [
  ⟨1, 28772797, 1, 9, []⟩, ⟨1, 28772797, 1, 10, []⟩, ⟨2, 16700819, 1, 10, []⟩,
  ⟨2, 16700819, 1, 10, []⟩, ⟨3, 24817115, 1, 13, []⟩, ⟨4, 22079156, 1, 14, []⟩,
  ⟨5, 16164421, 1, 13, []⟩, lm2M 6 17329171 1 14 3 [5], lm2M 7 11260047 1 12 4 [15],
  lm2M 8 11351964 1 13 16 [32799], lm2M 10 18378388 1 17 7 [112],
  lm2M 11 19523583 1 18 13 [4517], lm2M 11 2000 1 4 13 [4114], lm2M 13 19844014 1 19 11 [1537],
  lm2M 13 14084794 1 16 12 [2217], ⟨14, 15876045, 1, 17, []⟩ ]
private def lm2RowR15 : List ℕ := [
  455774, 17268513, 169993, 26813220, 834177, 361560, 355066898, 18595188, 300897559,
  2240822799, 6694152326, 8158169437, 36877307549, 520974110540, 424334890843 ]
private def lm2SegsR16 : List DickeSol.Rkm128kSeg := [
  ⟨1, 27016682, 1, 9, []⟩, ⟨1, 27016682, 1, 9, []⟩, ⟨2, 15440527, 1, 10, []⟩,
  ⟨2, 15440527, 1, 10, []⟩, ⟨3, 23143623, 1, 13, []⟩, ⟨4, 20522001, 1, 14, []⟩,
  ⟨5, 15565031, 1, 13, []⟩, ⟨6, 17560768, 1, 14, []⟩, lm2M 8 11713781 1 13 16 [32783],
  lm2M 8 10809435 1 13 17 [65567], lm2M 10 17632752 1 17 17 [65641],
  lm2M 12 24960328 1 22 14 [9011], lm2M 12 1934 1 4 14 [8210], lm2M 14 18948493 1 20 12 [3096],
  lm2M 14 12607009 1 16 13 [4384], ⟨15, 14800359, 1, 17, []⟩ ]
private def lm2RowR16 : List ℕ := [
  2648471, 1610209, 7675105, 13307119, 156394591, 69005095, 51011467, 441194646, 162393161,
  1718314845, 3121239745, 6012318389, 7922846360, 37741183342, 517219793201, 425358442710 ]
private def lm2SegsR18 : List DickeSol.Rkm128kSeg := [
  ⟨1, 25088387, 1, 9, []⟩, ⟨1, 25088387, 1, 9, []⟩, ⟨2, 14500536, 1, 10, []⟩,
  ⟨2, 14500536, 1, 10, []⟩, ⟨3, 21200140, 1, 13, []⟩, ⟨4, 18359887, 1, 13, []⟩,
  ⟨5, 14295643, 1, 13, []⟩, lm2M 6 17004047 1 15 2 [2], lm2M 8 12688772 1 14 4 [11],
  lm2M 9 8514105 1 13 17 [65567], lm2M 10 15858497 1 17 7 [99],
  lm2M 12 22371712 1 22 16 [33593], lm2M 12 2000 1 4 16 [32786],
  lm2M 15 22183995 1 23 13 [6465], lm2M 16 10784645 1 16 14 [8957], ⟨16, 14861463, 1, 19, []⟩ ]
private def lm2RowR18 : List ℕ := [
  409852, 1953970, 17788761, 1824342, 37049234, 7969945, 97500209, 6255216, 28999309, 160543564,
  18038393, 1588622422, 13340182970, 2544412402, 264829057, 234221099225, 538695672878,
  208955500876 ]
private def lm2SegsR22 : List DickeSol.Rkm128kSeg := [
  ⟨1, 22230983, 1, 9, []⟩, ⟨1, 22230983, 1, 9, []⟩, ⟨2, 13281850, 1, 10, []⟩,
  ⟨2, 13281850, 1, 10, []⟩, ⟨3, 18583826, 1, 13, []⟩, ⟨4, 15072321, 1, 13, []⟩,
  ⟨5, 11936398, 1, 13, []⟩, ⟨6, 15224918, 1, 15, []⟩, lm2M 8 14047601 1 16 16 [32779],
  lm2M 9 7558525 1 13 17 [98335], lm2M 11 12631358 1 17 23 [4784228],
  lm2M 13 17306825 1 21 20 [525092], lm2M 14 337046 1 5 20 [524306],
  lm2M 15 16593416 1 22 13 [6624], lm2M 17 7835199 1 15 14 [8896], ⟨19, 25091131, 1, 30, []⟩ ]
private def lm2RowR22 : List ℕ := [
  12828099, 6574237, 285652, 2808372, 2765957, 8525606, 62789216, 103794036, 77858028,
  383798163, 72698830, 152098161, 4464628859, 501299040, 12123885021, 385837358, 18303387979,
  9653430337, 263654551558, 445430606951, 214545738180, 30048990365 ]
private def lm2SegsR25 : List DickeSol.Rkm128kSeg := [
  ⟨1, 15018322, 1, 8, []⟩, ⟨1, 15018322, 1, 8, []⟩, ⟨2, 13520364, 1, 10, []⟩,
  ⟨2, 13520364, 1, 10, []⟩, ⟨3, 20590029, 1, 14, []⟩, ⟨5, 16449605, 1, 15, []⟩,
  ⟨7, 23516196, 1, 20, []⟩, lm2M 10 19371278 1 21 5 [24], lm2M 12 13295962 1 19 24 [10486008],
  lm2M 15 9419281 1 17 25 [25164900], lm2M 18 25206034 1 32 16 [61149],
  lm2M 21 19913665 1 29 20 [844630], lm2M 23 9962558 1 20 22 [3127576],
  lm2M 23 1920235 1 10 22 [3962609], lm2M 24 5019095 1 14 16 [57423], ⟨24, 5091443, 1, 14, []⟩ ]
private def lm2RowR25 : List ℕ := [
  26323, 11288702, 122658, 2978285, 6592272, 23902364, 6076689, 139385579, 1151138, 51571223,
  295208139, 772393378, 572184168, 114976516, 2208521067, 516577521, 984010006, 120438,
  1633501582, 3489744327, 6549714912, 1832838897, 66548411336, 520504470165, 393733797030 ]
private def lm2SegsR29 : List DickeSol.Rkm128kSeg := [
  ⟨1, 14740104, 1, 8, []⟩, ⟨1, 14740104, 1, 8, []⟩, ⟨2, 11947971, 1, 10, []⟩,
  ⟨2, 11947971, 1, 10, []⟩, ⟨3, 19422135, 1, 14, []⟩, ⟨5, 16647225, 1, 16, []⟩,
  ⟨7, 20604241, 1, 20, []⟩, lm2M 10 17322176 1 21 5 [27], lm2M 13 11577012 1 19 8 [254],
  lm2M 15 8459266 1 17 30 [1023409380], lm2M 19 20978960 1 31 29 [268494507],
  lm2M 23 14772403 1 27 20 [879899], lm2M 25 11984215 1 25 26 [43778579],
  lm2M 25 2000 1 4 26 [49620229], lm2M 26 10249178 1 22 25 [29112840], ⟨27, 9910450, 1, 22, []⟩
  ]
private def lm2RowR29 : List ℕ := [
  421444, 5377076, 395535, 232381, 1225899, 2704031, 6052116, 25424687, 8707712, 115162335,
  67771905, 226386741, 26135298, 260728077, 24822945, 129026963, 813390006, 824798561,
  3776899429, 1257340963, 361473893, 1803011321, 1982766981, 8203343658, 3033971013, 65550540,
  190258642390, 535671254690, 251046951823 ]
private def lm2SegsR31 : List DickeSol.Rkm128kSeg := [
  lm2M 1 1459195 1 5 3 [4], lm2M 1 1459195 1 5 3 [4], ⟨1, 96800389, 1, 18, []⟩ ]
private def lm2RowR31 : List ℕ := [
  331860005404, 631906673256 ]
private def lm2SegsR34 : List DickeSol.Rkm128kSeg := [
  ⟨1, 109829203, 1, 20, []⟩ ]
private def lm2RowR34 : List ℕ := [
  161252180927, 833362504607 ]
private def lm2SegsR36 : List DickeSol.Rkm128kSeg := [
  ⟨1, 25819006, 1, 11, []⟩, ⟨2, 18989561, 1, 11, []⟩, ⟨3, 17076307, 1, 11, []⟩,
  ⟨5, 14300773, 1, 11, []⟩, ⟨7, 9028345, 1, 11, []⟩, ⟨7, 9028345, 1, 11, []⟩,
  ⟨10, 7771322, 1, 11, []⟩, ⟨10, 7771323, 1, 11, []⟩, lm2M 14 7411777 1 11 28 [134217776],
  lm2M 14 7411777 1 11 9 [272], lm2M 14 7411778 1 11 28 [134218752], ⟨20, 5545621, 1, 11, []⟩,
  ⟨20, 5545622, 1, 11, []⟩, lm2M 20 5545622 1 11 33 [4295098325], ⟨24, 4331010, 1, 11, []⟩,
  lm2M 24 4331011 1 11 34 [8590533738], ⟨27, 4022282, 1, 11, []⟩,
  lm2M 27 4022282 1 11 23 [7822986], ⟨30, 3648170, 1, 11, []⟩, ⟨30, 3648171, 1, 11, []⟩,
  lm2M 30 3648171 1 11 27 [84485746], ⟨32, 4253869, 1, 11, []⟩,
  lm2M 32 4253870 1 11 30 [611699346], lm2M 33 4529410 1 11 32 [3908647870],
  lm2M 33 842446 1 11 32 [2574330699], ⟨34, 3052221, 1, 11, []⟩,
  lm2M 34 3052222 1 11 30 [811691577], ⟨35, 3105523, 1, 11, []⟩, ⟨35, 3105523, 1, 11, []⟩ ]
private def lm2RowR36 : List ℕ := [
  21389935, 18292066, 12493160, 10650514, 2636405, 4758447, 9991923, 6207064, 12933772,
  10319521, 10865805, 71752864, 1174698, 28866443, 36077247, 10930760, 48300014, 51819941,
  392150690, 254034968, 635043711, 253367729, 104098675, 18191021, 1054363492, 426882,
  1388953729, 8330480284, 785364957, 3101129919, 1758644961, 7458133, 255064726, 134159778231,
  533159342199, 313101252445 ]
private def lm2SegsR40 : List DickeSol.Rkm128kSeg := [
  ⟨1, 98359788, 1, 19, []⟩ ]
private def lm2RowR40 : List ℕ := [
  194693613452, 796005165017 ]
private def lm2SegsR41 : List DickeSol.Rkm128kSeg := [
  ⟨1, 90070934, 1, 18, []⟩ ]
private def lm2RowR41 : List ℕ := [
  285073189341, 689553278578 ]
private def lm2SegsR43 : List DickeSol.Rkm128kSeg := [
  ⟨1, 89361892, 1, 19, []⟩ ]
private def lm2RowR43 : List ℕ := [
  266048504707, 712694913001 ]
private def lm2SegsR46 : List DickeSol.Rkm128kSeg := [
  ⟨1, 94240391, 1, 20, []⟩ ]
private def lm2RowR46 : List ℕ := [
  160619762502, 833455192396 ]
private def lm2SegsR47 : List DickeSol.Rkm128kSeg := [
  ⟨1, 21251377, 1, 10, []⟩, ⟨2, 16012020, 1, 12, []⟩, ⟨3, 14804848, 1, 14, []⟩,
  ⟨5, 13179095, 1, 16, []⟩, ⟨7, 15393007, 1, 19, []⟩, ⟨10, 14735203, 1, 22, []⟩,
  lm2M 15 20201042 1 33 12 [3641], lm2M 24 16220078 1 37 45 [17901424622802],
  lm2M 32 13954103 2 25 46 [39582584948914], lm2M 36 5757880 1 24 47 [70370866203996],
  lm2M 40 13454415 2 27 38 [206108330687], lm2M 43 5401251 1 24 41 [1110080670864],
  lm2M 43 639160 1 9 43 [6242262168264], lm2M 43 2000 1 4 43 [4766271521522],
  lm2M 44 7949950 1 31 42 [3354270528941], ⟨45, 4843476, 1, 23, []⟩ ]
private def lm2RowR47 : List ℕ := [
  63650, 16826, 73337, 1231117, 62909, 6613496, 4106700, 2145995, 463301, 4798281, 7348909,
  35876536, 24975343, 9283935, 1400456, 58318375, 16233758, 15760043, 92994203, 609846156,
  207995697, 75723154, 8732066, 133675436, 5129344, 15057259, 529562069, 318984694, 3903676186,
  622058258, 985612845, 90138166, 1487893590, 1835823864, 62155252, 599066232, 19956685,
  788854773, 98715203, 407623850, 1419532317, 1881336242, 20155943819, 15969346, 205193743290,
  518728981705, 239516413881 ]
private def lm2SegsR49 : List DickeSol.Rkm128kSeg := [
  ⟨1, 82422921, 1, 19, []⟩ ]
private def lm2RowR49 : List ℕ := [
  282892944689, 691581092478 ]
private def lm2SegsR51 : List DickeSol.Rkm128kSeg := [
  ⟨1, 82181390, 1, 19, []⟩ ]
private def lm2RowR51 : List ℕ := [
  262652529168, 716245250161 ]
private def lm2SegsR54 : List DickeSol.Rkm128kSeg := [
  ⟨1, 86964601, 1, 20, []⟩ ]
private def lm2RowR54 : List ℕ := [
  159597809657, 834315971931 ]
private def lm2SegsR56 : List DickeSol.Rkm128kSeg := [
  ⟨1, 83079199, 1, 19, []⟩ ]
private def lm2RowR56 : List ℕ := [
  192531437397, 797713222000 ]
private def lm2SegsR58 : List DickeSol.Rkm128kSeg := [
  ⟨1, 80296961, 1, 19, []⟩ ]
private def lm2RowR58 : List ℕ := [
  212330193306, 775151906304 ]
private def lm2SegsR59 : List DickeSol.Rkm128kSeg := [
  ⟨1, 76550144, 1, 19, []⟩ ]
private def lm2RowR59 : List ℕ := [
  259301726581, 719888999480 ]
private def lm2SegsR61 : List DickeSol.Rkm128kSeg := [
  ⟨1, 75832029, 1, 19, []⟩ ]
private def lm2RowR61 : List ℕ := [
  250480854367, 730399651345 ]
private def lm2SegsR66 : List DickeSol.Rkm128kSeg := [
  ⟨1, 79097199, 1, 20, []⟩ ]
private def lm2RowR66 : List ℕ := [
  151770108934, 842599857008 ]
private def lm2SegsR68 : List DickeSol.Rkm128kSeg := [
  ⟨1, 75380655, 1, 19, []⟩ ]
private def lm2RowR68 : List ℕ := [
  191464280573, 798592492994 ]
private def lm2SegsR70 : List DickeSol.Rkm128kSeg := [
  ⟨1, 73113042, 1, 19, []⟩ ]
private def lm2RowR70 : List ℕ := [
  210747308601, 776624816552 ]
private def lm2SegsR72 : List DickeSol.Rkm128kSeg := [
  ⟨1, 71360213, 1, 19, []⟩ ]
private def lm2RowR72 : List ℕ := [
  222897525203, 762550786695 ]
private def lm2SegsR74 : List DickeSol.Rkm128kSeg := [
  ⟨1, 70061226, 1, 19, []⟩ ]
private def lm2RowR74 : List ℕ := [
  228373825677, 756123192208 ]
private def lm2SegsR76 : List DickeSol.Rkm128kSeg := [
  ⟨1, 68896926, 1, 19, []⟩ ]
private def lm2RowR76 : List ℕ := [
  232343780487, 751427806979 ]
private def lm2SegsR78 : List DickeSol.Rkm128kSeg := [
  ⟨1, 67922010, 1, 19, []⟩ ]
private def lm2RowR78 : List ℕ := [
  233720077644, 749766399992 ]
private def lm2SegsR80 : List DickeSol.Rkm128kSeg := [
  ⟨1, 67074612, 1, 19, []⟩ ]
private def lm2RowR80 : List ℕ := [
  233460282881, 750029066977 ]
private def lm2SegsR82 : List DickeSol.Rkm128kSeg := [
  ⟨1, 66267328, 1, 19, []⟩ ]
private def lm2RowR82 : List ℕ := [
  233047087125, 750474108893 ]
private def lm2SegsR84 : List DickeSol.Rkm128kSeg := [
  ⟨1, 65473682, 1, 19, []⟩ ]
private def lm2RowR84 : List ℕ := [
  232925322700, 750578555801 ]
private def lm2SegsR86 : List DickeSol.Rkm128kSeg := [
  ⟨1, 64707880, 1, 19, []⟩ ]
private def lm2RowR86 : List ℕ := [
  232809350669, 750677992898 ]
private def lm2SegsR88 : List DickeSol.Rkm128kSeg := [
  ⟨1, 63968340, 1, 19, []⟩ ]
private def lm2RowR88 : List ℕ := [
  232698604575, 750772963372 ]
private def lm2SegsR90 : List DickeSol.Rkm128kSeg := [
  ⟨1, 63253588, 1, 19, []⟩ ]
private def lm2RowR90 : List ℕ := [
  232592857745, 750863621947 ]
private def lm2SegsR92 : List DickeSol.Rkm128kSeg := [
  ⟨1, 66176150, 1, 19, []⟩ ]
private def lm2RowR92 : List ℕ := [
  164770002801, 827992577853 ]
private def lm2SegsR122 : List DickeSol.Rkm128kSeg := [
  ⟨1, 57419883, 1, 19, []⟩ ]
private def lm2RowR122 : List ℕ := [
  164718183386, 827816159688 ]
private def lm2R256C0 : List DickeSol.Rkm128kSeg := [
  ⟨2, 9352201, 1, 13, []⟩, ⟨4, 6127824, 1, 14, []⟩, ⟨9, 8075781, 1, 24, []⟩,
  ⟨14, 6510559, 1, 26, []⟩, lm2M 20 4456260 1 25 1 [1], lm2M 25 3736501 1 25 6 [57],
  lm2M 30 2411460 1 20 9 [297], lm2M 35 2156795 1 21 14 [14336],
  lm2M 40 1936818 1 20 21 [2060254], lm2M 47 2107482 1 24 27 [119382530],
  lm2M 52 1970122 1 25 34 [15947794714],
  lm2M 58 1821666 1 27 106 [2000710371024, 562949953421312],
  lm2M 63 1703760 1 28 87 [127481231290400, 1073741824],
  lm2M 69 1660401 1 29 137 [16013454860481377, 0, 16777218],
  lm2M 75 1545880 1 29 60 [66745940393517644, 15],
  lm2M 81 1443989 1 30 116 [42924553581837154, 562949953423305, 8],
  lm2M 88 1326442 1 30 176 [29377573962039869, 115160, 4398181253120, 144] ]
private def lm2R256C1 : List DickeSol.Rkm128kSeg := [
  lm2M 95 1273922 1 30 189 [10154045762568598, 6444132, 35184372088864, 1458176],
  lm2M 101 1221058 1 31 201 [36167622736618110, 920917641, 562950490292224, 5435885568],
  lm2M 106 1167582 1 30 213 [27340962067986746, 56530851755, 32768, 26265214271488],
  lm2M 113 1109388 1 30 227 [12524401805821468, 2233410610669, 0, 21660481344246016, 6],
  lm2M 119 1061703 1 30 236 [
    953636710520625, 205781665329497, 1099511627776, 24413890116845568, 3098],
  lm2M 125 1019857 1 31 250 [40005202514593823, 9195305954313280, 0, 4029555229720640, 51275472]
  ]
private def lm2R256C2 : List DickeSol.Rkm128kSeg := [
  lm2M 130 985300 1 30 254 [
    1164083330594206, 3028547879800630, 9, 44631653020073984, 971338150],
  lm2M 136 960679 1 31 255 [
    23445685675301824, 40673418684744010, 576, 38845762989211648, 2114723961],
  lm2M 141 928090 1 30 257 [
    45884957769070091, 14148894725265511, 70368744214696, 34359739392, 6284245760],
  lm2M 147 890725 1 30 257 [
    33407606374695881, 52354924449172536, 2138240, 4503600701112320, 5737807872],
  lm2M 152 845626 1 29 255 [
    19568027999681376, 41131772274852652, 2687264, 281474976710656, 1375993856]
  ]
private def lm2R256C3 : List DickeSol.Rkm128kSeg := [
  lm2M 157 822252 1 30 257 [
    2271631505326042, 316947536407090, 4462739654, 2269529572900864, 7591690242],
  lm2M 162 790576 1 29 257 [
    8030860008789964, 1125979272791084, 5972689304, 9008307364691968, 5646074376],
  lm2M 166 769009 1 29 257 [
    3365657682230234, 32635991416890678, 8529284435513, 36028868154359808, 5452730400],
  lm2M 171 906013 1 33 251 [
    9124831379375744, 159279948116041, 13194171304152, 1103940812800, 71311492],
  lm2M 178 870426 1 33 256 [
    14090150379912689, 39753532562361904, 9156732912194560, 268435456, 2164296736]
  ]
private def lm2R256C4 : List DickeSol.Rkm128kSeg := [
  lm2M 183 852541 1 32 254 [
    40291751935360897, 1130402685164036, 351937186759457, 12, 575668224],
  lm2M 188 832592 1 32 256 [47726065622974513, 296202973905723, 74822675615761, 2, 2156921344],
  lm2M 193 815631 1 32 256 [
    24927679530538125, 916202533276710, 12236364977026, 9007199254761473, 2703556608],
  lm2M 200 761174 1 31 257 [
    32971126047552843, 37587080645336122, 2287190344225125, 0, 4463346177],
  lm2M 204 773162 1 32 257 [
    14814886847503362, 24182398432176793, 9114963976163337, 0, 5001187332]
  ]
private def lm2R256C5 : List DickeSol.Rkm128kSeg := [
  lm2M 209 766425 1 32 257 [
    15769932648300558, 1127553473553065, 45071473039183985, 67371280, 5371072768],
  lm2M 212 758163 1 31 255 [
    41377072939676943, 780653662584068, 18033090355014088, 19456, 1342242824],
  lm2M 216 745419 1 32 257 [
    55315142604032203, 8180403129140113, 93467413872704, 134259846, 7513964466],
  lm2M 220 732384 1 32 257 [
    27944911798278120, 12948058936484148, 41680288967266896, 549890591746, 7247756032],
  lm2M 222 731025 1 32 254 [
    62178750709876140, 18129041463280143, 335276410117, 540688, 873463808]
  ]
private def lm2R256C6 : List DickeSol.Rkm128kSeg := [
  lm2M 225 715690 1 32 256 [
    18107054719373262, 18024987080278230, 3379246445804578, 8590721028, 2214592512],
  lm2M 226 713058 1 32 256 [
    18895706567903384, 19874275180746596, 897450581047023, 33901117477777548, 2147581952],
  lm2M 232 643871 1 29 257 [
    36362726565175007, 6782893692591313, 36314740172029962, 4949077399042, 4580311040],
  lm2M 235 643311 1 29 257 [
    26543466957905156, 79595190641890, 46232303584936960, 19929185174336, 4564451328],
  lm2M 236 638413 1 29 257 [
    41676727932297845, 18055641473794114, 73291932910016, 10775772619094020, 4294967296]
  ]
private def lm2R256C7 : List DickeSol.Rkm128kSeg := [
  lm2M 239 620369 1 29 257 [
    49669447399593056, 9658251447112880, 24785835963588650, 2289458360614915, 5502926848],
  lm2M 242 626315 1 29 255 [
    58523670521386418, 54096593573578947, 37296270993002737, 9095297640828928, 1073748032],
  lm2M 244 608695 1 28 217 [
    46115886651960765, 1003876263380035, 54140261823086640, 282041912393932],
  lm2M 246 593120 1 28 220 [
    31943183978520385, 24911935635307524, 1134696548778368, 3377699721125896],
  lm2M 246 595074 1 28 238 [
    11622391153670199, 6832093755081755, 9605334128451642, 2200140034049, 8192]
  ]
private def lm2R256C8 : List DickeSol.Rkm128kSeg := [
  lm2M 249 592319 1 28 201 [36080310953386264, 3035141324671272, 562951171343182, 4447011841],
  lm2M 249 589215 1 28 247 [
    1248717469171692, 21676540499689257, 11199009305902621, 4545694016940, 6494353],
  lm2M 250 622646 1 29 222 [
    4574815562241676, 18230457390358593, 20364055948674114, 9007199388958848],
  lm2M 250 616982 1 28 236 [
    17882186491313777, 15193634513057826, 40262054769559792, 54061131592896528, 2048],
  lm2M 250 613794 1 28 221 [
    1559960190322193, 19032570063749351, 1407375219167513, 4582835742572800],
  lm2M 250 616231 1 28 233 [
    14120551807746708, 51937444482366168, 1307320088855201, 844427078140928, 320]
  ]
private def lm2SegsR256 : List DickeSol.Rkm128kSeg :=
  lm2R256C0 ++ (lm2R256C1 ++ (lm2R256C2 ++ (lm2R256C3 ++
    (lm2R256C4 ++ (lm2R256C5 ++ (lm2R256C6 ++ (lm2R256C7 ++ lm2R256C8)))))))
private def lm2RowR256P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 3, 1, 0, 3, 3, 3, 7, 4, 24, 10, 2, 3,
  2, 16, 44, 26, 2, 12, 83, 249, 1, 27, 23, 3, 146, 8, 7, 80, 163 ]
private def lm2RowR256P1 : List ℕ := [
  87, 139, 251, 191, 17, 292, 824, 21, 32, 920, 905, 129, 26, 731, 70, 5, 1699, 1530, 222, 2135,
  969, 118, 2719, 4, 1789, 1535, 2557, 428, 4622, 441, 10013, 534, 299, 1678, 970, 3055, 684,
  454, 378, 5663, 8535, 302, 1038, 3213, 6962, 2471, 36, 1118 ]
private def lm2RowR256P2 : List ℕ := [
  4968, 2216, 26535, 13947, 1009, 4334, 610, 14145, 2954, 48, 7666, 692, 538, 357, 5602, 17122,
  31752, 10370, 7823, 47136, 2119, 51884, 101853, 4024, 5, 601, 208107, 189836, 10036, 72260,
  2895, 241885, 38356, 105677, 436677, 39588, 1046, 68054, 23835, 87774, 2351, 31777, 16694,
  491867, 17069, 211101, 537979, 239769 ]
private def lm2RowR256P3 : List ℕ := [
  233363, 305635, 334480, 3070240, 1485016, 1113651, 366846, 1487744, 1017990, 399709, 711896,
  6141133, 383463, 22273, 193, 2640879, 4640532, 404438, 8138729, 4961594, 13655712, 3865551,
  1210524, 6213805, 4552705, 30134076, 7796366, 198546, 189156, 10574025, 59651057, 22263190,
  373976, 1886754, 4617712, 7587058, 13766704, 5460078, 13946245, 41649840, 32997587, 87557127,
  32030362, 8805714, 8000986, 22084, 1737078, 99528213 ]
private def lm2RowR256P4 : List ℕ := [
  9873762, 28408459, 19031699, 3397945, 242665098, 22916765, 6557802, 17126873, 62286667,
  3018503, 10395142, 344488897, 47725200, 5255278, 391270733, 138355745, 641522093, 100483834,
  74786565, 159466453, 25708721, 174516590, 803642085, 1189464, 4060387, 298215421, 126461073,
  850488899, 170833521, 146007132, 353308196, 125732501, 186114990, 289189633, 188464606,
  128915542, 343018219, 18067589, 529976499, 3732053, 259575390, 36087306, 120859206, 55820041,
  976712257, 951156513, 620032800, 4617217657 ]
private def lm2RowR256P5 : List ℕ := [
  1111926284, 170281322, 167603149, 912796489, 3296304664, 582163353, 990345161, 2306642356,
  24971156402, 6320796883, 5490601735, 198892570, 132102136626, 402406550150, 325182666089,
  78492882673 ]
private def lm2RowR256 : List ℕ :=
  lm2RowR256P0 ++ (lm2RowR256P1 ++ (lm2RowR256P2 ++
    (lm2RowR256P3 ++ (lm2RowR256P4 ++ lm2RowR256P5))))
private def lm2R256V1P0 : List ℤ := [
  Int.ofNat 16274108620, Int.ofNat 5664502132, Int.ofNat 6833668097, Int.ofNat 12329918816,
  Int.ofNat 59278353010, Int.ofNat 41497081658, Int.ofNat 39394583125, Int.ofNat 105305125323,
  Int.ofNat 98703678192, Int.negSucc 38745244152, Int.negSucc 52000160144,
  Int.negSucc 61529958098, Int.ofNat 34858834909, Int.negSucc 19387402729,
  Int.negSucc 33209830208, Int.negSucc 32357807971, Int.negSucc 35806767896,
  Int.ofNat 54564554970, Int.negSucc 44233380701, Int.ofNat 130643040630, Int.ofNat 43672108257,
  Int.negSucc 198679012215, Int.negSucc 332294522250, Int.negSucc 321033998373,
  Int.negSucc 251472951227, Int.negSucc 52681596660, Int.negSucc 241409837217,
  Int.ofNat 500407571692, Int.ofNat 311689173073, Int.ofNat 347511748326,
  Int.negSucc 81288113962, Int.negSucc 134419216530, Int.negSucc 1191109912329,
  Int.negSucc 1015438008090, Int.negSucc 500503767352, Int.ofNat 95995219904,
  Int.ofNat 1259961439624, Int.negSucc 2416383433529, Int.negSucc 1071299906259,
  Int.ofNat 325990793147, Int.negSucc 422080388545, Int.negSucc 344045052869,
  Int.ofNat 963094089002, Int.ofNat 1111290541938, Int.negSucc 221330365277,
  Int.ofNat 3248387277, Int.negSucc 210435953415, Int.negSucc 2529543238065 ]
private def lm2R256V1P1 : List ℤ := [
  Int.ofNat 1138408721424, Int.ofNat 1361432494922, Int.ofNat 1387671203528,
  Int.ofNat 1177502317538, Int.ofNat 523701748935, Int.negSucc 37993906845,
  Int.ofNat 437747905359, Int.ofNat 2456050672264, Int.ofNat 617867214047,
  Int.ofNat 2394131885098, Int.ofNat 3490647836930, Int.ofNat 2554209930764,
  Int.ofNat 5822021630504, Int.ofNat 3404641212779, Int.negSucc 4516370387610,
  Int.negSucc 2068375854853, Int.negSucc 3657744250282, Int.negSucc 754900939753,
  Int.negSucc 7607277977090, Int.negSucc 5800220185046, Int.ofNat 1756656995077,
  Int.ofNat 4573963528961, Int.ofNat 391986072291, Int.ofNat 6802155552188,
  Int.ofNat 5464018715102, Int.ofNat 10408621670426, Int.ofNat 43472794798943,
  Int.ofNat 92354039868693, Int.ofNat 152299281457849, Int.ofNat 216180421894581,
  Int.ofNat 275878684773795, Int.ofNat 323858905270732, Int.ofNat 354566523538255,
  Int.ofNat 365304800290191, Int.ofNat 356422365162112, Int.ofNat 330854849572935,
  Int.ofNat 293230505041593, Int.ofNat 248822351332388, Int.ofNat 202606813377944,
  Int.ofNat 158601053041302, Int.ofNat 119541009530463, Int.ofNat 86867169058112,
  Int.ofNat 60927022430586, Int.ofNat 41285874304308, Int.ofNat 27051899022888,
  Int.ofNat 17152249886115, Int.ofNat 10530663416250, Int.ofNat 6264022542273 ]
private def lm2R256V1P2 : List ℤ := [
  Int.ofNat 3611913935431, Int.ofNat 2019790099972, Int.ofNat 1095821347491,
  Int.ofNat 577013827495, Int.ofNat 295002078735, Int.ofNat 146447145276, Int.ofNat 70643212234,
  Int.ofNat 33106839464, Int.ofNat 15063432036, Int.ofNat 6669884915, Int.ofNat 2880407019,
  Int.ofNat 1204779726, Int.ofNat 480117563, Int.ofNat 179654545, Int.ofNat 63060235,
  Int.ofNat 21132080, Int.ofNat 6981823, Int.ofNat 2346137, Int.ofNat 810049, Int.ofNat 283214,
  Int.ofNat 97849, Int.ofNat 32717, Int.ofNat 10437, Int.ofNat 3141, Int.ofNat 883,
  Int.ofNat 232, Int.ofNat 53, Int.ofNat 11, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V1P3 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V1 : List ℤ :=
  lm2R256V1P0 ++ (lm2R256V1P1 ++ (lm2R256V1P2 ++ lm2R256V1P3))
private def lm2R256V2P0 : List ℤ := [
  Int.ofNat 5012586552, Int.ofNat 3955871306, Int.negSucc 2570143387, Int.negSucc 17761764927,
  Int.negSucc 9870287517, Int.negSucc 6507092890, Int.ofNat 14061057312, Int.ofNat 14688715027,
  Int.negSucc 10797034121, Int.ofNat 8117603099, Int.ofNat 4246767528, Int.negSucc 2502303129,
  Int.ofNat 8021907565, Int.ofNat 31708312955, Int.ofNat 32443909632, Int.ofNat 93497477881,
  Int.negSucc 18711801949, Int.negSucc 95355802668, Int.negSucc 206178655388,
  Int.negSucc 11038741938, Int.ofNat 79369077163, Int.ofNat 116146913107, Int.ofNat 74839315931,
  Int.ofNat 6542276569, Int.negSucc 281022788840, Int.ofNat 214407139708,
  Int.negSucc 118471065452, Int.negSucc 11808613763, Int.negSucc 197904023915,
  Int.negSucc 728360580351, Int.ofNat 249904385608, Int.negSucc 88003011533,
  Int.negSucc 784532028073, Int.negSucc 472249269820, Int.ofNat 144083801280,
  Int.negSucc 175449504780, Int.ofNat 10619706729, Int.negSucc 578468690277,
  Int.ofNat 146132112515, Int.negSucc 416980916498, Int.negSucc 371991791126,
  Int.ofNat 794285966978, Int.negSucc 431967112438, Int.negSucc 448554365985,
  Int.ofNat 398434269721, Int.negSucc 50462673800, Int.ofNat 290316753143,
  Int.negSucc 996550101409 ]
private def lm2R256V2P1 : List ℤ := [
  Int.ofNat 8734822943, Int.negSucc 175817222044, Int.negSucc 815290234474,
  Int.negSucc 12491875028, Int.negSucc 895434040784, Int.negSucc 1047531741923,
  Int.ofNat 1457736915408, Int.negSucc 346687056876, Int.negSucc 273946707517,
  Int.negSucc 858116129879, Int.negSucc 2689540923678, Int.negSucc 3521371533070,
  Int.negSucc 1726267424008, Int.ofNat 1942983220662, Int.negSucc 1118321343840,
  Int.negSucc 2012347634894, Int.ofNat 4094356435738, Int.ofNat 4703115255989,
  Int.negSucc 4473842743, Int.negSucc 1720459726664, Int.ofNat 829063549271,
  Int.negSucc 1158691969897, Int.negSucc 1599048730489, Int.negSucc 3886395681394,
  Int.ofNat 4515399321021, Int.ofNat 4597763192921, Int.negSucc 419476378127,
  Int.negSucc 7245423699458, Int.ofNat 4158504154466, Int.ofNat 129215074368,
  Int.negSucc 2493969884122, Int.negSucc 4100933801162, Int.negSucc 2496881917657,
  Int.ofNat 1352743039632, Int.ofNat 6831188516395, Int.ofNat 4958289319186,
  Int.negSucc 9617311800232, Int.negSucc 6093143958490, Int.negSucc 3686496184205,
  Int.ofNat 4139936718023, Int.ofNat 4374814084771, Int.negSucc 2880617014454,
  Int.negSucc 4149222169061, Int.negSucc 4434396603700, Int.ofNat 3080952545431,
  Int.ofNat 13068556822883, Int.ofNat 9945341198603, Int.ofNat 7570925279256 ]
private def lm2R256V2P2 : List ℤ := [
  Int.ofNat 9553625684866, Int.negSucc 3773615345793, Int.negSucc 12630612540975,
  Int.negSucc 2835355393152, Int.ofNat 24955844796, Int.ofNat 4430335989754,
  Int.ofNat 2835272620540, Int.negSucc 1003725473756, Int.negSucc 4718992093600,
  Int.negSucc 2056564934416, Int.ofNat 2136395981412, Int.negSucc 1983464028715,
  Int.negSucc 11167577141804, Int.ofNat 13241362862662, Int.ofNat 2460937547445,
  Int.ofNat 39793964782578, Int.ofNat 95816944644587, Int.ofNat 162964009640093,
  Int.ofNat 231575884610028, Int.ofNat 292167075392034, Int.ofNat 337212267080976,
  Int.ofNat 362247555436011, Int.ofNat 366189783243747, Int.ofNat 350964113241207,
  Int.ofNat 320641082889435, Int.ofNat 280369064417177, Int.ofNat 235372259617480,
  Int.ofNat 190185669731505, Int.ofNat 148209256786917, Int.ofNat 111576721466029,
  Int.ofNat 81261771927602, Int.ofNat 57323872141732, Int.ofNat 39207084162396,
  Int.ofNat 26023091758794, Int.ofNat 16775161092927, Int.ofNat 10509870771267,
  Int.ofNat 6403331169773, Int.ofNat 3795771275481, Int.ofNat 2190215063708,
  Int.ofNat 1230894092881, Int.ofNat 674188733237, Int.ofNat 360039066336,
  Int.ofNat 187427283043, Int.ofNat 95007109065, Int.ofNat 46806616519, Int.ofNat 22363563461,
  Int.ofNat 10343399464, Int.ofNat 4626933505 ]
private def lm2R256V2P3 : List ℤ := [
  Int.ofNat 2002773169, Int.ofNat 840439900, Int.ofNat 342994972, Int.ofNat 136674853,
  Int.ofNat 53387143, Int.ofNat 20513788, Int.ofNat 7768110, Int.ofNat 2899929,
  Int.ofNat 1067815, Int.ofNat 387290, Int.ofNat 137135, Int.ofNat 46656, Int.ofNat 15043,
  Int.ofNat 4586, Int.ofNat 1334, Int.ofNat 378, Int.ofNat 105, Int.ofNat 27, Int.ofNat 6,
  Int.negSucc 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0 ]
private def lm2R256V2P4 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V2P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V2 : List ℤ :=
  lm2R256V2P0 ++ (lm2R256V2P1 ++ (lm2R256V2P2 ++
    (lm2R256V2P3 ++ (lm2R256V2P4 ++ lm2R256V2P5))))
private def lm2R256V3P0 : List ℤ := [
  Int.negSucc 1846739826, Int.negSucc 4549748566, Int.negSucc 1458440209,
  Int.negSucc 7473044182, Int.ofNat 3256440336, Int.ofNat 10996251096, Int.ofNat 7242910085,
  Int.negSucc 1206589471, Int.negSucc 14612063000, Int.negSucc 11012547152,
  Int.negSucc 4488481447, Int.ofNat 1121731225, Int.ofNat 23020592397, Int.ofNat 20513489557,
  Int.negSucc 1672646366, Int.ofNat 3668833246, Int.negSucc 1786003149, Int.negSucc 28850951339,
  Int.ofNat 10002390930, Int.ofNat 54254219365, Int.ofNat 40049016789, Int.ofNat 308231235,
  Int.ofNat 60420577769, Int.negSucc 75205146212, Int.ofNat 96029061029,
  Int.negSucc 14755722083, Int.ofNat 40185699729, Int.ofNat 20734852370, Int.ofNat 51681494073,
  Int.ofNat 199564281113, Int.ofNat 189125620121, Int.ofNat 244572622575,
  Int.ofNat 554045330455, Int.ofNat 534695490961, Int.ofNat 481645916638, Int.ofNat 57028452787,
  Int.negSucc 642060624972, Int.negSucc 1441347875, Int.ofNat 836687151378,
  Int.ofNat 368867380434, Int.negSucc 46737316961, Int.negSucc 1154880690762,
  Int.negSucc 396971310805, Int.negSucc 162768035530, Int.negSucc 161397239371,
  Int.ofNat 91203889484, Int.negSucc 387835406004, Int.ofNat 485579479838 ]
private def lm2R256V3P1 : List ℤ := [
  Int.ofNat 17478318338, Int.ofNat 186814480542, Int.ofNat 429924424141, Int.ofNat 504387572089,
  Int.ofNat 1057134079144, Int.negSucc 136526178438, Int.negSucc 223971177648,
  Int.ofNat 672741933644, Int.negSucc 129070968429, Int.negSucc 891393705504,
  Int.negSucc 1353008667859, Int.negSucc 654038292992, Int.ofNat 672064062399,
  Int.ofNat 80862826362, Int.ofNat 1310832332970, Int.negSucc 1097770456744,
  Int.negSucc 1527054375691, Int.ofNat 633288914370, Int.ofNat 1781222938323,
  Int.negSucc 851264198572, Int.negSucc 2195007985728, Int.negSucc 1408064446256,
  Int.negSucc 128231380689, Int.negSucc 328996778187, Int.ofNat 341278220924,
  Int.ofNat 1284201412519, Int.ofNat 710462018623, Int.negSucc 2143054421501,
  Int.negSucc 790752380429, Int.negSucc 2004751859577, Int.ofNat 1248329250321,
  Int.negSucc 2009436028727, Int.ofNat 4476080527125, Int.negSucc 577856296268,
  Int.negSucc 2873923368720, Int.negSucc 2626300846905, Int.negSucc 3969740040812,
  Int.negSucc 5125840948036, Int.negSucc 7503546647678, Int.negSucc 9088487421556,
  Int.negSucc 1672839438739, Int.ofNat 8480033674561, Int.ofNat 6791735570067,
  Int.ofNat 4444391254279, Int.ofNat 6557229565434, Int.ofNat 4992028044903,
  Int.negSucc 3341428742483, Int.ofNat 131943835477 ]
private def lm2R256V3P2 : List ℤ := [
  Int.negSucc 643633885671, Int.ofNat 5015482632359, Int.ofNat 5838660101702,
  Int.negSucc 1468004600345, Int.negSucc 7565699498540, Int.negSucc 4964591265970,
  Int.ofNat 5790298116632, Int.ofNat 4873125917446, Int.ofNat 447508155675,
  Int.negSucc 3239783969239, Int.negSucc 5405077435659, Int.ofNat 3117164934444,
  Int.negSucc 150942509258, Int.negSucc 8933122451167, Int.negSucc 5219961550766,
  Int.ofNat 2177410763623, Int.negSucc 3605624135900, Int.negSucc 2087310036707,
  Int.ofNat 3090552360771, Int.negSucc 4807553310487, Int.negSucc 11170638505963,
  Int.negSucc 2342977633075, Int.negSucc 22930008226301, Int.negSucc 6661541487724,
  Int.negSucc 6647009593984, Int.ofNat 9576738176151, Int.ofNat 19298145507915,
  Int.ofNat 15277949697402, Int.ofNat 2274748889621, Int.negSucc 5681377735258,
  Int.negSucc 10826331533008, Int.negSucc 4851060095398, Int.ofNat 7800464552389,
  Int.ofNat 10052327543186, Int.ofNat 1614790799186, Int.ofNat 2723028071655,
  Int.ofNat 3024490305817, Int.negSucc 2342013831549, Int.negSucc 1243106365972,
  Int.negSucc 4723443727887, Int.negSucc 12064712192290, Int.negSucc 20185116856910,
  Int.negSucc 17489097053472, Int.ofNat 6493923365383, Int.ofNat 54365725622225,
  Int.ofNat 120643424502558, Int.ofNat 194930237220946, Int.ofNat 265556155881850 ]
private def lm2R256V3P3 : List ℤ := [
  Int.ofNat 322450422239907, Int.ofNat 358944550779570, Int.ofNat 372395018399175,
  Int.ofNat 363975722565168, Int.ofNat 337555850807746, Int.ofNat 298723494007652,
  Int.ofNat 253163267423867, Int.ofNat 206205814704275, Int.ofNat 161771774575993,
  Int.ofNat 122474512086734, Int.ofNat 89682598770505, Int.ofNat 63568424307395,
  Int.ofNat 43653792082923, Int.ofNat 29108869710818, Int.ofNat 18862990642755,
  Int.ofNat 11862134521322, Int.ofNat 7243984162499, Int.ofNat 4316851669643,
  Int.ofNat 2518960357525, Int.ofNat 1431869647907, Int.ofNat 782734482045,
  Int.ofNat 406434094980, Int.ofNat 199705045273, Int.ofNat 93640852514, Int.ofNat 42727664372,
  Int.ofNat 19437315792, Int.ofNat 8971615386, Int.ofNat 4209276627, Int.ofNat 1982977190,
  Int.ofNat 922426377, Int.ofNat 418127309, Int.ofNat 183350144, Int.ofNat 77588075,
  Int.ofNat 31701693, Int.ofNat 12531010, Int.ofNat 4803151, Int.ofNat 1789283,
  Int.ofNat 649041, Int.ofNat 229567, Int.ofNat 79223, Int.ofNat 26651, Int.ofNat 8716,
  Int.ofNat 2758, Int.ofNat 836, Int.ofNat 239, Int.ofNat 61, Int.ofNat 14, Int.ofNat 1 ]
private def lm2R256V3P4 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V3P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V3 : List ℤ :=
  lm2R256V3P0 ++ (lm2R256V3P1 ++ (lm2R256V3P2 ++
    (lm2R256V3P3 ++ (lm2R256V3P4 ++ lm2R256V3P5))))
private def lm2R256V4P0 : List ℤ := [
  Int.ofNat 786777453, Int.ofNat 852878776, Int.negSucc 5900671363, Int.negSucc 1672307227,
  Int.negSucc 146327116, Int.ofNat 3144124552, Int.ofNat 7374590644, Int.negSucc 9250515238,
  Int.negSucc 2582320986, Int.negSucc 6851701652, Int.negSucc 19905119681,
  Int.negSucc 3725919526, Int.ofNat 14325939445, Int.negSucc 11152877420,
  Int.negSucc 11857791001, Int.negSucc 4012064171, Int.ofNat 18448109726,
  Int.negSucc 6319963913, Int.ofNat 11151279769, Int.negSucc 14127085984,
  Int.negSucc 7765840850, Int.ofNat 4379159050, Int.negSucc 16697442402,
  Int.negSucc 32321391485, Int.negSucc 39873411847, Int.negSucc 84584715993,
  Int.negSucc 57416794889, Int.ofNat 2700122377, Int.ofNat 128471229098, Int.ofNat 48105551642,
  Int.negSucc 66296661259, Int.ofNat 17061237963, Int.ofNat 9225195893, Int.negSucc 88811196380,
  Int.negSucc 208660342332, Int.ofNat 49828377258, Int.ofNat 14187431718,
  Int.ofNat 175174147075, Int.ofNat 170797756567, Int.ofNat 213225966432, Int.ofNat 72985936247,
  Int.ofNat 22932092501, Int.negSucc 112965818830, Int.negSucc 58305944221,
  Int.ofNat 117397433345, Int.negSucc 211623783752, Int.ofNat 72534759841,
  Int.ofNat 244949131218 ]
private def lm2R256V4P1 : List ℤ := [
  Int.ofNat 65582489346, Int.negSucc 69935084904, Int.ofNat 48835943225,
  Int.negSucc 154895500722, Int.negSucc 276052627936, Int.negSucc 140495727479,
  Int.negSucc 499843860280, Int.negSucc 1199920812287, Int.negSucc 1157679325852,
  Int.negSucc 819880727197, Int.negSucc 427488914187, Int.ofNat 4532100416,
  Int.ofNat 314378705755, Int.ofNat 105334584566, Int.negSucc 11268182741,
  Int.negSucc 1062971978213, Int.negSucc 1002546268938, Int.negSucc 246638444023,
  Int.ofNat 294042666867, Int.ofNat 130012208134, Int.ofNat 828060478598,
  Int.ofNat 1147437929673, Int.ofNat 2211521479520, Int.ofNat 3994814253517,
  Int.ofNat 3511090942060, Int.negSucc 954437808309, Int.negSucc 1845387131545,
  Int.negSucc 276947328472, Int.negSucc 188679617864, Int.ofNat 818960422187,
  Int.negSucc 1638084308549, Int.negSucc 1214901312696, Int.negSucc 2235122106353,
  Int.negSucc 52430817350, Int.ofNat 1307222800854, Int.ofNat 196253126621,
  Int.negSucc 2191103755924, Int.ofNat 61121645608, Int.negSucc 829965833170,
  Int.negSucc 1523833962691, Int.ofNat 923247981266, Int.negSucc 1280313667473,
  Int.negSucc 4524592853217, Int.negSucc 2842896276525, Int.negSucc 3595796963259,
  Int.ofNat 2247355715391, Int.negSucc 999282906505, Int.negSucc 2164348476695 ]
private def lm2R256V4P2 : List ℤ := [
  Int.negSucc 1316307748295, Int.negSucc 3097290197035, Int.negSucc 3058711732695,
  Int.negSucc 16925252809, Int.ofNat 473911144872, Int.ofNat 2398730639747,
  Int.ofNat 3885276002184, Int.ofNat 3357663160318, Int.ofNat 828882414606,
  Int.negSucc 4451911995228, Int.negSucc 1777588671228, Int.ofNat 591963846430,
  Int.negSucc 721941356491, Int.negSucc 5445264675249, Int.negSucc 3951330103282,
  Int.ofNat 1702118142376, Int.ofNat 3645753269947, Int.ofNat 3708826870765,
  Int.ofNat 2090303605658, Int.ofNat 1972518875060, Int.ofNat 6966765378916,
  Int.ofNat 8727888738560, Int.ofNat 17514064857252, Int.ofNat 15934693806752,
  Int.ofNat 10132666890310, Int.ofNat 7078180479276, Int.ofNat 5606959175527,
  Int.ofNat 2308946215668, Int.negSucc 1499641057749, Int.negSucc 78885941021,
  Int.ofNat 1959958023519, Int.ofNat 3966696681552, Int.ofNat 10254512018028,
  Int.ofNat 191232251518, Int.ofNat 2415685785640, Int.negSucc 2561907218339,
  Int.negSucc 6330001380260, Int.negSucc 926935523518, Int.ofNat 6611318979155,
  Int.negSucc 1000870537257, Int.negSucc 7909893615485, Int.negSucc 8023680949244,
  Int.ofNat 1165590019008, Int.negSucc 2911703898719, Int.negSucc 6192200953361,
  Int.negSucc 1800363397813, Int.ofNat 4859048291156, Int.ofNat 6562902518713 ]
private def lm2R256V4P3 : List ℤ := [
  Int.ofNat 15183077320471, Int.ofNat 10701236731639, Int.ofNat 21019228915476,
  Int.ofNat 11087365044683, Int.ofNat 12334643110109, Int.ofNat 6868608227906,
  Int.ofNat 11971228244219, Int.ofNat 7547277534789, Int.ofNat 4343459650473,
  Int.ofNat 6619321778421, Int.negSucc 2502530727983, Int.ofNat 4962401237335,
  Int.ofNat 9152586446698, Int.ofNat 14950030540739, Int.ofNat 2670960358466,
  Int.ofNat 5053359405197, Int.ofNat 8510995316567, Int.ofNat 31142795340127,
  Int.ofNat 39644231912338, Int.ofNat 25687193327219, Int.ofNat 1545789670097,
  Int.ofNat 11638620667842, Int.ofNat 2241052528689, Int.ofNat 47470103710890,
  Int.ofNat 117178245352694, Int.ofNat 197890081700879, Int.ofNat 274665594844023,
  Int.ofNat 335070641699948, Int.ofNat 371421225213378, Int.ofNat 381371044563706,
  Int.ofNat 367202776327167, Int.ofNat 334334106898200, Int.ofNat 289588794824753,
  Int.ofNat 239687234694052, Int.ofNat 190215362561900, Int.ofNat 145125295362807,
  Int.ofNat 106680037536952, Int.ofNat 75694746332515, Int.ofNat 51925412214240,
  Int.ofNat 34483357026121, Int.ofNat 22193178453852, Int.ofNat 13852839864789,
  Int.ofNat 8389846148389, Int.ofNat 4930839322148, Int.ofNat 2811962712718,
  Int.ofNat 1555636832854, Int.ofNat 834992279638, Int.ofNat 434394290462 ]
private def lm2R256V4P4 : List ℤ := [
  Int.ofNat 219674975283, Int.ofNat 107566691652, Int.ofNat 51101275470, Int.ofNat 23857435171,
  Int.negSucc 10862030559, Int.ofNat 4658644113, Int.ofNat 1827842070, Int.ofNat 663983015,
  Int.ofNat 238171725, Int.ofNat 90054086, Int.ofNat 35386224, Int.ofNat 13499294,
  Int.ofNat 4794570, Int.ofNat 1593666, Int.ofNat 511968, Int.ofNat 164312, Int.ofNat 53446,
  Int.ofNat 17413, Int.ofNat 5515, Int.ofNat 1649, Int.ofNat 462, Int.ofNat 121, Int.ofNat 27,
  Int.ofNat 5, Int.negSucc 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V4P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V4 : List ℤ :=
  lm2R256V4P0 ++ (lm2R256V4P1 ++ (lm2R256V4P2 ++
    (lm2R256V4P3 ++ (lm2R256V4P4 ++ lm2R256V4P5))))
private def lm2R256V5P0 : List ℤ := [
  Int.negSucc 350184659, Int.negSucc 2243834026, Int.negSucc 2076809321, Int.ofNat 2976243129,
  Int.ofNat 2256734118, Int.negSucc 11699130416, Int.negSucc 2532314316, Int.negSucc 6935115103,
  Int.negSucc 11880004502, Int.negSucc 11906556670, Int.ofNat 2156699123, Int.ofNat 4233242445,
  Int.negSucc 1820424167, Int.negSucc 1220756280, Int.negSucc 5557185730,
  Int.negSucc 5026592015, Int.negSucc 2687613143, Int.negSucc 1908806555,
  Int.negSucc 4324390558, Int.ofNat 520262750, Int.negSucc 9465568022, Int.negSucc 1447747356,
  Int.negSucc 5797237243, Int.ofNat 588768736, Int.negSucc 1658050539, Int.ofNat 1739955008,
  Int.ofNat 7534715952, Int.ofNat 2926111131, Int.ofNat 77879836725, Int.ofNat 34580715776,
  Int.ofNat 20190553948, Int.negSucc 13510400413, Int.negSucc 17527186100, Int.ofNat 6068400940,
  Int.negSucc 20019490865, Int.negSucc 51646848480, Int.negSucc 44464035707,
  Int.negSucc 86678837113, Int.negSucc 120320148147, Int.negSucc 65300431695,
  Int.negSucc 146226917063, Int.negSucc 42402355104, Int.negSucc 78285975334,
  Int.negSucc 17480189360, Int.ofNat 67165550963, Int.negSucc 113330835179,
  Int.negSucc 179952954714, Int.negSucc 117235749311 ]
private def lm2R256V5P1 : List ℤ := [
  Int.negSucc 290399717643, Int.negSucc 319922587751, Int.negSucc 136718645572,
  Int.ofNat 78057548499, Int.ofNat 198654337177, Int.ofNat 195687838607, Int.ofNat 158496066317,
  Int.negSucc 171495875961, Int.negSucc 128181990677, Int.negSucc 27224852020,
  Int.negSucc 46308502578, Int.negSucc 175043274546, Int.negSucc 272722709825,
  Int.negSucc 76150460638, Int.negSucc 56915592261, Int.ofNat 49195915668,
  Int.negSucc 224870591966, Int.ofNat 23561728637, Int.ofNat 448382922865,
  Int.negSucc 76679586985, Int.ofNat 39740453657, Int.ofNat 223196413764,
  Int.ofNat 233364351922, Int.ofNat 390530476904, Int.negSucc 19375875671,
  Int.negSucc 843970070055, Int.negSucc 1210078400520, Int.negSucc 248457349683,
  Int.negSucc 1194071003235, Int.negSucc 138560925863, Int.ofNat 1008410465536,
  Int.ofNat 1507548157941, Int.ofNat 1757141666449, Int.ofNat 1368075966918,
  Int.negSucc 145784791696, Int.negSucc 1643157659457, Int.negSucc 1730273960078,
  Int.negSucc 660729474832, Int.ofNat 5002759520, Int.ofNat 1925551419262,
  Int.ofNat 1962233430271, Int.ofNat 239378750298, Int.ofNat 171698843493,
  Int.ofNat 886951826033, Int.ofNat 2175417506774, Int.ofNat 2687648156000,
  Int.ofNat 4217274590227, Int.ofNat 4395767440532 ]
private def lm2R256V5P2 : List ℤ := [
  Int.ofNat 4653415841647, Int.ofNat 2503491171979, Int.ofNat 1551273130689,
  Int.negSucc 400323262852, Int.negSucc 939095578113, Int.negSucc 1077794422553,
  Int.negSucc 490175140387, Int.negSucc 2219945140364, Int.negSucc 366969280154,
  Int.negSucc 2274571764286, Int.ofNat 501344963296, Int.negSucc 1093552965546,
  Int.negSucc 3195969837462, Int.negSucc 1226268427437, Int.ofNat 1859457111668,
  Int.ofNat 1260224324887, Int.ofNat 1699792992973, Int.ofNat 1722223729738,
  Int.ofNat 3075407781409, Int.ofNat 4094508622306, Int.ofNat 4909705111026,
  Int.negSucc 1742800705283, Int.negSucc 843892939127, Int.negSucc 3136264271911,
  Int.negSucc 983317128635, Int.negSucc 1688461224000, Int.negSucc 4207145462555,
  Int.negSucc 3889237708671, Int.negSucc 729479551537, Int.negSucc 2322312722383,
  Int.negSucc 5642611175886, Int.negSucc 3364660993702, Int.negSucc 4830084796276,
  Int.negSucc 6128232679117, Int.negSucc 1495404416675, Int.negSucc 5051658184360,
  Int.negSucc 516826289848, Int.negSucc 2561099344192, Int.ofNat 2450679206067,
  Int.ofNat 131685748257, Int.negSucc 2256981905931, Int.negSucc 5640502004237,
  Int.negSucc 1538161238556, Int.ofNat 4653508594943, Int.negSucc 4802766175763,
  Int.ofNat 4390311114713, Int.ofNat 4919588210194, Int.negSucc 5613445696809 ]
private def lm2R256V5P3 : List ℤ := [
  Int.negSucc 5420233196927, Int.ofNat 5439983360725, Int.ofNat 4597990320519,
  Int.ofNat 11302417650752, Int.ofNat 12072228612200, Int.ofNat 15127249490018,
  Int.ofNat 11744161564487, Int.ofNat 17012605760612, Int.ofNat 522007226152,
  Int.negSucc 119557804037, Int.ofNat 1207909165028, Int.ofNat 13175045059487,
  Int.ofNat 18564452230149, Int.ofNat 2671483145829, Int.ofNat 4190343419378,
  Int.ofNat 12608995445635, Int.ofNat 6198721255602, Int.negSucc 7846486010848,
  Int.negSucc 6095013561134, Int.ofNat 3383336775767, Int.ofNat 7952427477579,
  Int.ofNat 418857217479, Int.negSucc 13614987531541, Int.negSucc 12419984271625,
  Int.ofNat 8307278552012, Int.ofNat 9854980498468, Int.ofNat 6970502362241,
  Int.negSucc 11660618771194, Int.ofNat 12216852461684, Int.ofNat 3272388633026,
  Int.ofNat 14978240693825, Int.ofNat 7428062000651, Int.ofNat 1173504462541,
  Int.ofNat 11261336770117, Int.ofNat 7077685334642, Int.ofNat 8186814315624,
  Int.ofNat 21148656753426, Int.ofNat 17098648361608, Int.negSucc 2521458211495,
  Int.negSucc 12208214502609, Int.negSucc 4122165982035, Int.ofNat 13472531476540,
  Int.ofNat 31947102993631, Int.ofNat 42510831860840, Int.ofNat 36129165148274,
  Int.ofNat 11959277998987, Int.negSucc 17374601258986, Int.negSucc 31521847527824 ]
private def lm2R256V5P4 : List ℤ := [
  Int.negSucc 13886441367227, Int.ofNat 40105731126170, Int.ofNat 121966615899779,
  Int.ofNat 214765622008670, Int.ofNat 299728096665460, Int.ofNat 361843055711459,
  Int.ofNat 393003480422935, Int.ofNat 392460815729762, Int.ofNat 365258135164048,
  Int.ofNat 319710446991924, Int.ofNat 264897309373738, Int.ofNat 208765971275955,
  Int.ofNat 157079075176730, Int.ofNat 113163931791580, Int.ofNat 78235415616282,
  Int.ofNat 51996789231880, Int.ofNat 33271463033514, Int.ofNat 20523504180088,
  Int.ofNat 12217591721369, Int.ofNat 7024135937211, Int.ofNat 3900925457402,
  Int.ofNat 2091911523212, Int.ofNat 1082248992561, Int.ofNat 539513381449,
  Int.ofNat 258863183260, Int.ofNat 119449232903, Int.ofNat 52996547960, Int.ofNat 22620000951,
  Int.ofNat 9297470430, Int.ofNat 3688569763, Int.ofNat 1412577785, Int.ofNat 525826751,
  Int.ofNat 190828568, Int.ofNat 65991907, Int.negSucc 20998758, Int.ofNat 6060334,
  Int.ofNat 1624363, Int.ofNat 429030, Int.ofNat 118958, Int.ofNat 35192, Int.ofNat 10744,
  Int.ofNat 3232, Int.ofNat 916, Int.ofNat 234, Int.negSucc 49, Int.ofNat 9, Int.ofNat 0,
  Int.ofNat 0 ]
private def lm2R256V5P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V5 : List ℤ :=
  lm2R256V5P0 ++ (lm2R256V5P1 ++ (lm2R256V5P2 ++
    (lm2R256V5P3 ++ (lm2R256V5P4 ++ lm2R256V5P5))))
private def lm2R256V6P0 : List ℤ := [
  Int.negSucc 241005031, Int.negSucc 297793890, Int.negSucc 713164449, Int.negSucc 510273217,
  Int.negSucc 2715948774, Int.negSucc 4386797432, Int.negSucc 3632700049, Int.ofNat 1962438306,
  Int.ofNat 5492550473, Int.ofNat 9046237515, Int.ofNat 3489782398, Int.ofNat 6114960791,
  Int.ofNat 4985004769, Int.ofNat 4133981502, Int.ofNat 2677117665, Int.negSucc 4974285775,
  Int.ofNat 1032186454, Int.ofNat 23335275547, Int.ofNat 6823490555, Int.negSucc 11309532972,
  Int.ofNat 10236759499, Int.ofNat 346705876, Int.ofNat 3879361585, Int.ofNat 3740061611,
  Int.negSucc 183966406, Int.ofNat 14802064521, Int.negSucc 5370006432, Int.ofNat 2813731671,
  Int.negSucc 409815525, Int.ofNat 9762435489, Int.negSucc 9788448309, Int.negSucc 2076982628,
  Int.ofNat 13312744669, Int.negSucc 9986915102, Int.negSucc 17253766685,
  Int.negSucc 15679258163, Int.negSucc 30393217987, Int.ofNat 39849433925, Int.ofNat 7222522093,
  Int.ofNat 43359005718, Int.negSucc 7686102258, Int.negSucc 18574193209, Int.ofNat 23886978904,
  Int.negSucc 20505001150, Int.ofNat 28895813808, Int.negSucc 24161031888,
  Int.negSucc 7816975532, Int.negSucc 48349478870 ]
private def lm2R256V6P1 : List ℤ := [
  Int.ofNat 67973305109, Int.ofNat 152115176881, Int.ofNat 23510857767, Int.ofNat 16028016498,
  Int.ofNat 66528658135, Int.ofNat 202094832981, Int.ofNat 71487531129, Int.ofNat 40744763992,
  Int.negSucc 66354326692, Int.negSucc 57890624677, Int.negSucc 6193156982,
  Int.ofNat 51695453834, Int.ofNat 90225734234, Int.ofNat 163018581017, Int.ofNat 153708251791,
  Int.ofNat 122104962221, Int.ofNat 48748324242, Int.negSucc 12367680986,
  Int.negSucc 339268575172, Int.negSucc 512501777222, Int.negSucc 360081236739,
  Int.negSucc 267240495605, Int.negSucc 334637589677, Int.negSucc 212358237607,
  Int.ofNat 22321348780, Int.ofNat 397974617297, Int.ofNat 509432769048, Int.ofNat 353435391449,
  Int.negSucc 175186717526, Int.negSucc 227690800120, Int.negSucc 211181630565,
  Int.ofNat 214231450721, Int.ofNat 348637644235, Int.ofNat 532146959084,
  Int.negSucc 428965000781, Int.negSucc 394572315310, Int.ofNat 310633693818,
  Int.ofNat 756784999475, Int.ofNat 266987365564, Int.ofNat 278598183410,
  Int.negSucc 253122069462, Int.negSucc 673777646466, Int.negSucc 23256156643,
  Int.negSucc 121544831065, Int.negSucc 850406843432, Int.negSucc 669672557107,
  Int.negSucc 440479280084, Int.negSucc 809871802714 ]
private def lm2R256V6P2 : List ℤ := [
  Int.negSucc 1064739072576, Int.negSucc 570802265311, Int.negSucc 752009426323,
  Int.ofNat 940426415023, Int.ofNat 810181295852, Int.ofNat 144402076918,
  Int.ofNat 221472716142, Int.ofNat 1344882961976, Int.negSucc 1644675779604,
  Int.negSucc 3566639070299, Int.negSucc 2297099727845, Int.negSucc 257048376825,
  Int.negSucc 81122143018, Int.ofNat 1392360940741, Int.ofNat 145947048760,
  Int.ofNat 2851483102252, Int.negSucc 1058424261497, Int.negSucc 42914351154,
  Int.negSucc 294810920980, Int.negSucc 2303661844426, Int.ofNat 3584259290764,
  Int.negSucc 226691382860, Int.negSucc 3277455828181, Int.ofNat 1918560661812,
  Int.ofNat 175808349224, Int.negSucc 2395787060434, Int.ofNat 447507769229,
  Int.ofNat 667872414493, Int.ofNat 4750125286802, Int.ofNat 1894106069547,
  Int.ofNat 5417836740494, Int.ofNat 5629255216522, Int.ofNat 7562544547206,
  Int.ofNat 4609093076626, Int.negSucc 369927297660, Int.ofNat 1011749084601,
  Int.negSucc 2092610993549, Int.negSucc 3551292324470, Int.negSucc 3212245425726,
  Int.ofNat 3583152837519, Int.negSucc 996798908387, Int.ofNat 2096641230968,
  Int.ofNat 2209118734952, Int.ofNat 886548571546, Int.negSucc 449865786928,
  Int.negSucc 5030664326352, Int.negSucc 1569531141621, Int.ofNat 515307310938 ]
private def lm2R256V6P3 : List ℤ := [
  Int.ofNat 2056789489107, Int.negSucc 363222086833, Int.negSucc 1140547393493,
  Int.ofNat 324777963560, Int.ofNat 2932661393469, Int.negSucc 1051122683116,
  Int.negSucc 3754908473561, Int.negSucc 3165076786865, Int.negSucc 5832259444536,
  Int.negSucc 4874310323797, Int.ofNat 4147091517135, Int.ofNat 4072426710460,
  Int.negSucc 6469532748229, Int.negSucc 16127751139470, Int.negSucc 9154112188316,
  Int.ofNat 3713670345154, Int.negSucc 1778134712934, Int.negSucc 7818674366539,
  Int.ofNat 2107133876203, Int.ofNat 3966337627555, Int.negSucc 6097075848233,
  Int.negSucc 8876858197924, Int.ofNat 5425645107638, Int.ofNat 9294263247457,
  Int.ofNat 3992549918147, Int.negSucc 622513287569, Int.negSucc 9179202144065,
  Int.negSucc 4865079724395, Int.negSucc 4065476476063, Int.negSucc 14905234973240,
  Int.ofNat 3388949151878, Int.ofNat 22556223584003, Int.ofNat 22077175308419,
  Int.ofNat 2694516577918, Int.ofNat 925974111894, Int.ofNat 10356312697437,
  Int.ofNat 17674268147357, Int.ofNat 14264366639750, Int.negSucc 3778880382061,
  Int.ofNat 530469996758, Int.ofNat 8921558846555, Int.ofNat 10070059503764,
  Int.ofNat 13361560461790, Int.ofNat 5518520811856, Int.ofNat 1286411095308,
  Int.ofNat 9293316611752, Int.ofNat 8390139938837, Int.ofNat 4212265366081 ]
private def lm2R256V6P4 : List ℤ := [
  Int.negSucc 5663901918008, Int.negSucc 12942870462698, Int.negSucc 2681899562469,
  Int.ofNat 10730683617127, Int.ofNat 10774364509665, Int.ofNat 2040560817198,
  Int.negSucc 4780879151626, Int.negSucc 3799820040445, Int.ofNat 6735828233086,
  Int.ofNat 21960003864852, Int.ofNat 28342861492182, Int.ofNat 16399839931504,
  Int.negSucc 10783797517455, Int.negSucc 31073735185777, Int.negSucc 26527162819007,
  Int.ofNat 4666735721316, Int.ofNat 44390276400464, Int.ofNat 65070519752657,
  Int.ofNat 49336791896063, Int.ofNat 2360783819684, Int.negSucc 50622200025843,
  Int.negSucc 78187180381921, Int.negSucc 57669255855374, Int.ofNat 13477664622819,
  Int.ofNat 121960151589985, Int.ofNat 237034114704034, Int.ofNat 339205791790957,
  Int.ofNat 397894199528244, Int.ofNat 420284036995980, Int.ofNat 397774896328161,
  Int.ofNat 346640527002911, Int.ofNat 285680798424993, Int.ofNat 217817433302755,
  Int.ofNat 154722848370656, Int.ofNat 106668711174116, Int.ofNat 70959356926861,
  Int.ofNat 43501707880458, Int.ofNat 24035547094436, Int.ofNat 12082632649682,
  Int.ofNat 5615194906578, Int.ofNat 2359798811352, Int.ofNat 892014304670,
  Int.ofNat 297916206782, Int.ofNat 83779104411, Int.ofNat 20565703763, Int.ofNat 6516337690,
  Int.ofNat 3601301277, Int.ofNat 2185753711 ]
private def lm2R256V6P5 : List ℤ := [
  Int.ofNat 1131319030, Int.ofNat 494159130, Int.ofNat 187233048, Int.ofNat 62823294,
  Int.negSucc 18852963, Int.ofNat 5072239, Int.ofNat 1222390, Int.ofNat 263608, Int.ofNat 50867,
  Int.ofNat 8785, Int.negSucc 1349, Int.ofNat 181, Int.negSucc 16, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0 ]
private def lm2R256V6 : List ℤ :=
  lm2R256V6P0 ++ (lm2R256V6P1 ++ (lm2R256V6P2 ++
    (lm2R256V6P3 ++ (lm2R256V6P4 ++ lm2R256V6P5))))
private def lm2R256V7P0 : List ℤ := [
  Int.ofNat 403450956, Int.ofNat 71889951, Int.negSucc 128422641, Int.negSucc 1013314289,
  Int.negSucc 466368604, Int.negSucc 1348424516, Int.ofNat 735290196, Int.negSucc 266321730,
  Int.negSucc 2681142527, Int.negSucc 384252532, Int.negSucc 423782328, Int.negSucc 862528914,
  Int.negSucc 3070226502, Int.negSucc 1117939407, Int.negSucc 5577392371,
  Int.negSucc 5501149268, Int.negSucc 6269556109, Int.ofNat 3602913402, Int.ofNat 7252567767,
  Int.ofNat 4109024275, Int.negSucc 2571870250, Int.negSucc 5766278261, Int.negSucc 10561922361,
  Int.ofNat 4036494626, Int.ofNat 751611111, Int.ofNat 7002848499, Int.ofNat 8998282559,
  Int.ofNat 8794806535, Int.ofNat 6150731739, Int.negSucc 14622199761, Int.negSucc 11785295099,
  Int.ofNat 4460262148, Int.negSucc 26459365793, Int.ofNat 2417542681, Int.ofNat 7094117994,
  Int.ofNat 19950266839, Int.ofNat 26094823188, Int.ofNat 10797506506, Int.ofNat 18444912770,
  Int.negSucc 26672110461, Int.negSucc 9295697972, Int.negSucc 6706060987,
  Int.ofNat 12733388513, Int.ofNat 32910940040, Int.ofNat 51721270625, Int.ofNat 43608682394,
  Int.ofNat 57462582659, Int.ofNat 26591875321 ]
private def lm2R256V7P1 : List ℤ := [
  Int.negSucc 16107790447, Int.negSucc 31479063737, Int.negSucc 58786035771,
  Int.ofNat 2197954730, Int.ofNat 78595601911, Int.negSucc 12489437802, Int.ofNat 8264020356,
  Int.ofNat 4531821650, Int.negSucc 2883166675, Int.ofNat 33258726561, Int.negSucc 68881307689,
  Int.negSucc 68056768450, Int.negSucc 355969314, Int.negSucc 75770636974,
  Int.negSucc 13793101569, Int.negSucc 73741865869, Int.negSucc 86796439259,
  Int.negSucc 148905883572, Int.negSucc 297585303565, Int.negSucc 58135245726,
  Int.negSucc 15241477683, Int.ofNat 185902269433, Int.ofNat 40501218693,
  Int.negSucc 46856272460, Int.negSucc 10317156352, Int.negSucc 124044727230,
  Int.negSucc 37813005949, Int.negSucc 31761831633, Int.negSucc 10515595719,
  Int.negSucc 52959763753, Int.negSucc 78072605874, Int.negSucc 9511757034,
  Int.negSucc 95006461328, Int.ofNat 68223449049, Int.ofNat 267010009835, Int.ofNat 83736802065,
  Int.negSucc 87602633653, Int.ofNat 191909368822, Int.ofNat 346273438468,
  Int.ofNat 52617222194, Int.negSucc 52932027954, Int.ofNat 83672419355, Int.ofNat 249778544805,
  Int.ofNat 615474672714, Int.ofNat 996061754661, Int.ofNat 759684964482,
  Int.ofNat 662466089408, Int.ofNat 445456911395 ]
private def lm2R256V7P2 : List ℤ := [
  Int.negSucc 636730964458, Int.negSucc 690488193363, Int.ofNat 58322400578,
  Int.ofNat 250095010615, Int.negSucc 284571681317, Int.negSucc 279047576377,
  Int.ofNat 773771504124, Int.ofNat 920119403107, Int.negSucc 451375745982,
  Int.ofNat 619181479550, Int.ofNat 125686691784, Int.ofNat 550915932029,
  Int.negSucc 180756067642, Int.ofNat 112972232595, Int.negSucc 196483051556,
  Int.ofNat 22659276148, Int.negSucc 545060188302, Int.negSucc 1240956838345,
  Int.negSucc 280241450280, Int.negSucc 1179963306707, Int.negSucc 2863578996690,
  Int.negSucc 1682248505541, Int.negSucc 1027958985380, Int.negSucc 909950123328,
  Int.ofNat 454332529324, Int.ofNat 2531768703899, Int.ofNat 2251678148339,
  Int.ofNat 1689434996784, Int.ofNat 1064448944782, Int.ofNat 1120665819188,
  Int.ofNat 17246991719, Int.ofNat 1955709240306, Int.negSucc 1626800566069,
  Int.negSucc 5384258668463, Int.negSucc 2654808799681, Int.ofNat 269707435985,
  Int.ofNat 1776565470400, Int.negSucc 2638519233774, Int.ofNat 3369870607848,
  Int.ofNat 417651640703, Int.ofNat 976852857423, Int.ofNat 2485069234339,
  Int.ofNat 2186823028673, Int.ofNat 3129835523831, Int.ofNat 2071637824842,
  Int.negSucc 2239360537548, Int.negSucc 2579829376588, Int.ofNat 1547405098633 ]
private def lm2R256V7P3 : List ℤ := [
  Int.ofNat 2987894531767, Int.ofNat 1617889530613, Int.ofNat 3091106534030,
  Int.ofNat 589491436167, Int.negSucc 481544319936, Int.negSucc 1406472975113,
  Int.ofNat 2981462966492, Int.negSucc 1514366696705, Int.negSucc 327820050894,
  Int.ofNat 1273071969018, Int.negSucc 2921673153789, Int.negSucc 10510284763603,
  Int.negSucc 5374688325508, Int.negSucc 882835944627, Int.ofNat 2859345229236,
  Int.negSucc 4879107441260, Int.negSucc 1595469843302, Int.negSucc 524637367788,
  Int.negSucc 2920166409339, Int.negSucc 1319484294981, Int.negSucc 945770188427,
  Int.ofNat 27691983511, Int.negSucc 7119533941592, Int.negSucc 3216989948583,
  Int.negSucc 1341680929345, Int.ofNat 1502605202011, Int.ofNat 6267667272311,
  Int.negSucc 3408030158215, Int.ofNat 9343336375026, Int.ofNat 16841811375848,
  Int.ofNat 6726357202679, Int.ofNat 12681007238013, Int.ofNat 10206612069549,
  Int.ofNat 5997710403056, Int.ofNat 313175987888, Int.ofNat 2458407746914,
  Int.ofNat 4476728830856, Int.ofNat 3045390339535, Int.negSucc 3368131940262,
  Int.negSucc 14945999833402, Int.negSucc 6778625874967, Int.negSucc 1307724607573,
  Int.negSucc 2299867937019, Int.negSucc 5739216546647, Int.negSucc 3668738974393,
  Int.ofNat 898793921756, Int.negSucc 2766602316568, Int.negSucc 1204780689745 ]
private def lm2R256V7P4 : List ℤ := [
  Int.negSucc 6348294343786, Int.negSucc 18780719746326, Int.ofNat 25295779315757,
  Int.ofNat 8244151992471, Int.ofNat 2223495276143, Int.ofNat 11011387470836,
  Int.ofNat 11965241376052, Int.ofNat 12685576989687, Int.ofNat 17782260083069,
  Int.ofNat 5741350340111, Int.ofNat 17226638160672, Int.ofNat 5604864210859,
  Int.ofNat 2496481620491, Int.ofNat 7960513282391, Int.ofNat 12365120312779,
  Int.ofNat 495393817679, Int.ofNat 4269289335835, Int.ofNat 11453389297913,
  Int.ofNat 10186991516353, Int.ofNat 1016054533481, Int.ofNat 15331774581061,
  Int.ofNat 15437582536027, Int.ofNat 4801455668894, Int.ofNat 8576751459126,
  Int.ofNat 39063444592836, Int.ofNat 1476677126870, Int.ofNat 7406087401417,
  Int.ofNat 52412029000241, Int.ofNat 40965089238334, Int.ofNat 10649052020314,
  Int.ofNat 11867309375246, Int.ofNat 56926120856611, Int.ofNat 40969419218841,
  Int.ofNat 9474008750344, Int.ofNat 31033155833280, Int.ofNat 80612234108701,
  Int.ofNat 91712000974873, Int.ofNat 48570020824051, Int.ofNat 1656389524671,
  Int.ofNat 7918064001938, Int.ofNat 92495425248356, Int.ofNat 221984793749214,
  Int.ofNat 350268932561273, Int.ofNat 431038732428986, Int.ofNat 448515659178677,
  Int.ofNat 410900215839701, Int.ofNat 341215336614780, Int.ofNat 254184883726043 ]
private def lm2R256V7P5 : List ℤ := [
  Int.ofNat 173760437860366, Int.ofNat 111833538624899, Int.ofNat 64797509734606,
  Int.ofNat 33541440389086, Int.ofNat 13707296763190, Int.ofNat 4215395465593,
  Int.ofNat 1024005980908, Int.ofNat 230241516576, Int.ofNat 62254079476, Int.ofNat 20946220853,
  Int.ofNat 6913890979, Int.ofNat 2030819289, Int.ofNat 450929676, Int.ofNat 72412200,
  Int.ofNat 9979634, Int.ofNat 1483392, Int.negSucc 159418 ]
private def lm2R256V7 : List ℤ :=
  lm2R256V7P0 ++ (lm2R256V7P1 ++ (lm2R256V7P2 ++
    (lm2R256V7P3 ++ (lm2R256V7P4 ++ lm2R256V7P5))))
private def lm2R256V8P0 : List ℤ := [
  Int.negSucc 307830421, Int.negSucc 111663770, Int.negSucc 354050638, Int.negSucc 545834180,
  Int.ofNat 131783116, Int.ofNat 393649080, Int.negSucc 382289375, Int.negSucc 501218815,
  Int.negSucc 1739707090, Int.negSucc 1762722408, Int.negSucc 247213697, Int.negSucc 1649252556,
  Int.negSucc 1351558821, Int.negSucc 592639345, Int.ofNat 617529476, Int.ofNat 4436539858,
  Int.ofNat 2663375052, Int.ofNat 1390064558, Int.ofNat 2456607867, Int.negSucc 1141727426,
  Int.negSucc 1471892634, Int.negSucc 2763159583, Int.negSucc 568383362, Int.ofNat 3984859262,
  Int.ofNat 1904111437, Int.ofNat 7019777736, Int.ofNat 7696764610, Int.ofNat 10358763451,
  Int.ofNat 2133395618, Int.ofNat 317303903, Int.negSucc 3472234601, Int.ofNat 2680463884,
  Int.ofNat 9994381113, Int.ofNat 2035099259, Int.negSucc 1883967899, Int.negSucc 13447559701,
  Int.negSucc 9565083995, Int.ofNat 3641688911, Int.ofNat 6706762663, Int.ofNat 231885031,
  Int.ofNat 3839462487, Int.ofNat 705397893, Int.ofNat 48451802398, Int.ofNat 1522696133,
  Int.ofNat 26900444710, Int.ofNat 35678997488, Int.ofNat 1756045473, Int.ofNat 1266594178 ]
private def lm2R256V8P1 : List ℤ := [
  Int.negSucc 9895589900, Int.negSucc 61969997292, Int.negSucc 29816305339,
  Int.negSucc 3922243233, Int.ofNat 2056309028, Int.ofNat 25846661126, Int.negSucc 2321920132,
  Int.negSucc 26366443462, Int.negSucc 9147737519, Int.negSucc 21125081915,
  Int.negSucc 23016913211, Int.negSucc 31553212843, Int.ofNat 4090775724, Int.ofNat 75855168667,
  Int.ofNat 20902644759, Int.negSucc 74956072922, Int.ofNat 11287034753, Int.ofNat 12477057895,
  Int.negSucc 9577106707, Int.negSucc 31931587607, Int.negSucc 85261384052,
  Int.negSucc 138088595455, Int.negSucc 12248894569, Int.negSucc 4290012110,
  Int.negSucc 48430821733, Int.negSucc 76561521808, Int.negSucc 68134307539,
  Int.ofNat 59271840689, Int.ofNat 72161894208, Int.ofNat 61780907778, Int.negSucc 27470495136,
  Int.negSucc 31104350128, Int.ofNat 3713370832, Int.ofNat 31711942680, Int.ofNat 7046437073,
  Int.ofNat 4135866336, Int.negSucc 64358590777, Int.negSucc 33159690135,
  Int.negSucc 5422687050, Int.ofNat 65580784530, Int.negSucc 449794134,
  Int.negSucc 148321785399, Int.negSucc 160947037509, Int.negSucc 227347026242,
  Int.negSucc 304167499469, Int.negSucc 111155164841, Int.ofNat 141189925359,
  Int.ofNat 53200896504 ]
private def lm2R256V8P2 : List ℤ := [
  Int.negSucc 29441642628, Int.negSucc 97947095928, Int.ofNat 151056276489,
  Int.negSucc 4386625421, Int.negSucc 47371809169, Int.negSucc 114474786161,
  Int.negSucc 101894280673, Int.negSucc 41336711726, Int.negSucc 421276394604,
  Int.negSucc 563257397222, Int.negSucc 343968368109, Int.negSucc 221256416917,
  Int.ofNat 193758172908, Int.ofNat 449502616568, Int.ofNat 589511665487,
  Int.ofNat 443355999172, Int.ofNat 206422919226, Int.negSucc 120468053853,
  Int.negSucc 10484973924, Int.negSucc 349347883269, Int.negSucc 56946450586,
  Int.ofNat 264393985838, Int.ofNat 583441143107, Int.ofNat 1077993566778,
  Int.ofNat 1373709733470, Int.ofNat 1035174014981, Int.ofNat 626888429535,
  Int.ofNat 1253763558300, Int.ofNat 377171678333, Int.ofNat 583395314322,
  Int.negSucc 110375001361, Int.negSucc 377571461398, Int.ofNat 786121030859,
  Int.ofNat 1547230867644, Int.negSucc 292890044115, Int.negSucc 562876324810,
  Int.ofNat 406268024560, Int.ofNat 732760779643, Int.ofNat 515287527119,
  Int.ofNat 834850504141, Int.negSucc 616473871888, Int.negSucc 1070165483223,
  Int.ofNat 382449853588, Int.ofNat 436691887987, Int.ofNat 1078275138542,
  Int.ofNat 184420856912, Int.negSucc 975035357949, Int.negSucc 2903963627061 ]
private def lm2R256V8P3 : List ℤ := [
  Int.negSucc 3249289565335, Int.negSucc 1273301375918, Int.negSucc 1682242346905,
  Int.negSucc 2319883057581, Int.negSucc 1935125166226, Int.negSucc 3497444758742,
  Int.negSucc 3591013684754, Int.negSucc 2797823070851, Int.negSucc 1853012610479,
  Int.negSucc 2136517163919, Int.negSucc 2923380596928, Int.negSucc 3601394251861,
  Int.negSucc 1134298786761, Int.negSucc 887841159513, Int.negSucc 4330911101953,
  Int.negSucc 3133443167974, Int.negSucc 1503384404590, Int.negSucc 2070838527712,
  Int.ofNat 8278039674597, Int.ofNat 7427806839937, Int.negSucc 5495976398725,
  Int.ofNat 1750693674123, Int.ofNat 1884062782405, Int.ofNat 2714735873096,
  Int.negSucc 1573210866946, Int.ofNat 3417557791406, Int.ofNat 4880199157640,
  Int.negSucc 5641911100728, Int.ofNat 1699523801573, Int.ofNat 6063121719817,
  Int.ofNat 4125523878573, Int.ofNat 4677680134106, Int.negSucc 1629668172598,
  Int.ofNat 785928655575, Int.negSucc 1734305724867, Int.negSucc 8762998090651,
  Int.negSucc 58222159589, Int.ofNat 2321774627787, Int.negSucc 5763308215662,
  Int.negSucc 5502759945510, Int.negSucc 9647500995273, Int.negSucc 1845388851319,
  Int.negSucc 3294296945794, Int.negSucc 10992072146818, Int.ofNat 3982950345834,
  Int.ofNat 1653796209973, Int.negSucc 1114319685447, Int.ofNat 787280129527 ]
private def lm2R256V8P4 : List ℤ := [
  Int.negSucc 1306660172957, Int.negSucc 3586491599687, Int.ofNat 5234834842933,
  Int.ofNat 1268318483957, Int.ofNat 16720278282308, Int.ofNat 13740106925875,
  Int.ofNat 1214395203687, Int.ofNat 14815241236492, Int.ofNat 17260723454479,
  Int.ofNat 13298309358959, Int.ofNat 1157196224679, Int.negSucc 5432875318743,
  Int.negSucc 16791845909932, Int.negSucc 17485340210485, Int.ofNat 1908253158678,
  Int.negSucc 12312862594118, Int.negSucc 12022546758833, Int.ofNat 2197147529965,
  Int.negSucc 8867309089092, Int.negSucc 13340792237207, Int.ofNat 8298032596564,
  Int.negSucc 3984222228855, Int.negSucc 7685837024605, Int.ofNat 24616485036477,
  Int.ofNat 19838018385512, Int.negSucc 6539974236627, Int.ofNat 17172739163633,
  Int.ofNat 26772374399397, Int.negSucc 2850081587571, Int.ofNat 5108372487372,
  Int.ofNat 40811689657193, Int.ofNat 17557556786858, Int.negSucc 10833366949056,
  Int.ofNat 17941295134843, Int.ofNat 31723973067260, Int.ofNat 12815109144330,
  Int.negSucc 6744505595996, Int.ofNat 16201603918855, Int.ofNat 36636226543599,
  Int.negSucc 10738348492507, Int.negSucc 5522601403920, Int.ofNat 42324309780713,
  Int.ofNat 52592905541840, Int.ofNat 28836156884761, Int.negSucc 1057861712530,
  Int.negSucc 740202477461, Int.ofNat 54196680912144, Int.ofNat 107249698719727 ]
private def lm2R256V8P5 : List ℤ := [
  Int.ofNat 89886793238111, Int.ofNat 10522599433520, Int.negSucc 41604853585756,
  Int.ofNat 15363707366767, Int.ofNat 177221299382998, Int.ofNat 361558879957553,
  Int.ofNat 480534210077757, Int.ofNat 496138519854060, Int.ofNat 423722582384479,
  Int.ofNat 306136231030138, Int.ofNat 187731892586060, Int.ofNat 97171223584272,
  Int.ofNat 41976616322747, Int.ofNat 14865008417852, Int.ofNat 4185587282668,
  Int.ofNat 883520622856, Int.ofNat 120934671335 ]
private def lm2R256V8 : List ℤ :=
  lm2R256V8P0 ++ (lm2R256V8P1 ++ (lm2R256V8P2 ++
    (lm2R256V8P3 ++ (lm2R256V8P4 ++ lm2R256V8P5))))
private def lm2Anc0 : List DickeSol.RampKick128kAnchor := [
  ⟨3, lm2SegsR3, lm2RowR3⟩, ⟨4, lm2SegsR4, lm2RowR4⟩, ⟨5, lm2SegsR5, lm2RowR5⟩,
  ⟨6, lm2SegsR6, lm2RowR6⟩, ⟨7, lm2SegsR7, lm2RowR7⟩, ⟨8, lm2SegsR8, lm2RowR8⟩,
  ⟨9, lm2SegsR9, lm2RowR9⟩, ⟨10, lm2SegsR10, lm2RowR10⟩, ⟨11, lm2SegsR11, lm2RowR11⟩,
  ⟨12, lm2SegsR12, lm2RowR12⟩, ⟨15, lm2SegsR15, lm2RowR15⟩, ⟨16, lm2SegsR16, lm2RowR16⟩,
  ⟨18, lm2SegsR18, lm2RowR18⟩, ⟨22, lm2SegsR22, lm2RowR22⟩, ⟨25, lm2SegsR25, lm2RowR25⟩,
  ⟨29, lm2SegsR29, lm2RowR29⟩, ⟨31, lm2SegsR31, lm2RowR31⟩ ]
private def lm2Anc1 : List DickeSol.RampKick128kAnchor := [
  ⟨34, lm2SegsR34, lm2RowR34⟩, ⟨36, lm2SegsR36, lm2RowR36⟩, ⟨40, lm2SegsR40, lm2RowR40⟩,
  ⟨41, lm2SegsR41, lm2RowR41⟩, ⟨43, lm2SegsR43, lm2RowR43⟩, ⟨46, lm2SegsR46, lm2RowR46⟩,
  ⟨47, lm2SegsR47, lm2RowR47⟩, ⟨49, lm2SegsR49, lm2RowR49⟩, ⟨51, lm2SegsR51, lm2RowR51⟩,
  ⟨54, lm2SegsR54, lm2RowR54⟩, ⟨56, lm2SegsR56, lm2RowR56⟩, ⟨58, lm2SegsR58, lm2RowR58⟩,
  ⟨59, lm2SegsR59, lm2RowR59⟩, ⟨61, lm2SegsR61, lm2RowR61⟩, ⟨66, lm2SegsR66, lm2RowR66⟩,
  ⟨68, lm2SegsR68, lm2RowR68⟩, ⟨70, lm2SegsR70, lm2RowR70⟩, ⟨72, lm2SegsR72, lm2RowR72⟩,
  ⟨74, lm2SegsR74, lm2RowR74⟩, ⟨76, lm2SegsR76, lm2RowR76⟩, ⟨78, lm2SegsR78, lm2RowR78⟩,
  ⟨80, lm2SegsR80, lm2RowR80⟩, ⟨82, lm2SegsR82, lm2RowR82⟩, ⟨84, lm2SegsR84, lm2RowR84⟩,
  ⟨86, lm2SegsR86, lm2RowR86⟩, ⟨88, lm2SegsR88, lm2RowR88⟩, ⟨90, lm2SegsR90, lm2RowR90⟩,
  ⟨92, lm2SegsR92, lm2RowR92⟩, ⟨122, lm2SegsR122, lm2RowR122⟩ ]
private def lm2k256Anchors : List DickeSol.RampKick128kAnchor :=
  lm2Anc0 ++ (lm2Anc1 ++ [⟨256, lm2SegsR256, lm2RowR256⟩])

private theorem lm2Batch0 : lm2AtF [
    DickeSol.rkm128kCheckTable 2 256 250 true lm2k256VPot lm2k256Anchors,
    lm2ChkCell 256 250 483770197151367 1000000000000000 lm2k256VPot lm2k256Anchors,
    lm2SegBds 256 lm2SegsR256, lm2ChkAnchors lm2Anc0
  ] = true := by decide +kernel
private theorem lm2Batch1 : lm2ChkAnchors lm2Anc1 = true := by decide +kernel
private theorem lm2Batch2 :
    lm2ChkSeg 256 lm2R256C0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (88, 176, 17832754, lm2R256V1) = true := by decide +kernel
private theorem lm2Batch3 :
    lm2ChkSeg 256 lm2R256C1 88 176 17832754 lm2R256V1
      (125, 250, 25468298, lm2R256V2) = true := by decide +kernel
private theorem lm2Batch4 :
    lm2ChkSeg 256 lm2R256C2 125 250 25468298 lm2R256V2
      (152, 256, 32282404, lm2R256V3) = true := by decide +kernel
private theorem lm2Batch5 :
    lm2ChkSeg 256 lm2R256C3 152 256 32282404 lm2R256V3
      (178, 256, 38773783, lm2R256V4) = true := by decide +kernel
private theorem lm2Batch6 :
    lm2ChkSeg 256 lm2R256C4 178 256 38773783 lm2R256V4
      (204, 256, 47105597, lm2R256V5) = true := by decide +kernel
private theorem lm2Batch7 :
    lm2ChkSeg 256 lm2R256C5 204 256 47105597 lm2R256V5
      (222, 256, 55124298, lm2R256V6) = true := by decide +kernel
private theorem lm2Batch8 :
    lm2ChkSeg 256 lm2R256C6 222 256 55124298 lm2R256V6
      (236, 256, 62684475, lm2R256V7) = true := by decide +kernel
private theorem lm2Batch9 :
    lm2ChkSeg 256 lm2R256C7 236 256 62684475 lm2R256V7
      (246, 256, 68310105, lm2R256V8) = true := by decide +kernel
private theorem lm2Batch10 :
    lm2ChkFin 256 lm2R256C8 246 256 68310105 lm2R256V8 lm2RowR256 = true := by decide +kernel

private theorem lm2Row256Sound :
    DickeSol.rkm128kEvalRowLo12 2 250 256 lm2SegsR256 = lm2RowR256 := by
  apply lm2CertSplit (lm2_hd (lm2_tl2 lm2Batch0)); unfold lm2SegsR256
  exact lm2TailStep lm2Batch2 (lm2TailStep lm2Batch3 (lm2TailStep lm2Batch4
    (lm2TailStep lm2Batch5 (lm2TailStep lm2Batch6 (lm2TailStep lm2Batch7
      (lm2TailStep lm2Batch8 (lm2TailStep lm2Batch9 (lm2TailEnd lm2Batch10))))))))
private theorem lm2AncSound :
    DickeSol.RampKick128kAnchorsSound 2 250 lm2k256Anchors :=
  lm2ChkAnchors_append (lm2_hd (lm2_tl1 (lm2_tl2 lm2Batch0)))
    (lm2ChkAnchors_append lm2Batch1 ⟨lm2Row256Sound, trivial⟩)
private theorem lm2k256Valid :
    DickeSol.RampKick128kTableValid 2 256 250 true lm2k256VPot lm2k256Anchors :=
  DickeSol.rkm128kCheckTable_sound lm2AncSound (lm2_hd lm2Batch0)
private theorem lm2k256CellChecks {m k : ℕ} (h : isLowM2K256KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (lowM2K256KrotovCertCellLMax m k)
        lm2k256Anchors = true ∧
      ∃ num den : ℕ, relCostLowM2K256KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (lm2k256VPot.getD k 0) num den = true := by
  unfold isLowM2K256KrotovCertCell at h
  split_ifs at h with hm2 hk256
  simp only [beq_iff_eq] at hm2 hk256
  subst hm2 hk256; have hm := lm2_hd (lm2_tl1 lm2Batch0)
  exact ⟨lm2_and_l hm, 483770197151367, 1000000000000000, rfl, lm2_and_r hm⟩

private lemma lm2k256_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma lm2k256_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma lm2k256_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl
private lemma lm2k256_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d
private lemma lm2k256_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lm2k256_le_of_add h), rfl⟩

private structure Lm2k256CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk256 : k ≤ 256
  hm2 : 2 ≤ m
  hl2 : 2 ≤ lowM2K256KrotovCertCellLMax m k
  hl1 : 1 ≤ lowM2K256KrotovCertCellLMax m k
  hlm : lowM2K256KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 256 250 true lm2k256VPot lm2k256Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM2K256KrotovCertCellLMax m k) lm2k256Anchors = true
  hcost : ∃ num den : ℕ, relCostLowM2K256KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (lm2k256VPot.getD k 0) num den = true

private lemma lm2k256_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hj : (j + 1) + d1 = 11)
    (h256 : k + dk = 256) (hl2 : 2 + dl2 = lowM2K256KrotovCertCellLMax 2 k)
    (hl1 : 1 + dl1 = lowM2K256KrotovCertCellLMax 2 k)
    (hlm : lowM2K256KrotovCertCellLMax 2 k * 2 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (lowM2K256KrotovCertCellLMax 2 k)
      lm2k256Anchors = true)
    (hcost : ∃ num den : ℕ, relCostLowM2K256KrotovCert 2 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 2 k (lm2k256VPot.getD k 0) num den = true) :
    Lm2k256CellProps 2 k :=
  ⟨lm2k256_mem_grid 1 9 rfl, hk ▸ lm2k256_mem_grid j d1 hj, lm2k256_le_of_add h256, le_rfl,
    lm2k256_le_of_add hl2, lm2k256_le_of_add hl1, lm2k256_le_of_add hlm, lm2k256Valid, hlmax,
    hcost⟩

private theorem lm2k256_all_props {m k : ℕ} (h : isLowM2K256KrotovCertCell m k = true) :
    Lm2k256CellProps m k := by
  rcases lm2k256CellChecks h with ⟨hlmax, hcost⟩; unfold isLowM2K256KrotovCertCell at h
  split_ifs at h with hm2 hk256
  simp only [beq_iff_eq] at hm2 hk256
  subst hm2 hk256; exact lm2k256_mk 8 2 0 248 249 65036 rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def lowM2K256KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM2K256KrotovCertQubits n m k)) Var
      (lowM2K256KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isLowM2K256KrotovCertCell m k = true then
    let p := lm2k256_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm2k256VPot lm2k256Anchors p.hk256
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit on the supported (2, 256) cell. -/
noncomputable def findAllJohnsonRampKick128kLowM2K256KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ lowM2K256KrotovCertQubits n m k)) Var
      (lowM2K256KrotovCertQubits n m k) ((n + 1) * m) :=
  lowM2K256KrotovCertCircuitImpl res n m k

private lemma lm2k256_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isLowM2K256KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kLowM2K256KrotovCertCircuit res n m k =
      let p := lm2k256_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG lm2k256VPot lm2k256Anchors p.hk256
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kLowM2K256KrotovCertCircuit lowM2K256KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-1 recovery of S on the supported (2, 256) cell. -/
theorem lowM2K256KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isLowM2K256KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kLowM2K256KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [lm2k256_targetSets_eq]
  have hp := lm2k256_all_props hcell
  rw [lm2k256_circuit_eq res n hcell, ← lm2k256_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG lm2k256VPot lm2k256Anchors hp.hk256
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound on the supported (2, 256) cell. -/
theorem lowM2K256KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isLowM2K256KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kLowM2K256KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostLowM2K256KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := lm2k256_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG lm2k256VPot
    lm2k256Anchors hp.hk256 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [lm2k256_circuit_eq res n hcell, ← lm2k256_oracle_eq]
    exact hq S (by rwa [lm2k256_targetSets_eq])
  · rw [← lm2k256_targetSets_eq, ← lm2k256_vanilla_eq]; exact hsum

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

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM2K256KrCert
