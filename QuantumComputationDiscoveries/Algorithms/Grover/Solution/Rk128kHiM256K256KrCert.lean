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

namespace QuantumComputation.Specs.GroverFindAll
namespace Rk128kHiM256K256KrCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-
# Krotov `(256, 256)` Certificate (`Rk128kHiM256K256KrCert`)

QHL-verified module packaging cell `(256, 256)` over `13` anchors
(`440,582` F1272 / `443,470` Horner coord-ops at `lTableMax = 2`, `useColdR2 = true`).
-/
def isHiTailM256K256KrotovCertCell (m k : ℕ) : Bool :=
  if m == 256 then
    if k == 256 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor L_max(256, 256) = 2 (2 * 256 = 512 <= 65536). -/
def hiTailM256K256KrotovCertCellLMax (m k : ℕ) : ℕ :=
  if m == 256 then
    if k == 256 then 2
    else 1
  else 1

/-- Total register qubit budget (hiTailM256K256KrotovCertCellLMax m k * m) * (n + 1) + k *
  n. -/
abbrev hiTailM256K256KrotovCertQubits (n m k : ℕ) : ℕ :=
  (hiTailM256K256KrotovCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified coprime relative-cost profile c(256, 256): ℚ≥0. -/
def relCostHiTailM256K256KrotovCert (m k : ℕ) : ℚ≥0 :=
  if m == 256 then
    if k == 256 then NNRat.divNat 48827154462093 1000000000000000
    else 1
  else 1

/-- Cost profile metadata (n0 = 80000, constructive threshold). -/
def hiTailM256K256KrotovCertProfile : FindAllCostProfile :=
  ⟨isHiTailM256K256KrotovCertCell, relCostHiTailM256K256KrotovCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kHiM256K256KrCert` cell lies on groverGrid × groverGrid. -/
theorem isHiTailM256K256KrotovCertCell_isGridCell {m k : ℕ}
    (h : isHiTailM256K256KrotovCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isHiTailM256K256KrotovCertCell at h
  split_ifs at h with hm256 hk256
  simp only [beq_iff_eq] at hm256 hk256
  subst hm256 hk256; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def hm2NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem hm2NatEq_eq {x y : ℕ} (h : hm2NatEq x y = true) : x = y := by
  unfold hm2NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def hm2IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => hm2NatEq m n
  | Int.negSucc m, Int.negSucc n => hm2NatEq m n
  | _, _ => false
private theorem hm2IntEq_eq {a b : ℤ} (h : hm2IntEq a b = true) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [hm2IntEq] at h; exact congrArg Int.ofNat (hm2NatEq_eq h)
    | negSucc _ => cases h
  | negSucc m =>
    cases b with
    | ofNat _ => cases h
    | negSucc n => dsimp only [hm2IntEq] at h; exact congrArg Int.negSucc (hm2NatEq_eq h)
private def hm2ListEq {α : Type} (eqF : α → α → Bool) (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (eqF x y) (hm2ListEq eqF xr yr) false
  | _, _ => false
private theorem hm2ListEq_eq {α : Type} {eqF : α → α → Bool}
    (heq : ∀ {a b : α}, eqF a b = true → a = b) {xs ys : List α}
    (h : hm2ListEq eqF xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [hm2ListEq] at h; cases hxy : eqF x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (heq hxy) (ih h)
private abbrev Hm2St := ℕ × ℕ × ℕ × List ℤ
private def hm2StEq (a b : Hm2St) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (hm2NatEq a1 b1)
      (cond (hm2NatEq a2 b2)
        (cond (hm2NatEq a3 b3) (hm2ListEq hm2IntEq av bv) false) false) false
private theorem hm2StEq_eq {a b : Hm2St} (h : hm2StEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩; dsimp only [hm2StEq] at h
  cases h1 : hm2NatEq a1 b1 with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h; dsimp only [cond] at h; cases h2 : hm2NatEq a2 b2 with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h; dsimp only [cond] at h; cases h3 : hm2NatEq a3 b3 with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h; dsimp only [cond] at h; exact Prod.ext (hm2NatEq_eq h1)
          (Prod.ext (hm2NatEq_eq h2)
            (Prod.ext (hm2NatEq_eq h3) (hm2ListEq_eq (@hm2IntEq_eq) h)))
private def hm2AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (hm2AtF rest) false
private theorem hm2_hd {b : Bool} {bs : List Bool} (h : hm2AtF (b :: bs) = true) :
    b = true := by
  unfold hm2AtF at h; cases b with
  | false => cases h
  | true => rfl
private theorem hm2_tl1 {b : Bool} {s : List Bool} (h : hm2AtF (b :: s) = true) :
    hm2AtF s = true := by
  unfold hm2AtF at h; cases b with
  | false => cases h
  | true => exact h
private theorem hm2_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : hm2AtF (b1 :: b2 :: bs) = true) : hm2AtF bs = true := hm2_tl1 (hm2_tl1 h)
private theorem hm2_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem hm2_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private abbrev hm2M (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def hm2ChkRow (r : ℕ) (s : List DickeSol.Rkm128kSeg) (ro : List ℕ) : Bool :=
  hm2ListEq hm2NatEq (DickeSol.rkm128kEvalRowLo12 256 2 r s) ro
private def hm2ChkAnchors (xs : List DickeSol.RampKick128kAnchor) : Bool :=
  match xs with
  | [] => true
  | a :: rest =>
    match a with
    | ⟨rAct, segs, row⟩ => cond (hm2ChkRow rAct segs row) (hm2ChkAnchors rest) false
private theorem hm2ChkAnchors_append {xs rest : List DickeSol.RampKick128kAnchor}
    (hxs : hm2ChkAnchors xs = true) (hrest : DickeSol.RampKick128kAnchorsSound 256 2 rest) :
    DickeSol.RampKick128kAnchorsSound 256 2 (xs ++ rest) := by
  induction xs with
  | nil => exact hrest
  | cons a tl ih =>
    rcases a with ⟨rAct, segs, row⟩; rw [List.cons_append]
    dsimp only [hm2ChkAnchors, DickeSol.RampKick128kAnchorsSound] at hxs ⊢
    cases ha : hm2ChkRow rAct segs row with
    | false => rw [ha] at hxs; cases hxs
    | true =>
      rw [ha] at hxs; dsimp only [cond] at hxs
      exact ⟨hm2ListEq_eq (@hm2NatEq_eq) ha, ih hxs⟩
private def hm2ChkSeg (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (st1 : Hm2St) : Bool := hm2StEq (DickeSol.rkm128kRunSegs 256 2 r s l0 d0 p0 v0) st1
private def hm2ChkFin (r : ℕ) (s : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Bool :=
  hm2ListEq hm2NatEq (DickeSol.rkm128kFinalizeState
    (DickeSol.rkm128kRunSegs 256 2 r s l0 d0 p0 v0)) ro
private def hm2SegBds (r : ℕ) (s : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen s))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen s) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def hm2TailOk (r : ℕ) (rest : List DickeSol.Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (ro : List ℕ) : Prop :=
  ∃ st, DickeSol.rkm128kRunSegs 256 2 r rest l0 d0 p0 v0 = st ∧
    DickeSol.rkm128kFinalizeState st = ro
private theorem hm2TailEnd {r : ℕ} {cLast : List DickeSol.Rkm128kSeg} {l0 d0 p0 : ℕ}
    {v0 : List ℤ} {ro : List ℕ} (h : hm2ChkFin r cLast l0 d0 p0 v0 ro = true) :
    hm2TailOk r cLast l0 d0 p0 v0 ro := ⟨_, rfl, hm2ListEq_eq (@hm2NatEq_eq) h⟩
private theorem hm2TailStep {r : ℕ} {cCur rest : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {ro : List ℕ}
    (h1 : hm2ChkSeg r cCur l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : hm2TailOk r rest l1 d1 p1 v1 ro) : hm2TailOk r (cCur ++ rest) l0 d0 p0 v0 ro := by
  rcases h2 with ⟨st, hr, hf⟩; refine ⟨st, ?_, hf⟩
  unfold hm2ChkSeg at h1; rw [DickeSol.rkm128kRunSegs_append, hm2StEq_eq h1]; exact hr
private theorem hm2CertSplit {r : ℕ} {segs : List DickeSol.Rkm128kSeg} {ro : List ℕ}
    (hb : hm2SegBds r segs = true)
    (ht : hm2TailOk r segs 1 0 1 [Int.ofNat DickeSol.wdScale] ro) :
    DickeSol.rkm128kEvalRowLo12 256 2 r segs = ro := by
  rcases ht with ⟨st, hr, hf⟩; exact DickeSol.rkm128kCertRow_of_runSegs hb hr hf
private def hm2ChkCell (k lm n d : ℕ) (v : List ℕ)
    (a : List DickeSol.RampKick128kAnchor) : Bool :=
  Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
    (DickeSol.checkAltBound12 256 k (v.getD k 0) n d)

private def hm256k256VPotP0 : List ℕ := [
  0, 40168692606171, 43079728286639, 47102765062732, 47677275849084, 48039248628592,
  48296248952724, 48493824159763, 48654627253465, 48791077257005, 48910696995711,
  61022013513329, 49116564828004, 60257355663381, 49293991589116, 59665503422625,
  69707676574168, 79450015542298, 88917867186705, 98133197279571, 49745438882140,
  58510966236197, 67074960274901, 75450711677116, 50015268967814, 58049007489049,
  65926736236525, 73657204732915, 81248374099096, 88707513056729, 96041279405360,
  103255789572912, 110356678306218, 117349150157906, 124238024106889, 131027772399487,
  137722554500516, 144326246886351, 150842469285889, 157274607873680, 163625835837014,
  169899131671467, 176097295504197, 182222963698768, 188278621957577, 194266617106557,
  200189167720596, 206048373726077 ]
private def hm256k256VPotP1 : List ℕ := [
  211846225098369, 217584609756394, 223265320743039, 228890062768826, 234460458186515,
  239978052455981, 245444319151527, 250860664557609, 256228431893571, 261548905203359,
  266823312942114, 272052831288035, 277238587204790, 282381661277068, 287483090339484,
  292543869916938, 297564956492710, 302547269618912, 307491693882496, 312399080738712,
  317270250222777, 322105992549511, 326907069609757, 331674216371620, 336408142193824,
  341109532057819, 345779047724713, 350417328822547, 355024993868980, 359602641234010,
  364150850046969, 368670181051691, 373161177413426, 377624365480779, 382060255505710,
  386469342324380, 390852106001409, 395209012439926, 399540513959606, 403847049844719,
  408129046864071, 412386919764588, 416621071740144, 420831894877144, 425019770578252,
  429185069965560, 433328154264405, 437449375168955 ]
private def hm256k256VPotP2 : List ℕ := [
  441549075190615, 445627587990226, 449685238694972, 453722344200845, 457739213461463,
  461736147763989, 465713440992848, 469671379881893, 473610244255631, 477530307260092,
  481431835583867, 485315089669832, 489180323918027, 493027786880143, 496857721446032,
  500670365022640, 504465949705731, 508244702444763, 512006845201236, 515752595100835,
  519482164579652, 523195761524778, 526893589409519, 530575847423486, 534242730597802,
  537894429925636, 541531132478289, 545153021517017, 548760276600793, 552353073690181,
  555931585247489, 559495980333372, 563046424700025, 566583080881127, 570106108278660,
  573615663246739, 577111899172583, 580594966554740, 584065013078676, 587522183689846,
  590966620664338, 594398463677194, 597817849868499, 601224913907327, 604619788053626,
  608002602218128, 611373484020353, 614732558844788 ]
private def hm256k256VPotP3 : List ℕ := [
  618079949895303, 621415778247880, 624740162901713, 628053220828737, 631355067021655,
  634645814540505, 637925574557833, 641194456402516, 644452567602285, 647700013924995,
  650936899418688, 654163326450490, 657379395744386, 660585206417906, 663780856017772,
  666966440554527, 670142054536194, 673307791000989, 676463741549125, 679609996373739,
  682746644290966, 685873772769192, 688991467957514, 692099814713432, 695198896629797,
  698288796061041, 701369594148712, 704441370846334, 707504204943620, 710558174090049,
  713603354817836, 716639822564309, 719667651693714, 722686915518464, 725697686319850,
  728700035368232, 731694032942722, 734679748350379, 737657249944929, 740626605145021,
  743587880452041, 746541141467486, 749486452909924, 752423878631538, 755353481634279,
  758275324085632, 761189467334007, 764095971923770 ]
private def hm256k256VPotP4 : List ℕ := [
  766994897609916, 769886303372407, 772770247430168, 775646787254768, 778515979583781,
  781377880433842, 784232545113410, 787080028235238, 789920383728561, 792753664851015,
  795579924200288, 798399213725513, 801211584738407, 804017087924168, 806815773352134,
  809607690486206, 812392888195051, 815171414762079, 817943317895212, 820708644736439,
  823467441871172, 826219755337401, 828965630634657, 831705112732791, 834438246080564,
  837165074614063, 839885641764940, 842599990468483, 845308163171524, 848010201840182,
  850706147967449, 853396042580626, 856079926248607, 858757839089019, 861429820775216,
  864095910543137, 866756147198031, 869410569121044, 872059214275679, 874702120214134,
  877339324083512, 879970862631912, 882596772214404, 885217088798890, 887831847971851,
  890441084943985, 893044834555740, 895643131282741 ]
private def hm256k256VPotP5 : List ℕ := [
  898236009241119, 900823502192732, 903405643550298, 905982466382428, 908554003418567,
  911120287053844, 913681349353834, 916237222059231, 918787936590439, 921333524052079,
  923874015237413, 926409440632691, 928939830421418, 931465214488549, 933985622424605,
  936501083529717, 73272216610283 ]
private def hm256k256VPot : List ℕ :=
  hm256k256VPotP0 ++ (hm256k256VPotP1 ++ (hm256k256VPotP2 ++
    (hm256k256VPotP3 ++ (hm256k256VPotP4 ++ hm256k256VPotP5))))
private def hm2SegsR3 : List DickeSol.Rkm128kSeg := [
  ⟨1, 44919386, 1, 23, []⟩ ]
private def hm2RowR3 : List ℕ := [
  805872816, 53487342527, 945703692259 ]
private def hm2SegsR4 : List DickeSol.Rkm128kSeg := [
  ⟨1, 46063982, 1, 29, []⟩ ]
private def hm2RowR4 : List ℕ := [
  805341, 402591115, 39730233379, 959866351966 ]
private def hm2SegsR5 : List DickeSol.Rkm128kSeg := [
  ⟨1, 37014165, 1, 29, []⟩, ⟨1, 9744260, 1, 13, []⟩ ]
private def hm2RowR5 : List ℕ := [
  1854, 34250, 201190869, 31670173555, 968128490964 ]
private def hm2SegsR6 : List DickeSol.Rkm128kSeg := [
  ⟨1, 16831441, 1, 19, []⟩, ⟨1, 17069434, 1, 19, []⟩, ⟨1, 5713791, 1, 12, []⟩,
  ⟨1, 3094959, 1, 10, []⟩, hm2M 1 2264590 1 8 1 [1], hm2M 1 1379868 1 6 3 [6],
  hm2M 1 718544 1 6 4 [12], ⟨1, 160275, 1, 4, []⟩ ]
private def hm2RowR6 : List ℕ := [
  39, 1, 456, 93636168, 26371201202, 973534821861 ]
private def hm2SegsR7 : List DickeSol.Rkm128kSeg := [
  ⟨1, 20902411, 1, 25, []⟩, ⟨1, 20967411, 1, 25, []⟩, ⟨1, 1904582, 1, 8, []⟩,
  hm2M 1 1333212 1 8 2 [2], hm2M 1 597294 1 6 3 [4], hm2M 1 711306 1 6 4 [8],
  hm2M 1 778246 1 6 5 [18], ⟨1, 389118, 1, 4, []⟩ ]
private def hm2RowR7 : List ℕ := [
  0, 0, 0, 9534, 36216392, 22621472063, 977342125478 ]
private def hm2SegsR8 : List DickeSol.Rkm128kSeg := [
  ⟨1, 12441876, 1, 19, []⟩, ⟨1, 6147863, 1, 13, []⟩, ⟨1, 5164425, 1, 12, []⟩,
  ⟨1, 4338553, 1, 12, []⟩, ⟨1, 3643887, 1, 10, []⟩, ⟨1, 2833993, 1, 10, []⟩,
  ⟨1, 2379542, 1, 8, []⟩, ⟨1, 2161857, 1, 8, []⟩, ⟨1, 1678628, 1, 8, []⟩,
  ⟨1, 1299917, 1, 8, []⟩, ⟨1, 1184402, 1, 6, []⟩, ⟨1, 1074249, 1, 6, []⟩,
  hm2M 1 835822 1 6 3 [6], hm2M 1 414945 1 6 4 [10], hm2M 1 51339 1 4 4 [10],
  hm2M 1 182034 1 4 4 [10], hm2M 1 590078 1 6 5 [20], hm2M 1 381777 1 6 5 [20],
  hm2M 1 314517 1 4 6 [40], hm2M 1 112985 1 4 6 [48], hm2M 1 23813 1 4 1 [1],
  hm2M 1 74200 1 4 6 [48], hm2M 1 118418 1 4 6 [40], hm2M 1 71207 1 4 6 [40],
  hm2M 1 67113 1 4 6 [40], hm2M 1 67158 1 4 5 [24], hm2M 1 12268 1 4 6 [40],
  hm2M 1 59701 1 4 6 [48], hm2M 1 61117 1 4 6 [48], hm2M 1 37357 1 4 6 [48],
  hm2M 1 24606 1 4 6 [48], ⟨1, 8135, 1, 4, []⟩ ]
private def hm2RowR8 : List ℕ := [
  0, 0, 0, 0, 25, 8476768, 19827554113, 980163287779 ]
private def hm2SegsR9 : List DickeSol.Rkm128kSeg := [
  ⟨1, 21465057, 1, 28, []⟩, ⟨1, 22402660, 1, 29, []⟩, ⟨1, 404592, 1, 6, []⟩,
  hm2M 1 901213 1 6 4 [8], hm2M 1 602695 1 6 5 [16], hm2M 1 700207 1 6 6 [48],
  hm2M 1 864748 1 6 7 [96], ⟨1, 740274, 1, 6, []⟩ ]
private def hm2RowR9 : List ℕ := [
  0, 0, 0, 1, 0, 17035, 35008, 17665968413, 982333772709 ]
private def hm2SegsR10 : List DickeSol.Rkm128kSeg := [
  ⟨1, 21713584, 1, 31, []⟩, hm2M 1 22402788 1 31 3 [4], ⟨1, 344612, 1, 6, []⟩,
  hm2M 1 721737 1 6 5 [16], hm2M 1 636215 1 6 6 [56], hm2M 1 698927 1 6 7 [80],
  hm2M 1 887372 1 6 8 [224], ⟨1, 864801, 1, 6, []⟩ ]
private def hm2RowR10 : List ℕ := [
  0, 0, 0, 0, 1, 1, 2263, 5116064, 15943507346, 984051156689 ]
private def hm2SegsR12 : List DickeSol.Rkm128kSeg := [
  ⟨1, 20386171, 1, 32, []⟩, ⟨1, 21888871, 1, 35, []⟩, ⟨1, 2085265, 1, 10, []⟩,
  hm2M 1 2369681 1 10 9 [464], hm2M 1 1629666 1 8 11 [1744], ⟨1, 220064, 1, 4, []⟩ ]
private def hm2RowR12 : List ℕ := [
  0, 0, 0, 0, 3, 125, 170, 158226, 5010656, 1427079, 13356889134, 986636301534 ]
private def hm2SegsR14 : List DickeSol.Rkm128kSeg := [
  ⟨1, 21225065, 1, 40, []⟩, ⟨1, 21717111, 1, 40, []⟩, hm2M 1 1949570 1 11 8 [192],
  hm2M 1 1852722 1 11 11 [1952], hm2M 1 793298 1 8 12 [2560], hm2M 1 436170 1 6 12 [2944],
  hm2M 1 540780 1 7 13 [4384], ⟨1, 316199, 1, 6, []⟩ ]
private def hm2RowR14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 31, 3, 11712, 832, 1238, 4442161, 11523506319, 988472031531 ]
private def hm2SegsR20 : List DickeSol.Rkm128kSeg := [
  ⟨1, 20623614, 2, 28, []⟩, ⟨1, 22604094, 2, 29, []⟩, hm2M 1 1899461 1 10 14 [15360],
  hm2M 1 1215708 1 8 16 [52224], hm2M 1 1557226 1 10 18 [204800], hm2M 1 347964 1 6 15 [17664],
  hm2M 1 653437 1 6 19 [285696], ⟨1, 511991, 1, 6, []⟩ ]
private def hm2RowR20 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 40, 1479, 860822, 195421, 14196222, 8246401577,
  991737989580 ]
private def hm2SegsR24 : List DickeSol.Rkm128kSeg := [
  ⟨1, 22784895, 2, 33, []⟩, hm2M 1 22503395 2 33 18 [237568], hm2M 1 612690 1 6 19 [335872],
  hm2M 1 1345713 1 10 21 [1798144], hm2M 1 921198 1 8 22 [2127872],
  hm2M 1 974485 1 8 23 [4472832], hm2M 1 590921 1 6 21 [1064960], ⟨2, 8, 1, 4, []⟩ ]
private def hm2RowR24 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 743, 90778, 1177, 944295, 19656984,
  6996156208, 992982805640 ]
private def hm2R256C0 : List DickeSol.Rkm128kSeg := [
  hm2M 1 907384 1 15 65 [69410244647714816, 277],
  hm2M 1 907384 1 15 128 [3157797394972672, 71007879165672193, 49603],
  hm2M 1 907385 1 15 196 [6755399441055744, 34734136864624832, 42673415165288762, 222137262],
  hm2M 1 907396 1 15 256 [
    0, 3511933162699847, 52755116347813712, 70024602323143006, 2979160681],
  hm2M 1 922255 1 15 255 [
    0, 18054123014322176, 69057760980910961, 18659076329455852, 1782418337],
  hm2M 1 468219 1 11 257 [
    72057594037927935, 139492678172671, 20043957965404416, 38171285364628745, 5296683353],
  hm2M 1 468576 1 11 256 [
    72057594037927935, 11168212049723391, 27986479235255776, 67391860210252817, 2776655115],
  hm2M 1 468591 1 11 257 [
    72057594037927935, 29730794415063039, 28201204306213859, 43695889943849021, 8028486718],
  hm2M 1 468605 1 11 256 [
    72057594037927935, 40813871623045119, 15407692669400478, 19678724200557758, 3967043178],
  hm2M 1 468636 1 11 257 [
    72057594037927935, 15903336184152063, 10045289755062960, 21371205079068795, 6153227098],
  hm2M 1 468652 1 11 256 [
    72057594037927935, 37154696925806591, 51393029486527118, 45798005181984984, 3860997908],
  hm2M 1 468678 1 11 256 [0, 0, 59646088631353088, 6048375855677062, 3307725186],
  hm2M 1 907730 1 15 255 [
    72057594037927935, 72057594037927935, 67149886880739391, 60511759701713195, 1445826434]
  ]
private def hm2R256C1 : List DickeSol.Rkm128kSeg := [
  hm2M 1 907834 1 15 257 [
    36028797018963967, 0, 16374121099821952, 70732516545195718, 7830318460],
  hm2M 1 907922 1 21 255 [
    0, 72057594037927904, 11242074519175167, 48815570351073493, 1358408534],
  hm2M 1 907984 1 21 254 [
    72057594037927935, 72057594037927935, 3917573065408511, 42190278694055149, 950083722],
  hm2M 1 453940 1 13 257 [0, 0, 46985947450966016, 19020698125610102, 7688707076],
  hm2M 1 472923 1 13 257 [
    72057594037927931, 72057594037927935, 62842600507310079, 56854453118309475, 5367880490],
  hm2M 1 472933 1 14 257 [11, 0, 30019884234571776, 27493751010009009, 8226126674],
  hm2M 1 472942 1 14 257 [61, 0, 65826391060381696, 35313793616976452, 5032802907],
  hm2M 1 472949 1 14 255 [102, 0, 15386733222821888, 16529146800037385, 1394575948],
  hm2M 1 472947 1 14 257 [
    72057594037927931, 72057594037927935, 65754781070655487, 43257600499772318, 5416142893],
  hm2M 1 473007 1 14 257 [997, 0, 37928753111760896, 31553388718004931, 8534062917],
  hm2M 1 473043 1 14 257 [
    72057594037922756, 72057594037927935, 72057594037927935, 10367995067646831, 4423736445]
  ]
private def hm2R256C2 : List DickeSol.Rkm128kSeg := [
  hm2M 1 473224 1 14 257 [118832, 0, 0, 27325305082855168, 6308172570],
  hm2M 1 907862 1 21 256 [2644754, 0, 0, 36069932411783136, 3256092263],
  hm2M 1 907930 1 22 252 [39660026, 0, 0, 36478762125114880, 183634313],
  hm2M 1 908093 1 22 256 [1249603842, 0, 0, 35304050904653824, 2519540146],
  hm2M 1 908421 1 22 255 [
    72057519927671594, 72057594037927935, 72057594037927935, 60051888929767423, 1172729208],
  hm2M 1 908636 1 22 257 [
    72057041143831266, 72057594037927935, 72057594037927935, 28522379596529663, 4984531591],
  hm2M 1 908772 1 22 256 [75940634741562, 0, 0, 6610255316254720, 2987716760],
  hm2M 1 909123 1 22 257 [2151508150325855, 0, 0, 70906405363646464, 8113055546] ]
private def hm2R256C3 : List DickeSol.Rkm128kSeg := [
  hm2M 1 909295 1 22 257 [
    71036298487500278, 72057594037927934, 72057594037927935, 22517998136852479, 8003817271],
  hm2M 1 909558 1 22 257 [
    38361822631386231, 72057594037927900, 72057594037927935, 72057594037927935, 7149918991],
  hm2M 1 909878 1 22 250 [
    6200978458390652, 72057594037917024, 72057594037927935, 72057594037927935, 36192255],
  hm2M 1 910258 1 22 256 [37859945785804233, 1729981, 0, 17592186044416, 2835316736],
  hm2M 1 910507 1 22 256 [
    56367738048001433, 72057593952774596, 72057594037927935, 72057594037927935, 4234149887],
  hm2M 1 910543 1 22 257 [
    21292286875966875, 72057577968359435, 72057594037927935, 72057594037665791, 8053063679],
  hm2M 1 910566 1 22 255 [52424700556379327, 1580558743214, 0, 2097152, 1207959552] ]
private def hm2R256C4 : List DickeSol.Rkm128kSeg := [
  hm2M 1 910497 1 22 255 [
    8721430079154600, 72037661422149199, 72057594037927935, 1, 1212284928],
  hm2M 1 910397 1 22 252 [67673370200935111, 8508749636444161, 0, 0, 134348800],
  hm2M 1 910819 1 22 257 [
    8064764376563267, 30500873629074412, 72057594037927933, 72057594037927167, 8447066111],
  hm2M 1 911559 1 22 248 [
    38150813839215433, 32723108710020830, 72057594037927908, 4294963199, 8388608],
  hm2M 1 455894 1 14 257 [
    48861771544161098, 53753251975799375, 72057594037927200, 72057576858075135, 8589934591],
  hm2M 1 910597 1 22 249 [51043250424293456, 52919151320604310, 113779, 131072, 16777216],
  hm2M 1 455966 1 14 253 [32170846915643704, 13674018315747279, 289692, 524288, 268500992],
  hm2M 2 413234 1 18 250 [
    20996058298270511, 11907303938625284, 8677253, 1099520016384, 35651584],
  hm2M 2 413667 1 18 257 [
    60909658495849027, 6756706079599014, 72057593151474976, 72057594037927935, 8053063679]
  ]
private def hm2R256C5 : List DickeSol.Rkm128kSeg := [
  hm2M 2 405112 1 18 255 [
    44948977865312455, 41233773425533073, 27742380007, 268435456, 1677754368],
  hm2M 2 427818 1 19 255 [
    39545110440906813, 35193097680281443, 2183761294767, 6442450944, 1074856960],
  hm2M 2 444972 1 20 257 [
    6906337231360136, 12821537178039550, 72042152620421968, 72057559678189567, 8436842495],
  hm2M 2 443756 1 20 256 [
    53009688193785458, 50365480155639272, 733055044928646, 274877906944, 2147483648],
  hm2M 2 443959 1 20 256 [65530581914563265, 3607905735601264, 9614535168930255, 0, 2181038080],
  hm2M 2 443955 1 20 257 [
    50244886297099694, 43975456358642524, 12981006726661303, 72057594037927930, 6407847931],
  hm2M 2 439878 1 20 257 [
    41899862479068349, 6856012289276373, 34817103331947238, 72057594037927632, 6366953463],
  hm2M 2 438360 1 20 257 [
    46530400537168234, 55447817397329558, 57723975994576739, 71494644084503483, 6434062335]
  ]
private def hm2R256C6 : List DickeSol.Rkm128kSeg := [
  hm2M 2 432853 1 20 256 [
    21523119298982653, 35434967325480094, 64033350501019481, 2251799813733331, 2164260992],
  hm2M 2 351883 1 17 257 [
    46994378511424978, 26753795754579525, 56952566940809386, 9007199255365192, 6442385408],
  hm2M 2 274364 1 15 250 [
    67338537052518372, 62049517068779521, 53734915432224530, 72057594032339895, 33816575],
  hm2M 2 536575 1 22 256 [
    66140289448369522, 14623277418359920, 26119922725559903, 72057593902272179, 4294967295],
  hm2M 2 499418 1 21 254 [
    46126733021710224, 63578379821372941, 1204105970986002, 2665550032, 671088640],
  hm2M 2 480020 1 21 257 [
    6078317289262265, 1056124804484286, 38784966856147396, 18829717513, 4303355904],
  hm2M 2 503691 1 22 257 [
    70231267400010309, 600612885115465, 37584731347810754, 19093884628, 4294967296],
  hm2M 2 262281 1 14 256 [
    67703505903711123, 66660630531108658, 12753934088119297, 72057540468926279, 4259315711],
  hm2M 2 519200 1 22 255 [
    37003484733713232, 52511275194223371, 68244694223708920, 60227367125439, 1073741824]
  ]
private def hm2R256C7 : List DickeSol.Rkm128kSeg := [
  hm2M 2 527818 1 22 212 [
    46706903893829623, 40006937277242937, 40136565474518616, 12096047974541],
  hm2M 2 508786 1 21 249 [
    33924890714429213, 287133747001555, 62777449584689438, 9003462827076604, 16777216],
  hm2M 2 517396 1 22 224 [
    13784757708446035, 7520894993001608, 32704324210544634, 37510526969996754],
  hm2M 2 473061 1 20 250 [
    228602169737395, 47272793056376888, 46287163247528408, 105842102293591, 33554437],
  hm2M 2 510854 1 21 251 [
    4121620300164882, 49633309004994951, 38592755514372455, 56688629717914392, 67108898],
  hm2M 2 425250 1 19 232 [
    45718898188476978, 6042924513614828, 35564801628640502, 49788212559919726, 249],
  hm2M 2 488162 1 21 226 [
    9622654104175421, 21704638671985805, 36479033156086914, 4796166765734657, 3],
  hm2M 2 528760 1 22 254 [
    64501290369445171, 11291086792317601, 4768602520408250, 15196332807, 536870912]
  ]
private def hm2R256C8 : List DickeSol.Rkm128kSeg := [
  hm2M 2 398738 1 18 239 [
    31626996733502415, 18829071212504364, 47876701748475423, 5560329585682733, 16896],
  hm2M 2 387391 1 17 226 [
    39991570195818376, 13801329301552541, 14218840983836415, 37321871538974358, 2],
  hm2M 2 365101 1 17 256 [
    15754185840364264, 41233837253556448, 34494446055590844, 18368455524643031, 2147713665],
  hm2M 2 370911 1 17 243 [
    57422971498581849, 9012087948719088, 54789157351687131, 707202107880756, 262146],
  hm2M 2 368274 1 17 240 [
    20798826674032772, 42354644680634520, 25984733146147031, 3487079098177202, 32769],
  hm2M 2 387709 1 17 256 [
    18160927755991504, 55658387642847808, 47375963679676512, 31231439098390120, 2150852745],
  hm2M 2 402175 1 18 242 [
    19197408489078476, 28251118274309645, 21695096868194960, 19233705365363596, 132160],
  hm2M 2 270559 1 14 248 [
    29228403904265486, 42563834262588467, 53709450919873221, 32305904718005239, 12269883],
  hm2M 2 321571 1 16 244 [
    1882733004255077, 35467763668222228, 62207878017294898, 290838158736953, 524288],
  hm2M 2 471126 1 20 223 [
    9827525241993263, 34055477314589307, 21384024232041996, 18808022736326306]
  ]
private def hm2R256C9 : List DickeSol.Rkm128kSeg := [
  hm2M 2 457061 1 19 228 [
    58636497899199844, 40013255995084777, 23661773621901347, 1239985150595905, 8],
  hm2M 2 384123 1 17 252 [
    57660585294634513, 42918074309892676, 42030361391100677, 12332413382472236, 246535870],
  hm2M 2 397483 1 18 229 [
    60386003832303372, 37853585603312104, 20976394233635191, 36301292748695, 16],
  hm2M 2 399061 1 18 224 [
    54015619961351084, 209690923147192, 38503082087359302, 41500801084245453],
  hm2M 2 403062 1 18 254 [
    55278837227389099, 67154872213683908, 70246496300556237, 13394431282329124, 963873723],
  hm2M 2 474375 1 20 235 [
    54680684539667107, 10076894516530611, 17276207985947680, 9139511902264485, 1028],
  hm2M 2 359666 1 16 255 [
    44226068056258477, 45016335968113569, 29167851976510453, 34952907037924711, 2145354250],
  hm2M 2 401358 1 18 222 [
    65266569950429851, 14487684382301695, 64734702732574995, 15424202269422410],
  hm2M 2 406857 1 18 237 [
    20222306362829332, 16043709293435253, 14633952643142324, 6195798102890146, 4096]
  ]
private def hm2SegsR256 : List DickeSol.Rkm128kSeg :=
  hm2R256C0 ++ (hm2R256C1 ++ (hm2R256C2 ++ (hm2R256C3 ++ (hm2R256C4 ++
    (hm2R256C5 ++ (hm2R256C6 ++ (hm2R256C7 ++ (hm2R256C8 ++ hm2R256C9))))))))
private def hm2RowR256P0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]
private def hm2RowR256P1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]
private def hm2RowR256P2 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]
private def hm2RowR256P3 : List ℕ := [
  0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 16, 5, 1, 4, 0, 46, 27, 31, 52, 8, 54, 8, 3, 24, 365, 361, 9,
  128, 33, 0, 325, 331, 2403, 441, 27, 4382, 1353, 420, 88, 2962, 2415, 10512, 53, 3849, 24047,
  71, 63005, 180 ]
private def hm2RowR256P4 : List ℕ := [
  16306, 17554, 27246, 8053, 6292, 97382, 82749, 7706, 155689, 72944, 2823, 15675, 161588,
  45254, 386, 6291, 100621, 70341, 73575, 7706, 963127, 979817, 154483, 744254, 14193, 6042,
  141486, 60323, 451277, 650121, 200375, 287866, 108843, 1284148, 16513355, 3177413, 6170910,
  19555238, 125268418, 56298325, 2666420, 157879, 98799277, 17405632, 3399942, 22152961,
  24928712, 45305709 ]
private def hm2RowR256P5 : List ℕ := [
  13480243, 47833537, 2714657, 68360040, 34317681, 60644530, 107898023, 134981833, 346302058,
  326031763, 8055581, 111740185, 559420444, 541149, 2355933467, 995372035836 ]
private def hm2RowR256 : List ℕ :=
  hm2RowR256P0 ++ (hm2RowR256P1 ++ (hm2RowR256P2 ++
    (hm2RowR256P3 ++ (hm2RowR256P4 ++ hm2RowR256P5))))
private def hm2R256V1P0 : List ℤ := [
  Int.negSucc 34129954556, Int.negSucc 161309052047, Int.negSucc 536899441577,
  Int.negSucc 1453118615632, Int.negSucc 3391974963988, Int.negSucc 7052697726185,
  Int.negSucc 13331116869302, Int.negSucc 23232545438943, Int.negSucc 37715211635334,
  Int.negSucc 57482881746532, Int.negSucc 82766240073528, Int.negSucc 113145150096254,
  Int.negSucc 147462500576398, Int.negSucc 183863786176654, Int.negSucc 219968858535806,
  Int.negSucc 253151207224549, Int.negSucc 280874598744228, Int.negSucc 301023935885909,
  Int.negSucc 312169782605528, Int.negSucc 313722472458226, Int.negSucc 305956751675632,
  Int.negSucc 289914503064254, Int.negSucc 267214804253743, Int.negSucc 239813175822071,
  Int.negSucc 209754113758933, Int.negSucc 178954326129364, Int.negSucc 149041720765998,
  Int.negSucc 121260903492965, Int.negSucc 96443047295654, Int.negSucc 75028648746902,
  Int.negSucc 57126738370316, Int.negSucc 42593256261901, Int.negSucc 31113507204445,
  Int.negSucc 22277549368995, Int.negSucc 15641811372880, Int.negSucc 10774250676416,
  Int.negSucc 7283431814774, Int.negSucc 4833845273112, Int.negSucc 3150698622146,
  Int.negSucc 2017529138069, Int.negSucc 1269595294585, Int.negSucc 785362013176,
  Int.negSucc 477698096144, Int.negSucc 285778746110, Int.negSucc 168192704324,
  Int.negSucc 97406477144, Int.negSucc 55522574858, Int.negSucc 31156262620 ]
private def hm2R256V1P1 : List ℤ := [
  Int.negSucc 17214864638, Int.negSucc 9367608287, Int.negSucc 5021126197,
  Int.negSucc 2651536607, Int.negSucc 1379721694, Int.negSucc 707542846, Int.negSucc 357641808,
  Int.negSucc 178214093, Int.negSucc 87557859, Int.negSucc 42419537, Int.negSucc 20267969,
  Int.negSucc 9551705, Int.negSucc 4440458, Int.negSucc 2036564, Int.negSucc 921579,
  Int.negSucc 411493, Int.negSucc 181306, Int.negSucc 78820, Int.negSucc 33804,
  Int.negSucc 14292, Int.negSucc 5948, Int.negSucc 2431, Int.negSucc 967, Int.negSucc 372,
  Int.negSucc 135, Int.negSucc 43, Int.negSucc 12, Int.negSucc 1, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V1P2 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V1P3 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V1 : List ℤ :=
  hm2R256V1P0 ++ (hm2R256V1P1 ++ (hm2R256V1P2 ++ hm2R256V1P3))
private def hm2R256V2P0 : List ℤ := [
  Int.negSucc 4939247, Int.negSucc 15270559, Int.negSucc 14662466, Int.ofNat 3002166,
  Int.negSucc 7514580, Int.ofNat 5925755, Int.negSucc 33899387, Int.negSucc 43059630,
  Int.negSucc 15092263, Int.negSucc 27153016, Int.ofNat 14954364, Int.ofNat 10762168,
  Int.negSucc 53293060, Int.ofNat 142183788, Int.ofNat 341399800, Int.ofNat 776356277,
  Int.ofNat 1706870220, Int.ofNat 3596128695, Int.ofNat 7394380206, Int.ofNat 14560395127,
  Int.ofNat 28190887164, Int.ofNat 52182391322, Int.ofNat 95538170339, Int.ofNat 167204969443,
  Int.ofNat 290134830155, Int.ofNat 482936174133, Int.ofNat 795183043834,
  Int.ofNat 1265101627249, Int.ofNat 1980310101973, Int.ofNat 3019466244964,
  Int.ofNat 4509085044170, Int.ofNat 6592707606760, Int.ofNat 9431374679369,
  Int.ofNat 13227433831677, Int.ofNat 18179136105041, Int.ofNat 24495654021567,
  Int.ofNat 32384715318238, Int.ofNat 42009449242247, Int.ofNat 53491752411561,
  Int.ofNat 66889439255528, Int.ofNat 82156348261247, Int.ofNat 99142974579152,
  Int.ofNat 117591616996117, Int.ofNat 137113106364741, Int.ofNat 157204064688279,
  Int.ofNat 177278160017831, Int.ofNat 196676039009093, Int.ofNat 214698988924466 ]
private def hm2R256V2P1 : List ℤ := [
  Int.ofNat 230667014502516, Int.ofNat 243956602939385, Int.ofNat 254030133581223,
  Int.ofNat 260479854706315, Int.ofNat 263062532946151, Int.ofNat 261706948423186,
  Int.ofNat 256510593673378, Int.ofNat 247735556478977, Int.ofNat 235792163549811,
  Int.ofNat 221204167803961, Int.ofNat 204566713264675, Int.ofNat 186509508287095,
  Int.ofNat 167664638482892, Int.ofNat 148632614584389, Int.ofNat 129948945357817,
  Int.ofNat 112061434665844, Int.ofNat 95322421103861, Int.ofNat 79989148472184,
  Int.ofNat 66224976300920, Int.ofNat 54102860196546, Int.ofNat 43616519096786,
  Int.ofNat 34698981892746, Int.ofNat 27241767138541, Int.ofNat 21109108272788,
  Int.ofNat 16147734643308, Int.ofNat 12196009282210, Int.ofNat 9094113664557,
  Int.ofNat 6693358251319, Int.ofNat 4861849433127, Int.ofNat 3485838747545,
  Int.ofNat 2468419088725, Int.ofNat 1727762475041, Int.ofNat 1195999236457,
  Int.ofNat 818533908108, Int.ofNat 553094366658, Int.ofNat 368120099444,
  Int.ofNat 240640595029, Int.ofNat 154093638666, Int.ofNat 96482951828, Int.ofNat 59041254250,
  Int.ofNat 35349804810, Int.ofNat 20766558644, Int.ofNat 12021831938, Int.ofNat 6895197239,
  Int.ofNat 3940329003, Int.ofNat 2254189057, Int.ofNat 1294641653, Int.ofNat 746721705 ]
private def hm2R256V2P2 : List ℤ := [
  Int.ofNat 431677030, Int.ofNat 249243970, Int.ofNat 143151898, Int.ofNat 81477938,
  Int.ofNat 45818690, Int.ofNat 25402849, Int.ofNat 13867444, Int.ofNat 7449258,
  Int.ofNat 3937054, Int.ofNat 2047632, Int.ofNat 1048369, Int.ofNat 528638, Int.ofNat 262653,
  Int.ofNat 128634, Int.ofNat 62114, Int.ofNat 29570, Int.ofNat 13873, Int.ofNat 6405,
  Int.ofNat 2906, Int.ofNat 1285, Int.ofNat 548, Int.ofNat 223, Int.ofNat 83, Int.ofNat 26,
  Int.ofNat 6, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V2P3 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V2P4 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V2P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V2 : List ℤ :=
  hm2R256V2P0 ++ (hm2R256V2P1 ++ (hm2R256V2P2 ++
    (hm2R256V2P3 ++ (hm2R256V2P4 ++ hm2R256V2P5))))
private def hm2R256V3P0 : List ℤ := [
  Int.negSucc 240958, Int.ofNat 433582, Int.ofNat 3384846, Int.negSucc 9762164,
  Int.ofNat 5579092, Int.ofNat 17080669, Int.ofNat 5135381, Int.ofNat 24933627,
  Int.ofNat 35417267, Int.ofNat 50471462, Int.ofNat 33705206, Int.ofNat 55293496,
  Int.negSucc 17344463, Int.ofNat 113113591, Int.ofNat 258507692, Int.ofNat 496445524,
  Int.ofNat 629376517, Int.ofNat 329139358, Int.negSucc 283042932, Int.negSucc 189366616,
  Int.negSucc 122591077, Int.negSucc 520661105, Int.negSucc 78081265, Int.ofNat 590875369,
  Int.ofNat 1100452119, Int.ofNat 1100201143, Int.ofNat 2226499923, Int.ofNat 1518322577,
  Int.negSucc 36625875, Int.negSucc 865289471, Int.negSucc 3188839257, Int.negSucc 917531447,
  Int.ofNat 322897833, Int.negSucc 169700641, Int.negSucc 1380464902, Int.negSucc 39236008,
  Int.negSucc 1327911963, Int.ofNat 981096141, Int.negSucc 1118050419, Int.negSucc 432652990,
  Int.ofNat 54687319, Int.negSucc 1255516041, Int.ofNat 1116697585, Int.negSucc 808717966,
  Int.negSucc 1128647719, Int.ofNat 1353943961, Int.negSucc 8677557, Int.negSucc 1748999393 ]
private def hm2R256V3P1 : List ℤ := [
  Int.negSucc 1550372725, Int.negSucc 133250913, Int.negSucc 125144425, Int.ofNat 1556483706,
  Int.ofNat 2107453559, Int.ofNat 1352845869, Int.ofNat 1690782555, Int.ofNat 4732321764,
  Int.ofNat 9395000912, Int.ofNat 14806261162, Int.ofNat 23391267576, Int.ofNat 39619756810,
  Int.ofNat 66998527874, Int.ofNat 108639332174, Int.ofNat 171256525193, Int.ofNat 267505037862,
  Int.ofNat 414536117070, Int.ofNat 632719486386, Int.ofNat 948491507286,
  Int.ofNat 1399410814481, Int.ofNat 2036522494570, Int.ofNat 2923249736001,
  Int.ofNat 4134983151733, Int.ofNat 5762084756963, Int.ofNat 7913361229539,
  Int.ofNat 10715278554517, Int.ofNat 14306615950458, Int.ofNat 18832522179978,
  Int.ofNat 24440251754643, Int.ofNat 31273893339430, Int.ofNat 39464167494451,
  Int.ofNat 49113575768666, Int.ofNat 60281342169071, Int.ofNat 72971659287687,
  Int.ofNat 87124531681426, Int.ofNat 102606748956942, Int.ofNat 119203365062657,
  Int.ofNat 136613709158324, Int.ofNat 154455811860222, Int.ofNat 172279352969075,
  Int.ofNat 189584052479882, Int.ofNat 205840845507774, Int.ofNat 220515778408479,
  Int.ofNat 233097670661542, Int.ofNat 243128665048624, Int.ofNat 250233866981448,
  Int.ofNat 254145373674553, Int.ofNat 254717886004538 ]
private def hm2R256V3P2 : List ℤ := [
  Int.ofNat 251935847567548, Int.ofNat 245913338307515, Int.ofNat 236887323812477,
  Int.ofNat 225203820341441, Int.ofNat 211296711786464, Int.ofNat 195660531039382,
  Int.ofNat 178820271255417, Int.ofNat 161301890871721, Int.ofNat 143606327960307,
  Int.ofNat 126188338789504, Int.ofNat 109440359811053, Int.ofNat 93681305811793,
  Int.ofNat 79150441688669, Int.ofNat 66006577979967, Int.ofNat 54332479234332,
  Int.ofNat 44143661196287, Int.ofNat 35400100837743, Int.ofNat 28019143891267,
  Int.ofNat 21888134641933, Int.ofNat 16875816005012, Int.ofNat 12842074576927,
  Int.ofNat 9645948558438, Int.ofNat 7151949053148, Int.ofNat 5234754231028,
  Int.ofNat 3782330294034, Int.ofNat 2697574817602, Int.ofNat 1898664706202,
  Int.ofNat 1318381902686, Int.ofNat 902742845417, Int.ofNat 609253196935,
  Int.ofNat 405055196285, Int.ofNat 265154877523, Int.ofNat 170835782760,
  Int.ofNat 108301820256, Int.ofNat 67550613816, Int.ofNat 41457556232, Int.ofNat 25043353466,
  Int.ofNat 14897589721, Int.ofNat 8733176946, Int.ofNat 5049179607, Int.ofNat 2881776395,
  Int.ofNat 1625174574, Int.ofNat 906417821, Int.ofNat 500357925, Int.ofNat 273533603,
  Int.ofNat 148139028, Int.ofNat 79487060, Int.ofNat 42249470 ]
private def hm2R256V3P3 : List ℤ := [
  Int.ofNat 22237067, Int.ofNat 11583082, Int.ofNat 5967201, Int.ofNat 3038106,
  Int.ofNat 1527580, Int.ofNat 757996, Int.ofNat 370938, Int.ofNat 178914, Int.ofNat 84998,
  Int.ofNat 39746, Int.ofNat 18277, Int.ofNat 8253, Int.ofNat 3652, Int.ofNat 1575,
  Int.ofNat 657, Int.ofNat 261, Int.ofNat 96, Int.ofNat 32, Int.ofNat 8, Int.ofNat 2,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V3P4 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V3P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V3 : List ℤ :=
  hm2R256V3P0 ++ (hm2R256V3P1 ++ (hm2R256V3P2 ++
    (hm2R256V3P3 ++ (hm2R256V3P4 ++ hm2R256V3P5))))
private def hm2R256V4P0 : List ℤ := [
  Int.ofNat 2367924, Int.ofNat 4363757, Int.ofNat 1216619, Int.ofNat 8250696,
  Int.negSucc 210183, Int.negSucc 4011493, Int.ofNat 1625339, Int.negSucc 6463471,
  Int.ofNat 20154481, Int.negSucc 21193977, Int.negSucc 12873018, Int.negSucc 53140457,
  Int.ofNat 29030669, Int.negSucc 95543711, Int.ofNat 3164015, Int.ofNat 90336490,
  Int.negSucc 13376611, Int.negSucc 68666999, Int.negSucc 163452892, Int.negSucc 77127476,
  Int.ofNat 73923275, Int.ofNat 115930950, Int.negSucc 142671128, Int.ofNat 290945408,
  Int.ofNat 187681626, Int.ofNat 31041557, Int.ofNat 52002678, Int.ofNat 631294956,
  Int.ofNat 768875302, Int.ofNat 109022378, Int.negSucc 380524110, Int.ofNat 11094257,
  Int.ofNat 179078978, Int.ofNat 734485519, Int.negSucc 518655810, Int.ofNat 73410955,
  Int.ofNat 9629975, Int.negSucc 327710749, Int.ofNat 689681048, Int.ofNat 627574564,
  Int.ofNat 1456762893, Int.ofNat 1319194325, Int.ofNat 970825001, Int.ofNat 608016571,
  Int.ofNat 517628851, Int.negSucc 140727789, Int.ofNat 146629182, Int.ofNat 784805652 ]
private def hm2R256V4P1 : List ℤ := [
  Int.ofNat 175316251, Int.negSucc 2145022258, Int.negSucc 3132200055, Int.negSucc 3243938616,
  Int.negSucc 1536225267, Int.negSucc 458237481, Int.negSucc 948700577, Int.negSucc 463042476,
  Int.ofNat 1516997997, Int.negSucc 395653815, Int.negSucc 1096419133, Int.negSucc 108288394,
  Int.ofNat 1689326025, Int.ofNat 1481476289, Int.ofNat 1236876727, Int.ofNat 1382717178,
  Int.negSucc 279407965, Int.negSucc 1370377385, Int.negSucc 204681010, Int.negSucc 379636214,
  Int.ofNat 150366041, Int.negSucc 198382589, Int.negSucc 273534585, Int.negSucc 961862626,
  Int.negSucc 686269416, Int.negSucc 1184052904, Int.ofNat 902872837, Int.ofNat 1472348586,
  Int.ofNat 59117647, Int.ofNat 289092099, Int.ofNat 121695212, Int.negSucc 1099645941,
  Int.negSucc 305195785, Int.negSucc 2215142547, Int.negSucc 1251825463, Int.negSucc 13642401,
  Int.negSucc 137801955, Int.ofNat 479391866, Int.ofNat 1374237946, Int.ofNat 806215020,
  Int.ofNat 290457166, Int.ofNat 348598080, Int.negSucc 51516411, Int.negSucc 501830878,
  Int.negSucc 143431802, Int.negSucc 1314169903, Int.negSucc 1114642906, Int.negSucc 1136831915
  ]
private def hm2R256V4P2 : List ℤ := [
  Int.ofNat 4041834258, Int.negSucc 6248271588, Int.negSucc 8911379397, Int.negSucc 15509976043,
  Int.negSucc 29541679913, Int.negSucc 53422273208, Int.negSucc 90570517117,
  Int.negSucc 148971455420, Int.negSucc 243076446311, Int.negSucc 393380092280,
  Int.negSucc 626269227028, Int.negSucc 976825874335, Int.negSucc 1494167366416,
  Int.negSucc 2246321703476, Int.negSucc 3322439057701, Int.negSucc 4833113637821,
  Int.negSucc 6911098796883, Int.negSucc 9712993213345, Int.negSucc 13419542939455,
  Int.negSucc 18231306386540, Int.negSucc 24358455798474, Int.negSucc 32006212109362,
  Int.negSucc 41358161173671, Int.negSucc 52558237191207, Int.negSucc 65690675440633,
  Int.negSucc 80757805661875, Int.negSucc 97657958476504, Int.negSucc 116167847875387,
  Int.negSucc 135933757257218, Int.negSucc 156473872952419, Int.negSucc 177191899203523,
  Int.negSucc 197401087363900, Int.negSucc 216357902917244, Int.negSucc 233304470525614,
  Int.negSucc 247517701447150, Int.negSucc 258360916381771, Int.negSucc 265332105114696,
  Int.negSucc 268102832841689, Int.negSucc 266543311197578, Int.negSucc 260731452475544,
  Int.negSucc 250945802835390, Int.negSucc 237643641233248, Int.negSucc 221426437865344,
  Int.negSucc 202995722151388, Int.negSucc 183103373000627, Int.negSucc 162501138887713,
  Int.negSucc 141894361967680, Int.negSucc 121904153032128 ]
private def hm2R256V4P3 : List ℤ := [
  Int.negSucc 103040775032267, Int.negSucc 85689188228295, Int.negSucc 70106088048562,
  Int.negSucc 56426642815893, Int.negSucc 44678568266738, Int.negSucc 34801033168569,
  Int.negSucc 26666004886844, Int.negSucc 20099899070103, Int.negSucc 14903750629709,
  Int.negSucc 10870566027233, Int.negSucc 7799029587755, Int.negSucc 5503266304144,
  Int.negSucc 3818836803116, Int.negSucc 2605491225391, Int.negSucc 1747404278878,
  Int.negSucc 1151659548370, Int.negSucc 745683147064, Int.negSucc 474193286506,
  Int.negSucc 296077846475, Int.negSucc 181467876154, Int.negSucc 109157408313,
  Int.negSucc 64433327567, Int.negSucc 37320533948, Int.negSucc 21211667445,
  Int.negSucc 11831362695, Int.negSucc 6477428721, Int.negSucc 3481617849,
  Int.negSucc 1837786216, Int.negSucc 952981002, Int.negSucc 485618860, Int.negSucc 243261359,
  Int.negSucc 119825522, Int.negSucc 58054438, Int.negSucc 27670274, Int.negSucc 12975663,
  Int.negSucc 5986738, Int.negSucc 2717399, Int.negSucc 1213307, Int.negSucc 532485,
  Int.negSucc 230124, Int.negSucc 97110, Int.negSucc 40625, Int.negSucc 16798, Int.negSucc 6493,
  Int.negSucc 2238, Int.ofNat 700, Int.negSucc 210, Int.negSucc 64 ]
private def hm2R256V4P4 : List ℤ := [
  Int.negSucc 17, Int.negSucc 4, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V4P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V4 : List ℤ :=
  hm2R256V4P0 ++ (hm2R256V4P1 ++ (hm2R256V4P2 ++
    (hm2R256V4P3 ++ (hm2R256V4P4 ++ hm2R256V4P5))))
private def hm2R256V5P0 : List ℤ := [
  Int.ofNat 164871, Int.ofNat 1397429, Int.ofNat 41534, Int.negSucc 2436470,
  Int.negSucc 1129197, Int.negSucc 3320919, Int.negSucc 6999657, Int.ofNat 3168415,
  Int.ofNat 1563429, Int.ofNat 624093, Int.ofNat 8435103, Int.ofNat 4996813,
  Int.negSucc 4510516, Int.negSucc 60687222, Int.negSucc 72216624, Int.ofNat 2695980,
  Int.ofNat 22844444, Int.ofNat 26950430, Int.negSucc 7473889, Int.negSucc 27205314,
  Int.negSucc 15858882, Int.negSucc 4938094, Int.ofNat 7087963, Int.ofNat 110453790,
  Int.negSucc 69742799, Int.negSucc 106941217, Int.negSucc 82328135, Int.negSucc 45965845,
  Int.ofNat 52440199, Int.negSucc 28583047, Int.negSucc 135073228, Int.negSucc 215325975,
  Int.negSucc 182092823, Int.ofNat 101511925, Int.negSucc 260078735, Int.negSucc 63407033,
  Int.negSucc 88918414, Int.ofNat 144786919, Int.ofNat 422873343, Int.ofNat 328732044,
  Int.ofNat 358155892, Int.ofNat 103658907, Int.negSucc 213363643, Int.negSucc 186667880,
  Int.negSucc 339630226, Int.negSucc 934835290, Int.negSucc 849271557, Int.negSucc 419051815 ]
private def hm2R256V5P1 : List ℤ := [
  Int.negSucc 450702128, Int.negSucc 451242773, Int.negSucc 337096844, Int.negSucc 528002617,
  Int.negSucc 418772728, Int.negSucc 53376815, Int.ofNat 142342309, Int.ofNat 42574681,
  Int.ofNat 12207759, Int.negSucc 27376963, Int.ofNat 209930073, Int.ofNat 152583523,
  Int.ofNat 363049660, Int.negSucc 388947840, Int.negSucc 608607633, Int.negSucc 180184470,
  Int.ofNat 63178751, Int.ofNat 605284582, Int.ofNat 884830079, Int.ofNat 452374243,
  Int.ofNat 1116119294, Int.ofNat 1949723124, Int.ofNat 2760974546, Int.ofNat 2897390642,
  Int.ofNat 1710430067, Int.ofNat 1460580186, Int.ofNat 2359384714, Int.ofNat 563767964,
  Int.negSucc 1073138945, Int.ofNat 1068380426, Int.negSucc 1805257548, Int.negSucc 2214321993,
  Int.negSucc 728047076, Int.ofNat 593932210, Int.ofNat 131573539, Int.negSucc 19750815,
  Int.ofNat 1560027853, Int.ofNat 680269877, Int.ofNat 110888746, Int.ofNat 160296731,
  Int.ofNat 930161036, Int.ofNat 1093879525, Int.ofNat 952133407, Int.ofNat 1923805351,
  Int.ofNat 2737507229, Int.ofNat 1470489341, Int.negSucc 1094800467, Int.negSucc 1938852129 ]
private def hm2R256V5P2 : List ℤ := [
  Int.ofNat 407408000, Int.ofNat 726809021, Int.ofNat 1690051407, Int.ofNat 2731383822,
  Int.ofNat 2879908223, Int.ofNat 284366649, Int.negSucc 2007712524, Int.negSucc 1997487361,
  Int.negSucc 2129435766, Int.ofNat 426727935, Int.ofNat 765566079, Int.ofNat 1974984106,
  Int.ofNat 1322278176, Int.negSucc 797484949, Int.negSucc 1420007139, Int.ofNat 1119623070,
  Int.negSucc 1264955627, Int.negSucc 368003173, Int.negSucc 413504421, Int.ofNat 2340489769,
  Int.ofNat 306798257, Int.negSucc 1120626165, Int.ofNat 447784913, Int.ofNat 1100739985,
  Int.negSucc 405271256, Int.ofNat 1490185404, Int.negSucc 1314464281, Int.ofNat 167072799,
  Int.ofNat 150259195, Int.ofNat 319115056, Int.ofNat 1098251213, Int.ofNat 292154775,
  Int.negSucc 497070728, Int.ofNat 720150916, Int.negSucc 601490806, Int.negSucc 880032544,
  Int.negSucc 897153765, Int.negSucc 1946644505, Int.negSucc 4325621361, Int.ofNat 3520197270,
  Int.ofNat 7258774452, Int.negSucc 12867417575, Int.negSucc 14652560781,
  Int.negSucc 17828572507, Int.negSucc 25026065445, Int.ofNat 19710250105,
  Int.ofNat 26972911346, Int.ofNat 8036000717 ]
private def hm2R256V5P3 : List ℤ := [
  Int.ofNat 50466518335, Int.ofNat 116872687717, Int.ofNat 195208187194, Int.ofNat 432274006322,
  Int.ofNat 763352646043, Int.ofNat 1387175600371, Int.ofNat 2428678133868,
  Int.ofNat 4018607312901, Int.ofNat 6522472214585, Int.ofNat 10223744497605,
  Int.ofNat 15453919723155, Int.ofNat 22824708516897, Int.ofNat 32561876020501,
  Int.ofNat 45256950329522, Int.ofNat 61051640449120, Int.ofNat 80271641747367,
  Int.ofNat 102521848836549, Int.ofNat 127690475570978, Int.ofNat 154896027289093,
  Int.ofNat 182993083141778, Int.ofNat 210906017602606, Int.ofNat 237023089203493,
  Int.ofNat 259710460578733, Int.ofNat 277832746775097, Int.ofNat 289937620358041,
  Int.ofNat 295414145337859, Int.ofNat 293844427063135, Int.ofNat 285380047872853,
  Int.ofNat 270694513120307, Int.ofNat 250842666715906, Int.ofNat 227036193533422,
  Int.ofNat 200668528597328, Int.ofNat 173451497770587, Int.ofNat 146379510025894,
  Int.ofNat 120873956136035, Int.ofNat 97286448202041, Int.ofNat 76679728049765,
  Int.ofNat 59088010078500, Int.ofNat 44505006595308, Int.ofNat 32721558691657,
  Int.ofNat 23513689540866, Int.ofNat 16453251473208, Int.ofNat 11254848795976,
  Int.ofNat 7629459244106, Int.ofNat 5189870155033, Int.ofNat 3302708931389,
  Int.ofNat 1994667316919, Int.ofNat 1072861275772 ]
private def hm2R256V5P4 : List ℤ := [
  Int.ofNat 475431766578, Int.ofNat 173919920918, Int.ofNat 59459145389, Int.ofNat 24929685562,
  Int.ofNat 14668107287, Int.ofNat 10008880191, Int.ofNat 6737988786, Int.ofNat 4273740263,
  Int.ofNat 2541347125, Int.ofNat 1421765545, Int.ofNat 751854545, Int.ofNat 377606531,
  Int.ofNat 180829422, Int.ofNat 83164954, Int.ofNat 36397672, Int.ofNat 15761381,
  Int.ofNat 6503044, Int.ofNat 2343644, Int.ofNat 727324, Int.ofNat 213585, Int.ofNat 69001,
  Int.ofNat 25508, Int.ofNat 9772, Int.ofNat 3567, Int.ofNat 1207, Int.ofNat 378, Int.ofNat 105,
  Int.ofNat 26, Int.ofNat 4, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V5P5 : List ℤ := [
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V5 : List ℤ :=
  hm2R256V5P0 ++ (hm2R256V5P1 ++ (hm2R256V5P2 ++
    (hm2R256V5P3 ++ (hm2R256V5P4 ++ hm2R256V5P5))))
private def hm2R256V6P0 : List ℤ := [
  Int.negSucc 67955, Int.ofNat 116779, Int.negSucc 242911, Int.negSucc 341852,
  Int.negSucc 235670, Int.negSucc 2772803, Int.negSucc 1394785, Int.ofNat 572507,
  Int.ofNat 3277866, Int.ofNat 428522, Int.negSucc 5946501, Int.negSucc 388521,
  Int.ofNat 3002448, Int.ofNat 155135, Int.negSucc 1754257, Int.negSucc 2109803,
  Int.negSucc 13367570, Int.negSucc 6155053, Int.ofNat 15742731, Int.ofNat 12607967,
  Int.negSucc 17209286, Int.ofNat 22989697, Int.ofNat 22844757, Int.ofNat 19928282,
  Int.ofNat 65734385, Int.ofNat 65863476, Int.ofNat 81925044, Int.ofNat 75188028,
  Int.ofNat 51323478, Int.ofNat 8101825, Int.ofNat 70877978, Int.negSucc 5261074,
  Int.negSucc 49642066, Int.ofNat 112369738, Int.ofNat 54371595, Int.negSucc 193692035,
  Int.negSucc 15234506, Int.negSucc 37656870, Int.negSucc 147971548, Int.negSucc 105314307,
  Int.negSucc 6260389, Int.negSucc 17800504, Int.ofNat 202795343, Int.ofNat 195086237,
  Int.ofNat 74071315, Int.ofNat 174007748, Int.ofNat 130152399, Int.negSucc 27738871 ]
private def hm2R256V6P1 : List ℤ := [
  Int.negSucc 235076784, Int.ofNat 259885542, Int.negSucc 134401160, Int.negSucc 295037768,
  Int.negSucc 632745270, Int.negSucc 369779061, Int.ofNat 107061750, Int.ofNat 336742136,
  Int.ofNat 227198439, Int.ofNat 79064744, Int.negSucc 266704678, Int.negSucc 273897400,
  Int.negSucc 540808953, Int.ofNat 798403812, Int.negSucc 23004041, Int.ofNat 394551910,
  Int.ofNat 42882809, Int.negSucc 707554135, Int.negSucc 718809902, Int.negSucc 519270460,
  Int.negSucc 283680443, Int.ofNat 136158160, Int.negSucc 217464754, Int.negSucc 300796188,
  Int.ofNat 566544244, Int.negSucc 426546132, Int.negSucc 165802742, Int.negSucc 210978089,
  Int.negSucc 1055602201, Int.negSucc 721714272, Int.negSucc 778784704, Int.ofNat 289539935,
  Int.ofNat 187070775, Int.ofNat 1003073849, Int.negSucc 249367340, Int.ofNat 148254479,
  Int.ofNat 830831485, Int.ofNat 210604226, Int.ofNat 119535129, Int.ofNat 435064264,
  Int.negSucc 642375489, Int.negSucc 1851550846, Int.negSucc 3105957682, Int.negSucc 3112139249,
  Int.negSucc 1908259213, Int.ofNat 1516202457, Int.ofNat 2826136615, Int.negSucc 733112687 ]
private def hm2R256V6P2 : List ℤ := [
  Int.ofNat 847873146, Int.ofNat 65755736, Int.negSucc 885133906, Int.negSucc 2253997478,
  Int.negSucc 678697926, Int.negSucc 96311661, Int.ofNat 1173763729, Int.negSucc 776287440,
  Int.negSucc 956225435, Int.negSucc 704870427, Int.negSucc 1173715996, Int.negSucc 1810177623,
  Int.negSucc 783361479, Int.negSucc 2078348698, Int.negSucc 1343197869, Int.negSucc 688720939,
  Int.negSucc 641674600, Int.negSucc 2044599334, Int.ofNat 3749166033, Int.ofNat 3874142999,
  Int.ofNat 2453130623, Int.ofNat 1430358570, Int.ofNat 2502024402, Int.ofNat 974579295,
  Int.ofNat 973009373, Int.ofNat 124902200, Int.ofNat 2808587154, Int.ofNat 467959430,
  Int.ofNat 185580864, Int.ofNat 2271889728, Int.ofNat 2997004884, Int.ofNat 607649358,
  Int.negSucc 1823978518, Int.negSucc 3541405869, Int.negSucc 1071902300, Int.ofNat 4469486833,
  Int.negSucc 327807376, Int.ofNat 10217756360, Int.ofNat 6617234635, Int.ofNat 11319224105,
  Int.negSucc 4924617658, Int.negSucc 927142609, Int.negSucc 432863873, Int.ofNat 11845808649,
  Int.negSucc 20277014379, Int.negSucc 12536136488, Int.ofNat 12358454826,
  Int.negSucc 32522620495 ]
private def hm2R256V6P3 : List ℤ := [
  Int.negSucc 30935775485, Int.negSucc 25580900552, Int.negSucc 24839815024,
  Int.ofNat 17511362056, Int.ofNat 113812095, Int.ofNat 9753363632, Int.negSucc 38704341570,
  Int.ofNat 39127515427, Int.negSucc 29463631867, Int.negSucc 18242495914,
  Int.negSucc 42116064031, Int.negSucc 23197978489, Int.negSucc 24888387914,
  Int.negSucc 49442987813, Int.negSucc 49971611605, Int.negSucc 23099185523,
  Int.negSucc 11146207691, Int.ofNat 3097336388, Int.negSucc 6277050903, Int.ofNat 32415511779,
  Int.negSucc 54819932492, Int.negSucc 67573010393, Int.ofNat 25025275462,
  Int.negSucc 74694132833, Int.negSucc 33157346172, Int.negSucc 6680554304,
  Int.ofNat 60406043178, Int.ofNat 83531770491, Int.negSucc 39524745780, Int.ofNat 88072053389,
  Int.ofNat 88091335297, Int.negSucc 13948481176, Int.negSucc 16016812360,
  Int.negSucc 144960824112, Int.negSucc 149576539179, Int.ofNat 136447636789,
  Int.ofNat 166024993536, Int.ofNat 369955086195, Int.ofNat 1045325714858,
  Int.ofNat 2877899403655, Int.ofNat 5895364731422, Int.ofNat 11264839041066,
  Int.ofNat 19818063242638, Int.ofNat 32178119410007, Int.ofNat 49551674913275,
  Int.ofNat 72242796236325, Int.ofNat 100271849565242, Int.ofNat 132839946471988 ]
private def hm2R256V6P4 : List ℤ := [
  Int.ofNat 168588064235394, Int.ofNat 206004534749048, Int.ofNat 241710541031515,
  Int.ofNat 273369990768585, Int.ofNat 298198938234959, Int.ofNat 314558137163591,
  Int.ofNat 320623925872978, Int.ofNat 316031288926023, Int.ofNat 301933287111035,
  Int.ofNat 279398277711177, Int.ofNat 250392053179229, Int.ofNat 217751434437646,
  Int.ofNat 183907917998384, Int.ofNat 150762221901649, Int.ofNat 119885949944485,
  Int.ofNat 92407500278168, Int.ofNat 69073084480494, Int.ofNat 50266808018053,
  Int.ofNat 35804080096593, Int.ofNat 24953090280495, Int.ofNat 16840099150117,
  Int.ofNat 10820150132608, Int.ofNat 6512894460700, Int.ofNat 3634351456657,
  Int.ofNat 1873743185704, Int.negSucc 895727856727, Int.ofNat 401460649047,
  Int.ofNat 172167397163, Int.ofNat 72858397793, Int.ofNat 31589236413, Int.ofNat 14427847110,
  Int.ofNat 6987328405, Int.ofNat 3522994644, Int.ofNat 1731225205, Int.ofNat 929861911,
  Int.ofNat 435673199, Int.ofNat 155112293, Int.ofNat 45535992, Int.ofNat 14150977,
  Int.ofNat 5725732, Int.ofNat 2703718, Int.ofNat 1256828, Int.ofNat 539529, Int.ofNat 211406,
  Int.ofNat 75820, Int.ofNat 25050, Int.ofNat 7673, Int.ofNat 2185 ]
private def hm2R256V6P5 : List ℤ := [
  Int.ofNat 575, Int.ofNat 135, Int.ofNat 25, Int.ofNat 2, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
  Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0 ]
private def hm2R256V6 : List ℤ :=
  hm2R256V6P0 ++ (hm2R256V6P1 ++ (hm2R256V6P2 ++
    (hm2R256V6P3 ++ (hm2R256V6P4 ++ hm2R256V6P5))))
private def hm2R256V7P0 : List ℤ := [
  Int.negSucc 22577, Int.negSucc 66266, Int.negSucc 158120, Int.negSucc 401596,
  Int.negSucc 862849, Int.negSucc 560625, Int.negSucc 190359, Int.negSucc 106812,
  Int.negSucc 584550, Int.ofNat 419325, Int.ofNat 581381, Int.ofNat 1136568, Int.ofNat 7305903,
  Int.ofNat 5349574, Int.negSucc 507780, Int.negSucc 220320, Int.negSucc 1150762,
  Int.negSucc 1738449, Int.ofNat 1197083, Int.negSucc 2817801, Int.ofNat 1947813,
  Int.ofNat 15332809, Int.ofNat 22024758, Int.ofNat 1736409, Int.ofNat 7358082,
  Int.negSucc 27317052, Int.ofNat 10790225, Int.negSucc 3974886, Int.negSucc 7534832,
  Int.ofNat 9916735, Int.negSucc 1453770, Int.negSucc 36783013, Int.negSucc 17293093,
  Int.ofNat 12043420, Int.negSucc 3095724, Int.negSucc 18150915, Int.negSucc 11142801,
  Int.negSucc 4345066, Int.negSucc 49407237, Int.negSucc 61324052, Int.negSucc 49886473,
  Int.negSucc 70969047, Int.negSucc 69616193, Int.negSucc 142611106, Int.negSucc 125881501,
  Int.negSucc 70263441, Int.ofNat 66726681, Int.negSucc 100171585 ]
private def hm2R256V7P1 : List ℤ := [
  Int.negSucc 99420173, Int.negSucc 102885978, Int.ofNat 104018626, Int.ofNat 225659047,
  Int.ofNat 171290148, Int.ofNat 129481922, Int.ofNat 99682966, Int.negSucc 17878261,
  Int.ofNat 77139015, Int.ofNat 92540306, Int.negSucc 59852758, Int.negSucc 15472399,
  Int.negSucc 168635164, Int.negSucc 264570808, Int.negSucc 326979356, Int.negSucc 510199654,
  Int.negSucc 499773054, Int.negSucc 429268513, Int.negSucc 511486784, Int.negSucc 457051654,
  Int.negSucc 313408537, Int.ofNat 280754506, Int.ofNat 163639838, Int.negSucc 175942235,
  Int.ofNat 343250222, Int.ofNat 911644856, Int.ofNat 690829030, Int.ofNat 437499981,
  Int.ofNat 383571539, Int.negSucc 176346897, Int.ofNat 522101317, Int.negSucc 407158188,
  Int.ofNat 197668169, Int.ofNat 305101681, Int.negSucc 139866168, Int.negSucc 115498977,
  Int.negSucc 213927891, Int.ofNat 460422514, Int.negSucc 22612183, Int.negSucc 91029004,
  Int.negSucc 66118517, Int.negSucc 74244279, Int.negSucc 594400546, Int.negSucc 247001859,
  Int.ofNat 594099848, Int.ofNat 485696500, Int.ofNat 49098642, Int.negSucc 60697161 ]
private def hm2R256V7P2 : List ℤ := [
  Int.negSucc 405532026, Int.ofNat 861885775, Int.ofNat 963972125, Int.ofNat 1520813875,
  Int.negSucc 520744426, Int.negSucc 682867104, Int.negSucc 793149174, Int.ofNat 432834270,
  Int.ofNat 1088061298, Int.ofNat 707955133, Int.negSucc 485376537, Int.negSucc 727798925,
  Int.negSucc 281855087, Int.negSucc 480366782, Int.ofNat 253463559, Int.negSucc 459755095,
  Int.negSucc 920156293, Int.ofNat 493397760, Int.ofNat 981138623, Int.negSucc 766472466,
  Int.negSucc 355873233, Int.negSucc 1473238149, Int.negSucc 2425252282, Int.negSucc 2223123810,
  Int.negSucc 548180555, Int.ofNat 2030649142, Int.negSucc 4409741941, Int.negSucc 2013264902,
  Int.negSucc 1569350145, Int.negSucc 1683136814, Int.ofNat 888150088, Int.ofNat 421145741,
  Int.ofNat 220915399, Int.negSucc 1413197800, Int.negSucc 3176401532, Int.negSucc 1492017584,
  Int.negSucc 6524615246, Int.negSucc 6312244343, Int.ofNat 5747718172, Int.ofNat 7315140684,
  Int.negSucc 5591640288, Int.negSucc 9444599167, Int.negSucc 1153358019, Int.ofNat 5155195419,
  Int.negSucc 8270237344, Int.negSucc 16626622059, Int.negSucc 9226031637,
  Int.negSucc 14191671650 ]
private def hm2R256V7P3 : List ℤ := [
  Int.negSucc 24634318497, Int.negSucc 17243618750, Int.negSucc 6051041672,
  Int.negSucc 19995215927, Int.negSucc 13845463340, Int.negSucc 4287631084,
  Int.ofNat 6109454866, Int.ofNat 16847023847, Int.ofNat 780499230, Int.ofNat 10517574588,
  Int.ofNat 38094659412, Int.negSucc 3567883265, Int.negSucc 27097867449,
  Int.negSucc 54437241271, Int.negSucc 19761492885, Int.negSucc 18847911398,
  Int.negSucc 36156376247, Int.ofNat 17275693010, Int.ofNat 19823163220, Int.negSucc 9730148667,
  Int.negSucc 11670502498, Int.ofNat 32213600561, Int.ofNat 39193437900, Int.ofNat 13717982582,
  Int.ofNat 57232046855, Int.ofNat 70627305110, Int.ofNat 100104952200, Int.ofNat 30724499377,
  Int.negSucc 42758729556, Int.negSucc 48542571421, Int.ofNat 20481704626,
  Int.ofNat 17651349160, Int.ofNat 49816888324, Int.ofNat 19544160442, Int.negSucc 19047727676,
  Int.negSucc 59151512075, Int.negSucc 132777948201, Int.negSucc 157160632984,
  Int.negSucc 50551993699, Int.ofNat 69829407307, Int.ofNat 46469071294, Int.ofNat 226418621130,
  Int.negSucc 122996419916, Int.ofNat 68895133864, Int.ofNat 22274542203, Int.ofNat 34914079188,
  Int.negSucc 65634533458, Int.negSucc 169407122390 ]
private def hm2R256V7P4 : List ℤ := [
  Int.negSucc 261324510685, Int.negSucc 171271120290, Int.ofNat 242961365037,
  Int.negSucc 287772154278, Int.ofNat 266477877969, Int.ofNat 1011833505369,
  Int.ofNat 419321346658, Int.ofNat 496227522868, Int.negSucc 25859619128,
  Int.negSucc 283516694349, Int.negSucc 80030880134, Int.ofNat 1003353957480,
  Int.ofNat 443750666166, Int.negSucc 294063111739, Int.ofNat 283496421945,
  Int.ofNat 352148003173, Int.negSucc 756194590679, Int.ofNat 291200524579,
  Int.negSucc 1304281560064, Int.ofNat 2142353502412, Int.negSucc 3008006617948,
  Int.negSucc 2363324243218, Int.negSucc 5234172423259, Int.negSucc 21020426938369,
  Int.negSucc 45580148624630, Int.negSucc 82853912245662, Int.negSucc 132209259400516,
  Int.negSucc 187510343617367, Int.negSucc 243918509947963, Int.negSucc 296549772043599,
  Int.negSucc 337271316586550, Int.negSucc 359542787050299, Int.negSucc 362551757674267,
  Int.negSucc 348142975908960, Int.negSucc 317918106342132, Int.negSucc 275091751007273,
  Int.negSucc 226009130606524, Int.negSucc 177702944552831, Int.negSucc 134623301898197,
  Int.negSucc 98127375655132, Int.negSucc 68132480030043, Int.negSucc 44470569551160,
  Int.negSucc 26993334771299, Int.negSucc 15149479872924, Int.negSucc 7856707056794,
  Int.negSucc 3779824651165, Int.negSucc 1699790786371, Int.negSucc 722107233939 ]
private def hm2R256V7P5 : List ℤ := [
  Int.negSucc 293370901914, Int.negSucc 115300683715, Int.negSucc 44237506159,
  Int.negSucc 16415956190, Int.negSucc 6223072357, Int.negSucc 1972356798,
  Int.negSucc 480849569, Int.negSucc 110364259, Int.negSucc 33623572, Int.negSucc 9836864,
  Int.negSucc 2161442, Int.negSucc 396728, Int.negSucc 76144, Int.negSucc 15736, Int.ofNat 2953,
  Int.negSucc 426, Int.negSucc 34 ]
private def hm2R256V7 : List ℤ :=
  hm2R256V7P0 ++ (hm2R256V7P1 ++ (hm2R256V7P2 ++
    (hm2R256V7P3 ++ (hm2R256V7P4 ++ hm2R256V7P5))))
private def hm2R256V8P0 : List ℤ := [
  Int.negSucc 6728, Int.negSucc 8782, Int.negSucc 30181, Int.negSucc 51316, Int.negSucc 36178,
  Int.ofNat 255674, Int.ofNat 622313, Int.ofNat 563562, Int.ofNat 99843, Int.ofNat 848603,
  Int.ofNat 1281187, Int.negSucc 838689, Int.negSucc 1036346, Int.negSucc 1759250,
  Int.ofNat 631565, Int.ofNat 3290945, Int.ofNat 2897909, Int.ofNat 988947, Int.ofNat 2340729,
  Int.negSucc 2810239, Int.negSucc 3635801, Int.ofNat 458776, Int.negSucc 176107,
  Int.negSucc 9647078, Int.ofNat 315251, Int.negSucc 3133060, Int.ofNat 6247863,
  Int.ofNat 3239801, Int.negSucc 3234084, Int.negSucc 8147965, Int.negSucc 6151137,
  Int.negSucc 5209832, Int.negSucc 4728510, Int.ofNat 1432353, Int.ofNat 9774204,
  Int.negSucc 5509715, Int.ofNat 7673823, Int.ofNat 19299718, Int.negSucc 24600138,
  Int.ofNat 33452958, Int.ofNat 25356398, Int.ofNat 51527478, Int.ofNat 24139857,
  Int.ofNat 3479949, Int.ofNat 10926939, Int.ofNat 27788183, Int.ofNat 47519721,
  Int.ofNat 8842339 ]
private def hm2R256V8P1 : List ℤ := [
  Int.negSucc 20596180, Int.negSucc 18878276, Int.negSucc 21983892, Int.negSucc 10668067,
  Int.negSucc 21907091, Int.negSucc 44385850, Int.negSucc 38884059, Int.ofNat 25791313,
  Int.ofNat 128946419, Int.ofNat 25522722, Int.negSucc 19460085, Int.ofNat 754449,
  Int.ofNat 57298317, Int.ofNat 92678295, Int.negSucc 2210960, Int.ofNat 24408837,
  Int.ofNat 135346028, Int.negSucc 164267635, Int.negSucc 29368542, Int.ofNat 73350664,
  Int.negSucc 156424380, Int.negSucc 4092461, Int.ofNat 201819067, Int.negSucc 254637453,
  Int.negSucc 9371706, Int.negSucc 16273959, Int.negSucc 24781195, Int.negSucc 105983473,
  Int.negSucc 75918490, Int.negSucc 33189986, Int.ofNat 6801322, Int.negSucc 116502516,
  Int.ofNat 134426663, Int.ofNat 42454615, Int.negSucc 168918611, Int.negSucc 167992654,
  Int.negSucc 274457720, Int.ofNat 112214337, Int.ofNat 239961863, Int.negSucc 44602543,
  Int.negSucc 834648338, Int.negSucc 954385803, Int.negSucc 1042803497, Int.negSucc 1005060786,
  Int.ofNat 211908182, Int.ofNat 280370743, Int.negSucc 375053892, Int.negSucc 225080195 ]
private def hm2R256V8P2 : List ℤ := [
  Int.negSucc 389258847, Int.negSucc 150437211, Int.ofNat 447914939, Int.ofNat 441865566,
  Int.ofNat 591126392, Int.ofNat 7720752, Int.negSucc 427099668, Int.negSucc 114135692,
  Int.negSucc 423988972, Int.negSucc 175464946, Int.negSucc 155062053, Int.negSucc 76762831,
  Int.negSucc 163729291, Int.negSucc 477734387, Int.negSucc 914542059, Int.negSucc 476796609,
  Int.negSucc 649834317, Int.negSucc 247433530, Int.negSucc 440347818, Int.negSucc 113170990,
  Int.negSucc 1118390591, Int.negSucc 329411389, Int.negSucc 226421130, Int.negSucc 484282322,
  Int.negSucc 790956884, Int.negSucc 2078915739, Int.negSucc 1556959743, Int.negSucc 915529995,
  Int.negSucc 232899410, Int.negSucc 374599303, Int.ofNat 164328648, Int.negSucc 1805298593,
  Int.negSucc 1056409952, Int.negSucc 529131836, Int.negSucc 2596631761, Int.ofNat 1436450566,
  Int.ofNat 403941630, Int.negSucc 946192546, Int.ofNat 1278659904, Int.ofNat 621882755,
  Int.negSucc 710140135, Int.negSucc 2333062792, Int.negSucc 4812773962, Int.negSucc 1945502428,
  Int.ofNat 876938978, Int.negSucc 1727438365, Int.negSucc 4880863081, Int.ofNat 690332241 ]
private def hm2R256V8P3 : List ℤ := [
  Int.ofNat 2343601196, Int.ofNat 831957670, Int.negSucc 708299654, Int.negSucc 6902046026,
  Int.negSucc 14229428426, Int.negSucc 15398984054, Int.negSucc 11376490046,
  Int.negSucc 10812162784, Int.ofNat 2047665898, Int.negSucc 3403322387,
  Int.negSucc 10711050957, Int.negSucc 25248514751, Int.negSucc 4244067770,
  Int.ofNat 1119823745, Int.ofNat 5811115471, Int.ofNat 4232919397, Int.negSucc 9411416745,
  Int.negSucc 39081550154, Int.negSucc 26945682102, Int.ofNat 13666300884, Int.ofNat 9625702573,
  Int.negSucc 6405351857, Int.negSucc 2521749788, Int.ofNat 14407596549, Int.negSucc 8181273578,
  Int.ofNat 1516739673, Int.negSucc 19712174588, Int.ofNat 1980607286, Int.ofNat 584721428,
  Int.ofNat 25160721098, Int.ofNat 10430051181, Int.ofNat 66197850092, Int.ofNat 10763469922,
  Int.ofNat 8027365134, Int.ofNat 37373488164, Int.ofNat 78291228478, Int.ofNat 143473035560,
  Int.ofNat 54327840477, Int.negSucc 24977227626, Int.ofNat 77352642187, Int.ofNat 105139849765,
  Int.ofNat 39113318798, Int.ofNat 63652663656, Int.ofNat 180004760809, Int.ofNat 89467754284,
  Int.ofNat 220662628414, Int.ofNat 8525534589, Int.negSucc 56106000186 ]
private def hm2R256V8P4 : List ℤ := [
  Int.negSucc 445917816506, Int.negSucc 296697259613, Int.ofNat 111892693375,
  Int.ofNat 44690586258, Int.negSucc 4896288, Int.negSucc 530257234616,
  Int.negSucc 321983313371, Int.negSucc 339087966767, Int.negSucc 236248224175,
  Int.ofNat 131709538586, Int.ofNat 182702255071, Int.ofNat 397322016450,
  Int.ofNat 408531035339, Int.ofNat 1506944048245, Int.negSucc 1154783624216,
  Int.ofNat 93334335377, Int.ofNat 1739512194834, Int.ofNat 1986918359804,
  Int.negSucc 109185489154, Int.ofNat 327321220527, Int.negSucc 684200609434,
  Int.negSucc 308079963285, Int.negSucc 1659076379336, Int.ofNat 359482407746,
  Int.ofNat 565352991101, Int.negSucc 1169634637207, Int.ofNat 987638652963,
  Int.negSucc 421316117042, Int.ofNat 5731741731067, Int.ofNat 1682684129308,
  Int.ofNat 2159702506760, Int.ofNat 157589748804, Int.negSucc 1286719079094,
  Int.ofNat 1019787721616, Int.ofNat 307777275285, Int.negSucc 2478839343557,
  Int.negSucc 672251538669, Int.negSucc 5476328030343, Int.ofNat 788109507355,
  Int.ofNat 7346434782371, Int.negSucc 445980820144, Int.negSucc 7864120406708,
  Int.negSucc 1228406641422, Int.ofNat 10734260620332, Int.ofNat 8203323626865,
  Int.negSucc 25520218380219, Int.negSucc 96948611629690, Int.negSucc 197802242516619 ]
private def hm2R256V8P5 : List ℤ := [
  Int.negSucc 305306826150124, Int.negSucc 391281067629948, Int.negSucc 435051755288209,
  Int.negSucc 429925818620035, Int.negSucc 383484581974632, Int.negSucc 310316706750488,
  Int.negSucc 228177465211064, Int.negSucc 152287031429498, Int.negSucc 91119891807111,
  Int.negSucc 49140397255656, Int.negSucc 23763807467321, Int.negSucc 9897165131448,
  Int.negSucc 3382351614192, Int.ofNat 920886373644, Int.negSucc 197918706889,
  Int.negSucc 33381458252, Int.negSucc 4091138521 ]
private def hm2R256V8 : List ℤ :=
  hm2R256V8P0 ++ (hm2R256V8P1 ++ (hm2R256V8P2 ++
    (hm2R256V8P3 ++ (hm2R256V8P4 ++ hm2R256V8P5))))
private def hm2R256V9P0 : List ℤ := [
  Int.negSucc 5065, Int.negSucc 867, Int.negSucc 464, Int.ofNat 5835, Int.ofNat 211615,
  Int.ofNat 411659, Int.negSucc 213134, Int.negSucc 82466, Int.negSucc 11994, Int.ofNat 418112,
  Int.ofNat 157398, Int.negSucc 527810, Int.ofNat 321989, Int.negSucc 616072,
  Int.negSucc 256805, Int.negSucc 528604, Int.ofNat 179008, Int.ofNat 664762, Int.ofNat 2182845,
  Int.ofNat 880214, Int.negSucc 1767238, Int.ofNat 410261, Int.negSucc 19436,
  Int.negSucc 1219810, Int.negSucc 2491877, Int.negSucc 462722, Int.ofNat 3565296,
  Int.ofNat 622180, Int.negSucc 1885326, Int.negSucc 7488666, Int.negSucc 5916982,
  Int.ofNat 195475, Int.ofNat 6612558, Int.negSucc 6401708, Int.ofNat 5788072,
  Int.ofNat 4161597, Int.ofNat 449702, Int.negSucc 7601201, Int.negSucc 14805886,
  Int.ofNat 7448389, Int.negSucc 7869318, Int.negSucc 5103255, Int.ofNat 5569218,
  Int.negSucc 3879350, Int.ofNat 6381358, Int.ofNat 11271610, Int.negSucc 12401180,
  Int.negSucc 17420922 ]
private def hm2R256V9P1 : List ℤ := [
  Int.negSucc 4975808, Int.negSucc 12412471, Int.ofNat 9800258, Int.ofNat 12857267,
  Int.ofNat 3658108, Int.negSucc 12187633, Int.negSucc 3212649, Int.negSucc 44812692,
  Int.ofNat 16330348, Int.ofNat 31400823, Int.ofNat 27784981, Int.negSucc 39940359,
  Int.negSucc 14877473, Int.negSucc 31813535, Int.negSucc 16258513, Int.ofNat 29464438,
  Int.ofNat 7916834, Int.ofNat 28774629, Int.ofNat 7547665, Int.negSucc 29701218,
  Int.negSucc 27641764, Int.negSucc 35777995, Int.negSucc 51837180, Int.negSucc 60690327,
  Int.negSucc 30390139, Int.ofNat 24391441, Int.negSucc 22790692, Int.negSucc 57377176,
  Int.negSucc 72511284, Int.negSucc 98717135, Int.ofNat 187695965, Int.ofNat 264516809,
  Int.negSucc 23447878, Int.negSucc 20160106, Int.negSucc 205559285, Int.negSucc 132694041,
  Int.ofNat 83218565, Int.negSucc 55554482, Int.ofNat 29124729, Int.negSucc 62481714,
  Int.ofNat 106424229, Int.ofNat 16762647, Int.negSucc 102272286, Int.negSucc 232409770,
  Int.negSucc 255450899, Int.negSucc 180266775, Int.negSucc 66129893, Int.ofNat 135311126 ]
private def hm2R256V9P2 : List ℤ := [
  Int.ofNat 177600795, Int.ofNat 6662449, Int.negSucc 120872361, Int.negSucc 316779921,
  Int.negSucc 88299776, Int.negSucc 180446217, Int.negSucc 489353689, Int.negSucc 100910717,
  Int.ofNat 89957332, Int.negSucc 77058840, Int.ofNat 260756555, Int.negSucc 280900724,
  Int.ofNat 46120126, Int.negSucc 119975822, Int.negSucc 367571788, Int.negSucc 1393896864,
  Int.negSucc 1090477843, Int.negSucc 558193329, Int.ofNat 1059872807, Int.ofNat 555386957,
  Int.negSucc 146551084, Int.negSucc 207868049, Int.negSucc 7235099, Int.ofNat 175298670,
  Int.ofNat 513012464, Int.negSucc 190630521, Int.ofNat 493422254, Int.ofNat 5233637,
  Int.ofNat 379520584, Int.ofNat 166072502, Int.negSucc 627418842, Int.negSucc 15393443,
  Int.negSucc 190123870, Int.negSucc 921009135, Int.negSucc 1344141112, Int.negSucc 711755752,
  Int.negSucc 877896332, Int.ofNat 201595279, Int.negSucc 1009854214, Int.negSucc 424828006,
  Int.ofNat 211988449, Int.ofNat 371552227, Int.negSucc 1162391170, Int.ofNat 148237523,
  Int.ofNat 312443575, Int.ofNat 1412733697, Int.negSucc 4536205885, Int.negSucc 4020196919 ]
private def hm2R256V9P3 : List ℤ := [
  Int.negSucc 2823523168, Int.negSucc 2615590851, Int.negSucc 650940985, Int.negSucc 2612807415,
  Int.negSucc 864924196, Int.ofNat 372448960, Int.ofNat 1598670221, Int.ofNat 585191028,
  Int.ofNat 1430320685, Int.ofNat 5856711475, Int.ofNat 3812513702, Int.ofNat 4876159094,
  Int.ofNat 4132783368, Int.negSucc 7573996023, Int.negSucc 7939445858, Int.negSucc 259327930,
  Int.ofNat 1701647914, Int.negSucc 5463155268, Int.negSucc 15871523277, Int.negSucc 8465474827,
  Int.negSucc 6320752514, Int.negSucc 14752991573, Int.ofNat 7678291213,
  Int.negSucc 26371969136, Int.negSucc 43525496709, Int.negSucc 23111406624,
  Int.negSucc 13206713146, Int.negSucc 16906766547, Int.negSucc 26538378575,
  Int.negSucc 32971143064, Int.negSucc 62559553060, Int.ofNat 1218710639,
  Int.negSucc 33040871945, Int.negSucc 24499149796, Int.negSucc 1598929701,
  Int.negSucc 69362948738, Int.negSucc 57119951393, Int.negSucc 17317714671,
  Int.ofNat 26274228943, Int.negSucc 10396240768, Int.negSucc 54455369978,
  Int.negSucc 66487941432, Int.negSucc 106187465785, Int.ofNat 79286646552,
  Int.ofNat 120875705191, Int.negSucc 131441394415, Int.ofNat 27070586121, Int.ofNat 5657038855
  ]
private def hm2R256V9P4 : List ℤ := [
  Int.ofNat 97971940342, Int.negSucc 270540411628, Int.negSucc 294553524748,
  Int.negSucc 88146752977, Int.negSucc 466356355856, Int.ofNat 214019712135,
  Int.negSucc 121718635898, Int.negSucc 212499202440, Int.negSucc 20824163615,
  Int.negSucc 182529827413, Int.negSucc 361907629274, Int.negSucc 28908467409,
  Int.negSucc 609055928720, Int.negSucc 397834223868, Int.negSucc 155494699868,
  Int.ofNat 247601565219, Int.ofNat 172257300675, Int.ofNat 929533499172,
  Int.negSucc 330913215130, Int.ofNat 594835073653, Int.negSucc 501343406333,
  Int.negSucc 424011644763, Int.ofNat 725447885882, Int.negSucc 1048551042795,
  Int.negSucc 117954811283, Int.negSucc 1167442370266, Int.negSucc 3553356122243,
  Int.negSucc 3750701077334, Int.negSucc 2923999865514, Int.ofNat 1165861665491,
  Int.ofNat 3821004101274, Int.ofNat 2651560790235, Int.negSucc 5209295546677,
  Int.ofNat 1043716802485, Int.ofNat 749410879159, Int.ofNat 4646837323361,
  Int.negSucc 3036232637611, Int.negSucc 8836417982208, Int.negSucc 3365322079916,
  Int.ofNat 1656900696568, Int.negSucc 3421929430048, Int.ofNat 4635658491579,
  Int.negSucc 3523856422093, Int.negSucc 1758867800299, Int.ofNat 127641901569,
  Int.negSucc 7858973147177, Int.negSucc 1396697260060, Int.negSucc 3255685406091 ]
private def hm2R256V9P5 : List ℤ := [
  Int.negSucc 14715041793838, Int.negSucc 61798302702, Int.ofNat 1542771461046,
  Int.ofNat 7925070059286, Int.negSucc 4891332483751, Int.ofNat 4680861340023,
  Int.ofNat 22377492288512, Int.ofNat 11922515843463, Int.ofNat 36579290420048,
  Int.ofNat 34801673047588, Int.negSucc 98716997793809, Int.negSucc 324891025014518,
  Int.negSucc 541606588244080, Int.negSucc 549604039035748, Int.negSucc 475958880613376,
  Int.negSucc 235462280801482, Int.negSucc 58824341918386 ]
private def hm2R256V9 : List ℤ :=
  hm2R256V9P0 ++ (hm2R256V9P1 ++ (hm2R256V9P2 ++
    (hm2R256V9P3 ++ (hm2R256V9P4 ++ hm2R256V9P5))))
private def hm2Anc0 : List DickeSol.RampKick128kAnchor := [
  ⟨3, hm2SegsR3, hm2RowR3⟩, ⟨4, hm2SegsR4, hm2RowR4⟩, ⟨5, hm2SegsR5, hm2RowR5⟩,
  ⟨6, hm2SegsR6, hm2RowR6⟩, ⟨7, hm2SegsR7, hm2RowR7⟩, ⟨8, hm2SegsR8, hm2RowR8⟩,
  ⟨9, hm2SegsR9, hm2RowR9⟩, ⟨10, hm2SegsR10, hm2RowR10⟩, ⟨12, hm2SegsR12, hm2RowR12⟩,
  ⟨14, hm2SegsR14, hm2RowR14⟩, ⟨20, hm2SegsR20, hm2RowR20⟩, ⟨24, hm2SegsR24, hm2RowR24⟩ ]
private def hm256k256Anchors : List DickeSol.RampKick128kAnchor :=
  hm2Anc0 ++ [⟨256, hm2SegsR256, hm2RowR256⟩]

private theorem hm2Batch0 : hm2AtF [
    DickeSol.rkm128kCheckTable 256 256 2 true hm256k256VPot hm256k256Anchors,
    hm2ChkCell 256 2 48827154462093 1000000000000000 hm256k256VPot hm256k256Anchors,
    hm2SegBds 256 hm2SegsR256, hm2ChkAnchors hm2Anc0
  ] = true := by decide +kernel
private theorem hm2Batch1 :
    hm2ChkSeg 256 hm2R256C0 1 0 1 [Int.ofNat DickeSol.wdScale]
      (1, 256, 37195590, hm2R256V1) = true := by decide +kernel
private theorem hm2Batch2 :
    hm2ChkSeg 256 hm2R256C1 1 256 37195590 hm2R256V1
      (1, 256, 76964283, hm2R256V2) = true := by decide +kernel
private theorem hm2Batch3 :
    hm2ChkSeg 256 hm2R256C2 1 256 76964283 hm2R256V2
      (1, 256, 99525021, hm2R256V3) = true := by decide +kernel
private theorem hm2Batch4 :
    hm2ChkSeg 256 hm2R256C3 1 256 99525021 hm2R256V3
      (1, 256, 118582077, hm2R256V4) = true := by decide +kernel
private theorem hm2Batch5 :
    hm2ChkSeg 256 hm2R256C4 1 256 118582077 hm2R256V4
      (2, 256, 151197393, hm2R256V5) = true := by decide +kernel
private theorem hm2Batch6 :
    hm2ChkSeg 256 hm2R256C5 2 256 151197393 hm2R256V5
      (2, 256, 176151749, hm2R256V6) = true := by decide +kernel
private theorem hm2Batch7 :
    hm2ChkSeg 256 hm2R256C6 2 256 176151749 hm2R256V6
      (2, 256, 208463880, hm2R256V7) = true := by decide +kernel
private theorem hm2Batch8 :
    hm2ChkSeg 256 hm2R256C7 2 256 208463880 hm2R256V7
      (2, 256, 239215340, hm2R256V8) = true := by decide +kernel
private theorem hm2Batch9 :
    hm2ChkSeg 256 hm2R256C8 2 256 239215340 hm2R256V8
      (2, 256, 275504963, hm2R256V9) = true := by decide +kernel
private theorem hm2Batch10 :
    hm2ChkFin 256 hm2R256C9 2 256 275504963 hm2R256V9 hm2RowR256 = true := by decide +kernel

private theorem hm2Row256Sound :
    DickeSol.rkm128kEvalRowLo12 256 2 256 hm2SegsR256 = hm2RowR256 := by
  apply hm2CertSplit (hm2_hd (hm2_tl2 hm2Batch0)); unfold hm2SegsR256
  exact hm2TailStep hm2Batch1 (hm2TailStep hm2Batch2 (hm2TailStep hm2Batch3
    (hm2TailStep hm2Batch4 (hm2TailStep hm2Batch5 (hm2TailStep hm2Batch6
      (hm2TailStep hm2Batch7 (hm2TailStep hm2Batch8
        (hm2TailStep hm2Batch9 (hm2TailEnd hm2Batch10)))))))))
private theorem hm2AncSound :
    DickeSol.RampKick128kAnchorsSound 256 2 hm256k256Anchors :=
  hm2ChkAnchors_append (hm2_hd (hm2_tl1 (hm2_tl2 hm2Batch0))) ⟨hm2Row256Sound, trivial⟩
private theorem hm256k256Valid :
    DickeSol.RampKick128kTableValid 256 256 2 true hm256k256VPot hm256k256Anchors :=
  DickeSol.rkm128kCheckTable_sound hm2AncSound (hm2_hd hm2Batch0)
private theorem hm256k256CellChecks {m k : ℕ}
    (h : isHiTailM256K256KrotovCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (hiTailM256K256KrotovCertCellLMax m k)
        hm256k256Anchors = true ∧
      ∃ num den : ℕ, relCostHiTailM256K256KrotovCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (hm256k256VPot.getD k 0) num den = true := by
  unfold isHiTailM256K256KrotovCertCell at h
  split_ifs at h with hm256 hk256
  simp only [beq_iff_eq] at hm256 hk256
  subst hm256 hk256; have hm := hm2_hd (hm2_tl1 hm2Batch0)
  exact ⟨hm2_and_l hm, 48827154462093, 1000000000000000, rfl, hm2_and_r hm⟩

private lemma hm256k256_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma hm256k256_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma hm256k256_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private lemma hm256k256_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d

private lemma hm256k256_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) :
    2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (hm256k256_le_of_add h), rfl⟩

private structure Hm256k256CellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk256 : k ≤ 256
  hm2 : 2 ≤ m
  hl2 : 2 ≤ hiTailM256K256KrotovCertCellLMax m k
  hl1 : 1 ≤ hiTailM256K256KrotovCertCellLMax m k
  hlm : hiTailM256K256KrotovCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 256 2 true hm256k256VPot hm256k256Anchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (hiTailM256K256KrotovCertCellLMax m k)
    hm256k256Anchors = true
  hcost : ∃ num den : ℕ, relCostHiTailM256K256KrotovCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (hm256k256VPot.getD k 0) num den = true

private lemma hm256k256_mk {k : ℕ} (j d1 dk dl2 dl1 dlm : ℕ) (hj : (j + 1) + d1 = 11)
    (h256 : k + dk = 256) (hl2 : 2 + dl2 = hiTailM256K256KrotovCertCellLMax 256 k)
    (hl1 : 1 + dl1 = hiTailM256K256KrotovCertCellLMax 256 k)
    (hlm : hiTailM256K256KrotovCertCellLMax 256 k * 256 + dlm = 65536) (hk : 2 ^ j = k)
    (hlmax : DickeSol.rkm128kCheckAnchorsLMax k (hiTailM256K256KrotovCertCellLMax 256 k)
      hm256k256Anchors = true)
    (hcost : ∃ num den : ℕ, relCostHiTailM256K256KrotovCert 256 k = NNRat.divNat num den ∧
      DickeSol.checkAltBound12 256 k (hm256k256VPot.getD k 0) num den = true) :
    Hm256k256CellProps 256 k :=
  ⟨hm256k256_mem_grid 8 2 rfl, hk ▸ hm256k256_mem_grid j d1 hj, hm256k256_le_of_add h256,
    hm256k256_le_of_add (rfl : 2 + 254 = 256), hm256k256_le_of_add hl2, hm256k256_le_of_add hl1,
    hm256k256_le_of_add hlm, hm256k256Valid, hlmax, hcost⟩

private theorem hm256k256_all_props {m k : ℕ}
    (h : isHiTailM256K256KrotovCertCell m k = true) :
    Hm256k256CellProps m k := by
  rcases hm256k256CellChecks h with ⟨hlmax, hcost⟩; unfold isHiTailM256K256KrotovCertCell at h
  split_ifs at h with hm256 hk256
  simp only [beq_iff_eq] at hm256 hk256
  subst hm256 hk256; exact hm256k256_mk 8 2 0 0 1 65024 rfl rfl rfl rfl rfl rfl hlmax hcost

private noncomputable def hiTailM256K256KrotovCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM256K256KrotovCertQubits n m k)) Var
      (hiTailM256K256KrotovCertQubits n m k) ((n + 1) * m) :=
  if h : isHiTailM256K256KrotovCertCell m k = true then
    let p := hm256k256_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG hm256k256VPot hm256k256Anchors p.hk256
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit on the supported (256, 256) cell. -/
noncomputable def findAllJohnsonRampKick128kHiTailM256K256KrotovCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM256K256KrotovCertQubits n m k)) Var
      (hiTailM256K256KrotovCertQubits n m k) ((n + 1) * m) :=
  hiTailM256K256KrotovCertCircuitImpl res n m k

private lemma hm256k256_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isHiTailM256K256KrotovCertCell m k = true) :
    findAllJohnsonRampKick128kHiTailM256K256KrotovCertCircuit res n m k =
      let p := hm256k256_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG hm256k256VPot hm256k256Anchors p.hk256
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kHiTailM256K256KrotovCertCircuit
    hiTailM256K256KrotovCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-1 recovery of S on the supported (256, 256) cell. -/
theorem hiTailM256K256KrotovCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isHiTailM256K256KrotovCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ ⊤ ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kHiTailM256K256KrotovCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [hm256k256_targetSets_eq]
  have hp := hm256k256_all_props hcell
  rw [hm256k256_circuit_eq res n hcell, ← hm256k256_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG hm256k256VPot hm256k256Anchors hp.hk256
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound on the supported (256, 256) cell. -/
theorem hiTailM256K256KrotovCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isHiTailM256K256KrotovCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kHiTailM256K256KrotovCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostHiTailM256K256KrotovCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := hm256k256_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG hm256k256VPot
    hm256k256Anchors hp.hk256 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [hm256k256_circuit_eq res n hcell, ← hm256k256_oracle_eq]
    exact hq S (by rwa [hm256k256_targetSets_eq])
  · rw [← hm256k256_targetSets_eq, ← hm256k256_vanilla_eq]; exact hsum

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

end Rk128kHiM256K256KrCert
end QuantumComputation.Specs.GroverFindAll
