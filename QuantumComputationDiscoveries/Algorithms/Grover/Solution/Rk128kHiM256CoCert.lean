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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256CoPt0
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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM8K128KrCert

/-
# 128-Segment 128k `m = 256` Mode-1 Certificate (`Rk128kHiM256CoCert`)

QHL-verified module packaging all `6` `m = 256, k ≤ 256` cells
(`(256, 8), (256, 16), (256, 32), (256, 64), (256, 128), (256, 256)`) by chaining
`Rk128kHiM256CoPt0` (`38` `r ≤ 128` prefix anchors plus `r = 256` segment `0`) with
`r = 256` segments `1..118` and finalize (`421,376` Horner coord-ops at `lTableMax = 2`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kHiM256CoCert

@[expose] public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Supported `(m, k)` cells (`m = 256, k ∈ {8, 16, 32, 64, 128, 256}`, `6` cells). -/
def isHiTailM256CoCertCell (m k : ℕ) : Bool :=
  if m == 256 then
    if k == 8 then true
    else if k == 16 then true
    else if k == 32 then true
    else if k == 64 then true
    else if k == 128 then true
    else if k == 256 then true
    else false
  else false

/-- Per-cell workspace multiplexing factor `L_{\max}(256, k) = 2` across `k ∈ {8..256}`. -/
def hiTailM256CoCertCellLMax (m k : ℕ) : ℕ :=
  if m == 256 then
    if k == 8 then 2
    else if k == 16 then 2
    else if k == 32 then 2
    else if k == 64 then 2
    else if k == 128 then 2
    else if k == 256 then 2
    else 1
  else 1

/-- Total register qubit budget `(hiTailM256CoCertCellLMax m k * m) * (n + 1) + k * n`. -/
abbrev hiTailM256CoCertQubits (n m k : ℕ) : ℕ :=
  (hiTailM256CoCertCellLMax m k * m) * (n + 1) + k * n

/-- Certified relative-cost profile `c(m, k): ℚ≥0` across the `6` `m = 256, k ≤ 256` cells. -/
def relCostHiTailM256CoCert (m k : ℕ) : ℚ≥0 :=
  if m == 256 then
    if k == 8 then NNRat.divNat 56685214054921 250000000000000
    else if k == 16 then NNRat.divNat 6047258346089 40000000000000
    else if k == 32 then NNRat.divNat 51771084026387 500000000000000
    else if k == 64 then NNRat.divNat 73425717276763 1000000000000000
    else if k == 128 then NNRat.divNat 436301823401 7812500000000
    else if k == 256 then NNRat.divNat 24416968724737 500000000000000
    else 1
  else 1

/-- Cost profile metadata (`n0 = 80000`, constructive threshold). -/
def hiTailM256CoCertProfile : FindAllCostProfile :=
  ⟨isHiTailM256CoCertCell, relCostHiTailM256CoCert, fun _ _ ↦ 80000⟩

/-- Every supported `Rk128kHiM256CoCert` cell lies on `groverGrid × groverGrid`. -/
theorem isHiTailM256CoCertCell_isGridCell {m k : ℕ}
    (h : isHiTailM256CoCertCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isHiTailM256CoCertCell at h
  split_ifs at h with hm256 hk8 hk16 hk32 hk64 hk128 hk256
  all_goals simp only [beq_iff_eq] at *
  · subst hm256 hk8; rfl
  · subst hm256 hk16; rfl
  · subst hm256 hk32; rfl
  · subst hm256 hk64; rfl
  · subst hm256 hk128; rfl
  · subst hm256 hk256; rfl

end

public section

open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

private def htbNatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private def htbListNatEq (xs ys : List ℕ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (htbNatEq x y) (htbListNatEq xr yr) false
  | _, _ => false
private lemma htbNatEq_eq {x y : ℕ} (h : htbNatEq x y = true) : x = y := by
  unfold htbNatEq at h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
private lemma htbListNatEq_eq {xs ys : List ℕ} (h : htbListNatEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with | nil => cases h | cons y yr =>
      change cond (htbNatEq x y) (htbListNatEq xr yr) false = true at h
      cases hxy : htbNatEq x y <;> rw [hxy] at h <;> [cases h; rw [htbNatEq_eq hxy, ih h]]
private def htbIntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => htbNatEq m n
  | Int.negSucc m, Int.negSucc n => htbNatEq m n
  | _, _ => false
private lemma htbIntEq_eq {a b : ℤ} (h : htbIntEq a b = true) : a = b := by
  cases a <;> cases b <;> first | cases h | exact congrArg _ (htbNatEq_eq h)
private def htbListIntEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (htbIntEq x y) (htbListIntEq xr yr) false
  | _, _ => false
private lemma htbListIntEq_eq {xs ys : List ℤ} (h : htbListIntEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with | nil => cases h | cons y yr =>
      change cond (htbIntEq x y) (htbListIntEq xr yr) false = true at h
      cases hxy : htbIntEq x y <;> rw [hxy] at h <;> [cases h; rw [htbIntEq_eq hxy, ih h]]
private abbrev htbP : ℕ → ℤ := Int.ofNat
private abbrev htbN : ℕ → ℤ := Int.negSucc
private abbrev HtbSt := ℕ × ℕ × ℕ × List ℤ
private def htbStEq (a b : HtbSt) : Bool :=
  match a, b with
  | (a1, a2, a3, av), (b1, b2, b3, bv) =>
    cond (htbNatEq a1 b1) (cond (htbNatEq a2 b2)
      (cond (htbNatEq a3 b3) (htbListIntEq av bv) false) false) false
private lemma htbStEq_eq {a b : HtbSt} (h : htbStEq a b = true) : a = b := by
  rcases a with ⟨a1, a2, a3, av⟩; rcases b with ⟨b1, b2, b3, bv⟩
  change cond (htbNatEq a1 b1) (cond (htbNatEq a2 b2)
    (cond (htbNatEq a3 b3) (htbListIntEq av bv) false) false) false = true at h
  cases h1 : htbNatEq a1 b1 <;> rw [h1] at h; · cases h
  cases h2 : htbNatEq a2 b2 <;> rw [h2] at h; · cases h
  cases h3 : htbNatEq a3 b3 <;> rw [h3] at h; · cases h
  exact Prod.ext (htbNatEq_eq h1) (Prod.ext (htbNatEq_eq h2)
    (Prod.ext (htbNatEq_eq h3) (htbListIntEq_eq h)))
private def htbAtF (bs : List Bool) : Bool :=
  match bs with | [] => true | b :: rest => cond b (htbAtF rest) false
private lemma htb_hd {b : Bool} {bs : List Bool} (h : htbAtF (b :: bs) = true) :
    b = true := by unfold htbAtF at h; cases b <;> first | cases h | rfl
private lemma htb_tl1 {b : Bool} {s : List Bool} (h : htbAtF (b :: s) = true) :
    htbAtF s = true := by unfold htbAtF at h; cases b <;> first | cases h | exact h
private lemma htb_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : htbAtF (b1 :: b2 :: bs) = true) : htbAtF bs = true := htb_tl1 (htb_tl1 h)
private lemma htb_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : htbAtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : htbAtF bs = true := htb_tl2 (htb_tl2 h)
private lemma htb_and_l {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a <;> cases h; rfl
private lemma htb_and_r {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a <;> cases b <;> cases h; rfl
private abbrev htbM (l t n d r : ℕ) (w : List ℕ) : DickeSol.Rkm128kSeg :=
  ⟨l, t, n, d, DickeSol.rkm128kMask56 r w⟩
private def htbChkSlice (r : ℕ) (s : List DickeSol.Rkm128kSeg)
    (l0 d0 p0 : ℕ) (v0 : List ℤ) (st1 : HtbSt) : Bool :=
  htbStEq (DickeSol.rkm128kRunSegs 256 2 r s l0 d0 p0 v0) st1
private lemma htb_sl_end {s : List DickeSol.Rkm128kSeg} {l0 d0 p0 : ℕ}
    {v0 : List ℤ} {st1 : HtbSt} (h : htbChkSlice 256 s l0 d0 p0 v0 st1 = true) :
    DickeSol.rkm128kRunSegs 256 2 256 s l0 d0 p0 v0 = st1 := by
  unfold htbChkSlice at h; exact htbStEq_eq h
private lemma htb_sl_step {s1 s2 : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ} {st2 : HtbSt}
    (h1 : htbChkSlice 256 s1 l0 d0 p0 v0 (l1, d1, p1, v1) = true)
    (h2 : DickeSol.rkm128kRunSegs 256 2 256 s2 l1 d1 p1 v1 = st2) :
    DickeSol.rkm128kRunSegs 256 2 256 (s1 ++ s2) l0 d0 p0 v0 = st2 := by
  unfold htbChkSlice at h1; rw [DickeSol.rkm128kRunSegs_append, htbStEq_eq h1]; exact h2
private lemma htb_s0_glue {s1 s2 : List DickeSol.Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1a v1b : List ℤ} {st2 : HtbSt}
    (h1 : DickeSol.rkm128kRunSegs 256 2 256 s1 l0 d0 p0 v0 = (l1, d1, p1, v1a))
    (hv : v1a = v1b)
    (h2 : DickeSol.rkm128kRunSegs 256 2 256 s2 l1 d1 p1 v1b = st2) :
    DickeSol.rkm128kRunSegs 256 2 256 (s1 ++ s2) l0 d0 p0 v0 = st2 := by
  rw [DickeSol.rkm128kRunSegs_append, h1, hv]; exact h2
private def htbSegsGuard (r : ℕ) (segs : List DickeSol.Rkm128kSeg) : Bool :=
  Bool.and (Nat.ble 1 (DickeSol.rkm128kSegListLen segs))
    (Bool.and (Nat.ble (DickeSol.rkm128kSegListLen segs) 128)
      (Bool.and (Nat.ble 2 r) (Nat.ble r 1024)))
private def htbFinGuard (st : HtbSt) (ro : List ℕ) : Bool :=
  htbListNatEq (DickeSol.rkm128kFinalizeState st) ro
private lemma htb_cert_row (r : ℕ) (segs : List DickeSol.Rkm128kSeg)
    (st : HtbSt) (ro : List ℕ) (hsegs : htbSegsGuard r segs = true)
    (hrun : DickeSol.rkm128kRunSegs 256 2 r segs 1 0 1 [Int.ofNat DickeSol.wdScale] = st)
    (hfin : htbFinGuard st ro = true) :
    DickeSol.rkm128kEvalRowLo12 256 2 r segs = ro := by
  unfold htbSegsGuard at hsegs; unfold htbFinGuard at hfin
  exact @DickeSol.rkm128kCertRow_of_runSegs 256 2 r segs st ro hsegs hrun (htbListNatEq_eq hfin)
private def htbChkCell (k lm n d : ℕ) (v : List ℕ) (a : List DickeSol.RampKick128kAnchor) :
    Bool := Bool.and (DickeSol.rkm128kCheckAnchorsLMax k lm a)
      (DickeSol.checkAltBound12 256 k (v.getD k 0) n d)
private lemma htbChkCell_l {k lm n d : ℕ} {v : List ℕ} {a : List DickeSol.RampKick128kAnchor}
    (h : htbChkCell k lm n d v a = true) : DickeSol.rkm128kCheckAnchorsLMax k lm a = true := by
  unfold htbChkCell at h; exact htb_and_l h
private lemma htbChkCell_r {k lm n d : ℕ} {v : List ℕ} {a : List DickeSol.RampKick128kAnchor}
    (h : htbChkCell k lm n d v a = true) :
    DickeSol.checkAltBound12 256 k (v.getD k 0) n d = true := by
  unfold htbChkCell at h; exact htb_and_r h
private lemma htb_anc_append {xs ys : List DickeSol.RampKick128kAnchor}
    (hx : DickeSol.RampKick128kAnchorsSound 256 2 xs)
    (hy : DickeSol.RampKick128kAnchorsSound 256 2 ys) :
    DickeSol.RampKick128kAnchorsSound 256 2 (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons _ _ ih => rcases hx with ⟨h1, h2⟩; exact ⟨h1, ih h2⟩
private abbrev htbS0Pfx :=
  GroverFindAll.Rk128kHiM256CoPt0.pfxAnchorsLt256
private abbrev htbS0Segs :=
  GroverFindAll.Rk128kHiM256CoPt0.s0Segs
private abbrev htbS0Vec :=
  GroverFindAll.Rk128kHiM256CoPt0.s0Vec

private def htbSegs_r256_0 : List DickeSol.Rkm128kSeg :=
  [ htbM 1 452954 1 10 107 [16894662669008896, 1717732154647073],
    htbM 1 452954 1 10 163 [6954964897955840, 56785496157422498, 1484108973628587],
    htbM 1 452954 1 10 217 [42895633021140992, 22675262054536855,
      2408334993688350, 357578231057232],
    htbM 1 452954 1 10 242 [42474643932577792, 39394024007469238,
      3285997966415991, 70012789236175007,
      200239],
    htbM 1 452955 1 10 252 [46412527359229952, 67583005554043659,
      2168595788661262, 40229305572999325,
      205262874],
    htbM 1 452957 1 10 257 [58667176671838208, 69682485658264900,
      58309541957535553, 47141953389496249,
      5932469486],
    htbM 1 452958 1 10 256 [26534102702227456, 9088677578324851,
      29086572374495339, 42426205520497918,
      2698911434],
    htbM 1 452959 1 10 257 [66225557938896896, 25197997183933589,
      22223084787090375, 38009816596551265,
      7753995110],
    htbM 1 467817 1 10 252 [7003499837521920, 9301506031526569,
      24456200879148853, 25215366984631452,
      258367446],
    htbM 1 467824 1 10 256 [1874278630817792, 13716511115803550,
      59420850322170018, 33928319101598854,
      2290709143],
    htbM 1 467833 1 10 257 [17235549140025344, 57381735015538443,
      64739737054118404, 60602960265623071,
      4358234401],
    htbM 1 467847 1 10 252 [61334813046472704, 32365497865946749,
      50604720797947047, 13050319633139700,
      256226187],
    htbM 1 467853 1 10 256 [45254524209725440, 26666465858878053,
      3130355824995135, 38325935647986862,
      2409277822],
    htbM 1 467884 1 10 257 [3560218650738688, 201132550777384,
      58846722485912488, 54268816787601508,
      4718705977],
    htbM 1 467900 1 10 255 [64308236085362688, 67406697064332896,
      10953226194362766, 69364964432370166,
      2102318603],
    htbM 1 467908 1 10 257 [59883801295192064, 45125942920374033,
      58586470495703790, 58821811788252187,
      5758399879],
    htbM 1 453071 1 10 257 [38843546786070528, 53744770048719694,
      52426845940289825, 832919398574064,
      6363315300] ]
private def htbSegs_r256_1 : List DickeSol.Rkm128kSeg :=
  [ htbM 1 453083 1 10 256 [6755399441055744, 71094523373562149,
      51441820141588943, 66220167146846658,
      3419815944],
    htbM 1 453099 1 10 256 [54043195528445952, 37629481097854079,
      46093906178004664, 14762087083771277,
      2340498788],
    htbM 1 453114 1 10 255 [0, 63705199054285971,
      41618968728661505, 60159387139111216,
      2042553292],
    htbM 1 453122 1 10 257 [0, 24346871073119896,
      11242523224222413, 25805490155164412,
      7805910868],
    htbM 1 453122 1 10 257 [0, 58716352174889152,
      58098843208195497, 62116264387021568,
      8144103113],
    htbM 1 453123 1 10 257 [0, 49099176601371136,
      11332603288405417, 56787152818070471,
      8013359585],
    htbM 1 453123 1 10 256 [0, 61289175071954944, 719929694890376, 27099250914414134, 3697031306],
    htbM 1 453124 1 10 257 [72057594037927935, 28128647362265087,
      646171313332028, 45933610621208035,
      5796952503],
    htbM 1 472020 1 12 257 [0, 37500194164965376,
      16120893678753485, 65468423693628893,
      7738676986],
    htbM 1 472021 1 12 257 [16, 2655804749512704,
      64477361366427153, 27560490259495978,
      5375727245],
    htbM 1 472022 1 12 256 [89, 52485444071325696,
      39116849602011076, 57574078009558919,
      2880713423],
    htbM 1 472024 1 12 256 [82, 22582052842897408,
      875362617624665, 48593621715405147,
      4231714097],
    htbM 1 472025 1 12 256 [977, 38477673286074368,
      29234102524249896, 5252586322129807,
      2958762278],
    htbM 1 472026 1 12 256 [2422, 28876753053155328,
      5498753002119962, 53764337866872064,
      4019767678],
    htbM 1 472026 1 12 257 [1680, 17119224245780480,
      7082554287738851, 49254344590822611,
      7286643038] ]
private def htbSegs_r256_2 : List DickeSol.Rkm128kSeg :=
  [ htbM 1 472025 1 12 257 [72057594037865288, 3167967877529599,
      5065736313371071, 45340823943539479,
      5658972484],
    htbM 1 452639 1 12 257 [205230, 29697809066229760,
      55310138606579015, 18617855875676773,
      4670871973],
    htbM 1 452638 1 12 256 [704854, 52943683900669952,
      5546596950077572, 67613883631911628,
      2645591188],
    htbM 1 452641 1 12 256 [1049395, 64105925945851904,
      61045672933085640, 43503349241435899,
      4205680798],
    htbM 1 452641 1 12 256 [55631164, 60235645016080384,
      18473525892430515, 9679719777240081,
      3629486298],
    htbM 1 452641 1 12 256 [121811749, 4503599627370496,
      24655506515048574, 34286304277823704,
      2405772512],
    htbM 1 452641 1 12 257 [300665323, 54043195528445952,
      70232165513186572, 358780766507804,
      6648489823],
    htbM 1 452649 1 12 257 [5636532737, 0, 64360559992685342, 69832779693298016, 7165837846],
    htbM 1 452654 1 12 257 [36217025499, 0, 58972694656775056, 32839404740567055, 4314192309],
    htbM 1 452656 1 12 257 [230094466161, 0, 18443174239655872, 70693716231018950, 6711260103],
    htbM 1 452659 1 12 254 [2640849849861, 0, 68084112589217280, 71099127718338701, 713418900],
    htbM 1 452660 1 12 256 [272859011067, 0, 18389232279943168, 57209082199488509, 4257538827],
    htbM 1 452668 1 12 257 [11851636472307, 0, 62722639337930752, 16198937548130677, 7436772681],
    htbM 1 452669 1 12 256 [2231264792837472, 0,
      69609570585411584, 41403319886575377,
      2324137190] ]
private def htbSegs_r256_3 : List DickeSol.Rkm128kSeg :=
  [ htbM 1 452671 1 12 257 [4721536713634457, 0,
      25049496462819328, 40728876365993996,
      5363144402],
    htbM 1 452677 1 12 256 [38407652918485776, 0,
      20701888185892864, 28954129781376307,
      3675794070],
    htbM 1 452687 1 12 257 [35665258954020343, 14,
      46458897564696576, 51935373707829892,
      6426079361],
    htbM 1 452691 1 12 257 [28203458222210180, 47,
      37955167429066752, 69733966177700129,
      7954205828],
    htbM 1 452710 1 12 257 [57834470568913325, 395,
      10345282357166080, 70291557801541294,
      7454243903],
    htbM 1 452714 1 12 256 [64547075176069474, 3947,
      30091563077992448, 61735677262790416,
      3802053831],
    htbM 1 452727 1 12 256 [34857500710362286, 127678,
      29560988588048384, 28641326066646561,
      3112941508],
    htbM 1 452731 1 12 257 [10380844218017104, 493886,
      40616784163766272, 52948809053529691,
      7329109460],
    htbM 1 452732 1 12 256 [41272499655444243, 6033040,
      6001134464401408, 43249848860107616,
      4190899376],
    htbM 1 452733 1 12 256 [20874154305689722, 17853037,
      24870953020293120, 28033773702631291,
      3164304662],
    htbM 1 452739 1 12 257 [49212350149198431, 155340995,
      57983845202395136, 46494675428675820,
      8059452891],
    htbM 1 452748 1 12 257 [7760884445900613, 367743096,
      52917295621603328, 28643044903819326,
      5445900676],
    htbM 1 452759 1 12 257 [48765850707935435, 24251245567,
      34902897112121344, 23881844603514955,
      5588692741],
    htbM 1 452760 1 12 257 [64109797705774730, 144028741748,
      40532396646334464, 9400695755118589,
      6667963854] ]
private def htbSegs_r256_4 : List DickeSol.Rkm128kSeg :=
  [ htbM 1 452770 1 12 255 [8740773625319387, 781831920571,
      63050394783186944, 35406859958462183,
      1648998643],
    htbM 1 452778 1 12 257 [30555140346632411, 21921213846304, 0, 42688765973315559, 5404617351],
    htbM 1 452778 1 12 257 [69450688437826993, 31649228133092, 0, 32487085518097106, 8308032867],
    htbM 1 452783 1 12 257 [14958060136757353, 1124624072704707, 0, 7898482155995224, 8255078980],
    htbM 1 452760 1 12 257 [7172556055058256, 5053731295411253, 0, 12003735164387552, 5291374134],
    htbM 1 452836 1 12 255 [6908697295625686, 32777595888404080,
      0, 27416824186189440,
      1888989148],
    htbM 1 452841 1 12 256 [27620515111118578, 38225120630381984,
      1, 5030955647024896,
      3449270203],
    htbM 1 453016 1 12 253 [69746889196976804, 50367809893279525,
      22, 61962884994840576,
      349289271],
    htbM 1 453044 1 12 257 [30318487689483382, 22970703949843745,
      611, 39872606450581504,
      6212435172],
    htbM 1 453110 1 12 257 [64418738815203610, 42199220680715927,
      3491, 21560885397602304,
      7618315574],
    htbM 1 453035 1 12 257 [30316732507251146, 18606097619707167,
      18796, 34688919106551808,
      5363310441],
    htbM 1 453418 1 12 257 [60847915788307339, 23559719593916498,
      582026, 13251766435053568,
      7595395329],
    htbM 1 453404 1 12 256 [13335293639038390, 28560224509044991,
      72057594034553223, 19008795107131391,
      3173107471],
    htbM 2 438347 1 18 254 [15832844632187798, 14967380053462308,
      40327468, 48972310253666304,
      853028380] ]
private def htbSegs_r256_5 : List DickeSol.Rkm128kSeg :=
  [ htbM 2 438777 1 18 257 [46110012490181362, 42161625463985232,
      286269125, 20750636341526528,
      4469315513],
    htbM 2 438153 1 18 257 [70263876224780896, 40949024584753209,
      37537676281, 24492584386691072,
      6214010616],
    htbM 2 439546 1 18 256 [2390109219345956, 57181070844177611,
      1972502391059, 62768926248927232,
      2657937500],
    htbM 2 440062 1 18 257 [38220914892153824, 35775303201213020,
      2174145071400, 69805828583981056,
      7208277732],
    htbM 2 439572 1 18 257 [36810011608427800, 40342938856677238, 987738159400879, 0, 8326748640],
    htbM 2 439723 1 18 257 [58150054469181888, 58236123639437651,
      17494390161040923, 0,
      5188701040],
    htbM 2 439684 1 18 257 [44983557694229668, 59362298148408654,
      20356003836538764, 35184372088839,
      5266067136],
    htbM 2 435499 1 18 255 [40110745213386918, 47885100368322722,
      58325914181390383, 429,
      1617942528],
    htbM 2 435014 1 18 257 [6090725374926295, 15541685591660810,
      11802078419886684, 562949953423437,
      6848479232] ]
private def htbSegs_r256_6 : List DickeSol.Rkm128kSeg :=
  [ htbM 2 439336 1 18 257 [46623508552441298, 69061380327620833,
      41730436285118302, 2251799813807010,
      5991366656],
    htbM 2 410700 1 18 257 [43535478410828895, 58050044463571778,
      68117352314535526, 9007199255888981,
      6986072064],
    htbM 2 489349 1 20 257 [69784823723425730, 6051300002008141,
      59839886865487349, 19679444,
      4712316928],
    htbM 2 488813 1 20 253 [66778421977321353, 23579425348975552,
      55498918854820098, 766849663,
      503349248],
    htbM 2 491279 1 20 257 [27139532414571024, 28846421529268770,
      7096688205134080, 954735641,
      4404019200],
    htbM 2 490599 1 20 256 [16576486203986705, 41815637575218315,
      67699110297065466, 251938003689,
      3364093952],
    htbM 2 517777 1 20 250 [13310978517379705, 10918901935755853,
      23937262320982731, 37453903184,
      36175872],
    htbM 2 517100 1 20 256 [54978329829582236, 42641766775579313,
      2947996918786789, 59718423384553,
      2147483648] ]
private def htbSegs_r256_7 : List DickeSol.Rkm128kSeg :=
  [ htbM 2 518242 1 20 248 [19088646481167492, 44102906741672481,
      43865812612615607, 38517359806469,
      8388608],
    htbM 2 528110 1 20 249 [62220689571599529, 8584015813279479,
      59187719694554558, 8721720202952558,
      16777216],
    htbM 2 523322 1 20 250 [7606969163252604, 24999692754576520,
      595024601698543, 36382839797211850,
      33554432],
    htbM 2 482686 1 20 250 [8746505470624040, 16949018047095002,
      5001223861248384, 310322803780,
      33554437],
    htbM 2 482168 1 20 251 [29423776158716643, 7355988578051077,
      65170837142354486, 38386150888539661,
      67108898],
    htbM 2 432076 1 18 232 [13867371610604460, 5664918859396377,
      34124431137944024, 40778783978100013,
      249],
    htbM 2 452660 1 18 226 [15475940874376309, 32984253328226552,
      1780587394636880, 4813680362531616,
      3],
    htbM 2 466839 1 20 254 [1795499306997743, 10511014711747641,
      36103548376282029, 572339045690638,
      536870912],
    htbM 2 453181 1 18 234 [32648058971638443, 68282854957493615,
      10639096379665210, 5506513157238666,
      512] ]
private def htbSegs_r256_8 : List DickeSol.Rkm128kSeg :=
  [ htbM 2 398528 1 18 226 [70255271100506972, 64178701722754941,
      18667803480445361, 19360202340320009,
      2],
    htbM 2 384964 1 16 256 [54223378931583996, 58662403518089023,
      56366161752100825, 18368441303049892,
      2147713669],
    htbM 2 381785 1 16 243 [60918880964403825, 67709715436922033,
      7022741706255980, 144041392222555,
      262146],
    htbM 2 387795 1 16 240 [55198478354151109, 24452578395257702,
      36068702097675260, 16923958334129364,
      32769],
    htbM 2 374417 1 16 256 [60843931449593503, 3866992254106122,
      6844000424568843, 29537645660999296,
      2150852745],
    htbM 2 332438 1 16 235 [66743790628915053, 1034107434462385,
      18043447019596450, 20284136254080199,
      1024],
    htbM 2 338236 1 16 248 [23642533490781284, 69072700377816234,
      1206551465036865, 25573080229910450,
      12269875],
    htbM 2 404680 1 18 244 [40933297451526635, 1418834604293234,
      5631114614090801, 317776048801052,
      524288],
    htbM 2 416456 1 18 242 [39118434410890377, 18913818696211523,
      18577464698176520, 18159568404188549,
      131072],
    htbM 2 403152 1 18 219 [10271812085957790, 10450902349233861,
      5928635529793057, 1125899907936418] ]
private def htbSegs_r256_9 : List DickeSol.Rkm128kSeg :=
  [ htbM 2 407998 1 18 252 [63915735495133502, 50745157572053001,
      63995511248315441, 11982503901208932,
      246535862],
    htbM 2 392915 1 16 229 [10496085622642409, 13660448238882489,
      18015532917723137, 69210704,
      16],
    htbM 2 399186 1 18 225 [18265920644980632, 1161120250333349,
      27603256595212672, 5366175374514968,
      1],
    htbM 2 404315 1 18 254 [47117881101789621, 30022423256721989,
      52234908537144148, 4279333757924467,
      963873467],
    htbM 2 423451 1 18 227 [23411901365257967, 27303353102074866,
      8796160266928, 9086364091977729,
      4],
    htbM 2 410235 1 18 255 [57752067409291718, 53376902225866810,
      3824394459551, 31586199657697257,
      2136969738],
    htbM 2 406189 1 18 212 [20275003027097916, 1114180, 12885037568, 8796160131074],
    ⟨2, 404695, 1, 18, []⟩ ]
private abbrev htbTail_r256_8 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_8 ++ htbSegs_r256_9
private abbrev htbTail_r256_7 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_7 ++ htbTail_r256_8
private abbrev htbTail_r256_6 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_6 ++ htbTail_r256_7
private abbrev htbTail_r256_5 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_5 ++ htbTail_r256_6
private abbrev htbTail_r256_4 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_4 ++ htbTail_r256_5
private abbrev htbTail_r256_3 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_3 ++ htbTail_r256_4
private abbrev htbTail_r256_2 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_2 ++ htbTail_r256_3
private abbrev htbTail_r256_1 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_1 ++ htbTail_r256_2
private abbrev htbTail_r256_0 : List DickeSol.Rkm128kSeg :=
  htbSegs_r256_0 ++ htbTail_r256_1
private def htbSegs_r256 : List DickeSol.Rkm128kSeg := htbS0Segs ++ htbTail_r256_0
private def htbVec_r256_0 : List ℤ :=
  [ htbP 973464840338461, htbP 225790178669534, htbP 36887129735784, htbP 4901086851957,
    htbP 561729460140, htbP 57357227917, htbP 5325129204, htbP 455738665, htbP 36350917,
    htbP 2794312, htbP 197722 ]
private def htbVec_r256_1 : List ℤ :=
  [ htbP 102174565662, htbP 454392633694, htbP 1423113423234, htbP 3624331331218,
    htbP 7961065458383, htbP 15576548828527, htbP 27707064152306, htbP 45439741916029,
    htbP 69419263684111, htbP 99571310065627, htbP 134924291437550, htbP 173588915123562,
    htbP 212924527321350, htbP 249865519044918, htbP 281349552363732, htbP 304752921016397,
    htbP 318252668403878, htbP 321040864605784, htbP 313370877856196, htbP 296435311202899,
    htbP 272125630277734, htbP 242724133009633, htbP 210593502188418, htbP 177913225129317,
    htbP 146488560365753, htbP 117652928096373, htbP 92244998512268, htbP 70654772112885,
    htbP 52903010962514, htbP 38747129149244, htbP 27775244988033, htbP 19497699507072,
    htbP 13409346593457, htbP 9039574888268, htbP 5976558841276, htbP 3875880855966,
    htbP 2467042495447, htbP 1541614250262, htbP 946680147224, htbP 569912598339,
    htbP 338125510690, htbP 196927747621, htbP 112702202007, htbP 64401172659,
    htbP 35881916678, htbP 19290419690, htbP 9066702802, htbP 3482812614, htbP 1080504334,
    htbN 260703018, htbP 43470136, htbN 2250754, htbN 1490759, htbN 670023, htbN 188083,
    htbP 44215, htbN 7552, htbP 506, htbN 243, htbN 194, htbP 68, htbP 18, htbN 2, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0 ]
private def htbVec_r256_2 : List ℤ :=
  [ htbN 78011699, htbN 4476312, htbP 152172184, htbN 13451633, htbN 133088214, htbP 45910056,
    htbP 56597640, htbN 349264446, htbN 231492067, htbN 403135543, htbN 132510960,
    htbN 67725836, htbN 80493870, htbN 393515348, htbN 316009247, htbN 858189598,
    htbN 2022245809, htbN 3510761022, htbN 8510233848, htbN 15498623785, htbN 30368092659,
    htbN 56592538911, htbN 102099848058, htbN 180166009686, htbN 308766284071,
    htbN 517775434199, htbN 843492507702, htbN 1345873273942, htbN 2095954087411,
    htbN 3191714161045, htbN 4753906115811, htbN 6931250629816, htbN 9897124739530,
    htbN 13843152730656, htbN 18980316916988, htbN 25516872764371, htbN 33650318928751,
    htbN 43549194848405, htbN 55321852114855, htbN 69010070108677, htbN 84560231972847,
    htbN 101804330177556, htbN 120460643865477, htbN 140123027402375, htbN 160279770095244,
    htbN 180318950402874, htbN 199575510219428, htbN 217351470880878, htbN 232971020168913,
    htbN 245812528850016, htbN 255359847226240, htbN 261232897087939, htbN 263205675656341,
    htbN 261236796681386, htbN 255451181914511, htbN 246137152619649, htbN 233728206726863,
    htbN 218756535688793, htbN 201831893517498, htbN 183589313918080, htbN 164659268083000,
    htbN 145631643765238, htbN 127027659669848, htbN 109289959432636, htbN 92750482649982,
    htbN 77654462125218, htbN 64143144686446, htbN 52283016514156, htbN 42047664539972,
    htbN 33376439653630, htbN 26144157527836, htbN 20213292485240, htbN 15430939393386,
    htbN 11622612504977, htbN 8645310650313, htbN 6349501387746, htbN 4603241462458,
    htbN 3294503534749, htbN 2326251832345, htbN 1627801445285, htbN 1120254463122,
    htbN 761997267264, htbN 513266808888, htbN 342610453680, htbN 228517932584,
    htbN 150613346869, htbN 92812178765, htbN 51951898103, htbN 25252119982, htbN 10285285685,
    htbN 3473039874, htbP 971366321, htbP 222097585, htbN 38014190, htbP 2810811, htbN 1145990,
    htbN 679080, htbP 224412, htbP 51100, htbP 4860, htbP 2414, htbN 1626, htbP 583, htbP 156,
    htbN 32, htbN 4, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0 ]
private def htbVec_r256_3 : List ℤ :=
  [ htbN 104062720, htbP 130462315, htbP 14262505, htbN 37627706, htbP 20863771, htbP 75622924,
    htbP 13556243, htbN 69226596, htbP 9204076, htbP 312486857, htbN 72633599, htbN 111823905,
    htbP 312227935, htbP 602928468, htbP 581235445, htbP 3377018, htbN 768798129,
    htbP 273834979, htbN 493159399, htbN 483764854, htbP 493808976, htbP 387802801,
    htbP 95231858, htbP 1739638032, htbP 163653473, htbP 360732687, htbP 71493491,
    htbN 405846995, htbN 237832782, htbN 17347285, htbN 241293157, htbP 1108682779,
    htbP 1355379769, htbN 1350558245, htbN 903903636, htbP 892593007, htbP 154720149,
    htbP 1197623273, htbP 1227613383, htbN 1546279518, htbN 327960425, htbP 1371912385,
    htbP 1605613885, htbN 2950401172, htbN 677909827, htbP 1026605801, htbN 268359315,
    htbP 2189383790, htbP 373465880, htbN 918348020, htbN 820219467, htbP 2458735548,
    htbP 5399739418, htbP 8992528300, htbP 15482433498, htbP 25886349900, htbP 44646823852,
    htbP 71806568116, htbP 115437365710, htbP 186223295997, htbP 288885894180,
    htbP 446647164901, htbP 679876998254, htbP 1015251114142, htbP 1498486354331,
    htbP 2176332133663, htbP 3116565465658, htbP 4392877199209, htbP 6111416274133,
    htbP 8374076590300, htbP 11311030398214, htbP 15059210172617, htbP 19773326173803,
    htbP 25595123214970, htbP 32664432557840, htbP 41111490495685, htbP 51023358927837,
    htbP 62457677437514, htbP 75401757713471, htbP 89784036955166, htbP 105460993556761,
    htbP 122190674244579, htbP 139666870900409, htbP 157493948947809, htbP 175214564167484,
    htbP 192326827977787, htbP 208296384298071, htbP 222597417419296, htbP 234724794119257,
    htbP 244252276597339, htbP 250812988544946, htbP 254166791043124, htbP 254184136563858,
    htbP 250882965067549, htbP 244386261795993, htbP 234957811120261, htbP 222955808313639,
    htbP 208812479912337, htbP 193037781973569, htbP 176141590820487, htbP 158647065073031,
    htbP 141045681055248, htbP 123771784490378, htbP 107218183217304, htbP 91683723131353,
    htbP 77394915005238, htbP 64482509981406, htbP 53039029042741, htbP 43061916637872,
    htbP 34519676864502, htbP 27309323913009, htbP 21334170583364, htbP 16453875858083,
    htbP 12516173063452, htbP 9404255298997, htbP 6973372497317, htbP 5105217131004,
    htbP 3685175508867, htbP 2638062585945, htbP 1851240499234, htbP 1294721684817,
    htbP 890804417500, htbP 601769367534, htbP 410883593527, htbP 271254638232,
    htbP 167427040560, htbP 85579417742, htbP 35055204657, htbP 11705344417, htbN 2957166550,
    htbN 422466546, htbN 28559334, htbP 27276563, htbP 2390577, htbP 2565583, htbN 1479443,
    htbN 481029, htbN 116635, htbN 23187, htbN 3846, htbN 487, htbP 21, htbN 17, htbN 7,
    htbP 1, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0 ]
private def htbVec_r256_4 : List ℤ :=
  [ htbP 84619201, htbN 21863517, htbN 78668573, htbP 126650067, htbP 67109311, htbP 61608598,
    htbN 71544334, htbP 18084702, htbN 1028887, htbP 164547698, htbN 141939278, htbN 697230993,
    htbN 284443322, htbP 690964066, htbP 270644392, htbN 277523573, htbN 539928693,
    htbP 87532850, htbP 227356989, htbP 686908462, htbN 1506919891, htbN 704602837,
    htbN 543922863, htbP 23795107, htbP 321536294, htbN 80587039, htbN 175043126,
    htbN 444665638, htbP 1006179378, htbN 629891419, htbP 643044495, htbP 753011576,
    htbP 1772339499, htbP 515022005, htbN 1970387343, htbN 1364961036, htbP 2346823481,
    htbN 642411379, htbN 1381634140, htbP 255974818, htbN 479293730, htbN 1010770494,
    htbN 170561963, htbP 777067054, htbN 1011324893, htbN 37030454, htbP 1757357007,
    htbP 628331003, htbP 1261184095, htbN 118545052, htbP 2842651612, htbN 2766057815,
    htbN 1770858513, htbP 369526749, htbP 1268460614, htbP 673168228, htbN 1677588899,
    htbP 1938224687, htbP 1424004294, htbN 220323507, htbN 728563729, htbP 700804554,
    htbP 115527946, htbN 1697661051, htbN 371132213, htbN 2110310460, htbP 1727543663,
    htbN 538685754, htbP 920667807, htbP 985208723, htbP 3101753249, htbP 291470945,
    htbN 1506988196, htbN 990484479, htbN 486865453, htbP 5366287670, htbP 794022971,
    htbN 1229179309, htbN 3751192994, htbN 3384165412, htbP 2285897479, htbP 2914853868,
    htbN 127729254, htbN 4065211163, htbN 3451243033, htbP 1297201447, htbP 988318143,
    htbN 3548732694, htbP 2960212015, htbP 3688112332, htbP 1997450100, htbN 2313402129,
    htbP 5760707721, htbP 2553862307, htbP 8708580465, htbP 13800490126, htbP 22180357334,
    htbP 37201198691, htbP 71917568279, htbP 109267891499, htbP 186686190423,
    htbP 303718467292, htbP 478077766566, htbP 747828002311, htbP 1150734156279,
    htbP 1743445205693, htbP 2588609564421, htbP 3781198354878, htbP 5441909155929,
    htbP 7693979099136, htbP 10710228161279, htbP 14652623544321, htbP 19725336992989,
    htbP 26135411062514, htbP 34059868460522, htbP 43673357909550, htbP 55104746939099,
    htbP 68418137198119, htbP 83581726790368, htbP 100498102818534, htbP 118910427247688,
    htbP 138455576840254, htbP 158664223081780, htbP 178963101258285, htbP 198660379872761,
    htbP 217045593181888, htbP 233411708994255, htbP 247053304035851, htbP 257383695339878,
    htbP 263939350155763, htbP 266412866697217, htbP 264692974405048, htbP 258853160305955,
    htbP 249173947134470, htbP 236096017575460, htbP 220200926692205, htbP 202150670459471,
    htbP 182671011924162, htbP 162470335133758, htbP 142231909224879, htbP 122557870227862,
    htbP 103948073983954, htbP 86775528520072, htbP 71290262191041, htbP 57637788324723,
    htbP 45878929603631, htbP 35929092026580, htbP 27703386527186, htbP 21006733162713,
    htbP 15670690233159, htbP 11507645376073, htbP 8308734556406, htbP 5909987501675,
    htbP 4152395625362, htbP 2872129931028, htbP 1947079573786, htbP 1295658492593,
    htbP 846501498352, htbP 535426757552, htbP 320890850814, htbP 174070610250,
    htbP 90055230969, htbP 38831940796, htbP 12218396183, htbN 2456266116, htbP 124631434,
    htbN 136953182, htbP 70607282, htbP 21704629, htbN 5159233, htbP 1059928, htbP 200966,
    htbP 35955, htbP 5997, htbP 900, htbP 116, htbP 14, htbP 2, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0 ]
private def htbVec_r256_5 : List ℤ :=
  [ htbN 21692658, htbP 124933203, htbP 21015155, htbP 55113719, htbP 72420050, htbN 136982767,
    htbP 243863075, htbP 182093168, htbP 198864463, htbN 403278176, htbP 104216581,
    htbN 267124637, htbP 486356909, htbP 96201591, htbN 278995280, htbP 618328009,
    htbP 491387920, htbP 678911089, htbP 18395610, htbN 224302482, htbN 500718892,
    htbP 540970666, htbP 486183386, htbP 925337424, htbN 1050224016, htbP 1832098984,
    htbP 174167233, htbP 124007862, htbP 1012712290, htbP 1813883909, htbN 71013601,
    htbP 1521530581, htbP 1122710495, htbN 931360935, htbN 722439025, htbN 308382474,
    htbN 389053898, htbN 1904463166, htbP 106372272, htbN 168102024, htbP 2221396237,
    htbP 1236054085, htbP 553972723, htbP 1379800404, htbN 839280685, htbN 964758572,
    htbN 2056080045, htbP 1872060206, htbN 213200434, htbN 1055759617, htbP 34642370,
    htbN 1761967907, htbN 1615710978, htbP 27097883, htbN 654092146, htbP 1665547613,
    htbN 1343037125, htbP 710861196, htbP 2573935283, htbN 145591955, htbN 1369183918,
    htbN 910706030, htbN 1929042600, htbN 363775598, htbP 2791379860, htbN 2538066644,
    htbP 767920098, htbN 3946617997, htbP 518590507, htbP 84932981, htbN 240963715,
    htbP 554904695, htbP 2685062285, htbN 645578885, htbN 77529387, htbP 3543322334,
    htbP 2744678720, htbN 2182813115, htbN 586474544, htbN 3186766356, htbN 2641477109,
    htbN 5066046511, htbN 1278945336, htbN 782014447, htbN 3732853870, htbP 3412357770,
    htbP 123772685, htbN 2942362148, htbN 4517497610, htbN 652830960, htbP 2824394894,
    htbP 2426556749, htbP 6616775025, htbP 1255882254, htbP 5648074220, htbP 4735160944,
    htbP 506505057, htbN 3570052728, htbN 38041962, htbN 6051040021, htbN 3387711624,
    htbN 1029710454, htbN 4146356167, htbP 125625011, htbN 1466790668, htbN 4959875832,
    htbP 1316337396, htbN 1941829465, htbP 8147107044, htbN 125691002, htbN 6313203228,
    htbP 7379663587, htbN 648437105, htbP 4499821879, htbP 846232850, htbN 3517675921,
    htbP 3313367734, htbP 257734487, htbN 4958597214, htbP 1355605585, htbN 18213663,
    htbP 2751022708, htbP 3516255040, htbN 2386101028, htbP 2994045229, htbN 16649661799,
    htbN 9338800391, htbP 1001929699, htbP 24361249932, htbN 4517972706, htbN 8854669603,
    htbP 735398726, htbN 4845050345, htbP 4480233729, htbP 23668365006, htbN 10819252865,
    htbN 10002428699, htbN 1948174807, htbN 17905712094, htbN 35676433344, htbN 82151900947,
    htbN 171971941654, htbN 323699207076, htbN 592463801409, htbN 1084586508122,
    htbN 1835007248956, htbN 3088690497042, htbN 4971796242888, htbN 7833993540333,
    htbN 11943731539442, htbN 17689903294577, htbN 25505352318677, htbN 35791020920242,
    htbN 48869870863296, htbN 65032968270960, htbN 84309728733472, htbN 106555595446679,
    htbN 131337358393725, htbN 157931670248956, htbN 185312177108560, htbN 212188629644449,
    htbN 237268689820582, htbN 259007682079051, htbN 276224733736403, htbN 287683977041829,
    htbN 292762992623365, htbN 291157733261248, htbN 282920880701284, htbN 268742752775793,
    htbN 249539671696014, htbN 226456259942570, htbN 200953113021730, htbN 174338032898223,
    htbN 147897892157741, htbN 122654695129221, htbN 99553702901071, htbN 78936346443430,
    htbN 61168150883806, htbN 46435386595922, htbN 34433757710990, htbN 25017020585741,
    htbN 17657368535374, htbN 12309978413829, htbN 8328464335070, htbN 5544295738831,
    htbN 3638976625146, htbN 2369678975169, htbN 1414283454935, htbN 712333540693,
    htbN 296011618873, htbN 103616268823, htbP 31984984424, htbN 9268759400, htbN 2682460843,
    htbP 798241025, htbN 240084356, htbN 70203096, htbN 19312980, htbN 4902342, htbP 1137042,
    htbN 239807, htbP 45846, htbP 7911, htbP 1220, htbN 164, htbN 18, htbN 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0 ]
private def htbVec_r256_6 : List ℤ :=
  [ htbN 59001019, htbP 29418587, htbP 153956520, htbP 305325961, htbP 89590163,
    htbP 140638163, htbP 85072196, htbP 426267185, htbN 73474496, htbP 455783027,
    htbP 197543921, htbN 582736506, htbN 50792797, htbN 138732566, htbN 163094563,
    htbN 580796010, htbP 112388766, htbP 755982667, htbN 906692349, htbN 626196171,
    htbP 711036850, htbP 1134407610, htbN 416544050, htbN 716778700, htbP 302802475,
    htbN 1482402287, htbN 268542202, htbP 501050880, htbN 1140273648, htbP 155313507,
    htbP 589130091, htbN 981509393, htbP 1224197047, htbN 697914647, htbP 188264487,
    htbP 1520330236, htbN 2026428847, htbP 1961299644, htbP 3425654554, htbP 1125532299,
    htbP 566093400, htbN 367194867, htbP 1375681492, htbN 2409997650, htbN 386519640,
    htbP 1333710096, htbN 980169209, htbN 296626696, htbN 707512933, htbN 370970308,
    htbN 410321191, htbP 283481484, htbP 1219873432, htbP 926510084, htbN 894159118,
    htbN 237642823, htbP 285289490, htbN 1185400141, htbN 1042016652, htbN 575148220,
    htbN 1015167702, htbP 1027925449, htbN 1885940615, htbP 5201795851, htbN 268513409,
    htbN 3653047883, htbN 1075896910, htbN 992359976, htbP 3767375409, htbN 873319623,
    htbN 718942059, htbP 822543440, htbN 684830987, htbN 2467706122, htbN 1514574042,
    htbN 510751799, htbN 1938511539, htbN 2496514980, htbN 469393505, htbP 3680009642,
    htbN 2606306167, htbN 4312559258, htbP 2589167383, htbP 3438409251, htbP 2304978513,
    htbN 2008412904, htbP 888314032, htbN 2241513237, htbP 142453612, htbP 5399019603,
    htbN 1150153568, htbP 7050355975, htbN 531837074, htbP 5561160847, htbN 7999367199,
    htbP 829275451, htbP 70654763, htbP 2218777930, htbN 2778384597, htbP 4805014835,
    htbN 2270818704, htbN 2484532312, htbP 984791681, htbN 2014684586, htbP 2710410263,
    htbP 4926403372, htbP 238144196, htbP 8431522739, htbN 622462989, htbN 3406293518,
    htbN 614896976, htbP 437172006, htbP 5214809790, htbP 6456548287, htbN 4551879060,
    htbN 826907089, htbP 2265134415, htbN 3528411517, htbN 2029797505, htbN 8866922698,
    htbP 2027858784, htbP 1398120603, htbN 10753486201, htbN 1856737452, htbP 3214389784,
    htbN 11866879409, htbN 2343726098, htbN 565081128, htbP 2710320875, htbP 6857419484,
    htbP 8700516911, htbN 10377822396, htbN 5039127933, htbN 10071592020, htbP 5913918655,
    htbP 5549956856, htbP 31006214244, htbP 868100042, htbN 11283675203, htbN 16996718838,
    htbP 7358937273, htbN 4623158523, htbN 7712024056, htbP 402302074, htbN 23993993457,
    htbP 7774636439, htbP 17324931383, htbP 2914398465, htbP 9608562781, htbP 28659568846,
    htbN 12139835131, htbP 29869209230, htbN 8996233360, htbP 8505172358, htbN 8696707426,
    htbN 7531593668, htbN 16254270398, htbP 6768930682, htbN 2305240467, htbP 8227791515,
    htbN 18503324860, htbP 24274589750, htbP 5491911009, htbN 33581458299, htbN 16095092763,
    htbP 1463798450, htbN 26205571022, htbP 58769742005, htbP 9219904478, htbP 50272236794,
    htbN 77700474967, htbP 33010022088, htbN 51001745144, htbN 35081461549, htbN 63278842751,
    htbN 24893288239, htbN 1806569475, htbP 202457553187, htbN 34825017195, htbN 218540424448,
    htbN 134569560520, htbN 299440918062, htbN 987250105538, htbN 2720531058394,
    htbN 5672929561615, htbN 10774767433595, htbN 19082817426178, htbN 31177721435642,
    htbN 48046012324551, htbN 70222066448335, htbN 97955512293384, htbN 130014950200434,
    htbN 165520783137512, htbN 202838877955812, htbN 238709287217979, htbN 270561507671398,
    htbN 296305088485989, htbN 313407410954446, htbN 320190606236759, htbN 316597278915191,
    htbN 303392577622038, htbN 281668152869228, htbN 253233262699560, htbN 220741595708474,
    htbN 186960872397749, htbN 153854920204028, htbN 122852724296781, htbN 94805940007930,
    htbN 71213157053497, htbN 51832804853850, htbN 37204733998688, htbN 26026573462706,
    htbN 17442083922453, htbN 11280387817631, htbN 6976959102481, htbN 3968928461283,
    htbN 2006982909590, htbP 896427140129, htbN 361453590092, htbN 137346577611,
    htbN 51656087383, htbN 19823403022, htbN 7746903099, htbN 3020149143, htbN 1153445638,
    htbN 427977175, htbN 153985316, htbN 53691730, htbN 18102250, htbN 5877255, htbN 1828843,
    htbN 542815, htbN 152754, htbN 40397, htbN 9929, htbN 2232, htbN 448, htbN 77, htbN 9,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0,
    htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0, htbP 0 ]
private def htbVec_r256_7 : List ℤ :=
  [ htbP 19292500, htbN 205979128, htbP 66173290, htbP 359916071, htbN 103884132,
    htbN 187111184, htbN 73998835, htbN 301829160, htbP 179338511, htbN 383186064,
    htbN 302748067, htbN 329060248, htbP 572465053, htbN 313806099, htbN 584503510,
    htbP 1431302744, htbP 232604796, htbP 254278797, htbN 453070339, htbP 715992907,
    htbN 170768690, htbP 814467806, htbP 387155245, htbN 382695443, htbP 1390207978,
    htbP 458348935, htbP 42484891, htbN 882071635, htbN 4850893, htbN 1118573511,
    htbN 830284103, htbN 1160470424, htbP 655276832, htbN 2939900037, htbP 1917994835,
    htbP 875285550, htbN 2946097249, htbN 1046873038, htbP 811975751, htbN 289375551,
    htbN 463319896, htbN 1399435338, htbP 162216712, htbN 1398225096, htbN 1880799288,
    htbP 523443839, htbN 1723212478, htbN 1442413229, htbP 2158463319, htbP 676611473,
    htbP 267711365, htbN 93317309, htbP 602620766, htbN 366670492, htbP 661745327,
    htbP 211213852, htbN 2666127132, htbN 1186610408, htbN 1696241328, htbP 1571637279,
    htbP 2316832429, htbN 2664925629, htbN 3127763461, htbP 1159813668, htbP 2200316902,
    htbN 2486692093, htbP 1065195214, htbP 110988233, htbP 2515802572, htbP 576318044,
    htbP 1323737267, htbN 203877303, htbN 1515626509, htbN 1810079582, htbP 656318049,
    htbN 862208323, htbP 3673051565, htbN 3061045483, htbP 966655629, htbN 850632166,
    htbP 5789728824, htbP 3060322370, htbP 1879248580, htbN 3369961407, htbN 4228278966,
    htbP 2217404200, htbN 2760927, htbP 1749099893, htbP 6295197464, htbP 449476082,
    htbN 4764077855, htbN 4154623249, htbP 5132249032, htbN 3917994490, htbN 22823908,
    htbN 2861865125, htbN 1642298147, htbN 2356014392, htbN 6077585928, htbP 2152891039,
    htbP 794157601, htbN 1150546660, htbP 5591544157, htbP 5031788606, htbN 3139077439,
    htbN 63398866, htbN 2976619370, htbN 5931679565, htbN 2696680512, htbN 3305973250,
    htbN 786932202, htbP 4824606891, htbP 1888055138, htbN 2147842131, htbN 7182534997,
    htbN 6973267661, htbP 3695107793, htbN 983950035, htbP 7902000170, htbP 6311853561,
    htbP 8210234595, htbN 8070681759, htbP 7628809922, htbN 10503028219, htbN 2547418655,
    htbP 4303232395, htbP 961152889, htbP 13002623172, htbP 1832235688, htbP 13275000324,
    htbP 14991881981, htbP 2701613283, htbN 1256146909, htbN 8513186972, htbP 14218639578,
    htbP 2775336943, htbP 13142477029, htbP 33307904982, htbP 3758155856, htbN 9524597301,
    htbP 8833406655, htbN 2033758423, htbN 19458940378, htbN 13546683602, htbN 7837417175,
    htbN 17832776782, htbN 5303252923, htbN 4253354056, htbN 22012402200, htbP 29542191515,
    htbP 6025259015, htbP 3031311728, htbN 28876032824, htbN 31594438715, htbP 39330702963,
    htbP 29072529652, htbN 14407224499, htbN 23700432056, htbN 17962970274, htbP 21296164865,
    htbP 816483319, htbN 5013678065, htbN 18706086022, htbP 11744753673, htbP 87952904320,
    htbP 2889631915, htbP 10798547795, htbN 439512548, htbP 9510994989, htbN 16311622243,
    htbP 1153462986, htbP 49902653704, htbP 84176491353, htbN 7023288761, htbP 84521924967,
    htbP 85665792651, htbN 161495729027, htbN 161329924421, htbN 74907768141,
    htbP 158742990429, htbP 97212798853, htbP 103428190292, htbN 18698361172,
    htbP 105572119953, htbP 34722134363, htbP 18199550838, htbP 164985624879,
    htbP 215411976779, htbP 225061746670, htbN 155127798122, htbP 69702131744,
    htbP 36811331912, htbP 115479582962, htbP 185220150769, htbP 152906886021,
    htbP 337922318559, htbP 309450911705, htbP 216328824766, htbP 103198844806,
    htbP 101917706930, htbN 646171828827, htbP 745599508233, htbN 381675483440,
    htbP 517285221830, htbP 898704422591, htbN 510512781633, htbN 220452625746,
    htbP 311547394647, htbN 890524190005, htbP 1905820900882, htbP 429502489029,
    htbP 438945375741, htbN 1710696950707, htbN 1879950918150, htbN 6126013905455,
    htbN 22322021364017, htbN 46546829082351, htbN 84243448054473, htbN 134172988151107,
    htbN 188949507456882, htbN 244807698656410, htbN 297529952274272, htbN 337915305083325,
    htbN 359241046494684, htbN 361771066052535, htbN 347558859860935, htbN 317390528426103,
    htbN 274209478592078, htbN 224924107442346, htbN 176934894066410, htbN 134390002250919,
    htbN 98178699974060, htbN 68103780725748, htbN 44206134868297, htbN 26567001867154,
    htbN 14711325576528, htbN 7508604735745, htbN 3547913707567, htbN 1563184647434,
    htbN 648338317081, htbN 255510105919, htbN 95869405645, htbN 36040891069, htbN 11895425008,
    htbN 3185500720, htbN 666997202, htbN 109215710, htbN 18120184, htbN 5268134, htbN 1666713,
    htbN 385233, htbN 67863, htbN 10566, htbN 1579, htbN 207, htbP 19, htbP 0 ]
private def htbVec_r256_8 : List ℤ :=
  [ htbP 10928657, htbP 103032165, htbP 159159916, htbP 234736964, htbN 179221136,
    htbN 759051527, htbN 511846865, htbP 197182343, htbN 163668852, htbN 450009954,
    htbN 98670014, htbN 211110112, htbN 268105359, htbN 579776431, htbN 1440837653,
    htbP 665988389, htbN 334673952, htbN 293004187, htbN 602769037, htbP 1061450962,
    htbN 41485146, htbN 1175149771, htbN 193798968, htbN 173296576, htbN 23838325,
    htbP 344329205, htbN 766353419, htbP 1198329366, htbN 897068219, htbP 518572494,
    htbN 2716611844, htbN 335987757, htbP 789022674, htbN 2215863251, htbP 587303363,
    htbN 2051643184, htbN 890043848, htbN 314784398, htbN 439120546, htbP 651484695,
    htbN 2214590311, htbP 1270658558, htbN 825819589, htbP 1131978617, htbN 200671500,
    htbN 1636594395, htbN 2104373785, htbN 1713264568, htbP 1893740718, htbN 2466068634,
    htbN 487632847, htbP 233992353, htbP 3576643458, htbN 1305154946, htbN 1487907109,
    htbN 976012997, htbP 2662703099, htbP 414223051, htbN 803817415, htbN 2258098979,
    htbN 275593592, htbN 453088458, htbN 166369477, htbN 1979229403, htbN 1641471173,
    htbN 206963331, htbP 16740923, htbN 555495960, htbN 567380081, htbN 1364364805,
    htbP 350565838, htbP 3393713572, htbP 4498231671, htbN 913584366, htbN 703445815,
    htbP 4419592392, htbN 5018907737, htbP 4497602129, htbN 1273515994, htbP 1794082445,
    htbP 386391605, htbN 677289891, htbN 1746601031, htbP 2622887557, htbP 3767609144,
    htbP 995753675, htbP 270042681, htbN 3020726177, htbP 2777284075, htbP 2817321306,
    htbP 4875633531, htbP 4300899056, htbP 2131161559, htbP 236424326, htbN 3272925821,
    htbP 1550839931, htbN 2450688189, htbP 7740394251, htbP 1263428281, htbP 3179102766,
    htbN 61696360, htbP 326317238, htbP 4382762110, htbN 10916375412, htbN 9507388513,
    htbP 1826649771, htbP 2226914101, htbN 6652680490, htbN 6470097980, htbP 10392570256,
    htbP 6294659558, htbN 1538378573, htbP 8063902353, htbP 5875828462, htbN 8872435156,
    htbN 1238581100, htbN 3870819051, htbN 74632941, htbP 585382772, htbN 8176941549,
    htbP 5834167160, htbP 487400609, htbP 12089015108, htbP 7421501325, htbN 6530388832,
    htbN 6380772958, htbN 14357236274, htbP 9887824949, htbP 3048182600, htbP 3222543147,
    htbP 4379619554, htbP 19685507394, htbP 3333067093, htbP 3783852449, htbP 18434505208,
    htbN 3383389631, htbN 7559827647, htbN 4826151239, htbN 7845546436, htbP 12837585179,
    htbP 10618592122, htbP 6497026231, htbP 5050481906, htbN 14286465053, htbP 12056690592,
    htbN 18133058178, htbP 22941716758, htbP 18207596527, htbP 45201075540, htbP 40128039741,
    htbN 5244219015, htbP 4091504416, htbN 1435672667, htbN 1315558673, htbP 17209554707,
    htbP 24159586814, htbN 14247899983, htbN 77325041623, htbN 36088218035, htbN 37244741302,
    htbP 66367637988, htbP 77770605040, htbN 10042580022, htbN 33929360844, htbN 37403816678,
    htbN 1202448665, htbP 63421751665, htbN 43406860509, htbP 25062195261, htbP 41306629049,
    htbP 45198938194, htbN 3180659929, htbN 32280496656, htbN 36365521451, htbP 108083116493,
    htbN 12092767239, htbP 112584236760, htbP 5862770874, htbN 1376364492, htbN 82157828110,
    htbN 361335954265, htbN 161217564221, htbP 58973925090, htbN 171715544278,
    htbP 266686620143, htbP 83390941012, htbN 146225987798, htbP 44319667048, htbN 36478187618,
    htbP 122733396277, htbN 38052080028, htbN 290868484982, htbP 313914534236,
    htbP 506657459483, htbN 204415846622, htbP 59946594400, htbP 314382981047,
    htbP 265584284879, htbP 210574540377, htbP 391577732090, htbP 23581995204,
    htbP 239339539504, htbP 193914089806, htbP 840879625246, htbN 856236297123,
    htbN 175616064687, htbP 1145449060672, htbP 636855692977, htbN 1084827412722,
    htbN 214770378574, htbN 403764465528, htbP 987225079908, htbP 137409168684,
    htbP 597224963285, htbN 1419142120690, htbP 1234155981886, htbN 407893141670,
    htbP 1061910276623, htbP 2179422236554, htbN 1886603505151, htbN 679234173689,
    htbP 2564286191936, htbP 1281285482557, htbP 3757235425183, htbP 1824412347444,
    htbN 986274229337, htbP 783091212419, htbN 2033603475900, htbP 2694384828891,
    htbN 65900651652, htbN 7854131973506, htbN 1975267327964, htbP 6647594662670,
    htbN 1966420427773, htbN 7001563253815, htbN 4640306753829, htbP 8656686398450,
    htbP 17246839076109, htbP 393811009212, htbN 57011568607647, htbN 154068125365930,
    htbN 269627774359407, htbN 372323648409111, htbN 434525503496843, htbN 444487917012337,
    htbN 405652409981512, htbN 332635385509820, htbN 245998759160380, htbN 162875038680857,
    htbN 96166392946561, htbN 50631593886963, htbN 23206541748482, htbN 9643443544785,
    htbN 1869927117644, htbN 255242036457, htbN 53779919229, htbN 9891195084 ]
private def htbVec_r256_9 : List ℤ :=
  [ htbN 97495091, htbN 313654473, htbP 414870333, htbN 42869939, htbP 738585093,
    htbP 58039931, htbN 145511253, htbP 394814606, htbP 272687380, htbP 307028947,
    htbN 16118755, htbP 1226482519, htbP 888455253, htbP 288394286, htbN 903500762,
    htbP 385796970, htbP 232624147, htbN 623781195, htbN 1000659551, htbN 1434914386,
    htbN 519071214, htbN 80043215, htbP 1979947514, htbP 67870774, htbP 630200254,
    htbP 57752947, htbN 1788727535, htbN 834211841, htbN 97396417, htbP 2975443513,
    htbN 515829342, htbP 493940794, htbP 243311654, htbP 334503973, htbP 293027070,
    htbP 502187639, htbN 1310532003, htbP 1253576426, htbP 546596065, htbN 2836981600,
    htbP 1236299466, htbN 1531934070, htbN 59211872, htbP 2572380154, htbN 2094984557,
    htbN 510068535, htbP 1090566164, htbP 691890191, htbP 2488183550, htbN 999203834,
    htbN 1796942612, htbN 652414791, htbP 49204176, htbP 1756408519, htbN 3845809770,
    htbN 396079735, htbN 686808192, htbN 265760755, htbP 1754226802, htbN 13564349,
    htbP 981709484, htbN 328300412, htbP 2800415126, htbN 3466577826, htbN 1386928962,
    htbN 5334668523, htbN 531276788, htbN 1226769058, htbP 4514969863, htbN 3029939169,
    htbN 80094317, htbN 2429764694, htbN 1131888995, htbN 2058187801, htbP 2030083565,
    htbN 2754665687, htbP 1737719446, htbN 1134666156, htbP 745341755, htbP 1244978088,
    htbN 1856414301, htbN 3227978863, htbN 2926243877, htbN 1294194033, htbP 1561153092,
    htbP 3290173707, htbN 2752801451, htbN 2814379873, htbP 424377461, htbN 430342126,
    htbP 2329304641, htbN 3142327369, htbP 5829860179, htbN 1281584849, htbN 823288499,
    htbN 6416875782, htbN 197872898, htbN 4257936640, htbN 254522907, htbN 4443389190,
    htbN 3236490238, htbN 10188099666, htbN 11326497378, htbP 3462194763, htbP 13052493227,
    htbN 4826258832, htbN 2403955599, htbN 6306266887, htbN 403962866, htbN 7522642243,
    htbP 1086057381, htbP 6681559412, htbP 1806034161, htbN 2210557602, htbP 3925884639,
    htbP 3682749502, htbP 3147823474, htbP 5742118311, htbN 8863782198, htbP 5918766761,
    htbN 2252518728, htbN 5507020006, htbP 7344975637, htbN 17074164805, htbP 2086584182,
    htbN 14502121887, htbN 7790278058, htbN 13988994063, htbP 9693477537, htbP 4273488202,
    htbN 671651945, htbP 1257048371, htbN 2553971187, htbP 1095630307, htbN 143533032,
    htbP 3458828961, htbP 1105932248, htbP 17240537544, htbP 17033949636, htbN 13961824191,
    htbP 8145255697, htbN 12878109600, htbP 12241336838, htbP 7572020860, htbN 3097907754,
    htbP 2358526860, htbN 31822235553, htbP 13159136401, htbP 25693352522, htbN 33860040350,
    htbP 42190931938, htbN 18729015457, htbP 1574897380, htbP 16941039295, htbN 36597148415,
    htbN 22823537827, htbP 24754355364, htbP 22542584327, htbP 88474964191, htbN 37205189292,
    htbN 32482457891, htbN 45770275710, htbN 17251396823, htbN 27659585724, htbN 9967321921,
    htbN 163638343, htbP 14961201258, htbP 76841266705, htbP 64625703166, htbN 80207156346,
    htbN 16760949053, htbP 57045164917, htbP 6781159115, htbP 39031476191, htbN 83482043755,
    htbP 21658341747, htbP 59484460469, htbN 78632195790, htbP 50566836413, htbP 84184388536,
    htbN 23475225911, htbN 46759428205, htbP 21945433080, htbN 45369300321, htbN 119536134590,
    htbN 82213615487, htbP 157129023689, htbP 21453568777, htbN 12556064292, htbP 224511211290,
    htbP 191344611, htbP 45489795712, htbN 127007715709, htbN 475013452624, htbN 199970035299,
    htbN 10046195373, htbP 164929189634, htbN 159620969119, htbP 298350168792,
    htbN 657168632850, htbN 848337825294, htbN 891399100655, htbN 658622855348,
    htbN 900753713648, htbP 429902020100, htbN 133995499182, htbN 249706922389,
    htbN 263440033210, htbN 320333980944, htbN 310257852859, htbP 1168796937865,
    htbP 183743874346, htbP 681081517894, htbP 205261231967, htbN 1402798809063,
    htbP 287692214340, htbN 896118230614, htbN 1996941010674, htbN 479487863110,
    htbP 1270786961995, htbN 3910080000258, htbN 2552672853691, htbN 2573184265091,
    htbP 3810913666477, htbP 1555574354715, htbP 989335313887, htbN 971913906017,
    htbN 1539883990856, htbP 2671676464246, htbP 2930344599159, htbN 7399797646996,
    htbN 4494576813085, htbN 2820594001057, htbP 1944340281374, htbN 3746503975953,
    htbN 5640736392290, htbP 5490525579135, htbN 1577342769145, htbN 4140411454356,
    htbP 8446690958820, htbN 6172439478676, htbN 9007550863669, htbN 7571416595053,
    htbP 10675583410586, htbP 5047669392777, htbN 10115168285128, htbP 16003310323831,
    htbP 12976295225564, htbP 10103121192176, htbP 59663546798562, htbP 48681384373569,
    htbN 94175333247514, htbN 395632329026899, htbN 554317903792129, htbN 596195286602031,
    htbN 385337965675250, htbN 127259883444848 ]
private def htbVec_r256_10 : List ℤ :=
  [ htbN 185446717, htbP 501824210, htbP 306960940, htbN 604812922, htbP 61413845,
    htbP 316795422, htbN 248281114, htbP 92842202, htbN 179768815, htbN 207241957,
    htbP 386954481, htbP 46640020, htbN 578855261, htbP 153652081, htbN 212334586,
    htbN 276401287, htbN 818451394, htbP 543696944, htbN 1672621654, htbP 947940352,
    htbP 862640635, htbP 632041956, htbP 1160981389, htbP 2785515641, htbN 2814711322,
    htbP 526210873, htbN 54834636, htbP 2526868465, htbN 1061066549, htbN 410021762,
    htbP 163600122, htbN 214169905, htbP 146386413, htbN 202000996, htbP 560964676,
    htbN 1287865888, htbN 125175278, htbN 34552038, htbP 1451766024, htbN 3563387502,
    htbP 581646072, htbP 151236807, htbP 529762826, htbP 1869410539, htbP 316400014,
    htbN 140376423, htbP 822187094, htbP 269967426, htbN 99585368, htbP 504478737,
    htbN 1905845852, htbN 624568341, htbP 2354115416, htbP 351013495, htbP 2761256999,
    htbP 3227449601, htbN 3245180883, htbP 279654515, htbP 1249925663, htbP 190776166,
    htbN 5250442554, htbP 37435442, htbP 1875703274, htbP 218342897, htbN 1308217816,
    htbP 1683017480, htbN 2008648198, htbN 1661247432, htbP 1024897715, htbN 777505107,
    htbP 3158002760, htbP 1588336590, htbP 256303618, htbP 1528069312, htbP 3210896311,
    htbN 724451904, htbP 546416135, htbP 4863416237, htbN 344531569, htbP 257981115,
    htbN 4268726659, htbP 1846278164, htbP 3261235563, htbP 3505035994, htbP 660533590,
    htbP 3410394175, htbN 2024016856, htbP 3826626556, htbP 2979603166, htbP 1310215764,
    htbN 2406770263, htbP 45145181, htbN 8054882509, htbN 1575259478, htbN 956290360,
    htbN 3087336025, htbP 2983198799, htbP 83828688, htbN 248775265, htbN 8392920721,
    htbP 8472569690, htbN 2025125567, htbP 164341926, htbP 3747754315, htbN 2213216345,
    htbP 827623700, htbN 2529240954, htbN 3644734945, htbN 5221530000, htbN 11688084838,
    htbP 4699377539, htbN 7525591984, htbN 6140599920, htbP 2599034229, htbP 5758004733,
    htbN 12880731186, htbN 4175785496, htbP 2831316805, htbP 15868448860, htbP 3084962176,
    htbP 15159643144, htbN 2951190893, htbN 11330060552, htbN 5459455484, htbP 12339307999,
    htbN 6540743332, htbN 11604127121, htbN 13098754596, htbP 12424036318, htbN 10310423044,
    htbP 11752024733, htbP 14282488389, htbP 10178985426, htbP 9529282251, htbN 11223694952,
    htbP 1108846714, htbP 8724883629, htbP 13101961125, htbN 3454949846, htbP 10980128312,
    htbP 13863411384, htbN 15530205320, htbP 19212930002, htbP 17043841881, htbN 32794335536,
    htbP 3984219529, htbP 10500024992, htbP 6306103808, htbN 19557945800, htbN 20135998914,
    htbN 8101521055, htbP 22289522024, htbN 39381188258, htbP 18614105879, htbN 15520312532,
    htbP 8977422812, htbP 16279113732, htbP 10342308994, htbN 17533754044, htbN 16331483341,
    htbP 2060854829, htbP 5981526410, htbN 46991792573, htbN 1888679539, htbN 7774585805,
    htbN 99082688052, htbN 22397000104, htbN 22339282408, htbP 34018092454, htbN 30265376157,
    htbP 145127799883, htbP 49103993096, htbN 37537466947, htbP 125031755882, htbP 72389499556,
    htbP 20191368432, htbN 70056535753, htbN 67334390642, htbP 28154190996, htbP 39166511395,
    htbP 1922903776, htbP 75682595548, htbN 55114161668, htbP 59274983800, htbN 161167678355,
    htbP 22895853731, htbP 198410625063, htbP 25575257308, htbP 57944095870, htbN 12727959030,
    htbN 93467576576, htbP 117528532199, htbN 157814096265, htbN 108066188114,
    htbP 172202643646, htbN 238269062445, htbN 24707924374, htbP 161721022716,
    htbP 234725401021, htbP 293095133318, htbN 329275625531, htbP 171777387403,
    htbP 102878445219, htbP 46697448812, htbP 259171297975, htbN 450500703169,
    htbN 686612195097, htbN 99526413481, htbP 1035292121955, htbN 477355460453,
    htbN 314556379672, htbN 2062445378936, htbN 524416129685, htbP 682638981982,
    htbP 1135543349065, htbP 393897490156, htbP 713909451519, htbN 124834543960,
    htbP 147067769839, htbN 402481685354, htbP 841553177065, htbP 71551595605,
    htbN 119274387668, htbN 873368000561, htbN 1020050407340, htbP 790070256270,
    htbP 2063626062584, htbP 2485508094486, htbP 5051682411172, htbP 1039445056961,
    htbN 2029139703307, htbN 5837486113220, htbN 7957924139988, htbN 1615437606909,
    htbP 2250334360787, htbN 14993589037246, htbN 278997713455, htbN 88433843961,
    htbP 6244690537797, htbN 4954082721782, htbP 8907532056220, htbP 3022571983842,
    htbP 2228862606937, htbN 1203958147378, htbP 9564918970537, htbP 6577549168406,
    htbN 8468683810402, htbN 12754031967812, htbP 10179676667486, htbN 17958420979911,
    htbN 18114221916335, htbN 2814589450071, htbN 9748409022395, htbN 24371864857524,
    htbN 1563302306696, htbN 48708404795197, htbN 997628222249208 ]
private def htbSt_r256_fin : HtbSt :=
  (2, 256, 7138804677, htbVec_r256_10)
private def htbRow_r256 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 32, 0, 0, 76, 0,
    64, 0, 17, 0, 27, 0, 19, 35, 27, 10, 21, 51, 9, 5, 16, 0, 2, 35, 0, 14, 45, 70, 145, 98,
    658, 0, 11, 0, 154, 168, 0, 229, 1039, 131, 70, 3, 83, 10, 108, 84, 0, 0, 1588, 0, 0, 8453,
    232, 231, 722, 534, 19040, 1761, 924, 13898, 4257, 170, 3958, 3623, 441, 1025, 0, 4698,
    2301, 2718, 23724, 248, 36584, 339, 2581, 31, 7452, 12185, 22703, 10186, 27246, 53421, 308,
    23895, 51795, 81771, 103772, 27105, 9166, 1564, 63520, 196569, 461684, 8535, 1057099,
    221103, 94505, 4224285, 267575, 456300, 1273296, 149582, 499524, 13852, 19580, 156295,
    696247, 4149, 12574, 750353, 1025989, 612981, 4229139, 6142314, 25447420, 1065656, 4088487,
    33992949, 63214987, 2586625, 5031926, 224593690, 73907, 6608, 38907051, 24472254, 79217000,
    9092837, 4936056, 1432376, 91351161, 43170292, 71597743, 162483285, 103480526, 322248531,
    327866458, 7881779, 94892345, 593639875, 2421644, 2371813309, 995247826133 ]
private theorem htb_sl_r256_0 :
    htbChkSlice 256 htbSegs_r256_0 1 256 5948126 htbVec_r256_0
      (1, 256, 293532995, htbVec_r256_1) = true := by
  decide +kernel
private theorem htb_sl_r256_1 :
    htbChkSlice 256 htbSegs_r256_1 1 256 293532995 htbVec_r256_1
      (1, 256, 1195192530, htbVec_r256_2) = true := by
  decide +kernel
private theorem htb_sl_r256_2 :
    htbChkSlice 256 htbSegs_r256_2 1 256 1195192530 htbVec_r256_2
      (1, 256, 1959844421, htbVec_r256_3) = true := by
  decide +kernel
private theorem htb_sl_r256_3 :
    htbChkSlice 256 htbSegs_r256_3 1 256 1959844421 htbVec_r256_3
      (1, 256, 3120995542, htbVec_r256_4) = true := by
  decide +kernel
private theorem htb_sl_r256_4 :
    htbChkSlice 256 htbSegs_r256_4 1 256 3120995542 htbVec_r256_4
      (2, 256, 4653244721, htbVec_r256_5) = true := by
  decide +kernel
private theorem htb_sl_r256_5 :
    htbChkSlice 256 htbSegs_r256_5 2 256 4653244721 htbVec_r256_5
      (2, 256, 5080240818, htbVec_r256_6) = true := by
  decide +kernel
private theorem htb_sl_r256_6 :
    htbChkSlice 256 htbSegs_r256_6 2 256 5080240818 htbVec_r256_6
      (2, 256, 5435299228, htbVec_r256_7) = true := by
  decide +kernel
private theorem htb_sl_r256_7 :
    htbChkSlice 256 htbSegs_r256_7 2 256 5435299228 htbVec_r256_7
      (2, 256, 6220424779, htbVec_r256_8) = true := by
  decide +kernel
private theorem htb_sl_r256_8 :
    htbChkSlice 256 htbSegs_r256_8 2 256 6220424779 htbVec_r256_8
      (2, 256, 6829495850, htbVec_r256_9) = true := by
  decide +kernel
private theorem htb_sl_r256_9 :
    htbChkSlice 256 htbSegs_r256_9 2 256 6829495850 htbVec_r256_9
      htbSt_r256_fin = true := by
  decide +kernel
private def hm256coVPot : List ℕ :=
  [ 0, 40168692606171, 43079728286639, 47102760966452, 47677275125593, 48039244134973,
    48296234586762, 48493816692889, 48654597588673, 48791068307168, 48910687393415,
    49018168564189, 49116552930431, 49207895493608, 49293992157145, 49375856898183,
    49454187032685, 49530090206594, 49603595984530, 49675263255746, 49745405497244,
    49814289674774, 49882109522170, 49949070622054, 50015236595942, 50080467442858,
    50145454314100, 50210042395772, 50274316311487, 50338317931002, 50402233343827,
    57616743511379, 50528871828501, 50595938768433, 57484812717416, 64274561010014,
    50789735691709, 57393428077544, 63909650477082, 70341789064873, 51043946578843,
    57317242413296, 51167862563153, 57293530757724, 63349189016533, 51359737610921,
    57282288224960, 63141494230441, 51554105662880, 57292490320905, 62973201307550,
    68597943333337, 74168338751026, 79685933020492, 85152199716038, 90568545122120,
    95936312458082, 101256785767870, 106531193506625, 111760711852546, 116946467769301,
    122089541841579, 127190970903995, 132251750481449, 52629876070586, 57612189196788,
    62556613460372, 67464000316588, 72335169800653, 77170912127387, 81971989187633,
    86739135949496, 91473061771700, 96174451635695, 100843967302589, 105482248400423,
    110089913446856, 114667560811886, 119215769624845, 123735100629567, 128226096991302,
    132689285058655, 137125175083586, 141534261902256, 145917025579285, 150273932017802,
    154605433537482, 158911969422595, 163193966441947, 167451839342464, 171685991318020,
    175896814455020, 87332286460256, 91497585847564, 95640670146409, 99761891050959,
    103861591072619, 107940103872230, 111997754576976, 116034860082849, 120051729343467,
    124048663645993, 128025956874852, 131983895763897, 135922760137635, 139842823142096,
    143744351465871, 147627605551836, 151492839800031, 155340302762147, 159170237328036,
    162982880904644, 166778465587735, 170557218326767, 174319361083240, 178065110982839,
    181794680461656, 185508277406782, 189206105291523, 192888363305490, 196555246479806,
    200206945807640, 203843648360293, 207465537399021, 211072792482797, 214665589572185,
    218244101129493, 221808496215376, 58147722122626, 61684378303728, 65207405701261,
    68716960669340, 72213196595184, 75696263977341, 79166310501277, 82623481112447,
    86067918086939, 89499761099795, 92919147291100, 96326211329928, 99721085476227,
    103103899640729, 106474781442954, 109833856267389, 113181247317904, 116517075670481,
    119841460324314, 123154518251338, 126456364444256, 129747111963106, 133026871980434,
    136295753825117, 139553865024886, 142801311347596, 146038196841289, 149264623873091,
    152480693166987, 155686503840507, 158882153440373, 162067737977128, 165243351958795,
    168409088423590, 171565038971726, 174711293796340, 177847941713567, 180975070191793,
    184092765380115, 187201112136033, 190300194052398, 193390093483642, 196470891571313,
    199542668268935, 202605502366221, 205659471512650, 208704652240437, 211741119986910,
    214768949116315, 217788212941065, 220798983742451, 223801332790833, 226795330365323,
    229781045772980, 232758547367530, 235727902567622, 238689177874642, 241642438890087,
    244587750332525, 247525176054139, 250454779056880, 253376621508233, 256290764756608,
    259197269346371, 262096195032517, 264987600795008, 267871544852769, 270748084677369,
    273617277006382, 276479177856443, 279333842536011, 282181325657839, 285021681151162,
    287854962273616, 290681221622889, 293500511148114, 296312882161008, 299118385346769,
    301917070774735, 304708987908807, 307494185617652, 310272712184680, 313044615317813,
    315809942159040, 318568739293773, 321321052760002, 324066928057258, 326806410155392,
    329539543503165, 332266372036664, 334986939187541, 337701287891084, 340409460594125,
    343111499262783, 345807445390050, 348497340003227, 351181223671208, 353859136511620,
    356531118197817, 359197207965738, 361857444620632, 364511866543645, 367160511698280,
    369803417636735, 372440621506113, 375072160054513, 377698069637005, 380318386221491,
    382933145394452, 385542382366586, 388146131978341, 390744428705342, 393337306663720,
    395924799615333, 398506940972899, 401083763805029, 403655300841168, 406221584476445,
    408782646776435, 411338519481832, 413889234013040, 416434821474680, 418975312660014,
    421510738055292, 424041127844019, 426566511911150, 429086919847206, 431602380952318,
    73282395465187 ]
private def hm256coAnchors : List DickeSol.RampKick128kAnchor :=
  htbS0Pfx ++ [⟨256, htbSegs_r256, htbRow_r256⟩]
private theorem htb_meta : htbAtF [
    DickeSol.rkm128kCheckTable 256 256 2 true hm256coVPot hm256coAnchors,
    htbChkCell 8 2 56685214054921 250000000000000 hm256coVPot hm256coAnchors,
    htbChkCell 16 2 6047258346089 40000000000000 hm256coVPot hm256coAnchors,
    htbChkCell 32 2 51771084026387 500000000000000 hm256coVPot hm256coAnchors,
    htbChkCell 64 2 73425717276763 1000000000000000 hm256coVPot hm256coAnchors,
    htbChkCell 128 2 436301823401 7812500000000 hm256coVPot hm256coAnchors,
    htbChkCell 256 2 24416968724737 500000000000000 hm256coVPot hm256coAnchors,
    htbSegsGuard 256 htbSegs_r256,
    htbFinGuard htbSt_r256_fin htbRow_r256,
    htbListIntEq htbS0Vec htbVec_r256_0
  ] = true := by
  decide +kernel
private lemma htb_row_eq_r256 :
    DickeSol.rkm128kEvalRowLo12 256 2 256 htbSegs_r256 = htbRow_r256 := by
  have hc9 := htb_sl_end htb_sl_r256_9
  have hc8 := htb_sl_step htb_sl_r256_8 hc9
  have hc7 := htb_sl_step htb_sl_r256_7 hc8
  have hc6 := htb_sl_step htb_sl_r256_6 hc7
  have hc5 := htb_sl_step htb_sl_r256_5 hc6
  have hc4 := htb_sl_step htb_sl_r256_4 hc5
  have hc3 := htb_sl_step htb_sl_r256_3 hc4
  have hc2 := htb_sl_step htb_sl_r256_2 hc3
  have hc1 := htb_sl_step htb_sl_r256_1 hc2
  have hc0 := htb_sl_step htb_sl_r256_0 hc1
  have h01 := htbListIntEq_eq (htb_hd (htb_tl1 (htb_tl4 (htb_tl4 htb_meta))))
  have hrun : DickeSol.rkm128kRunSegs 256 2 256 htbSegs_r256 1 0 1 [Int.ofNat DickeSol.wdScale] =
      htbSt_r256_fin := by
    unfold htbSegs_r256
    exact htb_s0_glue
      GroverFindAll.Rk128kHiM256CoPt0.s0Segs_step
      h01 hc0
  exact htb_cert_row 256 htbSegs_r256 htbSt_r256_fin htbRow_r256
    (htb_hd (htb_tl1 (htb_tl2 (htb_tl4 htb_meta)))) hrun (htb_hd (htb_tl4 (htb_tl4 htb_meta)))
private lemma hm256coAncSound : DickeSol.RampKick128kAnchorsSound 256 2 hm256coAnchors := by
  unfold hm256coAnchors
  exact htb_anc_append
    GroverFindAll.Rk128kHiM256CoPt0.pfxAnchorsLt256_sound
    ⟨htb_row_eq_r256, trivial⟩
private theorem hm256coValid :
    DickeSol.RampKick128kTableValid 256 256 2 true hm256coVPot hm256coAnchors :=
  DickeSol.rkm128kCheckTable_sound hm256coAncSound (htb_hd htb_meta)
private theorem hm256coCellChecks {m k : ℕ} (h : isHiTailM256CoCertCell m k = true) :
    DickeSol.rkm128kCheckAnchorsLMax k (hiTailM256CoCertCellLMax m k) hm256coAnchors =
        true ∧
      ∃ num den : ℕ, relCostHiTailM256CoCert m k = NNRat.divNat num den ∧
        DickeSol.checkAltBound12 m k (hm256coVPot.getD k 0) num den = true := by
  unfold isHiTailM256CoCertCell at h
  split_ifs at h with hm256 hk8 hk16 hk32 hk64 hk128 hk256
  all_goals simp only [beq_iff_eq] at *
  · subst hm256 hk8; have hm := htb_hd (htb_tl1 htb_meta)
    exact ⟨htbChkCell_l hm, 56685214054921, 250000000000000, rfl, htbChkCell_r hm⟩
  · subst hm256 hk16; have hm := htb_hd (htb_tl2 htb_meta)
    exact ⟨htbChkCell_l hm, 6047258346089, 40000000000000, rfl, htbChkCell_r hm⟩
  · subst hm256 hk32; have hm := htb_hd (htb_tl1 (htb_tl2 htb_meta))
    exact ⟨htbChkCell_l hm, 51771084026387, 500000000000000, rfl, htbChkCell_r hm⟩
  · subst hm256 hk64; have hm := htb_hd (htb_tl4 htb_meta)
    exact ⟨htbChkCell_l hm, 73425717276763, 1000000000000000, rfl, htbChkCell_r hm⟩
  · subst hm256 hk128; have hm := htb_hd (htb_tl1 (htb_tl4 htb_meta))
    exact ⟨htbChkCell_l hm, 436301823401, 7812500000000, rfl, htbChkCell_r hm⟩
  · subst hm256 hk256; have hm := htb_hd (htb_tl2 (htb_tl4 htb_meta))
    exact ⟨htbChkCell_l hm, 24416968724737, 500000000000000, rfl, htbChkCell_r hm⟩

private lemma hm256co_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl

private lemma hm256co_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl

private lemma hm256co_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

private lemma hm256co_le_of_add {a b d : ℕ} (h : a + d = b) : a ≤ b := h ▸ Nat.le_add_right a d

private lemma hm256co_mem_grid (j d : ℕ) (h : (j + 1) + d = 11) : 2 ^ j ∈ DickeSol.groverGrid :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (hm256co_le_of_add h), rfl⟩

private structure Hm256coCellProps (m k : ℕ) : Prop where
  hmG : m ∈ DickeSol.groverGrid
  hkG : k ∈ DickeSol.groverGrid
  hk256 : k ≤ 256
  hm2 : 2 ≤ m
  hl2 : 2 ≤ hiTailM256CoCertCellLMax m k
  hl1 : 1 ≤ hiTailM256CoCertCellLMax m k
  hlm : hiTailM256CoCertCellLMax m k * m ≤ 65536
  htab : DickeSol.RampKick128kTableValid m 256 2 true hm256coVPot hm256coAnchors
  hlmax : DickeSol.rkm128kCheckAnchorsLMax k (hiTailM256CoCertCellLMax m k)
    hm256coAnchors = true
  hcost : ∃ num den : ℕ, relCostHiTailM256CoCert m k = NNRat.divNat num den ∧
    DickeSol.checkAltBound12 m k (hm256coVPot.getD k 0) num den = true

private theorem hm256co_all_props {m k : ℕ} (h : isHiTailM256CoCertCell m k = true) :
    Hm256coCellProps m k := by
  rcases hm256coCellChecks h with ⟨hlmax, hcost⟩
  unfold isHiTailM256CoCertCell at h
  split_ifs at h with hm256 hk8 hk16 hk32 hk64 hk128 hk256
  all_goals simp only [beq_iff_eq] at *
  · subst hm256 hk8
    exact ⟨hm256co_mem_grid 8 2 rfl, hm256co_mem_grid 3 7 rfl,
      hm256co_le_of_add (d := 248) rfl, hm256co_le_of_add (d := 254) rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 1) rfl,
      hm256co_le_of_add (d := 65024) rfl, hm256coValid, hlmax, hcost⟩
  · subst hm256 hk16
    exact ⟨hm256co_mem_grid 8 2 rfl, hm256co_mem_grid 4 6 rfl,
      hm256co_le_of_add (d := 240) rfl, hm256co_le_of_add (d := 254) rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 1) rfl,
      hm256co_le_of_add (d := 65024) rfl, hm256coValid, hlmax, hcost⟩
  · subst hm256 hk32
    exact ⟨hm256co_mem_grid 8 2 rfl, hm256co_mem_grid 5 5 rfl,
      hm256co_le_of_add (d := 224) rfl, hm256co_le_of_add (d := 254) rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 1) rfl,
      hm256co_le_of_add (d := 65024) rfl, hm256coValid, hlmax, hcost⟩
  · subst hm256 hk64
    exact ⟨hm256co_mem_grid 8 2 rfl, hm256co_mem_grid 6 4 rfl,
      hm256co_le_of_add (d := 192) rfl, hm256co_le_of_add (d := 254) rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 1) rfl,
      hm256co_le_of_add (d := 65024) rfl, hm256coValid, hlmax, hcost⟩
  · subst hm256 hk128
    exact ⟨hm256co_mem_grid 8 2 rfl, hm256co_mem_grid 7 3 rfl,
      hm256co_le_of_add (d := 128) rfl, hm256co_le_of_add (d := 254) rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 1) rfl,
      hm256co_le_of_add (d := 65024) rfl, hm256coValid, hlmax, hcost⟩
  · subst hm256 hk256
    exact ⟨hm256co_mem_grid 8 2 rfl, hm256co_mem_grid 8 2 rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 254) rfl,
      hm256co_le_of_add (d := 0) rfl, hm256co_le_of_add (d := 1) rfl,
      hm256co_le_of_add (d := 65024) rfl, hm256coValid, hlmax, hcost⟩

private noncomputable def hiTailM256CoCertCircuitImpl {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM256CoCertQubits n m k)) Var
      (hiTailM256CoCertQubits n m k) ((n + 1) * m) :=
  if h : isHiTailM256CoCertCell m k = true then
    let p := hm256co_all_props h
    DickeSol.rkm128kCellCircuit res p.hmG p.hkG hm256coVPot hm256coAnchors p.hk256
      (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n
  else .skip

/-- Dynamic parallel query-model circuit for the `6` supported `m = 256, k ≤ 256` cells. -/
noncomputable def findAllJohnsonRampKick128kHiTailM256CoCertCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hiTailM256CoCertQubits n m k)) Var
      (hiTailM256CoCertQubits n m k) ((n + 1) * m) :=
  hiTailM256CoCertCircuitImpl res n m k

private lemma hm256co_circuit_eq {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    {m k : ℕ} (h : isHiTailM256CoCertCell m k = true) :
    findAllJohnsonRampKick128kHiTailM256CoCertCircuit res n m k =
      let p := hm256co_all_props h
      DickeSol.rkm128kCellCircuit res p.hmG p.hkG hm256coVPot hm256coAnchors p.hk256
        (fun _ ↦ p.hm2) (fun _ ↦ p.hl2) p.hl1 p.hlm p.htab p.hlmax n := by
  unfold findAllJohnsonRampKick128kHiTailM256CoCertCircuit hiTailM256CoCertCircuitImpl
  exact dite_eq_left h

/-- Exact probability-`1` recovery of `S` across all `6` supported `m = 256, k ≤ 256` cells. -/
theorem hiTailM256CoCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isHiTailM256CoCertCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ hiTailM256CoCertQubits n m k)) ⦄
    (QProg.qSet ;;
      (findAllJohnsonRampKick128kHiTailM256CoCertCircuit res n m k).compile QProg.qAssign
        (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [hm256co_targetSets_eq]
  have hp := hm256co_all_props hcell
  rw [hm256co_circuit_eq res n hcell, ← hm256co_oracle_eq]
  exact DickeSol.rkm128kCell_correctness res hp.hmG hp.hkG hm256coVPot hm256coAnchors hp.hk256
    (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax hn hkN hS'

/-- Asymptotic uniform-average relative-cost bound across all `6` `m = 256, k ≤ 256` cells. -/
theorem hiTailM256CoCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isHiTailM256CoCertCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound
            (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;;
              (findAllJohnsonRampKick128kHiTailM256CoCertCircuit res n m k).compile
                QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostHiTailM256CoCert m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  have hp := hm256co_all_props hcell
  obtain ⟨n₁, hn₁⟩ := DickeSol.rkm128kCell_rel_cost (Var := Var) res hp.hmG hp.hkG hm256coVPot
    hm256coAnchors hp.hk256 (fun _ ↦ hp.hm2) (fun _ ↦ hp.hl2) hp.hl1 hp.hlm hp.htab hp.hlmax
    hp.hcost
  refine ⟨n₁, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₁ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · rw [hm256co_circuit_eq res n hcell, ← hm256co_oracle_eq]
    exact hq S (by rwa [hm256co_targetSets_eq])
  · rw [← hm256co_targetSets_eq, ← hm256co_vanilla_eq]; exact hsum

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

end QuantumComputation.Specs.GroverFindAll.Rk128kHiM256CoCert
