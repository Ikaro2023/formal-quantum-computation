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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.WeakDickeCore
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingZoomK2Base
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RampKickMuxHiCert1024
/-
# Middle-`p` Unpadded `wt = r - 1` Multi-Collision Zoom Evaluator (`GaussianHammingMidPZoomEval`)

QHL-free `10 ^ 15`-scaled complex-interval evaluator, outward `sqrt(1..16)` / `arcsin` ratio
enclosures, `64`-step structural Newton `midPUnpaddedZoomScaleHi15`, and `W = 16` Bellman
spine / row-slice checkers shared across `GaussianHammingMidPZoomPt0..3` and
`GaussianHammingMidPZoomSoundness`.
-/
section GHMidPZoomEval
namespace QuantumComputation.Specs.DickeSol
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
@[expose] public section
/- ## 1. Schedule & Summary Structures (`3 ≤ r ≤ 16`) -/
/-- Single Gaussian-rational phase `(ga + i * gb) / gd` (`ga ^ 2 + gb ^ 2 = gd ^ 2`). -/
structure MidPPhaseSpec where
  ga : ℤ
  gb : ℤ
  gd : ℕ
  deriving DecidableEq, Repr
/-- Alias matching `GHMidP*` signature convention. -/
abbrev GHMidPPhaseSpec := MidPPhaseSpec
/-- One `3 ≤ r ≤ 16` Gaussian-Hamming probe `(da, rotTop, phases)`. -/
structure MidPProbeSpec where
  daNum : ℕ
  daDen : ℕ
  cNum : ℤ
  sNum : ℕ
  cDen : ℕ
  phases : List MidPPhaseSpec
  deriving DecidableEq, Repr
/-- Alias matching `GHMidP*` signature convention. -/
abbrev GHMidPProbeSpec := MidPProbeSpec
/-- Row specification `(a0, kz, probes)` for middle-`p` `wt = r - 1` collision zoom. -/
structure MidPRowSpec where
  a0Num : ℕ
  a0Den : ℕ
  kzNum : ℕ
  kzDen : ℕ
  probes : List MidPProbeSpec
  deriving DecidableEq, Repr
/-- Alias matching `GHMidP*` signature convention. -/
abbrev GHMidPRowSpec := MidPRowSpec
/-- Precomputed `10 ^ 15`-scaled multi-collision summary for one `(m, r)` row (`3 ≤ r ≤
  16`). -/
structure MidPSummary where
  qDistHi : ℤ
  qCollHi : ℤ
  qZoomHi : ℤ
  zHitLo : ℤ
  uAbs2Hi : List ℤ
  z0Abs2Hi : List ℤ
  z1Abs2Hi : List ℤ
  tpWtHi : List ℤ
  stWtHi : List ℤ
  q1WtHi : List ℤ
  deriving DecidableEq, Repr
/-- Alias matching `GHMidP*` signature convention. -/
abbrev GHMidPSummary := MidPSummary
/-- Total fallback `MidPRowSpec` for `.getD` indexing. -/
def midPEmptyRowSpec : MidPRowSpec := ⟨0, 0, 0, 0, []⟩
/-- Total fallback `MidPSummary` for `.getD` indexing. -/
def midPEmptySummary : MidPSummary := ⟨0, 0, 0, 0, [], [], [], [], [], []⟩
/- ## 2. Bare-Literal `@Nat.casesOn` WHNF Barriers & Primitive `Int` Ops -/
/-- Forces `x: ℕ` to an atomic `Literal.natVal` via `@Nat.casesOn` on `Nat.add 1 x`. -/
def midPLitNat {α : Type*} (x : ℕ) (k : ℕ → α) : α := @Nat.casesOn (fun _ ↦ α) (Nat.add 1 x) (k 0) k
private lemma midP_one_add_eq_succ : ∀ x : ℕ, Nat.add 1 x = Nat.succ x
  | 0 => rfl
  | x + 1 => congrArg Nat.succ (midP_one_add_eq_succ x)
theorem midPLitNat_eq {α : Type*} (x : ℕ) (k : ℕ → α) : midPLitNat x k = k x := by
  dsimp only [midPLitNat]; rw [midP_one_add_eq_succ x]
/-- Strict CPS WHNF barrier forcing `x: ℤ` to an atomic GMP literal before `k`. -/
def midPSeqInt {α : Type*} (x : ℤ) (k : ℤ → α) : α :=
  Int.casesOn x (fun n ↦ midPLitNat n fun v ↦ k (Int.ofNat v))
    (fun n ↦ midPLitNat n fun v ↦ k (Int.negSucc v))
theorem midPSeqInt_eq {α : Type*} (x : ℤ) (k : ℤ → α) : midPSeqInt x k = k x := by cases x with
  | ofNat n => dsimp only [midPSeqInt]; exact midPLitNat_eq n (fun v ↦ k (Int.ofNat v))
  | negSucc n => dsimp only [midPSeqInt]; exact midPLitNat_eq n (fun v ↦ k (Int.negSucc v))
/-- Forces a single `ℤ` to an atomic GMP literal. -/
def midPForceInt (z : ℤ) : ℤ := midPSeqInt z id
theorem midPForceInt_eq (z : ℤ) : midPForceInt z = z := midPSeqInt_eq z id
/-- Constructor-level `Bool` `≤` on `ℤ` avoiding Mathlib `LinearOrder Int` in kernel
  evaluation. -/
def midPBleZ : ℤ → ℤ → Bool
  | Int.ofNat a, Int.ofNat b => Nat.ble a b
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc _, Int.ofNat _ => true
  | Int.negSucc a, Int.negSucc b => Nat.ble b a
theorem midPBleZ_iff (a b : ℤ) : midPBleZ a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp [midPBleZ, Nat.ble_eq] <;> omega
/-- Constructor-level `Bool` `<` on `ℤ` avoiding Mathlib `LinearOrder Int` in kernel
  evaluation. -/
def midPBltZ (a b : ℤ) : Bool := midPBleZ (Int.add a 1) b
theorem midPBltZ_iff (a b : ℤ) : midPBltZ a b = true ↔ a < b := by
  unfold midPBltZ; rw [midPBleZ_iff]; change a + 1 ≤ b ↔ a < b; omega
/-- Strict CPS WHNF barrier forcing both `ℤ` endpoints of `iv: WDIVal`. -/
def midPSeqIV {α : Type*} (iv : WDIVal) (k : WDIVal → α) : α :=
  midPSeqInt iv.1 fun a ↦ midPSeqInt iv.2 fun b ↦ k (a, b)
theorem midPSeqIV_eq {α : Type*} (iv : WDIVal) (k : WDIVal → α) : midPSeqIV iv k = k iv := by
  rcases iv with ⟨a, b⟩; simp only [midPSeqIV, midPSeqInt_eq]
/-- Strict CPS WHNF barrier forcing all four `ℤ` endpoints of `z: WDCVal`. -/
def midPSeqCIV {α : Type*} (z : WDCVal) (k : WDCVal → α) : α :=
  midPSeqIV z.1 fun re' ↦ midPSeqIV z.2 fun im' ↦ k (re', im')
theorem midPSeqCIV_eq {α : Type*} (z : WDCVal) (k : WDCVal → α) : midPSeqCIV z k = k z := by
  rcases z with ⟨_, _⟩; simp only [midPSeqCIV, midPSeqIV_eq]
/-- Strict CPS WHNF barrier forcing a `List WDCVal` spine. -/
def midPSeqCIVList {α : Type*} : List WDCVal → (List WDCVal → α) → α
  | [], k => k []
  | z :: zs, k => midPSeqCIV z fun z' ↦ midPSeqCIVList zs fun zs' ↦ k (z' :: zs')
theorem midPSeqCIVList_eq {α : Type*} (xs : List WDCVal) (k : List WDCVal → α) :
    midPSeqCIVList xs k = k xs := by induction xs generalizing k with
  | nil => rfl
  | cons z zs ih => simp only [midPSeqCIVList, midPSeqCIV_eq, ih]
/-- Strict CPS WHNF barrier forcing a `List (List WDCVal)` matrix via `midPSeqCIVList`. -/
def midPSeqCIVRows {α : Type*} : List (List WDCVal) → (List (List WDCVal) → α) → α
  | [], k => k []
  | row :: rest, k => midPSeqCIVList row fun row' ↦
        midPSeqCIVRows rest fun rest' ↦ k (row' :: rest')
theorem midPSeqCIVRows_eq {α : Type*} (rows : List (List WDCVal))
    (k : List (List WDCVal) → α) : midPSeqCIVRows rows k = k rows := by
  induction rows generalizing k with
  | nil => rfl
  | cons row rest ih => simp only [midPSeqCIVRows, midPSeqCIVList_eq, ih]
/-- Strict CPS WHNF barrier forcing a `List ℤ` spine. -/
def midPSeqZList {α : Type*} : List ℤ → (List ℤ → α) → α
  | [], k => k []
  | z :: zs, k => midPSeqInt z fun z' ↦ midPSeqZList zs fun zs' ↦ k (z' :: zs')
theorem midPSeqZList_eq {α : Type*} (xs : List ℤ) (k : List ℤ → α) : midPSeqZList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons z zs ih => simp only [midPSeqZList, midPSeqInt_eq, ih]
/-- Re-forces the 8 scalar fields of a `GHZoomSummary` to bare GMP literals before Bellman
  steps. -/
def midPForceZoomSummary {α : Type*} (s : GHZoomSummary) (k : GHZoomSummary → α) : α :=
  midPSeqInt s.qDistHi fun qd ↦ midPSeqInt s.qCollHi fun qc ↦ midPSeqInt s.qZoomHi fun qz ↦
  midPSeqInt s.zHitLo fun zh ↦ midPSeqInt s.u0Hi fun u0 ↦ midPSeqInt s.u1Hi fun u1 ↦
  midPSeqInt s.z0Hi fun z0 ↦ midPSeqInt s.z1Hi fun z1 ↦ k ⟨qd, qc, qz, zh, u0, u1, z0, z1⟩
theorem midPForceZoomSummary_eq {α : Type*} (s : GHZoomSummary) (k : GHZoomSummary → α) :
    midPForceZoomSummary s k = k s := by
  rcases s with ⟨_, _, _, _, _, _, _, _⟩; simp only [midPForceZoomSummary, midPSeqInt_eq]
/-- Pre-cast primitive `10 ^ 15: ℤ` constant avoiding `NatCast` unfolding in kernel
  evaluation. -/
def midPScaleZ : ℤ := Int.ofNat 1000000000000000
/-- Primitive `WDIVal` multiplication binding `p1.. p4` via `midPSeqInt` (`= ghMulIV`). -/
def midPFastMulIV (x y : WDIVal) : WDIVal :=
  midPSeqInt (Int.mul x.1 y.1) fun p1 ↦ midPSeqInt (Int.mul x.1 y.2) fun p2 ↦
  midPSeqInt (Int.mul x.2 y.1) fun p3 ↦ midPSeqInt (Int.mul x.2 y.2) fun p4 ↦
    (Int.ediv (ghMinZ (ghMinZ p1 p2) (ghMinZ p3 p4)) midPScaleZ,
      Int.neg (Int.ediv (Int.neg (ghMaxZ (ghMaxZ p1 p2) (ghMaxZ p3 p4))) midPScaleZ))
theorem midPFastMulIV_eq (x y : WDIVal) : midPFastMulIV x y = ghMulIV x y := by
  unfold midPFastMulIV ghMulIV; simp only [midPSeqInt_eq]; rfl
/-- Primitive complex-interval addition (`rfl`-equal to `wdCAdd`). -/
def midPFastCAdd (a b : WDCVal) : WDCVal :=
  ((Int.add a.1.1 b.1.1, Int.add a.1.2 b.1.2), (Int.add a.2.1 b.2.1, Int.add a.2.2 b.2.2))
theorem midPFastCAdd_eq (a b : WDCVal) : midPFastCAdd a b = wdCAdd a b := rfl
/-- Primitive complex-interval subtraction (`rfl`-equal to `wdCSub`). -/
def midPFastCSub (a b : WDCVal) : WDCVal :=
  ((Int.sub a.1.1 b.1.2, Int.sub a.1.2 b.1.1), (Int.sub a.2.1 b.2.2, Int.sub a.2.2 b.2.1))
theorem midPFastCSub_eq (a b : WDCVal) : midPFastCSub a b = wdCSub a b := rfl
/-- Primitive real-interval × complex-interval product (`= wdCRMul`). -/
def midPFastCRMul (rIV : WDIVal) (z : WDCVal) : WDCVal :=
  (midPFastMulIV rIV z.1, midPFastMulIV rIV z.2)
theorem midPFastCRMul_eq (rIV : WDIVal) (z : WDCVal) : midPFastCRMul rIV z = wdCRMul rIV z := by
  unfold midPFastCRMul wdCRMul; rw [midPFastMulIV_eq, midPFastMulIV_eq, ghMulIV_eq, ghMulIV_eq]
/-- Primitive complex-interval product binding `ac, bd, ad, bc` via `midPSeqIV` (`=
  wdCMul`). -/
def midPFastCMul (a b : WDCVal) : WDCVal :=
  midPSeqIV (midPFastMulIV a.1 b.1) fun ac ↦ midPSeqIV (midPFastMulIV a.2 b.2) fun bd ↦
  midPSeqIV (midPFastMulIV a.1 b.2) fun ad ↦ midPSeqIV (midPFastMulIV a.2 b.1) fun bc ↦
    ((Int.sub ac.1 bd.2, Int.sub ac.2 bd.1), (Int.add ad.1 bc.1, Int.add ad.2 bc.2))
theorem midPFastCMul_eq (a b : WDCVal) : midPFastCMul a b = wdCMul a b := by
  unfold midPFastCMul wdCMul wdSub; simp only [midPSeqIV_eq, midPFastMulIV_eq, ghMulIV_eq]; rfl
/-- CPS bare-literal-forced 10-step double-angle recursion (`0` `Nat.add` thunks). -/
def midPDoubleAngleIterCPS {α : Type*} : ℕ → WDIVal → WDIVal → (WDIVal → WDIVal → α) → α
  | 0, c, s, k => k c s
  | n + 1, c, s, k => midPSeqIV (wdSub (ghSqIV c) (ghSqIV s)) fun c' ↦
        midPSeqIV (wdScaleNat 2 (midPFastMulIV s c)) fun s' ↦ midPDoubleAngleIterCPS n c' s' k
theorem midPDoubleAngleIterCPS_eq {α : Type*} : ∀ (n : ℕ) (c s : WDIVal) (k : WDIVal → WDIVal → α),
      midPDoubleAngleIterCPS n c s k = ghDoubleAngleIterCPS n c s k
  | 0, _, _, _ => rfl
  | n + 1, c, s, k => by
      simp only [midPDoubleAngleIterCPS, ghDoubleAngleIterCPS,
        midPSeqIV_eq, ghSeqIV_eq, midPFastMulIV_eq]
      exact midPDoubleAngleIterCPS_eq n _ _ k
/-- CPS bare-literal-forced trigonometric enclosure (`= wdTrig`). -/
def midPTrigCPS {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) : α :=
  midPSeqIV (wdDivFloor x.1 1024, wdDivCeil x.2 1024) fun u ↦ ghTrigBaseCPS u fun c0 s0 ↦
      midPSeqIV c0 fun c0F ↦ midPSeqIV s0 fun s0F ↦ midPDoubleAngleIterCPS 10 c0F s0F k
theorem midPTrigCPS_eq {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) :
    midPTrigCPS x k = k (wdTrig x).1 (wdTrig x).2 := by
  have heq : midPTrigCPS x k = ghTrigCPS x k := by
    unfold midPTrigCPS ghTrigCPS
    simp only [midPSeqIV_eq, ghSeqIV_eq, ghTrigBaseCPS_eq, midPDoubleAngleIterCPS_eq]
  rw [heq, ghTrigCPS_eq]
/-- Strictly forced `O(N)` GMP integer range sum `∑_{w < N} f w`. -/
def midPSumRangeZAux (f : ℕ → ℤ) : ℕ → ℤ → ℤ
  | 0, acc => acc
  | n + 1, acc => midPSeqInt (Int.add acc (f n)) fun acc' ↦ midPSumRangeZAux f n acc'
/-- Strictly forced `O(N)` GMP integer sum over `0.. N - 1`. -/
def midPSumRangeZ (N : ℕ) (f : ℕ → ℤ) : ℤ := midPSumRangeZAux f N 0
theorem midPSumRangeZAux_eq (f : ℕ → ℤ) :
    ∀ (n : ℕ) (acc : ℤ), midPSumRangeZAux f n acc = acc + ∑ w ∈ Finset.range n, f w
  | 0, acc => by simp [midPSumRangeZAux]
  | n + 1, acc => by
      simp only [midPSumRangeZAux, midPSeqInt_eq]; have hadd : Int.add acc (f n) = acc + f n := rfl
      rw [hadd, midPSumRangeZAux_eq f n (acc + f n), Finset.sum_range_succ]; ring
/-- Structural falling factorial `m * (m - 1) *... * (m - k + 1)` (`= m.descFactorial k`). -/
def midPDescFact (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (m - k) * midPDescFact m k
theorem midPDescFact_eq (m : ℕ) : ∀ k : ℕ, midPDescFact m k = m.descFactorial k
  | 0 => rfl
  | k + 1 => by simp only [midPDescFact, Nat.descFactorial_succ, midPDescFact_eq m k]
/- ## 3. Outward `10 ^ 15` `sqrt(1..16)` / `arcsin` Bounds & Unpadded Zoom Scale -/
/-- Outward `10 ^ 15`-scaled enclosure `[lo, hi]` for `√w * 10 ^ 15` (`1 ≤ w ≤ 16`). -/
structure MidPSqrtEntry where
  w : ℕ
  exactSq : Bool
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr
/-- Certified outward `10 ^ 15` `sqrt(1..16)` table (`lo ^ 2 ≤ w * 10 ^ 30 ≤ hi ^ 2`). -/
def midPSqrtTable16 : List MidPSqrtEntry :=
  [ ⟨1, true, 1000000000000000, 1000000000000000⟩, ⟨2, false, 1414213562373095, 1414213562373096⟩
  , ⟨3, false, 1732050807568877, 1732050807568878⟩, ⟨4, true, 2000000000000000, 2000000000000000⟩
  , ⟨5, false, 2236067977499789, 2236067977499790⟩, ⟨6, false, 2449489742783178, 2449489742783179⟩
  , ⟨7, false, 2645751311064590, 2645751311064591⟩, ⟨8, false, 2828427124746190, 2828427124746191⟩
  , ⟨9, true, 3000000000000000, 3000000000000000⟩, ⟨10, false, 3162277660168379, 3162277660168380⟩
  , ⟨11, false, 3316624790355399, 3316624790355400⟩, ⟨12, false, 3464101615137754, 3464101615137755⟩
  , ⟨13, false, 3605551275463989, 3605551275463990⟩, ⟨14, false, 3741657386773941, 3741657386773942⟩
  , ⟨15, false, 3872983346207416, 3872983346207417⟩
  , ⟨16, true, 4000000000000000, 4000000000000000⟩ ]
/-- Total lookup of `MidPSqrtEntry` for `1 ≤ w ≤ 16`. -/
def midPSqrtEntry (w : ℕ) : MidPSqrtEntry :=
  midPSqrtTable16.getD (w - 1) ⟨1, true, 1000000000000000, 1000000000000000⟩
/-- Outward `subN ≥ 200` `arcsin(√w / √D) / arcsin(1 / √D)` interval `(lo - 1, hi + 1)`. -/
def midPSqrtRatioIv (w : ℕ) : WDIVal :=
  let e := midPSqrtEntry w
  (Int.sub e.lo 1, Int.add e.hi 1)
/-- Structural `64`-step Newton integer square-root loop (exact 64-step integer isqrt
  mirror). -/
def midPIsqrtLoop : ℕ → ℕ → ℕ → ℕ
  | 0, g, _ => g
  | fuel + 1, g, n =>
      let den := if g == 0 then 1 else g
      let g1 := (g + n / den) / 2
      if Nat.ble g g1 then g else midPIsqrtLoop fuel g1 n
/-- Exact `0`-ULP outward `10 ^ 15` unpadded middle-`p` zoom scale `⌊√(wt * 10 ^ 30 / m)⌋ +
  1`. -/
def midPUnpaddedZoomScaleHi15 (wt m : ℕ) : ℤ :=
  if m == 0 then 0
  else
    let num : ℕ := wt * 1000000000000000 * 1000000000000000
    let n : ℕ := num / m
    midPLitNat (midPIsqrtLoop 64 1000000000000000 n) fun g ↦
      let isq : ℕ := if Nat.ble (g * g) n then g else g - 1
      let uCand : ℕ := isq + 1
      midPLitNat (if Nat.ble num (m * (uCand * uCand)) then uCand else n + 1) Int.ofNat
/-- Alias matching `wdUnpaddedZoomScaleHi15` signature convention. -/
abbrev wdUnpaddedZoomScaleHi15 := midPUnpaddedZoomScaleHi15
/- ## 4. `.getD`-Free CPS Multi-Collision Tensor Evaluator (`3 ≤ r ≤ 16`) -/
lemma midPList_headD_eq_getD_zero {α : Type*} (xs : List α) (d : α) : xs.headD d = xs.getD 0 d := by
  cases xs with
  | nil => exact List.getD_nil.symm
  | cons x tl => exact List.getD_cons_zero.symm
lemma midPList_tail_getD {α : Type*} (xs : List α) (k : ℕ) (d : α) :
    xs.tail.getD k d = xs.getD (k + 1) d := by cases xs with
  | nil => rw [List.tail_nil, List.getD_nil, List.getD_nil]
  | cons x tl => rw [List.tail_cons, List.getD_cons_succ]
/-- Decomposes `xs: List WDCVal` into `(headD wdCZero, tail)`. -/
def midPUnconsC {α : Type*} (xs : List WDCVal) (k : WDCVal → List WDCVal → α) : α :=
  match xs with
  | [] => k wdCZero []
  | x :: tl => k x tl
lemma midPUnconsC_eq {α : Type*} (xs : List WDCVal) (k : WDCVal → List WDCVal → α) :
    midPUnconsC xs k = k (xs.headD wdCZero) xs.tail := by
  cases xs <;> rfl
/-- Decomposes `rows: List (List WDCVal)` into `(headD [], tail)`. -/
def midPUnconsRows {α : Type*} (rows : List (List WDCVal))
    (k : List WDCVal → List (List WDCVal) → α) : α :=
  match rows with
  | [] => k [] []
  | r0 :: tl => k r0 tl
lemma midPUnconsRows_eq {α : Type*} (rows : List (List WDCVal))
    (k : List WDCVal → List (List WDCVal) → α) :
    midPUnconsRows rows k = k (rows.headD []) rows.tail := by
  cases rows <;> rfl
/-- Structural `O(t)` `.getD`-free lockstep Pascal pair combiner (`= dickeCombinePairCIV`). -/
def midPCombineZip : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, c, s, left, right => midPUnconsC left fun l0 _ ↦ midPUnconsC right fun r0 _ ↦
          [midPFastCSub (midPFastCRMul c l0) (midPFastCRMul s r0),
            midPFastCAdd (midPFastCRMul s l0) (midPFastCRMul c r0)]
  | t + 1, c, s, left, right => midPUnconsC left fun l0 ltl ↦ midPUnconsC right fun r0 rtl ↦
          midPFastCSub (midPFastCRMul c l0) (midPFastCRMul s r0) :: midPCombineZip t c s ltl rtl
lemma midPCombineZip_eq : ∀ (t : ℕ) (c s : WDIVal) (left right : List WDCVal),
      midPCombineZip t c s left right = dickeCombinePairCIV t c s left right
  | 0, c, s, left, right => by
      have hr2 : List.range (Nat.add 0 2) = [0, 1] := rfl; unfold midPCombineZip dickeCombinePairCIV
      rw [hr2, List.map_cons, List.map_cons, List.map_nil,
        ite_eq_left (Nat.le_refl 0), ite_eq_right (by omega : ¬(1 ≤ 0))]
      simp only [midPUnconsC_eq, midPList_headD_eq_getD_zero,
        midPFastCSub_eq, midPFastCAdd_eq, midPFastCRMul_eq]
  | t + 1, c, s, left, right => by
      have hn : Nat.add (t + 1) 2 = (Nat.add t 2) + 1 := rfl; unfold dickeCombinePairCIV
      rw [hn, List.range_succ_eq_map, List.map_cons, List.map_map,
        ite_eq_left (Nat.zero_le (t + 1))]
      simp only [midPCombineZip, midPUnconsC_eq, midPList_headD_eq_getD_zero,
        midPFastCSub_eq, midPFastCRMul_eq, midPCombineZip_eq t c s left.tail right.tail]
      unfold dickeCombinePairCIV; refine congrArg (_ :: ·) (List.map_congr_left fun w' _ ↦ ?_)
      dsimp only [Function.comp_def]; have hsucc : Nat.succ w' = w' + 1 := rfl; rw [hsucc]
      by_cases hw : w' ≤ t
      · have hw1 : w' + 1 ≤ t + 1 := Nat.succ_le_succ hw
        rw [ite_eq_left hw, ite_eq_left hw1, midPList_tail_getD, midPList_tail_getD]
      · have hw1 : ¬(w' + 1 ≤ t + 1) := by omega
        rw [ite_eq_right hw, ite_eq_right hw1, midPList_tail_getD, midPList_tail_getD]
/-- Structural `O(numOut * t)` `.getD`-free adjacent-row Pascal step (`=
  dickeAdvanceLayerCIV`). -/
def midPAdvanceZip : ℕ → ℕ → WDIVal → WDIVal → List (List WDCVal) → List (List WDCVal)
  | 0, _, _, _, _ => []
  | numOut + 1, t, c, s, rows => midPUnconsRows rows fun r0 tl ↦
        midPUnconsRows tl fun r1 _ ↦ midPCombineZip t c s r0 r1 :: midPAdvanceZip numOut t c s tl
lemma midPAdvanceZip_eq : ∀ (numOut t : ℕ) (c s : WDIVal) (rows : List (List WDCVal)),
      midPAdvanceZip numOut t c s rows = dickeAdvanceLayerCIV t numOut c s rows
  | 0, _, _, _, _ => rfl
  | numOut + 1, t, c, s, rows => by
      unfold dickeAdvanceLayerCIV; rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [midPAdvanceZip, midPUnconsRows_eq, midPCombineZip_eq,
        midPList_headD_eq_getD_zero, midPList_tail_getD,
        midPAdvanceZip_eq numOut t c s rows.tail]
      unfold dickeAdvanceLayerCIV; refine congrArg (_ :: ·) (List.map_congr_left fun off _ ↦ ?_)
      dsimp only [Function.comp_def]; have h1 : Nat.succ off = off + 1 := rfl
      have h2 : Nat.add (off + 1) 1 = Nat.add off 1 + 1 := rfl
      rw [h1, h2, midPList_tail_getD, midPList_tail_getD]
/-- Structural `O(deg ^ 2)` `.getD`-free Pascal layer iterator (`= dickeIterLayersCIV`). -/
def midPFastIterLayersCIV : ℕ → ℕ → WDIVal → WDIVal → List (List WDCVal) → List (List WDCVal)
  | 0, _, _, _, rows => rows
  | rem + 1, t, c, s, rows => midPSeqCIVRows (midPAdvanceZip (Nat.add rem 1) t c s rows) fun rows' ↦
        midPFastIterLayersCIV rem (Nat.add t 1) c s rows'
lemma midPFastIterLayersCIV_eq : ∀ (rem t : ℕ) (c s : WDIVal) (rows : List (List WDCVal)),
      midPFastIterLayersCIV rem t c s rows = dickeIterLayersCIV c s rem t rows
  | 0, _, _, _, _ => rfl
  | rem + 1, t, c, s, rows => by
      simp only [midPFastIterLayersCIV, dickeIterLayersCIV, midPAdvanceZip_eq,
        midPSeqCIVRows_eq, ghSeqCIVRows_eq]
      exact midPFastIterLayersCIV_eq rem (Nat.add t 1) c s _
/-- Structural `O(n)` `.getD`-free initial singleton-row list from `uList: List WDCVal`. -/
def midPFastInitRowsList : ℕ → List WDCVal → List (List WDCVal)
  | 0, _ => []
  | n + 1, xs => midPUnconsC xs fun x0 tl ↦ [x0] :: midPFastInitRowsList n tl
lemma midPFastInitRowsList_eq : ∀ (n : ℕ) (xs : List WDCVal),
      midPFastInitRowsList n xs = (List.range n).map fun off ↦ [xs.getD off wdCZero]
  | 0, _ => rfl
  | n + 1, xs => by
      simp only [midPFastInitRowsList, midPUnconsC_eq, midPList_headD_eq_getD_zero,
        midPFastInitRowsList_eq n xs.tail]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg (_ :: ·) (List.map_congr_left fun off _ ↦ ?_); dsimp only [Function.comp_def]
      have h1 : Nat.succ off = off + 1 := rfl; rw [h1, midPList_tail_getD]
/-- Fast `.getD`-free `dickeStepCIVVec` over `uList` (`= dickeStepCIVVec`). -/
def midPFastDickeStepVec (deg : ℕ) (cIV sIV : WDIVal) (uList : List WDCVal) : List WDCVal :=
  midPSeqCIVRows (midPFastInitRowsList (Nat.add deg 1) uList) fun initRows ↦
    (midPFastIterLayersCIV deg 0 cIV sIV initRows).headD []
theorem midPFastDickeStepVec_eq (deg : ℕ) (cIV sIV : WDIVal) (uList : List WDCVal) :
    midPFastDickeStepVec deg cIV sIV uList =
      dickeStepCIVVec deg cIV sIV (fun w ↦ uList.getD w wdCZero) := by
  unfold midPFastDickeStepVec dickeStepCIVVec; rw [midPFastInitRowsList_eq]
  simp only [midPSeqCIVRows_eq, ghSeqCIVRows_eq, midPFastIterLayersCIV_eq,
    midPList_headD_eq_getD_zero]
/-- One-hot `[wdCOne, wdCZero,..., wdCZero]` vector of length `len`. -/
def midPOneHot0 : ℕ → List WDCVal
  | 0 => []
  | n + 1 => wdCOne :: List.replicate n wdCZero
/-- Structural `.getD`-free lockstep `c * m0 - s * m1` combiner. -/
def midPZipRotSub : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _, _, _ => []
  | n + 1, cIV, sIV, m0, m1 => midPUnconsC m0 fun a0 tl0 ↦ midPUnconsC m1 fun a1 tl1 ↦
          midPFastCSub (midPFastCRMul cIV a0) (midPFastCRMul sIV a1) ::
            midPZipRotSub n cIV sIV tl0 tl1
/-- Structural `.getD`-free lockstep `s * m0 + c * m1` combiner. -/
def midPZipRotAdd : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _, _, _ => []
  | n + 1, cIV, sIV, m0, m1 => midPUnconsC m0 fun a0 tl0 ↦ midPUnconsC m1 fun a1 tl1 ↦
          midPFastCAdd (midPFastCRMul sIV a0) (midPFastCRMul cIV a1) ::
            midPZipRotAdd n cIV sIV tl0 tl1
/-- Decomposes `gs: List WDCVal` into `(headD wdCOne, tail)`. -/
def midPUnconsC1 {α : Type*} (gs : List WDCVal) (k : WDCVal → List WDCVal → α) : α :=
  match gs with
  | [] => k wdCOne []
  | g :: tl => k g tl
/-- `.getD`-free phase damping on `1.. deg1` (`d0[w1] = gIVs[w1 - 1] * r0[w1]`). -/
def midPDampShift0Aux : ℕ → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _ => []
  | k + 1, gs, xs => midPUnconsC1 gs fun g gsTl ↦
        midPUnconsC xs fun x xsTl ↦ midPFastCMul g x :: midPDampShift0Aux k gsTl xsTl
/-- Row-0 damping (`w1 = 0` untouched, `1 ≤ w1 ≤ deg1` multiplied by `gIVs[w1 - 1]`). -/
def midPFastDamp2Row0 (deg1 : ℕ) (gIVs r0 : List WDCVal) : List WDCVal :=
  midPUnconsC r0 fun x0 r0Tl ↦ x0 :: midPDampShift0Aux deg1 gIVs r0Tl
/-- Shifted row damping (`0 ≤ w1 ≤ deg1` multiplied by `gs[w1]`). -/
def midPFastDamp2Row1 (deg1 : ℕ) (gs r1 : List WDCVal) : List WDCVal :=
  midPDampShift0Aux (Nat.add deg1 1) gs r1
/-- Structural `Nat.rec` tail helper for `midPFastDampUAux` (`0` `WellFounded.fix`). -/
def midPFastDampUTail : ℕ → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, cTop, gs, xs => midPUnconsC1 gs fun g _ ↦
        midPUnconsC xs fun x _ ↦ [midPFastCRMul cTop (midPFastCMul g x)]
  | k + 1, cTop, gs, xs => midPUnconsC1 gs fun g gsTl ↦
        midPUnconsC xs fun x xsTl ↦ midPFastCMul g x :: midPFastDampUTail k cTop gsTl xsTl
/-- `.getD`-free injective-fiber damping on `0.. r` (`rotTop.cos` on top weight `r`). -/
def midPFastDampUAux : ℕ → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _, _ => []
  | k + 1, cTop, gs, xs => midPFastDampUTail k cTop gs xs
/-- Injective-fiber damping vector on `0.. r`. -/
def midPFastDampU (r : ℕ) (gIVs : List WDCVal) (cTop : WDIVal) (uVec : List WDCVal) : List WDCVal :=
  midPUnconsC uVec fun u0 uTl ↦ u0 :: midPFastDampUAux r cTop gIVs uTl
/-- CPS `2`-row collision-fiber step (`SinglePair` at `deg1 = r - 2`, `SingleTriple` at `r -
  3`,
  `SingleQuad` at `r - 4`). -/
def midPFastStep2RowCPS {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal)
    (c1 s1 cC sC : WDIVal) (r0 r1 : List WDCVal) (k : List WDCVal → List WDCVal → α) : α :=
  midPSeqCIVList (midPFastDamp2Row0 deg1 gIVs r0) fun d0 ↦
  midPSeqCIVList (midPFastDamp2Row1 deg1 gIVs r1) fun d1 ↦
  midPSeqCIVList (midPFastDickeStepVec deg1 c1 s1 d0) fun m0 ↦
  midPSeqCIVList (midPFastDickeStepVec deg1 c1 s1 d1) fun m1 ↦
  midPSeqCIVList (midPZipRotSub (Nat.add deg1 1) cC sC m0 m1) fun n0 ↦
  midPSeqCIVList (midPZipRotAdd (Nat.add deg1 1) cC sC m0 m1) fun n1 ↦ k n0 n1
/-- Lockstep column-wise degree-`2` Dicke step across `(r0, r1, r2)` (`len = deg1 + 1`). -/
def midPDicke2Cols : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal →
      List WDCVal × List WDCVal × List WDCVal
  | 0, _, _, _, _, _ => ([], [], [])
  | n + 1, c2, s2, r0, r1, r2 => midPUnconsC r0 fun a r0Tl ↦ midPUnconsC r1 fun b r1Tl ↦
      midPUnconsC r2 fun d r2Tl ↦
      midPSeqCIV (midPFastCSub (midPFastCRMul c2 a) (midPFastCRMul s2 b)) fun m00 ↦
      midPSeqCIV (midPFastCAdd (midPFastCRMul s2 a) (midPFastCRMul c2 b)) fun m01 ↦
      midPSeqCIV (midPFastCSub (midPFastCRMul c2 b) (midPFastCRMul s2 d)) fun m10 ↦
      midPSeqCIV (midPFastCAdd (midPFastCRMul s2 b) (midPFastCRMul c2 d)) fun m11 ↦
      midPSeqCIV (midPFastCSub (midPFastCRMul c2 m00) (midPFastCRMul s2 m10)) fun y0 ↦
      midPSeqCIV (midPFastCSub (midPFastCRMul c2 m01) (midPFastCRMul s2 m11)) fun y1 ↦
      midPSeqCIV (midPFastCAdd (midPFastCRMul s2 m01) (midPFastCRMul c2 m11)) fun y2 ↦
      match midPDicke2Cols n c2 s2 r0Tl r1Tl r2Tl with
      | (t0, t1, t2) => (y0 :: t0, y1 :: t1, y2 :: t2)
/-- CPS `TwoPair` `[2, 2, 1 ^ {r - 4}]` `3 × (r - 3)` step (`r ≥ 4`). -/
def midPFastStepTwoPairCPS {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal)
    (c1 s1 c2 s2 : WDIVal) (tp0 tp1 tp2 : List WDCVal)
    (k : List WDCVal → List WDCVal → List WDCVal → α) : α :=
  midPSeqCIVList (midPFastDamp2Row0 deg1 gIVs tp0) fun d0 ↦
  midPSeqCIVList (midPFastDamp2Row1 deg1 gIVs tp1) fun d1 ↦
  midPSeqCIVList (midPFastDamp2Row1 deg1 gIVs.tail tp2) fun d2 ↦
  midPSeqCIVList (midPFastDickeStepVec deg1 c1 s1 d0) fun m0 ↦
  midPSeqCIVList (midPFastDickeStepVec deg1 c1 s1 d1) fun m1 ↦
  midPSeqCIVList (midPFastDickeStepVec deg1 c1 s1 d2) fun m2 ↦
  match midPDicke2Cols (Nat.add deg1 1) c2 s2 m0 m1 m2 with
  | (c0, c1', c2') => midPSeqCIVList c0 fun n0 ↦ midPSeqCIVList c1' fun n1 ↦
      midPSeqCIVList c2' fun n2 ↦ k n0 n1 n2
/-- Evaluates one `MidPPhaseSpec` into its forced `WDCVal` enclosure. -/
def evalMidPPhaseIV (ph : MidPPhaseSpec) : Option WDCVal :=
  if 0 < ph.gd ∧ ph.ga ^ 2 + ph.gb ^ 2 = (ph.gd : ℤ) ^ 2 then
    midPSeqCIV (wdCGaussRat ph.ga ph.gb ph.gd) some
  else none
/-- Evaluates a `List MidPPhaseSpec` into a forced `List WDCVal`. -/
def evalMidPPhasesIV : List MidPPhaseSpec → Option (List WDCVal)
  | [] => some []
  | ph :: rest =>
      match evalMidPPhaseIV ph, evalMidPPhasesIV rest with
      | some gIV, some tl => some (gIV :: tl)
      | _, _ => none
/-- Strictly forced state across `3 ≤ r ≤ 16` probes. -/
structure MidPProbeState where
  qExtraHi : ℤ
  qCollAddHi : ℤ
  uVec : List WDCVal
  sp0 : List WDCVal
  sp1 : List WDCVal
  st0 : List WDCVal
  st1 : List WDCVal
  tp0 : List WDCVal
  tp1 : List WDCVal
  tp2 : List WDCVal
  q10 : List WDCVal
  q11 : List WDCVal
  deriving DecidableEq, Repr
/-- Single-probe CPS WHNF-forced multi-collision transition (`3 ≤ r ≤ 16`). -/
def evalMidPProbeStep (r : ℕ) (includeRm3 : Bool) (p : MidPProbeSpec)
    (st : MidPProbeState) : Option MidPProbeState :=
  if p.phases.length = r ∧ 0 < p.daDen ∧ 0 < p.cDen ∧
      p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 = (p.cDen : ℤ) ^ 2 then
    match evalMidPPhasesIV p.phases with
    | none => none
    | some gIVs =>
        let daIV := wdRat (p.daNum : ℤ) p.daDen
        let dphi1 : WDIVal := (ghMaxZ 0 (Int.sub daIV.1 2), daIV.2)
        let dphi2 : WDIVal := midPFastMulIV dphi1 (midPSqrtRatioIv 2)
        let dphi3 : WDIVal := midPFastMulIV dphi1 (midPSqrtRatioIv 3)
        let dphi4 : WDIVal := midPFastMulIV dphi1 (midPSqrtRatioIv 4)
        let maxAng : ℤ := Int.mul 1024 midPScaleZ
        if midPBleZ 0 dphi1.1 && midPBleZ dphi4.2 maxAng then
          let cTop := wdRat p.cNum p.cDen
          midPSeqCIVList (midPFastDampU r gIVs cTop st.uVec) fun uD ↦
          let sHi := midPSumRangeZ (Nat.add r 1) fun w ↦
            Int.mul (Int.ofNat (ghBinom r w)) (wdCAbs2Hi (uD.getD w wdCZero))
          let qdaHi := wdDivCeil (Int.mul (Int.add daIV.2 4) wdPi4InvHi) (Int.mul 2 midPScaleZ)
          let stepQ := wdDivCeil (Int.mul sHi qdaHi) midPScaleZ
          midPSeqInt (Int.add st.qExtraHi stepQ) fun qExNext ↦
          midPSeqInt (Int.add st.qCollAddHi qdaHi) fun qCollNext ↦ midPTrigCPS dphi1 fun c1 s1 ↦
          midPTrigCPS dphi2 fun c2 s2 ↦ midPTrigCPS dphi3 fun c3 s3 ↦
          midPSeqCIVList (midPFastDickeStepVec r c1 s1 uD) fun uNext ↦
          midPFastStep2RowCPS (r - 2) gIVs c1 s1 c2 s2 st.sp0 st.sp1 fun sp0N sp1N ↦
          midPFastStep2RowCPS (r - 3) gIVs c1 s1 c3 s3 st.st0 st.st1 fun st0N st1N ↦
          if Nat.ble 4 r then
            midPFastStepTwoPairCPS (r - 4) gIVs c1 s1 c2 s2 st.tp0 st.tp1 st.tp2
              fun tp0N tp1N tp2N ↦
                if includeRm3 then
                  midPTrigCPS dphi4 fun c4 s4 ↦
                  midPFastStep2RowCPS (r - 4) gIVs c1 s1 c4 s4 st.q10 st.q11 fun q10N q11N ↦
                    some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N,
                      tp0N, tp1N, tp2N, q10N, q11N⟩
                else
                  some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N, tp0N, tp1N, tp2N, [], []⟩
          else some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N, [], [], [], [], []⟩
        else none
  else none
/-- Multi-probe CPS WHNF-forced chain evaluator (`3 ≤ r ≤ 16`). -/
def evalMidPProbes (r : ℕ) (includeRm3 : Bool) :
    List MidPProbeSpec → MidPProbeState → Option MidPProbeState
  | [], st => some st
  | p :: rest, st =>
      match evalMidPProbeStep r includeRm3 p st with
      | none => none
      | some st' => evalMidPProbes r includeRm3 rest st'
/-- Collapses a `2`-row `[c, 1 ^ {deg1}]` state into total-click weights `0.. r`. -/
def midPCollapse2RowWt (deg1 r : ℕ) (r0 r1 : List WDCVal) : List ℤ :=
  midPSeqZList (r0.map wdCAbs2Hi) fun a0 ↦ midPSeqZList (r1.map wdCAbs2Hi) fun a1 ↦
    (List.range (Nat.add r 1)).map fun wt ↦
      let t0 : ℤ :=
        if Nat.ble wt deg1 then Int.mul (Int.ofNat (ghBinom deg1 wt)) (a0.getD wt 0) else 0
      let t1 : ℤ :=
        if Nat.ble 1 wt && Nat.ble (wt - 1) deg1 then
          Int.mul (Int.ofNat (ghBinom deg1 (wt - 1))) (a1.getD (wt - 1) 0)
        else 0
      midPForceInt (Int.add t0 t1)
/-- Collapses a `3`-row `TwoPair` `[2, 2, 1 ^ {deg1}]` state into total-click weights `0..
  r`. -/
def midPCollapseTwoPairWt (deg1 r : ℕ) (tp0 tp1 tp2 : List WDCVal) : List ℤ :=
  midPSeqZList (tp0.map wdCAbs2Hi) fun a0 ↦ midPSeqZList (tp1.map wdCAbs2Hi) fun a1 ↦
  midPSeqZList (tp2.map wdCAbs2Hi) fun a2 ↦
    (List.range (Nat.add r 1)).map fun wt ↦
      let t0 : ℤ :=
        if Nat.ble wt deg1 then Int.mul (Int.ofNat (ghBinom deg1 wt)) (a0.getD wt 0) else 0
      let t1 : ℤ :=
        if Nat.ble 1 wt && Nat.ble (wt - 1) deg1 then
          Int.mul (Int.ofNat (2 * ghBinom deg1 (wt - 1))) (a1.getD (wt - 1) 0)
        else 0
      let t2 : ℤ :=
        if Nat.ble 2 wt && Nat.ble (wt - 2) deg1 then
          Int.mul (Int.ofNat (ghBinom deg1 (wt - 2))) (a2.getD (wt - 2) 0)
        else 0
      midPForceInt (Int.add (Int.add t0 t1) t2)
/-- Evaluates one `(m, r)` schedule row into its forced `MidPSummary` (`3 ≤ r ≤ 16`). -/
def evalMidPRowSummary (m r : ℕ) (includeRm3 : Bool) (spec : MidPRowSpec) : Option MidPSummary :=
  let p := Stage2CertInternals.gridExp m
  if 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ 2 ≤ p ∧ p ≤ 10 ∧ m = 2 ^ p ∧ 0 < spec.a0Den ∧ 0 < spec.kzDen then
    let a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
    let phi01 : WDIVal := (ghMaxZ 0 (Int.sub a0IV.1 1), Int.add a0IV.2 1)
    let phi02 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 2)
    let phi03 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 3)
    let phi04 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 4)
    let maxAng : ℤ := Int.mul 1024 midPScaleZ
    if midPBleZ 0 phi01.1 && midPBleZ phi04.2 maxAng then
      midPTrigCPS phi01 fun c01 s01 ↦ midPTrigCPS phi02 fun c02 s02 ↦
      midPTrigCPS phi03 fun c03 s03 ↦
      midPSeqCIVList (midPFastDickeStepVec r c01 s01 (midPOneHot0 (Nat.add r 1))) fun u0 ↦
      midPSeqCIVList (midPFastDickeStepVec (r - 2) c01 s01 (midPOneHot0 (r - 1))) fun uRm2 ↦
      midPSeqCIVList (uRm2.map (midPFastCRMul c02)) fun sp0Init ↦
      midPSeqCIVList (uRm2.map (midPFastCRMul s02)) fun sp1Init ↦
      midPSeqCIVList (midPFastDickeStepVec (r - 3) c01 s01 (midPOneHot0 (r - 2))) fun uRm3 ↦
      midPSeqCIVList (uRm3.map (midPFastCRMul c03)) fun st0Init ↦
      midPSeqCIVList (uRm3.map (midPFastCRMul s03)) fun st1Init ↦
      let runChain (tp0I tp1I tp2I q10I q11I : List WDCVal) : Option MidPSummary :=
        let stInit : MidPProbeState :=
          ⟨0, 0, u0, sp0Init, sp1Init, st0Init, st1Init, tp0I, tp1I, tp2I, q10I, q11I⟩
        match evalMidPProbes r includeRm3 spec.probes stInit with
        | none => none
        | some fin =>
            let q0Hi := wdDivCeil (Int.mul (Int.add a0IV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
            let qDistHi := Int.add q0Hi fin.qExtraHi
            let qCollHi := Int.add q0Hi fin.qCollAddHi
            let kzIV := wdRat (spec.kzNum : ℤ) spec.kzDen
            let azIV : WDIVal := (ghMaxZ 0 (Int.sub kzIV.1 1), Int.add kzIV.2 1)
            if midPBleZ 0 azIV.1 && midPBleZ azIV.2 maxAng then
              midPTrigCPS azIV fun _ sAz ↦
              let zHitLo := (ghSqIV sAz).1
              let qzSub := wdDivCeil (Int.mul (Int.add kzIV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
              let uScale := midPUnpaddedZoomScaleHi15 (r - 1) m
              let qZoomHi := wdDivCeil (Int.mul qzSub uScale) midPScaleZ
              if midPBleZ 0 zHitLo && midPBleZ zHitLo midPScaleZ &&
                  midPBleZ (Int.add qCollHi qZoomHi) (Int.mul 12 midPScaleZ) then
                midPSeqInt qDistHi fun qdF ↦ midPSeqInt qCollHi fun qcF ↦
                midPSeqInt qZoomHi fun qzF ↦ midPSeqInt zHitLo fun zhF ↦
                midPSeqZList (fin.uVec.map wdCAbs2Hi) fun uAbs ↦
                midPSeqZList (fin.sp0.map wdCAbs2Hi) fun z0Abs ↦
                midPSeqZList (fin.sp1.map wdCAbs2Hi) fun z1Abs ↦
                let tpWt :=
                  if Nat.ble 4 r then midPCollapseTwoPairWt (r - 4) r fin.tp0 fin.tp1 fin.tp2
                  else List.replicate (Nat.add r 1) 0
                let stWt := midPCollapse2RowWt (r - 3) r fin.st0 fin.st1
                let q1Wt :=
                  if Nat.ble 4 r && includeRm3 then midPCollapse2RowWt (r - 4) r fin.q10 fin.q11
                  else List.replicate (Nat.add r 1) 0
                midPSeqZList tpWt fun tpF ↦ midPSeqZList stWt fun stF ↦ midPSeqZList q1Wt fun q1F ↦
                  some ⟨qdF, qcF, qzF, zhF, uAbs, z0Abs, z1Abs, tpF, stF, q1F⟩
              else none
            else none
      if Nat.ble 4 r then
        midPSeqCIVList (midPFastDickeStepVec (r - 4) c01 s01 (midPOneHot0 (r - 3))) fun uRm4 ↦
        midPSeqCIVList (midPFastDickeStepVec 2 c02 s02 (midPOneHot0 3)) fun uP2 ↦
        let p20 := uP2.getD 0 wdCZero
        let p21 := uP2.getD 1 wdCZero
        let p22 := uP2.getD 2 wdCZero
        midPSeqCIVList (uRm4.map (midPFastCMul p20)) fun tp0I ↦
        midPSeqCIVList (uRm4.map (midPFastCMul p21)) fun tp1I ↦
        midPSeqCIVList (uRm4.map (midPFastCMul p22)) fun tp2I ↦
        if includeRm3 then
          midPTrigCPS phi04 fun c04 s04 ↦ midPSeqCIVList (uRm4.map (midPFastCRMul c04)) fun q10I ↦
          midPSeqCIVList (uRm4.map (midPFastCRMul s04)) fun q11I ↦ runChain tp0I tp1I tp2I q10I q11I
        else runChain tp0I tp1I tp2I [] []
      else runChain [] [] [] [] []
    else none
  else none
/-- Alias with `includeRm3`-first parameter order. -/
abbrev evalGHMidPRowSummary (includeRm3 : Bool) (m r : ℕ) (spec : GHMidPRowSpec) :
    Option GHMidPSummary :=
  evalMidPRowSummary m r includeRm3 spec
/-- Scalar `O(r)` Bellman step contracting `vNext` via precomputed `MidPSummary`. -/
def evalMidPStepFromSummary (m r : ℕ) (includeRm3 : Bool) (s : MidPSummary)
    (vNext : List ℕ) : Option ℕ :=
  if 4 ≤ m ∧ 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ r < vNext.length then
    if midPBleZ 0 s.zHitLo && midPBleZ s.zHitLo midPScaleZ &&
        midPBleZ (Int.add s.qCollHi s.qZoomHi) (Int.mul 12 midPScaleZ) then
      let fHi (u : ℕ) : ℤ := Int.mul (Int.ofNat (vNext.getD u 0)) 1000000
      let remMiss1 : ℤ := Int.add s.qZoomHi (fHi 1)
      let remHit1 : ℤ :=
        Int.add s.qZoomHi (wdDivCeil (Int.mul (Int.sub midPScaleZ s.zHitLo) (fHi 1)) midPScaleZ)
      let remDist : ℤ := midPSumRangeZ r fun w ↦
        let cNext := if w + 1 == r then remMiss1 else fHi (r - w)
        wdDivCeil (Int.mul (Int.mul (Int.ofNat (ghBinom r w)) (s.uAbs2Hi.getD w 0)) cNext)
          midPScaleZ
      let remSp0 : ℤ := midPSumRangeZ (r - 1) fun w1 ↦
        wdDivCeil (Int.mul (Int.mul (Int.ofNat (ghBinom (r - 2) w1)) (s.z0Abs2Hi.getD w1 0))
            (fHi (r - w1)))
          midPScaleZ
      let remSp1 : ℤ := midPSumRangeZ (r - 1) fun w1 ↦
        let cNext := if w1 + 2 == r then remHit1 else fHi (r - 1 - w1)
        wdDivCeil (Int.mul (Int.mul (Int.ofNat (ghBinom (r - 2) w1)) (s.z1Abs2Hi.getD w1 0)) cNext)
          midPScaleZ
      let remTp : ℤ :=
        if Nat.ble 4 r then
          midPSumRangeZ (r - 1) fun wt ↦
            wdDivCeil (Int.mul (s.tpWtHi.getD wt 0) (fHi (r - wt))) midPScaleZ
        else 0
      let remSt : ℤ := midPSumRangeZ (r - 1) fun wt ↦
        wdDivCeil (Int.mul (s.stWtHi.getD wt 0) (fHi (r - wt))) midPScaleZ
      let remSq : ℤ :=
        if Nat.ble 4 r && includeRm3 then
          midPSumRangeZ (r - 2) fun wt ↦
            wdDivCeil (Int.mul (s.q1WtHi.getD wt 0) (fHi (r - wt))) midPScaleZ
        else 0
      let mPow : ℤ := Int.ofNat (m ^ r)
      let nInj : ℤ := if Nat.ble r m then Int.ofNat (midPDescFact m r) else 0
      let nSp : ℤ := Int.ofNat (ghBinom r 2 * midPDescFact m (r - 1))
      let nTp : ℤ := if Nat.ble 4 r then Int.ofNat (3 * ghBinom r 4 * midPDescFact m (r - 2)) else 0
      let nSt : ℤ := Int.ofNat (ghBinom r 3 * midPDescFact m (r - 2))
      let nSq : ℤ :=
        if Nat.ble 4 r && includeRm3 then Int.ofNat (ghBinom r 4 * midPDescFact m (r - 3)) else 0
      let used : ℤ := Int.add (Int.add (Int.add (Int.add nInj nSp) nTp) nSt) nSq
      let nRem : ℤ := Int.sub mPow used
      if midPBleZ 0 nRem then
        let tInj := Int.mul nInj (Int.add s.qDistHi remDist)
        let tSp := Int.mul nSp (Int.add s.qCollHi (Int.add remSp0 remSp1))
        let tTp := Int.mul nTp (Int.add s.qCollHi remTp)
        let tSt := Int.mul nSt (Int.add s.qCollHi remSt)
        let tSq := Int.mul nSq (Int.add s.qCollHi remSq)
        let tRem := Int.mul nRem (Int.add s.qCollHi (fHi r))
        let tot := Int.add (Int.add (Int.add (Int.add (Int.add tInj tSp) tTp) tSt) tSq) tRem
        let outZ := wdDivCeil tot (Int.mul mPow 1000000)
        if midPBleZ 0 outZ then some outZ.toNat else none
      else none
    else none
  else none
/-- Alias with `includeRm3`-first parameter order. -/
abbrev evalGHMidPStepFromSummary (includeRm3 : Bool) (m r : ℕ) (s : GHMidPSummary)
    (vNext : List ℕ) : Option ℕ :=
  evalMidPStepFromSummary m r includeRm3 s vNext
/- ## 5. Spine, Row-Slice, Pass-Slice, & Cell-Ratio Checkers -/
/-- Evaluates a contiguous list of `(m, r)` row schedules starting at `rCur`. -/
def evalMidPRowSummaries (includeRm3 : Bool) (m : ℕ) :
    ℕ → List GHMidPRowSpec → Option (List GHMidPSummary)
  | _, [] => some []
  | rCur, spec :: rest =>
      match evalMidPRowSummary m rCur includeRm3 spec,
          evalMidPRowSummaries includeRm3 m (Nat.add rCur 1) rest with
      | some s, some tl => some (s :: tl)
      | _, _ => none
/-- Checks one stationary Bellman pass across `r = 0.. kMax` from `(s2, sMidP)`. -/
def checkGHMidPPassSummaries (includeRm3 : Bool) (m kMax : ℕ) (s2 : GHZoomSummary)
    (sMidP : List GHMidPSummary) (vCur vNext : List ℕ) : Bool :=
  (vCur.getD 0 0 == 0) &&
    (List.range kMax).all (fun u ↦ Nat.ble (vCur.getD u 0) (vCur.getD (u + 1) 0)) &&
    Nat.ble (vNext.getD 1 0) (vCur.getD 1 0) &&
    (match evalGHZoomStepFromSummary m s2 vNext with
      | some hi2 => Nat.ble hi2 (vCur.getD 2 0)
      | none => false) &&
    (List.range (kMax - 2)).all (fun j ↦
      match evalMidPStepFromSummary m (j + 3) includeRm3
          (sMidP.getD j midPEmptySummary) vNext with
      | some hir => Nat.ble hir (vCur.getD (j + 3) 0)
      | none => false)
/-- Checks a contiguous slice of Bellman passes `[pStart.. pStart + pCount - 1]`. -/
def checkGHMidPPassesSlice (includeRm3 : Bool) (m kMax : ℕ) (s2 : GHZoomSummary)
    (sMidP : List GHMidPSummary) (vSeq : List (List ℕ)) (pStart pCount : ℕ) : Bool :=
  (List.range pCount).all fun off ↦
    let i := pStart + off
    checkGHMidPPassSummaries includeRm3 m kMax s2 sMidP (vSeq.getD i []) (vSeq.getD (i + 1) [])
/-- Evaluates all summaries on an `m`-spine `r = 2.. kMax` once and checks `W` Bellman
  passes. -/
def checkGHMidPSpine (includeRm3 : Bool) (m kMax W : ℕ) (row2 : GHZoomRowSpec)
    (rowsMidP : List GHMidPRowSpec) (vSeq : List (List ℕ)) : Bool :=
  if hgm : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10 then
    match evalGHZoomRowSummary m row2, evalMidPRowSummaries includeRm3 m 3 rowsMidP with
    | some s2Raw, some sMidP =>
        midPForceZoomSummary s2Raw fun s2 ↦
          let p := Stage2CertInternals.gridExp m
          let pIdx : Fin 10 := ⟨p - 1, by omega⟩
          let vLast := vSeq.getD W []
          decide (4 ≤ m ∧ m = 2 ^ p ∧ 4 ≤ kMax ∧ kMax ≤ 16 ∧ W ≤ 16 ∧
              vSeq.length = W + 1 ∧ rowsMidP.length + 2 = kMax) && (vLast.getD 0 0 == 0) &&
            (List.range kMax).all (fun u ↦ Nat.ble (vLast.getD u 0) (vLast.getD (u + 1) 0)) &&
            (List.range (kMax + 1)).all (fun r ↦
              Nat.ble (Stage2CertInternals.potWInt pIdx r) (vLast.getD r 0)) &&
            (List.range W).all (fun i ↦
              checkGHMidPPassSummaries includeRm3 m kMax s2 sMidP
                (vSeq.getD i []) (vSeq.getD (i + 1) []))
    | _, _ => false
  else false
/-- Checks the `m`-spine header, terminal potential bounds, and `r = 2` Bellman pass bounds. -/
def checkGHMidPSpineHeaderAndR2 (m kMax W rowsLen : ℕ) (row2 : GHZoomRowSpec)
    (vSeq : List (List ℕ)) : Bool :=
  if hgm : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10 then
    match evalGHZoomRowSummary m row2 with
    | none => false
    | some s2Raw =>
        midPForceZoomSummary s2Raw fun s2 ↦
          let p := Stage2CertInternals.gridExp m
          let pIdx : Fin 10 := ⟨p - 1, by omega⟩
          let vLast := vSeq.getD W []
          decide (4 ≤ m ∧ m = 2 ^ p ∧ 4 ≤ kMax ∧ kMax ≤ 16 ∧ W ≤ 16 ∧
              vSeq.length = W + 1 ∧ rowsLen + 2 = kMax) && (vLast.getD 0 0 == 0) &&
            (List.range kMax).all (fun u ↦ Nat.ble (vLast.getD u 0) (vLast.getD (u + 1) 0)) &&
            (List.range (kMax + 1)).all (fun r ↦
              Nat.ble (Stage2CertInternals.potWInt pIdx r) (vLast.getD r 0)) &&
            (List.range W).all (fun i ↦
              let vCur := vSeq.getD i []
              let vNext := vSeq.getD (i + 1) []
              (vCur.getD 0 0 == 0) &&
                (List.range kMax).all (fun u ↦ Nat.ble (vCur.getD u 0) (vCur.getD (u + 1) 0)) &&
                Nat.ble (vNext.getD 1 0) (vCur.getD 1 0) &&
                (match evalGHZoomStepFromSummary m s2 vNext with
                  | some hi2 => Nat.ble hi2 (vCur.getD 2 0)
                  | none => false))
  else false
/-- Checks `W` Bellman passes across a contiguous slice of `3 ≤ r ≤ 16` rows starting at
  `rCur`. -/
def checkGHMidPRowsSlice (includeRm3 : Bool) (m W : ℕ) (vSeq : List (List ℕ)) :
    ℕ → List GHMidPRowSpec → Bool
  | _, [] => true
  | rCur, spec :: rest =>
      match evalMidPRowSummary m rCur includeRm3 spec with
      | none => false
      | some s =>
          (List.range W).all (fun i ↦
            match evalMidPStepFromSummary m rCur includeRm3 s (vSeq.getD (i + 1) []) with
            | some hir => Nat.ble hir ((vSeq.getD i []).getD rCur 0)
            | none => false) &&
            checkGHMidPRowsSlice includeRm3 m W vSeq (Nat.add rCur 1) rest
/-- Concatenates two certified contiguous `checkGHMidPRowsSlice` blocks. -/
theorem checkGHMidPRowsSlice_append (includeRm3 : Bool) (m W : ℕ) (vSeq : List (List ℕ)) :
    ∀ (rCur : ℕ) (xs ys : List GHMidPRowSpec),
      checkGHMidPRowsSlice includeRm3 m W vSeq rCur xs = true →
      checkGHMidPRowsSlice includeRm3 m W vSeq (rCur + xs.length) ys = true →
      checkGHMidPRowsSlice includeRm3 m W vSeq rCur (xs ++ ys) = true
  | rCur, [], _, _, hy => by
      have hr0 : rCur + ([] : List GHMidPRowSpec).length = rCur := Nat.add_zero rCur; rw [hr0] at hy
      rw [List.nil_append]; exact hy
  | rCur, spec :: rest, ys, hx, hy => by
      simp only [List.cons_append, checkGHMidPRowsSlice] at hx ⊢
      cases hs : evalMidPRowSummary m rCur includeRm3 spec with
      | none => rw [hs] at hx; cases hx
      | some s =>
          rw [hs] at hx; simp only [Bool.and_eq_true] at hx ⊢; refine ⟨hx.1, ?_⟩
          have hr1 : Nat.add rCur 1 = rCur + 1 := rfl; rw [hr1] at hx ⊢; have hy' :
              checkGHMidPRowsSlice includeRm3 m W vSeq ((rCur + 1) + rest.length) ys = true := by
            have heq : (rCur + 1) + rest.length = rCur + (spec :: rest).length := by
              simp only [List.length_cons]; omega
            rwa [heq]
          exact checkGHMidPRowsSlice_append includeRm3 m W vSeq (rCur + 1) rest ys hx.2 hy'
lemma checkGHMidPRowsSlice_sound (includeRm3 : Bool) (m W : ℕ) (vSeq : List (List ℕ)) :
    ∀ (rCur : ℕ) (specs : List GHMidPRowSpec),
      checkGHMidPRowsSlice includeRm3 m W vSeq rCur specs = true →
      ∃ sums : List GHMidPSummary, evalMidPRowSummaries includeRm3 m rCur specs = some sums ∧
        ∀ i < W, ∀ j < specs.length,
          (match evalMidPStepFromSummary m (rCur + j) includeRm3
              (sums.getD j midPEmptySummary) (vSeq.getD (i + 1) []) with
            | some hir => Nat.ble hir ((vSeq.getD i []).getD (rCur + j) 0)
            | none => false) = true
  | _, [], _ => ⟨[], rfl, fun _ _ _ hj ↦ by simp at hj⟩
  | rCur, spec :: rest, hok => by
      simp only [checkGHMidPRowsSlice] at hok
      cases hs : evalMidPRowSummary m rCur includeRm3 spec with
      | none => rw [hs] at hok; cases hok
      | some s =>
          rw [hs] at hok; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
          have hr1 : Nat.add rCur 1 = rCur + 1 := rfl; rw [hr1] at hok; obtain ⟨tl, htl, hstep⟩ :=
            checkGHMidPRowsSlice_sound includeRm3 m W vSeq (rCur + 1) rest hok.2
          refine ⟨s :: tl, ?_, fun i hi j hj ↦ ?_⟩
          · simp only [evalMidPRowSummaries, hr1, hs, htl]
          · cases j with
            | zero => simp only [Nat.add_zero, List.getD_cons_zero]; exact hok.1 i hi
            | succ j' =>
                have hj' : j' < rest.length := by simp only [List.length_cons] at hj; omega
                have hadd : rCur + (j' + 1) = (rCur + 1) + j' := by omega
                simp only [hadd, List.getD_cons_succ]; exact hstep i hi j' hj'
/-- Certifies `checkGHMidPSpine` from `checkGHMidPSpineHeaderAndR2` and
  `checkGHMidPRowsSlice`. -/
theorem checkGHMidPSpine_of_slices {includeRm3 : Bool} {m kMax W : ℕ} {row2 : GHZoomRowSpec}
    {rowsMidP : List GHMidPRowSpec} {vSeq : List (List ℕ)}
    (hhdr : checkGHMidPSpineHeaderAndR2 m kMax W rowsMidP.length row2 vSeq = true)
    (hrows : checkGHMidPRowsSlice includeRm3 m W vSeq 3 rowsMidP = true) :
    checkGHMidPSpine includeRm3 m kMax W row2 rowsMidP vSeq = true := by
  unfold checkGHMidPSpineHeaderAndR2 at hhdr; unfold checkGHMidPSpine
  by_cases hgm : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10
  · rw [dite_eq_left hgm] at hhdr ⊢
    have h_opt2 : ∃ s2Raw, evalGHZoomRowSummary m row2 = some s2Raw := by
      cases hs2 : evalGHZoomRowSummary m row2 with
      | none => rw [hs2] at hhdr; cases hhdr
      | some s2Raw => exact ⟨s2Raw, rfl⟩
    obtain ⟨s2Raw, hs2⟩ := h_opt2
    obtain ⟨sMidP, hsMidP, hstep⟩ := checkGHMidPRowsSlice_sound includeRm3 m W vSeq 3 rowsMidP hrows
    rw [hs2] at hhdr; rw [hs2, hsMidP]; dsimp only at hhdr ⊢; rw [midPForceZoomSummary_eq] at hhdr ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hhdr ⊢
    rcases hhdr with ⟨⟨⟨⟨hh0, hh1⟩, hh2⟩, hh3⟩, hhPasses⟩
    refine ⟨⟨⟨⟨hh0, hh1⟩, hh2⟩, hh3⟩, fun i hi ↦ ?_⟩; have hp := hhPasses i hi
    unfold checkGHMidPPassSummaries
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp ⊢
    refine ⟨hp, fun j hj ↦ ?_⟩; rcases of_decide_eq_true hh0 with ⟨_, _, _, _, _, _, hlen⟩
    have hj_len : j < rowsMidP.length := by omega
    have h3j : 3 + j = j + 3 := by omega
    have hsj := hstep i hi j hj_len; rwa [h3j] at hsj
  · rw [dite_eq_right hgm] at hhdr; cases hhdr
/-- Fast cell-ratio check `1 ≤ den ∧ den * ((vSeq.getD 0 []).getD k 0 + 1) ≤ num *
  treeSum(k)`. -/
def checkGHMidPCellRatio (k : ℕ) (vSeq : List (List ℕ)) (num den : ℕ) : Bool :=
  Nat.ble 1 den && Nat.ble (den * ((vSeq.getD 0 []).getD k 0 + 1))
      (num * Stage2CertInternals.treeSum (Stage2CertInternals.gridExp k) 0
        (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1)))

private theorem _ord_gme : True :=
  (And.intro (Eq.refl QuantumComputation.Specs.DickeSol.rkmValidHi_m1024) trivial).right

end
end QuantumComputation.Specs.DickeSol
end GHMidPZoomEval
