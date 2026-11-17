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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistBasis2L
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLQHL
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistOverlap2L
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylL2BallCertDefs
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.LongTailM1K2Only
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.MultiTapStage2AGL1QHL
/-
# `m = 1` `H_dist(2 <= L <= 50)` CertDefs, QHL & `k in {4, 8, 16, 32}` Router
-/
section Sec_SchurWeylL2BallM1L50CertDefs
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
namespace SchurWeylLCert
open scoped BigOperators

/- ## 1. Pure-GMP Kernel Forcing & Arithmetic Helpers -/
theorem int_add_eq (a b : ℤ) : Int.add a b = a + b := rfl
theorem int_sub_eq (a b : ℤ) : Int.sub a b = a - b := rfl
theorem int_mul_eq (a b : ℤ) : Int.mul a b = a * b := rfl
theorem int_ediv_eq (a b : ℤ) : Int.ediv a b = a / b := rfl
theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
theorem swLNatBle_eq_decide : ∀ (a b : ℕ), Nat.ble a b = decide (a ≤ b)
  | 0, _ => rfl | _ + 1, 0 => rfl
  | a + 1, b + 1 => by simp only [Nat.ble, swLNatBle_eq_decide a b, Nat.add_le_add_iff_right]
theorem kpNatBle_one_eq_pos (a : ℕ) : Nat.ble 1 a = decide (0 < a) := by
  rw [swLNatBle_eq_decide]; by_cases h : 0 < a
  · have h1 : 1 ≤ a := (by omega); simp [h, h1]
  · have h1 : ¬(1 ≤ a) := (by omega); simp [h, h1]
theorem swLNatBeq_eq_decide : ∀ (a b : ℕ), Nat.beq a b = decide (a = b)
  | 0, 0 => rfl | 0, _ + 1 => rfl | _ + 1, 0 => rfl
  | a + 1, b + 1 => (swLNatBeq_eq_decide a b).trans (by simp)
theorem swLNatBeq_eq_beq (a b : ℕ) : Nat.beq a b = (a == b) := by
  rw [swLNatBeq_eq_decide, Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
/-- Pure-GMP WHNF-forcing `ℕ` wrapper (`@Nat.casesOn` binds bare `Literal.natVal`). -/
def kpForceNat {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  @Nat.casesOn (fun _ ↦ α) (Nat.add 1 x) (k 0) k
theorem kpForceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) : kpForceNat x k = k x := by
  unfold kpForceNat; rw [nat_add_eq, Nat.one_add]
/-- Pure-GMP WHNF-forcing `ℤ` wrapper (`0` `HAdd.hAdd`, `0` `Nat.succ`, `0` thunks). -/
def kpForceInt {α : Type} (x : ℤ) (k : ℤ → α) : α :=
  Int.casesOn x (fun n ↦ kpForceNat n fun v ↦ k (Int.ofNat v))
    (fun n ↦ kpForceNat n fun v ↦ k (Int.negSucc v))
theorem kpForceInt_eq {α : Type} (x : ℤ) (k : ℤ → α) : kpForceInt x k = k x := by
  cases x with
  | ofNat n => exact kpForceNat_eq n fun v ↦ k (Int.ofNat v)
  | negSucc n => exact kpForceNat_eq n fun v ↦ k (Int.negSucc v)
/-- Single-eval WHNF-forcing `IvInt` wrapper (`match` evaluates `iv` once). -/
def kpForceIv {α : Type} (iv : IvInt) (k : IvInt → α) : α :=
  match iv with
  | (x, y) => kpForceInt x fun a ↦ kpForceInt y fun b ↦ k (a, b)
theorem kpForceIv_eq {α : Type} (iv : IvInt) (k : IvInt → α) : kpForceIv iv k = k iv := by
  rcases iv with ⟨x, y⟩; simp only [kpForceIv, kpForceInt_eq]
/-- Single-eval WHNF-forcing `IvInt × IvInt` wrapper. -/
def kpForcePair {α : Type} (p : IvInt × IvInt) (k : IvInt × IvInt → α) : α :=
  match p with
  | (u, v) => kpForceIv u fun a ↦ kpForceIv v fun b ↦ k (a, b)
theorem kpForcePair_eq {α : Type} (p : IvInt × IvInt) (k : IvInt × IvInt → α) : kpForcePair p k = k
  p := by rcases p with ⟨u, v⟩; simp only [kpForcePair, kpForceIv_eq]
/-- Strict `O(N)` spine-and-element pure-GMP WHNF forcing for `List ℤ`. -/
def kpForceIntList : List ℤ → List ℤ
  | [] => []
  | x :: xs =>
      kpForceInt x fun x' ↦
        match kpForceIntList xs with
        | [] => [x']
        | hd :: tl => x' :: hd :: tl
theorem kpForceIntList_eq : ∀ (xs : List ℤ), kpForceIntList xs = xs
  | [] => rfl
  | x :: xs => by unfold kpForceIntList; rw [kpForceInt_eq, kpForceIntList_eq xs]; cases xs <;> rfl
/-- Continuation wrapper strictly forcing a `List ℤ`. -/
def kpWithIntList {α : Type} (xs : List ℤ) (k : List ℤ → α) : α :=
  match kpForceIntList xs with
  | [] => k []
  | hd :: tl => k (hd :: tl)
theorem kpWithIntList_eq {α : Type} (xs : List ℤ) (k : List ℤ → α) : kpWithIntList xs k = k xs := by
  unfold kpWithIntList; rw [kpForceIntList_eq]; cases xs <;> rfl
/-- Strict `O(N)` spine-and-row pure-GMP WHNF forcing for `List SwLKRow`. -/
def kpForceGrid : List SwLKRow → List SwLKRow
  | [] => []
  | r :: rs =>
      kpWithIntList r fun r' ↦
        match kpForceGrid rs with
        | [] => [r']
        | hd :: tl => r' :: hd :: tl
theorem kpForceGrid_eq : ∀ (rs : List SwLKRow), kpForceGrid rs = rs
  | [] => rfl
  | r :: rs => by unfold kpForceGrid; rw [kpWithIntList_eq, kpForceGrid_eq rs]; cases rs <;> rfl
/-- Continuation wrapper strictly forcing a `List SwLKRow`. -/
def kpWithGrid {α : Type} (rs : List SwLKRow) (k : List SwLKRow → α) : α :=
  match kpForceGrid rs with
  | [] => k []
  | hd :: tl => k (hd :: tl)
theorem kpWithGrid_eq {α : Type} (rs : List SwLKRow) (k : List SwLKRow → α) : kpWithGrid rs k = k rs
  := by unfold kpWithGrid; rw [kpForceGrid_eq]; cases rs <;> rfl
/-- Kernel-fast minimum on `ℕ` via primitive `Nat.ble`, avoiding `LinearOrder.toMin`. -/
def swLMinNat (a b : ℕ) : ℕ :=
  cond (Nat.ble a b) a b
theorem swLMinNat_eq (a b : ℕ) : swLMinNat a b = min a b := by
  unfold swLMinNat; rw [swLNatBle_eq_decide]; by_cases h : a ≤ b
  · simp [h]
  · rw [decide_eq_false h]; dsimp [cond]; omega
/-- Kernel-fast `a ≤ b` on `ℤ` via `Int.sub` constructor matching, avoiding `LinearOrder`. -/
def swLBleInt (a b : ℤ) : Bool :=
  match Int.sub b a with
  | Int.ofNat _ => true
  | Int.negSucc _ => false
theorem swLBleInt_eq_decide (a b : ℤ) : swLBleInt a b = decide (a ≤ b) := by
  unfold swLBleInt; rw [int_sub_eq]
  cases h : b - a with
  | ofNat n => have hab : a ≤ b := (by rw [Int.ofNat_eq_natCast] at h; omega); simp [hab]
  | negSucc n => have hab : ¬(a ≤ b) := (by rw [Int.negSucc_eq] at h; omega); simp [hab]
/-- Kernel-fast `a < b` on `ℤ` via `swLBleInt (Int.add a 1) b`. -/
def swLBltInt (a b : ℤ) : Bool :=
  swLBleInt (Int.add a (Int.ofNat 1)) b
theorem swLBltInt_eq_decide (a b : ℤ) : swLBltInt a b = decide (a < b) := by
  unfold swLBltInt; rw [swLBleInt_eq_decide, int_add_eq, Int.ofNat_eq_natCast, Bool.eq_iff_iff,
    decide_eq_true_eq, decide_eq_true_eq]; omega
/-- Kernel-fast integer squaring `x * x` avoiding `Monoid.toNatPow`. -/
def swLIntSq (x : ℤ) : ℤ :=
  Int.mul x x
theorem swLIntSq_eq (x : ℤ) : swLIntSq x = x ^ 2 := by unfold swLIntSq; rw [int_mul_eq]; ring
/-- Kernel-fast falling factorial `n * (n - 1) *... * (n - k + 1)` via pure-GMP
  `kpForceNat`. -/
def swLDescFactFast (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
      kpForceNat (swLDescFactFast n k) fun p ↦
        Nat.mul (Nat.sub n k) p
theorem swLDescFactFast_eq (n : ℕ) : ∀ k : ℕ, swLDescFactFast n k = n.descFactorial k
  | 0 => rfl
  | k + 1 => by
    unfold swLDescFactFast; rw [kpForceNat_eq, nat_mul_eq, nat_sub_eq, swLDescFactFast_eq n k,
      Nat.descFactorial_succ]
/-- Kernel-fast small binomial coefficient via `Nat.div` and `swLDescFactFast`. -/
def swLBinomSmallFast (n k : ℕ) : ℕ :=
  Nat.div (swLDescFactFast n k) (swLDescFactFast k k)
theorem swLBinomSmallFast_eq (n k : ℕ) : swLBinomSmallFast n k = swLBinomSmall n k := by
  unfold swLBinomSmallFast swLBinomSmall; rw [nat_div_eq, swLDescFactFast_eq, swLDescFactFast_eq]
/-- Kernel-fast integer numerator `k_j(u)` using pure-GMP `kpForceNat`/`kpForceInt` ops. -/
def swLKNumIntFast (L r : ℕ) (tailLbs : List ℤ) (j u : ℕ) : ℤ :=
  kpForceNat (Nat.sub r u) fun wJ ↦
    kpForceNat (swLDescFactFast wJ j) fun wJDesc ↦
      (List.range (Nat.sub (Nat.add L 1) j)).foldl (fun acc dC ↦
        kpForceNat (Nat.add j dC) fun c ↦
          kpForceNat
            (Nat.mul
              (Nat.mul
                (Nat.mul (swLBinomSmallFast (Nat.sub c 1) (Nat.sub j 1)) wJDesc)
                (swLDescFactFast u (Nat.sub c j)))
              (swLDescFactFast (Nat.sub r c) (Nat.sub L c))) fun comb ↦
            kpForceInt
              (Int.add acc
                (Int.mul (tailLbs.getD (Nat.sub c 1) (Int.ofNat 0)) (Int.ofNat comb)))
              id) (Int.ofNat 0)
theorem swLKNumIntFast_eq (L r : ℕ) (tailLbs : List ℤ) (j u : ℕ) : swLKNumIntFast L r tailLbs j u =
  swLKNumInt L r tailLbs j u := by
  unfold swLKNumIntFast swLKNumInt; simp only [kpForceNat_eq, kpForceInt_eq, withForcedNat_eq,
    id_eq, nat_sub_eq, nat_add_eq, nat_mul_eq, int_add_eq, int_mul_eq, Int.ofNat_eq_natCast,
    Nat.cast_zero, swLDescFactFast_eq, swLBinomSmallFast_eq]
/-- Kernel-fast row builder `[k_1,..., k_{min L s}]` at threshold `s`. -/
def swLKRowBuildFast (L r : ℕ) (tailLbs : List ℤ) (s : ℕ) : SwLKRow :=
  if Nat.beq s 0 then []
  else
    kpForceIntList
      ((List.range (swLMinNat L s)).map fun jIdx ↦
        kpForceNat (Nat.add jIdx 1) fun j ↦
          swLKNumIntFast L r tailLbs j (Nat.sub s j))
theorem swLKRowBuildFast_eq (L r : ℕ) (tailLbs : List ℤ) (s : ℕ) : swLKRowBuildFast L r tailLbs s =
  swLKRowBuild L r tailLbs s := by
  unfold swLKRowBuildFast swLKRowBuild; rw [swLNatBeq_eq_beq, kpForceIntList_eq, swLMinNat_eq]
  split_ifs
  · rfl
  · refine List.map_congr_left fun jIdx _ ↦ ?_; rw [kpForceNat_eq, nat_add_eq, nat_sub_eq,
      swLKNumIntFast_eq]

/- ## 2. Pure-GMP Sliding-Window Union-Tail & Bellman Evaluators -/
/-- Constructor-pattern-matched linear dot product accumulating `acc + ∑_i ks_i * ds_i`. -/
def swLDotLinear : List ℤ → List ℤ → ℤ → ℤ
  | [], _, acc => acc
  | _ :: _, [], acc => acc
  | k :: ks, d :: ds, acc =>
      kpForceInt (Int.add acc (Int.mul k d)) fun acc' ↦ swLDotLinear ks ds acc'
/-- Constructor-pattern-matched positive-index (`1 ≤ s ≤ curMax`) sliding-window DP step. -/
def swLStepPosFast (den : ℤ) : ℕ → List SwLKRow → List ℤ → ℤ → List ℤ → List ℤ
  | 0, _, _, _, _ => []
  | rem + 1, [], _, _, _ => List.replicate (Nat.add rem 1) (Int.ofNat 0)
  | rem + 1, row :: kRest, [], pPrev, winDiffs =>
      kpForceInt pPrev fun d0 ↦
        kpForceInt (swLDotLinear row (d0 :: winDiffs) (Int.ofNat 0)) fun num ↦
          kpForceInt (Int.ediv num den) fun v ↦
            v :: swLStepPosFast den rem kRest [] (Int.ofNat 0) (d0 :: winDiffs)
  | rem + 1, row :: kRest, pCur :: pRest, pPrev, winDiffs =>
      kpForceInt (Int.sub pPrev pCur) fun d0 ↦
        kpForceInt (swLDotLinear row (d0 :: winDiffs) (Int.mul den pCur)) fun num ↦
          kpForceInt (Int.ediv num den) fun v ↦
            v :: swLStepPosFast den rem kRest pRest pCur (d0 :: winDiffs)
/-- Linear `O(mCopies * min(mCopies * L, r) * L)` sliding-window union-tail lower-bound
  list,
  proved bit-for-bit equal to `swLUnionTailLbList` for all `(L, r, tailLbs, mCopies)`. -/
def swLUnionTailLbListFast (L r : ℕ) (tailLbs : List ℤ) (mCopies : ℕ) : List ℤ :=
  kpForceInt (Int.mul swScale (Int.ofNat (swLDescFactFast r L))) fun den ↦
    kpForceNat (swLMinNat (Nat.mul mCopies L) r) fun maxS ↦
      kpWithGrid
        ((List.range maxS).map fun idx ↦
          swLKRowBuildFast L r tailLbs (Nat.add idx 1)) fun kRowsPos ↦
        kpWithIntList
          ((List.range mCopies).foldl (fun prevPos tIdx ↦
            kpForceNat (swLMinNat (Nat.mul (Nat.add tIdx 1) L) maxS) fun curMax ↦
              kpForceIntList (swLStepPosFast den curMax kRowsPos prevPos swUnionScale [])) [])
          fun finalPos ↦
            kpForceIntList
              (swUnionScale ::
                (finalPos ++ List.replicate (Nat.sub r finalPos.length) (Int.ofNat 0)))
/-- Constructor-pattern-matched linear Abel summation over `tailPos = tailL.drop 1`. -/
def swLAbSumLoop (vTable : ℕ → ℤ) : ℕ → ℕ → List ℤ → ℤ → ℤ
  | 0, _, _, acc => acc
  | cnt + 1, curR, [], acc =>
      swLAbSumLoop vTable cnt (Nat.sub curR 1) [] acc
  | cnt + 1, curR, t :: ts, acc =>
      kpForceInt
        (Int.add acc (Int.mul t (Int.sub (vTable curR) (vTable (Nat.sub curR 1)))))
        fun acc' ↦ swLAbSumLoop vTable cnt (Nat.sub curR 1) ts acc'
/-- Linear-time `MultiSW_L` Bellman step checker proved bit-for-bit equal to
  `checkMultiSWLStep`. -/
def checkMultiSWLStepFast (L mEff r numPulses tauNum tauDen verCalls : ℕ)
    (tailLbs : List ℤ) (vScale : ℤ) (vTable : ℕ → ℤ) : Bool :=
  (Nat.ble 2 L && Nat.ble L 8 && Nat.ble 1 mEff && Nat.ble L r && Nat.ble r 1024 &&
    Nat.ble 1 numPulses && Nat.ble 1 tauNum && Nat.ble 1 tauDen &&
    swLBltInt (Int.ofNat 0) vScale && Nat.beq tailLbs.length L &&
    swLBleInt (Int.ofNat 0) (tailLbs.getD (Nat.sub L 1) (Int.ofNat 0)) &&
    swLBleInt (tailLbs.getD 0 (Int.ofNat 0)) swScale) &&
  ((List.range (Nat.sub L 1)).all fun i ↦
    swLBleInt (tailLbs.getD (Nat.add i 1) (Int.ofNat 0)) (tailLbs.getD i (Int.ofNat 0))) &&
  kpWithIntList (swLUnionTailLbListFast L r tailLbs mEff) fun tailL ↦
    let tailPos : List ℤ := match tailL with | [] => [] | _ :: ts => ts
    let t1 : ℤ := match tailPos with | [] => Int.ofNat 0 | x :: _ => x
    kpForceNat (swLMinNat (Nat.mul L mEff) r) fun maxS ↦
      kpForceInt (swLAbSumLoop vTable maxS r tailPos (Int.ofNat 0)) fun abSum ↦
        kpForceInt
          (Int.add (Int.mul (Int.ofNat 3) (Int.ofNat numPulses))
            (Int.mul (Int.ofNat 2) (Int.ofNat verCalls))) fun bNum ↦
          kpForceInt
            (Int.sub (Int.mul abSum swBden49)
              (Int.mul (Int.mul swUnionScale vScale) bNum)) fun rem ↦
            kpForceInt
              (swLIntSq
                (Int.mul
                  (Int.mul
                    (Int.mul (Int.mul (Int.ofNat numPulses) (Int.ofNat tauNum)) swUnionScale)
                    vScale)
                  swBden49)) fun lhsSq ↦
              kpForceInt
                (Int.mul
                  (Int.mul
                    (Int.mul (Int.ofNat 4) (swLIntSq (Int.ofNat tauDen)))
                    (Int.ofNat r))
                  (swLIntSq rem)) fun rhsSq ↦
                swLBltInt (Int.ofNat 0) t1 &&
                  swLBleInt (Int.ofNat 0) rem &&
                  swLBleInt lhsSq rhsSq

/- ## 3. Exact Bit-for-Bit Equivalence Proofs for Sliding-Window Bellman Checkers -/
theorem foldl_range_add_init_int (n : ℕ) (initA : ℤ) (f : ℕ → ℤ) : (List.range n).foldl (fun acc i ↦
  acc + f i) initA = initA + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Finset.sum_range_succ, add_assoc]
theorem swLDotLinear_eq_sum : ∀ (ks ds : List ℤ) (acc : ℤ), ks.length ≤ ds.length → swLDotLinear ks
  ds acc = acc + ∑ jIdx ∈ Finset.range ks.length, ks.getD jIdx 0 * ds.getD jIdx 0
  | [], _, acc, _ => (by simp [swLDotLinear]) | _ :: _, [], _, hlen => (by simp at hlen)
  | k :: ks, d :: ds, acc, hlen => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen; simp only [swLDotLinear,
      kpForceInt_eq, int_add_eq, int_mul_eq, List.length_cons]; rw [swLDotLinear_eq_sum ks ds (acc +
      k * d) hlen, Finset.sum_range_succ']; have hk0 : (k :: ks).getD 0 0 = k := rfl; have hd0 : (d
      :: ds).getD 0 0 = d := rfl
    have hks : ∀ i, (k :: ks).getD (i + 1) 0 = ks.getD i 0 := fun _ ↦ rfl; have hds : ∀ i, (d ::
      ds).getD (i + 1) 0 = ds.getD i 0 := fun _ ↦ rfl; simp only [hk0, hd0, hks, hds]; ring
theorem swLDotLinear_eq_foldl (ks ds : List ℤ) (acc : ℤ) (hlen : ks.length ≤ ds.length) :
  swLDotLinear ks ds acc = (List.range ks.length).foldl (fun a jIdx ↦ a + ks.getD jIdx 0 * ds.getD
  jIdx 0) acc := by rw [swLDotLinear_eq_sum ks ds acc hlen, foldl_range_add_init_int]
theorem getD_append_replicate_zero : ∀ (xs : List ℤ) (n i : ℕ), (xs ++ List.replicate n (0 :
  ℤ)).getD i 0 = xs.getD i 0
  | [], n, i => by
    simp only [List.nil_append, List.getD_eq_getElem?_getD]; by_cases hi : i < n <;> simp [hi]
  | x :: _xs, _n, 0 => rfl | _x :: xs, n, i + 1 => getD_append_replicate_zero xs n i
theorem list_int_eq_of_length_getD : ∀ (xs ys : List ℤ), xs.length = ys.length → (∀ k < xs.length,
  xs.getD k 0 = ys.getD k 0) → xs = ys
  | [], [], _, _ => rfl | [], _ :: _, hlen, _ => (by simp at hlen)
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hget => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hx : x = y := hget 0 (by simp); subst hx; congr 1
    exact list_int_eq_of_length_getD xs ys hlen fun k hk ↦ hget (k + 1) (Nat.succ_lt_succ hk)
theorem swLStepPosFast_length (den : ℤ) : ∀ (rem : ℕ) (kRows : List SwLKRow) (pTail : List ℤ) (pPrev
  : ℤ) (winDiffs : List ℤ), (swLStepPosFast den rem kRows pTail pPrev winDiffs).length = rem
  | 0, _, _, _, _ => rfl | rem + 1, [], _, _, _ => (by simp [swLStepPosFast])
  | rem + 1, _ :: kRest, [], pPrev, winDiffs => by
    simp [swLStepPosFast, kpForceInt_eq, swLStepPosFast_length den rem]
  | rem + 1, _ :: kRest, pCur :: pRest, pPrev, winDiffs => by
    simp [swLStepPosFast, kpForceInt_eq, swLStepPosFast_length den rem]
theorem winDiffs_push_eq (P : List ℤ) (s0 : ℕ) : (P.getD s0 0 - P.getD (s0 + 1) 0) :: (List.range
  s0).map (fun jIdx ↦ P.getD (s0 - 1 - jIdx) 0 - P.getD (s0 - jIdx) 0) = (List.range (s0 + 1)).map
  (fun jIdx ↦ P.getD (s0 - jIdx) 0 - P.getD (s0 + 1 - jIdx) 0) := by
  refine list_int_eq_of_length_getD _ _ (by simp) fun k hk ↦ ?_
  simp only [List.length_cons, List.length_map, List.length_range] at hk; rcases k with _ | k'
  · have hrhs : ((List.range (s0 + 1)).map (fun jIdx ↦ P.getD (s0 - jIdx) 0 - P.getD (s0 + 1 - jIdx)
      0)).getD 0 0 = P.getD s0 0 - P.getD (s0 + 1) 0 := (by simp [List.getD_eq_getElem?_getD])
    exact hrhs.symm
  · have hk' : k' < s0 := (by omega)
    have hlhs : ((P.getD s0 0 - P.getD (s0 + 1) 0) :: (List.range s0).map (fun jIdx ↦ P.getD (s0 - 1
      - jIdx) 0 - P.getD (s0 - jIdx) 0)).getD (k' + 1) 0 = P.getD (s0 - 1 - k') 0 - P.getD (s0 - k')
      0 := by
      change ((List.range s0).map (fun jIdx ↦ P.getD (s0 - 1 - jIdx) 0 - P.getD (s0 - jIdx)
        0)).getD k' 0 = _; simp [List.getD_eq_getElem?_getD, hk']
    have hrhs : ((List.range (s0 + 1)).map (fun jIdx ↦ P.getD (s0 - jIdx) 0 - P.getD (s0 + 1 - jIdx)
      0)).getD (k' + 1) 0 = P.getD (s0 - (k' + 1)) 0 - P.getD (s0 + 1 - (k' + 1)) 0 :=
      (by simp [List.getD_eq_getElem?_getD, hk])
    rw [hlhs, hrhs, show s0 - (k' + 1) = s0 - 1 - k' by omega,
      show s0 + 1 - (k' + 1) = s0 - k' by omega]
theorem swLStepPosFast_getD (den : ℤ) (P : List ℤ) :
    ∀ (rem s0 : ℕ) (kRows : List SwLKRow) (pTail : List ℤ) (pPrev : ℤ) (winDiffs : List ℤ),
      rem ≤ kRows.length →
      (∀ i < rem, (kRows.getD i []).length ≤ s0 + 1 + i) →
      pPrev = P.getD s0 0 →
      (∀ m : ℕ, pTail.getD m 0 = P.getD (s0 + 1 + m) 0) →
      winDiffs =
        (List.range s0).map (fun jIdx ↦ P.getD (s0 - 1 - jIdx) 0 - P.getD (s0 - jIdx) 0) →
      ∀ idx < rem,
        (swLStepPosFast den rem kRows pTail pPrev winDiffs).getD idx 0 =
          let s := s0 + 1 + idx
          let row := kRows.getD idx []
          ((List.range row.length).foldl
            (fun acc jIdx ↦
              acc + row.getD jIdx 0 *
                (P.getD (s - (jIdx + 1)) 0 - P.getD (s - (jIdx + 1) + 1) 0))
            (den * P.getD s 0)) / den
  | 0, _, _, _, _, _, _, _, _, _, _, idx, hidx => by omega
  | rem + 1, _, [], _, _, _, hkr, _, _, _, _, _, _ => by simp at hkr
  | rem + 1, s0, row :: kRest, pTail, pPrev, winDiffs, hkr, hrowLen, hpPrev, hpTail, hwin,
    idx, hidx => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hkr; have hp0 : P.getD (s0 + 1) 0 =
      pTail.getD 0 0 := (by simpa using (hpTail 0).symm)
    have hstep_head :
        swLStepPosFast den (rem + 1) (row :: kRest) pTail pPrev winDiffs =
          let pCur := pTail.getD 0 0
          let pRest := pTail.drop 1
          let d0 := pPrev - pCur
          let v := (swLDotLinear row (d0 :: winDiffs) (den * pCur)) / den
          v :: swLStepPosFast den rem kRest pRest pCur (d0 :: winDiffs) := by
      cases pTail with
      | nil => simp [swLStepPosFast, kpForceInt_eq, int_ediv_eq]
      | cons pCur pRest => simp [swLStepPosFast, kpForceInt_eq, int_sub_eq, int_ediv_eq]
    rw [hstep_head]; dsimp only; have hd0_eq : pPrev - pTail.getD 0 0 = P.getD s0 0 - P.getD (s0 +
      1) 0 := (by rw [hpPrev, hp0]); have hwin' : (pPrev - pTail.getD 0 0) :: winDiffs = (List.range
      (s0 + 1)).map (fun jIdx ↦ P.getD (s0 - jIdx) 0 - P.getD (s0 + 1 - jIdx) 0) :=
      (by rw [hd0_eq, hwin, winDiffs_push_eq]); rcases idx with _ | idx'
    · set ds0 : List ℤ := (pPrev - pTail.getD 0 0) :: winDiffs; change (swLDotLinear row ds0 (den *
        pTail.getD 0 0)) / den = _
      have hr0 : (row :: kRest).getD 0 [] = row := rfl; simp only [hr0, Nat.add_zero]
      have hrlen : row.length ≤ s0 + 1 := (by simpa [hr0] using hrowLen 0 (by omega))
      have hdlen : row.length ≤ ds0.length := by rw [hwin']; simpa using hrlen
      rw [swLDotLinear_eq_foldl row ds0 _ hdlen]; congr 1; rw [foldl_range_add_init_int,
        foldl_range_add_init_int, ← hp0]; congr 1; refine Finset.sum_congr rfl fun jIdx hjIdx ↦ ?_
      rw [Finset.mem_range] at hjIdx; have hj_lt : jIdx < s0 + 1 := lt_of_lt_of_le hjIdx hrlen
      have hget_w : ds0.getD jIdx 0 = P.getD (s0 - jIdx) 0 - P.getD (s0 + 1 - jIdx) 0 :=
        (by rw [hwin']; simp [List.getD_eq_getElem?_getD, hj_lt])
      have ha : s0 + 1 - (jIdx + 1) = s0 - jIdx := (by omega); have hb : s0 + 1 - (jIdx + 1) + 1 =
        s0 + 1 - jIdx := (by omega); rw [hget_w, hb, ha]
    · have hidx' : idx' < rem := (by omega); change (swLStepPosFast den rem kRest (pTail.drop 1)
        (pTail.getD 0 0) ((pPrev - pTail.getD 0 0) :: winDiffs)).getD idx' 0 = _
      have hrowLen' : ∀ i < rem, (kRest.getD i []).length ≤ (s0 + 1) + 1 + i := by
        intro i hi; have h1 := hrowLen (i + 1) (by omega)
        have hget : (row :: kRest).getD (i + 1) [] = kRest.getD i [] := rfl; rw [hget] at h1; omega
      have hpTail' : ∀ m : ℕ, (pTail.drop 1).getD m 0 = P.getD ((s0 + 1) + 1 + m) 0 := by
        intro m
        cases pTail with
        | nil =>
            have hnil : ([] : List ℤ).getD (m + 1) 0 = 0 := rfl; have hd0 : (([] : List ℤ).drop
              1).getD m 0 = 0 := rfl; have hm1 := hpTail (m + 1); rw [hnil] at hm1; rw [hd0, show
              (s0 + 1) + 1 + m = s0 + 1 + (m + 1) by omega]; exact hm1
        | cons pCur pRest =>
            have hcons : (pCur :: pRest).getD (m + 1) 0 = pRest.getD m 0 := rfl; have hd1 : ((pCur
              :: pRest).drop 1).getD m 0 = pRest.getD m 0 := rfl
            have hm1 := hpTail (m + 1); rw [hcons] at hm1; rw [hd1, show (s0 + 1) + 1 + m = s0 + 1 +
              (m + 1) by omega]; exact hm1
      have hwin_shift : (pPrev - pTail.getD 0 0) :: winDiffs = (List.range (s0 + 1)).map (fun jIdx ↦
        P.getD ((s0 + 1) - 1 - jIdx) 0 - P.getD ((s0 + 1) - jIdx) 0) := (by simpa using hwin')
      have hrec := swLStepPosFast_getD den P rem (s0 + 1) kRest (pTail.drop 1) (pTail.getD 0 0)
        ((pPrev - pTail.getD 0 0) :: winDiffs) hkr hrowLen' hp0.symm hpTail' hwin_shift idx' hidx'
      have hkr_idx : (row :: kRest).getD (idx' + 1) [] = kRest.getD idx' [] := rfl; simpa [hkr_idx,
        show (s0 + 1) + 1 + idx' = s0 + 1 + (idx' + 1) by omega] using hrec
/-- Universal bit-for-bit equivalence between `swLUnionTailLbListFast` and
  `swLUnionTailLbList`. -/
theorem swLUnionTailLbListFast_eq (L r : ℕ) (tailLbs : List ℤ) (mCopies : ℕ) :
  swLUnionTailLbListFast L r tailLbs mCopies = swLUnionTailLbList L r tailLbs mCopies := by
  unfold swLUnionTailLbListFast swLUnionTailLbList; simp only [kpForceInt_eq, kpForceNat_eq,
    kpWithGrid_eq, kpWithIntList_eq, kpForceIntList_eq, withForcedInt_eq, withForcedNat_eq,
    withForcedGrid_eq, forceListId_eq, int_mul_eq, Int.ofNat_eq_natCast, Nat.cast_zero,
    swLDescFactFast_eq, swLMinNat_eq, nat_mul_eq, nat_add_eq, nat_sub_eq, swLKRowBuildFast_eq]
  set den : ℤ := swScale * (r.descFactorial L : ℤ); set maxS : ℕ := min (mCopies * L) r
  set kRowsPos : List SwLKRow := (List.range maxS).map fun idx ↦ swLKRowBuild L r tailLbs (idx + 1)
  set kByS : List SwLKRow := (List.range (maxS + 1)).map (swLKRowBuild L r tailLbs)
  set init : List ℤ := swUnionScale :: List.replicate r (0 : ℤ); have hmaxS_r : maxS ≤ r :=
    Nat.min_le_right _ _; have hkPos_len : kRowsPos.length = maxS := (by simp [kRowsPos])
  have hkPos_eq : ∀ idx < maxS, kRowsPos.getD idx [] = kByS.getD (idx + 1) [] := by
    intro idx hidx; have hidx1 : idx + 1 < maxS + 1 := (by omega); simp [kRowsPos, kByS,
      List.getD_eq_getElem?_getD, hidx, hidx1]
  have hkPos_rowLen : ∀ idx < maxS, (kRowsPos.getD idx []).length ≤ idx + 1 := by
    intro idx hidx; have hget : kRowsPos.getD idx [] = swLKRowBuild L r tailLbs (idx + 1) :=
      (by simp [kRowsPos, List.getD_eq_getElem?_getD, hidx]); rw [hget]; unfold swLKRowBuild; simp
  suffices hind : ∀ t : ℕ,
      let posT := (List.range t).foldl (fun prevPos tIdx ↦
        swLStepPosFast den (min ((tIdx + 1) * L) maxS) kRowsPos prevPos swUnionScale []) []
      let refT := (List.range t).foldl (fun prev tIdx ↦
        swLUnionTailStepInt r den kByS (min ((tIdx + 1) * L) maxS) prev) init
      posT.length ≤ r ∧
      swUnionScale :: (posT ++ List.replicate (r - posT.length) (0 : ℤ)) = refT from
    (hind mCopies).2
  intro t
  induction t with
  | zero => simp [init]
  | succ t' ih =>
      rcases ih with ⟨hlen_prev, href_prev⟩; dsimp only at hlen_prev href_prev ⊢
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append,
        List.foldl_cons, List.foldl_nil]; set posPrev := (List.range t').foldl (fun prevPos tIdx ↦
        swLStepPosFast den (min ((tIdx + 1) * L) maxS) kRowsPos prevPos swUnionScale []) []
      set refPrev := (List.range t').foldl (fun prev tIdx ↦ swLUnionTailStepInt r den kByS (min
        ((tIdx + 1) * L) maxS) prev) init
      set curMax := min ((t' + 1) * L) maxS; have hcur_maxS : curMax ≤ maxS := Nat.min_le_right _ _
      have hcur_r : curMax ≤ r := hcur_maxS.trans hmaxS_r
      set posNext := swLStepPosFast den curMax kRowsPos posPrev swUnionScale []
      have hlen_next : posNext.length = curMax := swLStepPosFast_length den curMax kRowsPos posPrev
        swUnionScale []; refine ⟨hlen_next.trans_le hcur_r, ?_⟩; rw [swLUnionTailStepInt,
        forceListId_eq, id_eq]; refine list_int_eq_of_length_getD _ _ ?_ fun k hk ↦ ?_
      · simp [hlen_next]; omega
      · have hk_lt : k < r + 1 := (by simp [hlen_next] at hk; omega)
        have hrhs : ((List.range (r + 1)).map fun s ↦ if s == 0 then swUnionScale else if curMax < s
          then 0 else forceListId (kByS.getD s []) fun row ↦ withForcedInt ((List.range
          row.length).foldl (fun acc jIdx ↦ withForcedNat (jIdx + 1) fun j ↦ acc + row.getD jIdx 0 *
          (refPrev.getD (s - j) 0 - refPrev.getD (s - j + 1) 0)) (den * refPrev.getD s 0)) fun num ↦
          num / den).getD k 0 = if k == 0 then swUnionScale else if curMax < k then 0 else
          ((List.range (kByS.getD k []).length).foldl (fun acc jIdx ↦ acc + (kByS.getD k []).getD
          jIdx 0 * (refPrev.getD (k - (jIdx + 1)) 0 - refPrev.getD (k - (jIdx + 1) + 1) 0)) (den *
          refPrev.getD k 0)) / den := by
          simp [List.getD_eq_getElem?_getD, hk_lt, forceListId_eq, withForcedInt_eq,
            withForcedNat_eq]
        rw [hrhs]; rcases k with _ | idx
        · rfl
        · simp only [beq_false_of_ne (Nat.succ_ne_zero idx), Bool.false_eq_true, ↓reduceIte]
          have hlhs_pad : (swUnionScale :: (posNext ++ List.replicate (r - posNext.length) (0 :
            ℤ))).getD (idx + 1) 0 = posNext.getD idx 0 := by
            change (posNext ++ List.replicate (r - posNext.length) (0 : ℤ)).getD idx 0 = _
            exact getD_append_replicate_zero posNext (r - posNext.length) idx
          rw [hlhs_pad]; by_cases hgt : curMax < idx + 1
          · simp only [hgt, ↓reduceIte]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
              (by rw [hlen_next]; omega), Option.getD_none]
          · simp only [hgt, ↓reduceIte]; have hidx_cur : idx < curMax := (by omega)
            have hidx_maxS : idx < maxS := lt_of_lt_of_le hidx_cur hcur_maxS
            have hp0 : swUnionScale = refPrev.getD 0 0 := (by rw [← href_prev]; rfl)
            have hpTail : ∀ m : ℕ, posPrev.getD m 0 = refPrev.getD (0 + 1 + m) 0 := by
              intro m; rw [← href_prev, zero_add, add_comm 1 m]
              change posPrev.getD m 0 = (posPrev ++ List.replicate (r - posPrev.length) (0 :
                ℤ)).getD m 0; exact (getD_append_replicate_zero posPrev _ m).symm
            have hrowLen0 : ∀ i < curMax, (kRowsPos.getD i []).length ≤ 0 + 1 + i :=
              (by intro i hi; have h1 := hkPos_rowLen i (lt_of_lt_of_le hi hcur_maxS); omega)
            have hstep := swLStepPosFast_getD den refPrev curMax 0 kRowsPos posPrev swUnionScale []
              (by rw [hkPos_len]; exact hcur_maxS) hrowLen0 hp0 hpTail rfl idx hidx_cur
            dsimp [posNext]; rw [hstep]; dsimp only; rw [zero_add, add_comm 1 idx, hkPos_eq idx
              hidx_maxS]
theorem swLAbSumLoop_eq_sum (vTable : ℕ → ℤ) : ∀ (cnt curR : ℕ) (ts : List ℤ) (acc : ℤ), cnt ≤ curR
  → swLAbSumLoop vTable cnt curR ts acc = acc + ∑ i ∈ Finset.range cnt, ts.getD i 0 * (vTable (curR
  - i) - vTable (curR - i - 1))
  | 0, _, _, acc, _ => by simp [swLAbSumLoop]
  | cnt + 1, curR, [], acc, hle => by
    simp only [swLAbSumLoop, nat_sub_eq]; rw [swLAbSumLoop_eq_sum vTable cnt (curR - 1) [] acc
      (by omega), Finset.sum_range_succ']; simp
  | cnt + 1, curR, t :: ts, acc, hle => by
    simp only [swLAbSumLoop, kpForceInt_eq, int_add_eq, int_mul_eq, int_sub_eq, nat_sub_eq]
    rw [swLAbSumLoop_eq_sum vTable cnt (curR - 1) ts (acc + t * (vTable curR - vTable (curR - 1)))
      (by omega), Finset.sum_range_succ']; have ht0 : (t :: ts).getD 0 0 = t := rfl
    have hts : ∀ i : ℕ, (t :: ts).getD (i + 1) 0 = ts.getD i 0 := fun _ ↦ rfl; simp only [ht0, hts,
      Nat.sub_zero]
    have hsum_eq : ∑ x ∈ Finset.range cnt, ts.getD x 0 * (vTable (curR - 1 - x) - vTable (curR - 1 -
      x - 1)) = ∑ x ∈ Finset.range cnt, ts.getD x 0 * (vTable (curR - (x + 1)) - vTable (curR - (x +
      1) - 1)) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_; rw [show curR - (x + 1) = curR - 1 - x by omega]
    rw [hsum_eq]; ring
/-- Universal bit-for-bit equivalence between `checkMultiSWLStepFast` and
  `checkMultiSWLStep`. -/
theorem checkMultiSWLStepFast_eq (L mEff r numPulses tauNum tauDen verCalls : ℕ) (tailLbs : List ℤ)
  (vScale : ℤ) (vTable : ℕ → ℤ) : checkMultiSWLStepFast L mEff r numPulses tauNum tauDen verCalls
  tailLbs vScale vTable = checkMultiSWLStep L mEff r numPulses tauNum tauDen verCalls tailLbs vScale
  vTable := by
  unfold checkMultiSWLStepFast checkMultiSWLStep; refine congrArg₂ Bool.and (congrArg₂ Bool.and ?_
    ?_) ?_
  · rw [swLNatBeq_eq_beq, swLBltInt_eq_decide, swLBleInt_eq_decide, swLBleInt_eq_decide,
      nat_sub_eq, Int.ofNat_eq_natCast, Nat.cast_zero, Bool.eq_iff_iff]; simp only
      [Bool.and_eq_true, swLNatBle_eq_decide, beq_iff_eq, decide_eq_true_eq]; omega
  · rw [nat_sub_eq]; refine congrArg (List.all _) (funext fun i ↦ ?_); rw [swLBleInt_eq_decide,
      nat_add_eq, Int.ofNat_eq_natCast, Nat.cast_zero]
  rw [swLUnionTailLbListFast_eq]; simp only [kpWithIntList_eq,
    kpForceNat_eq, kpForceInt_eq, forceListId_eq, withForcedNat_eq, withForcedInt_eq, id_eq,
    swLMinNat_eq, nat_mul_eq, int_add_eq, int_sub_eq, int_mul_eq, swLIntSq_eq, Int.ofNat_eq_natCast,
    Nat.cast_zero, Nat.cast_ofNat]; generalize swLUnionTailLbList L r tailLbs mEff = tailL
  set maxS := min (L * mEff) r; have hmaxS_r : maxS ≤ r := Nat.min_le_right _ _
  have ht1 : (match (match tailL with | [] => [] | _ :: ts => ts) with
      | [] => (0 : ℤ) | x :: _ => x) = tailL.getD 1 0 := by
    rcases tailL with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have htailPos_get : ∀ s : ℕ,
      (match tailL with | [] => [] | _ :: ts => ts).getD s 0 = tailL.getD (s + 1) 0 := by
    intro s; rcases tailL with _ | ⟨_, _⟩ <;> rfl
  have hab_eq : swLAbSumLoop vTable maxS r (match tailL with | [] => [] | _ :: ts => ts) 0 =
      (List.range maxS).foldl (fun acc s ↦
        acc + tailL.getD (s + 1) 0 * (vTable (r - s) - vTable (r - s - 1))) 0 := by
    rw [swLAbSumLoop_eq_sum vTable maxS r _ 0 hmaxS_r, zero_add, foldl_range_add_init_int, zero_add]
    refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [htailPos_get s]
  rw [ht1, hab_eq, swLBltInt_eq_decide, swLBleInt_eq_decide, swLBleInt_eq_decide, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]; exact and_assoc

/- ## 4. Pure-GMP `L2Ball` Interval Bucket Evaluator (`checkSwLBucketCertL2P`) -/
/-- Strict `O(N)` spine-and-element WHNF forcing for `List IvInt`. -/
def kpForceIvList : List IvInt → List IvInt
  | [] => []
  | x :: xs =>
      kpForceIv x fun x' ↦
        match kpForceIvList xs with
        | [] => [x']
        | hd :: tl => x' :: hd :: tl
theorem kpForceIvList_eq : ∀ (xs : List IvInt), kpForceIvList xs = xs
  | [] => rfl
  | x :: xs => by unfold kpForceIvList; rw [kpForceIv_eq, kpForceIvList_eq xs]; cases xs <;> rfl
/-- Continuation wrapper strictly forcing a `List IvInt`. -/
def kpWithIvList {α : Type} (xs : List IvInt) (k : List IvInt → α) : α :=
  match kpForceIvList xs with
  | [] => k []
  | hd :: tl => k (hd :: tl)
theorem kpWithIvList_eq {α : Type} (xs : List IvInt) (k : List IvInt → α) : kpWithIvList xs k = k xs
  := by unfold kpWithIvList; rw [kpForceIvList_eq]; cases xs <;> rfl
/-- Strict `O(N)` spine-and-element WHNF forcing for `List (IvInt × IvInt)`. -/
def kpForcePairList : List (IvInt × IvInt) → List (IvInt × IvInt)
  | [] => []
  | x :: xs =>
      kpForcePair x fun x' ↦
        match kpForcePairList xs with
        | [] => [x']
        | hd :: tl => x' :: hd :: tl
theorem kpForcePairList_eq : ∀ (xs : List (IvInt × IvInt)), kpForcePairList xs = xs
  | [] => rfl
  | x :: xs => by
    unfold kpForcePairList; rw [kpForcePair_eq, kpForcePairList_eq xs]; cases xs <;> rfl
/-- Continuation wrapper strictly forcing a `List (IvInt × IvInt)`. -/
def kpWithPairList {α : Type} (xs : List (IvInt × IvInt))
    (k : List (IvInt × IvInt) → α) : α :=
  match kpForcePairList xs with
  | [] => k []
  | hd :: tl => k (hd :: tl)
theorem kpWithPairList_eq {α : Type} (xs : List (IvInt × IvInt)) (k : List (IvInt × IvInt) → α) :
  kpWithPairList xs k = k xs := by unfold kpWithPairList; rw [kpForcePairList_eq]; cases xs <;> rfl
/-- Single-eval WHNF-forcing wrapper for `(stIv, cumIv, survIv)`. -/
def kpWithState {α : Type} (s : List IvInt × IvInt × IvInt)
    (k : List IvInt × IvInt × IvInt → α) : α :=
  match s with
  | (st, cum, surv) =>
      kpWithIvList st fun st' ↦
        kpForceIv cum fun cum' ↦
          kpForceIv surv fun surv' ↦ k (st', cum', surv')
theorem kpWithState_eq {α : Type} (s : List IvInt × IvInt × IvInt) (k : List IvInt × IvInt × IvInt →
  α) : kpWithState s k = k s := by
  rcases s with ⟨st, cum, surv⟩; simp only [kpWithState, kpWithIvList_eq, kpForceIv_eq]
/-- Single-eval WHNF-forcing wrapper for `(cVec, rho, survUb)`. -/
def kpWithL2State {α : Type} (s : List ℤ × ℕ × ℤ)
    (k : List ℤ × ℕ × ℤ → α) : α :=
  match s with
  | (cVec, rho, survUb) =>
      kpWithIntList cVec fun cVec' ↦
        kpForceNat rho fun rho' ↦
          kpForceInt survUb fun survUb' ↦ k (cVec', rho', survUb')
theorem kpWithL2State_eq {α : Type} (s : List ℤ × ℕ × ℤ) (k : List ℤ × ℕ × ℤ → α) : kpWithL2State s
  k = k s := by
  rcases s with ⟨cVec, rho, survUb⟩; simp only [kpWithL2State, kpWithIntList_eq, kpForceNat_eq,
    kpForceInt_eq]
/-- Pure-GMP `≤` on `ℤ` via `Int.sub` constructor match (`bleZ`). -/
def kpBleZ (a b : ℤ) : Bool := bleZ a b
theorem kpBleZ_eq_decide (a b : ℤ) : kpBleZ a b = decide (a ≤ b) := bleZ_eq_decide a b
/-- Pure-GMP `=` on `ℤ` via `kpBleZ`. -/
def kpBeqZ (a b : ℤ) : Bool := kpBleZ a b && kpBleZ b a
theorem kpBeqZ_eq_beqZ (a b : ℤ) : kpBeqZ a b = beqZ a b := by
  unfold kpBeqZ beqZ; rw [kpBleZ_eq_decide, kpBleZ_eq_decide, bleZ_eq_decide, bleZ_eq_decide]
theorem kpBeqZ_eq_decide (a b : ℤ) : kpBeqZ a b = decide (a = b) := by
  unfold kpBeqZ; rw [kpBleZ_eq_decide, kpBleZ_eq_decide, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
/-- Pure-GMP `min` on `ℤ` via `kpBleZ`. -/
def kpMinZ (a b : ℤ) : ℤ := cond (kpBleZ a b) a b
theorem kpMinZ_eq (a b : ℤ) : kpMinZ a b = minZ a b := by
  unfold kpMinZ minZ; rw [kpBleZ_eq_decide, bleZ_eq_decide]
/-- Pure-GMP `max` on `ℤ` via `kpBleZ`. -/
def kpMaxZ (a b : ℤ) : ℤ := cond (kpBleZ a b) b a
theorem kpMaxZ_eq (a b : ℤ) : kpMaxZ a b = maxZ a b := by
  unfold kpMaxZ maxZ; rw [kpBleZ_eq_decide, bleZ_eq_decide]
/-- Structural `0..k-1` boolean conjunction avoiding `List.range` allocation. -/
def kpAllRange (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => kpAllRange p k && p k
theorem kpAllRange_eq (p : ℕ → Bool) : ∀ (k : ℕ), kpAllRange p k = (List.range k).all p
  | 0 => rfl
  | k + 1 => by
    simp only [kpAllRange, kpAllRange_eq p k, List.range_succ, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true]
/-- Pure-GMP `10^9`-scale interval addition. -/
def kpIvAdd (a b : IvInt) : IvInt :=
  match a, b with
  | (a1, a2), (b1, b2) =>
      kpForceInt (Int.add a1 b1) fun lo ↦
        kpForceInt (Int.add a2 b2) fun hi ↦ (lo, hi)
theorem kpIvAdd_eq (a b : IvInt) : kpIvAdd a b = ivAddIntP a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; simp only [kpIvAdd, ivAddIntP, kpForceInt_eq]
/-- Pure-GMP `10^9`-scale interval subtraction. -/
def kpIvSub (a b : IvInt) : IvInt :=
  match a, b with
  | (a1, a2), (b1, b2) =>
      kpForceInt (Int.sub a1 b2) fun lo ↦
        kpForceInt (Int.sub a2 b1) fun hi ↦ (lo, hi)
theorem kpIvSub_eq (a b : IvInt) : kpIvSub a b = ivSubIntP a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; simp only [kpIvSub, ivSubIntP, kpForceInt_eq]
/-- Pure-GMP `10^9`-scale interval multiplication with WHNF-forced output endpoints. -/
def kpIvMul (a b : IvInt) : IvInt :=
  match a, b with
  | (a1, a2), (b1, b2) =>
      kpForceInt (Int.mul a1 b1) fun p1 ↦
        kpForceInt (Int.mul a1 b2) fun p2 ↦
          kpForceInt (Int.mul a2 b1) fun p3 ↦
            kpForceInt (Int.mul a2 b2) fun p4 ↦
              kpForceInt (kpMinZ (kpMinZ p1 p2) (kpMinZ p3 p4)) fun lo ↦
                kpForceInt (kpMaxZ (kpMaxZ p1 p2) (kpMaxZ p3 p4)) fun hi ↦
                  kpForceInt (Int.ediv lo (.ofNat 1000000000)) fun qlo ↦
                    kpForceInt (Int.neg (Int.ediv (Int.neg hi) (.ofNat 1000000000)))
                      fun qhi ↦ (qlo, qhi)
theorem kpIvMul_eq (a b : IvInt) : kpIvMul a b = ivMulIntP a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; unfold kpIvMul ivMulIntP
  simp only [kpForceInt_eq, withForcedInt_eq, kpMinZ_eq, kpMaxZ_eq]; rfl
/-- Pure-GMP `10^9`-scale interval squaring. -/
def kpIvSq (a : IvInt) : IvInt :=
  match a with
  | (a1, a2) =>
      cond (kpBleZ (.ofNat 0) a1)
        (kpForceInt (Int.ediv (Int.mul a1 a1) (.ofNat 1000000000)) fun qlo ↦
          kpForceInt (Int.neg (Int.ediv (Int.neg (Int.mul a2 a2)) (.ofNat 1000000000)))
            fun qhi ↦ (qlo, qhi))
        (cond (kpBleZ a2 (.ofNat 0))
          (kpForceInt (Int.ediv (Int.mul a2 a2) (.ofNat 1000000000)) fun qlo ↦
            kpForceInt (Int.neg (Int.ediv (Int.neg (Int.mul a1 a1)) (.ofNat 1000000000)))
              fun qhi ↦ (qlo, qhi))
          (kpForceInt (kpMaxZ (Int.neg a1) a2) fun m ↦
            kpForceInt (Int.neg (Int.ediv (Int.neg (Int.mul m m)) (.ofNat 1000000000)))
              fun qhi ↦ (.ofNat 0, qhi)))
theorem kpIvSq_eq (a : IvInt) : kpIvSq a = ivSqIntP a := by
  rcases a with ⟨a1, a2⟩; unfold kpIvSq ivSqIntP; simp only [kpForceInt_eq, withForcedInt_eq,
    kpMaxZ_eq, kpBleZ_eq_decide, bleZ_eq_decide]; rfl
/-- Pure-GMP `10^9`-scale outward rational interval. -/
def kpIvRatDiv (num den : ℤ) : IvInt :=
  kpForceInt (Int.mul num (.ofNat 1000000000)) fun sc ↦
    kpForceInt (Int.ediv sc den) fun qlo ↦
      kpForceInt (Int.neg (Int.ediv (Int.neg sc) den)) fun qhi ↦ (qlo, qhi)
theorem kpIvRatDiv_eq (num den : ℤ) : kpIvRatDiv num den = ivRatDivP num den := by
  unfold kpIvRatDiv ivRatDivP; simp only [kpForceInt_eq, withForcedInt_eq]; rfl
/-- Pure-GMP `10^9`-scale Pythagorean `(cos, sin)` intervals. -/
def kpIvPythag (uNum uDen : ℤ) : IvInt × IvInt :=
  kpForceInt (Int.add (Int.mul uDen uDen) (Int.mul uNum uNum)) fun d ↦
    kpForceIv (kpIvRatDiv (Int.sub (Int.mul uDen uDen) (Int.mul uNum uNum)) d) fun cIv ↦
      kpForceIv (kpIvRatDiv (Int.mul (Int.mul (.ofNat 2) uNum) uDen) d) fun sIv ↦
        (cIv, sIv)
theorem kpIvPythag_eq (uNum uDen : ℤ) : kpIvPythag uNum uDen = ivPythagP uNum uDen := by
  unfold kpIvPythag ivPythagP; simp only [kpForceInt_eq, kpForceIv_eq, withForcedInt_eq,
    kpIvRatDiv_eq]; rfl
/-- Direct `O(m)` Pythagorean list builder avoiding `O(m^2)` `Fin.succ` closures. -/
def kpUPythagsGo (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) :
    ∀ (rem : ℕ), rem ≤ m → List (IvInt × IvInt)
  | 0, _ => []
  | rem + 1, h =>
      let idx := Nat.sub m (Nat.add rem 1)
      have hlt : idx < m :=
        Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ rem) h) (Nat.zero_lt_succ rem)
      kpForcePair (kpIvPythag (f ⟨idx, hlt⟩) uDen) fun py ↦
        match kpUPythagsGo uDen m f rem (Nat.le_of_succ_le h) with
        | [] => [py]
        | hd :: tl => py :: hd :: tl
theorem kpUPythagsGo_length (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : ∀ (rem : ℕ) (h : rem ≤ m),
  (kpUPythagsGo uDen m f rem h).length = rem
  | 0, _ => rfl
  | rem + 1, h => by
    unfold kpUPythagsGo; dsimp only; rw [kpForcePair_eq]
    generalize hgo : kpUPythagsGo uDen m f rem (Nat.le_of_succ_le h) = xs; have hlen :=
      kpUPythagsGo_length uDen m f rem (Nat.le_of_succ_le h); rw [hgo] at hlen; cases xs <;> simp [←
      hlen]
theorem kpUPythagsGo_getD (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : ∀ (rem : ℕ) (h : rem ≤ m) (i : ℕ) (hi
  : i < rem), (kpUPythagsGo uDen m f rem h).getD i ((0, 0), (0, 0)) = ivPythag (f ⟨m - rem + i,
  by omega⟩) uDen
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | rem + 1, h, i, hi => by
    unfold kpUPythagsGo; dsimp only; rw [kpForcePair_eq, kpIvPythag_eq, ivPythagP_eq]; set py :=
      ivPythag (f ⟨Nat.sub m (Nat.add rem 1), Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ rem)
      h) (Nat.zero_lt_succ rem)⟩) uDen
    have hcons : (match kpUPythagsGo uDen m f rem (Nat.le_of_succ_le h) with
        | [] => [py] | hd :: tl => py :: hd :: tl) =
        py :: kpUPythagsGo uDen m f rem (Nat.le_of_succ_le h) := by
      cases kpUPythagsGo uDen m f rem (Nat.le_of_succ_le h) <;> rfl
    rw [hcons]
    cases i with
    | zero => simp only [List.getD_cons_zero, py]; congr 2
    | succ j =>
        simp only [List.getD_cons_succ]; rw [kpUPythagsGo_getD uDen m f rem (Nat.le_of_succ_le h) j
          (by omega)]; congr 2
        ext
        dsimp only; omega
/-- Pure-GMP replacement for `uPythagsFin`. -/
def kpUPythags (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : List (IvInt × IvInt) :=
  kpUPythagsGo uDen m f m le_rfl
theorem kpUPythags_eq (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : kpUPythags uDen m f = uPythagsFin uDen m
  f := by
  rw [uPythagsFin_eq]; apply List.ext_getElem
  · simp [kpUPythags, kpUPythagsGo_length]
  · intro i hi1 _; have hi : i < m := (by simpa [kpUPythags, kpUPythagsGo_length] using hi1)
    rw [list_getElem_eq_getD _ ((0, 0), (0, 0)) i hi1, kpUPythags, kpUPythagsGo_getD uDen m f m
      le_rfl i hi]; simp only [List.getElem_map, List.getElem_finRange]; congr 2; ext; simp
/-- Single-pass `O(L)` Grover plane walk (`0` quadratic tail re-forcing). -/
def kpGroverWalk : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, ts, cs =>
      let ce := headZP cs
      let co := secondZP cs
      match headTrigP ts with
      | (cw, sw) =>
          kpForceIv (kpIvSub (kpIvMul cw (ce, ce)) (kpIvMul sw (co, co))) fun e' ↦
            kpForceIv (kpIvAdd (kpIvMul sw (ce, ce)) (kpIvMul cw (co, co))) fun o' ↦
              match kpGroverWalk k (drop1TrigP ts) (drop2ZP cs) with
              | [] => [e', o']
              | hd :: tl => e' :: o' :: hd :: tl
theorem kpGroverWalk_eq : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ), kpGroverWalk k ts cs
  = groverWalkP k ts cs
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
    unfold kpGroverWalk groverWalkP; rcases headTrigP ts with ⟨cw, sw⟩; simp only [kpForceIv_eq,
      withForcedIv_eq, withForcedPairList_eq, forceListId_eq, kpIvSub_eq, kpIvAdd_eq, kpIvMul_eq,
      kpGroverWalk_eq k]; cases groverWalkP k (drop1TrigP ts) (drop2ZP cs) <;> rfl
/-- Single-pass `O(L)` Pieri + weak-measurement walk (`0` quadratic tail re-forcing). -/
def kpPieriWalk (cv : IvInt) : ℕ → List (IvInt × IvInt) → List IvInt → List IvInt
  | 0, _, ss =>
      kpForceIv (kpIvMul cv (headIvP ss)) fun top ↦ [top]
  | k + 1, us, ss =>
      let lv := headIvP ss
      let rv := secondIvP ss
      match headTrigP us with
      | (cu, su) =>
          kpForceIv (kpIvSub (kpIvMul cu lv) (kpIvMul su rv)) fun l' ↦
            kpForceIv (kpIvAdd (kpIvMul su lv) (kpIvMul cu rv)) fun r' ↦
              match kpPieriWalk cv k (drop1TrigP us) (drop2IvP ss) with
              | [] => [l', r']
              | hd :: tl => l' :: r' :: hd :: tl
theorem kpPieriWalk_eq (cv : IvInt) : ∀ (k : ℕ) (us : List (IvInt × IvInt)) (ss : List IvInt),
  kpPieriWalk cv k us ss = pieriWalkIvP cv k us ss
  | 0, _, _ => by simp only [kpPieriWalk, pieriWalkIvP, kpForceIv_eq, kpIvMul_eq]
  | k + 1, us, ss => by
    unfold kpPieriWalk pieriWalkIvP; rcases headTrigP us with ⟨cu, su⟩; simp only [kpForceIv_eq,
      withForcedIv_eq, withForcedPairList_eq, withForcedList_eq, kpIvSub_eq, kpIvAdd_eq, kpIvMul_eq,
      kpPieriWalk_eq cv k]; cases pieriWalkIvP cv k (drop1TrigP us) (drop2IvP ss) <;> rfl
/-- Pure-GMP Pieri + weak-measurement interval step. -/
def kpPieriAndWeakIv : ∀ (L : ℕ), SwLPulseRat L → IvInt → List IvInt → List IvInt
  | 0, _, _, _ => []
  | m + 1, p, cv, naIv =>
      kpWithPairList (kpUPythags (Int.ofNat p.uvDen) m p.uNum) fun ups ↦
        let h0 := headIvP naIv
        match kpPieriWalk cv m ups (drop1IvP naIv) with
        | [] => [h0]
        | hd :: tl => h0 :: hd :: tl
theorem kpPieriAndWeakIv_eq : ∀ (L : ℕ) (p : SwLPulseRat L) (cv : IvInt) (naIv : List IvInt),
  kpPieriAndWeakIv L p cv naIv = swLPieriAndWeakIvP L p cv naIv
  | 0, _, _, _ => rfl
  | m + 1, p, cv, naIv => by
    unfold kpPieriAndWeakIv swLPieriAndWeakIvP; simp only [kpWithPairList_eq, withForcedPairList_eq,
      withForcedList_eq, kpUPythags_eq, kpPieriWalk_eq]; cases pieriWalkIvP cv m (uPythagsFin
      (Int.ofNat p.uvDen) m p.uNum) (drop1IvP naIv) <;> rfl
/-- Pure-GMP tail-recursive sum of squared magnitudes. -/
def kpSumSqAbs : List ℤ → ℕ → ℕ
  | [], acc => acc
  | cj :: cjs, acc =>
      kpForceNat cj.natAbs fun m ↦
        kpForceNat (Nat.add acc (Nat.mul m m)) fun acc' ↦
          kpSumSqAbs cjs acc'
theorem kpSumSqAbs_eq : ∀ (xs : List ℤ) (acc : ℕ), kpSumSqAbs xs acc = swLSumSqAbs xs acc
  | [], _ => rfl
  | _ :: xs, acc => by
    unfold kpSumSqAbs swLSumSqAbs; simp only [kpForceNat_eq, withForcedNat_eq, kpSumSqAbs_eq xs]
/-- Pure-GMP ceiling integer square root (`Nat.add s 1` reduces to `Literal.natVal`). -/
def kpCeilIsqrtNat (n : ℕ) : ℕ :=
  kpForceNat (Nat.sqrt n) fun s ↦
    cond (Nat.beq (Nat.mul s s) n) s (Nat.add s 1)
theorem kpCeilIsqrtNat_eq (n : ℕ) : kpCeilIsqrtNat n = ceilIsqrtNat n := by
  unfold kpCeilIsqrtNat ceilIsqrtNat; simp only [kpForceNat_eq, withForcedNat_eq]
/-- Pure-GMP midpoint and radius extraction. -/
def kpIvMidRad (iv : IvInt) : ℤ × ℕ :=
  match iv with
  | (lo, hi) =>
      kpForceInt (Int.ediv (Int.add lo hi) (.ofNat 2)) fun mid ↦
        kpForceNat (kpMaxZ (Int.sub mid lo) (Int.sub hi mid)).toNat fun rad ↦
          (mid, rad)
theorem kpIvMidRad_eq (iv : IvInt) : kpIvMidRad iv = ivMidRad iv := by
  rcases iv with ⟨lo, hi⟩; unfold kpIvMidRad ivMidRad; simp only [kpForceInt_eq, kpForceNat_eq,
    withForcedInt_eq, kpMaxZ_eq]; rfl
/-- Single-pass `O(L)` recentering and squared-radius sum. -/
def kpRecenterAndRadSq : List IvInt → List ℤ × ℕ
  | [] => ([], 0)
  | iv :: ivs =>
      match kpIvMidRad iv, kpRecenterAndRadSq ivs with
      | (mid, rad), (cs, acc) =>
          kpForceInt mid fun mid' ↦
            kpForceNat (Nat.add (Nat.mul rad rad) acc) fun acc' ↦
              (match cs with | [] => [mid'] | hd :: tl => mid' :: hd :: tl, acc')
theorem kpRecenterAndRadSq_eq : ∀ (ivs : List IvInt), kpRecenterAndRadSq ivs = swLRecenterAndRadSq
  ivs
  | [] => rfl
  | iv :: ivs => by
    unfold kpRecenterAndRadSq swLRecenterAndRadSq; rw [kpIvMidRad_eq, kpRecenterAndRadSq_eq ivs]
    rcases ivMidRad iv with ⟨mid, rad⟩; rcases swLRecenterAndRadSq ivs with ⟨cs, acc⟩
    simp only [kpForceInt_eq, kpForceNat_eq, withForcedInt_eq, forceListId_eq, withForcedNat_eq]
    cases cs <;> rfl
/-- Pure-GMP `L2Ball` conveyor pulse step. -/
def kpPulseStepL2 (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) (p : SwLPulseRat L) : List ℤ × ℕ × ℤ :=
  kpForceNat (kpSumSqAbs cVec 0) fun normSqC ↦
    kpForceNat (kpCeilIsqrtNat normSqC) fun normCUb ↦
      kpForceNat (Nat.add normCUb rho) fun sumR ↦
        kpForceInt
          (kpMinZ (.ofNat 1000000000)
            (Int.neg (Int.ediv (Int.neg (Int.ofNat (Nat.mul sumR sumR)))
              (.ofNat 1000000000))))
          fun oneMinusCumUb ↦
            kpForceInt (Int.add survUb oneMinusCumUb) fun survUb' ↦
              kpWithIvList (kpGroverWalk L trigIvs cVec) fun naIv ↦
                kpForceIv
                  (cond (kpBeqZ p.vNum (.ofNat 0)) (.ofNat 1000000000, .ofNat 1000000000)
                    (kpIvPythag p.vNum (Int.ofNat p.uvDen)).1)
                  fun cv ↦
                    kpWithIvList (kpPieriAndWeakIv L p cv naIv) fun nxtPtIv ↦
                      match kpRecenterAndRadSq nxtPtIv with
                      | (cNext, radSqSum) =>
                          kpForceNat (Nat.add rho (kpCeilIsqrtNat radSqSum)) fun rho' ↦
                            (cNext, rho', survUb')
theorem kpPulseStepL2_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) (cVec : List ℤ) (rho : ℕ) (survUb
  : ℤ) (p : SwLPulseRat L) : kpPulseStepL2 L trigIvs cVec rho survUb p = swLPulseStepL2 L trigIvs
  cVec rho survUb p := by
  unfold kpPulseStepL2 swLPulseStepL2; have hz0 : (.ofNat 0 : ℤ) = 0 := rfl; have hsc : (.ofNat
    1000000000 : ℤ) = swScale := rfl; have hcd : ∀ x : ℤ, Int.neg (Int.ediv (Int.neg x) swScale) =
    ceilDivScaleP x := fun _ ↦ rfl; simp only [kpForceNat_eq, kpForceInt_eq, kpWithIvList_eq,
    kpForceIv_eq, withForcedNat_eq, withForcedInt_eq, withForcedList_eq, withForcedIv_eq,
    kpSumSqAbs_eq, kpCeilIsqrtNat_eq, kpMinZ_eq, kpGroverWalk_eq, kpBeqZ_eq_beqZ, kpIvPythag_eq,
    kpPieriAndWeakIv_eq, kpRecenterAndRadSq_eq, hz0, hsc, hcd]
  rcases swLRecenterAndRadSq (swLPieriAndWeakIvP L p (cond (beqZ p.vNum 0) (swScale, swScale)
    (ivPythagP p.vNum (Int.ofNat p.uvDen)).1) (groverWalkP L trigIvs cVec)) with ⟨cNext, radSqSum⟩
  simp only [forceListId_eq]
/-- Pure-GMP multi-pulse `L2Ball` trajectory loop (`match` avoids triple `.1`/`.2` eval). -/
def kpEvolutionL2Aux (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List (SwLPulseRat L) → List ℤ × ℕ × ℤ
  | [] => (cVec, rho, survUb)
  | p :: ps =>
      kpWithL2State (kpPulseStepL2 L trigIvs cVec rho survUb p) fun nxt ↦
        match nxt with
        | (cNext, rho', survUb') => kpEvolutionL2Aux L trigIvs cNext rho' survUb' ps
theorem kpEvolutionL2Aux_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) : ∀ (ps : List (SwLPulseRat L))
  (cVec : List ℤ) (rho : ℕ) (survUb : ℤ), kpEvolutionL2Aux L trigIvs cVec rho survUb ps =
  swLEvolutionL2Aux L trigIvs cVec rho survUb ps
  | [], _, _, _ => rfl
  | p :: ps, cVec, rho, survUb => by
    unfold kpEvolutionL2Aux swLEvolutionL2Aux; rw [kpWithL2State_eq, withForcedL2State_eq,
      kpPulseStepL2_eq]; rcases swLPulseStepL2 L trigIvs cVec rho survUb p with ⟨cNext, rho',
      survUb'⟩; exact kpEvolutionL2Aux_eq L trigIvs ps cNext rho' survUb'
/-- Pure-GMP multi-pulse `L2Ball` trajectory from `(|b_0, 0⟩, 0, 0)`. -/
def kpEvolutionL2 (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L)) : List ℤ × ℕ × ℤ :=
  kpWithIntList (.ofNat 1000000000 :: List.replicate (Nat.sub (Nat.mul 2 L) 1) (.ofNat 0))
    fun cInit ↦ kpEvolutionL2Aux L trigIvs cInit 0 (.ofNat 0) pulses
theorem kpEvolutionL2_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) (pulses : List (SwLPulseRat L)) :
  kpEvolutionL2 L trigIvs pulses = swLEvolutionL2 L trigIvs pulses := by
  unfold kpEvolutionL2 swLEvolutionL2; rw [kpWithIntList_eq, forceListId_eq, kpEvolutionL2Aux_eq]
  rfl
/-- Pure-GMP terminal interval extraction from `(cVec, rho, survUb)`. -/
def kpTerminalStateL2 (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List IvInt × IvInt × IvInt :=
  kpForceNat (kpSumSqAbs cVec 0) fun normSqK ↦
    kpForceNat (kpCeilIsqrtNat normSqK) fun normKUb ↦
      kpForceNat (Nat.sub (Nat.sqrt normSqK) rho) fun normKLb ↦
        kpForceNat (Nat.add normKUb rho) fun sumR ↦
          kpForceInt
            (kpMinZ (.ofNat 1000000000)
              (Int.neg (Int.ediv (Int.neg (Int.ofNat (Nat.mul sumR sumR)))
                (.ofNat 1000000000))))
            fun oneMinusCumUb ↦
              kpForceInt (kpMaxZ (.ofNat 0) (Int.sub (.ofNat 1000000000) oneMinusCumUb))
                fun cumLo ↦
                  kpForceInt
                    (kpMinZ (.ofNat 1000000000)
                      (Int.sub (.ofNat 1000000000)
                        (Int.ediv (Int.ofNat (Nat.mul normKLb normKLb))
                          (.ofNat 1000000000))))
                    fun cumHi ↦
                      let rhoZ := Int.ofNat rho
                      kpWithState
                        (cVec.map fun cj ↦ (Int.sub cj rhoZ, Int.add cj rhoZ),
                         (cumLo, cumHi),
                         (.ofNat 0, survUb))
                        id
theorem kpTerminalStateL2_eq (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) : kpTerminalStateL2 cVec rho
  survUb = swLTerminalStateL2 cVec rho survUb := by
  unfold kpTerminalStateL2 swLTerminalStateL2; simp only [kpForceNat_eq, kpForceInt_eq,
    kpWithState_eq, withForcedNat_eq, withForcedInt_eq, withForcedState_eq, kpSumSqAbs_eq,
    kpCeilIsqrtNat_eq, kpMinZ_eq, kpMaxZ_eq]; rfl
/-- Pure-GMP linear orbit projection accumulator. -/
def kpOrbLinAux (o : ℕ) : ℕ → IvInt → List IvInt → IvInt
  | _, acc, [] => acc
  | j, acc, sj :: sjs =>
      let mIv : IvInt :=
        cond (Nat.beq j o) (.ofNat 999999999, .ofNat 1000000000) (.negSucc 0, .ofNat 1)
      kpForceIv (kpIvAdd acc (kpIvMul sj mIv)) fun acc' ↦
        kpOrbLinAux o (Nat.add j 1) acc' sjs
theorem kpOrbLinAux_eq (o : ℕ) : ∀ (j : ℕ) (acc : IvInt) (stIv : List IvInt), kpOrbLinAux o j acc
  stIv = swLOrbLinAuxP o j acc stIv
  | _, _, [] => rfl
  | j, acc, sj :: sjs => by
    unfold kpOrbLinAux swLOrbLinAuxP; simp only [kpForceIv_eq, withForcedIv_eq, kpIvAdd_eq,
      kpIvMul_eq]; exact kpOrbLinAux_eq o (j + 1) _ sjs
/-- Pure-GMP squared orbit projection interval. -/
def kpOrbSqIv (stIv : List IvInt) (o : ℕ) : IvInt :=
  kpIvSq (kpOrbLinAux o 0 (.ofNat 0, .ofNat 0) stIv)
theorem kpOrbSqIv_eqP (stIv : List IvInt) (o : ℕ) : kpOrbSqIv stIv o = swLOrbSqIvP stIv o := by
  unfold kpOrbSqIv swLOrbSqIvP; have hz0 : (.ofNat 0 : ℤ) = 0 := rfl; rw [hz0, kpIvSq_eq,
    kpOrbLinAux_eq]
/-- Pure-GMP descending suffix tail intervals. -/
def kpTailSuffixIvs (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ℕ → List IvInt
  | 0 => []
  | m + 1 =>
      let c := Nat.sub L m
      cond (Nat.beq c L)
        (kpForceIv
          (kpIvAdd (kpOrbSqIv stIv (Nat.sub (Nat.mul 2 L) 1))
            (kpIvMul cumIv (kpIvSq (.ofNat 999999999, .ofNat 1000000000))))
          fun topIv ↦ [topIv])
        (match kpTailSuffixIvs L stIv cumIv m with
        | [] => []
        | nextIv :: rest =>
            let phIv := kpIvAdd
              (kpIvAdd (kpOrbSqIv stIv (Nat.sub (Nat.mul 2 c) 1))
                (kpOrbSqIv stIv (Nat.mul 2 c)))
              (kpIvMul cumIv (.ofNat 0, .ofNat 2))
            kpForceIv (kpIvAdd phIv nextIv) fun curIv ↦ curIv :: nextIv :: rest)
theorem kpTailSuffixIvs_eqP (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ∀ (m : ℕ), kpTailSuffixIvs
  L stIv cumIv m = swLTailSuffixIvsP L stIv cumIv m
  | 0 => rfl
  | m + 1 => by
    unfold kpTailSuffixIvs swLTailSuffixIvsP; dsimp only; have hc1 : (.ofNat 999999999, .ofNat
      1000000000) = (Int.sub swScale swOrbPad, swScale) := rfl; have hc2 : (.ofNat 0, .ofNat 2) =
      ((0 : ℤ), Int.mul 2 swOrbPad) := rfl; rw [swLNatBeq_eq_beq]
    by_cases h : (Nat.sub L m == L) = true
    · simp only [h, Bool.cond_true, kpForceIv_eq, kpIvAdd_eq, kpOrbSqIv_eqP, kpIvMul_eq, kpIvSq_eq,
        hc1]
    · have hf : (Nat.sub L m == L) = false := Bool.eq_false_iff.2 h; simp only [hf,
        Bool.cond_false, kpTailSuffixIvs_eqP L stIv cumIv m]
      cases swLTailSuffixIvsP L stIv cumIv m with
      | nil => rfl
      | cons nextIv rest =>
          simp only [kpForceIv_eq, withForcedIv_eq, kpIvAdd_eq, kpOrbSqIv_eqP, kpIvMul_eq, hc2]
/-- Pure-GMP clamped monotone lower bounds. -/
def kpClampTailLbs : List IvInt → List ℤ
  | [] => []
  | [ivL] =>
      match ivL with
      | (lo, _) => kpForceInt (kpMaxZ (.ofNat 0) lo) fun v ↦ [v]
  | iv :: rest =>
      match iv, kpClampTailLbs rest with
      | (lo, _), [] => kpForceInt (kpMaxZ (.ofNat 0) lo) fun v ↦ [v]
      | (lo, _), nextLb :: lbs =>
          kpForceInt (kpMaxZ nextLb (kpMinZ (.ofNat 1000000000) lo)) fun curLb ↦
            curLb :: nextLb :: lbs
theorem kpClampTailLbs_eqP : ∀ (ivs : List IvInt), kpClampTailLbs ivs = swLClampTailLbsP ivs
  | [] => rfl
  | [⟨lo, hi⟩] => by
    unfold kpClampTailLbs swLClampTailLbsP; dsimp only; have hz0 : (.ofNat 0 : ℤ) = 0 := rfl
    simp only [kpForceInt_eq, kpMaxZ_eq, hz0]
  | ⟨lo, hi⟩ :: iv2 :: tl => by
    have ih := kpClampTailLbs_eqP (iv2 :: tl); unfold kpClampTailLbs swLClampTailLbsP; dsimp only
    rw [ih]; have hz0 : (.ofNat 0 : ℤ) = 0 := rfl; have hsc : (.ofNat 1000000000 : ℤ) = swScale :=
      rfl
    cases swLClampTailLbsP (iv2 :: tl) with
    | nil => simp only [kpForceInt_eq, kpMaxZ_eq, hz0]
    | cons nextLb lbs => simp only [kpForceInt_eq, withForcedInt_eq, kpMaxZ_eq, kpMinZ_eq, hsc]
/-- Pure-GMP pulse denominator check `0 < p.uvDen`. -/
def kpPulseValid {L : ℕ} (p : SwLPulseRat L) : Bool := Nat.ble 1 p.uvDen
theorem kpPulsesAllValid_eq {L : ℕ} (ps : List (SwLPulseRat L)) : ps.all kpPulseValid = ps.all
  swLPulseValid := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.all_cons, kpPulseValid, swLPulseValid, kpNatBle_one_eq_pos, ih]
/-- Pure-GMP unitary pulse check (`0 < p.uvDen` and `p.vNum = 0`). -/
def kpPulseUnitValid {L : ℕ} (p : SwLPulseRat L) : Bool :=
  kpPulseValid p && kpBeqZ p.vNum (.ofNat 0)
theorem kpPulsesAllUnitValid_eq {L : ℕ} (ps : List (SwLPulseRat L)) : ps.all kpPulseUnitValid =
  ps.all (fun p ↦ swLPulseValid p && decide (p.vNum = 0)) := by
  have hz0 : (.ofNat 0 : ℤ) = 0 := rfl
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.all_cons, kpPulseUnitValid, kpPulseValid, swLPulseValid, kpNatBle_one_eq_pos,
      kpBeqZ_eq_decide, hz0, ih]
/-- Pure-GMP `10^18`-stepped double-angle trig checker (`0` `HAdd.hAdd` / `LinearOrder`). -/
def kpCheckSwLTrigRat (a d b e cLo cHi sLo sHi : ℤ) : Bool :=
  let s18 : ℤ := .ofNat 1000000000000000000
  let sc : ℤ := .ofNat 1000000000
  kpForceInt (Int.ediv (Int.mul a s18) d) fun qLoLo ↦
    kpForceInt (Int.neg (Int.ediv (Int.neg (Int.mul a s18)) d)) fun qLoHi ↦
      kpForceInt (Int.neg (Int.ediv (Int.neg (Int.mul b s18)) e)) fun qHiHi ↦
        kpForceInt
          (Int.ediv
            (Int.mul qLoLo
              (Int.sub (Int.mul (Int.mul (.ofNat 24) s18) s18) (Int.mul qLoLo qLoLo)))
            (Int.mul (Int.mul (.ofNat 48) s18) s18))
          fun s2Lo ↦
            kpForceInt
              (Int.sub s18
                (Int.neg
                  (Int.ediv (Int.neg (Int.mul qLoHi qLoHi)) (Int.mul (.ofNat 32) s18))))
              fun c4Lo ↦
                kpForceInt
                  (Int.sub (Int.ediv (Int.mul (Int.mul (.ofNat 2) c4Lo) c4Lo) s18) s18)
                  fun c2Lo ↦
                    kpForceInt
                      (Int.sub s18
                        (Int.neg
                          (Int.ediv (Int.neg (Int.mul qHiHi qHiHi))
                            (Int.mul (.ofNat 128) s18))))
                      fun c8H ↦
                        kpForceInt
                          (Int.sub
                            (Int.ediv (Int.mul (Int.mul (.ofNat 2) c8H) c8H) s18) s18)
                          fun c4H ↦
                            kpForceInt
                              (Int.sub
                                (Int.ediv (Int.mul (Int.mul (.ofNat 2) c4H) c4H) s18) s18)
                              fun c2H ↦
                                kpForceInt
                                  (Int.sub
                                    (Int.ediv (Int.mul (Int.mul (.ofNat 2) c2H) c2H) s18)
                                    s18)
                                  fun c1H ↦
                                    kpBleZ (.ofNat 1) a &&
                                    (kpBleZ (.ofNat 1) d &&
                                    (kpBleZ (.ofNat 0) b &&
                                    (kpBleZ (.ofNat 1) e &&
                                    (kpBleZ b e &&
                                    (kpBleZ (.ofNat 0) cLo &&
                                    (kpBleZ (.ofNat 0) cHi &&
                                    (kpBleZ (.ofNat 0) sLo &&
                                    (kpBleZ (.ofNat 0) sHi &&
                                    (kpBleZ (.ofNat 1) qLoLo &&
                                    (kpBleZ qLoHi s18 &&
                                    (kpBleZ qHiHi s18 &&
                                    (kpBleZ (.ofNat 0) s2Lo &&
                                    (kpBleZ (.ofNat 0) c4Lo &&
                                    (kpBleZ (.ofNat 0) c2Lo &&
                                    (kpBleZ (Int.mul (Int.mul sLo s18) s18)
                                      (Int.mul (Int.mul (Int.mul (.ofNat 2) s2Lo) c2Lo)
                                        sc) &&
                                    (kpBleZ (.ofNat 0) c8H &&
                                    (kpBleZ (.ofNat 0) c4H &&
                                    (kpBleZ (.ofNat 0) c2H &&
                                    (kpBleZ (Int.mul cLo s18) (Int.mul c1H sc) &&
                                    (kpBleZ (Int.mul sc sc)
                                      (Int.add (Int.mul cLo cLo) (Int.mul sHi sHi)) &&
                                     kpBleZ (Int.mul sc sc)
                                      (Int.add (Int.mul sLo sLo)
                                        (Int.mul cHi cHi))))))))))))))))))))))
theorem kpCheckSwLTrigRat_eq (a d b e cLo cHi sLo sHi : ℤ) : kpCheckSwLTrigRat a d b e cLo cHi sLo
  sHi = checkSwLTrigRat a d b e cLo cHi sLo sHi := by
  unfold kpCheckSwLTrigRat checkSwLTrigRat; simp only [kpForceInt_eq, withForcedInt_eq,
    kpBleZ_eq_decide, ← Bool.decide_and]; rfl
/-- Pure-GMP stratum angle-ratio checker (`1 ≤ shiftW ≤ 7`). -/
def kpCheckSwLStratumRatio (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  let s20 : ℤ := .ofNat 100000000000000000000
  let s20m1 : ℤ := Int.sub s20 (.ofNat 1)
  let sc : ℤ := .ofNat 1000000000
  let sc2 : ℤ := Int.mul sc sc
  let rMinZ : ℤ := Int.ofNat rMin
  let rMaxZ : ℤ := Int.ofNat rMax
  let swZ : ℤ := Int.ofNat shiftW
  let rLo1 : ℤ := Int.add ratioLo (.ofNat 1)
  let rHi1 : ℤ := Int.sub ratioHi (.ofNat 1)
  Nat.ble (Nat.add shiftW 1) rMin &&
  (Nat.ble rMin rMax &&
  (Nat.ble rMax 1024 &&
  (Nat.ble 1 shiftW &&
  (Nat.ble shiftW 7 &&
  (kpBleZ (.ofNat 1) ratioLo &&
  (kpBleZ (.ofNat 2) ratioHi &&
  (kpBleZ ratioHi sc &&
  (kpBleZ (Int.mul (Int.mul rLo1 rLo1) rMinZ) (Int.mul sc2 (Int.sub rMinZ swZ)) &&
  (kpBleZ (Int.mul sc2 (Int.sub rMaxZ swZ))
    (Int.mul (Int.sub (Int.mul rHi1 rHi1) swZ) rMaxZ) &&
  (kpBleZ (Int.mul ratioLo s20) (Int.mul rLo1 s20m1) &&
   kpBleZ (Int.mul rHi1 s20) (Int.mul ratioHi s20m1)))))))))))
theorem kpCheckSwLStratumRatio_eq (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) :
  kpCheckSwLStratumRatio rMin rMax shiftW ratioLo ratioHi = checkSwLStratumRatio rMin rMax shiftW
  ratioLo ratioHi := by
  unfold kpCheckSwLStratumRatio checkSwLStratumRatio; simp only [swLNatBle_eq_decide,
    kpBleZ_eq_decide, ← Bool.decide_and]; rfl
/-- Pure-GMP `2 ≤ L ≤ 8` bucket angle checker. -/
def kpCheckSwLBucketAngles (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := .ofNat 100000000000
  let tnZ : ℤ := Int.ofNat tauNum
  let tdZ : ℤ := Int.ofNat tauDen
  kpForceInt (Int.add (Int.mul tnZ s11) tdZ) fun q1HiNum ↦
    kpForceInt (Int.mul tdZ s11) fun q1HiDen ↦
      (Nat.ble 2 L &&
      (Nat.ble L 8 &&
      (Nat.ble L rMin &&
      (Nat.ble rMin rMax &&
      (Nat.ble rMax 1024 &&
      (Nat.ble 1 tauNum &&
      (Nat.ble 1 tauDen &&
      (Nat.beq ratios.length (Nat.sub L 1) &&
       Nat.beq trigIvs.length L)))))))) &&
      match trigIvs with
      | [] => false
      | ((c0Lo, c0Hi), (s0Lo, s0Hi)) :: restTrig =>
          kpCheckSwLTrigRat tnZ tdZ q1HiNum q1HiDen c0Lo c0Hi s0Lo s0Hi &&
          kpAllRange (fun idx ↦
            let w := Nat.add idx 1
            match ratios.getD idx (.ofNat 0, .ofNat 0),
                restTrig.getD idx ((.ofNat 0, .ofNat 0), (.ofNat 0, .ofNat 0)) with
            | (rLo, rHi), ((cLo, cHi), (sLo, sHi)) =>
                kpCheckSwLStratumRatio rMin rMax w rLo rHi &&
                kpCheckSwLTrigRat (Int.mul tnZ rLo) (Int.mul tdZ (.ofNat 1000000000))
                  (Int.mul q1HiNum rHi) (Int.mul q1HiDen (.ofNat 1000000000))
                  cLo cHi sLo sHi) (Nat.sub L 1)
theorem kpCheckSwLBucketAngles_eq (L rMin rMax tauNum tauDen : ℕ) (ratios : List IvInt) (trigIvs :
  List (IvInt × IvInt)) : kpCheckSwLBucketAngles L rMin rMax tauNum tauDen ratios trigIvs =
  checkSwLBucketAngles L rMin rMax tauNum tauDen ratios trigIvs := by
  unfold kpCheckSwLBucketAngles checkSwLBucketAngles; have hsub : Nat.sub L 1 = L - 1 := rfl
  simp only [kpForceInt_eq, withForcedInt_eq, swLNatBle_eq_decide, natBeq_eq_decide, ←
    Bool.decide_and, hsub]; rcases trigIvs with _ | ⟨⟨⟨c0Lo, c0Hi⟩, ⟨s0Lo, s0Hi⟩⟩, restTrig⟩
  · rfl
  · dsimp only; rw [kpCheckSwLTrigRat_eq, kpAllRange_eq]; congr 2; congr 1; funext idx
    have hz0 : (.ofNat 0 : ℤ) = 0 := rfl; simp only [hz0]; rcases ratios.getD idx (0, 0) with ⟨rLo,
      rHi⟩; rcases restTrig.getD idx ((0, 0), (0, 0)) with ⟨⟨cLo, cHi⟩, ⟨sLo, sHi⟩⟩
    simp only [kpCheckSwLStratumRatio_eq, kpCheckSwLTrigRat_eq]; rfl
/-- Pure-GMP `2 ≤ L ≤ 8` `L2Ball` bucket certificate checker equal to
  `checkSwLBucketCertL2`. -/
def checkSwLBucketCertL2P (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L)) (tailLbs : List ℤ) (survUb : ℤ) : Bool :=
  kpWithIvList ratios fun rats' ↦
    kpWithPairList trigIvs fun trigs' ↦
      kpWithIntList tailLbs fun tails' ↦
        kpForceInt survUb fun surv' ↦
          let plen := pulses.length
          let t0 := tails'.getD 0 (.ofNat 0)
          let tLast := tails'.getD (Nat.sub L 1) (.ofNat 0)
          (Nat.ble 1 plen &&
          (Nat.ble plen 250 &&
          (Nat.beq tails'.length L &&
          (kpBleZ (.ofNat 0) surv' &&
          (kpBleZ (.ofNat 1) t0 &&
          (kpBleZ t0 (.ofNat 1000000000) &&
           kpBleZ (.ofNat 0) tLast)))))) &&
          pulses.all kpPulseValid &&
          kpAllRange (fun i ↦ kpBleZ (tails'.getD (Nat.add i 1) (.ofNat 0))
            (tails'.getD i (.ofNat 0))) (Nat.sub L 1) &&
          kpCheckSwLBucketAngles L rMin rMax tauNum tauDen rats' trigs' &&
          kpWithL2State (kpEvolutionL2 L trigs' pulses) fun evol ↦
            match evol with
            | (cVec, rho, survEvol) =>
                kpWithState (kpTerminalStateL2 cVec rho survEvol) fun outIv ↦
                  match outIv with
                  | (stIv, cumIv, (_, survOut)) =>
                      kpForceIv
                        (kpIvAdd (kpOrbSqIv stIv 0) (kpIvMul cumIv (.ofNat 0, .ofNat 1)))
                        fun p0Iv ↦
                          kpForceIv
                            (kpIvSub (.ofNat 1000000000, .ofNat 1000000000) p0Iv)
                            fun t1Iv ↦
                              kpWithIvList
                                (t1Iv :: kpTailSuffixIvs L stIv cumIv (Nat.sub L 1))
                                fun tailIvs ↦
                                  kpWithIntList (kpClampTailLbs tailIvs) fun certLbs ↦
                                    (kpBleZ survOut surv' &&
                                     Nat.beq certLbs.length L) &&
                                    kpAllRange (fun i ↦
                                      kpBleZ (tails'.getD i (.ofNat 0))
                                        (certLbs.getD i (.ofNat 0))) L
theorem checkSwLBucketCertL2P_eq (L rMin rMax tauNum tauDen : ℕ) (ratios : List IvInt) (trigIvs :
  List (IvInt × IvInt)) (pulses : List (SwLPulseRat L)) (tailLbs : List ℤ) (survUb : ℤ) :
  checkSwLBucketCertL2P L rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb =
  checkSwLBucketCertL2 L rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb := by
  unfold checkSwLBucketCertL2P checkSwLBucketCertL2; have hsub : Nat.sub L 1 = L - 1 := rfl
  simp only [kpWithIvList_eq, kpWithPairList_eq, kpWithIntList_eq, kpForceInt_eq, kpWithL2State_eq,
    kpWithState_eq, kpForceIv_eq, withForcedL2State_eq, withForcedState_eq, withForcedIv_eq,
    withForcedList_eq, forceListId_eq, kpPulsesAllValid_eq, kpAllRange_eq,
    kpCheckSwLBucketAngles_eq, kpEvolutionL2_eq, kpTerminalStateL2_eq, swLNatBle_eq_decide,
    natBeq_eq_decide, kpBleZ_eq_decide, ← Bool.decide_and, hsub]
  rcases swLEvolutionL2 L trigIvs pulses with ⟨cVec, rho, survEvol⟩
  rcases swLTerminalStateL2 cVec rho survEvol with ⟨stIv, cumIv, survLo, survOut⟩; dsimp only
  simp only [kpIvAdd_eq, kpOrbSqIv_eqP, kpIvMul_eq, kpIvSub_eq, kpTailSuffixIvs_eqP,
    kpClampTailLbs_eqP]; rfl

/- ## 3. Schedule-Precompiled `L2Ball` Bucket Evaluator (`0` Per-Bucket `kpIvPythag` / `Fin`) -/
section PrecompiledPulses
/-- Precompiled `(cv, ups)` interval data for one `SwLPulseRat L`. -/
abbrev KpPrePulse : Type := IvInt × List (IvInt × IvInt)
/-- Pure-GMP weak-measurement cosine interval for a pulse `p`. -/
def kpPulseCv {L : ℕ} (p : SwLPulseRat L) : IvInt :=
  cond (kpBeqZ p.vNum (.ofNat 0)) (.ofNat 1000000000, .ofNat 1000000000)
    (kpIvPythag p.vNum (Int.ofNat p.uvDen)).1
/-- Compile one `SwLPulseRat L` into its bucket-independent `(cv, ups)` intervals. -/
def kpCompilePulse : ∀ (L : ℕ), SwLPulseRat L → KpPrePulse
  | 0, p => kpForceIv (kpPulseCv p) fun cv ↦ (cv, [])
  | m + 1, p =>
      kpForceIv (kpPulseCv p) fun cv ↦
        kpWithPairList (kpUPythags (Int.ofNat p.uvDen) m p.uNum) fun ups ↦ (cv, ups)
/-- Compile an entire schedule's pulses once per schedule. -/
def kpCompilePulses (L : ℕ) (ps : List (SwLPulseRat L)) : List KpPrePulse :=
  ps.map (kpCompilePulse L)
/-- Pure-GMP Pieri + weak-measurement step consuming a precompiled `KpPrePulse`. -/
def kpPieriAndWeakPre : ℕ → KpPrePulse → List IvInt → List IvInt
  | 0, _, _ => []
  | m + 1, (cv, ups), naIv =>
      let h0 := headIvP naIv
      match kpPieriWalk cv m ups (drop1IvP naIv) with
      | [] => [h0]
      | hd :: tl => h0 :: hd :: tl
/-- Pure-GMP `L2Ball` conveyor pulse step consuming a precompiled `KpPrePulse`. -/
def kpPulseStepL2Pre (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) (pp : KpPrePulse) : List ℤ × ℕ × ℤ :=
  kpForceNat (kpSumSqAbs cVec 0) fun normSqC ↦
    kpForceNat (kpCeilIsqrtNat normSqC) fun normCUb ↦
      kpForceNat (Nat.add normCUb rho) fun sumR ↦
        kpForceInt
          (kpMinZ (.ofNat 1000000000)
            (Int.neg (Int.ediv (Int.neg (Int.ofNat (Nat.mul sumR sumR)))
              (.ofNat 1000000000))))
          fun oneMinusCumUb ↦
            kpForceInt (Int.add survUb oneMinusCumUb) fun survUb' ↦
              kpWithIvList (kpGroverWalk L trigIvs cVec) fun naIv ↦
                kpWithIvList (kpPieriAndWeakPre L pp naIv) fun nxtPtIv ↦
                  match kpRecenterAndRadSq nxtPtIv with
                  | (cNext, radSqSum) =>
                      kpForceNat (Nat.add rho (kpCeilIsqrtNat radSqSum)) fun rho' ↦
                        (cNext, rho', survUb')
/-- Pure-GMP multi-pulse `L2Ball` loop over precompiled `List KpPrePulse`. -/
def kpEvolutionL2AuxPre (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List KpPrePulse → List ℤ × ℕ × ℤ
  | [] => (cVec, rho, survUb)
  | pp :: pps =>
      kpWithL2State (kpPulseStepL2Pre L trigIvs cVec rho survUb pp) fun nxt ↦
        match nxt with
        | (cNext, rho', survUb') => kpEvolutionL2AuxPre L trigIvs cNext rho' survUb' pps
/-- Pure-GMP multi-pulse `L2Ball` trajectory from `(|b_0, 0⟩, 0, 0)` over `List KpPrePulse`. -/
def kpEvolutionL2Pre (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (pps : List KpPrePulse) : List ℤ × ℕ × ℤ :=
  kpWithIntList (.ofNat 1000000000 :: List.replicate (Nat.sub (Nat.mul 2 L) 1) (.ofNat 0))
    fun cInit ↦ kpEvolutionL2AuxPre L trigIvs cInit 0 (.ofNat 0) pps
/-- Pure-GMP `2 ≤ L ≤ 8` `L2Ball` bucket checker over schedule-precompiled `pps`. -/
def checkSwLBucketCertL2Pre (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (pps : List KpPrePulse) (tailLbs : List ℤ) (survUb : ℤ) : Bool :=
  kpWithIvList ratios fun rats' ↦
    kpWithPairList trigIvs fun trigs' ↦
      kpWithIntList tailLbs fun tails' ↦
        kpForceInt survUb fun surv' ↦
          let plen := pps.length
          let t0 := tails'.getD 0 (.ofNat 0)
          let tLast := tails'.getD (Nat.sub L 1) (.ofNat 0)
          (Nat.ble 1 plen &&
          (Nat.ble plen 250 &&
          (Nat.beq tails'.length L &&
          (kpBleZ (.ofNat 0) surv' &&
          (kpBleZ (.ofNat 1) t0 &&
          (kpBleZ t0 (.ofNat 1000000000) &&
           kpBleZ (.ofNat 0) tLast)))))) &&
          kpAllRange (fun i ↦ kpBleZ (tails'.getD (Nat.add i 1) (.ofNat 0))
            (tails'.getD i (.ofNat 0))) (Nat.sub L 1) &&
          kpCheckSwLBucketAngles L rMin rMax tauNum tauDen rats' trigs' &&
          kpWithL2State (kpEvolutionL2Pre L trigs' pps) fun evol ↦
            match evol with
            | (cVec, rho, survEvol) =>
                kpWithState (kpTerminalStateL2 cVec rho survEvol) fun outIv ↦
                  match outIv with
                  | (stIv, cumIv, (_, survOut)) =>
                      kpForceIv
                        (kpIvAdd (kpOrbSqIv stIv 0) (kpIvMul cumIv (.ofNat 0, .ofNat 1)))
                        fun p0Iv ↦
                          kpForceIv
                            (kpIvSub (.ofNat 1000000000, .ofNat 1000000000) p0Iv)
                            fun t1Iv ↦
                              kpWithIvList
                                (t1Iv :: kpTailSuffixIvs L stIv cumIv (Nat.sub L 1))
                                fun tailIvs ↦
                                  kpWithIntList (kpClampTailLbs tailIvs) fun certLbs ↦
                                    (kpBleZ survOut surv' &&
                                     Nat.beq certLbs.length L) &&
                                    kpAllRange (fun i ↦
                                      kpBleZ (tails'.getD i (.ofNat 0))
                                        (certLbs.getD i (.ofNat 0))) L
theorem kpPieriAndWeakPre_compile : ∀ (L : ℕ) (p : SwLPulseRat L) (naIv : List IvInt),
  kpPieriAndWeakPre L (kpCompilePulse L p) naIv = kpPieriAndWeakIv L p (kpPulseCv p) naIv
  | 0, _, _ => rfl
  | m + 1, p, naIv => by
    simp only [kpCompilePulse, kpForceIv_eq, kpWithPairList_eq, kpPieriAndWeakPre, kpPieriAndWeakIv]
theorem kpPulseStepL2Pre_compile (L : ℕ) (trigIvs : List (IvInt × IvInt)) (cVec : List ℤ) (rho : ℕ)
  (survUb : ℤ) (p : SwLPulseRat L) : kpPulseStepL2Pre L trigIvs cVec rho survUb (kpCompilePulse L p)
  = kpPulseStepL2 L trigIvs cVec rho survUb p := by
  unfold kpPulseStepL2Pre kpPulseStepL2; simp only [kpForceNat_eq, kpForceInt_eq, kpWithIvList_eq,
    kpForceIv_eq, kpPieriAndWeakPre_compile, kpPulseCv]
theorem kpEvolutionL2AuxPre_compile (L : ℕ) (trigIvs : List (IvInt × IvInt)) : ∀ (ps : List
  (SwLPulseRat L)) (cVec : List ℤ) (rho : ℕ) (survUb : ℤ), kpEvolutionL2AuxPre L trigIvs cVec rho
  survUb (kpCompilePulses L ps) = kpEvolutionL2Aux L trigIvs cVec rho survUb ps
  | [], _, _, _ => rfl
  | p :: ps, cVec, rho, survUb => by
    simp only [kpCompilePulses, List.map_cons, kpEvolutionL2AuxPre, kpEvolutionL2Aux,
      kpPulseStepL2Pre_compile, kpWithL2State_eq]
    rcases kpPulseStepL2 L trigIvs cVec rho survUb p with ⟨cNext, rho', survUb'⟩
    exact kpEvolutionL2AuxPre_compile L trigIvs ps cNext rho' survUb'
theorem kpEvolutionL2Pre_compile (L : ℕ) (trigIvs : List (IvInt × IvInt)) (pulses : List
  (SwLPulseRat L)) : kpEvolutionL2Pre L trigIvs (kpCompilePulses L pulses) = kpEvolutionL2 L trigIvs
  pulses := by
  unfold kpEvolutionL2Pre kpEvolutionL2; rw [kpWithIntList_eq, kpWithIntList_eq,
    kpEvolutionL2AuxPre_compile]
theorem checkSwLBucketCertL2Pre_eq (L rMin rMax tauNum tauDen : ℕ) (ratios : List IvInt) (trigIvs :
  List (IvInt × IvInt)) (pulses : List (SwLPulseRat L)) (pps : List KpPrePulse) (tailLbs : List ℤ)
  (survUb : ℤ) (hpv : pulses.all kpPulseValid = true) (hpps : kpCompilePulses L pulses = pps) :
  checkSwLBucketCertL2Pre L rMin rMax tauNum tauDen ratios trigIvs pps tailLbs survUb =
  checkSwLBucketCertL2 L rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb := by
  subst hpps; rw [← checkSwLBucketCertL2P_eq]; have hlen : (kpCompilePulses L pulses).length =
    pulses.length := (by simp [kpCompilePulses])
  unfold checkSwLBucketCertL2Pre checkSwLBucketCertL2P; simp only [kpWithIvList_eq,
    kpWithPairList_eq, kpWithIntList_eq, kpForceInt_eq, hlen, hpv, Bool.and_true,
    kpEvolutionL2Pre_compile]
end PrecompiledPulses
/-- Initial Heron overestimate `g₀ ≥ ⌊√n⌋` for `1 ≤ n ≤ 2^64`. -/
def fastIsqrtInit (n : ℕ) : ℕ :=
  cond (Nat.ble n 256) 16
    (cond (Nat.ble n 65536) 256
      (cond (Nat.ble n 16777216) 4096
        (cond (Nat.ble n 4294967296) 65536
          (cond (Nat.ble n 281474976710656) 16777216
            (cond (Nat.ble n 18446744073709551616) 4294967296 n)))))
/-- Pure-GMP structural-fuel Heron loop (`≤ 6` divisions; zero `WellFounded.fix`). -/
def fastIsqrtLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
      kpForceNat (Nat.div (Nat.add g (Nat.div n g)) 2) fun g' ↦
        cond (Nat.ble g g') g (fastIsqrtLoop fuel n g')
/-- Self-certifying pure-GMP `⌊√n⌋` (`O(1)` GMP ops in WHNF; lazy `Nat.sqrt`). -/
def fastFloorIsqrt (n : ℕ) : ℕ :=
  Nat.casesOn n 0 fun nPred ↦
    let n1 := Nat.add nPred 1
    kpForceNat (fastIsqrtLoop 40 n1 (fastIsqrtInit n1)) fun s ↦
      cond
        (Nat.ble (Nat.mul s s) n1 &&
          Nat.ble (Nat.add n1 1) (Nat.mul (Nat.add s 1) (Nat.add s 1)))
        s (Nat.sqrt n1)
/-- Self-certifying pure-GMP `⌈√n⌉` (`= kpCeilIsqrtNat n`). -/
def fastCeilIsqrt (n : ℕ) : ℕ :=
  kpForceNat (fastFloorIsqrt n) fun s ↦
    cond (Nat.beq (Nat.mul s s) n) s (Nat.add s 1)
/-- Pure-GMP `≤` on `ℤ` via constructor pattern-matching and `Nat.ble`. -/
def kpFastBleZ : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m
/-- Pure-GMP `=` on `ℤ` via constructor pattern-matching and `Nat.beq`. -/
def kpFastBeqZ : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.beq m n
  | .negSucc m, .negSucc n => Nat.beq m n
  | _, _ => false
/-- Pure-GMP `min` on `ℤ` via `cond` and `kpFastBleZ` (`0` `Decidable`). -/
def kpFastMinZ (a b : ℤ) : ℤ :=
  cond (kpFastBleZ a b) a b
/-- Pure-GMP `max` on `ℤ` via `cond` and `kpFastBleZ` (`0` `Decidable`). -/
def kpFastMaxZ (a b : ℤ) : ℤ :=
  cond (kpFastBleZ a b) b a
/-- Zero-closure pure-GMP tail-recursive sum of squared magnitudes. -/
def kpSumSqAbsFast : List ℤ → ℕ → ℕ
  | [], acc => acc
  | .ofNat n :: cjs, acc =>
      kpSumSqAbsFast cjs (Nat.add acc (Nat.mul n n))
  | .negSucc n :: cjs, acc =>
      let m := Nat.add n 1
      kpSumSqAbsFast cjs (Nat.add acc (Nat.mul m m))
/-- Pure-GMP `Int.negOfNat` via `cond` and `Nat.sub` (`0` `Nat.succ`). -/
def kpFastNegOfNat (n : ℕ) : ℤ :=
  cond (Nat.beq n 0) (.ofNat 0) (kpForceNat (Nat.sub n 1) Int.negSucc)
/-- Pure-GMP `Int.subNatNat` via direct `Nat.sub` (`0` `HSub.hSub`). -/
def kpFastSubNatNat (m n : ℕ) : ℤ :=
  match Nat.sub n m with
  | 0 => kpForceNat (Nat.sub m n) Int.ofNat
  | .succ k => .negSucc k
/-- Pure-GMP `Int.neg` preserving `Literal.natVal` (`Nat.add n 1`). -/
def kpFastNegZ : ℤ → ℤ
  | .ofNat n => kpFastNegOfNat n
  | .negSucc n => kpForceNat (Nat.add n 1) Int.ofNat
/-- Pure-GMP `Int.add` preserving `Literal.natVal` (`0` `Nat.succ`). -/
def kpFastAddZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => kpForceNat (Nat.add m n) Int.ofNat
  | .ofNat m, .negSucc n => kpFastSubNatNat m (Nat.add n 1)
  | .negSucc m, .ofNat n => kpFastSubNatNat n (Nat.add m 1)
  | .negSucc m, .negSucc n => kpForceNat (Nat.add (Nat.add m n) 1) Int.negSucc
/-- Pure-GMP `Int.sub` preserving `Literal.natVal`. -/
def kpFastSubZ (x y : ℤ) : ℤ :=
  kpFastAddZ x (kpFastNegZ y)
/-- Pure-GMP `Int.mul` preserving `Literal.natVal` (`0` `Nat.succ`). -/
def kpFastMulZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => kpForceNat (Nat.mul m n) Int.ofNat
  | .ofNat m, .negSucc n => kpFastNegOfNat (Nat.mul m (Nat.add n 1))
  | .negSucc m, .ofNat n => kpFastNegOfNat (Nat.mul (Nat.add m 1) n)
  | .negSucc m, .negSucc n => kpForceNat (Nat.mul (Nat.add m 1) (Nat.add n 1)) Int.ofNat
/-- Pure-GMP `Int.ediv` preserving `Literal.natVal` (`0` `Nat.succ`). -/
def kpFastEdivZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => kpForceNat (Nat.div m n) Int.ofNat
  | .ofNat m, .negSucc n => kpFastNegOfNat (Nat.div m (Nat.add n 1))
  | .negSucc m, .ofNat n =>
      cond (Nat.beq n 0) (.ofNat 0) (kpForceNat (Nat.div m n) Int.negSucc)
  | .negSucc m, .negSucc n => kpForceNat (Nat.add (Nat.div m (Nat.add n 1)) 1) Int.ofNat
/-- Pure-GMP ceiling division `-((-x) / y)` preserving `Literal.natVal`. -/
def kpFastCeilDiv (x y : ℤ) : ℤ :=
  kpFastNegZ (kpFastEdivZ (kpFastNegZ x) y)
/-- Direct `ℕ` ceiling division `⌈n / 10^9⌉` as `ℤ` (`0` `Int.ediv`). -/
def kpNatCeilDivScale (n : ℕ) : ℤ :=
  kpForceNat (Nat.div (Nat.add n 999999999) 1000000000) Int.ofNat
/-- Direct `ℕ` floor division `⌊(-n) / 10^9⌋` as `ℤ` (`0` `Int.ediv`). -/
def kpNegFloorDivScale (n : ℕ) : ℤ :=
  kpFastNegOfNat (Nat.div (Nat.add n 999999999) 1000000000)
/-- Direct `ℕ` ceiling division `⌈(-n) / 10^9⌉` as `ℤ` (`0` `Int.ediv`). -/
def kpNegCeilDivScale (n : ℕ) : ℤ :=
  kpFastNegOfNat (Nat.div n 1000000000)
/-- Pure-GMP `10^9`-scale interval addition. -/
def kpIvAddFast (a b : IvInt) : IvInt :=
  match a, b with
  | (a1, a2), (b1, b2) => (kpFastAddZ a1 b1, kpFastAddZ a2 b2)
/-- Pure-GMP `10^9`-scale interval subtraction. -/
def kpIvSubFast (a b : IvInt) : IvInt :=
  match a, b with
  | (a1, a2), (b1, b2) => (kpFastSubZ a1 b2, kpFastSubZ a2 b1)
/-- General `2`-mul fallback for `a * (z, z)`. -/
def kpMulIvPtFastCore (a1 a2 z : ℤ) : IvInt :=
  kpForceInt (kpFastMulZ a1 z) fun p1 ↦
    kpForceInt (kpFastMulZ a2 z) fun p3 ↦
      cond (kpFastBleZ p1 p3)
        (kpFastEdivZ p1 (.ofNat 1000000000),
         kpFastCeilDiv p3 (.ofNat 1000000000))
        (kpFastEdivZ p3 (.ofNat 1000000000),
         kpFastCeilDiv p1 (.ofNat 1000000000))
/-- Zero-closure `Nat`-direct point-interval product `a * (z, z)`. -/
def kpMulIvPtFast (a : IvInt) (z : ℤ) : IvInt :=
  match a with
  | (.ofNat c1, .ofNat c2) =>
      cond (Nat.ble c1 c2)
        (match z with
        | .ofNat m =>
            (kpForceNat (Nat.div (Nat.mul c1 m) 1000000000) Int.ofNat,
             kpNatCeilDivScale (Nat.mul c2 m))
        | .negSucc m =>
            let m1 := Nat.add m 1
            (kpNegFloorDivScale (Nat.mul c2 m1),
             kpNegCeilDivScale (Nat.mul c1 m1)))
        (kpMulIvPtFastCore (.ofNat c1) (.ofNat c2) z)
  | (.ofNat c1, .negSucc c2) => kpMulIvPtFastCore (.ofNat c1) (.negSucc c2) z
  | (.negSucc c1, .ofNat c2) =>
      match z with
      | .ofNat m =>
          (kpNegFloorDivScale (Nat.mul (Nat.add c1 1) m),
           kpNatCeilDivScale (Nat.mul c2 m))
      | .negSucc m =>
          (kpNegFloorDivScale (Nat.mul c2 (Nat.add m 1)),
           kpNatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add m 1)))
  | (.negSucc c1, .negSucc c2) =>
      cond (Nat.ble c2 c1)
        (match z with
        | .ofNat m =>
            (kpNegFloorDivScale (Nat.mul (Nat.add c1 1) m),
             kpNegCeilDivScale (Nat.mul (Nat.add c2 1) m))
        | .negSucc m =>
            let m1 := Nat.add m 1
            (kpForceNat (Nat.div (Nat.mul (Nat.add c2 1) m1) 1000000000) Int.ofNat,
             kpNatCeilDivScale (Nat.mul (Nat.add c1 1) m1)))
        (kpMulIvPtFastCore (.negSucc c1) (.negSucc c2) z)
/-- General `4`-comparison tournament fallback for `a * b`. -/
def kpIvMulFastCore (a1 a2 b1 b2 : ℤ) : IvInt :=
  kpForceInt (kpFastMulZ a1 b1) fun p1 ↦
    kpForceInt (kpFastMulZ a1 b2) fun p2 ↦
      kpForceInt (kpFastMulZ a2 b1) fun p3 ↦
        kpForceInt (kpFastMulZ a2 b2) fun p4 ↦
          cond (kpFastBleZ p1 p2)
            (cond (kpFastBleZ p3 p4)
              (kpFastEdivZ (kpFastMinZ p1 p3) (.ofNat 1000000000),
               kpFastCeilDiv (kpFastMaxZ p2 p4) (.ofNat 1000000000))
              (kpFastEdivZ (kpFastMinZ p1 p4) (.ofNat 1000000000),
               kpFastCeilDiv (kpFastMaxZ p2 p3) (.ofNat 1000000000)))
            (cond (kpFastBleZ p3 p4)
              (kpFastEdivZ (kpFastMinZ p2 p3) (.ofNat 1000000000),
               kpFastCeilDiv (kpFastMaxZ p1 p4) (.ofNat 1000000000))
              (kpFastEdivZ (kpFastMinZ p2 p4) (.ofNat 1000000000),
               kpFastCeilDiv (kpFastMaxZ p1 p3) (.ofNat 1000000000)))
/-- Zero-closure `2`-mul `Nat`-direct `10^9`-scale interval product. -/
def kpIvMulFast (a b : IvInt) : IvInt :=
  match a with
  | (.ofNat c1, .ofNat c2) =>
      cond (Nat.ble c1 c2)
        (match b with
        | (.ofNat d1, .ofNat d2) =>
            cond (Nat.ble d1 d2)
              (kpForceNat (Nat.div (Nat.mul c1 d1) 1000000000) Int.ofNat,
               kpNatCeilDivScale (Nat.mul c2 d2))
              (kpIvMulFastCore (.ofNat c1) (.ofNat c2) (.ofNat d1) (.ofNat d2))
        | (.ofNat d1, .negSucc d2) =>
            kpIvMulFastCore (.ofNat c1) (.ofNat c2) (.ofNat d1) (.negSucc d2)
        | (.negSucc d1, .ofNat d2) =>
            (kpNegFloorDivScale (Nat.mul c2 (Nat.add d1 1)),
             kpNatCeilDivScale (Nat.mul c2 d2))
        | (.negSucc d1, .negSucc d2) =>
            cond (Nat.ble d2 d1)
              (kpNegFloorDivScale (Nat.mul c2 (Nat.add d1 1)),
               kpNegCeilDivScale (Nat.mul c1 (Nat.add d2 1)))
              (kpIvMulFastCore (.ofNat c1) (.ofNat c2) (.negSucc d1) (.negSucc d2)))
        (kpIvMulFastCore (.ofNat c1) (.ofNat c2) b.1 b.2)
  | (.ofNat c1, .negSucc c2) => kpIvMulFastCore (.ofNat c1) (.negSucc c2) b.1 b.2
  | (.negSucc c1, .ofNat c2) =>
      match b with
      | (.ofNat d1, .ofNat d2) =>
          cond (Nat.ble d1 d2)
            (kpNegFloorDivScale (Nat.mul (Nat.add c1 1) d2),
             kpNatCeilDivScale (Nat.mul c2 d2))
            (kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.ofNat d1) (.ofNat d2))
      | (.ofNat d1, .negSucc d2) =>
          kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.ofNat d1) (.negSucc d2)
      | (.negSucc d1, .ofNat d2) =>
          kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.negSucc d1) (.ofNat d2)
      | (.negSucc d1, .negSucc d2) =>
          cond (Nat.ble d2 d1)
            (kpNegFloorDivScale (Nat.mul c2 (Nat.add d1 1)),
             kpNatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add d1 1)))
            (kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.negSucc d1) (.negSucc d2))
  | (.negSucc c1, .negSucc c2) =>
      cond (Nat.ble c2 c1)
        (match b with
        | (.ofNat d1, .ofNat d2) =>
            cond (Nat.ble d1 d2)
              (kpNegFloorDivScale (Nat.mul (Nat.add c1 1) d2),
               kpNegCeilDivScale (Nat.mul (Nat.add c2 1) d1))
              (kpIvMulFastCore (.negSucc c1) (.negSucc c2) (.ofNat d1) (.ofNat d2))
        | (.ofNat d1, .negSucc d2) =>
            kpIvMulFastCore (.negSucc c1) (.negSucc c2) (.ofNat d1) (.negSucc d2)
        | (.negSucc d1, .ofNat d2) =>
            (kpNegFloorDivScale (Nat.mul (Nat.add c1 1) d2),
             kpNatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add d1 1)))
        | (.negSucc d1, .negSucc d2) =>
            cond (Nat.ble d2 d1)
              (kpForceNat
                (Nat.div (Nat.mul (Nat.add c2 1) (Nat.add d2 1)) 1000000000) Int.ofNat,
               kpNatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add d1 1)))
              (kpIvMulFastCore (.negSucc c1) (.negSucc c2) (.negSucc d1) (.negSucc d2)))
        (kpIvMulFastCore (.negSucc c1) (.negSucc c2) b.1 b.2)
/-- Zero-closure `Nat`-direct `10^9`-scale interval squaring (`0` `Nat.succ`). -/
def kpIvSqFast (a : IvInt) : IvInt :=
  match a with
  | (.ofNat c1, .ofNat c2) =>
      (kpForceNat (Nat.div (Nat.mul c1 c1) 1000000000) Int.ofNat,
       kpNatCeilDivScale (Nat.mul c2 c2))
  | (.ofNat c1, .negSucc c2) =>
      let c2p := Nat.add c2 1
      (kpForceNat (Nat.div (Nat.mul c1 c1) 1000000000) Int.ofNat,
       kpNatCeilDivScale (Nat.mul c2p c2p))
  | (.negSucc c1, .ofNat c2) =>
      let c1p := Nat.add c1 1
      let m := cond (Nat.ble c1p c2) c2 c1p
      (.ofNat 0, kpNatCeilDivScale (Nat.mul m m))
  | (.negSucc c1, .negSucc c2) =>
      let c1p := Nat.add c1 1
      let c2p := Nat.add c2 1
      (kpForceNat (Nat.div (Nat.mul c2p c2p) 1000000000) Int.ofNat,
       kpNatCeilDivScale (Nat.mul c1p c1p))
/-- Pure-GMP `10^9`-scale outward rational interval (`0` `Nat.succ`). -/
def kpIvRatDivFast (num den : ℤ) : IvInt :=
  kpForceInt (kpFastMulZ num (.ofNat 1000000000)) fun sc ↦
    kpForceInt (kpFastEdivZ sc den) fun qlo ↦
      kpForceInt (kpFastCeilDiv sc den) fun qhi ↦ (qlo, qhi)
/-- Pure-GMP `10^9`-scale Pythagorean `(cos, sin)` intervals (`0` `Nat.succ`). -/
def kpIvPythagFast (uNum uDen : ℤ) : IvInt × IvInt :=
  kpForceInt uNum fun u ↦
    kpForceInt uDen fun d0 ↦
      kpForceInt (kpFastMulZ d0 d0) fun dSq ↦
        kpForceInt (kpFastMulZ u u) fun uSq ↦
          kpForceInt (kpFastAddZ dSq uSq) fun d ↦
            kpForceIv (kpIvRatDivFast (kpFastSubZ dSq uSq) d) fun cIv ↦
              kpForceIv
                (kpIvRatDivFast
                  (kpFastMulZ (kpFastMulZ (.ofNat 2) u) d0) d)
                fun sIv ↦ (cIv, sIv)
/-- Direct `O(m)` pure-GMP Pythagorean list builder (`0` `Nat.succ`). -/
def kpUPythagsGoFast (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) :
    ∀ (rem : ℕ), rem ≤ m → List (IvInt × IvInt)
  | 0, _ => []
  | rem + 1, h =>
      let idx := Nat.sub m (Nat.add rem 1)
      have hlt : idx < m :=
        Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ rem) h) (Nat.zero_lt_succ rem)
      kpForcePair (kpIvPythagFast (f ⟨idx, hlt⟩) uDen) fun py ↦
        match kpUPythagsGoFast uDen m f rem (Nat.le_of_succ_le h) with
        | [] => [py]
        | hd :: tl => py :: hd :: tl
/-- Pure-GMP replacement for `kpUPythags`. -/
def kpUPythagsFast (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : List (IvInt × IvInt) :=
  kpUPythagsGoFast uDen m f m le_rfl
/-- Pure-GMP weak-measurement cosine interval for a pulse `p`. -/
def kpPulseCvFast {L : ℕ} (p : SwLPulseRat L) : IvInt :=
  cond (kpFastBeqZ p.vNum (.ofNat 0)) (.ofNat 1000000000, .ofNat 1000000000)
    (kpIvPythagFast p.vNum (Int.ofNat p.uvDen)).1
/-- Pure-GMP single-pulse compiler into `(cv, ups)` (`0` `Nat.succ`). -/
def kpCompilePulseFast : ∀ (L : ℕ), SwLPulseRat L → KpPrePulse
  | 0, p => kpForceIv (kpPulseCvFast p) fun cv ↦ (cv, [])
  | m + 1, p =>
      kpForceIv (kpPulseCvFast p) fun cv ↦
        kpWithPairList (kpUPythagsFast (Int.ofNat p.uvDen) m p.uNum) fun ups ↦
          (cv, ups)
/-- Pure-GMP schedule pulse compiler (`= kpCompilePulses L ps`). -/
def kpCompilePulsesFast (L : ℕ) (ps : List (SwLPulseRat L)) : List KpPrePulse :=
  ps.map (kpCompilePulseFast L)
/-- Single-match uncons for `List (IvInt × IvInt)` (`0` `OfNat` fallback). -/
def kpUnconsTrig {α : Type} (ts : List (IvInt × IvInt))
    (k : IvInt → IvInt → List (IvInt × IvInt) → α) : α :=
  match ts with
  | (cw, sw) :: ts' => k cw sw ts'
  | [] => k (.ofNat 0, .ofNat 0) (.ofNat 0, .ofNat 0) []
/-- Single-match 2-element uncons for `List ℤ` (`0` `OfNat` fallback). -/
def kpUncons2Z {α : Type} (cs : List ℤ) (k : ℤ → ℤ → List ℤ → α) : α :=
  match cs with
  | ce :: co :: cs' => k ce co cs'
  | [ce] => k ce (.ofNat 0) []
  | [] => k (.ofNat 0) (.ofNat 0) []
/-- Head interval with `(.ofNat 0,.ofNat 0)` fallback. -/
def kpHeadIvF : List IvInt → IvInt
  | x :: _ => x
  | [] => (.ofNat 0, .ofNat 0)
/-- Single-match 1-element uncons for `List IvInt`. -/
def kpUncons1Iv {α : Type} (ss : List IvInt) (k : IvInt → List IvInt → α) : α :=
  match ss with
  | h0 :: ss' => k h0 ss'
  | [] => k (.ofNat 0, .ofNat 0) []
/-- Single-match 2-element uncons for `List IvInt`. -/
def kpUncons2Iv {α : Type} (ss : List IvInt)
    (k : IvInt → IvInt → List IvInt → α) : α :=
  match ss with
  | lv :: rv :: ss' => k lv rv ss'
  | [lv] => k lv (.ofNat 0, .ofNat 0) []
  | [] => k (.ofNat 0, .ofNat 0) (.ofNat 0, .ofNat 0) []
/-- Pure-GMP single-pass `O(L)` Grover plane walk (`2`-mul point products). -/
def kpGroverWalkFast : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, ts, cs =>
      kpUnconsTrig ts fun cw sw ts' ↦
        kpUncons2Z cs fun ce co cs' ↦
          kpForceIv
            (kpIvSubFast (kpMulIvPtFast cw ce) (kpMulIvPtFast sw co))
            fun e' ↦
              kpForceIv
                (kpIvAddFast (kpMulIvPtFast sw ce) (kpMulIvPtFast cw co))
                fun o' ↦
                  match kpGroverWalkFast k ts' cs' with
                  | [] => [e', o']
                  | hd :: tl => e' :: o' :: hd :: tl
/-- Pure-GMP single-pass `O(L)` Pieri + weak-measurement walk (`0` `Nat.succ`). -/
def kpPieriWalkFast (cv : IvInt) : ℕ → List (IvInt × IvInt) → List IvInt → List IvInt
  | 0, _, ss =>
      kpForceIv (kpIvMulFast cv (kpHeadIvF ss)) fun top ↦ [top]
  | k + 1, us, ss =>
      kpUnconsTrig us fun cu su us' ↦
        kpUncons2Iv ss fun lv rv ss' ↦
          kpForceIv
            (kpIvSubFast (kpIvMulFast cu lv) (kpIvMulFast su rv))
            fun l' ↦
              kpForceIv
                (kpIvAddFast (kpIvMulFast su lv) (kpIvMulFast cu rv))
                fun r' ↦
                  match kpPieriWalkFast cv k us' ss' with
                  | [] => [l', r']
                  | hd :: tl => l' :: r' :: hd :: tl
/-- Pure-GMP Pieri + weak-measurement step over `KpPrePulse`. -/
def kpPieriAndWeakPreFast : ℕ → KpPrePulse → List IvInt → List IvInt
  | 0, _, _ => []
  | m + 1, (cv, ups), naIv =>
      kpUncons1Iv naIv fun h0 naTail ↦
        match kpPieriWalkFast cv m ups naTail with
        | [] => [h0]
        | hd :: tl => h0 :: hd :: tl
/-- CPS `O(L)` recentering and squared-radius sum with spine-forced `cs`. -/
def kpRecenterAndRadSqCPS {α : Type} : List IvInt → (List ℤ → ℕ → α) → α
  | [], k => k [] 0
  | (lo, hi) :: ivs, k =>
      kpForceInt (kpFastEdivZ (kpFastAddZ lo hi) (.ofNat 2)) fun mid ↦
        kpForceNat (kpFastMaxZ (kpFastSubZ mid lo)
          (kpFastSubZ hi mid)).toNat fun rad ↦
          kpRecenterAndRadSqCPS ivs fun cs acc ↦
            let acc' := Nat.add (Nat.mul rad rad) acc
            match cs with
            | [] => k [mid] acc'
            | hd :: tl => k (mid :: hd :: tl) acc'
/-- CPS pure-GMP terminal interval extraction (`0` `Nat.succ`). -/
def kpTerminalStateL2FastCPS {α : Type} (cVec : List ℤ) (rho : ℕ) (survUb : ℤ)
    (k : List IvInt → IvInt → ℤ → α) : α :=
  kpForceNat (kpSumSqAbsFast cVec 0) fun normSqK ↦
    kpForceNat (fastCeilIsqrt normSqK) fun normKUb ↦
      kpForceNat (Nat.sub (fastFloorIsqrt normSqK) rho) fun normKLb ↦
        kpForceNat (Nat.add normKUb rho) fun sumR ↦
          kpForceInt
            (kpFastMinZ (.ofNat 1000000000)
              (kpNatCeilDivScale (Nat.mul sumR sumR)))
            fun oneMinusCumUb ↦
              kpForceInt (kpFastMaxZ (.ofNat 0)
                (kpFastSubZ (.ofNat 1000000000) oneMinusCumUb))
                fun cumLo ↦
                  kpForceInt
                    (kpFastMinZ (.ofNat 1000000000)
                      (kpFastSubZ (.ofNat 1000000000)
                        (kpForceNat (Nat.div (Nat.mul normKLb normKLb) 1000000000) Int.ofNat)))
                    fun cumHi ↦
                      let rhoZ := Int.ofNat rho
                      kpWithIvList
                        (cVec.map fun cj ↦ (kpFastSubZ cj rhoZ,
                          kpFastAddZ cj rhoZ))
                        fun stIv ↦
                          kpForceInt survUb fun survOut ↦
                            k stIv (cumLo, cumHi) survOut
/-- CPS pure-GMP `L2Ball` conveyor pulse step (`0` list re-walks). -/
def kpPulseStepL2PreFastCPS {α : Type} (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) (pp : KpPrePulse)
    (k : List ℤ → ℕ → ℤ → α) : α :=
  kpForceNat (kpSumSqAbsFast cVec 0) fun normSqC ↦
    kpForceNat (fastCeilIsqrt normSqC) fun normCUb ↦
      kpForceNat (Nat.add normCUb rho) fun sumR ↦
        kpForceInt
          (kpFastMinZ (.ofNat 1000000000)
            (kpNatCeilDivScale (Nat.mul sumR sumR)))
          fun oneMinusCumUb ↦
            kpForceInt (kpFastAddZ survUb oneMinusCumUb) fun survUb' ↦
              kpRecenterAndRadSqCPS
                (kpPieriAndWeakPreFast L pp (kpGroverWalkFast L trigIvs cVec))
                fun cNext radSqSum ↦
                  kpForceNat (Nat.add rho (fastCeilIsqrt radSqSum)) fun rho' ↦
                    k cNext rho' survUb'
/-- CPS pure-GMP multi-pulse `L2Ball` loop (`0` `kpWithL2State` blowup). -/
def kpEvolutionL2AuxPreFastCPS {α : Type} (L : ℕ)
    (trigIvs : List (IvInt × IvInt)) (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List KpPrePulse → (List ℤ → ℕ → ℤ → α) → α
  | [], k => k cVec rho survUb
  | pp :: pps, k =>
      kpPulseStepL2PreFastCPS L trigIvs cVec rho survUb pp fun cNext rho' survUb' ↦
        kpEvolutionL2AuxPreFastCPS L trigIvs cNext rho' survUb' pps k
/-- CPS pure-GMP multi-pulse `L2Ball` trajectory. -/
def kpEvolutionL2PreFastCPS {α : Type} (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (pps : List KpPrePulse) (k : List ℤ → ℕ → ℤ → α) : α :=
  kpWithIntList (.ofNat 1000000000 :: List.replicate (Nat.sub (Nat.mul 2 L) 1) (.ofNat 0))
    fun cInit ↦ kpEvolutionL2AuxPreFastCPS L trigIvs cInit 0 (.ofNat 0) pps k
/-- Pure-GMP linear orbit projection accumulator (`0` `Nat.succ`). -/
def kpOrbLinAuxFast (o : ℕ) : ℕ → IvInt → List IvInt → IvInt
  | _, acc, [] => acc
  | j, acc, sj :: sjs =>
      let mIv : IvInt :=
        cond (Nat.beq j o) (.ofNat 999999999, .ofNat 1000000000) (.negSucc 0, .ofNat 1)
      kpForceIv (kpIvAddFast acc (kpIvMulFast sj mIv)) fun acc' ↦
        kpOrbLinAuxFast o (Nat.add j 1) acc' sjs
/-- Pure-GMP squared orbit projection interval (`0` `Nat.succ`). -/
def kpOrbSqIvFast (stIv : List IvInt) (o : ℕ) : IvInt :=
  kpIvSqFast (kpOrbLinAuxFast o 0 (.ofNat 0, .ofNat 0) stIv)
/-- Pure-GMP descending suffix tail intervals (`0` `Nat.succ`). -/
def kpTailSuffixIvsFast (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ℕ → List IvInt
  | 0 => []
  | m + 1 =>
      let c := Nat.sub L m
      cond (Nat.beq c L)
        (kpForceIv
          (kpIvAddFast (kpOrbSqIvFast stIv (Nat.sub (Nat.mul 2 L) 1))
            (kpIvMulFast cumIv (kpIvSqFast (.ofNat 999999999, .ofNat 1000000000))))
          fun topIv ↦ [topIv])
        (match kpTailSuffixIvsFast L stIv cumIv m with
        | [] => []
        | nextIv :: rest =>
            let phIv := kpIvAddFast
              (kpIvAddFast (kpOrbSqIvFast stIv (Nat.sub (Nat.mul 2 c) 1))
                (kpOrbSqIvFast stIv (Nat.mul 2 c)))
              (kpIvMulFast cumIv (.ofNat 0, .ofNat 2))
            kpForceIv (kpIvAddFast phIv nextIv) fun curIv ↦ curIv :: nextIv :: rest)
/-- Pure-GMP clamped monotone lower bounds (`0` `bleZ` `Int.sub`). -/
def kpClampTailLbsFast : List IvInt → List ℤ
  | [] => []
  | [ivL] =>
      match ivL with
      | (lo, _) => kpForceInt (kpFastMaxZ (.ofNat 0) lo) fun v ↦ [v]
  | iv :: rest =>
      match iv, kpClampTailLbsFast rest with
      | (lo, _), [] => kpForceInt (kpFastMaxZ (.ofNat 0) lo) fun v ↦ [v]
      | (lo, _), nextLb :: lbs =>
          kpForceInt (kpFastMaxZ nextLb (kpFastMinZ (.ofNat 1000000000) lo))
            fun curLb ↦ curLb :: nextLb :: lbs
/-- Pure-GMP `10^18`-stepped double-angle trig checker (`0` `Nat.succ`). -/
def kpCheckSwLTrigRatFast (a d b e cLo cHi sLo sHi : ℤ) : Bool :=
  let s18 : ℤ := .ofNat 1000000000000000000
  let sc : ℤ := .ofNat 1000000000
  kpForceInt (kpFastEdivZ (kpFastMulZ a s18) d) fun qLoLo ↦
    kpForceInt (kpFastCeilDiv (kpFastMulZ a s18) d) fun qLoHi ↦
      kpForceInt (kpFastCeilDiv (kpFastMulZ b s18) e) fun qHiHi ↦
        kpForceInt
          (kpFastEdivZ
            (kpFastMulZ qLoLo
              (kpFastSubZ (kpFastMulZ (kpFastMulZ (.ofNat 24) s18) s18)
                (kpFastMulZ qLoLo qLoLo)))
            (kpFastMulZ (kpFastMulZ (.ofNat 48) s18) s18))
          fun s2Lo ↦
            kpForceInt
              (kpFastSubZ s18
                (kpFastCeilDiv (kpFastMulZ qLoHi qLoHi)
                  (kpFastMulZ (.ofNat 32) s18)))
              fun c4Lo ↦
                kpForceInt
                  (kpFastSubZ
                    (kpFastEdivZ (kpFastMulZ (kpFastMulZ (.ofNat 2) c4Lo) c4Lo)
                      s18)
                    s18)
                  fun c2Lo ↦
                    kpForceInt
                      (kpFastSubZ s18
                        (kpFastCeilDiv (kpFastMulZ qHiHi qHiHi)
                          (kpFastMulZ (.ofNat 128) s18)))
                      fun c8H ↦
                        kpForceInt
                          (kpFastSubZ
                            (kpFastEdivZ
                              (kpFastMulZ (kpFastMulZ (.ofNat 2) c8H) c8H) s18)
                            s18)
                          fun c4H ↦
                            kpForceInt
                              (kpFastSubZ
                                (kpFastEdivZ
                                  (kpFastMulZ (kpFastMulZ (.ofNat 2) c4H) c4H) s18)
                                s18)
                              fun c2H ↦
                                kpForceInt
                                  (kpFastSubZ
                                    (kpFastEdivZ
                                      (kpFastMulZ (kpFastMulZ (.ofNat 2) c2H) c2H)
                                      s18)
                                    s18)
                                  fun c1H ↦
                                    kpFastBleZ (.ofNat 1) a &&
                                    (kpFastBleZ (.ofNat 1) d &&
                                    (kpFastBleZ (.ofNat 0) b &&
                                    (kpFastBleZ (.ofNat 1) e &&
                                    (kpFastBleZ b e &&
                                    (kpFastBleZ (.ofNat 0) cLo &&
                                    (kpFastBleZ (.ofNat 0) cHi &&
                                    (kpFastBleZ (.ofNat 0) sLo &&
                                    (kpFastBleZ (.ofNat 0) sHi &&
                                    (kpFastBleZ (.ofNat 1) qLoLo &&
                                    (kpFastBleZ qLoHi s18 &&
                                    (kpFastBleZ qHiHi s18 &&
                                    (kpFastBleZ (.ofNat 0) s2Lo &&
                                    (kpFastBleZ (.ofNat 0) c4Lo &&
                                    (kpFastBleZ (.ofNat 0) c2Lo &&
                                    (kpFastBleZ
                                      (kpFastMulZ (kpFastMulZ sLo s18) s18)
                                      (kpFastMulZ
                                        (kpFastMulZ (kpFastMulZ (.ofNat 2) s2Lo) c2Lo)
                                        sc) &&
                                    (kpFastBleZ (.ofNat 0) c8H &&
                                    (kpFastBleZ (.ofNat 0) c4H &&
                                    (kpFastBleZ (.ofNat 0) c2H &&
                                    (kpFastBleZ (kpFastMulZ cLo s18)
                                      (kpFastMulZ c1H sc) &&
                                    (kpFastBleZ (kpFastMulZ sc sc)
                                      (kpFastAddZ (kpFastMulZ cLo cLo)
                                        (kpFastMulZ sHi sHi)) &&
                                     kpFastBleZ (kpFastMulZ sc sc)
                                      (kpFastAddZ (kpFastMulZ sLo sLo)
                                        (kpFastMulZ cHi cHi))))))))))))))))))))))
/-- Pure-GMP stratum angle-ratio checker (`0` `bleZ` `Int.sub`). -/
def kpCheckSwLStratumRatioFast (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  let s20 : ℤ := .ofNat 100000000000000000000
  let s20m1 : ℤ := kpFastSubZ s20 (.ofNat 1)
  let sc : ℤ := .ofNat 1000000000
  let sc2 : ℤ := kpFastMulZ sc sc
  let rMinZ : ℤ := Int.ofNat rMin
  let rMaxZ : ℤ := Int.ofNat rMax
  let swZ : ℤ := Int.ofNat shiftW
  let rLo1 : ℤ := kpFastAddZ ratioLo (.ofNat 1)
  let rHi1 : ℤ := kpFastSubZ ratioHi (.ofNat 1)
  Nat.ble (Nat.add shiftW 1) rMin &&
  (Nat.ble rMin rMax &&
  (Nat.ble rMax 1024 &&
  (Nat.ble 1 shiftW &&
  (Nat.ble shiftW 7 &&
  (kpFastBleZ (.ofNat 1) ratioLo &&
  (kpFastBleZ (.ofNat 2) ratioHi &&
  (kpFastBleZ ratioHi sc &&
  (kpFastBleZ (kpFastMulZ (kpFastMulZ rLo1 rLo1) rMinZ)
    (kpFastMulZ sc2 (kpFastSubZ rMinZ swZ)) &&
  (kpFastBleZ (kpFastMulZ sc2 (kpFastSubZ rMaxZ swZ))
    (kpFastMulZ (kpFastSubZ (kpFastMulZ rHi1 rHi1) swZ) rMaxZ) &&
  (kpFastBleZ (kpFastMulZ ratioLo s20) (kpFastMulZ rLo1 s20m1) &&
   kpFastBleZ (kpFastMulZ rHi1 s20) (kpFastMulZ ratioHi s20m1)))))))))))
/-- Pure-GMP `2 ≤ L ≤ 8` bucket angle checker (`0` `Nat.succ`). -/
def kpCheckSwLBucketAnglesFast (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := .ofNat 100000000000
  let tnZ : ℤ := Int.ofNat tauNum
  let tdZ : ℤ := Int.ofNat tauDen
  kpForceInt (kpFastAddZ (kpFastMulZ tnZ s11) tdZ) fun q1HiNum ↦
    kpForceInt (kpFastMulZ tdZ s11) fun q1HiDen ↦
      (Nat.ble 2 L &&
      (Nat.ble L 8 &&
      (Nat.ble L rMin &&
      (Nat.ble rMin rMax &&
      (Nat.ble rMax 1024 &&
      (Nat.ble 1 tauNum &&
      (Nat.ble 1 tauDen &&
      (Nat.beq ratios.length (Nat.sub L 1) &&
       Nat.beq trigIvs.length L)))))))) &&
      match trigIvs with
      | [] => false
      | ((c0Lo, c0Hi), (s0Lo, s0Hi)) :: restTrig =>
          kpCheckSwLTrigRatFast tnZ tdZ q1HiNum q1HiDen c0Lo c0Hi s0Lo s0Hi &&
          kpAllRange (fun idx ↦
            let w := Nat.add idx 1
            match ratios.getD idx (.ofNat 0, .ofNat 0),
                restTrig.getD idx ((.ofNat 0, .ofNat 0), (.ofNat 0, .ofNat 0)) with
            | (rLo, rHi), ((cLo, cHi), (sLo, sHi)) =>
                kpCheckSwLStratumRatioFast rMin rMax w rLo rHi &&
                kpCheckSwLTrigRatFast
                  (kpFastMulZ tnZ rLo) (kpFastMulZ tdZ (.ofNat 1000000000))
                  (kpFastMulZ q1HiNum rHi)
                  (kpFastMulZ q1HiDen (.ofNat 1000000000))
                  cLo cHi sLo sHi) (Nat.sub L 1)
/-- Pure-GMP `2 ≤ L ≤ 8` `L2Ball` bucket checker (`0` `Nat.succ` / `Int.*`). -/
def checkSwLBucketCertL2PreFast (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (pps : List KpPrePulse) (tailLbs : List ℤ) (survUb : ℤ) : Bool :=
  kpWithIvList ratios fun rats' ↦
    kpWithPairList trigIvs fun trigs' ↦
      kpWithIntList tailLbs fun tails' ↦
        kpForceInt survUb fun surv' ↦
          let plen := pps.length
          let t0 := tails'.getD 0 (.ofNat 0)
          let tLast := tails'.getD (Nat.sub L 1) (.ofNat 0)
          (Nat.ble 1 plen &&
          (Nat.ble plen 250 &&
          (Nat.beq tails'.length L &&
          (kpFastBleZ (.ofNat 0) surv' &&
          (kpFastBleZ (.ofNat 1) t0 &&
          (kpFastBleZ t0 (.ofNat 1000000000) &&
           kpFastBleZ (.ofNat 0) tLast)))))) &&
          kpAllRange (fun i ↦ kpFastBleZ (tails'.getD (Nat.add i 1) (.ofNat 0))
            (tails'.getD i (.ofNat 0))) (Nat.sub L 1) &&
          kpCheckSwLBucketAnglesFast L rMin rMax tauNum tauDen rats' trigs' &&
          kpEvolutionL2PreFastCPS L trigs' pps fun cVec rho survEvol ↦
            kpTerminalStateL2FastCPS cVec rho survEvol fun stIv cumIv survOut ↦
              kpForceIv
                (kpIvAddFast (kpOrbSqIvFast stIv 0)
                  (kpIvMulFast cumIv (.ofNat 0, .ofNat 1)))
                fun p0Iv ↦
                  kpForceIv
                    (kpIvSubFast (.ofNat 1000000000, .ofNat 1000000000) p0Iv)
                    fun t1Iv ↦
                      kpWithIvList
                        (t1Iv :: kpTailSuffixIvsFast L stIv cumIv (Nat.sub L 1))
                        fun tailIvs ↦
                          kpWithIntList (kpClampTailLbsFast tailIvs) fun certLbs ↦
                            (kpFastBleZ survOut surv' &&
                             Nat.beq certLbs.length L) &&
                            kpAllRange (fun i ↦
                              kpFastBleZ (tails'.getD i (.ofNat 0))
                                (certLbs.getD i (.ofNat 0))) L
theorem fastFloorIsqrt_eq (n : ℕ) : fastFloorIsqrt n = Nat.sqrt n := by
  cases n with
  | zero => rfl
  | succ nPred =>
    unfold fastFloorIsqrt; dsimp only; rw [kpForceNat_eq]
    set s := fastIsqrtLoop 40 (Nat.add nPred 1) (fastIsqrtInit (Nat.add nPred 1))
    cases hcond : (Nat.ble (Nat.mul s s) (Nat.add nPred 1) && Nat.ble (Nat.add (Nat.add nPred 1) 1)
      (Nat.mul (Nat.add s 1) (Nat.add s 1)))
    · rfl
    · change s = Nat.sqrt (nPred + 1); simp only [Bool.and_eq_true, swLNatBle_eq_decide,
        decide_eq_true_eq, nat_add_eq, nat_mul_eq] at hcond; exact Nat.eq_sqrt.mpr ⟨hcond.1,
        by omega⟩
theorem fastCeilIsqrt_eq (n : ℕ) : fastCeilIsqrt n = kpCeilIsqrtNat n := by
  unfold fastCeilIsqrt kpCeilIsqrtNat; rw [fastFloorIsqrt_eq]
theorem kpFastBleZ_eq (a b : ℤ) : kpFastBleZ a b = kpBleZ a b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [kpBleZ_eq_decide, Bool.eq_iff_iff]; simp only [kpFastBleZ, swLNatBle_eq_decide,
        decide_eq_true_eq, Int.ofNat_eq_natCast]; omega
    | negSucc n =>
      symm; rw [kpBleZ_eq_decide, show kpFastBleZ (.ofNat m) (.negSucc n) = false from rfl]
      rw [decide_eq_false_iff_not, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      symm; rw [kpBleZ_eq_decide, show kpFastBleZ (.negSucc m) (.ofNat n) = true from rfl]
      rw [decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
    | negSucc n =>
      rw [kpBleZ_eq_decide, Bool.eq_iff_iff]; simp only [kpFastBleZ, swLNatBle_eq_decide,
        decide_eq_true_eq, Int.negSucc_eq]; omega
theorem kpFastBeqZ_eq (a b : ℤ) : kpFastBeqZ a b = kpBeqZ a b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [kpBeqZ_eq_decide, Bool.eq_iff_iff]; simp only [kpFastBeqZ, swLNatBeq_eq_decide,
        decide_eq_true_eq, Int.ofNat_eq_natCast]; omega
    | negSucc n =>
      symm; rw [kpBeqZ_eq_decide, show kpFastBeqZ (.ofNat m) (.negSucc n) = false from rfl]
      rw [decide_eq_false_iff_not, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      symm; rw [kpBeqZ_eq_decide, show kpFastBeqZ (.negSucc m) (.ofNat n) = false from rfl]
      rw [decide_eq_false_iff_not, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
    | negSucc n =>
      rw [kpBeqZ_eq_decide, Bool.eq_iff_iff]; simp only [kpFastBeqZ, swLNatBeq_eq_decide,
        decide_eq_true_eq, Int.negSucc_eq]; omega
theorem kpFastMinZ_eq (a b : ℤ) : kpFastMinZ a b = kpMinZ a b := by
  unfold kpFastMinZ kpMinZ; rw [kpFastBleZ_eq]
theorem kpFastMaxZ_eq (a b : ℤ) : kpFastMaxZ a b = kpMaxZ a b := by
  unfold kpFastMaxZ kpMaxZ; rw [kpFastBleZ_eq]
theorem kpMinZ_of_le {x y : ℤ} (h : x ≤ y) : kpMinZ x y = x := by
  unfold kpMinZ; rw [kpBleZ_eq_decide]; simp [h]
theorem kpMinZ_of_ge {x y : ℤ} (h : y ≤ x) : kpMinZ x y = y := by
  unfold kpMinZ; rw [kpBleZ_eq_decide]; by_cases hxy : x ≤ y
  · rw [decide_eq_true hxy]; dsimp [cond]; omega
  · simp [hxy]
theorem kpMaxZ_of_le {x y : ℤ} (h : x ≤ y) : kpMaxZ x y = y := by
  unfold kpMaxZ; rw [kpBleZ_eq_decide]; simp [h]
theorem kpMaxZ_of_ge {x y : ℤ} (h : y ≤ x) : kpMaxZ x y = x := by
  unfold kpMaxZ; rw [kpBleZ_eq_decide]; by_cases hxy : x ≤ y
  · rw [decide_eq_true hxy]; dsimp [cond]; omega
  · simp [hxy]
theorem kpSumSqAbsFast_eq : ∀ (xs : List ℤ) (acc : ℕ), kpSumSqAbsFast xs acc = kpSumSqAbs xs
  acc
  | [], _ => rfl
  | .ofNat n :: cjs, acc => by
    unfold kpSumSqAbsFast kpSumSqAbs; simp only [kpForceNat_eq]
    exact kpSumSqAbsFast_eq cjs (Nat.add acc (Nat.mul n n))
  | .negSucc n :: cjs, acc => by
    unfold kpSumSqAbsFast kpSumSqAbs; simp only [kpForceNat_eq]
    exact kpSumSqAbsFast_eq cjs (Nat.add acc (Nat.mul (Nat.add n 1) (Nat.add n 1)))
theorem kpFastNegOfNat_eq (n : ℕ) : kpFastNegOfNat n = Int.negOfNat n := by
  unfold kpFastNegOfNat
  cases n with
  | zero => rfl | succ m => exact kpForceNat_eq m Int.negSucc
theorem kpFastSubNatNat_eq (m n : ℕ) : kpFastSubNatNat m n = Int.subNatNat m n := by
  unfold kpFastSubNatNat Int.subNatNat; have hsub : n - m = Nat.sub n m := rfl; rw [hsub]
  cases Nat.sub n m with
  | zero => exact kpForceNat_eq (Nat.sub m n) Int.ofNat | succ _ => rfl
theorem int_negOfNat_eq (n : ℕ) : Int.negOfNat n = -(n : ℤ) := by cases n <;> rfl
theorem int_negOfNat_le_of_le {x y : ℕ} (h : x ≤ y) : Int.negOfNat y ≤ Int.negOfNat x := by
  rw [int_negOfNat_eq, int_negOfNat_eq]; omega
theorem int_negOfNat_le_ofNat (x y : ℕ) : Int.negOfNat x ≤ Int.ofNat y := by
  rw [int_negOfNat_eq, Int.ofNat_eq_natCast]; omega
theorem kpFastNegZ_eq (x : ℤ) : kpFastNegZ x = Int.neg x := by
  unfold kpFastNegZ Int.neg
  cases x with
  | ofNat n => exact kpFastNegOfNat_eq n
  | negSucc n => exact kpForceNat_eq (Nat.add n 1) Int.ofNat
theorem kpFastAddZ_eq (x y : ℤ) : kpFastAddZ x y = Int.add x y := by
  unfold kpFastAddZ Int.add
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact kpForceNat_eq (Nat.add m n) Int.ofNat
    | negSucc n => exact kpFastSubNatNat_eq m (Nat.add n 1)
  | negSucc m =>
    cases y with
    | ofNat n => exact kpFastSubNatNat_eq n (Nat.add m 1)
    | negSucc n => exact kpForceNat_eq (Nat.add (Nat.add m n) 1) Int.negSucc
theorem kpFastSubZ_eq (x y : ℤ) : kpFastSubZ x y = Int.sub x y := by
  unfold kpFastSubZ Int.sub; rw [kpFastAddZ_eq, kpFastNegZ_eq]; rfl
theorem kpFastMulZ_eq (x y : ℤ) : kpFastMulZ x y = Int.mul x y := by
  unfold kpFastMulZ Int.mul
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact kpForceNat_eq (Nat.mul m n) Int.ofNat
    | negSucc n => exact kpFastNegOfNat_eq (Nat.mul m (Nat.add n 1))
  | negSucc m =>
    cases y with
    | ofNat n => exact kpFastNegOfNat_eq (Nat.mul (Nat.add m 1) n)
    | negSucc n => exact kpForceNat_eq (Nat.mul (Nat.add m 1) (Nat.add n 1)) Int.ofNat
theorem kpFastEdivZ_eq (x y : ℤ) : kpFastEdivZ x y = Int.ediv x y := by
  unfold kpFastEdivZ Int.ediv
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact kpForceNat_eq (Nat.div m n) Int.ofNat
    | negSucc n => exact kpFastNegOfNat_eq (Nat.div m (Nat.add n 1))
  | negSucc m =>
    cases y with
    | ofNat n =>
      cases n with
      | zero => rfl | succ k => exact kpForceNat_eq (Nat.div m (k + 1)) Int.negSucc
    | negSucc n => exact kpForceNat_eq (Nat.add (Nat.div m (Nat.add n 1)) 1) Int.ofNat
theorem kpFastCeilDiv_eq (x y : ℤ) : kpFastCeilDiv x y = Int.neg (Int.ediv (Int.neg x) y) :=
  by unfold kpFastCeilDiv; rw [kpFastNegZ_eq, kpFastEdivZ_eq, kpFastNegZ_eq]
theorem kpNatCeilDivScale_eq (n : ℕ) : kpNatCeilDivScale n = Int.neg (Int.ediv (Int.neg
  (.ofNat n)) (.ofNat 1000000000)) := by
  unfold kpNatCeilDivScale; rw [kpForceNat_eq]
  cases n with
  | zero => rfl
  | succ k =>
    change Int.ofNat (Nat.div (Nat.add (k + 1) 999999999) 1000000000) = Int.ofNat (Nat.div k
      1000000000 + 1); congr 1; simp only [nat_div_eq, nat_add_eq]; omega
theorem kpNegFloorDivScale_eq (n : ℕ) : kpNegFloorDivScale n = Int.ediv (Int.negOfNat n)
  (.ofNat 1000000000) := by
  cases n with
  | zero => rfl
  | succ k =>
    unfold kpNegFloorDivScale; rw [kpFastNegOfNat_eq]; change Int.negOfNat (Nat.div (Nat.add
      (k + 1) 999999999) 1000000000) = Int.negSucc (Nat.div k 1000000000)
    have hdiv : Nat.div (Nat.add (k + 1) 999999999) 1000000000 = Nat.div k 1000000000 + 1 :=
      (by simp only [nat_div_eq, nat_add_eq]; omega); rw [hdiv]; rfl
theorem kpNegCeilDivScale_eq (n : ℕ) : kpNegCeilDivScale n = Int.neg (Int.ediv (Int.neg
  (Int.negOfNat n)) (.ofNat 1000000000)) := by
  cases n with
  | zero => rfl
  | succ k => unfold kpNegCeilDivScale; rw [kpFastNegOfNat_eq]; rfl
theorem kpIvAddFast_eq (a b : IvInt) : kpIvAddFast a b = kpIvAdd a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  unfold kpIvAddFast kpIvAdd; simp only [kpForceInt_eq, kpFastAddZ_eq]
theorem kpIvSubFast_eq (a b : IvInt) : kpIvSubFast a b = kpIvSub a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  unfold kpIvSubFast kpIvSub; simp only [kpForceInt_eq, kpFastSubZ_eq]
theorem kpMulIvPtFastCore_eq (a1 a2 z : ℤ) : kpMulIvPtFastCore a1 a2 z = kpIvMul (a1, a2)
  (z, z) := by
  unfold kpMulIvPtFastCore kpIvMul kpMinZ kpMaxZ; simp only [kpForceInt_eq, kpFastMulZ_eq,
    kpFastBleZ_eq, kpFastEdivZ_eq, kpFastCeilDiv_eq, Bool.cond_self]
  cases kpBleZ (Int.mul a1 z) (Int.mul a2 z) <;> rfl
theorem kpMulIvPtFast_eq (a : IvInt) (z : ℤ) : kpMulIvPtFast a z = kpIvMul a (z, z) := by
  rcases a with ⟨c1 | c1, c2 | c2⟩
  · unfold kpMulIvPtFast; dsimp only; cases hc : Nat.ble c1 c2
    · exact kpMulIvPtFastCore_eq (.ofNat c1) (.ofNat c2) z
    · have hc_le : c1 ≤ c2 := (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hc; exact hc)
      cases z with
      | ofNat m =>
          dsimp only; have hm : Nat.mul c1 m ≤ Nat.mul c2 m :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right m hc_le)
          have hp : Int.ofNat (Nat.mul c1 m) ≤ Int.ofNat (Nat.mul c2 m) := Int.ofNat_le.mpr hm
          have him1 : Int.mul (.ofNat c1) (.ofNat m) = .ofNat (Nat.mul c1 m) := rfl
          have him2 : Int.mul (.ofNat c2) (.ofNat m) = .ofNat (Nat.mul c2 m) := rfl
          have hed : Int.ediv (.ofNat (Nat.mul c1 m)) (.ofNat 1000000000) = .ofNat (Nat.div (Nat.mul
            c1 m) 1000000000) := rfl; unfold kpIvMul; simp only [Bool.cond_true, kpForceNat_eq,
            kpForceInt_eq, him1, him2, hed, kpMinZ_of_le (le_refl _), kpMaxZ_of_le (le_refl
            _), kpMinZ_of_le hp, kpMaxZ_of_le hp, ← kpNatCeilDivScale_eq]
      | negSucc m =>
          dsimp only; have hm : Nat.mul c1 (Nat.add m 1) ≤ Nat.mul c2 (Nat.add m 1) :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right _ hc_le)
          have hp := int_negOfNat_le_of_le hm; have him1 : Int.mul (.ofNat c1) (.negSucc m) =
              Int.negOfNat (Nat.mul c1 (Nat.add m 1)) := rfl
          have him2 : Int.mul (.ofNat c2) (.negSucc m) = Int.negOfNat (Nat.mul c2 (Nat.add m 1)) :=
            rfl; unfold kpIvMul; simp only [Bool.cond_true, kpForceInt_eq, him1, him2,
            kpMinZ_of_le (le_refl _), kpMaxZ_of_le (le_refl _), kpMinZ_of_ge hp,
            kpMaxZ_of_ge hp, ← kpNegFloorDivScale_eq, ← kpNegCeilDivScale_eq]
  · exact kpMulIvPtFastCore_eq (.ofNat c1) (.negSucc c2) z
  · unfold kpMulIvPtFast
    cases z with
    | ofNat m =>
        dsimp only; have hp := int_negOfNat_le_ofNat (Nat.mul (Nat.add c1 1) m) (Nat.mul c2 m)
        have him1 : Int.mul (.negSucc c1) (.ofNat m) = Int.negOfNat (Nat.mul (Nat.add c1 1) m) :=
          rfl
        have him2 : Int.mul (.ofNat c2) (.ofNat m) = .ofNat (Nat.mul c2 m) := rfl; unfold kpIvMul
        simp only [kpForceInt_eq, him1, him2, kpMinZ_of_le (le_refl _), kpMaxZ_of_le
          (le_refl _), kpMinZ_of_le hp, kpMaxZ_of_le hp, ← kpNegFloorDivScale_eq, ←
          kpNatCeilDivScale_eq]
    | negSucc m =>
        dsimp only; have hp := int_negOfNat_le_ofNat
          (Nat.mul c2 (Nat.add m 1)) (Nat.mul (Nat.add c1 1) (Nat.add m 1))
        have him1 : Int.mul (.negSucc c1) (.negSucc m) = .ofNat (Nat.mul (Nat.add c1 1) (Nat.add m
          1)) := rfl; have him2 : Int.mul (.ofNat c2) (.negSucc m) = Int.negOfNat (Nat.mul c2
          (Nat.add m 1)) := rfl; unfold kpIvMul; simp only [kpForceInt_eq, him1, him2,
          kpMinZ_of_le (le_refl _), kpMaxZ_of_le (le_refl _), kpMinZ_of_ge hp,
          kpMaxZ_of_ge hp, ← kpNegFloorDivScale_eq, ← kpNatCeilDivScale_eq]
  · unfold kpMulIvPtFast; dsimp only; cases hc : Nat.ble c2 c1
    · exact kpMulIvPtFastCore_eq (.negSucc c1) (.negSucc c2) z
    · have hc1_le : Nat.add c2 1 ≤ Nat.add c1 1 :=
        (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hc; simp only [nat_add_eq]; omega)
      cases z with
      | ofNat m =>
          dsimp only; have hm : Nat.mul (Nat.add c2 1) m ≤ Nat.mul (Nat.add c1 1) m :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right m hc1_le)
          have hp := int_negOfNat_le_of_le hm; have him1 : Int.mul (.negSucc c1) (.ofNat m) =
              Int.negOfNat (Nat.mul (Nat.add c1 1) m) := rfl
          have him2 : Int.mul (.negSucc c2) (.ofNat m) = Int.negOfNat (Nat.mul (Nat.add c2 1) m) :=
            rfl; unfold kpIvMul; simp only [Bool.cond_true, kpForceInt_eq, him1, him2,
            kpMinZ_of_le (le_refl _), kpMaxZ_of_le (le_refl _), kpMinZ_of_le hp,
            kpMaxZ_of_le hp, ← kpNegFloorDivScale_eq, ← kpNegCeilDivScale_eq]
      | negSucc m =>
          dsimp only; have hm : Nat.mul (Nat.add c2 1) (Nat.add m 1) ≤
              Nat.mul (Nat.add c1 1) (Nat.add m 1) := by
            simp only [nat_mul_eq]; exact Nat.mul_le_mul_right _ hc1_le
          have hp : Int.ofNat (Nat.mul (Nat.add c2 1) (Nat.add m 1)) ≤ Int.ofNat (Nat.mul (Nat.add
            c1 1) (Nat.add m 1)) := Int.ofNat_le.mpr hm; have him1 : Int.mul (.negSucc c1) (.negSucc
            m) = .ofNat (Nat.mul (Nat.add c1 1) (Nat.add m 1)) := rfl; have him2 : Int.mul (.negSucc
            c2) (.negSucc m) = .ofNat (Nat.mul (Nat.add c2 1) (Nat.add m 1)) := rfl
          have hed : Int.ediv (.ofNat (Nat.mul (Nat.add c2 1) (Nat.add m 1))) (.ofNat 1000000000) =
            .ofNat (Nat.div (Nat.mul (Nat.add c2 1) (Nat.add m 1)) 1000000000) := rfl
          unfold kpIvMul; simp only [Bool.cond_true, kpForceNat_eq, kpForceInt_eq, him1, him2, hed,
            kpMinZ_of_le (le_refl _), kpMaxZ_of_le (le_refl _), kpMinZ_of_ge hp,
            kpMaxZ_of_ge hp, ← kpNatCeilDivScale_eq]
theorem kpIvMulFastCore_eq (a1 a2 b1 b2 : ℤ) : kpIvMulFastCore a1 a2 b1 b2 = kpIvMul (a1,
  a2) (b1, b2) := by
  unfold kpIvMulFastCore kpIvMul kpFastMinZ kpFastMaxZ kpMinZ kpMaxZ
  simp only [kpForceInt_eq, kpFastMulZ_eq, kpFastBleZ_eq, kpFastEdivZ_eq,
    kpFastCeilDiv_eq]; cases kpBleZ (Int.mul a1 b1) (Int.mul a1 b2) <;> cases kpBleZ (Int.mul a2
    b1) (Int.mul a2 b2) <;> rfl
theorem kpIvMulFast_eq (a b : IvInt) : kpIvMulFast a b = kpIvMul a b := by
  rcases b with ⟨b1, b2⟩; rcases a with ⟨c1 | c1, c2 | c2⟩
  · unfold kpIvMulFast; dsimp only; cases hc : Nat.ble c1 c2
    · exact kpIvMulFastCore_eq (.ofNat c1) (.ofNat c2) b1 b2
    · have hc_le : c1 ≤ c2 := (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hc; exact hc)
      rcases b1 with d1 | d1 <;> rcases b2 with d2 | d2
      · dsimp only; cases hd : Nat.ble d1 d2
        · exact kpIvMulFastCore_eq (.ofNat c1) (.ofNat c2) (.ofNat d1) (.ofNat d2)
        · have hd_le : d1 ≤ d2 := (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hd; exact hd)
          have hp12 : Int.ofNat (Nat.mul c1 d1) ≤ Int.ofNat (Nat.mul c1 d2) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left c1 hd_le)
          have hp34 : Int.ofNat (Nat.mul c2 d1) ≤ Int.ofNat (Nat.mul c2 d2) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left c2 hd_le)
          have hp13 : Int.ofNat (Nat.mul c1 d1) ≤ Int.ofNat (Nat.mul c2 d1) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right d1 hc_le)
          have hp24 : Int.ofNat (Nat.mul c1 d2) ≤ Int.ofNat (Nat.mul c2 d2) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right d2 hc_le)
          have him1 : Int.mul (.ofNat c1) (.ofNat d1) = .ofNat (Nat.mul c1 d1) := rfl
          have him2 : Int.mul (.ofNat c1) (.ofNat d2) = .ofNat (Nat.mul c1 d2) := rfl
          have him3 : Int.mul (.ofNat c2) (.ofNat d1) = .ofNat (Nat.mul c2 d1) := rfl
          have him4 : Int.mul (.ofNat c2) (.ofNat d2) = .ofNat (Nat.mul c2 d2) := rfl
          have hed : Int.ediv (.ofNat (Nat.mul c1 d1)) (.ofNat 1000000000) = .ofNat (Nat.div
            (Nat.mul c1 d1) 1000000000) := rfl; unfold kpIvMul; simp only [Bool.cond_true,
            kpForceNat_eq, kpForceInt_eq, him1, him2, him3, him4, hed, kpMinZ_of_le hp12,
            kpMinZ_of_le hp34, kpMinZ_of_le hp13, kpMaxZ_of_le hp12, kpMaxZ_of_le
            hp34, kpMaxZ_of_le hp24, ← kpNatCeilDivScale_eq]
      · exact kpIvMulFastCore_eq (.ofNat c1) (.ofNat c2) (.ofNat d1) (.negSucc d2)
      · dsimp only; have hp12 := int_negOfNat_le_ofNat (Nat.mul c1 (Nat.add d1 1)) (Nat.mul c1
          d2); have hp34 := int_negOfNat_le_ofNat (Nat.mul c2 (Nat.add d1 1)) (Nat.mul c2 d2)
        have hm31 : Nat.mul c1 (Nat.add d1 1) ≤ Nat.mul c2 (Nat.add d1 1) :=
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right (Nat.add d1 1) hc_le); have hp31 :=
          int_negOfNat_le_of_le hm31
        have hp24 : Int.ofNat (Nat.mul c1 d2) ≤ Int.ofNat (Nat.mul c2 d2) := Int.ofNat_le.mpr
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right d2 hc_le)
        have him1 : Int.mul (.ofNat c1) (.negSucc d1) = Int.negOfNat (Nat.mul c1 (Nat.add d1 1)) :=
          rfl; have him2 : Int.mul (.ofNat c1) (.ofNat d2) = .ofNat (Nat.mul c1 d2) := rfl
        have him3 : Int.mul (.ofNat c2) (.negSucc d1) = Int.negOfNat (Nat.mul c2 (Nat.add d1 1)) :=
          rfl
        have him4 : Int.mul (.ofNat c2) (.ofNat d2) = .ofNat (Nat.mul c2 d2) := rfl; unfold kpIvMul
        simp only [Bool.cond_true, kpForceInt_eq, him1, him2, him3, him4, kpMinZ_of_le hp12,
          kpMinZ_of_le hp34, kpMinZ_of_ge hp31, kpMaxZ_of_le hp12, kpMaxZ_of_le
          hp34, kpMaxZ_of_le hp24, ← kpNegFloorDivScale_eq, ← kpNatCeilDivScale_eq]
      · dsimp only; cases hd : Nat.ble d2 d1
        · exact kpIvMulFastCore_eq (.ofNat c1) (.ofNat c2) (.negSucc d1) (.negSucc d2)
        · have hd1_le : Nat.add d2 1 ≤ Nat.add d1 1 :=
            (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hd; simp only [nat_add_eq]; omega)
          have hm12 : Nat.mul c1 (Nat.add d2 1) ≤ Nat.mul c1 (Nat.add d1 1) :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left c1 hd1_le)
          have hm34 : Nat.mul c2 (Nat.add d2 1) ≤ Nat.mul c2 (Nat.add d1 1) :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left c2 hd1_le)
          have hm31 : Nat.mul c1 (Nat.add d1 1) ≤ Nat.mul c2 (Nat.add d1 1) :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right (Nat.add d1 1) hc_le)
          have hm42 : Nat.mul c1 (Nat.add d2 1) ≤ Nat.mul c2 (Nat.add d2 1) :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right (Nat.add d2 1) hc_le)
          have hp12 := int_negOfNat_le_of_le hm12; have hp34 := int_negOfNat_le_of_le hm34
          have hp31 := int_negOfNat_le_of_le hm31; have hp42 := int_negOfNat_le_of_le hm42
          have him1 : Int.mul (.ofNat c1) (.negSucc d1) = Int.negOfNat (Nat.mul c1 (Nat.add d1 1))
            := rfl; have him2 : Int.mul (.ofNat c1) (.negSucc d2) = Int.negOfNat (Nat.mul c1
            (Nat.add d2 1)) := rfl
          have him3 : Int.mul (.ofNat c2) (.negSucc d1) = Int.negOfNat (Nat.mul c2 (Nat.add d1 1))
            := rfl; have him4 : Int.mul (.ofNat c2) (.negSucc d2) = Int.negOfNat (Nat.mul c2
            (Nat.add d2 1)) := rfl; unfold kpIvMul; simp only [Bool.cond_true, kpForceInt_eq, him1,
            him2, him3, him4, kpMinZ_of_le hp12, kpMinZ_of_le hp34, kpMinZ_of_ge hp31,
            kpMaxZ_of_le hp12, kpMaxZ_of_le hp34, kpMaxZ_of_ge hp42, ←
            kpNegFloorDivScale_eq, ← kpNegCeilDivScale_eq]
  · exact kpIvMulFastCore_eq (.ofNat c1) (.negSucc c2) b1 b2
  · unfold kpIvMulFast; rcases b1 with d1 | d1 <;> rcases b2 with d2 | d2
    · dsimp only; cases hd : Nat.ble d1 d2
      · exact kpIvMulFastCore_eq (.negSucc c1) (.ofNat c2) (.ofNat d1) (.ofNat d2)
      · have hd_le : d1 ≤ d2 := (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hd; exact hd)
        have hm12 : Nat.mul (Nat.add c1 1) d1 ≤ Nat.mul (Nat.add c1 1) d2 :=
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left (Nat.add c1 1) hd_le); have hp21 :=
          int_negOfNat_le_of_le hm12; have hp34 : Int.ofNat (Nat.mul c2 d1) ≤ Int.ofNat (Nat.mul
          c2 d2) := Int.ofNat_le.mpr (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left c2 hd_le)
        have hp23 := int_negOfNat_le_ofNat (Nat.mul (Nat.add c1 1) d2) (Nat.mul c2 d1)
        have hp14 := int_negOfNat_le_ofNat (Nat.mul (Nat.add c1 1) d1) (Nat.mul c2 d2)
        have him1 : Int.mul (.negSucc c1) (.ofNat d1) = Int.negOfNat (Nat.mul (Nat.add c1 1) d1) :=
          rfl; have him2 : Int.mul (.negSucc c1) (.ofNat d2) = Int.negOfNat (Nat.mul (Nat.add c1 1)
          d2) := rfl; have him3 : Int.mul (.ofNat c2) (.ofNat d1) = .ofNat (Nat.mul c2 d1) := rfl
        have him4 : Int.mul (.ofNat c2) (.ofNat d2) = .ofNat (Nat.mul c2 d2) := rfl; unfold kpIvMul
        simp only [Bool.cond_true, kpForceInt_eq, him1, him2, him3, him4, kpMinZ_of_ge hp21,
          kpMinZ_of_le hp34, kpMinZ_of_le hp23, kpMaxZ_of_ge hp21, kpMaxZ_of_le
          hp34, kpMaxZ_of_le hp14, ← kpNegFloorDivScale_eq, ← kpNatCeilDivScale_eq]
    · exact kpIvMulFastCore_eq (.negSucc c1) (.ofNat c2) (.ofNat d1) (.negSucc d2)
    · exact kpIvMulFastCore_eq (.negSucc c1) (.ofNat c2) (.negSucc d1) (.ofNat d2)
    · dsimp only; cases hd : Nat.ble d2 d1
      · exact kpIvMulFastCore_eq (.negSucc c1) (.ofNat c2) (.negSucc d1) (.negSucc d2)
      · have hd1_le : Nat.add d2 1 ≤ Nat.add d1 1 :=
          (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hd; simp only [nat_add_eq]; omega)
        have hp21 : Int.ofNat (Nat.mul (Nat.add c1 1) (Nat.add d2 1)) ≤ Int.ofNat (Nat.mul (Nat.add
          c1 1) (Nat.add d1 1)) := Int.ofNat_le.mpr
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left (Nat.add c1 1) hd1_le)
        have hm43 : Nat.mul c2 (Nat.add d2 1) ≤ Nat.mul c2 (Nat.add d1 1) :=
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left c2 hd1_le); have hp34 :=
          int_negOfNat_le_of_le hm43; have hp32 := int_negOfNat_le_ofNat (Nat.mul c2
          (Nat.add d1 1)) (Nat.mul (Nat.add c1 1) (Nat.add d2 1)); have hp41 :=
          int_negOfNat_le_ofNat (Nat.mul c2 (Nat.add d2 1)) (Nat.mul (Nat.add c1 1) (Nat.add d1
          1)); have him1 : Int.mul (.negSucc c1) (.negSucc d1) = .ofNat (Nat.mul (Nat.add c1 1)
          (Nat.add d1 1)) := rfl; have him2 : Int.mul (.negSucc c1) (.negSucc d2) = .ofNat (Nat.mul
          (Nat.add c1 1) (Nat.add d2 1)) := rfl; have him3 : Int.mul (.ofNat c2) (.negSucc d1) =
          Int.negOfNat (Nat.mul c2 (Nat.add d1 1)) := rfl; have him4 : Int.mul (.ofNat c2) (.negSucc
          d2) = Int.negOfNat (Nat.mul c2 (Nat.add d2 1)) := rfl; unfold kpIvMul
        simp only [Bool.cond_true, kpForceInt_eq, him1, him2, him3, him4, kpMinZ_of_ge hp21,
          kpMinZ_of_le hp34, kpMinZ_of_ge hp32, kpMaxZ_of_ge hp21, kpMaxZ_of_le
          hp34, kpMaxZ_of_ge hp41, ← kpNegFloorDivScale_eq, ← kpNatCeilDivScale_eq]
  · unfold kpIvMulFast; dsimp only; cases hc : Nat.ble c2 c1
    · exact kpIvMulFastCore_eq (.negSucc c1) (.negSucc c2) b1 b2
    · have hc1_le : Nat.add c2 1 ≤ Nat.add c1 1 :=
        (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hc; simp only [nat_add_eq]; omega)
      rcases b1 with d1 | d1 <;> rcases b2 with d2 | d2
      · dsimp only; cases hd : Nat.ble d1 d2
        · exact kpIvMulFastCore_eq (.negSucc c1) (.negSucc c2) (.ofNat d1) (.ofNat d2)
        · have hd_le : d1 ≤ d2 := (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hd; exact hd)
          have hm12 : Nat.mul (Nat.add c1 1) d1 ≤ Nat.mul (Nat.add c1 1) d2 :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left (Nat.add c1 1) hd_le)
          have hm34 : Nat.mul (Nat.add c2 1) d1 ≤ Nat.mul (Nat.add c2 1) d2 :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left (Nat.add c2 1) hd_le)
          have hm42 : Nat.mul (Nat.add c2 1) d2 ≤ Nat.mul (Nat.add c1 1) d2 :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right d2 hc1_le)
          have hm31 : Nat.mul (Nat.add c2 1) d1 ≤ Nat.mul (Nat.add c1 1) d1 :=
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right d1 hc1_le); have hp21 :=
            int_negOfNat_le_of_le hm12; have hp43 := int_negOfNat_le_of_le hm34
          have hp24 := int_negOfNat_le_of_le hm42; have hp13 := int_negOfNat_le_of_le hm31
          have him1 : Int.mul (.negSucc c1) (.ofNat d1) = Int.negOfNat (Nat.mul (Nat.add c1 1) d1)
            := rfl; have him2 : Int.mul (.negSucc c1) (.ofNat d2) = Int.negOfNat (Nat.mul (Nat.add
            c1 1) d2) := rfl; have him3 : Int.mul (.negSucc c2) (.ofNat d1) = Int.negOfNat (Nat.mul
            (Nat.add c2 1) d1) := rfl
          have him4 : Int.mul (.negSucc c2) (.ofNat d2) = Int.negOfNat (Nat.mul (Nat.add c2 1) d2)
            := rfl; unfold kpIvMul; simp only [Bool.cond_true, kpForceInt_eq, him1, him2, him3,
            him4, kpMinZ_of_ge hp21, kpMinZ_of_ge hp43, kpMinZ_of_le hp24,
            kpMaxZ_of_ge hp21, kpMaxZ_of_ge hp43, kpMaxZ_of_le hp13, ←
            kpNegFloorDivScale_eq, ← kpNegCeilDivScale_eq]
      · exact kpIvMulFastCore_eq (.negSucc c1) (.negSucc c2) (.ofNat d1) (.negSucc d2)
      · dsimp only; have hp21 := int_negOfNat_le_ofNat
          (Nat.mul (Nat.add c1 1) d2) (Nat.mul (Nat.add c1 1) (Nat.add d1 1)); have hp43 :=
          int_negOfNat_le_ofNat (Nat.mul (Nat.add c2 1) d2) (Nat.mul (Nat.add c2 1) (Nat.add d1
          1)); have hm42 : Nat.mul (Nat.add c2 1) d2 ≤ Nat.mul (Nat.add c1 1) d2 :=
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right d2 hc1_le); have hp24 :=
          int_negOfNat_le_of_le hm42
        have hp31 : Int.ofNat (Nat.mul (Nat.add c2 1) (Nat.add d1 1)) ≤ Int.ofNat (Nat.mul (Nat.add
          c1 1) (Nat.add d1 1)) := Int.ofNat_le.mpr
          (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right (Nat.add d1 1) hc1_le)
        have him1 : Int.mul (.negSucc c1) (.negSucc d1) = .ofNat (Nat.mul (Nat.add c1 1) (Nat.add d1
          1)) := rfl; have him2 : Int.mul (.negSucc c1) (.ofNat d2) = Int.negOfNat (Nat.mul (Nat.add
          c1 1) d2) := rfl; have him3 : Int.mul (.negSucc c2) (.negSucc d1) = .ofNat (Nat.mul
          (Nat.add c2 1) (Nat.add d1 1)) := rfl; have him4 : Int.mul (.negSucc c2) (.ofNat d2) =
          Int.negOfNat (Nat.mul (Nat.add c2 1) d2) := rfl; unfold kpIvMul
        simp only [Bool.cond_true, kpForceInt_eq, him1, him2, him3, him4, kpMinZ_of_ge hp21,
          kpMinZ_of_ge hp43, kpMinZ_of_le hp24, kpMaxZ_of_ge hp21, kpMaxZ_of_ge
          hp43, kpMaxZ_of_ge hp31, ← kpNegFloorDivScale_eq, ← kpNatCeilDivScale_eq]
      · dsimp only; cases hd : Nat.ble d2 d1
        · exact kpIvMulFastCore_eq (.negSucc c1) (.negSucc c2) (.negSucc d1) (.negSucc d2)
        · have hd1_le : Nat.add d2 1 ≤ Nat.add d1 1 :=
            (by rw [swLNatBle_eq_decide, decide_eq_true_eq] at hd; simp only [nat_add_eq]; omega)
          have hp21 : Int.ofNat (Nat.mul (Nat.add c1 1) (Nat.add d2 1)) ≤ Int.ofNat (Nat.mul
            (Nat.add c1 1) (Nat.add d1 1)) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left (Nat.add c1 1) hd1_le)
          have hp43 : Int.ofNat (Nat.mul (Nat.add c2 1) (Nat.add d2 1)) ≤ Int.ofNat (Nat.mul
            (Nat.add c2 1) (Nat.add d1 1)) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_left (Nat.add c2 1) hd1_le)
          have hp42 : Int.ofNat (Nat.mul (Nat.add c2 1) (Nat.add d2 1)) ≤ Int.ofNat (Nat.mul
            (Nat.add c1 1) (Nat.add d2 1)) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right (Nat.add d2 1) hc1_le)
          have hp31 : Int.ofNat (Nat.mul (Nat.add c2 1) (Nat.add d1 1)) ≤ Int.ofNat (Nat.mul
            (Nat.add c1 1) (Nat.add d1 1)) := Int.ofNat_le.mpr
            (by simp only [nat_mul_eq]; exact Nat.mul_le_mul_right (Nat.add d1 1) hc1_le)
          have him1 : Int.mul (.negSucc c1) (.negSucc d1) = .ofNat (Nat.mul (Nat.add c1 1) (Nat.add
            d1 1)) := rfl; have him2 : Int.mul (.negSucc c1) (.negSucc d2) = .ofNat (Nat.mul
            (Nat.add c1 1) (Nat.add d2 1)) := rfl; have him3 : Int.mul (.negSucc c2) (.negSucc d1) =
            .ofNat (Nat.mul (Nat.add c2 1) (Nat.add d1 1)) := rfl
          have him4 : Int.mul (.negSucc c2) (.negSucc d2) = .ofNat (Nat.mul (Nat.add c2 1) (Nat.add
            d2 1)) := rfl
          have hed : Int.ediv (.ofNat (Nat.mul (Nat.add c2 1) (Nat.add d2 1))) (.ofNat 1000000000) =
            .ofNat (Nat.div (Nat.mul (Nat.add c2 1) (Nat.add d2 1)) 1000000000) := rfl
          unfold kpIvMul; simp only [Bool.cond_true, kpForceNat_eq, kpForceInt_eq, him1, him2, him3,
            him4, hed, kpMinZ_of_ge hp21, kpMinZ_of_ge hp43, kpMinZ_of_ge hp42,
            kpMaxZ_of_ge hp21, kpMaxZ_of_ge hp43, kpMaxZ_of_ge hp31, ←
            kpNatCeilDivScale_eq]
theorem kpIvSqFast_eq (a : IvInt) : kpIvSqFast a = kpIvSq a := by
  rcases a with ⟨c1 | c1, c2 | c2⟩
  · have hb : kpBleZ (.ofNat 0) (.ofNat c1) = true := (by rw [← kpFastBleZ_eq]; rfl)
    have him1 : Int.mul (.ofNat c1) (.ofNat c1) = .ofNat (Nat.mul c1 c1) := rfl
    have him2 : Int.mul (.ofNat c2) (.ofNat c2) = .ofNat (Nat.mul c2 c2) := rfl
    have hed : Int.ediv (.ofNat (Nat.mul c1 c1)) (.ofNat 1000000000) = .ofNat (Nat.div (Nat.mul c1
      c1) 1000000000) := rfl; unfold kpIvSqFast kpIvSq; simp only [hb, Bool.cond_true,
      kpForceNat_eq, kpForceInt_eq, him1, him2, hed, ← kpNatCeilDivScale_eq]
  · have hb : kpBleZ (.ofNat 0) (.ofNat c1) = true := (by rw [← kpFastBleZ_eq]; rfl)
    have him1 : Int.mul (.ofNat c1) (.ofNat c1) = .ofNat (Nat.mul c1 c1) := rfl
    have him2 : Int.mul (.negSucc c2) (.negSucc c2) = .ofNat (Nat.mul (Nat.add c2 1) (Nat.add c2 1))
      := rfl; have hed : Int.ediv (.ofNat (Nat.mul c1 c1)) (.ofNat 1000000000) = .ofNat (Nat.div
      (Nat.mul c1 c1) 1000000000) := rfl; unfold kpIvSqFast kpIvSq; simp only [hb,
      Bool.cond_true, kpForceNat_eq, kpForceInt_eq, him1, him2, hed, ← kpNatCeilDivScale_eq]
  · have hb1 : kpBleZ (.ofNat 0) (.negSucc c1) = false := (by rw [← kpFastBleZ_eq]; rfl)
    cases c2 with
    | zero =>
        have hb2 : kpBleZ (.ofNat 0) (.ofNat 0) = true := (by rw [← kpFastBleZ_eq]; rfl)
        have hble : Nat.ble (Nat.add c1 1) 0 = false :=
          (by rw [swLNatBle_eq_decide, decide_eq_false_iff_not, nat_add_eq]; omega)
        have him1 : Int.mul (.negSucc c1) (.negSucc c1) = .ofNat (Nat.mul (Nat.add c1 1) (Nat.add c1
          1)) := rfl; have hq0 : Int.ediv (Int.mul (.ofNat 0) (.ofNat 0)) (.ofNat 1000000000) =
          .ofNat 0 := rfl; unfold kpIvSqFast kpIvSq; simp only [hb1, hb2, hble, Bool.cond_false,
          Bool.cond_true, kpForceInt_eq, him1, hq0, ← kpNatCeilDivScale_eq]
    | succ d =>
        have hb2 : kpBleZ (.ofNat (d + 1)) (.ofNat 0) = false := (by rw [← kpFastBleZ_eq]; rfl)
        have hneg : Int.neg (.negSucc c1) = .ofNat (Nat.add c1 1) := rfl
        unfold kpIvSqFast kpIvSq; dsimp only
        rw [hb1, hb2, hneg, ← kpFastMaxZ_eq]; unfold kpFastMaxZ kpFastBleZ
        simp only [Bool.cond_false, kpForceInt_eq]; cases Nat.ble (Nat.add c1 1) (d + 1)
        · have him : Int.mul (.ofNat (Nat.add c1 1)) (.ofNat (Nat.add c1 1)) = .ofNat (Nat.mul
            (Nat.add c1 1) (Nat.add c1 1)) := rfl; simp only [Bool.cond_false, him, ←
            kpNatCeilDivScale_eq]
        · have him : Int.mul (.ofNat (d + 1)) (.ofNat (d + 1)) = .ofNat (Nat.mul (d + 1) (d + 1)) :=
            rfl; simp only [Bool.cond_true, him, ← kpNatCeilDivScale_eq]
  · have hb1 : kpBleZ (.ofNat 0) (.negSucc c1) = false := (by rw [← kpFastBleZ_eq]; rfl)
    have hb2 : kpBleZ (.negSucc c2) (.ofNat 0) = true := (by rw [← kpFastBleZ_eq]; rfl)
    have him1 : Int.mul (.negSucc c1) (.negSucc c1) = .ofNat (Nat.mul (Nat.add c1 1) (Nat.add c1 1))
      := rfl; have him2 : Int.mul (.negSucc c2) (.negSucc c2) = .ofNat (Nat.mul (Nat.add c2 1)
      (Nat.add c2 1)) := rfl
    have hed : Int.ediv (.ofNat (Nat.mul (Nat.add c2 1) (Nat.add c2 1))) (.ofNat 1000000000) =
      .ofNat (Nat.div (Nat.mul (Nat.add c2 1) (Nat.add c2 1)) 1000000000) := rfl
    unfold kpIvSqFast kpIvSq; simp only [hb1, hb2, Bool.cond_false, Bool.cond_true,
      kpForceNat_eq, kpForceInt_eq, him1, him2, hed, ← kpNatCeilDivScale_eq]
theorem kpIvRatDivFast_eq (num den : ℤ) : kpIvRatDivFast num den = kpIvRatDiv num den := by
  unfold kpIvRatDivFast kpIvRatDiv; simp only [kpFastMulZ_eq, kpFastEdivZ_eq,
    kpFastCeilDiv_eq]
theorem kpIvPythagFast_eq (uNum uDen : ℤ) : kpIvPythagFast uNum uDen = kpIvPythag uNum uDen
  := by
  unfold kpIvPythagFast kpIvPythag; simp only [kpForceInt_eq, kpFastMulZ_eq,
    kpFastAddZ_eq, kpFastSubZ_eq, kpIvRatDivFast_eq]
theorem kpUPythagsGoFast_eq (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : ∀ (rem : ℕ) (h : rem ≤ m),
  kpUPythagsGoFast uDen m f rem h = kpUPythagsGo uDen m f rem h
  | 0, _ => rfl
  | rem + 1, h => by
    unfold kpUPythagsGoFast kpUPythagsGo; dsimp only; simp only [kpForcePair_eq,
      kpIvPythagFast_eq, kpUPythagsGoFast_eq uDen m f rem (Nat.le_of_succ_le h)]
theorem kpUPythagsFast_eq (uDen : ℤ) (m : ℕ) (f : Fin m → ℤ) : kpUPythagsFast uDen m f =
  kpUPythags uDen m f := by
  unfold kpUPythagsFast kpUPythags; exact kpUPythagsGoFast_eq uDen m f m le_rfl
theorem kpPulseCvFast_eq {L : ℕ} (p : SwLPulseRat L) : kpPulseCvFast p = kpPulseCv p := by
  unfold kpPulseCvFast kpPulseCv; simp only [kpFastBeqZ_eq, kpIvPythagFast_eq]
theorem kpCompilePulseFast_eq : ∀ (L : ℕ) (p : SwLPulseRat L), kpCompilePulseFast L p =
  kpCompilePulse L p
  | 0, p => by
    unfold kpCompilePulseFast kpCompilePulse; simp only [kpForceIv_eq, kpPulseCvFast_eq]
  | m + 1, p => by
    unfold kpCompilePulseFast kpCompilePulse; simp only [kpForceIv_eq, kpWithPairList_eq,
      kpPulseCvFast_eq, kpUPythagsFast_eq]
theorem kpCompilePulsesFast_eq (L : ℕ) (ps : List (SwLPulseRat L)) : kpCompilePulsesFast L
  ps = kpCompilePulses L ps := by
  unfold kpCompilePulsesFast kpCompilePulses; have hfn : kpCompilePulseFast L =
    kpCompilePulse L := funext (kpCompilePulseFast_eq L); rw [hfn]
theorem kpUnconsTrig_eq {α : Type} (ts : List (IvInt × IvInt)) (k : IvInt → IvInt → List (IvInt
  × IvInt) → α) : kpUnconsTrig ts k = k (headTrigP ts).1 (headTrigP ts).2 (drop1TrigP ts) := by
  rcases ts with _ | ⟨⟨cw, sw⟩, ts'⟩ <;> rfl
theorem kpUncons2Z_eq {α : Type} (cs : List ℤ) (k : ℤ → ℤ → List ℤ → α) : kpUncons2Z cs k =
  k (headZP cs) (secondZP cs) (drop2ZP cs) := by rcases cs with _ | ⟨ce, _ | ⟨co, cs'⟩⟩ <;> rfl
theorem kpHeadIvF_eq (ss : List IvInt) : kpHeadIvF ss = headIvP ss := by cases ss <;> rfl
theorem kpUncons1Iv_eq {α : Type} (ss : List IvInt) (k : IvInt → List IvInt → α) :
  kpUncons1Iv ss k = k (headIvP ss) (drop1IvP ss) := by cases ss <;> rfl
theorem kpUncons2Iv_eq {α : Type} (ss : List IvInt) (k : IvInt → IvInt → List IvInt → α) :
  kpUncons2Iv ss k = k (headIvP ss) (secondIvP ss) (drop2IvP ss) := by
  rcases ss with _ | ⟨lv, _ | ⟨rv, ss'⟩⟩ <;> rfl
theorem kpGroverWalkFast_eq : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ),
  kpGroverWalkFast k ts cs = kpGroverWalk k ts cs
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
    unfold kpGroverWalkFast kpGroverWalk; rw [kpUnconsTrig_eq, kpUncons2Z_eq]
    rcases headTrigP ts with ⟨cw, sw⟩; simp only [kpForceIv_eq, kpIvSubFast_eq,
      kpIvAddFast_eq, kpMulIvPtFast_eq, kpGroverWalkFast_eq k]
theorem kpPieriWalkFast_eq (cv : IvInt) : ∀ (k : ℕ) (us : List (IvInt × IvInt)) (ss : List
  IvInt), kpPieriWalkFast cv k us ss = kpPieriWalk cv k us ss
  | 0, _, ss => by unfold kpPieriWalkFast kpPieriWalk; rw [kpHeadIvF_eq, kpIvMulFast_eq]
  | k + 1, us, ss => by
    unfold kpPieriWalkFast kpPieriWalk; rw [kpUnconsTrig_eq, kpUncons2Iv_eq]
    rcases headTrigP us with ⟨cu, su⟩; simp only [kpForceIv_eq, kpIvSubFast_eq,
      kpIvAddFast_eq, kpIvMulFast_eq, kpPieriWalkFast_eq cv k]
theorem kpPieriAndWeakPreFast_eq : ∀ (L : ℕ) (pp : KpPrePulse) (naIv : List IvInt),
  kpPieriAndWeakPreFast L pp naIv = kpPieriAndWeakPre L pp naIv
  | 0, _, _ => rfl
  | m + 1, (cv, ups), naIv => by
    unfold kpPieriAndWeakPreFast kpPieriAndWeakPre; dsimp only; rw [kpUncons1Iv_eq,
      kpPieriWalkFast_eq]
theorem kpRecenterAndRadSqCPS_eq {α : Type} : ∀ (ivs : List IvInt) (k : List ℤ → ℕ → α),
  kpRecenterAndRadSqCPS ivs k = k (kpRecenterAndRadSq ivs).1 (kpRecenterAndRadSq ivs).2
  | [], _ => rfl
  | (lo, hi) :: ivs, k => by
      unfold kpRecenterAndRadSqCPS kpRecenterAndRadSq kpIvMidRad; simp only [kpForceInt_eq,
        kpForceNat_eq, kpFastAddZ_eq, kpFastSubZ_eq, kpFastEdivZ_eq, kpFastMaxZ_eq]
      rw [kpRecenterAndRadSqCPS_eq ivs]; rcases kpRecenterAndRadSq ivs with ⟨cs, acc⟩
      cases cs <;> rfl
theorem kpTerminalStateL2FastCPS_eq {α : Type} (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) (k : List
  IvInt → IvInt → ℤ → α) : kpTerminalStateL2FastCPS cVec rho survUb k =
      let outIv := kpTerminalStateL2 cVec rho survUb
      k outIv.1 outIv.2.1 outIv.2.2.2 := by
  unfold kpTerminalStateL2FastCPS kpTerminalStateL2; simp only [kpForceNat_eq, kpForceInt_eq,
    kpWithIvList_eq, kpWithState_eq, kpSumSqAbsFast_eq, fastCeilIsqrt_eq,
    fastFloorIsqrt_eq, kpFastMinZ_eq, kpFastMaxZ_eq, kpNatCeilDivScale_eq,
    kpFastSubZ_eq, kpFastAddZ_eq]; rfl
theorem kpPulseStepL2PreFastCPS_eq {α : Type} (L : ℕ) (trigIvs : List (IvInt × IvInt)) (cVec :
  List ℤ) (rho : ℕ) (survUb : ℤ) (pp : KpPrePulse) (k : List ℤ → ℕ → ℤ → α) :
  kpPulseStepL2PreFastCPS L trigIvs cVec rho survUb pp k =
      let st := kpPulseStepL2Pre L trigIvs cVec rho survUb pp
      k st.1 st.2.1 st.2.2 := by
  unfold kpPulseStepL2PreFastCPS kpPulseStepL2Pre; simp only [kpForceNat_eq, kpForceInt_eq,
    kpWithIvList_eq, kpSumSqAbsFast_eq, fastCeilIsqrt_eq, kpFastMinZ_eq,
    kpNatCeilDivScale_eq, kpFastAddZ_eq, kpPieriAndWeakPreFast_eq,
    kpGroverWalkFast_eq]; rw [kpRecenterAndRadSqCPS_eq]
theorem kpEvolutionL2AuxPreFastCPS_eq {α : Type} (L : ℕ)
    (trigIvs : List (IvInt × IvInt)) :
    ∀ (pps : List KpPrePulse) (cVec : List ℤ) (rho : ℕ) (survUb : ℤ)
      (k : List ℤ → ℕ → ℤ → α),
    kpEvolutionL2AuxPreFastCPS L trigIvs cVec rho survUb pps k =
      let ev := kpEvolutionL2AuxPre L trigIvs cVec rho survUb pps
      k ev.1 ev.2.1 ev.2.2
  | [], _, _, _, _ => rfl
  | pp :: pps, cVec, rho, survUb, k => by
    unfold kpEvolutionL2AuxPreFastCPS kpEvolutionL2AuxPre; rw [kpPulseStepL2PreFastCPS_eq]
    rcases kpPulseStepL2Pre L trigIvs cVec rho survUb pp with ⟨cNext, rho', survUb'⟩
    simp only [kpWithL2State_eq]
    exact kpEvolutionL2AuxPreFastCPS_eq L trigIvs pps cNext rho' survUb' k
theorem kpEvolutionL2PreFastCPS_eq {α : Type} (L : ℕ) (trigIvs : List (IvInt × IvInt)) (pps :
  List KpPrePulse) (k : List ℤ → ℕ → ℤ → α) : kpEvolutionL2PreFastCPS L trigIvs pps k =
      let ev := kpEvolutionL2Pre L trigIvs pps
      k ev.1 ev.2.1 ev.2.2 := by
  unfold kpEvolutionL2PreFastCPS kpEvolutionL2Pre; simp only [kpWithIntList_eq,
    kpEvolutionL2AuxPreFastCPS_eq]
theorem kpOrbLinAuxFast_eq (o : ℕ) : ∀ (j : ℕ) (acc : IvInt) (stIv : List IvInt),
  kpOrbLinAuxFast o j acc stIv = kpOrbLinAux o j acc stIv
  | _, _, [] => rfl
  | j, acc, _ :: sjs => by
    unfold kpOrbLinAuxFast kpOrbLinAux; simp only [kpForceIv_eq, kpIvAddFast_eq,
      kpIvMulFast_eq, kpOrbLinAuxFast_eq o (Nat.add j 1) _ sjs]
theorem kpOrbSqIvFast_eq (stIv : List IvInt) (o : ℕ) : kpOrbSqIvFast stIv o = kpOrbSqIv stIv
  o := by unfold kpOrbSqIvFast kpOrbSqIv; rw [kpIvSqFast_eq, kpOrbLinAuxFast_eq]
theorem kpTailSuffixIvsFast_eq (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ∀ (m : ℕ),
  kpTailSuffixIvsFast L stIv cumIv m = kpTailSuffixIvs L stIv cumIv m
  | 0 => rfl
  | m + 1 => by
    unfold kpTailSuffixIvsFast kpTailSuffixIvs; dsimp only; rw [swLNatBeq_eq_beq]
    by_cases h : (Nat.sub L m == L) = true
    · simp only [h, Bool.cond_true, kpForceIv_eq, kpIvAddFast_eq, kpOrbSqIvFast_eq,
        kpIvMulFast_eq, kpIvSqFast_eq]
    · have hf : (Nat.sub L m == L) = false := Bool.eq_false_iff.2 h; simp only [hf,
        Bool.cond_false, kpTailSuffixIvsFast_eq L stIv cumIv m]
      cases kpTailSuffixIvs L stIv cumIv m with
      | nil => rfl
      | cons nextIv rest =>
          simp only [kpForceIv_eq, kpIvAddFast_eq, kpOrbSqIvFast_eq, kpIvMulFast_eq]
theorem kpClampTailLbsFast_eq : ∀ (ivs : List IvInt), kpClampTailLbsFast ivs =
  kpClampTailLbs ivs
  | [] => rfl
  | [⟨lo, _⟩] => by
    unfold kpClampTailLbsFast kpClampTailLbs; simp only [kpForceInt_eq, kpFastMaxZ_eq]
  | ⟨lo, _⟩ :: iv2 :: tl => by
    have ih := kpClampTailLbsFast_eq (iv2 :: tl); unfold kpClampTailLbsFast kpClampTailLbs
    rw [ih]
    cases kpClampTailLbs (iv2 :: tl) with
    | nil => simp only [kpForceInt_eq, kpFastMaxZ_eq]
    | cons nextLb lbs => simp only [kpForceInt_eq, kpFastMaxZ_eq, kpFastMinZ_eq]
theorem kpCheckSwLTrigRatFast_eq (a d b e cLo cHi sLo sHi : ℤ) : kpCheckSwLTrigRatFast a d b
  e cLo cHi sLo sHi = kpCheckSwLTrigRat a d b e cLo cHi sLo sHi := by
  unfold kpCheckSwLTrigRatFast kpCheckSwLTrigRat; simp only [kpFastMulZ_eq,
    kpFastAddZ_eq, kpFastSubZ_eq, kpFastEdivZ_eq, kpFastCeilDiv_eq,
    kpFastBleZ_eq]
theorem kpCheckSwLStratumRatioFast_eq (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) :
  kpCheckSwLStratumRatioFast rMin rMax shiftW ratioLo ratioHi = kpCheckSwLStratumRatio rMin rMax
  shiftW ratioLo ratioHi := by
  unfold kpCheckSwLStratumRatioFast kpCheckSwLStratumRatio; simp only [kpFastMulZ_eq,
    kpFastAddZ_eq, kpFastSubZ_eq, kpFastBleZ_eq]
theorem kpCheckSwLBucketAnglesFast_eq (L rMin rMax tauNum tauDen : ℕ) (ratios : List IvInt)
  (trigIvs : List (IvInt × IvInt)) : kpCheckSwLBucketAnglesFast L rMin rMax tauNum tauDen ratios
  trigIvs = kpCheckSwLBucketAngles L rMin rMax tauNum tauDen ratios trigIvs := by
  unfold kpCheckSwLBucketAnglesFast kpCheckSwLBucketAngles; simp only [kpForceInt_eq,
    kpFastAddZ_eq, kpFastMulZ_eq]; rcases trigIvs with _ | ⟨⟨⟨c0Lo, c0Hi⟩, ⟨s0Lo, s0Hi⟩⟩,
    restTrig⟩
  · rfl
  · simp only [kpCheckSwLTrigRatFast_eq, kpCheckSwLStratumRatioFast_eq]
theorem checkSwLBucketCertL2PreFast_eq (L rMin rMax tauNum tauDen : ℕ) (ratios : List IvInt)
  (trigIvs : List (IvInt × IvInt)) (pps : List KpPrePulse) (tailLbs : List ℤ) (survUb : ℤ) :
  checkSwLBucketCertL2PreFast L rMin rMax tauNum tauDen ratios trigIvs pps tailLbs survUb =
  checkSwLBucketCertL2Pre L rMin rMax tauNum tauDen ratios trigIvs pps tailLbs survUb := by
  unfold checkSwLBucketCertL2PreFast checkSwLBucketCertL2Pre
  simp only [kpWithIvList_eq, kpWithPairList_eq, kpWithIntList_eq, kpForceInt_eq, kpFastBleZ_eq,
    kpCheckSwLBucketAnglesFast_eq, kpEvolutionL2PreFastCPS_eq]
  rcases kpEvolutionL2Pre L trigIvs pps with ⟨cVec, rho, survEvol⟩
  simp only [kpWithL2State_eq]; rw [kpTerminalStateL2FastCPS_eq]
  rcases kpTerminalStateL2 cVec rho survEvol with ⟨stIv, cumIv, ⟨_, survOut⟩⟩
  simp only [kpWithState_eq, kpForceIv_eq, kpIvAddFast_eq, kpIvSubFast_eq,
    kpIvMulFast_eq, kpOrbSqIvFast_eq, kpTailSuffixIvsFast_eq, kpClampTailLbsFast_eq]
end SchurWeylLCert
end QuantumComputation.Specs.GroverFindAll
end

@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.SchurWeylM1L50
open Real SchurWeylLCert
open scoped BigOperators
/- ## 1. High-Rank (`2 ≤ L ≤ 50`, `1 ≤ shiftW ≤ 49`) Angle Ratios, Bucket Certs & Stage Spec -/
/-- Pure-integer ratio-bound check for stratum `1 ≤ shiftW ≤ 49` on `[rMin, rMax]` (`rMax ≤
  1024`). -/
def checkSwLStratumRatioL50 (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  let s20 : ℤ := 100000000000000000000
  decide (shiftW + 1 ≤ rMin ∧ rMin ≤ rMax ∧ rMax ≤ 1024 ∧ 1 ≤ shiftW ∧ shiftW ≤ 49 ∧
    0 < ratioLo ∧ 1 < ratioHi ∧ ratioHi ≤ swScale ∧ (ratioLo + 1) * (ratioLo + 1) * (rMin : ℤ) ≤
      swScale * swScale * ((rMin : ℤ) - (shiftW : ℤ)) ∧
    swScale * swScale * ((rMax : ℤ) - (shiftW : ℤ)) ≤
      ((ratioHi - 1) * (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ) ∧
    ratioLo * s20 ≤ (ratioLo + 1) * (s20 - 1) ∧ (ratioHi - 1) * s20 ≤ ratioHi * (s20 - 1))
/-- Pure-GMP stratum angle-ratio checker (`1 ≤ shiftW ≤ 49`). -/
def kpCheckSwLStratumRatioL50 (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  let s20 : ℤ := .ofNat 100000000000000000000
  let s20m1 : ℤ := kpFastSubZ s20 (.ofNat 1)
  let sc : ℤ := .ofNat 1000000000
  let sc2 : ℤ := kpFastMulZ sc sc
  let rMinZ : ℤ := Int.ofNat rMin
  let rMaxZ : ℤ := Int.ofNat rMax
  let swZ : ℤ := Int.ofNat shiftW
  let rLo1 : ℤ := kpFastAddZ ratioLo (.ofNat 1)
  let rHi1 : ℤ := kpFastSubZ ratioHi (.ofNat 1)
  Nat.ble (Nat.add shiftW 1) rMin && (Nat.ble rMin rMax && (Nat.ble rMax 1024 &&
  (Nat.ble 1 shiftW && (Nat.ble shiftW 49 && (kpFastBleZ (.ofNat 1) ratioLo &&
  (kpFastBleZ (.ofNat 2) ratioHi && (kpFastBleZ ratioHi sc &&
  (kpFastBleZ (kpFastMulZ (kpFastMulZ rLo1 rLo1) rMinZ)
    (kpFastMulZ sc2 (kpFastSubZ rMinZ swZ)) &&
  (kpFastBleZ (kpFastMulZ sc2 (kpFastSubZ rMaxZ swZ))
    (kpFastMulZ (kpFastSubZ (kpFastMulZ rHi1 rHi1) swZ) rMaxZ) &&
  (kpFastBleZ (kpFastMulZ ratioLo s20) (kpFastMulZ rLo1 s20m1) &&
   kpFastBleZ (kpFastMulZ rHi1 s20) (kpFastMulZ ratioHi s20m1)))))))))))
theorem kpCheckSwLStratumRatioL50_eq (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) :
  kpCheckSwLStratumRatioL50 rMin rMax shiftW ratioLo ratioHi = checkSwLStratumRatioL50 rMin rMax
  shiftW ratioLo ratioHi := by
  unfold kpCheckSwLStratumRatioL50 checkSwLStratumRatioL50; simp only [kpFastSubZ_eq,
    kpFastAddZ_eq, kpFastMulZ_eq, kpFastBleZ_eq, swLNatBle_eq_decide, kpBleZ_eq_decide,
    ← Bool.decide_and]; rfl
/-- Pure-integer `2 ≤ L ≤ 50` bucket angle checker for `r ∈ [rMin, rMax]`. -/
def checkSwLBucketAnglesL50 (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := 100000000000
  withForcedInt ((tauNum : ℤ) * s11 + (tauDen : ℤ)) fun q1HiNum ↦
    withForcedInt ((tauDen : ℤ) * s11) fun q1HiDen ↦
      decide (2 ≤ L ∧ L ≤ 50 ∧ L ≤ rMin ∧ rMin ≤ rMax ∧ rMax ≤ 1024 ∧
        0 < tauNum ∧ 0 < tauDen ∧ ratios.length = L - 1 ∧ trigIvs.length = L) &&
      match trigIvs with
      | [] => false
      | (c0, s0) :: restTrig =>
          checkSwLTrigRat (tauNum : ℤ) (tauDen : ℤ) q1HiNum q1HiDen c0.1 c0.2 s0.1 s0.2 &&
          (List.range (L - 1)).all fun idx ↦
            let w := idx + 1
            let rat := ratios.getD idx (0, 0)
            let cs := restTrig.getD idx ((0, 0), (0, 0))
            checkSwLStratumRatioL50 rMin rMax w rat.1 rat.2 &&
            checkSwLTrigRat ((tauNum : ℤ) * rat.1) ((tauDen : ℤ) * swScale)
              (q1HiNum * rat.2) (q1HiDen * swScale) cs.1.1 cs.1.2 cs.2.1 cs.2.2
/-- Pure-GMP `2 ≤ L ≤ 50` bucket angle checker equal to `checkSwLBucketAnglesL50`. -/
def kpCheckSwLBucketAnglesL50 (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := .ofNat 100000000000
  let tnZ : ℤ := Int.ofNat tauNum
  let tdZ : ℤ := Int.ofNat tauDen
  kpForceInt (kpFastAddZ (kpFastMulZ tnZ s11) tdZ) fun q1HiNum ↦
    kpForceInt (kpFastMulZ tdZ s11) fun q1HiDen ↦
      (Nat.ble 2 L && (Nat.ble L 50 && (Nat.ble L rMin && (Nat.ble rMin rMax &&
      (Nat.ble rMax 1024 && (Nat.ble 1 tauNum && (Nat.ble 1 tauDen &&
      (Nat.beq ratios.length (Nat.sub L 1) && Nat.beq trigIvs.length L)))))))) &&
      match trigIvs with
      | [] => false
      | ((c0Lo, c0Hi), (s0Lo, s0Hi)) :: restTrig =>
          kpCheckSwLTrigRatFast tnZ tdZ q1HiNum q1HiDen c0Lo c0Hi s0Lo s0Hi &&
          kpAllRange (fun idx ↦
            let w := Nat.add idx 1
            match ratios.getD idx (.ofNat 0, .ofNat 0),
                restTrig.getD idx ((.ofNat 0, .ofNat 0), (.ofNat 0, .ofNat 0)) with
            | (rLo, rHi), ((cLo, cHi), (sLo, sHi)) =>
                kpCheckSwLStratumRatioL50 rMin rMax w rLo rHi && kpCheckSwLTrigRatFast
                  (kpFastMulZ tnZ rLo) (kpFastMulZ tdZ (.ofNat 1000000000))
                  (kpFastMulZ q1HiNum rHi) (kpFastMulZ q1HiDen (.ofNat 1000000000))
                  cLo cHi sLo sHi) (Nat.sub L 1)
theorem kpCheckSwLBucketAnglesL50_eq (L rMin rMax tauNum tauDen : ℕ) (ratios : List IvInt) (trigIvs
  : List (IvInt × IvInt)) : kpCheckSwLBucketAnglesL50 L rMin rMax tauNum tauDen ratios trigIvs =
  checkSwLBucketAnglesL50 L rMin rMax tauNum tauDen ratios trigIvs := by
  unfold kpCheckSwLBucketAnglesL50 checkSwLBucketAnglesL50; have hsub : Nat.sub L 1 = L - 1 := rfl
  simp only [kpForceInt_eq, withForcedInt_eq, kpFastAddZ_eq, kpFastMulZ_eq,
    swLNatBle_eq_decide, natBeq_eq_decide, ← Bool.decide_and, hsub]
  rcases trigIvs with _ | ⟨⟨⟨c0Lo, c0Hi⟩, ⟨s0Lo, s0Hi⟩⟩, restTrig⟩
  · rfl
  · dsimp only; rw [kpCheckSwLTrigRatFast_eq, kpCheckSwLTrigRat_eq, kpAllRange_eq]; congr 2
    congr 1; funext idx; have hz0 : (.ofNat 0 : ℤ) = 0 := rfl; simp only [hz0]
    rcases ratios.getD idx (0, 0) with ⟨rLo, rHi⟩; rcases restTrig.getD idx ((0, 0), (0, 0)) with
      ⟨⟨cLo, cHi⟩, ⟨sLo, sHi⟩⟩; simp only [kpCheckSwLStratumRatioL50_eq,
      kpCheckSwLTrigRatFast_eq, kpCheckSwLTrigRat_eq]; rfl
theorem stratum_angle_ratio_boundsL50 {N r rMin rMax shiftW : ℕ} {ratioLo ratioHi : ℤ} (hN96 :
  (79228162514264337593543950336 : ℝ) ≤ (N : ℝ)) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkSwLStratumRatioL50 rMin rMax shiftW ratioLo ratioHi = true) :
    let α₀ := Real.arcsin (1 / √((N : ℝ) / (r : ℝ))); let θ := swLThetaShiftReal N r shiftW
    ((ratioLo : ℝ) / (swScale : ℝ)) * (2 * α₀) ≤ θ ∧ θ ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * (2 * α₀)
      := by
  intro α₀ θ; unfold checkSwLStratumRatioL50 at hchk; rw [decide_eq_true_eq] at hchk
  rcases hchk with ⟨hsw_min, _, hrMax_1024, hsw1, hsw49, hrat_lo0, hrat_hi1, hrat_hi_le, hsq_lo,
    hsq_hi, hc_lo20, hc_hi20⟩; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hr_ge : shiftW + 1 ≤ r := hsw_min.trans hmin; have hr1024 : r ≤ 1024 := hmax.trans hrMax_1024
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hrMin_pos : (0 :
    ℝ) < (rMin : ℝ) := (by exact_mod_cast (by omega : 0 < rMin)); have hrMax_pos : (0 : ℝ) < (rMax :
    ℝ) := (by exact_mod_cast (by omega : 0 < rMax)); have hN_pos : (0 : ℝ) < (N : ℝ) :=
    (by linarith); set d : ℕ := 2 * shiftW; have hd_r : (d : ℝ) ≤ 98 :=
    (by exact_mod_cast (by omega : d ≤ 98)); have hNd_eq : (N : ℝ) - 2 * (shiftW : ℝ) = (N : ℝ) - (d
    : ℝ) := (by dsimp [d]; push_cast; ring); have hNd_pos : (0 : ℝ) < (N : ℝ) - (d : ℝ) :=
    (by linarith); have hrk_pos : (0 : ℝ) < (r : ℝ) - (shiftW : ℝ) :=
    (by have : (shiftW : ℝ) + 1 ≤ (r : ℝ) := (by exact_mod_cast hr_ge); linarith); set c₁ : ℝ := (N
    : ℝ) / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]
    exact (mul_le_mul_of_nonneg_left (mod_cast hr1024 : (r : ℝ) ≤ 1024) (by norm_num)).trans
      ((by norm_num : (8796093022208 : ℝ) ^ 2 * 1024 ≤ 79228162514264337593543950336).trans hN96)
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ :=
    (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]; exact Real.sqrt_le_sqrt hc1_ge)
  have hx0_pos : 0 < 1 / √c₁ := (by positivity); have hx0_ub : 1 / √c₁ ≤ 1 / 8000000000000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  rcases arcsin_small_boundsL hx0_pos hx0_ub with ⟨hα_pos, _, hα_lb, hα_ub⟩; set xk : ℝ := √(((r :
    ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ))); have hxk_pos : 0 < xk := Real.sqrt_pos.2 (div_pos
    hrk_pos hNd_pos); have hxk_sq : xk ^ 2 = ((r : ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ)) :=
    Real.sq_sqrt (div_nonneg hrk_pos.le hNd_pos.le)
  have hxk_ub : xk ≤ 1 / 8000000000000 := by
    have hsq : xk ^ 2 ≤ (1 / 8000000000000 : ℝ) ^ 2 := by
      rw [hxk_sq, div_le_iff₀ hNd_pos]; have hr_le : (r : ℝ) ≤ 1024 := mod_cast hr1024
      have hsw_nn : (0 : ℝ) ≤ (shiftW : ℝ) := by positivity
      linarith [mul_le_mul_of_nonneg_left (by linarith [hN96, hd_r] :
        (65536000000000000000000000000 : ℝ) ≤ (N : ℝ) - (d : ℝ))
        (by norm_num : (0 : ℝ) ≤ (1 / 8000000000000 : ℝ) ^ 2)]
    rw [← Real.sqrt_sq hxk_pos.le, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8000000000000)]
    exact Real.sqrt_le_sqrt hsq
  rcases arcsin_small_boundsL hxk_pos hxk_ub with ⟨_, _, hβ_lb, hβ_ub⟩; set β : ℝ := Real.arcsin xk
  have hx0_sq : (1 / √c₁) ^ 2 = (r : ℝ) / (N : ℝ) :=
    (by dsimp [c₁]; rw [one_div_pow, Real.sq_sqrt (div_nonneg hN_pos.le hr_pos.le), one_div_div])
  have hlo_sq_real : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 * (1 / √c₁) ^ 2 ≤ xk ^ 2 := by
    rw [hx0_sq, hxk_sq]; have h1 : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 ≤
        ((rMin : ℝ) - (shiftW : ℝ)) / (rMin : ℝ) := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hS) hrMin_pos]; have hcast : (((ratioLo + 1) *
        (ratioLo + 1) * (rMin : ℤ) : ℤ) : ℝ) ≤ ((swScale * swScale * ((rMin : ℤ) - (shiftW : ℤ)) :
        ℤ) : ℝ) := (by exact_mod_cast hsq_lo); have hl_eq : (((ratioLo + 1 : ℤ) : ℝ) ^ 2) * (rMin :
        ℝ) = (((ratioLo + 1) * (ratioLo + 1) * (rMin : ℤ) : ℤ) : ℝ) := (by push_cast; ring)
      have hr_eq : ((rMin : ℝ) - (shiftW : ℝ)) * (swScale : ℝ) ^ 2 = ((swScale * swScale * ((rMin :
        ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) := (by push_cast; ring); rw [hl_eq, hr_eq]; exact hcast
    have h2 : ((rMin : ℝ) - (shiftW : ℝ)) / (rMin : ℝ) ≤ ((r : ℝ) - (shiftW : ℝ)) / (r : ℝ) := by
      rw [div_le_div_iff₀ hrMin_pos hr_pos]; have hr_min_r : (rMin : ℝ) ≤ (r : ℝ) :=
        (by exact_mod_cast hmin); have hsw_nn : (0 : ℝ) ≤ (shiftW : ℝ) := (by positivity); nlinarith
    have h3 : (((r : ℝ) - (shiftW : ℝ)) / (r : ℝ)) * ((r : ℝ) / (N : ℝ)) = ((r : ℝ) - (shiftW : ℝ))
      / (N : ℝ) := (by field_simp [hr_pos.ne', hN_pos.ne'])
    have h4 : ((r : ℝ) - (shiftW : ℝ)) / (N : ℝ) ≤ ((r : ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ))
      := by
      rw [div_le_div_iff₀ hN_pos hNd_pos]; have hd_nn : (0 : ℝ) ≤ (d : ℝ) := (by positivity)
      nlinarith
    exact (mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)).trans (h3.trans_le h4)
  have hxk_ge : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) ≤ xk := by
    have hnn : 0 ≤ (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) := mul_nonneg (div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ ratioLo + 1)) hS.le) hx0_pos.le; rw [← Real.sqrt_sq hnn, ←
      Real.sqrt_sq hxk_pos.le]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
  have hhi_sq_real : xk ^ 2 ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 * (1 / √c₁) ^ 2 := by
    rw [hx0_sq, hxk_sq]; set a : ℝ := ((ratioHi - 1 : ℤ) : ℝ); have ha_nn : 0 ≤ a :=
      (by dsimp [a]; exact_mod_cast (by omega : 0 ≤ ratioHi - 1))
    have ha_le_S : a ≤ (swScale : ℝ) :=
      (by dsimp [a]; exact_mod_cast (by omega : ratioHi - 1 ≤ swScale))
    have h1 : ((r : ℝ) - (shiftW : ℝ)) / (r : ℝ) ≤ ((rMax : ℝ) - (shiftW : ℝ)) / (rMax : ℝ) := by
      rw [div_le_div_iff₀ hr_pos hrMax_pos]; have hr_max_r : (r : ℝ) ≤ (rMax : ℝ) :=
        (by exact_mod_cast hmax); have hsw_nn : (0 : ℝ) ≤ (shiftW : ℝ) := (by positivity); nlinarith
    have h2 : ((rMax : ℝ) - (shiftW : ℝ)) / (rMax : ℝ) ≤ (a ^ 2 - (shiftW : ℝ)) / (swScale : ℝ) ^ 2
      := by
      rw [div_le_div_iff₀ hrMax_pos (sq_pos_of_pos hS)]; have hcast : ((swScale * swScale * ((rMax :
        ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) ≤ ((((ratioHi - 1) * (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ)
        : ℤ) : ℝ) := (by exact_mod_cast hsq_hi); have hl_eq : ((rMax : ℝ) - (shiftW : ℝ)) * (swScale
        : ℝ) ^ 2 = ((swScale * swScale * ((rMax : ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) :=
        (by push_cast; ring); have hr_eq : (a ^ 2 - (shiftW : ℝ)) * (rMax : ℝ) = ((((ratioHi - 1) *
        (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ) : ℤ) : ℝ) := (by dsimp [a]; push_cast; ring)
      rw [hl_eq, hr_eq]; exact hcast
    have hsw1_r : (1 : ℝ) ≤ (shiftW : ℝ) := by exact_mod_cast hsw1
    have hN_ratio : (N : ℝ) / ((N : ℝ) - (d : ℝ)) ≤ (swScale : ℝ) ^ 2 / ((swScale : ℝ) ^ 2 - 1)
      := by
      rw [div_le_div_iff₀ hNd_pos (by unfold swScale; norm_num)]
      have hdS : (d : ℝ) * (swScale : ℝ) ^ 2 ≤ (N : ℝ) :=
        (mul_le_mul_of_nonneg_right hd_r (sq_nonneg _)).trans
          ((by unfold swScale; norm_num : 98 * (swScale : ℝ) ^ 2 ≤
            79228162514264337593543950336).trans hN96)
      linarith [show (swScale : ℝ) ^ 2 * ((N : ℝ) - (d : ℝ)) - (N : ℝ) * ((swScale : ℝ) ^ 2 - 1) =
        (N : ℝ) - (d : ℝ) * (swScale : ℝ) ^ 2 by ring]
    have hprod_le : ((a ^ 2 - (shiftW : ℝ)) / (swScale : ℝ) ^ 2) * ((swScale : ℝ) ^ 2 / ((swScale :
      ℝ) ^ 2 - 1)) ≤ (a / (swScale : ℝ)) ^ 2 := by
      have hS2 : (0 : ℝ) < (swScale : ℝ) ^ 2 := sq_pos_of_pos hS; rw [div_mul_div_cancel₀ hS2.ne',
        div_pow, div_le_div_iff₀ (by unfold swScale; norm_num) hS2]; linarith [pow_le_pow_left₀
        ha_nn ha_le_S 2, mul_le_mul_of_nonneg_right hsw1_r hS2.le, show (a ^ 2 - (shiftW : ℝ)) *
        (swScale : ℝ) ^ 2 - a ^ 2 * ((swScale : ℝ) ^ 2 - 1) = a ^ 2 - (shiftW : ℝ) * (swScale : ℝ) ^
        2 by ring]
    have hrew : ((r : ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ)) = (((r : ℝ) - (shiftW : ℝ)) / (r :
      ℝ)) * ((N : ℝ) / ((N : ℝ) - (d : ℝ))) * ((r : ℝ) / (N : ℝ)) :=
      (by field_simp [hr_pos.ne', hN_pos.ne', hNd_pos.ne'])
    rw [hrew]; have hm1 : (((r : ℝ) - (shiftW : ℝ)) / (r : ℝ)) * ((N : ℝ) / ((N : ℝ) - (d : ℝ))) ≤
        ((a ^ 2 - (shiftW : ℝ)) / (swScale : ℝ) ^ 2) *
          ((swScale : ℝ) ^ 2 / ((swScale : ℝ) ^ 2 - 1)) :=
      mul_le_mul (h1.trans h2) hN_ratio (by positivity)
        (le_trans (by positivity) (h1.trans h2)); exact mul_le_mul_of_nonneg_right (hm1.trans
      hprod_le) (by positivity)
  have hxk_le : xk ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) := by
    have hnn : 0 ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) := mul_nonneg (div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ ratioHi - 1)) hS.le) hx0_pos.le; rw [← Real.sqrt_sq
      hxk_pos.le, ← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
  set s20 : ℝ := 100000000000000000000; have hs20_pos : 0 < s20 := (by dsimp [s20]; norm_num)
  have hβ_ge_α : ((ratioLo : ℝ) / (swScale : ℝ)) * α₀ ≤ β := by
    have hcast0 : ((ratioLo * 100000000000000000000 : ℤ) : ℝ) ≤ (((ratioLo + 1) *
      (100000000000000000000 - 1) : ℤ) : ℝ) := Int.cast_le.2 hc_lo20; have hl_eq : ((ratioLo *
      100000000000000000000 : ℤ) : ℝ) = (ratioLo : ℝ) * s20 := (by dsimp [s20]; push_cast; ring)
    have hr_eq : (((ratioLo + 1) * (100000000000000000000 - 1) : ℤ) : ℝ) = ((ratioLo + 1 : ℤ) : ℝ) *
      (s20 - 1) := (by dsimp [s20]; push_cast; ring)
    rw [hl_eq, hr_eq] at hcast0; have h1 : (ratioLo : ℝ) / (swScale : ℝ) ≤
        (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 - 1 / s20) := by
      rw [div_mul_eq_mul_div]; have hdiv := div_le_div_of_nonneg_right hcast0 hs20_pos.le
      have hrew : ((ratioLo + 1 : ℤ) : ℝ) * (s20 - 1) / s20 = ((ratioLo + 1 : ℤ) : ℝ) * (1 - 1 /
        s20) := (by field_simp [hs20_pos.ne']); have hrew0 : (ratioLo : ℝ) * s20 / s20 = (ratioLo :
        ℝ) := mul_div_cancel_right₀ _ hs20_pos.ne'
      rw [hrew0, hrew] at hdiv; exact div_le_div_of_nonneg_right hdiv hS.le
    have h2 : ((ratioLo : ℝ) / (swScale : ℝ)) * α₀ ≤ (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * ((1
      - 1 / s20) * α₀) := (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hα_pos.le)
    have h3 : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * ((1 - 1 / s20) * α₀) ≤ (((ratioLo + 1 : ℤ)
      : ℝ) / (swScale : ℝ)) * (1 / √c₁) := mul_le_mul_of_nonneg_left hα_ub (div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ ratioLo + 1)) hS.le); exact ((h2.trans h3).trans
      hxk_ge).trans hβ_lb
  have hβ_le_α : β ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * α₀ := by
    have hcast0 : (((ratioHi - 1) * 100000000000000000000 : ℤ) : ℝ) ≤ ((ratioHi *
      (100000000000000000000 - 1) : ℤ) : ℝ) := Int.cast_le.2 hc_hi20; have hl_eq : (((ratioHi - 1) *
      100000000000000000000 : ℤ) : ℝ) = ((ratioHi - 1 : ℤ) : ℝ) * s20 :=
      (by dsimp [s20]; push_cast; ring); have hr_eq : ((ratioHi * (100000000000000000000 - 1) : ℤ) :
      ℝ) = (ratioHi : ℝ) * (s20 - 1) := (by dsimp [s20]; push_cast; ring)
    rw [hl_eq, hr_eq] at hcast0; have h1 : ((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ) ≤
        ((ratioHi : ℝ) / (swScale : ℝ)) * (1 - 1 / s20) := by
      rw [div_mul_eq_mul_div]; have hdiv := div_le_div_of_nonneg_right hcast0 hs20_pos.le
      have hrew : (ratioHi : ℝ) * (s20 - 1) / s20 = (ratioHi : ℝ) * (1 - 1 / s20) :=
        (by field_simp [hs20_pos.ne']); have hrew0 : ((ratioHi - 1 : ℤ) : ℝ) * s20 / s20 = ((ratioHi
        - 1 : ℤ) : ℝ) := mul_div_cancel_right₀ _ hs20_pos.ne'
      rw [hrew0, hrew] at hdiv; exact div_le_div_of_nonneg_right hdiv hS.le
    have h2 : xk ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * α₀ := hxk_le.trans
      (mul_le_mul_of_nonneg_left hα_lb (div_nonneg (by exact_mod_cast (by omega : 0 ≤ ratioHi - 1))
      hS.le))
    have h3 : (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * α₀ ≤ (1 - 1 / s20) * (((ratioHi : ℝ) /
      (swScale : ℝ)) * α₀) := by
      have hm := mul_le_mul_of_nonneg_right h1 hα_pos.le; have hcomm : (((ratioHi : ℝ) / (swScale :
        ℝ)) * (1 - 1 / s20)) * α₀ = (1 - 1 / s20) * (((ratioHi : ℝ) / (swScale : ℝ)) * α₀) :=
        (by ring); exact hm.trans_eq hcomm
    have h4 : (1 - 1 / s20) * β ≤ (1 - 1 / s20) * (((ratioHi : ℝ) / (swScale : ℝ)) * α₀) :=
      (hβ_ub.trans h2).trans h3; have h1s20 : (0 : ℝ) < 1 - 1 / s20 := (by dsimp [s20]; norm_num)
    exact le_of_mul_le_mul_left h4 h1s20
  have hθ_eq : θ = 2 * β := (by dsimp [θ, swLThetaShiftReal, β, xk]; rw [hNd_eq]); rw [hθ_eq]
  exact ⟨by linarith, by linarith⟩
theorem checkSwLBucketAnglesL50_sound {L n r rMin rMax tauNum tauDen : ℕ}
    {ratios : List IvInt} {trigIvs : List (IvInt × IvInt)}
    (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax)
    (hchk : checkSwLBucketAnglesL50 L rMin rMax tauNum tauDen ratios trigIvs = true) :
    2 ≤ L ∧ L ≤ 50 ∧ L ≤ r ∧ r ≤ 1024 ∧ trigIvs.length = L ∧ let K_blk := swLKBlk n r tauNum tauDen
    let N : ℕ := 2 ^ n
    ∀ w : Fin L, memIvInt (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N r w.1)) (trigIvs.getD w.1
      ((0, 0), (0, 0))).1 ∧ memIvInt (Real.sin ((K_blk : ℝ) * swLThetaShiftReal N r w.1))
      (trigIvs.getD w.1 ((0, 0), (0, 0))).2 := by
  unfold checkSwLBucketAnglesL50 at hchk; simp only [withForcedInt_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hchk; rcases hchk with ⟨⟨hL2, hL50, hLrMin, _, hrMax1024, htau_pos,
    hden_pos, _, hlen_trig⟩, hm⟩; have hLr : L ≤ r := hLrMin.trans hmin; have hr1024 : r ≤ 1024 :=
    hmax.trans hrMax1024; rcases trigIvs with _ | ⟨⟨c0, s0⟩, restTrig⟩
  · simp at hm
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hm; rcases hm with ⟨htrig0,
    hrest⟩; refine ⟨hL2, hL50, hLr, hr1024, hlen_trig, ?_⟩; intro K_blk N w; have hS : (0 : ℝ) <
    (swScale : ℝ) := (by unfold swScale; norm_num); have hr_pos : (0 : ℝ) < (r : ℝ) :=
    (by exact_mod_cast (by omega : 0 < r))
  have hN96 : (79228162514264337593543950336 : ℝ) ≤ (N : ℝ) := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ (N : ℝ) := (by exact_mod_cast hpow); have hval : ((2 ^ 96 : ℕ) : ℝ) =
      79228162514264337593543950336 := (by norm_num); linarith
  set c₁ : ℝ := (N : ℝ) / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]
    exact (mul_le_mul_of_nonneg_left (mod_cast hr1024 : (r : ℝ) ≤ 1024) (by norm_num)).trans
      ((by norm_num : (8796093022208 : ℝ) ^ 2 * 1024 ≤ 79228162514264337593543950336).trans hN96)
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ :=
    (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]; exact Real.sqrt_le_sqrt hc1_ge)
  set α₀ : ℝ := Real.arcsin (1 / √c₁)
  rcases arcsin_small_boundsL (by positivity) (one_div_le_one_div_of_le (by norm_num)
    (by linarith : (8000000000000 : ℝ) ≤ √c₁)) with ⟨hα_pos, hα_le, _, _⟩; set tauR : ℝ := (tauNum :
    ℝ) / (tauDen : ℝ); have htau_nn : 0 ≤ tauR := (by positivity); set K₀ : ℕ := (round (tauR / (2 *
    α₀))).toNat; have hK_eq : K_blk = K₀ + 1 :=
    (by simp only [K_blk, swLKBlk, K₀, tauR, α₀, c₁, N, Nat.cast_pow, Nat.cast_ofNat])
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩; have hφ0_lo : tauR ≤ 2 *
    (K_blk : ℝ) * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith); have hφ0_hi : 2 *
    (K_blk : ℝ) * α₀ ≤ tauR + 3 * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  set s11 : ℤ := 100000000000; set q1HiNum : ℤ := (tauNum : ℤ) * s11 + (tauDen : ℤ)
  set q1HiDen : ℤ := (tauDen : ℤ) * s11
  have hq1_eq : (q1HiNum : ℝ) / (q1HiDen : ℝ) = tauR + 1 / (100000000000 : ℝ) := by
    dsimp [q1HiNum, q1HiDen, s11, tauR]; have hden_ne : (tauDen : ℝ) ≠ 0 := (by positivity)
    push_cast; field_simp [hden_ne]
  have hφ0_hi_q1 : 2 * (K_blk : ℝ) * α₀ ≤ (q1HiNum : ℝ) / (q1HiDen : ℝ) :=
    (by rw [hq1_eq]; linarith [hφ0_hi, hα_le]); rcases w with ⟨_ | idx, hw_lt⟩
  · have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hθ0_eq : swLThetaShiftReal N r 0 = 2 * α₀ := by
      unfold swLThetaShiftReal; simp only [Nat.cast_zero, mul_zero, sub_zero, α₀, c₁]; congr 2
      rw [Real.sqrt_div hr_pos.le, Real.sqrt_div hN_pos.le, one_div_div]
    have hφ_eq : (K_blk : ℝ) * swLThetaShiftReal N r 0 = 2 * (K_blk : ℝ) * α₀ :=
      (by rw [hθ0_eq]; ring); rw [hφ_eq]
    simpa using checkSwLTrigRat_sound (by simpa [tauR] using hφ0_lo) hφ0_hi_q1 htrig0
  · have hidx : idx < L - 1 := (by omega); rcases hrest idx hidx with ⟨hrat_w, htrig_w⟩
    rcases stratum_angle_ratio_boundsL50 hN96 hmin hmax hrat_w with ⟨hr_lo, hr_hi⟩; set rat :=
      ratios.getD idx (0, 0)
    have hrat_lo_nn : 0 ≤ (rat.1 : ℝ) / (swScale : ℝ) := by
      unfold checkSwLStratumRatioL50 at hrat_w; rw [decide_eq_true_eq] at hrat_w
      exact div_nonneg (by exact_mod_cast hrat_w.2.2.2.2.2.1.le) hS.le
    have hrat_hi_nn : 0 ≤ (rat.2 : ℝ) / (swScale : ℝ) := by
      unfold checkSwLStratumRatioL50 at hrat_w; rw [decide_eq_true_eq] at hrat_w
      exact div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ rat.2)) hS.le
    have hφ_lo : (((tauNum : ℤ) * rat.1 : ℤ) : ℝ) / (((tauDen : ℤ) * swScale : ℤ) : ℝ) ≤ (K_blk : ℝ)
      * swLThetaShiftReal N r (idx + 1) := by
      have hm1 := mul_le_mul_of_nonneg_left hr_lo (Nat.cast_nonneg K_blk); have hm2 :=
        mul_le_mul_of_nonneg_left hφ0_lo hrat_lo_nn; have hrew1 : (K_blk : ℝ) * (((rat.1 : ℝ) /
        (swScale : ℝ)) * (2 * α₀)) = ((rat.1 : ℝ) / (swScale : ℝ)) * (2 * (K_blk : ℝ) * α₀) :=
        (by ring); have hrew2 : (((tauNum : ℤ) * rat.1 : ℤ) : ℝ) / (((tauDen : ℤ) * swScale : ℤ) :
        ℝ) = ((rat.1 : ℝ) / (swScale : ℝ)) * tauR :=
        (by dsimp [tauR]; push_cast; rw [div_mul_div_comm]; congr 1 <;> ring); linarith
    have hφ_hi : (K_blk : ℝ) * swLThetaShiftReal N r (idx + 1) ≤ ((q1HiNum * rat.2 : ℤ) : ℝ) /
      ((q1HiDen * swScale : ℤ) : ℝ) := by
      have hm1 := mul_le_mul_of_nonneg_left hr_hi (Nat.cast_nonneg K_blk); have hm2 :=
        mul_le_mul_of_nonneg_left hφ0_hi_q1 hrat_hi_nn; have hrew1 : (K_blk : ℝ) * (((rat.2 : ℝ) /
        (swScale : ℝ)) * (2 * α₀)) = ((rat.2 : ℝ) / (swScale : ℝ)) * (2 * (K_blk : ℝ) * α₀) :=
        (by ring)
      have hrew2 : ((q1HiNum * rat.2 : ℤ) : ℝ) / ((q1HiDen * swScale : ℤ) : ℝ) = ((rat.2 : ℝ) /
        (swScale : ℝ)) * ((q1HiNum : ℝ) / (q1HiDen : ℝ)) := by
        rw [Int.cast_mul, Int.cast_mul, div_mul_div_comm, mul_comm (q1HiNum : ℝ), mul_comm (q1HiDen
          : ℝ)]
      linarith
    simpa using checkSwLTrigRat_sound hφ_lo hφ_hi htrig_w
/-- Pure-integer `L2Ball` bucket certificate checker (`2 ≤ L ≤ 50`, `pulses.length ≤ 400`). -/
def checkSwLBucketCertL2L50 (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L)) (tailLbs : List ℤ) (survUb : ℤ) : Bool :=
  decide (1 ≤ pulses.length ∧ pulses.length ≤ 400 ∧ tailLbs.length = L ∧ 0 ≤ survUb ∧
    0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0) &&
  pulses.all swLPulseValid &&
  (List.range (L - 1)).all (fun i ↦ decide (tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0)) &&
  checkSwLBucketAnglesL50 L rMin rMax tauNum tauDen ratios trigIvs &&
  withForcedL2State (swLEvolutionL2 L trigIvs pulses) fun evol ↦
    withForcedState (swLTerminalStateL2 evol.1 evol.2.1 evol.2.2) fun outIv ↦
      withForcedIv (ivAddInt (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1 (0, swOrbPad)))
        fun p0Iv ↦
          withForcedIv (ivSubInt (swScale, swScale) p0Iv) fun t1Iv ↦
            withForcedList (t1Iv :: swLTailSuffixIvs L outIv.1 outIv.2.1 (L - 1)) fun tailIvs ↦
              forceListId (swLClampTailLbs tailIvs) fun certLbs ↦
                decide (outIv.2.2.2 ≤ survUb ∧ certLbs.length = L) &&
                (List.range L).all fun i ↦ decide (tailLbs.getD i 0 ≤ certLbs.getD i 0)
theorem checkSwLBucketCertL2L50_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb : ℤ}
  (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk : checkSwLBucketCertL2L50 L rMin rMax
  tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) : ∃ (hL2 : 2 ≤ L), L ≤ 50 ∧ L ≤ r ∧ r ≤
  1024 ∧ 1 ≤ pulses.length ∧ pulses.length ≤ 400 ∧ pulses.all swLPulseValid = true ∧ tailLbs.length
  = L ∧ 0 ≤ survUb ∧ 0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0
  ∧ (∀ i : ℕ, i + 1 < L → tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0) ∧ ∀ (M : Fin (2 * L) → Fin (2 *
  L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        0 ≤ out.2.2 ∧ out.2.2 ≤ (survUb : ℝ) / (swScale : ℝ) ∧ ∀ c ∈ Finset.Icc 1 L, ((tailLbs.getD
          (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈ Finset.Icc c L, p h := by
  unfold checkSwLBucketCertL2L50 at hchk; simp only [withForcedL2State_eq, withForcedState_eq,
    withForcedIv_eq, withForcedList_eq, forceListId_eq, Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hp1, hp400, htl_len, hsurv0, htl0_pos, htl0_le, htlL0⟩, hp_val⟩, htl_mono⟩,
    hang⟩, ⟨hsurv_ub, _⟩, htl_le⟩
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at htl_mono htl_le
  rcases checkSwLBucketAnglesL50_sound hn96 hmin hmax hang with ⟨hL2, hL50, hLr, hr1024, _, htrig⟩
  refine ⟨hL2, hL50, hLr, hr1024, hp1, hp400, hp_val, htl_len, hsurv0, htl0_pos, htl0_le, htlL0, fun
    i hi ↦ htl_mono i (by omega), ?_⟩; intro M hM K_blk cs out p
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hcs_unit : ∀ w : Fin L,
    (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit pulses hp_val with ⟨hcons, hcum0, _, hsurv_nn⟩
  rcases memIvInt_evolutionL2 (cs := cs) hL2 hcs_unit htrig pulses hp_val with ⟨hst_mem, hcum_mem,
    hsurv_mem⟩; set evol := swLEvolutionL2 L trigIvs pulses
  set outIv := swLTerminalStateL2 evol.1 evol.2.1 evol.2.2; have hsurv_le : out.2.2 ≤ (survUb : ℝ) /
    (swScale : ℝ) := hsurv_mem.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hsurv_ub)
    hS.le); have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range (L + 1), p h = 1 := swLAttemptProbReal_sum_one hL2 hM hcons
  have hp0_mem : memIvInt (p 0) (ivAddInt (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1 (0, swOrbPad)))
    := by
    dsimp [p]; unfold swLAttemptProbReal; simp only [↓reduceIte]; have ho0 : memIvInt ((swLOrbitProj
      M out.1 ⟨0, by omega⟩) ^ 2) (swLOrbSqIv outIv.1 0) := memIvInt_swLOrbSqIv hM hst_mem ⟨0,
      by omega⟩
    have hoff0 : |M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩| ≤ (1 : ℝ) / 10 ^ 9 :=
      hM.2.2.2 _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    have hsq0 : (M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 ≤ (1 : ℝ) / 10 ^ 18 :=
      (by rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hoff0 2).trans_eq (by norm_num))
    have hpad0 : memIvInt ((M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2) (0, swOrbPad) := by
      unfold memIvInt swScale swOrbPad; dsimp only
      exact ⟨by linarith [sq_nonneg (M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩)], by linarith⟩
    exact memIvInt_ivAddInt ho0 (memIvInt_ivMulInt hcum_mem hpad0)
  have ht1_eq : ∑ h ∈ Finset.Icc 1 L, p h = 1 - p 0 := by
    have hsplit : ∑ h ∈ Finset.range (L + 1), p h = p 0 + ∑ h ∈ Finset.Icc 1 L, p h := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L + 1),
        Finset.Ico_add_one_right_eq_Icc]
    linarith [hp_sum1, hsplit]
  have ht1_mem : memIvInt (∑ h ∈ Finset.Icc 1 L, p h) (ivSubInt (swScale, swScale) (ivAddInt
    (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1 (0, swOrbPad)))) :=
    (by rw [ht1_eq]; exact memIvInt_ivSubInt memIvInt_one hp0_mem)
  rcases memIvInt_swLTailSuffixIvs hL2 hM hst_mem hcum_mem (L - 1) le_rfl with ⟨hsfx_len, hsfx⟩
  set tailIvs := ivSubInt (swScale, swScale) (ivAddInt (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1
    (0, swOrbPad))) :: swLTailSuffixIvs L outIv.1 outIv.2.1 (L - 1)
  have htailIvs_len : tailIvs.length = L := by dsimp [tailIvs]; simp [hsfx_len]; omega
  set tReal : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c L, p h
  have hclamp := swLClampTailLbs_sound tailIvs tReal 1
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; have ht0 : 0 ≤ tReal (1 + i) := Finset.sum_nonneg fun h _ ↦ hp_nn h
      have ht1 : tReal (1 + i) ≤ 1 := by
        have hsub : Finset.Icc (1 + i) L ⊆ Finset.range (L + 1) := fun h hh ↦ by
          rw [Finset.mem_Icc] at hh; rw [Finset.mem_range]; omega
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ ↦ hp_nn h).trans_eq hp_sum1
      refine ⟨ht0, ht1, ?_⟩; rcases i with _ | i'
      · simpa [tailIvs, tReal] using ht1_mem.1
      · have hi' : i' < L - 1 := (by omega); have hmem := hsfx i' hi'
        have hcc_eq : L + 1 - (L - 1) + i' = 1 + (i' + 1) := (by omega); rw [hcc_eq] at hmem
        simpa [tailIvs, tReal] using hmem.1)
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; dsimp [tReal]; exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_left (by omega)) fun h _ _ ↦ hp_nn h)
  refine ⟨hsurv_nn, hsurv_le, fun c hc ↦ ?_⟩; rw [Finset.mem_Icc] at hc; have hidx : c - 1 < L :=
    (by omega); have hle_cert := htl_le (c - 1) hidx
  have hcert_real := hclamp.2 (c - 1) (by rw [htailIvs_len]; exact hidx)
  have h1c : 1 + (c - 1) = c := (by omega); rw [h1c] at hcert_real
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hle_cert) hS.le).trans hcert_real
/-- Pure-integer `m = 1` multi-step Bellman recurrence check for `2 ≤ L ≤ 50`. -/
def checkSwLM1StepL50 (L r tauNum tauDen verCalls : ℕ)
    (tailLbs : List ℤ) (survUb vScale vCur : ℤ) (vPrevs : List ℤ) : Bool :=
  let chain := vCur :: vPrevs
  let rhsInt := (List.range L).foldl
    (fun acc c ↦ acc + tailLbs.getD c 0 * (chain.getD c 0 - chain.getD (c + 1) 0)) 0
  let bNum := 3 * survUb + 2 * swScale * (verCalls : ℤ)
  withForcedInt (rhsInt * swBden49 - vScale * bNum) fun rem ↦
    decide (2 ≤ L ∧ L ≤ 50 ∧ L ≤ r ∧ r ≤ 1024 ∧ 0 < tauNum ∧ 0 < tauDen ∧
      tailLbs.length = L ∧ vPrevs.length = L ∧ 0 ≤ survUb ∧ 0 < vScale ∧
      0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0 ∧
      0 ≤ chain.getD L 0 ∧ 0 ≤ rem ∧ (survUb * (tauNum : ℤ) * vScale * swBden49) ^ 2 ≤
        4 * ((tauDen : ℤ) ^ 2) * (r : ℤ) * (rem ^ 2)) &&
    (List.range (L - 1)).all (fun i ↦ decide (tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0)) &&
    (List.range L).all (fun i ↦ decide (chain.getD (i + 1) 0 ≤ chain.getD i 0))
/-- Table-indexed wrapper around `checkSwLM1StepL50`. -/
def checkSwLM1StepTableL50 (L r tauNum tauDen verCalls : ℕ)
    (tailLbs : List ℤ) (survUb vScale : ℤ) (vTable : ℕ → ℤ) : Bool :=
  checkSwLM1StepL50 L r tauNum tauDen verCalls tailLbs survUb vScale
    (vTable r) ((List.range L).map fun i ↦ vTable (r - (i + 1)))
/-- Pure-data `m = 1` conveyor stage specification (`0` QHL imports). -/
structure M1L50RawStageSpec where
  L : ℕ
  tauNum : ℕ
  tauDen : ℕ
  pulses : List (SwLPulseRat L)
/-- Soundness of `s: M1L50RawStageSpec` at rank `r` for `vScale` and `vTable` (`128 ≤ n`). -/
def M1L50StageSoundAt (vScale : ℤ) (vTable : ℕ → ℤ) (s : M1L50RawStageSpec) (r : ℕ) : Prop :=
  ∀ {n : ℕ}, 128 ≤ n → ∃ (hL2 : 2 ≤ s.L), s.L ≤ 50 ∧ s.L ≤ r ∧ s.pulses.all swLPulseValid = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
          ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
theorem m1L50StageSound_join {vScale : ℤ} {vTable : ℕ → ℤ} {stageOfR : ℕ → M1L50RawStageSpec} {a m b
  : ℕ} (h1 : ∀ r, a ≤ r → r ≤ m → M1L50StageSoundAt vScale vTable (stageOfR r) r) (h2 : ∀ r, m + 1 ≤
  r → r ≤ b → M1L50StageSoundAt vScale vTable (stageOfR r) r) : ∀ r, a ≤ r → r ≤ b →
  M1L50StageSoundAt vScale vTable (stageOfR r) r := by
  exact fun r ha hb ↦ if hr : r ≤ m then h1 r ha hr else h2 r (by omega) hb
theorem checkSwLM1StageL2L50_sound_n96 {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb vScale
  : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hbkt :
  checkSwLBucketCertL2L50 L rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb = true)
  (hstep : checkSwLM1StepTableL50 L r tauNum tauDen L tailLbs survUb vScale vTable = true) : ∃ (hL2
  : 2 ≤ L), L ≤ 50 ∧ L ≤ r ∧ pulses.all swLPulseValid = true ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) →
  ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (L : ℝ) + ∑ h ∈ Finset.Icc 1 L, p h * V (r - h)) /
          pSucc ≤ V r := by
  rcases checkSwLBucketCertL2L50_sound hn96 hmin hmax hbkt with ⟨hL2, hL50, hLr, hr1024, _, _,
    hp_val, _, _, htl0_pos, _, _, _, hbkt_M⟩
  unfold checkSwLM1StepTableL50 checkSwLM1StepL50 at hstep; simp only [withForcedInt_eq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hstep
  rcases hstep with ⟨⟨⟨_, _, _, _, htau, hden, _, _, hsurv0, hvsc_pos, _, _, _, _, hrem0, hsq_ineq⟩,
    _⟩, hchain_mono⟩; refine ⟨hL2, hL50, hLr, hp_val, ?_⟩; intro M hM K_blk cs out p pSucc V
  rcases hbkt_M M hM with ⟨_, hsurv_le, htail_lbs⟩; have hS : (0 : ℝ) < (swScale : ℝ) :=
    (by unfold swScale; norm_num); have hvsc_r : (0 : ℝ) < (vScale : ℝ) :=
    (by exact_mod_cast hvsc_pos); have hbden_r : (0 : ℝ) < (swBden49 : ℝ) :=
    (by unfold swBden49; norm_num); set N : ℝ := (2 ^ n : ℝ); have hsqrtN_pos : 0 < √N :=
    (by dsimp [N]; positivity)
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow); have h1 : (281474976710656 : ℝ) ^ 2 ≤ N :=
      (by have : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := (by norm_num); linarith)
    have h2 : (281474976710656 : ℝ) ≤ √N :=
      (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]; exact Real.sqrt_le_sqrt h1)
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := (by unfold swBden49; norm_num); linarith
  have hpSucc_pos : 0 < pSucc := by
    have hlb1 := htail_lbs 1 (by rw [Finset.mem_Icc]; omega); have hpos : 0 < ((tailLbs.getD 0 0 :
      ℤ) : ℝ) / (swScale : ℝ) := div_pos (by exact_mod_cast htl0_pos) hS; exact hpos.trans_le hlb1
  refine ⟨hpSucc_pos, ?_⟩; set chain : List ℤ := vTable r :: (List.range L).map fun i ↦ vTable (r -
    (i + 1))
  have hchain_eq : ∀ c ≤ L, chain.getD c 0 = vTable (r - c) := by
    intro c hc; rcases c with _ | c'
    · simp [chain]
    · have hc' : c' < L := (by omega); simp [chain, List.getD_eq_getElem?_getD, hc']
  set rhsInt : ℤ := ∑ c ∈ Finset.range L, tailLbs.getD c 0 * (chain.getD c 0 - chain.getD (c + 1) 0)
  have hfold_eq : (List.range L).foldl (fun acc c ↦ acc + tailLbs.getD c 0 * (chain.getD c 0 -
    chain.getD (c + 1) 0)) 0 = rhsInt := foldl_range_add_eq_sum L _; rw [hfold_eq] at hrem0 hsq_ineq
  have hgain_ge : ((rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ))) * √N ≤ ∑ h ∈ Finset.Icc 1 L, p h *
    (V r - V (r - h)) := by
    have habel := sum_Icc_abel L p (fun k ↦ V (r - k)); simp only [Nat.sub_zero] at habel
    rw [habel, show ((rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ))) * √N =
      ∑ c ∈ Finset.range L, (((tailLbs.getD c 0 : ℤ) : ℝ) / (swScale : ℝ)) *
          ((((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (vScale : ℝ)) * √N) by
      dsimp [rhsInt]; push_cast; rw [sum_div_const, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring]
    refine Finset.sum_le_sum fun c hc ↦ ?_; rw [Finset.mem_range] at hc
    have hmono_c := hchain_mono c hc; have hdiff_nn : 0 ≤ (((chain.getD c 0 - chain.getD (c + 1) 0 :
      ℤ) : ℝ) / (vScale : ℝ)) * √N := mul_nonneg (div_nonneg
      (by exact_mod_cast sub_nonneg.2 hmono_c) hvsc_r.le) hsqrtN_pos.le; have hV_eq : (((chain.getD
      c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (vScale : ℝ)) * √N = V (r - c) - V (r - (c + 1)) :=
      (by rw [hchain_eq c (by omega), hchain_eq (c + 1) (by omega)]; dsimp [V]; push_cast; ring)
    have htl_c := htail_lbs (c + 1) (by rw [Finset.mem_Icc]; omega)
    simp only [Nat.add_sub_cancel] at htl_c; rw [← hV_eq]
    exact mul_le_mul_of_nonneg_right htl_c hdiff_nn
  have hK_ub := kBlk_le_main_add_three_halves hn96 (by omega) hr1024 htau hden; set bNum : ℤ := 3 *
    survUb + 2 * swScale * (L : ℤ)
  have hcost_ub : out.2.2 * (K_blk : ℝ) + (L : ℝ) ≤ (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale :
    ℝ) * (tauDen : ℝ) * √(r : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
    have h1 : out.2.2 * (K_blk : ℝ) ≤ ((survUb : ℝ) / (swScale : ℝ)) * (((tauNum : ℝ) / (2 * (tauDen
      : ℝ) * √(r : ℝ))) * √N + 3 / 2) := mul_le_mul hsurv_le hK_ub (Nat.cast_nonneg K_blk)
      (div_nonneg (by exact_mod_cast hsurv0) hS.le)
    have hbNum_nn : 0 ≤ (bNum : ℝ) := by
      dsimp [bNum]; unfold swScale
      exact_mod_cast (by omega : (0 : ℤ) ≤ 3 * survUb + 2 * 1000000000 * (L : ℤ))
    have hoverh : (bNum : ℝ) / (2 * (swScale : ℝ)) ≤ ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)))
      * √N := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtN_ge (div_nonneg hbNum_nn (mul_pos hS hbden_r).le)
      refine (?_ : (bNum : ℝ) / (2 * (swScale : ℝ)) = ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 :
        ℝ))) * ((swBden49 : ℝ) / 2)).trans_le hmul; field_simp [hS.ne', hbden_r.ne']
    have halg : ((survUb : ℝ) / (swScale : ℝ)) * (((tauNum : ℝ) / (2 * (tauDen : ℝ) * √(r : ℝ))) *
      √N + 3 / 2) + (L : ℝ) = (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) *
      √(r : ℝ))) * √N + (bNum : ℝ) / (2 * (swScale : ℝ)) :=
      (by dsimp [bNum]; push_cast; field_simp [hS.ne']; ring); linarith
  set rem : ℤ := rhsInt * swBden49 - vScale * bNum
  have hcoef_le : ((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ)) +
    (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)) ≤ (rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ))
    := by
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hsqrt_r_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
    have hden_r : (0 : ℝ) < (tauDen : ℝ) := (by exact_mod_cast hden); have hrem_r : (0 : ℝ) ≤ (rem :
      ℝ) := (by exact_mod_cast hrem0)
    have hlhs_nn : 0 ≤ (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) :=
      (by have : (0 : ℝ) ≤ (survUb : ℝ) := (by exact_mod_cast hsurv0); positivity)
    have hrhs_nn : 0 ≤ 2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ) := by positivity
    have hsq_r : ((survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) ^ 2 ≤ (2 * (tauDen :
      ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 := by
      have hcast : ((survUb * (tauNum : ℤ) * vScale * swBden49) ^ 2 : ℝ) ≤ ((4 * ((tauDen : ℤ) ^ 2)
        * (r : ℤ) * (rem ^ 2) : ℤ) : ℝ) := (by exact_mod_cast hsq_ineq)
      push_cast at hcast; have hsq_rhs : (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 =
          4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2 := by
        calc (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2
          _ = 4 * (tauDen : ℝ) ^ 2 * (√(r : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by ring
          _ = 4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
      linarith
    have hroot : (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) ≤ 2 * (tauDen : ℝ) *
      √(r : ℝ) * (rem : ℝ) :=
      (by rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_r)
    have hrem_def : (rem : ℝ) = (rhsInt : ℝ) * (swBden49 : ℝ) - (vScale : ℝ) * (bNum : ℝ) :=
      (by dsimp [rem]; push_cast; rfl); rw [hrem_def] at hroot; have hpos_prod : 0 < 2 * (swScale :
      ℝ) * (tauDen : ℝ) * √(r : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) := (by positivity)
    rw [← sub_nonneg]; have hdiff : (rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ)) -
        (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ)) +
          (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) = (2 * (tauDen : ℝ) * √(r : ℝ) *
            ((rhsInt : ℝ) * (swBden49 : ℝ) - (vScale : ℝ) * (bNum : ℝ)) -
          (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) /
        (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) := by
      field_simp [hS.ne', hden_r.ne', hsqrt_r_pos.ne', hvsc_r.ne', hbden_r.ne']; ring
    rw [hdiff]; exact div_nonneg (by linarith) hpos_prod.le
  have hnet : out.2.2 * (K_blk : ℝ) + (L : ℝ) ≤ ∑ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) :=
    (hcost_ub.trans (mul_le_mul_of_nonneg_right hcoef_le hsqrtN_pos.le)).trans hgain_ge
  have hexpand : ∑ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) = pSucc * V r - ∑ h ∈ Finset.Icc 1 L,
    p h * V (r - h) := by
    dsimp [pSucc]; rw [Finset.sum_mul]; have hsub : ∀ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) =
        p h * V r - p h * V (r - h) := fun _ _ ↦ mul_sub _ _ _; rw [Finset.sum_congr rfl hsub,
      Finset.sum_sub_distrib]
  rw [div_le_iff₀ hpSucc_pos]; linarith [hnet, hexpand]
theorem checkSwLM1StageL2L50_sound {L r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt} {trigIvs
  : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb vScale : ℤ}
  {vTable : ℕ → ℤ} (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hbkt : checkSwLBucketCertL2L50 L rMin rMax
  tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) (hstep : checkSwLM1StepTableL50 L r
  tauNum tauDen L tailLbs survUb vScale vTable = true) : M1L50StageSoundAt vScale vTable ⟨L, tauNum,
  tauDen, pulses⟩ r :=
  fun hn128 ↦ checkSwLM1StageL2L50_sound_n96 (by omega : 96 ≤ _) hmin hmax hbkt hstep
/- ## 2. Compact `16`-Bit / `32`-Bit Unpackers & Precompiled Bucket Checkers -/
/-- WHNF-forcing wrapper for a `List ℕ`. -/
def forceNatList {α : Type} : List ℕ → (List ℕ → α) → α
  | [], k => k []
  | x :: xs, k => kpForceNat x fun x' ↦ forceNatList xs fun xs' ↦ k (x' :: xs')
theorem forceNatList_eq {α : Type} (xs : List ℕ) (k : List ℕ → α) : forceNatList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => unfold forceNatList; rw [kpForceNat_eq, ih]
/-- Unpack `k` `16`-bit `+32768`-biased words into `+262144`-biased `Nat`s (`+229376`). -/
def split16Bias : ℕ → ℕ → List ℕ × ℕ
  | 0, raw => ([], raw)
  | k + 1, raw =>
      kpForceNat (Nat.add (Nat.mod raw 65536) 229376) fun x ↦
        kpForceNat (Nat.div raw 65536) fun r1 ↦
          match split16Bias k r1 with
          | (xs, rest) => (x :: xs, rest)
theorem split16Bias_length : ∀ (k raw : ℕ), (split16Bias k raw).1.length = k
  | 0, _ => rfl
  | k + 1, raw => by
    unfold split16Bias; simp only [kpForceNat_eq]; rcases h : split16Bias k (Nat.div raw 65536) with
      ⟨xs, rest⟩; have ih := split16Bias_length k (Nat.div raw 65536); rw [h] at ih; simp [ih]
/-- Unpack `k` consecutive `32`-bit words (`< 2^32 = 4294967296`) from `raw`. -/
def split32 : ℕ → ℕ → List ℕ × ℕ
  | 0, raw => ([], raw)
  | k + 1, raw =>
      kpForceNat (Nat.mod raw 4294967296) fun x ↦
        kpForceNat (Nat.div raw 4294967296) fun r1 ↦
          match split32 k r1 with
          | (xs, rest) => (x :: xs, rest)
theorem split32_length : ∀ (k raw : ℕ), (split32 k raw).1.length = k
  | 0, _ => rfl
  | k + 1, raw => by
    unfold split32; simp only [kpForceNat_eq]; rcases h : split32 k (Nat.div raw 4294967296) with
      ⟨xs, rest⟩; have ih := split32_length k (Nat.div raw 4294967296); rw [h] at ih; simp [ih]
/-- Unpack `numP` `m = 1` pulses `(bus, bv)` (`16` bits per parameter, lifted to `+262144`). -/
def unpackPulsesM1_16 (L : ℕ) : ℕ → ℕ → List (List ℕ × ℕ)
  | 0, _ => []
  | p + 1, raw =>
      kpForceNat (Nat.add (Nat.mod raw 65536) 229376) fun bv ↦
        kpForceNat (Nat.div raw 65536) fun r1 ↦
          match split16Bias (Nat.sub L 1) r1 with
          | (bus, rest) => (bus, bv) :: unpackPulsesM1_16 L p rest
theorem unpackPulsesM1_16_length (L : ℕ) : ∀ (numP raw : ℕ), (unpackPulsesM1_16 L numP raw).length =
  numP
  | 0, _ => rfl
  | p + 1, raw => by
    unfold unpackPulsesM1_16; simp only [kpForceNat_eq]; rcases split16Bias (Nat.sub L 1) (Nat.div
      raw 65536) with ⟨bus, rest⟩; simp [unpackPulsesM1_16_length L p rest]
/-- Convert a `+262144`-biased `(bus, bv)` pair into `SwLPulseRat L` (`uvDen = 65536`). -/
def decodePulseRaw (L : ℕ) (pv : List ℕ × ℕ) : SwLPulseRat L :=
  ⟨fun w0 ↦ kpFastSubNatNat (pv.1.getD w0.1 262144) 262144,
   kpFastSubNatNat pv.2 262144, 65536⟩
theorem decodePulseRaw_valid (L : ℕ) (pv : List ℕ × ℕ) : swLPulseValid (decodePulseRaw L pv) = true
  := by unfold swLPulseValid decodePulseRaw; rfl
/-- Total pulse count across blocked `(k, raw)` schedule pairs. -/
def sumBlockPulses : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (k, _) :: bs => Nat.add k (sumBlockPulses bs)
/-- Unpack blocked `(k, raw)` schedule pairs (`k ≤ 16`) into `(bus, bv)` pulses. -/
def unpackBlocksM1_16 (L : ℕ) : List (ℕ × ℕ) → List (List ℕ × ℕ)
  | [] => []
  | (k, raw) :: bs => unpackPulsesM1_16 L k raw ++ unpackBlocksM1_16 L bs
theorem unpackBlocksM1_16_length (L : ℕ) : ∀ (bs : List (ℕ × ℕ)), (unpackBlocksM1_16 L bs).length =
  sumBlockPulses bs
  | [] => rfl
  | (k, raw) :: bs => by
    simp only [unpackBlocksM1_16, sumBlockPulses, List.length_append, unpackPulsesM1_16_length,
      unpackBlocksM1_16_length L bs, nat_add_eq]
/-- Decode a blocked `16`-bit `m = 1` schedule into `List (SwLPulseRat L)`. -/
def decodeBlocksM1_16 (L : ℕ) (bs : List (ℕ × ℕ)) : List (SwLPulseRat L) :=
  (unpackBlocksM1_16 L bs).map (decodePulseRaw L)
/-- Unpack `k` pairs `(lo, hi)` biased by `+ 2*10^9` (`32` bits each) into `+ 2*10^{11}`
  `Nat`s. -/
def unpackPairsBias : ℕ → ℕ → List (ℕ × ℕ) × ℕ
  | 0, raw => ([], raw)
  | k + 1, raw =>
      kpForceNat (Nat.add (Nat.mod raw 4294967296) 198000000000) fun lo ↦
        kpForceNat (Nat.div raw 4294967296) fun r1 ↦
          kpForceNat (Nat.add (Nat.mod r1 4294967296) 198000000000) fun hi ↦
            kpForceNat (Nat.div r1 4294967296) fun r2 ↦
              match unpackPairsBias k r2 with
              | (ps, rest) => ((lo, hi) :: ps, rest)
theorem unpackPairsBias_length : ∀ (k raw : ℕ), (unpackPairsBias k raw).1.length = k
  | 0, _ => rfl
  | k + 1, raw => by
    unfold unpackPairsBias; simp only [kpForceNat_eq]; rcases h : unpackPairsBias k (Nat.div
      (Nat.div raw 4294967296) 4294967296) with ⟨ps, rest⟩
    have ih := unpackPairsBias_length k (Nat.div (Nat.div raw 4294967296) 4294967296); rw [h] at ih;
      simp [ih]
/-- Unpack `k` `(cosIv, sinIv)` quads (`32` bits each, `+ 2*10^9`) into `+ 2*10^{11}` quads. -/
def unpackTrigBias : ℕ → ℕ → List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ
  | 0, raw => ([], raw)
  | k + 1, raw =>
      kpForceNat (Nat.add (Nat.mod raw 4294967296) 198000000000) fun cLo ↦
        kpForceNat (Nat.div raw 4294967296) fun r1 ↦
          kpForceNat (Nat.add (Nat.mod r1 4294967296) 198000000000) fun cHi ↦
            kpForceNat (Nat.div r1 4294967296) fun r2 ↦
              kpForceNat (Nat.add (Nat.mod r2 4294967296) 198000000000) fun sLo ↦
                kpForceNat (Nat.div r2 4294967296) fun r3 ↦
                  kpForceNat (Nat.add (Nat.mod r3 4294967296) 198000000000) fun sHi ↦
                    kpForceNat (Nat.div r3 4294967296) fun r4 ↦
                      match unpackTrigBias k r4 with
                      | (qs, rest) => (((cLo, cHi), (sLo, sHi)) :: qs, rest)
theorem unpackTrigBias_length : ∀ (k raw : ℕ), (unpackTrigBias k raw).1.length = k
  | 0, _ => rfl
  | k + 1, raw => by
    unfold unpackTrigBias; simp only [kpForceNat_eq]; rcases h : unpackTrigBias k
      (Nat.div (Nat.div (Nat.div (Nat.div raw 4294967296) 4294967296) 4294967296) 4294967296)
      with ⟨qs, rest⟩; have ih := unpackTrigBias_length k (Nat.div (Nat.div (Nat.div (Nat.div raw
      4294967296) 4294967296) 4294967296) 4294967296); rw [h] at ih; simp [ih]
/-- Unpack `(tailLbsNat, uRatios, uTrig)` from a single `rawMeta: ℕ`. -/
def unpackMeta (L rawMeta : ℕ) : List ℕ × List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  match split32 L rawMeta with
  | (tlNat, r1) =>
      match unpackPairsBias (Nat.sub L 1) r1 with
      | (uRat, r2) => (tlNat, uRat, (unpackTrigBias L r2).1)
theorem unpackMeta_lengths (L rawMeta : ℕ) : (unpackMeta L rawMeta).1.length = L ∧ (unpackMeta L
  rawMeta).2.1.length = L - 1 ∧ (unpackMeta L rawMeta).2.2.length = L := by
  unfold unpackMeta; rcases h1 : split32 L rawMeta with ⟨tlNat, r1⟩; dsimp only
  rcases h2 : unpackPairsBias (Nat.sub L 1) r1 with ⟨uRat, r2⟩; dsimp only; have hl1 :=
    split32_length L rawMeta; have hl2 := unpackPairsBias_length (Nat.sub L 1) r1; rw [h1] at hl1;
    rw [h2] at hl2; exact ⟨hl1, hl2, unpackTrigBias_length L r2⟩
/-- Reassemble a non-negative integer from little-endian `352`-bit limbs
  (`Nat.add`/`Nat.mul`). -/
def packLimbs320 : List ℕ → ℕ
  | [] => 0
  | w :: ws =>
      Nat.add w (Nat.mul
        0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
        (packLimbs320 ws))
/-- Decode a `2 * 10^{11}`-biased `Nat` to `ℤ`. -/
def decZ (u : ℕ) : ℤ := (u : ℤ) - 200000000000
/-- Decode a `2 * 10^{11}`-biased `ℕ × ℕ` pair to `IvInt`. -/
def decIv (p : ℕ × ℕ) : IvInt := (decZ p.1, decZ p.2)
/-- Pure-GMP `+ 2 * 10^{11}` decoder to `ℤ` (`0` `HSub.hSub`). -/
def kpDecZ (u : ℕ) : ℤ := kpFastSubNatNat u 200000000000
/-- Pure-GMP `+ 2 * 10^{11}` interval decoder to `IvInt`. -/
def kpDecIv (p : ℕ × ℕ) : IvInt := (kpDecZ p.1, kpDecZ p.2)
theorem kpDecZ_eq : kpDecZ = decZ := by
  funext u; unfold kpDecZ decZ; rw [kpFastSubNatNat_eq]; change Int.subNatNat u 200000000000 =
    Int.sub (.ofNat u) (.ofNat 200000000000); rfl
theorem kpDecIv_eq : kpDecIv = decIv := by funext p; unfold kpDecIv decIv; rw [kpDecZ_eq]
/-- WHNF-forcing wrapper for `List KpPrePulse` so schedule intervals evaluate once per
  chunk. -/
def kpWithPrePulses {α : Type} : List KpPrePulse → (List KpPrePulse → α) → α
  | [], k => k []
  | (cv, ups) :: pps, k =>
      kpForceIv cv fun cv' ↦
        kpWithPairList ups fun ups' ↦
          kpWithPrePulses pps fun pps' ↦ k ((cv', ups') :: pps')
theorem kpWithPrePulses_eq {α : Type} (pps : List KpPrePulse) (k : List KpPrePulse → α) :
    kpWithPrePulses pps k = k pps := by induction pps generalizing k with
  | nil => rfl
  | cons pp pps ih =>
    rcases pp with ⟨cv, ups⟩; unfold kpWithPrePulses; rw [kpForceIv_eq, kpWithPairList_eq, ih]
/-- Force a non-negative GMP literal into `Int.ofNat` with zero lambda allocation. -/
def m1OfNat (q : ℕ) : ℤ := Nat.casesOn (Nat.add q 1) (.ofNat 0) Int.ofNat
private theorem m1OfNat_eq (q : ℕ) : m1OfNat q = Int.ofNat q := rfl
/-- Force a GMP literal into `Int.negSucc` with zero lambda allocation. -/
def m1NegSucc (q : ℕ) : ℤ := Nat.casesOn (Nat.add q 1) (.ofNat 0) Int.negSucc
private theorem m1NegSucc_eq (q : ℕ) : m1NegSucc q = Int.negSucc q := rfl
/-- Single-eval pure-GMP `Int.negOfNat` avoiding `Nat.beq` double-evaluation. -/
def m1NegOfNat (q : ℕ) : ℤ := Nat.casesOn q (.ofNat 0) Int.negSucc
private theorem m1NegOfNat_eq (q : ℕ) : m1NegOfNat q = kpFastNegOfNat q := by
  rw [kpFastNegOfNat_eq]; cases q <;> rfl
/-- Pure-GMP `Int.subNatNat` with forced `Literal.natVal` payload (`0` lambdas). -/
def m1SubNatNat (m n : ℕ) : ℤ := Nat.casesOn (Nat.sub n m) (m1OfNat (Nat.sub m n)) Int.negSucc
private theorem m1SubNatNat_eq (m n : ℕ) : m1SubNatNat m n = Int.subNatNat m n := by
  unfold m1SubNatNat Int.subNatNat m1OfNat; simp only [nat_sub_eq]; cases n - m <;> rfl
/-- Pure-GMP `Int.add` with zero lambda allocation. -/
def m1AddZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => m1OfNat (Nat.add m n)
  | .ofNat m, .negSucc n => m1SubNatNat m (Nat.add n 1)
  | .negSucc m, .ofNat n => m1SubNatNat n (Nat.add m 1)
  | .negSucc m, .negSucc n => m1NegSucc (Nat.add (Nat.add m n) 1)
private theorem m1AddZ_eq (x y : ℤ) : m1AddZ x y = Int.add x y := by
  rw [int_add_eq]; rcases x with m | m <;> rcases y with n | n <;> simp only [m1AddZ, m1OfNat_eq,
    m1NegSucc_eq, m1SubNatNat_eq, Int.subNatNat_eq_coe, Int.ofNat_eq_natCast, Int.negSucc_eq,
    nat_add_eq] <;> omega
/-- Pure-GMP `Int.sub` without intermediate `kpFastNegZ` allocation. -/
def m1SubZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => m1SubNatNat m n
  | .ofNat m, .negSucc n => m1OfNat (Nat.add m (Nat.add n 1))
  | .negSucc m, .ofNat n => m1NegSucc (Nat.add m n)
  | .negSucc m, .negSucc n => m1SubNatNat (Nat.add n 1) (Nat.add m 1)
private theorem m1SubZ_eq (x y : ℤ) : m1SubZ x y = Int.sub x y := by
  rw [int_sub_eq]; rcases x with m | m <;> rcases y with n | n <;> simp only [m1SubZ, m1OfNat_eq,
    m1NegSucc_eq, m1SubNatNat_eq, Int.subNatNat_eq_coe, Int.ofNat_eq_natCast, Int.negSucc_eq,
    nat_add_eq] <;> omega
/-- Strict `IvInt` constructor forcing both `ℤ` endpoints once to WHNF. -/
def m1MkIv (lo hi : ℤ) : IvInt :=
  Int.casesOn lo
    (fun a ↦ Int.casesOn hi (fun b ↦ (.ofNat a, .ofNat b)) (fun b ↦ (.ofNat a, .negSucc b)))
    (fun a ↦ Int.casesOn hi (fun b ↦ (.negSucc a, .ofNat b)) (fun b ↦ (.negSucc a, .negSucc b)))
private theorem m1MkIv_eq (lo hi : ℤ) : m1MkIv lo hi = (lo, hi) := by cases lo <;> cases hi <;> rfl
/-- Strict `IvInt` binder evaluating `iv` and both `ℤ` endpoints once before `k`. -/
def m1LetIv {α : Type} (iv : IvInt) (k : IvInt → α) : α :=
  Prod.casesOn iv fun lo hi ↦
    Int.casesOn lo
      (fun a ↦ Int.casesOn hi
        (fun b ↦ k (.ofNat a, .ofNat b)) (fun b ↦ k (.ofNat a, .negSucc b)))
      (fun a ↦ Int.casesOn hi
        (fun b ↦ k (.negSucc a, .ofNat b)) (fun b ↦ k (.negSucc a, .negSucc b)))
private theorem m1LetIv_eq {α : Type} (iv : IvInt) (k : IvInt → α) : m1LetIv iv k = k iv := by
  rcases iv with ⟨a | a, b | b⟩ <;> rfl
/-- Strictly forced `10^9`-scale interval addition (`1` eval per input pair). -/
def m1IvAdd (a b : IvInt) : IvInt :=
  Prod.casesOn a fun a1 a2 ↦
    Prod.casesOn b fun b1 b2 ↦ m1MkIv (m1AddZ a1 b1) (m1AddZ a2 b2)
private theorem m1IvAdd_eq (a b : IvInt) : m1IvAdd a b = kpIvAdd a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; simp only [m1IvAdd, kpIvAdd, m1MkIv_eq, m1AddZ_eq,
    kpForceInt_eq]
/-- Strictly forced `10^9`-scale interval subtraction (`1` eval per input pair). -/
def m1IvSub (a b : IvInt) : IvInt :=
  Prod.casesOn a fun a1 a2 ↦
    Prod.casesOn b fun b1 b2 ↦ m1MkIv (m1SubZ a1 b2) (m1SubZ a2 b1)
private theorem m1IvSub_eq (a b : IvInt) : m1IvSub a b = kpIvSub a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; simp only [m1IvSub, kpIvSub, m1MkIv_eq, m1SubZ_eq,
    kpForceInt_eq]
/-- Single-eval `ℕ` ceiling division `⌈n / 10^9⌉` as `ℤ`. -/
def m1NatCeilDivScale (n : ℕ) : ℤ := m1OfNat (Nat.div (Nat.add n 999999999) 1000000000)
private theorem m1NatCeilDivScale_eq (n : ℕ) : m1NatCeilDivScale n = kpNatCeilDivScale n := by
  unfold m1NatCeilDivScale kpNatCeilDivScale
  generalize Nat.div (Nat.add n 999999999) 1000000000 = q; rw [m1OfNat_eq, kpForceNat_eq]
/-- Single-eval `ℕ` floor division `⌊(-n) / 10^9⌋` as `ℤ` (`0` double-eval). -/
def m1NegFloorDivScale (n : ℕ) : ℤ := m1NegOfNat (Nat.div (Nat.add n 999999999) 1000000000)
private theorem m1NegFloorDivScale_eq (n : ℕ) : m1NegFloorDivScale n = kpNegFloorDivScale n :=
  by simp only [m1NegFloorDivScale, kpNegFloorDivScale, m1NegOfNat_eq]
/-- Single-eval `ℕ` ceiling division `⌈(-n) / 10^9⌉` as `ℤ` (`0` double-eval). -/
def m1NegCeilDivScale (n : ℕ) : ℤ := m1NegOfNat (Nat.div n 1000000000)
private theorem m1NegCeilDivScale_eq (n : ℕ) : m1NegCeilDivScale n = kpNegCeilDivScale n := by
  simp only [m1NegCeilDivScale, kpNegCeilDivScale, m1NegOfNat_eq]
/-- Zero-lambda `Nat`-direct point-interval product `a * (z, z)`. -/
def m1MulIvPt (a : IvInt) (z : ℤ) : IvInt :=
  match a with
  | (.ofNat c1, .ofNat c2) =>
      cond (Nat.ble c1 c2)
        (match z with
         | .ofNat m =>
             (m1OfNat (Nat.div (Nat.mul c1 m) 1000000000), m1NatCeilDivScale (Nat.mul c2 m))
         | .negSucc m =>
             let m1 := Nat.add m 1
             (m1NegFloorDivScale (Nat.mul c2 m1), m1NegCeilDivScale (Nat.mul c1 m1)))
        (kpMulIvPtFastCore (.ofNat c1) (.ofNat c2) z)
  | (.ofNat c1, .negSucc c2) => kpMulIvPtFastCore (.ofNat c1) (.negSucc c2) z
  | (.negSucc c1, .ofNat c2) =>
      match z with
      | .ofNat m =>
          (m1NegFloorDivScale (Nat.mul (Nat.add c1 1) m), m1NatCeilDivScale (Nat.mul c2 m))
      | .negSucc m =>
          (m1NegFloorDivScale (Nat.mul c2 (Nat.add m 1)),
           m1NatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add m 1)))
  | (.negSucc c1, .negSucc c2) =>
      cond (Nat.ble c2 c1)
        (match z with
         | .ofNat m =>
             (m1NegFloorDivScale (Nat.mul (Nat.add c1 1) m),
              m1NegCeilDivScale (Nat.mul (Nat.add c2 1) m))
         | .negSucc m =>
             let m1 := Nat.add m 1
             (m1OfNat (Nat.div (Nat.mul (Nat.add c2 1) m1) 1000000000),
              m1NatCeilDivScale (Nat.mul (Nat.add c1 1) m1)))
        (kpMulIvPtFastCore (.negSucc c1) (.negSucc c2) z)
private theorem m1MulIvPt_eq (a : IvInt) (z : ℤ) : m1MulIvPt a z = kpIvMul a (z, z) := by
  rw [← kpMulIvPtFast_eq]
  rcases a with ⟨c1 | c1, c2 | c2⟩ <;> cases z <;> simp only [m1MulIvPt, kpMulIvPtFast,
    m1OfNat_eq, kpForceNat_eq, m1NatCeilDivScale_eq, m1NegFloorDivScale_eq, m1NegCeilDivScale_eq]
/-- Zero-lambda `2`-mul `Nat`-direct `10^9`-scale interval product `a * b`. -/
def m1IvMul (a b : IvInt) : IvInt :=
  match a with
  | (.ofNat c1, .ofNat c2) =>
      cond (Nat.ble c1 c2)
        (match b with
         | (.ofNat d1, .ofNat d2) =>
             cond (Nat.ble d1 d2) (m1OfNat (Nat.div (Nat.mul c1 d1) 1000000000),
                m1NatCeilDivScale (Nat.mul c2 d2))
               (kpIvMulFastCore (.ofNat c1) (.ofNat c2) (.ofNat d1) (.ofNat d2))
         | (.ofNat d1, .negSucc d2) =>
             kpIvMulFastCore (.ofNat c1) (.ofNat c2) (.ofNat d1) (.negSucc d2)
         | (.negSucc d1, .ofNat d2) =>
             (m1NegFloorDivScale (Nat.mul c2 (Nat.add d1 1)), m1NatCeilDivScale (Nat.mul c2 d2))
         | (.negSucc d1, .negSucc d2) =>
             cond (Nat.ble d2 d1) (m1NegFloorDivScale (Nat.mul c2 (Nat.add d1 1)),
                m1NegCeilDivScale (Nat.mul c1 (Nat.add d2 1)))
               (kpIvMulFastCore (.ofNat c1) (.ofNat c2) (.negSucc d1) (.negSucc d2)))
        (kpIvMulFastCore (.ofNat c1) (.ofNat c2) b.1 b.2)
  | (.ofNat c1, .negSucc c2) => kpIvMulFastCore (.ofNat c1) (.negSucc c2) b.1 b.2
  | (.negSucc c1, .ofNat c2) =>
      match b with
      | (.ofNat d1, .ofNat d2) =>
          cond (Nat.ble d1 d2) (m1NegFloorDivScale (Nat.mul (Nat.add c1 1) d2),
             m1NatCeilDivScale (Nat.mul c2 d2))
            (kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.ofNat d1) (.ofNat d2))
      | (.ofNat d1, .negSucc d2) =>
          kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.ofNat d1) (.negSucc d2)
      | (.negSucc d1, .ofNat d2) =>
          kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.negSucc d1) (.ofNat d2)
      | (.negSucc d1, .negSucc d2) =>
          cond (Nat.ble d2 d1) (m1NegFloorDivScale (Nat.mul c2 (Nat.add d1 1)),
             m1NatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add d1 1)))
            (kpIvMulFastCore (.negSucc c1) (.ofNat c2) (.negSucc d1) (.negSucc d2))
  | (.negSucc c1, .negSucc c2) =>
      cond (Nat.ble c2 c1)
        (match b with
         | (.ofNat d1, .ofNat d2) =>
             cond (Nat.ble d1 d2) (m1NegFloorDivScale (Nat.mul (Nat.add c1 1) d2),
                m1NegCeilDivScale (Nat.mul (Nat.add c2 1) d1))
               (kpIvMulFastCore (.negSucc c1) (.negSucc c2) (.ofNat d1) (.ofNat d2))
         | (.ofNat d1, .negSucc d2) =>
             kpIvMulFastCore (.negSucc c1) (.negSucc c2) (.ofNat d1) (.negSucc d2)
         | (.negSucc d1, .ofNat d2) =>
             (m1NegFloorDivScale (Nat.mul (Nat.add c1 1) d2),
              m1NatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add d1 1)))
         | (.negSucc d1, .negSucc d2) =>
             cond (Nat.ble d2 d1)
               (m1OfNat (Nat.div (Nat.mul (Nat.add c2 1) (Nat.add d2 1)) 1000000000),
                m1NatCeilDivScale (Nat.mul (Nat.add c1 1) (Nat.add d1 1)))
               (kpIvMulFastCore (.negSucc c1) (.negSucc c2) (.negSucc d1) (.negSucc d2)))
        (kpIvMulFastCore (.negSucc c1) (.negSucc c2) b.1 b.2)
private theorem m1IvMul_eq (a b : IvInt) : m1IvMul a b = kpIvMul a b := by
  rw [← kpIvMulFast_eq]
  rcases a with ⟨c1 | c1, c2 | c2⟩ <;> rcases b with ⟨d1 | d1, d2 | d2⟩ <;> simp only [m1IvMul,
    kpIvMulFast, m1OfNat_eq, kpForceNat_eq, m1NatCeilDivScale_eq, m1NegFloorDivScale_eq,
    m1NegCeilDivScale_eq]
/-- Zero-CPS constructor-matched `O(L)` Grover plane walk (`1` eval per coordinate). -/
def m1GroverWalk : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, (cw, sw) :: ts', ce :: co :: cs' =>
      m1LetIv (m1IvSub (m1MulIvPt cw ce) (m1MulIvPt sw co)) fun e' ↦
        m1LetIv (m1IvAdd (m1MulIvPt sw ce) (m1MulIvPt cw co)) fun o' ↦
          e' :: o' :: m1GroverWalk k ts' cs'
  | k + 1, [], cs => kpGroverWalk (k + 1) [] cs
  | k + 1, (cw, sw) :: ts', [] => kpGroverWalk (k + 1) ((cw, sw) :: ts') []
  | k + 1, (cw, sw) :: ts', [ce] => kpGroverWalk (k + 1) ((cw, sw) :: ts') [ce]
private theorem m1GroverWalk_eq : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ), m1GroverWalk
  k ts cs = kpGroverWalk k ts cs
  | 0, _, _ => rfl | k + 1, [], _ => rfl | k + 1, _ :: _, [] => rfl | k + 1, _ :: _, [_] => rfl
  | k + 1, (cw, sw) :: ts', ce :: co :: cs' => by
    unfold m1GroverWalk kpGroverWalk
    change m1LetIv (m1IvSub (m1MulIvPt cw ce) (m1MulIvPt sw co)) (fun e' ↦
        m1LetIv (m1IvAdd (m1MulIvPt sw ce) (m1MulIvPt cw co)) fun o' ↦
          e' :: o' :: m1GroverWalk k ts' cs') =
      kpForceIv (kpIvSub (kpIvMul cw (ce, ce)) (kpIvMul sw (co, co))) fun e' ↦
        kpForceIv (kpIvAdd (kpIvMul sw (ce, ce)) (kpIvMul cw (co, co))) fun o' ↦
          match kpGroverWalk k ts' cs' with
          | [] => [e', o'] | hd :: tl => e' :: o' :: hd :: tl
    simp only [m1LetIv_eq, kpForceIv_eq, m1IvSub_eq, m1IvAdd_eq, m1MulIvPt_eq, m1GroverWalk_eq k]
    cases kpGroverWalk k ts' cs' <;> rfl
/-- Zero-CPS constructor-matched `O(L)` Pieri + weak-measurement walk (`1` eval per pair). -/
def m1PieriWalk (cv : IvInt) : ℕ → List (IvInt × IvInt) → List IvInt → List IvInt
  | 0, _, h0 :: _ => m1LetIv (m1IvMul cv h0) fun top ↦ [top]
  | 0, _, [] => m1LetIv (m1IvMul cv (.ofNat 0, .ofNat 0)) fun top ↦ [top]
  | k + 1, (cu, su) :: us', lv :: rv :: ss' =>
      m1LetIv (m1IvSub (m1IvMul cu lv) (m1IvMul su rv)) fun l' ↦
        m1LetIv (m1IvAdd (m1IvMul su lv) (m1IvMul cu rv)) fun r' ↦
          l' :: r' :: m1PieriWalk cv k us' ss'
  | k + 1, [], ss => kpPieriWalk cv (k + 1) [] ss
  | k + 1, (cu, su) :: us', [] => kpPieriWalk cv (k + 1) ((cu, su) :: us') []
  | k + 1, (cu, su) :: us', [lv] => kpPieriWalk cv (k + 1) ((cu, su) :: us') [lv]
private theorem m1PieriWalk_eq (cv : IvInt) : ∀ (k : ℕ) (us : List (IvInt × IvInt)) (ss : List
  IvInt), m1PieriWalk cv k us ss = kpPieriWalk cv k us ss
  | 0, _, [] => by
    unfold m1PieriWalk kpPieriWalk; change m1LetIv (m1IvMul cv (.ofNat 0, .ofNat 0)) (fun top ↦
      [top]) = kpForceIv (kpIvMul cv (.ofNat 0, .ofNat 0)) fun top ↦ [top]; rw [m1LetIv_eq,
      kpForceIv_eq, m1IvMul_eq]
  | 0, _, h0 :: _ => by
    unfold m1PieriWalk kpPieriWalk
    change m1LetIv (m1IvMul cv h0) (fun top ↦ [top]) = kpForceIv (kpIvMul cv h0) fun top ↦ [top]
    rw [m1LetIv_eq, kpForceIv_eq, m1IvMul_eq]
  | k + 1, [], _ => rfl | k + 1, _ :: _, [] => rfl | k + 1, _ :: _, [_] => rfl
  | k + 1, (cu, su) :: us', lv :: rv :: ss' => by
    unfold m1PieriWalk kpPieriWalk
    change m1LetIv (m1IvSub (m1IvMul cu lv) (m1IvMul su rv)) (fun l' ↦
        m1LetIv (m1IvAdd (m1IvMul su lv) (m1IvMul cu rv)) fun r' ↦
          l' :: r' :: m1PieriWalk cv k us' ss') =
      kpForceIv (kpIvSub (kpIvMul cu lv) (kpIvMul su rv)) fun l' ↦
        kpForceIv (kpIvAdd (kpIvMul su lv) (kpIvMul cu rv)) fun r' ↦
          match kpPieriWalk cv k us' ss' with
          | [] => [l', r'] | hd :: tl => l' :: r' :: hd :: tl
    simp only [m1LetIv_eq, kpForceIv_eq, m1IvSub_eq, m1IvAdd_eq, m1IvMul_eq, m1PieriWalk_eq cv k]
    cases kpPieriWalk cv k us' ss' <;> rfl
/-- Zero-CPS Pieri + weak-measurement step over `KpPrePulse`. -/
def m1PieriAndWeak : ℕ → KpPrePulse → List IvInt → List IvInt
  | 0, _, _ => []
  | m + 1, (cv, ups), h0 :: naTail => h0 :: m1PieriWalk cv m ups naTail
  | m + 1, (cv, ups), [] => (.ofNat 0, .ofNat 0) :: m1PieriWalk cv m ups []
private theorem m1PieriAndWeak_eq : ∀ (L : ℕ) (pp : KpPrePulse) (naIv : List IvInt), m1PieriAndWeak
  L pp naIv = kpPieriAndWeakPre L pp naIv
  | 0, _, _ => rfl
  | m + 1, (cv, ups), [] => by
    unfold m1PieriAndWeak kpPieriAndWeakPre; dsimp only; rw [m1PieriWalk_eq]
    change (.ofNat 0, .ofNat 0) :: kpPieriWalk cv m ups [] =
      match kpPieriWalk cv m ups [] with
      | [] => [(.ofNat 0, .ofNat 0)] | hd :: tl => (.ofNat 0, .ofNat 0) :: hd :: tl
    cases kpPieriWalk cv m ups [] <;> rfl
  | m + 1, (cv, ups), h0 :: naTail => by
    unfold m1PieriAndWeak kpPieriAndWeakPre; dsimp only; rw [m1PieriWalk_eq]
    change h0 :: kpPieriWalk cv m ups naTail =
      match kpPieriWalk cv m ups naTail with
      | [] => [h0] | hd :: tl => h0 :: hd :: tl
    cases kpPieriWalk cv m ups naTail <;> rfl
private theorem kpIvMidRad_of_add {lo hi : ℤ} {d : ℕ} (hd : hi = lo + (d : ℤ)) : kpIvMidRad (lo, hi)
  = (lo + ((d / 2 : ℕ) : ℤ), (d + 1) / 2) := by
  unfold kpIvMidRad kpMaxZ; simp only [kpForceInt_eq, kpForceNat_eq, kpBleZ_eq_decide, int_add_eq,
    int_sub_eq]; have h2 : (.ofNat 2 : ℤ) = 2 := rfl; have hed : Int.ediv (lo + hi) 2 = (lo + hi) /
    2 := rfl; rw [h2, hed]; set q : ℕ := d / 2; set rem : ℕ := d % 2; have hq : 2 * q + rem = d :=
    Nat.div_add_mod d 2; have hrem : rem < 2 := Nat.mod_lt d (by omega); have hmid : (lo + hi) / 2 =
    lo + (q : ℤ) := (by omega); rw [hmid]; have hle : lo + (q : ℤ) - lo ≤ hi - (lo + (q : ℤ)) :=
    (by omega); rw [decide_eq_true hle, Bool.cond_true]; exact Prod.ext rfl (by dsimp only; omega)
/-- Zero-closure pure-`Nat` midpoint and radius for ordered `IvInt` (`lo ≤ hi`). -/
def m1IvMidRad : IvInt → ℤ × ℕ
  | (.ofNat a, .ofNat b) =>
      cond (Nat.ble a b)
        (let d := Nat.sub b a
         (m1OfNat (Nat.add a (Nat.div d 2)), Nat.div (Nat.add d 1) 2))
        (kpIvMidRad (.ofNat a, .ofNat b))
  | (.negSucc a, .ofNat b) =>
      let a1 := Nat.add a 1
      let d := Nat.add b a1
      (m1SubNatNat (Nat.div d 2) a1, Nat.div (Nat.add d 1) 2)
  | (.negSucc a, .negSucc b) =>
      cond (Nat.ble b a)
        (let d := Nat.sub a b
         (m1NegSucc (Nat.sub a (Nat.div d 2)), Nat.div (Nat.add d 1) 2))
        (kpIvMidRad (.negSucc a, .negSucc b))
  | iv => kpIvMidRad iv
private theorem m1IvMidRad_eq (iv : IvInt) : m1IvMidRad iv = kpIvMidRad iv := by
  rcases iv with ⟨a | a, b | b⟩
  · unfold m1IvMidRad; dsimp only; cases h : Nat.ble a b
    · rfl
    · have hab : a ≤ b := Nat.ble_eq.mp h; rw [Bool.cond_true, kpIvMidRad_of_add (d := b - a)
        (by simp only [Int.ofNat_eq_natCast]; omega)]; simp only [m1OfNat_eq, Int.ofNat_eq_natCast,
        nat_sub_eq, nat_add_eq, nat_div_eq]; ext <;> dsimp only; omega
  · rfl
  · unfold m1IvMidRad; dsimp only; rw [kpIvMidRad_of_add (d := b + (a + 1))
      (by simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega)]; simp only [m1SubNatNat_eq,
      Int.subNatNat_eq_coe, Int.negSucc_eq, nat_add_eq, nat_div_eq]; ext <;> dsimp only; omega
  · unfold m1IvMidRad; dsimp only; cases h : Nat.ble b a
    · rfl
    · have hba : b ≤ a := Nat.ble_eq.mp h; rw [Bool.cond_true, kpIvMidRad_of_add (d := a - b)
        (by omega)]; simp only [m1NegSucc_eq, nat_sub_eq, nat_add_eq, nat_div_eq]
      ext <;> dsimp only; omega
/-- Tail-recursive list reversal returning `(out, radSq)` only after full spine forcing. -/
def m1RevZPair : List ℤ → List ℤ → ℕ → List ℤ × ℕ
  | [], out, radSq => (out, radSq)
  | x :: xs, out, radSq => m1RevZPair xs (x :: out) radSq
private theorem m1RevZPair_eq : ∀ (xs out : List ℤ) (radSq : ℕ), m1RevZPair xs out radSq =
  (xs.reverse ++ out, radSq)
  | [], out, radSq => by simp [m1RevZPair]
  | x :: xs, out, radSq => by
    simp [m1RevZPair, m1RevZPair_eq xs (x :: out) radSq, List.reverse_cons]
/-- Zero-CPS tail-recursive `O(L)` recentering and squared-radius accumulator. -/
def m1RecenterRev : List IvInt → List ℤ → ℕ → List ℤ × ℕ
  | [], revCs, acc => m1RevZPair revCs [] acc
  | iv :: ivs, revCs, acc =>
      Prod.casesOn (m1IvMidRad iv) fun mid rad0 ↦
        Nat.casesOn (Nat.add rad0 1) ([], 0) fun rad ↦
          Nat.casesOn (Nat.add (Nat.add acc (Nat.mul rad rad)) 1) ([], 0) fun acc' ↦
            kpForceInt mid fun mid' ↦ m1RecenterRev ivs (mid' :: revCs) acc'
private theorem m1RecenterRev_eq : ∀ (ivs : List IvInt) (revCs : List ℤ) (acc : ℕ), m1RecenterRev
  ivs revCs acc = (revCs.reverse ++ (kpRecenterAndRadSq ivs).1, acc + (kpRecenterAndRadSq ivs).2)
  | [], revCs, acc => by simp [m1RecenterRev, m1RevZPair_eq, kpRecenterAndRadSq]
  | iv :: ivs, revCs, acc => by
    unfold m1RecenterRev kpRecenterAndRadSq; rw [m1IvMidRad_eq]
    rcases kpIvMidRad iv with ⟨v | v, rad0⟩ <;>
    · dsimp only; rw [kpForceInt_eq, m1RecenterRev_eq ivs]
      rcases kpRecenterAndRadSq ivs with ⟨_ | ⟨hd, tl⟩, tailAcc⟩ <;>
      · simp only [kpForceInt_eq, kpForceNat_eq, nat_add_eq, nat_mul_eq, List.reverse_cons,
          List.append_assoc, List.singleton_append]; exact Prod.ext rfl (by dsimp only; omega)
/-- First-order `L2Ball` conveyor pulse step (`0` per-coordinate CPS closures). -/
def m1PulseStep (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) (pp : KpPrePulse) : List ℤ × ℕ × ℤ :=
  kpForceNat (kpSumSqAbsFast cVec 0) fun normSqC ↦
    kpForceNat (fastCeilIsqrt normSqC) fun normCUb ↦
      kpForceNat (Nat.add normCUb rho) fun sumR ↦
        kpForceInt (m1NatCeilDivScale (Nat.mul sumR sumR)) fun ceilSq ↦
          let oneMinusCumUb := kpFastMinZ (.ofNat 1000000000) ceilSq
          let survNext := m1AddZ survUb oneMinusCumUb
          match m1RecenterRev (m1PieriAndWeak L pp (m1GroverWalk L trigIvs cVec)) [] 0 with
          | (cNext, radSqSum) =>
              Nat.casesOn (Nat.add (Nat.add rho (fastCeilIsqrt radSqSum)) 1)
                ([], 0, .ofNat 0) fun rho' ↦
                Int.casesOn survNext (fun sv ↦ (cNext, rho', .ofNat sv))
                  (fun sv ↦ (cNext, rho', .negSucc sv))
private theorem m1PulseStep_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) (cVec : List ℤ) (rho : ℕ)
  (survUb : ℤ) (pp : KpPrePulse) : m1PulseStep L trigIvs cVec rho survUb pp = kpPulseStepL2Pre L
  trigIvs cVec rho survUb pp := by
  unfold m1PulseStep kpPulseStepL2Pre; simp only [kpForceNat_eq, kpForceInt_eq, kpWithIvList_eq,
    kpSumSqAbsFast_eq, fastCeilIsqrt_eq, m1NatCeilDivScale_eq, kpNatCeilDivScale_eq,
    kpFastMinZ_eq, m1AddZ_eq, m1PieriAndWeak_eq, m1GroverWalk_eq, m1RecenterRev_eq,
    List.reverse_nil, List.nil_append, Nat.zero_add]; rcases kpRecenterAndRadSq (kpPieriAndWeakPre L
    pp (kpGroverWalk L trigIvs cVec)) with ⟨cNext, radSqSum⟩; dsimp only
  set s := Int.add survUb (kpMinZ (.ofNat 1000000000) (Int.neg (Int.ediv (Int.neg (.ofNat (Nat.mul
    (Nat.add (kpCeilIsqrtNat (kpSumSqAbs cVec 0)) rho) (Nat.add (kpCeilIsqrtNat (kpSumSqAbs cVec 0))
    rho)))) (.ofNat 1000000000)))); cases s <;> rfl
/-- Primitive `List.rec` multi-pulse `L2Ball` trajectory loop (`0` CPS closures). -/
def m1EvolutionAux (L : ℕ) (trigIvs : List (IvInt × IvInt)) :
    List KpPrePulse → List ℤ → ℕ → ℤ → List ℤ × ℕ × ℤ
  | [], cVec, rho, survUb => (cVec, rho, survUb)
  | pp :: pps, cVec, rho, survUb =>
      Prod.casesOn (m1PulseStep L trigIvs cVec rho survUb pp) fun cNext rest ↦
        Prod.casesOn rest fun rho' survUb' ↦ m1EvolutionAux L trigIvs pps cNext rho' survUb'
private theorem m1EvolutionAux_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) : ∀ (pps : List
  KpPrePulse) (cVec : List ℤ) (rho : ℕ) (survUb : ℤ), m1EvolutionAux L trigIvs pps cVec rho survUb =
  kpEvolutionL2AuxPre L trigIvs cVec rho survUb pps
  | [], _, _, _ => rfl
  | pp :: pps, cVec, rho, survUb => by
    unfold m1EvolutionAux kpEvolutionL2AuxPre; rw [m1PulseStep_eq, kpWithL2State_eq]
    rcases kpPulseStepL2Pre L trigIvs cVec rho survUb pp with ⟨cNext, rho', survUb'⟩
    exact m1EvolutionAux_eq L trigIvs pps cNext rho' survUb'
/-- First-order multi-pulse `L2Ball` trajectory from `(|b_0, 0⟩, 0, 0)`. -/
def m1EvolutionL2Pre (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (pps : List KpPrePulse) : List ℤ × ℕ × ℤ :=
  kpWithIntList (.ofNat 1000000000 :: List.replicate (Nat.sub (Nat.mul 2 L) 1) (.ofNat 0))
    fun cInit ↦ m1EvolutionAux L trigIvs pps cInit 0 (.ofNat 0)
private theorem m1EvolutionL2Pre_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) (pps : List KpPrePulse)
  : m1EvolutionL2Pre L trigIvs pps = kpEvolutionL2Pre L trigIvs pps := by
  unfold m1EvolutionL2Pre kpEvolutionL2Pre; simp only [kpWithIntList_eq, m1EvolutionAux_eq]
private theorem kpIvAdd_zero_left (a : IvInt) : kpIvAdd (.ofNat 0, .ofNat 0) a = a := by
  rcases a with ⟨a1, a2⟩; have hz : (.ofNat 0 : ℤ) = 0 := rfl; simp only [kpIvAdd, kpForceInt_eq,
    int_add_eq, hz, zero_add]
private theorem kpIvAdd_zero_right (a : IvInt) : kpIvAdd a (.ofNat 0, .ofNat 0) = a := by
  rcases a with ⟨a1, a2⟩; have hz : (.ofNat 0 : ℤ) = 0 := rfl; simp only [kpIvAdd, kpForceInt_eq,
    int_add_eq, hz, add_zero]
private theorem kpIvAdd_assoc (a b c : IvInt) : kpIvAdd (kpIvAdd a b) c = kpIvAdd a (kpIvAdd b c) :=
  by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; rcases c with ⟨c1, c2⟩; simp only [kpIvAdd,
    kpForceInt_eq, int_add_eq, add_assoc]
/-- Linear `O(L)` right-to-left suffix accumulator for orbit linear forms. -/
def m1OrbSuffPairs : List IvInt → IvInt × List (IvInt × IvInt)
  | [] => ((.ofNat 0, .ofNat 0), [])
  | sj :: sjs =>
      match m1OrbSuffPairs sjs with
      | (suff, rest) =>
          m1LetIv (m1IvMul sj (.negSucc 0, .ofNat 1)) fun ej ↦
            m1LetIv (m1IvAdd ej suff) fun tot ↦ (tot, (sj, suff) :: rest)
/-- Linear `O(L)` left-to-right squared orbit projection walk. -/
def m1OrbSqWalk : IvInt → List (IvInt × IvInt) → List IvInt
  | _, [] => []
  | pref, (sj, suff) :: rest =>
      let mHit := m1IvMul sj (.ofNat 999999999, .ofNat 1000000000)
      let sq := kpIvSqFast (m1IvAdd (m1IvAdd pref mHit) suff)
      m1LetIv (m1IvAdd pref (m1IvMul sj (.negSucc 0, .ofNat 1))) fun pref' ↦
        m1LetIv sq fun sq' ↦ sq' :: m1OrbSqWalk pref' rest
/-- Linear `O(L)` batch computation of all `2 * L` squared orbit intervals. -/
def m1AllOrbSq (stIv : List IvInt) : IvInt × List IvInt :=
  match m1OrbSuffPairs stIv with
  | (totLin, pairs) =>
      m1LetIv (kpIvSqFast totLin) fun totSq ↦
        kpWithIvList (m1OrbSqWalk (.ofNat 0, .ofNat 0) pairs) fun orbs ↦ (totSq, orbs)
private theorem kpOrbLinAux_of_gt : ∀ (xs : List IvInt) (o j : ℕ) (acc : IvInt), o < j → kpOrbLinAux
  o j acc xs = kpIvAdd acc (m1OrbSuffPairs xs).1
  | [], _, _, acc, _ => (kpIvAdd_zero_right acc).symm
  | sj :: sjs, o, j, acc, hlt => by
    unfold kpOrbLinAux m1OrbSuffPairs; rcases hsp : m1OrbSuffPairs sjs with ⟨suff, rest⟩; dsimp only
    simp only [swLNatBeq_eq_decide j o, decide_eq_false (by omega : j ≠ o), Bool.cond_false,
      kpForceIv_eq, m1LetIv_eq, m1IvMul_eq, m1IvAdd_eq]; have hlt' : o < Nat.add j 1 :=
      (by rw [nat_add_eq]; omega); rw [kpOrbLinAux_of_gt sjs o (Nat.add j 1) _ hlt', hsp,
      kpIvAdd_assoc]
private theorem m1OrbSqWalk_getD : ∀ (xs : List IvInt) (o j : ℕ) (pref : IvInt), j ≤ o →
  (m1OrbSqWalk pref (m1OrbSuffPairs xs).2).getD (o - j) (kpIvSq (kpIvAdd pref (m1OrbSuffPairs
  xs).1)) = kpIvSq (kpOrbLinAux o j pref xs)
  | [], _, _, pref, _ => by
    unfold m1OrbSuffPairs m1OrbSqWalk kpOrbLinAux; dsimp only; rw [List.getD_nil,
      kpIvAdd_zero_right]
  | sj :: sjs, o, j, pref, hj => by
    unfold m1OrbSuffPairs kpOrbLinAux; rcases hsp : m1OrbSuffPairs sjs with ⟨suff, rest⟩
    dsimp only; simp only [m1LetIv_eq, m1IvMul_eq, m1IvAdd_eq, kpForceIv_eq]; unfold m1OrbSqWalk
    dsimp only; simp only [m1LetIv_eq, m1IvMul_eq, m1IvAdd_eq, kpIvSqFast_eq]
    by_cases heq : o = j
    · cases heq; simp only [Nat.sub_self, List.getD_cons_zero, Nat.beq_refl o, Bool.cond_true]
      have hlt : o < Nat.add o 1 := (by rw [nat_add_eq]; omega); rw [kpOrbLinAux_of_gt sjs o
        (Nat.add o 1) _ hlt, hsp]
    · have hlt : j < o := Nat.lt_of_le_of_ne hj (Ne.symm heq)
      have hsub : o - j = (o - Nat.add j 1) + 1 := by rw [nat_add_eq]; omega
      have hj' : Nat.add j 1 ≤ o := (by rw [nat_add_eq]; omega); rw [hsub, List.getD_cons_succ,
        swLNatBeq_eq_decide j o, decide_eq_false (Ne.symm heq), Bool.cond_false, ← kpIvAdd_assoc]
      have ih := m1OrbSqWalk_getD sjs o (Nat.add j 1) (kpIvAdd pref (kpIvMul sj
        (.negSucc 0, .ofNat 1))) hj'; rw [hsp] at ih; exact ih
private theorem m1AllOrbSq_getD (stIv : List IvInt) (o : ℕ) : (m1AllOrbSq stIv).2.getD o (m1AllOrbSq
  stIv).1 = kpOrbSqIv stIv o := by
  unfold m1AllOrbSq kpOrbSqIv
  have hwalk := m1OrbSqWalk_getD stIv o 0 (.ofNat 0, .ofNat 0) (Nat.zero_le o)
  rcases hsp : m1OrbSuffPairs stIv with ⟨totLin, pairs⟩; rw [hsp] at hwalk; dsimp only at hwalk ⊢
  simp only [m1LetIv_eq, kpWithIvList_eq, kpIvSqFast_eq]
  rw [Nat.sub_zero, kpIvAdd_zero_left] at hwalk; exact hwalk
/-- Linear `O(L)` suffix sum of squared orbit intervals for `c = L - m.. L`. -/
def m1TailSuffixIvs (L : ℕ) (orbs : List IvInt) (totSq cumIv : IvInt) : ℕ → List IvInt
  | 0 => []
  | m + 1 =>
      let c := Nat.sub L m
      cond (Nat.beq c L) (m1LetIv (m1IvAdd (orbs.getD (Nat.sub (Nat.mul 2 L) 1) totSq)
            (m1IvMul cumIv (kpIvSqFast (.ofNat 999999999, .ofNat 1000000000))))
          fun topIv ↦ [topIv])
        (match m1TailSuffixIvs L orbs totSq cumIv m with
         | [] => []
         | nextIv :: rest =>
             let phIv := m1IvAdd
               (m1IvAdd (orbs.getD (Nat.sub (Nat.mul 2 c) 1) totSq) (orbs.getD (Nat.mul 2 c) totSq))
               (m1IvMul cumIv (.ofNat 0, .ofNat 2))
             m1LetIv (m1IvAdd phIv nextIv) fun curIv ↦ curIv :: nextIv :: rest)
private theorem m1TailSuffixIvs_eq (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ∀ (m : ℕ),
  m1TailSuffixIvs L (m1AllOrbSq stIv).2 (m1AllOrbSq stIv).1 cumIv m = kpTailSuffixIvs L stIv cumIv m
  | 0 => rfl
  | m + 1 => by
    unfold m1TailSuffixIvs kpTailSuffixIvs; dsimp only; by_cases h : Nat.sub L m = L
    · simp only [swLNatBeq_eq_decide (Nat.sub L m) L, decide_eq_true h, Bool.cond_true, m1LetIv_eq,
        kpForceIv_eq, m1IvAdd_eq, m1IvMul_eq, kpIvSqFast_eq, m1AllOrbSq_getD]
    · simp only [swLNatBeq_eq_decide (Nat.sub L m) L, decide_eq_false h, Bool.cond_false,
        m1TailSuffixIvs_eq L stIv cumIv m]
      cases kpTailSuffixIvs L stIv cumIv m with
      | nil => rfl
      | cons nextIv rest =>
          simp only [m1LetIv_eq, kpForceIv_eq, m1IvAdd_eq, m1IvMul_eq, m1AllOrbSq_getD]
/-- Pure-GMP precompiled `m = 1` `L2Ball` bucket checker (`0` `witLimbs`, `0`
  `mulBias`). -/
def checkBucketPreDecodedL50 (L rMin rMax tauNum tauDen numP : ℕ)
    (pps : List KpPrePulse) (tlNat : List ℕ)
    (uRat : List (ℕ × ℕ)) (uTrig : List ((ℕ × ℕ) × (ℕ × ℕ))) (survUbNat : ℕ) : Bool :=
  kpWithIntList (tlNat.map Int.ofNat) fun tails' ↦
    kpWithIvList (uRat.map kpDecIv) fun rats' ↦
      kpWithPairList (uTrig.map fun q ↦ (kpDecIv q.1, kpDecIv q.2)) fun trigs' ↦
        let surv' : ℤ := Int.ofNat survUbNat
        let t0 := tails'.getD 0 (.ofNat 0)
        let tLast := tails'.getD (Nat.sub L 1) (.ofNat 0)
        (Nat.ble 1 numP && (Nat.ble numP 400 && (kpFastBleZ (.ofNat 1) t0 &&
        (kpFastBleZ t0 (.ofNat 1000000000) && kpFastBleZ (.ofNat 0) tLast)))) &&
        kpAllRange (fun i ↦ kpFastBleZ (tails'.getD (Nat.add i 1) (.ofNat 0))
          (tails'.getD i (.ofNat 0))) (Nat.sub L 1) &&
        kpCheckSwLBucketAnglesL50 L rMin rMax tauNum tauDen rats' trigs' &&
        match m1EvolutionL2Pre L trigs' pps with
        | (cVec, rho, survEvol) =>
            kpTerminalStateL2FastCPS cVec rho survEvol fun stIv cumIv survOut ↦
            match m1AllOrbSq stIv with
            | (totSq, orbs) =>
            m1LetIv (m1IvAdd (orbs.getD 0 totSq) (m1IvMul cumIv (.ofNat 0, .ofNat 1)))
              fun p0Iv ↦
                m1LetIv (m1IvSub (.ofNat 1000000000, .ofNat 1000000000) p0Iv)
                  fun t1Iv ↦
                    kpWithIvList (t1Iv :: m1TailSuffixIvs L orbs totSq cumIv (Nat.sub L 1))
                      fun tailIvs ↦
                        kpWithIntList (kpClampTailLbsFast tailIvs) fun certLbs ↦
                          (kpFastBleZ survOut surv' && Nat.beq certLbs.length L) &&
                          kpAllRange (fun i ↦
                            kpFastBleZ (tails'.getD i (.ofNat 0)) (certLbs.getD i (.ofNat 0))) L
theorem checkBucketPreDecodedL50_sound {L rMin rMax tauNum tauDen numP : ℕ} {pulses : List
  (SwLPulseRat L)} {pps : List KpPrePulse} {tlNat : List ℕ} {uRat : List (ℕ × ℕ)} {uTrig : List ((ℕ
  × ℕ) × (ℕ × ℕ))} {survUbNat : ℕ} (hp_len : pulses.length = numP) (hp_val : pulses.all
  swLPulseValid = true) (hpps : kpCompilePulsesFast L pulses = pps) (htl_len : tlNat.length = L)
  (hok : checkBucketPreDecodedL50 L rMin rMax tauNum tauDen numP pps tlNat uRat uTrig survUbNat =
  true) : checkSwLBucketCertL2L50 L rMin rMax tauNum tauDen (uRat.map decIv) (uTrig.map fun q ↦
  (decIv q.1, decIv q.2)) pulses (tlNat.map Int.ofNat) (survUbNat : ℤ) = true := by
  subst hpps; rw [kpCompilePulsesFast_eq] at hok; unfold checkBucketPreDecodedL50 at hok
  have hsub : Nat.sub L 1 = L - 1 := rfl; have hz0 : (.ofNat 0 : ℤ) = 0 := rfl; have hz1 : (.ofNat 1
    : ℤ) = 1 := rfl; have hpad1 : (.ofNat 1 : ℤ) = swOrbPad := rfl; have hsc : (.ofNat 1000000000 :
    ℤ) = swScale := rfl; simp only [kpDecIv_eq, kpWithIntList_eq, kpWithIvList_eq,
    kpWithPairList_eq, kpFastBleZ_eq, kpCheckSwLBucketAnglesL50_eq, kpAllRange_eq,
    swLNatBle_eq_decide, kpBleZ_eq_decide, nat_add_eq, hsub, Bool.and_eq_true] at hok
  rcases hok with ⟨⟨⟨hhead, hmono⟩, hang⟩, htail⟩; rw [m1EvolutionL2Pre_eq,
    kpEvolutionL2Pre_compile, kpEvolutionL2_eq] at htail; rcases hev : swLEvolutionL2 L (uTrig.map
    fun q ↦ (decIv q.1, decIv q.2)) pulses with ⟨cVec, rho, survEvol⟩
  rw [hev] at htail; dsimp only at htail
  rw [kpTerminalStateL2FastCPS_eq, kpTerminalStateL2_eq] at htail
  rcases hterm : swLTerminalStateL2 cVec rho survEvol with ⟨stIv, cumIv, survLo, survT⟩
  rw [hterm] at htail; dsimp only at htail; have horb0 : (m1AllOrbSq stIv).2.getD 0 (m1AllOrbSq
    stIv).1 = kpOrbSqIv stIv 0 := m1AllOrbSq_getD stIv 0; have htsuf : m1TailSuffixIvs L (m1AllOrbSq
    stIv).2 (m1AllOrbSq stIv).1 cumIv (L - 1) = kpTailSuffixIvs L stIv cumIv (L - 1) :=
    m1TailSuffixIvs_eq L stIv cumIv (L - 1)
  rcases horbs : m1AllOrbSq stIv with ⟨totSq, orbs⟩; rw [horbs] at horb0 htsuf htail
  dsimp only at horb0 htsuf htail; simp only [m1LetIv_eq, m1IvAdd_eq, m1IvSub_eq, m1IvMul_eq, horb0,
    htsuf, kpClampTailLbsFast_eq, kpIvAdd_eq, kpOrbSqIv_eqP, kpIvMul_eq, kpIvSub_eq,
    kpTailSuffixIvs_eqP, kpClampTailLbs_eqP, ivAddIntP_eq, swLOrbSqIvP_eq, ivMulIntP_eq,
    ivSubIntP_eq, swLTailSuffixIvsP_eq, swLClampTailLbsP_eq, swLNatBeq_eq_decide, hsc, hpad1, hz0,
    Bool.and_eq_true] at htail
  rcases htail with ⟨⟨hsurvT, hclen⟩, hall⟩; unfold checkSwLBucketCertL2L50
  simp only [withForcedL2State_eq, withForcedState_eq, withForcedIv_eq, withForcedList_eq,
    forceListId_eq, Bool.and_eq_true]; rw [hev, hterm]; dsimp only; simp only [hz0, hz1, hsc,
    decide_eq_true_eq] at hhead hmono; refine ⟨⟨⟨⟨?_, hp_val⟩, hmono⟩, hang⟩, ?_⟩
  · rw [decide_eq_true_eq]; simp only [List.length_map, hp_len, htl_len]; rcases hhead with ⟨hn1,
      hn400, ht0_1, ht0_sc, htlast⟩; exact ⟨hn1, hn400, trivial, Nat.cast_nonneg _,
      by linarith, ht0_sc, htlast⟩
  · exact ⟨decide_eq_true ⟨of_decide_eq_true hsurvT, of_decide_eq_true hclen⟩,
      by simpa only [List.all_eq_true, List.mem_range, decide_eq_true_eq] using hall⟩
/- ## 3. Table Monotonicity, Bellman Step & Contiguous Schedule-Chunk Checkers -/
/-- `100%`-`Nat` pure-GMP monotonicity checker for `vTable r = (vTableNat r: ℤ)`. -/
def checkSwLTableMonoNatL50 (kMax : ℕ) (vTableNat : ℕ → ℕ) : Bool :=
  kpAllRange (fun j ↦ Nat.ble (vTableNat j) (vTableNat (Nat.add j 1))) kMax
theorem checkSwLTableMonoNatL50_sound {kMax : ℕ} {vTableNat : ℕ → ℕ} (h : checkSwLTableMonoNatL50
  kMax vTableNat = true) : checkSwLTableMono kMax (fun r ↦ (vTableNat r : ℤ)) = true := by
  unfold checkSwLTableMonoNatL50 at h; rw [kpAllRange_eq] at h; unfold checkSwLTableMono
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Nat.ble_eq,
    nat_add_eq] at h ⊢; exact ⟨Nat.cast_nonneg _, fun j hj ↦ by exact_mod_cast h j hj⟩
private theorem list_getD_map_ofNat : ∀ (xs : List ℕ) (i : ℕ), (xs.map Int.ofNat).getD i 0 =
  ((xs.getD i 0 : ℕ) : ℤ)
  | [], _ => rfl | _ :: _, 0 => rfl | _ :: xs, i + 1 => list_getD_map_ofNat xs i
private theorem foldl_nat_cast_int (xs : List ℕ) (init : ℕ) (f : ℕ → ℕ) : ((xs.foldl (fun acc x ↦
  acc + f x) init : ℕ) : ℤ) = xs.foldl (fun (acc : ℤ) x ↦ acc + ((f x : ℕ) : ℤ)) (init : ℤ) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (init + f x), Nat.cast_add]
private theorem le_of_ble_succ_eq_false {a b : ℕ} (h : Nat.ble (a + 1) b = false) : b ≤ a :=
  Nat.not_lt.1 fun hlt ↦ Bool.false_ne_true (h.symm.trans (Eq.mpr Nat.ble_eq hlt))
private theorem list_headD_eq_getD_zero (xs : List ℕ) : xs.headD 0 = xs.getD 0 0 := by
  cases xs <;> rfl
private theorem getD_nil_zero (c : ℕ) : ([] : List ℕ).getD c 0 = 0 := rfl
private theorem getD_cons_zero (x : ℕ) (xs : List ℕ) : (x :: xs).getD 0 0 = x := rfl
private theorem getD_cons_succ (x : ℕ) (xs : List ℕ) (i : ℕ) :
    (x :: xs).getD (i + 1) 0 = xs.getD i 0 := rfl
private theorem all_map_succ (xs : List ℕ) (p : ℕ → Bool) :
    (xs.map Nat.succ).all p = xs.all (fun c ↦ p (c + 1)) := by induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.all_cons]; exact congrArg (p (x + 1) && ·) ih
private theorem foldl_map_succ (xs : List ℕ) (g : ℕ → ℕ → ℕ) (acc : ℕ) : (xs.map Nat.succ).foldl g
  acc = xs.foldl (fun a c ↦ g a (c + 1)) acc := by
  induction xs generalizing acc with
  | nil => rfl | cons x xs ih => exact ih (g acc (x + 1))
/-- Linear `O(k)` non-increasing adjacent-pair check on `List ℕ`. -/
def m1AdjMonoN : ℕ → List ℕ → Bool
  | 0, _ => true
  | k + 1, [] => Nat.ble 0 0 && m1AdjMonoN k []
  | k + 1, [x] => Nat.ble 0 x && m1AdjMonoN k []
  | k + 1, x :: y :: rest => Nat.ble y x && m1AdjMonoN k (y :: rest)
private theorem m1AdjMonoN_eq : ∀ (k : ℕ) (xs : List ℕ), m1AdjMonoN k xs = (List.range k).all (fun i
  ↦ Nat.ble (xs.getD (i + 1) 0) (xs.getD i 0))
  | 0, _ => rfl
  | k + 1, [] => by
    rw [List.range_succ_eq_map, List.all_cons, all_map_succ]; unfold m1AdjMonoN; rw [m1AdjMonoN_eq k
      []]; rfl
  | k + 1, [x] => by
    rw [List.range_succ_eq_map, List.all_cons, all_map_succ]; unfold m1AdjMonoN; rw [m1AdjMonoN_eq k
      []]; rfl
  | k + 1, x :: y :: rest => by
    rw [List.range_succ_eq_map, List.all_cons, all_map_succ]; unfold m1AdjMonoN; rw [m1AdjMonoN_eq k
      (y :: rest)]; rfl
private theorem foldl_nil_getD_zero : ∀ (ls ch : List ℕ) (acc : ℕ), ls.foldl (fun a c ↦ a + ([] :
  List ℕ).getD c 0 * (ch.getD c 0 - ch.getD (c + 1) 0)) acc = acc
  | [], _, _ => rfl
  | _ :: ls, ch, acc => by
    rw [List.foldl_cons, getD_nil_zero, Nat.zero_mul, Nat.add_zero]
    exact foldl_nil_getD_zero ls ch acc
/-- Linear `O(k)` Abel-difference dot product `∑ tl_c * (ch_c - ch_{c+1})`. -/
def m1ZipDiffDot : ℕ → List ℕ → List ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | _ + 1, [], _, acc => acc
  | k + 1, _ :: tlRest, [], acc => m1ZipDiffDot k tlRest [] acc
  | k + 1, t0 :: tlRest, [c0], acc =>
      kpForceNat (Nat.add acc (Nat.mul t0 c0)) fun acc' ↦ m1ZipDiffDot k tlRest [] acc'
  | k + 1, t0 :: tlRest, c0 :: c1 :: cRest, acc =>
      kpForceNat (Nat.add acc (Nat.mul t0 (Nat.sub c0 c1))) fun acc' ↦
        m1ZipDiffDot k tlRest (c1 :: cRest) acc'
private theorem m1ZipDiffDot_eq : ∀ (k : ℕ) (tl ch : List ℕ) (acc : ℕ), m1ZipDiffDot k tl ch acc =
  (List.range k).foldl (fun a c ↦ a + tl.getD c 0 * (ch.getD c 0 - ch.getD (c + 1) 0)) acc
  | 0, _, _, _ => rfl | k + 1, [], ch, acc => (foldl_nil_getD_zero (List.range (k + 1)) ch acc).symm
  | k + 1, t0 :: tlRest, ch, acc => by
    rw [List.range_succ_eq_map, List.foldl_cons, foldl_map_succ]; rcases ch with _ | ⟨c0, _ | ⟨c1,
      cRest⟩⟩
    · unfold m1ZipDiffDot; rw [m1ZipDiffDot_eq k tlRest []]; simp only [getD_nil_zero,
        getD_cons_zero, getD_cons_succ, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    · unfold m1ZipDiffDot; simp only [kpForceNat_eq, nat_add_eq, nat_mul_eq]; rw [m1ZipDiffDot_eq k
        tlRest []]; simp only [getD_nil_zero, getD_cons_zero, getD_cons_succ, Nat.sub_zero]
    · unfold m1ZipDiffDot; simp only [kpForceNat_eq, nat_add_eq, nat_mul_eq, nat_sub_eq]
      rw [m1ZipDiffDot_eq k tlRest (c1 :: cRest)]; simp only [getD_cons_zero, getD_cons_succ]
/-- Pure-GMP single-rank `m = 1` Bellman step checker (`2 ≤ L ≤ 50`). -/
def checkSwLM1StepNatL50 (L r tauNum tauDen : ℕ)
    (tlNat : List ℕ) (survUbNat vScaleNat : ℕ) (vTableNat : ℕ → ℕ) : Bool :=
  forceNatList (vTableNat r :: (List.range L).map fun i ↦ vTableNat (Nat.sub r (Nat.add i 1)))
    fun chainNat ↦
      let chainMono := m1AdjMonoN L chainNat
      cond (!chainMono) false (kpForceNat (m1ZipDiffDot L tlNat chainNat 0)
          fun rhsNat ↦
            kpForceNat (Nat.add (Nat.mul 3 survUbNat) (Nat.mul 2000000000 L)) fun bNum ↦
              kpForceNat (Nat.mul rhsNat 562949953421312) fun lhsRem ↦
                kpForceNat (Nat.mul vScaleNat bNum) fun rhsRem ↦
                  cond (Nat.ble (Nat.add lhsRem 1) rhsRem) false
                    (kpForceNat (Nat.sub lhsRem rhsRem) fun rem ↦
                      kpForceNat (Nat.mul (Nat.mul (Nat.mul survUbNat tauNum) vScaleNat)
                          562949953421312) fun sqL ↦
                        (Nat.ble 2 L && (Nat.ble L 50 && (Nat.ble L r && (Nat.ble r 1024 &&
                        (Nat.ble 1 tauNum && (Nat.ble 1 tauDen && (Nat.beq tlNat.length L &&
                        (Nat.ble 1 vScaleNat && (Nat.ble 1 (tlNat.headD 0) &&
                         Nat.ble (tlNat.headD 0) 1000000000))))))))) &&
                        m1AdjMonoN (Nat.sub L 1) tlNat && Nat.ble (Nat.mul sqL sqL)
                          (Nat.mul (Nat.mul (Nat.mul (Nat.mul 4 tauDen) tauDen) r)
                            (Nat.mul rem rem))))
theorem checkSwLM1StepNatL50_sound {L r tauNum tauDen : ℕ} {tlNat : List ℕ} {survUbNat vScaleNat :
  ℕ} {vTableNat : ℕ → ℕ} (hok : checkSwLM1StepNatL50 L r tauNum tauDen tlNat survUbNat vScaleNat
  vTableNat = true) : checkSwLM1StepTableL50 L r tauNum tauDen L (tlNat.map Int.ofNat) (survUbNat :
  ℤ) (vScaleNat : ℤ) (fun j ↦ (vTableNat j : ℤ)) = true := by
  unfold checkSwLM1StepNatL50 at hok; simp only [forceNatList_eq, nat_add_eq, nat_sub_eq,
    nat_mul_eq, m1AdjMonoN_eq, m1ZipDiffDot_eq, list_headD_eq_getD_zero] at hok; set chainNat :=
    vTableNat r :: (List.range L).map fun i ↦ vTableNat (r - (i + 1)); set chainMono := (List.range
    L).all fun i ↦ Nat.ble (chainNat.getD (i + 1) 0) (chainNat.getD i 0); change (cond (!chainMono)
    false _) = true at hok
  cases hcm : chainMono with
  | false => simp [hcm] at hok
  | true =>
      simp only [hcm, Bool.not_true, Bool.cond_false] at hok; iterate 4 rw [kpForceNat_eq] at hok
      have hcm_le : ∀ i < L, chainNat.getD (i + 1) 0 ≤ chainNat.getD i 0 := by
        intro i hi
        have h := (List.all_eq_true.1 hcm) i (List.mem_range.2 hi); rwa [Nat.ble_eq] at h
      set rhsNat := (List.range L).foldl (fun acc c ↦ acc + tlNat.getD c 0 * (chainNat.getD c 0 -
        chainNat.getD (c + 1) 0)) 0; set bNum : ℕ := 3 * survUbNat + 2000000000 * L
      set lhsRem : ℕ := rhsNat * 562949953421312; set rhsRem : ℕ := vScaleNat * bNum; change (cond
        (Nat.ble (lhsRem + 1) rhsRem) false _) = true at hok
      cases hlt : Nat.ble (lhsRem + 1) rhsRem with
      | true => simp [hlt] at hok
      | false =>
          simp only [hlt, Bool.cond_false, kpForceNat_eq, Bool.and_eq_true, List.all_eq_true,
            List.mem_range, Nat.ble_eq, swLNatBeq_eq_decide, decide_eq_true_eq] at hok
          have hle_rem : rhsRem ≤ lhsRem := le_of_ble_succ_eq_false hlt; rcases hok with ⟨⟨⟨hL2,
            hL50, hLr, hr1024, htau1, hden1, htl_len, hvsc1, htl0_1, htl0_le⟩, htl_mono⟩, hsq⟩
          unfold checkSwLM1StepTableL50 checkSwLM1StepL50
          set chainZ : List ℤ := (vTableNat r : ℤ) :: (List.range L).map fun i ↦ (vTableNat (r - (i
            + 1)) : ℤ); have hchain_map : chainZ = chainNat.map Int.ofNat :=
            (by simp [chainZ, chainNat, List.map_map, Function.comp])
          have hrhs_eq : (List.range L).foldl (fun acc c ↦ acc + (tlNat.map Int.ofNat).getD c 0 *
            (chainZ.getD c 0 - chainZ.getD (c + 1) 0)) (0 : ℤ) = (rhsNat : ℤ) := by
            rw [foldl_range_add_eq_sum]; dsimp [rhsNat]; rw [foldl_nat_cast_int, Nat.cast_zero,
              foldl_range_add_eq_sum]
            refine Finset.sum_congr rfl fun c hc ↦ ?_; rw [Finset.mem_range] at hc
            rw [list_getD_map_ofNat, hchain_map, list_getD_map_ofNat, list_getD_map_ofNat]
            push_cast [Nat.cast_sub (hcm_le c hc)]; rfl
          simp only [withForcedInt_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
            List.mem_range]; change (((_ ∧ _) ∧ _) ∧ ∀ i < L, chainZ.getD (i + 1) 0 ≤ chainZ.getD i
            0); rw [hrhs_eq]; set rem : ℕ := lhsRem - rhsRem
          have hrem_eq : (rhsNat : ℤ) * swBden49 - (vScaleNat : ℤ) * (3 * (survUbNat : ℤ) + 2 *
            swScale * (L : ℤ)) = (rem : ℤ) := by
            have hl_eq : (rhsNat : ℤ) * swBden49 = (lhsRem : ℤ) :=
              (by dsimp [lhsRem]; unfold swBden49; rfl); have hr_eq : (vScaleNat : ℤ) * (3 *
              (survUbNat : ℤ) + 2 * swScale * (L : ℤ)) = (rhsRem : ℤ) :=
              (by dsimp [rhsRem, bNum]; unfold swScale; push_cast; ring); rw [hl_eq, hr_eq, ←
              Nat.cast_sub hle_rem]
          rw [hrem_eq]
          refine ⟨⟨⟨hL2, hL50, hLr, hr1024, by omega, by omega, by simp [htl_len], by simp,
            Nat.cast_nonneg _, mod_cast (by omega : 0 < vScaleNat), ?_, ?_, ?_, ?_,
            Nat.cast_nonneg _, ?_⟩, fun i hi ↦ ?_⟩, fun i hi ↦ ?_⟩
          · rw [list_getD_map_ofNat]; exact_mod_cast (by omega : 0 < tlNat.getD 0 0)
          · rw [list_getD_map_ofNat]; unfold swScale; exact_mod_cast htl0_le
          · rw [list_getD_map_ofNat]; exact Nat.cast_nonneg _
          · rw [hchain_map, list_getD_map_ofNat]; exact Nat.cast_nonneg _
          · have hcast : (((survUbNat * tauNum * vScaleNat * 562949953421312) * (survUbNat * tauNum
              * vScaleNat * 562949953421312) : ℕ) : ℤ) ≤ ((4 * tauDen * tauDen * r * (rem * rem) :
              ℕ) : ℤ) := mod_cast hsq; unfold swBden49; push_cast at hcast ⊢
            linarith [show ((survUbNat : ℤ) * (tauNum : ℤ) * (vScaleNat : ℤ) *
                562949953421312) ^ 2 =
              ((survUbNat : ℤ) * (tauNum : ℤ) * (vScaleNat : ℤ) * 562949953421312) *
              ((survUbNat : ℤ) * (tauNum : ℤ) * (vScaleNat : ℤ) * 562949953421312) by ring,
              show 4 * (tauDen : ℤ) ^ 2 * (r : ℤ) * (rem : ℤ) ^ 2 =
                4 * (tauDen : ℤ) * (tauDen : ℤ) * (r : ℤ) * ((rem : ℤ) * (rem : ℤ)) by ring]
          · rw [list_getD_map_ofNat, list_getD_map_ofNat]; exact_mod_cast htl_mono i hi
          · rw [hchain_map, list_getD_map_ofNat, list_getD_map_ofNat]; exact_mod_cast hcm_le i hi
/-- Compact witness-free per-bucket record for `checkSchedChunkL50`. -/
structure M1L50BktRec where
  rMin : ℕ
  rMax : ℕ
  tauNum : ℕ
  survUbNat : ℕ
  metaLimbs : List ℕ
/-- Polymorphic `m = 1` stage builder from blocked schedule-bank tables (`0` `match` on
  `L`). -/
def m1L50BuildRawStage (sidxOfR tauNumOfR schedL : ℕ → ℕ)
    (schedBlocks : ℕ → List (ℕ × ℕ)) (tauDen r : ℕ) : M1L50RawStageSpec :=
  let sidx := sidxOfR r
  let L := schedL sidx
  ⟨L, tauNumOfR r, tauDen, decodeBlocksM1_16 L (schedBlocks sidx)⟩
/-- Contiguous bucket-list checker sharing precompiled schedule `pps` (right-nested `&&`). -/
def checkBktListPreL50 (sidx L numP tauDen vScaleNat : ℕ) (sidxOfR tauNumOfR vTableNat : ℕ → ℕ)
    (pps : List KpPrePulse) (curR rEnd : ℕ) : List M1L50BktRec → Bool
  | [] => Nat.beq curR (Nat.add rEnd 1)
  | b :: bs =>
      let cnt := Nat.add (Nat.sub b.rMax b.rMin) 1
      let rawMeta := packLimbs320 b.metaLimbs
      Nat.beq b.rMin curR && (Nat.ble b.rMin b.rMax && (Nat.ble b.rMax rEnd &&
      (kpAllRange (fun off ↦
        let r := Nat.add b.rMin off
        Nat.beq (sidxOfR r) sidx && Nat.beq (tauNumOfR r) b.tauNum) cnt &&
      ((match unpackMeta L rawMeta with
        | (tlNat, uRat, uTrig) =>
            checkBucketPreDecodedL50 L b.rMin b.rMax b.tauNum tauDen numP pps
              tlNat uRat uTrig b.survUbNat &&
            kpAllRange (fun off ↦
              checkSwLM1StepNatL50 L (Nat.add b.rMin off) b.tauNum tauDen
                tlNat b.survUbNat vScaleNat vTableNat) cnt) &&
       checkBktListPreL50 sidx L numP tauDen vScaleNat sidxOfR tauNumOfR vTableNat pps
         (Nat.add b.rMax 1) rEnd bs))))
theorem checkBktListPreL50_sound {sidx L numP tauDen vScaleNat rEnd : ℕ} {sidxOfR tauNumOfR schedL :
  ℕ → ℕ} {schedBlocks : ℕ → List (ℕ × ℕ)} {vTableNat : ℕ → ℕ} {pps : List KpPrePulse} (hL_eq :
  schedL sidx = L) (hnumP_eq : sumBlockPulses (schedBlocks sidx) = numP) (hpps_eq :
  kpCompilePulsesFast L (decodeBlocksM1_16 L (schedBlocks sidx)) = pps) : ∀ (bkts : List
  M1L50BktRec) (curR : ℕ), checkBktListPreL50 sidx L numP tauDen vScaleNat sidxOfR tauNumOfR
  vTableNat pps curR rEnd bkts = true → ∀ r, curR ≤ r → r ≤ rEnd → M1L50StageSoundAt (vScaleNat : ℤ)
  (fun j ↦ (vTableNat j : ℤ)) (m1L50BuildRawStage sidxOfR tauNumOfR schedL schedBlocks tauDen r) r
  | [], curR, hok => by
    unfold checkBktListPreL50 at hok; have hcur : curR = rEnd + 1 := Nat.eq_of_beq_eq_true hok
    intro r hlo hhi; omega
  | b :: bs, curR, hok => by
    unfold checkBktListPreL50 at hok; simp only [Bool.and_eq_true] at hok; rcases hok with
      ⟨hrMin_eq', hrMin_le', hrMax_le', htbl, hbkt_and_steps, hrest⟩
    have hrMin_eq : b.rMin = curR := Nat.eq_of_beq_eq_true hrMin_eq'; have hrMin_le : b.rMin ≤
      b.rMax := Nat.ble_eq.mp hrMin_le'; have hrMax_le : b.rMax ≤ rEnd := Nat.ble_eq.mp hrMax_le'
    intro r hlo hhi; by_cases hr : r ≤ b.rMax
    · have hr_ge : b.rMin ≤ r := (by omega); set off : ℕ := r - b.rMin
      have hoff_lt : off < Nat.add (Nat.sub b.rMax b.rMin) 1 :=
        (by change off < b.rMax - b.rMin + 1; omega); have hoff_r : Nat.add b.rMin off = r :=
        (by change b.rMin + off = r; omega); rw [kpAllRange_eq, List.all_eq_true] at htbl
      have htbl_r := htbl off (List.mem_range.2 hoff_lt); rw [hoff_r, Bool.and_eq_true] at htbl_r
      have hsidx_r : sidxOfR r = sidx := Nat.eq_of_beq_eq_true htbl_r.1; have htau_r : tauNumOfR r =
        b.tauNum := Nat.eq_of_beq_eq_true htbl_r.2; rcases unpackMeta_lengths L (packLimbs320
        b.metaLimbs) with ⟨htl_len, _, _⟩; rcases hm : unpackMeta L (packLimbs320 b.metaLimbs) with
        ⟨tlNat, uRat, uTrig⟩
      rw [hm] at hbkt_and_steps htl_len; dsimp only at hbkt_and_steps htl_len
      rcases hbkt_and_steps with ⟨hbkt_pre, hsteps⟩
      have hp_len : (decodeBlocksM1_16 L (schedBlocks sidx)).length = numP :=
        (by unfold decodeBlocksM1_16; rw [List.length_map, unpackBlocksM1_16_length, hnumP_eq])
      have hp_val : (decodeBlocksM1_16 L (schedBlocks sidx)).all swLPulseValid = true := by
        unfold decodeBlocksM1_16; rw [List.all_map, List.all_eq_true]
        intro pv _; exact decodePulseRaw_valid L pv
      have hbkt_cert := checkBucketPreDecodedL50_sound hp_len hp_val hpps_eq htl_len hbkt_pre
      rw [kpAllRange_eq, List.all_eq_true] at hsteps; have hstep_nat := hsteps off (List.mem_range.2
        hoff_lt); rw [hoff_r] at hstep_nat; have hstep_cert := checkSwLM1StepNatL50_sound hstep_nat
      have hstg : m1L50BuildRawStage sidxOfR tauNumOfR schedL schedBlocks tauDen r = ⟨L, b.tauNum,
        tauDen, decodeBlocksM1_16 L (schedBlocks sidx)⟩ := by
        change M1L50RawStageSpec.mk (schedL (sidxOfR r)) (tauNumOfR r) tauDen (decodeBlocksM1_16
          (schedL (sidxOfR r)) (schedBlocks (sidxOfR r))) = _; rw [hsidx_r, hL_eq, htau_r]
      rw [hstg]; exact checkSwLM1StageL2L50_sound hr_ge hr hbkt_cert hstep_cert
    · exact checkBktListPreL50_sound hL_eq hnumP_eq hpps_eq bs (Nat.add b.rMax 1) hrest r
        (by change b.rMax + 1 ≤ r; omega) hhi
/-- Linear `O(m)` Pythagorean interval list builder from `+262144`-biased `List ℕ`. -/
def m1UPythagsList : ℕ → List ℕ → List (IvInt × IvInt)
  | 0, _ => []
  | k + 1, uRaw :: us =>
      kpForcePair (kpIvPythagFast (m1SubNatNat uRaw 262144) (.ofNat 65536)) fun py ↦
        py :: m1UPythagsList k us
  | k + 1, [] =>
      kpForcePair (kpIvPythagFast (.ofNat 0) (.ofNat 65536)) fun py ↦ py :: m1UPythagsList k []
private theorem m1UPythagsList_length : ∀ (m : ℕ) (xs : List ℕ), (m1UPythagsList m xs).length = m
  | 0, _ => rfl
  | k + 1, [] => by simp [m1UPythagsList, kpForcePair_eq, m1UPythagsList_length k []]
  | k + 1, _ :: us => by simp [m1UPythagsList, kpForcePair_eq, m1UPythagsList_length k us]
private theorem m1UPythagsList_getD : ∀ (m : ℕ) (xs : List ℕ) (i : ℕ), i < m → (m1UPythagsList m
  xs).getD i ((0, 0), (0, 0)) = ivPythag (kpFastSubNatNat (xs.getD i 262144) 262144) (.ofNat
  65536)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, [], 0, _ => by
    have hz : kpFastSubNatNat ([].getD 0 262144) 262144 = .ofNat 0 := rfl
    unfold m1UPythagsList; rw [kpForcePair_eq, List.getD_cons_zero,
      kpIvPythagFast_eq, kpIvPythag_eq, ivPythagP_eq, hz]
  | k + 1, [], j + 1, hi => by
    unfold m1UPythagsList; rw [kpForcePair_eq, List.getD_cons_succ]
    exact m1UPythagsList_getD k [] j (by omega)
  | k + 1, uRaw :: us, 0, _ => by
    unfold m1UPythagsList; rw [kpForcePair_eq, List.getD_cons_zero,
      List.getD_cons_zero, m1SubNatNat_eq, kpFastSubNatNat_eq,
      kpIvPythagFast_eq, kpIvPythag_eq, ivPythagP_eq]
  | k + 1, uRaw :: us, j + 1, hi => by
    unfold m1UPythagsList; rw [kpForcePair_eq, List.getD_cons_succ,
      List.getD_cons_succ]; exact m1UPythagsList_getD k us j (by omega)
private theorem m1UPythagsList_eq (m : ℕ) (pv : List ℕ × ℕ) : m1UPythagsList m pv.1 =
  kpUPythagsFast (Int.ofNat (decodePulseRaw (m + 1) pv).uvDen) m (decodePulseRaw (m + 1)
  pv).uNum := by
  rw [kpUPythagsFast_eq]; apply List.ext_getElem
  · simp [m1UPythagsList_length, kpUPythags, kpUPythagsGo_length]
  · intro i hi1 hi2; have hi : i < m := (by simpa [m1UPythagsList_length] using hi1)
    rw [list_getElem_eq_getD _ ((0, 0), (0, 0)) i hi1, list_getElem_eq_getD _ ((0, 0), (0, 0)) i
      hi2, m1UPythagsList_getD m pv.1 i hi, kpUPythags, kpUPythagsGo_getD _ m _ m le_rfl i hi]
    have hidx : m - m + i = i := (by omega); dsimp [decodePulseRaw]; simp only [hidx]
/-- Linear `O(L)` single-pulse precompiler from `(bus, bv)` (`0` quadratic `List.getD`). -/
def m1CompilePulseRaw : ℕ → List ℕ × ℕ → KpPrePulse
  | 0, pv => kpForceIv (kpPulseCvFast (decodePulseRaw 0 pv)) fun cv ↦ (cv, [])
  | m + 1, pv =>
      kpForceIv (kpPulseCvFast (decodePulseRaw (m + 1) pv)) fun cv ↦
        kpWithPairList (m1UPythagsList m pv.1) fun ups ↦ (cv, ups)
private theorem m1CompilePulseRaw_eq (L : ℕ) (pv : List ℕ × ℕ) :
    m1CompilePulseRaw L pv = kpCompilePulseFast L (decodePulseRaw L pv) := by cases L with
  | zero => rfl
  | succ m =>
    unfold m1CompilePulseRaw kpCompilePulseFast; dsimp only; rw [m1UPythagsList_eq m pv]
/-- Linear `O(L)` schedule-bank precompiler equal to `kpCompilePulsesFast ∘
  decodeBlocksM1_16`. -/
def m1CompileBlocks16 (L : ℕ) (bs : List (ℕ × ℕ)) : List KpPrePulse :=
  (unpackBlocksM1_16 L bs).map (m1CompilePulseRaw L)
private theorem m1CompileBlocks16_eq (L : ℕ) (bs : List (ℕ × ℕ)) : m1CompileBlocks16 L bs =
  kpCompilePulsesFast L (decodeBlocksM1_16 L bs) := by
  unfold m1CompileBlocks16 kpCompilePulsesFast decodeBlocksM1_16; rw [List.map_map]; congr 1
  funext pv; exact m1CompilePulseRaw_eq L pv
/-- Precompile schedule `sidx` once and verify all buckets covering `[curR, rEnd]`. -/
def checkSchedChunkL50 (sidx tauDen vScaleNat curR rEnd : ℕ) (sidxOfR tauNumOfR schedL : ℕ → ℕ)
    (schedBlocks : ℕ → List (ℕ × ℕ)) (vTableNat : ℕ → ℕ) (bkts : List M1L50BktRec) : Bool :=
  kpForceNat (schedL sidx) fun L ↦
    let blks := schedBlocks sidx
    kpForceNat (sumBlockPulses blks) fun numP ↦
      kpWithPrePulses (m1CompileBlocks16 L blks) fun pps ↦
        checkBktListPreL50 sidx L numP tauDen vScaleNat sidxOfR tauNumOfR vTableNat pps curR rEnd
          bkts
theorem checkSchedChunkL50_sound {sidx tauDen vScaleNat curR rEnd : ℕ} {sidxOfR tauNumOfR schedL : ℕ
  → ℕ} {schedBlocks : ℕ → List (ℕ × ℕ)} {vTableNat : ℕ → ℕ} {bkts : List M1L50BktRec} (hok :
  checkSchedChunkL50 sidx tauDen vScaleNat curR rEnd sidxOfR tauNumOfR schedL schedBlocks vTableNat
  bkts = true) : ∀ r, curR ≤ r → r ≤ rEnd → M1L50StageSoundAt (vScaleNat : ℤ) (fun j ↦ (vTableNat j
  : ℤ)) (m1L50BuildRawStage sidxOfR tauNumOfR schedL schedBlocks tauDen r) r := by
  unfold checkSchedChunkL50 at hok; simp only [kpForceNat_eq, kpWithPrePulses_eq] at hok
  exact checkBktListPreL50_sound rfl rfl (m1CompileBlocks16_eq _ _).symm bkts curR hok
end QuantumComputation.Specs.GroverFindAll.SchurWeylM1L50
end
end Sec_SchurWeylL2BallM1L50CertDefs
section Sec_SchurWeylL2BallM1L50Overlap
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Real
namespace SwLOverlapL50Internal
theorem swLRawLiftAOnOrbit_signed_ge_l50 {L N r m b : ℕ} (hb : b ≤ 1) (hL : 2 ≤ L)
    (hL50 : L ≤ 50) (hm1 : 1 ≤ m) (hmL : m ≤ L) (hr : m ≤ r) (hN : 2 * r + L ≤ N) :
    (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) ≤
      (-1 : ℝ) ^ (b + 1) * swLRawLiftAOnOrbit L N r m b (m - 1) := by
  let B : ℕ := N - r - L
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : 0 < B := (by omega); exact_mod_cast this
  let term : ℕ → ℝ := fun u ↦ (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) *
      (-1 : ℝ) ^ (m + (b + u)) * ((SwLOverlapInternal.swLTermFac N r m b u : ℕ) : ℝ)
  have hdef : swLRawLiftAOnOrbit L N r m b (m - 1) = ∑ u ∈ Finset.range m, term u := rfl
  have hrange : Finset.range m = Finset.range ((m - 1) + 1) :=
    congrArg Finset.range (by omega)
  rw [hdef, hrange, Finset.sum_range_succ, mul_add]
  have htop : (-1 : ℝ) ^ (b + 1) * term (m - 1) =
      (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    dsimp [term]; rw [Nat.choose_self, Nat.sub_self, Nat.choose_zero_right]
    have hsgn : (-1 : ℝ) ^ (b + 1) * (-1 : ℝ) ^ (m + (b + (m - 1))) = 1 := by
      rw [← pow_add, show (b + 1) + (m + (b + (m - 1))) = 2 * (b + m) by omega, pow_mul]
      norm_num
    calc
      (-1 : ℝ) ^ (b + 1) *
          (((1 * 1 : ℕ) : ℝ) * (-1 : ℝ) ^ (m + (b + (m - 1))) *
            (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ))
          = ((-1 : ℝ) ^ (b + 1) * (-1 : ℝ) ^ (m + (b + (m - 1)))) *
              (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by push_cast; ring
      _ = (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by rw [hsgn, one_mul]
  have htail_term : ∀ u ∈ Finset.range (m - 1),
      (B : ℝ) * |term u| ≤
        (562949953421312 * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    intro u hu; have hu_lt : u < m - 1 := Finset.mem_range.mp hu
    have habs : |term u| = (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) *
          (SwLOverlapInternal.swLTermFac N r m b u : ℝ) := by
      dsimp [term]
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    have hc_prod : (m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) ≤ 562949953421312 := by
      have hc1 := SwLOverlapInternal.choose_le_two_pow (m - 1) u
      have hc2 := SwLOverlapInternal.choose_le_two_pow (L - 1 - (m - 1)) (m - 1 - u)
      have hpow : 2 ^ (m - 1) * 2 ^ (L - 1 - (m - 1)) ≤ 562949953421312 := by
        rw [← pow_add, show m - 1 + (L - 1 - (m - 1)) = L - 1 by omega]
        exact le_trans (Nat.pow_le_pow_right (by omega) (show L - 1 ≤ 49 by omega)) (by norm_num)
      exact (Nat.mul_le_mul hc1 hc2).trans hpow
    have hfac : B * SwLOverlapInternal.swLTermFac N r m b u ≤
        r * SwLOverlapInternal.swLTermFac N r m b (m - 1) :=
      SwLOverlapInternal.swLTermFac_tail_bound hb hL hmL hr hN hu_lt
    have hnat : ((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u)) *
        (B * SwLOverlapInternal.swLTermFac N r m b u) ≤
        562949953421312 * (r * SwLOverlapInternal.swLTermFac N r m b (m - 1)) :=
      Nat.mul_le_mul hc_prod hfac
    have hreal : (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) *
        ((B : ℝ) * (SwLOverlapInternal.swLTermFac N r m b u : ℝ)) ≤
        (562949953421312 : ℝ) *
          ((r : ℝ) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) := by
      exact_mod_cast hnat
    rw [habs]; linarith
  have htail_sum : (B : ℝ) * |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
      (28000000000000000 * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    have habs_sgn : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| =
        |∑ u ∈ Finset.range (m - 1), term u| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [habs_sgn]
    have h1 : (B : ℝ) * |∑ u ∈ Finset.range (m - 1), term u| ≤
        (B : ℝ) * ∑ u ∈ Finset.range (m - 1), |term u| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hBpos.le
    have h2 : (B : ℝ) * ∑ u ∈ Finset.range (m - 1), |term u| ≤ ((m - 1 : ℕ) : ℝ) *
          ((562949953421312 * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) := by
      rw [Finset.mul_sum]; refine (Finset.sum_le_sum htail_term).trans ?_
      simp [Finset.sum_const, nsmul_eq_mul]
    have hm49 : ((m - 1 : ℕ) : ℝ) ≤ 49 := by
      have : m - 1 ≤ 49 := (by omega); exact_mod_cast this
    have hnn : 0 ≤ (562949953421312 * (r : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by positivity
    have h3 : ((m - 1 : ℕ) : ℝ) *
        ((562949953421312 * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) ≤
        49 * ((562949953421312 * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) :=
      mul_le_mul_of_nonneg_right hm49 hnn
    linarith
  have htail_div : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
      ((28000000000000000 * (r : ℝ)) / (B : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    have h2 : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
        ((28000000000000000 * (r : ℝ)) *
          (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) / (B : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le hBpos; linarith [htail_sum]
    simpa [mul_div_right_comm] using h2
  have hneg := neg_le_abs ((-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u); rw [htop]
  linarith
theorem ratio_pow_ge_half_tol_l50 {L n r : ℕ} (hL50 : L ≤ 50) (hn : 128 ≤ n) (hr1024 : r ≤ 1024) :
    1 - (1 : ℝ) / (2 * 10 ^ 18) ≤ (((2 ^ n - r - L : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)) ^ L := by
  let N : ℕ := 2 ^ n
  have hN38 : 10 ^ 38 ≤ N :=
    le_trans (by norm_num : 10 ^ 38 ≤ 2 ^ 128) (Nat.pow_le_pow_right (by omega) hn)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := (by omega); exact_mod_cast this
  have hsub_eq : ((N - r - L : ℕ) : ℝ) / (N : ℝ) = 1 - ((r + L : ℕ) : ℝ) / (N : ℝ) := by
    have hle : r + L ≤ N := (by omega); have hsub : N - r - L = N - (r + L) := by omega
    rw [hsub, Nat.cast_sub hle, sub_div, div_self hNpos.ne']
  have hx0 : 0 ≤ ((r + L : ℕ) : ℝ) / (N : ℝ) := by positivity
  have hx1 : ((r + L : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
    apply SwLOverlapInternal.div_le_of_le_mul hNpos; have : r + L ≤ N := by omega
    have hR : ((r + L : ℕ) : ℝ) ≤ (N : ℝ) := (by exact_mod_cast this); linarith
  have hbern := SwLOverlapInternal.one_sub_mul_le_pow hx0 hx1 L; rw [hsub_eq]
  have herr : (L : ℝ) * (((r + L : ℕ) : ℝ) / (N : ℝ)) ≤ (1 : ℝ) / (2 * 10 ^ 18) := by
    have hnum_le : L * (r + L) ≤ 10 ^ 5 :=
      le_trans (Nat.mul_le_mul hL50 (show r + L ≤ 1074 by omega)) (by norm_num)
    have hnumR : (L : ℝ) * ((r + L : ℕ) : ℝ) ≤ (10 ^ 5 : ℝ) := by exact_mod_cast hnum_le
    have hNR : (10 ^ 38 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN38
    have hdiv : ((L : ℝ) * ((r + L : ℕ) : ℝ)) / (N : ℝ) ≤ (1 : ℝ) / (2 * 10 ^ 18) := by
      apply SwLOverlapInternal.div_le_of_le_mul hNpos; linarith
    simpa [mul_div_assoc] using hdiv
  linarith
theorem tail_factor_ge_half_tol_l50 {L n r : ℕ} (hL50 : L ≤ 50) (hn : 128 ≤ n) (hr1024 : r ≤ 1024) :
    0 ≤ 1 - (28000000000000000 * (r : ℝ)) / ((2 ^ n - r - L : ℕ) : ℝ) ∧
    1 - (1 : ℝ) / (2 * 10 ^ 18) ≤
      (1 - (28000000000000000 * (r : ℝ)) / ((2 ^ n - r - L : ℕ) : ℝ)) ^ 2 := by
  let B : ℕ := 2 ^ n - r - L
  have hN128 : 34 * 10 ^ 37 ≤ 2 ^ n :=
    le_trans (by norm_num : 34 * 10 ^ 37 ≤ 2 ^ 128) (Nat.pow_le_pow_right (by omega) hn)
  have hB37 : 33 * 10 ^ 37 ≤ B := by omega
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : 0 < B := (by omega); exact_mod_cast this
  have hy : (28000000000000000 * (r : ℝ)) / (B : ℝ) ≤ (1 : ℝ) / (4 * 10 ^ 18) := by
    apply SwLOverlapInternal.div_le_of_le_mul hBpos
    have hrR : (r : ℝ) ≤ 1024 := by exact_mod_cast hr1024
    have hBR : (33 * 10 ^ 37 : ℝ) ≤ (B : ℝ) := (by exact_mod_cast hB37); linarith
  refine ⟨by linarith, ?_⟩
  have hsq : 1 - 2 * ((28000000000000000 * (r : ℝ)) / (B : ℝ)) ≤
      (1 - (28000000000000000 * (r : ℝ)) / (B : ℝ)) ^ 2 := by
    have hnn : 0 ≤ ((28000000000000000 * (r : ℝ)) / (B : ℝ)) ^ 2 := sq_nonneg _
    linarith [show (1 - (28000000000000000 * (r : ℝ)) / (B : ℝ)) ^ 2 =
      1 - 2 * ((28000000000000000 * (r : ℝ)) / (B : ℝ)) +
        ((28000000000000000 * (r : ℝ)) / (B : ℝ)) ^ 2 by ring]
  linarith
end SwLOverlapL50Internal
theorem swLDiagOverlap_bounds_l50 {L n r : ℕ} (hL : 2 ≤ L) (hL50 : L ≤ 50) (hn : 128 ≤ n)
    (hrL : L ≤ r) (hr1024 : r ≤ 1024) (j : Fin (2 * L)) : 0 ≤ swLDiagOverlap L (2 ^ n) r j ∧
    1 - (1 : ℝ) / 10 ^ 18 ≤ (swLDiagOverlap L (2 ^ n) r j) ^ 2 := by
  let N : ℕ := 2 ^ n
  have hN38 : 10 ^ 38 ≤ N :=
    le_trans (by norm_num : 10 ^ 38 ≤ 2 ^ 128) (Nat.pow_le_pow_right (by omega) hn)
  have hN_bound : 2 * r + L ≤ N := by omega
  have hrat_tol : 1 - (1 : ℝ) / (2 * 10 ^ 18) ≤
      (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) := by
    have h := SwLOverlapL50Internal.ratio_pow_ge_half_tol_l50 hL50 hn hr1024 (r := r)
    simpa [N, div_pow] using h
  have htail_tol := SwLOverlapL50Internal.tail_factor_ge_half_tol_l50 (L := L) hL50 hn hr1024
  unfold swLDiagOverlap; dsimp only; split_ifs with hj0 hjodd
  · refine ⟨Real.sqrt_nonneg _, ?_⟩
    rw [Real.sq_sqrt (by positivity)]
    have hoc_eq : swLOrbitCardNat L N r j =
        (N - r) * SwLOverlapInternal.swLFallProd (N - r - 1) (L - 1) := by
      have hev : j.1 % 2 = 0 := (by omega); have hdiv : j.1 / 2 = 0 := by omega
      rw [SwLOverlapInternal.swLOrbitCardNat_even hev, hdiv]
      simp [SwLOverlapInternal.factorial_mul_choose_eq_swLFallProd
        (show L - 1 ≤ N - r - 1 by omega)]
    have hoc_ge : (N - r - L) ^ L ≤ swLOrbitCardNat L N r j := by
      rw [hoc_eq]; have hp1 : N - r - L ≤ N - r := by omega
      have hp2 := SwLOverlapInternal.pow_le_swLFallProd (N - r - L) (N - r - 1) (L - 1)
        (fun _ _ ↦ by omega)
      calc
        (N - r - L) ^ L = (N - r - L) * (N - r - L) ^ (L - 1) := by
          have hexp : (L - 1) + 1 = L := by omega
          calc
            (N - r - L) ^ L = (N - r - L) ^ ((L - 1) + 1) := by rw [hexp]
            _ = (N - r - L) * (N - r - L) ^ (L - 1) := by ring
        _ ≤ (N - r) * SwLOverlapInternal.swLFallProd (N - r - 1) (L - 1) := Nat.mul_le_mul hp1 hp2
    have hden_le : L.factorial * N.choose L ≤ N ^ L := by
      rw [SwLOverlapInternal.factorial_mul_choose_eq_swLFallProd (show L ≤ N by omega)]
      exact SwLOverlapInternal.swLFallProd_le_pow le_rfl L
    have hden_pos : 0 < L.factorial * N.choose L :=
      Nat.mul_pos (Nat.factorial_pos L) (Nat.choose_pos (by omega))
    have hbr1 : (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) ≤
        (swLOrbitCardNat L N r j : ℝ) / ((L.factorial * N.choose L : ℕ) : ℝ) :=
      SwLOverlapInternal.nat_scaled_ratio_ge (scale := 1) (common := 1) (by omega) hden_pos
        (Nat.pow_pos (by omega)) (by simpa using hoc_ge) (by simpa using hden_le)
    linarith
  · let m : ℕ := (j.1 + 1) / 2
    have hm1 : 1 ≤ m := (by omega); have hmL : m ≤ L := by omega
    have hraw_ge : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ≤
        swLRawLiftAOnOrbit L N r m 1 (m - 1) := by
      have h := SwLOverlapL50Internal.swLRawLiftAOnOrbit_signed_ge_l50 (L := L) (N := N)
        (r := r) (m := m) (b := 1) le_rfl hL hL50 hm1 hmL (by omega) hN_bound
      simpa using h
    have hlhs_nn : 0 ≤ (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) :=
      mul_nonneg htail_tol.1 (Nat.cast_nonneg _)
    have hraw_nn : 0 ≤ swLRawLiftAOnOrbit L N r m 1 (m - 1) := hlhs_nn.trans hraw_ge
    refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hraw_nn) (Real.sqrt_nonneg _), ?_⟩
    have hraw_sq : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ^ 2 ≤
        (swLRawLiftAOnOrbit L N r m 1 (m - 1)) ^ 2 :=
      SwLOverlapInternal.mul_sq_le_sq_of_nonneg hlhs_nn hraw_ge
    obtain ⟨hden_pos, hrat2⟩ := SwLOverlapInternal.branch2_ratio_ge hL hrL hN_bound hjodd
    have hdenR_pos : (0 : ℝ) < ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) := by
      exact_mod_cast hden_pos
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    have hstep1 : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
        (((swLOrbitCardNat L N r j * (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) /
          ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) ≤
        ((swLOrbitCardNat L N r j : ℝ) * (swLRawLiftAOnOrbit L N r m 1 (m - 1)) ^ 2) /
          ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le hdenR_pos
      have h1 : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
          (((swLOrbitCardNat L N r j *
            (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) /
            ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) *
          ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) =
          (swLOrbitCardNat L N r j : ℝ) *
            ((1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
              (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ^ 2) := by
        rw [mul_assoc, div_mul_cancel₀ _ hdenR_pos.ne']; push_cast; ring
      rw [h1]; exact mul_le_mul_of_nonneg_left hraw_sq (Nat.cast_nonneg _)
    have hstep2 : (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) ≤
        (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
          (((swLOrbitCardNat L N r j *
            (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) /
            ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) :=
      mul_le_mul htail_tol.2 (hrat_tol.trans hrat2) (by norm_num) (sq_nonneg _)
    have hcomb : 1 - (1 : ℝ) / 10 ^ 18 ≤
        (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) := by norm_num
    exact hcomb.trans (hstep2.trans hstep1)
  · have heven : j.1 % 2 = 0 := by omega
    let w : ℕ := j.1 / 2; let m : ℕ := w + 1; have hmL : m ≤ L := by omega
    have hraw_ge : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ≤
        -swLRawLiftAOnOrbit L N r m 0 w := by
      have h := SwLOverlapL50Internal.swLRawLiftAOnOrbit_signed_ge_l50 (L := L) (N := N)
        (r := r) (m := m) (b := 0) (by omega) hL hL50 (by omega) hmL (by omega) hN_bound
      simpa [m] using h
    have hlhs_nn : 0 ≤ (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) := mul_nonneg htail_tol.1 (Nat.cast_nonneg _)
    have hraw_nn : 0 ≤ -swLRawLiftAOnOrbit L N r m 0 w := hlhs_nn.trans hraw_ge
    have hrew : (-√(((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ))) *
        (√(swLOrbitCardNat L N r j : ℝ) * swLRawLiftAOnOrbit L N r m 0 w /
          √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) =
        √(((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ)) *
          (√(swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) /
            √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) := by ring
    rw [hrew]
    refine ⟨mul_nonneg (Real.sqrt_nonneg _)
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hraw_nn) (Real.sqrt_nonneg _)), ?_⟩
    have hraw_sq : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
        (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ^ 2 ≤
        (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 :=
      SwLOverlapInternal.mul_sq_le_sq_of_nonneg hlhs_nn hraw_ge
    obtain ⟨hden_pos, hrw_pos, hrat3⟩ :=
      SwLOverlapInternal.branch3_ratio_ge hL hrL hN_bound hj0 heven
    have htot_den_pos : (0 : ℝ) <
        (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hrw_pos hden_pos
    rw [mul_pow, div_pow, mul_pow,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    have hsq_eq : (((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ)) *
        ((swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 /
          ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) =
        (((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
          (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) /
          (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      rw [div_mul_div_comm]
      have hnum_r : ((N - r - w : ℕ) : ℝ) *
          ((swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) =
          ((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
            (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 := by ring
      have hden_r : ((r - w : ℕ) : ℝ) * ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) =
          (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
        push_cast; ring
      rw [hnum_r, hden_r]
    rw [hsq_eq]
    have hstep1 : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
        ((((N - r - w) * swLOrbitCardNat L N r j *
          (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) /
          (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) ≤
        (((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
          (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) /
          (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le htot_den_pos
      have h1 : (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
          ((((N - r - w) * swLOrbitCardNat L N r j *
            (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) /
            (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) *
          (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) =
          ((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
            ((1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
              (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ^ 2) := by
        rw [mul_assoc, div_mul_cancel₀ _ htot_den_pos.ne']; push_cast; ring
      rw [h1]; exact mul_le_mul_of_nonneg_left hraw_sq (by positivity)
    have hstep2 : (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) ≤
        (1 - (28000000000000000 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
          ((((N - r - w) * swLOrbitCardNat L N r j *
            (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) /
            (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) :=
      mul_le_mul htail_tol.2 (hrat_tol.trans hrat3) (by norm_num) (sq_nonneg _)
    have hcomb : 1 - (1 : ℝ) / 10 ^ 18 ≤
        (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) := by norm_num
    exact hcomb.trans (hstep2.trans hstep1)
theorem isValidSwLOverlap_swLOverlapMatFn_l50 {L n r : ℕ} (hL : 2 ≤ L) (hL50 : L ≤ 50)
    (hn : 128 ≤ n) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hr1024 : r ≤ 1024) (hR : R.card = r) :
    SchurWeylLCert.IsValidSwLOverlap (swLOverlapMatFn L R) := by
  have : NeZero L := ⟨by omega⟩
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩; have hL0 : L ≠ 0 := by omega
  have hN128 : 2 ^ 128 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hrN : r + L ≤ 2 ^ n := by omega
  have hM : swLOverlapMatFn L R = SwLInternal.overlapTupleMat L (2 ^ n) R := by
    unfold swLOverlapMatFn; rw [dite_eq_right hL0]
  rw [hM]
  refine isValidSwLOverlap_of_orth_and_diag
    (SwLInternal.overlapTupleMat_col_orth hL hrL hrN hR)
    (SwLInternal.overlapTupleMat_row_orth hL hrL hrN hR)
    (fun j ↦ ?_) (fun j ↦ ?_)
  · rw [SwLInternal.overlapTupleMat_diag_eq hL hrL hrN hR j]
    exact (swLDiagOverlap_bounds_l50 hL hL50 hn hrL hr1024 j).1
  · rw [SwLInternal.overlapTupleMat_diag_eq hL hrL hrN hR j]
    exact (swLDiagOverlap_bounds_l50 hL hL50 hn hrL hr1024 j).2
end QuantumComputation.Specs.GroverFindAll
end
end Sec_SchurWeylL2BallM1L50Overlap
section Sec_SchurWeylL2BallM1L50QHL
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation
theorem swLWireBound_m1_le_findAllQubits_l50 {n L k : ℕ} (hL2 : 2 ≤ L) (hL50 : L ≤ 50)
    (hLk : L ≤ k) (hn50 : 50 ≤ n) : swLWireBound n 1 L ≤ findAllQubits n 1 k := by
  unfold swLWireBound findAllQubits
  have h1 : (L - 1) * 1 * n + 1 * L ≤ (L - 1) * n + n := by
    have : 1 * L ≤ n := (by omega); linarith [show (L - 1) * 1 * n = (L - 1) * n by ring]
  have h2 : (L - 1) * n + n = L * n := by
    calc (L - 1) * n + n = (L - 1 + 1) * n := by ring
      _ = L * n := by rw [Nat.sub_add_cancel (by omega)]
  have h3 : L * n ≤ n * k := (Nat.mul_le_mul_right n hLk).trans_eq (Nat.mul_comm k n)
  omega
/-- Real-soundness stage bundle for `m = 1` `H_dist(2 ≤ L ≤ 50)` (`128 ≤ n`), with
  cold-entry
  fallback at any stage `r` where `useSwL r = false`. -/
structure SwLM1L50CertBundle where
  kMax : ℕ
  vScale : ℤ
  vTable : ℕ → ℤ
  useSwL : ℕ → Bool
  stageOfR : ℕ → SwLM1StageSpec
  hKMax : kMax ≤ 1024
  hScalePos : 0 < vScale
  hV0 : vTable 0 = 0
  hMono : ∀ r : ℕ, r < kMax → vTable r ≤ vTable (r + 1)
  hStageSound : ∀ {n r : ℕ}, 128 ≤ n → 1 ≤ r → r ≤ kMax → useSwL r = true →
    let s := stageOfR r
    ∃ (hL2 : 2 ≤ s.L), s.L ≤ 50 ∧ s.L ≤ r ∧ s.pulses.all swLPulseValid = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ), IsValidSwLOverlap M →
        let K_blk := hdistLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := hdistLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧
        (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) + ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
theorem swLM1L50_vTable_mono_le (B : SwLM1L50CertBundle) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ B.kMax) :
    B.vTable a ≤ B.vTable b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
      exact (ih (by omega) (by omega)).trans (B.hMono (a + d) (by omega))
theorem swLM1L50_vTable_nonneg (B : SwLM1L50CertBundle) {r : ℕ} (hr : r ≤ B.kMax) :
    0 ≤ B.vTable r := by
  rw [← B.hV0]; exact swLM1L50_vTable_mono_le B (Nat.zero_le r) hr
/-- Fuel-bounded `m = 1` stage recursion dispatching `H_dist(2 ≤ L ≤ 50)` or `coldCirc`. -/
noncomputable def hdistL50M1StageLoop {Var : Type} (res : Var) (B : SwLM1L50CertBundle)
    {n k Q : ℕ} (hQ : findAllQubits n 1 k ≤ Q) (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) : ℕ → ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)
  | 0, _, T => swLWriteFinsetLiftCircuit res hQ T
  | fuel + 1, r, T =>
      if r = 0 then swLWriteFinsetLiftCircuit res hQ T
      else if B.useSwL r = true then
        let s := B.stageOfR r
        if hs : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧ swLWireBound n 1 s.L ≤ Q then
          let K_blk := hdistLKBlk n r s.tauNum s.tauDen
          let cBody := swLM1AttemptBodyCircuit res n s.L Q hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 K_blk
            s.pulses
          let cAtt := deflateCirc n 1 T
            (swLResetWhileCircuit res (fun v ↦ !swLHasVerifHit n 1 s.L Q hs.1 hs.2.1 hs.2.2.2 v)
              cBody)
          .seq cAtt
            (dispBits res Q 0 fun v ↦
              let H := swLDecodeHarvest n 1 s.L Q hs.1 hs.2.1 hs.2.2.2 v
              if 1 ≤ H.card then hdistL50M1StageLoop res B hQ coldCirc fuel (r - H.card) (T ∪ H)
              else .skip)
        else coldCirc r T
      else coldCirc r T
/-- Polymorphic cold-entry `m = 1` `H_dist(2 ≤ L ≤ 50)` stage circuit on `findAllQubits n 1
  k`. -/
noncomputable def hdistL50M1FromSetWithColdCircuit {Var : Type} (res : Var)
    (B : SwLM1L50CertBundle) {n k : ℕ} (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
        (findAllQubits n 1 k) ((n + 1) * 1)) (r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) := hdistL50M1StageLoop res B le_rfl coldCirc r r T
theorem hdistL50M1StageLoop_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var)
    (B : SwLM1L50CertBundle) {n k Q : ℕ} (hQ : findAllQubits n 1 k ≤ Q)
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1))
    (hn : 128 ≤ n) (_hk1 : 1 ≤ k) (hkMax : k ≤ B.kMax)
    (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))}, 1 ≤ r' → r' ≤ k → B.useSwL r' = false →
      ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card = r' →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ))) :
    ∀ (fuel r : ℕ) (T : Finset (Fin (2 ^ n))), r ≤ fuel → r ≤ k →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → (S \ T).card = r →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (hdistL50M1StageLoop res B hQ coldCirc fuel r T).compile
          QProg.qAssign (parallelMarkingOracle 1 S)
        𝔼[(interp prog).toStateFun Δ,
            liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
          expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
            stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro r T hrf _ S hScard hTS hrem Δ hΔ; have hr0 : r = 0 := (by omega); subst hr0
      have hTS_eq : T = S := by
        have hsub0 : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem)
        exact Finset.Subset.antisymm hTS hsub0
      subst hTS_eq; obtain ⟨hexp, hcost⟩ := swLWriteFinsetLift_transition res hQ hScard hΔ
      refine ⟨hexp, ?_⟩; dsimp only [hdistL50M1StageLoop]; rw [hcost, B.hV0]; simp
  | succ fuel ih =>
      intro r T hrf hr_le S hScard hTS hrem Δ hΔ
      by_cases hr0 : r = 0
      · subst hr0
        have hTS_eq : T = S := by
          have hsub0 : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem)
          exact Finset.Subset.antisymm hTS hsub0
        subst hTS_eq; unfold hdistL50M1StageLoop; rw [ite_eq_left rfl]
        obtain ⟨hexp, hcost⟩ := swLWriteFinsetLift_transition res hQ hScard hΔ; refine ⟨hexp, ?_⟩
        rw [hcost, B.hV0]; simp
      · have hr1 : 1 ≤ r := by omega
        by_cases hsw : B.useSwL r = true
        · set R := S \ T
          set s := B.stageOfR r; have hr_kMax : r ≤ B.kMax := hr_le.trans hkMax
          have hr1024 : r ≤ 1024 := hr_kMax.trans B.hKMax
          obtain ⟨hL2, hL50, hrL, hpulses, hsound⟩ := B.hStageSound hn hr1 hr_kMax hsw
          have hn0 : 0 < n := (by omega); have h128_pow : 1074 ≤ 2 ^ 128 := by norm_num
          have hn_pow : 2 ^ 128 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
          have hL50_s : s.L ≤ 50 := hL50; have hn2L : 2 * s.L ≤ 2 ^ n := by omega
          have hrN : r + s.L ≤ 2 ^ n := by omega
          have hQ_sw : swLWireBound n 1 s.L ≤ Q :=
            (swLWireBound_m1_le_findAllQubits_l50 hL2 hL50 (hrL.trans hr_le) (by omega)).trans hQ
          have hcond : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧ swLWireBound n 1 s.L ≤ Q :=
            ⟨hn0, hL2, hn2L, hQ_sw⟩
          have hM_valid : IsValidSwLOverlap (swLOverlapMatFn s.L R) :=
            isValidSwLOverlap_swLOverlapMatFn_l50 hL2 hL50 hn hrL hr1024 hrem
          obtain ⟨hpSucc_pos, hBell⟩ := hsound (swLOverlapMatFn s.L R) hM_valid
          set K_blk := hdistLKBlk n r s.tauNum s.tauDen
          set cs : Fin s.L → ℝ × ℝ := fun w ↦
            (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
             Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
          set out := hdistLEvolutionReal s.L hL2 cs s.pulses
          set pHit : ℕ → ℝ := swLAttemptProbReal s.L hL2 (swLOverlapMatFn s.L R) out.1 out.2.1
          set V : ℕ → ℝ := fun j ↦ ((B.vTable j : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)
          have hV_nn : ∀ j ≤ B.kMax, 0 ≤ V j := fun j hj ↦ by
            dsimp only [V]
            have hv_nn : (0 : ℝ) ≤ (B.vTable j : ℝ) := by exact_mod_cast swLM1L50_vTable_nonneg B hj
            have hsc_pos : (0 : ℝ) < (B.vScale : ℝ) := (by exact_mod_cast B.hScalePos); positivity
          obtain ⟨hwt_nn, hwt_sum, hbot, hwp0, hcost_body, hsub_wt, hsum_P⟩ :=
            swLM1AttemptBody_profile (Var := Var) res hn0 hL2 hn2L hQ_sw hrL hrN hrem K_blk hpulses
          set cBody := swLM1AttemptBodyCircuit (Var := Var) res n s.L Q hn0 hL2 hn2L hQ_sw K_blk
            s.pulses
          set keepLoop : ℕ → Bool := fun v ↦ !swLHasVerifHit n 1 s.L Q hn0 hL2 hQ_sw v
          set wt : Fin (2 ^ Q) → ℝ := fun o ↦ ∑ z : Fin (2 ^ (s.L * n + 1)),
              if swLPackVerifBasis n 1 s.L Q hn0 hL2 hQ_sw R (fun _ ↦ z) = o then
                Complex.normSq (swLSurvVec s.L n R out.1 z) +
                  out.2.1 * Complex.normSq (swLClickVec s.L n R z)
              else 0
          have hkeep0 : keepLoop 0 = true := by simp [keepLoop, swLHasVerifHit_zero]
          have hpSucc_eq : (∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o) =
              ∑ h ∈ Finset.Icc 1 s.L, pHit h := by
            have h1 := hsum_P (fun _ ↦ (1 : ℝ)); simpa [keepLoop, wt, pHit, mul_one] using h1
          have hsucc_wt_pos : 0 < ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o := by
            rwa [hpSucc_eq]
          set cRaw := swLResetWhileCircuit res keepLoop cBody
          have hcRaw_zero : ZeroStepCost cRaw :=
            zeroStepCost_swLResetWhileCircuit res keepLoop
              (zeroStepCost_swLM1AttemptBodyCircuit res n s.L Q hn0 hL2 hn2L hQ_sw K_blk s.pulses)
          obtain ⟨hslice_att, hcost_att⟩ :=
            swLResetWhile_transition res (parallelMarkingOracle 1 R) hkeep0 cBody wt
              (out.2.2 * (K_blk : ℝ) + (s.L : ℝ)) hwt_nn hwt_sum hbot hwp0
              (fun {Ξ} hΞ ↦ hcost_body hΞ) hsucc_wt_pos hΔ
          set pSucc : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o
          set Δ_att := (interp (cRaw.compile QProg.qAssign (parallelMarkingOracle 1 R))).toStateFun
            Δ
          set fBranch : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1) := fun v ↦
            let H := swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v
            if 1 ≤ H.card then hdistL50M1StageLoop res B hQ coldCirc fuel (r - H.card) (T ∪ H)
            else .skip
          unfold hdistL50M1StageLoop; rw [ite_eq_right hr0, ite_eq_left hsw]; dsimp only
          rw [dite_eq_left hcond]
          change (let prog := (OracleDynamicCircuit.seq (deflateCirc n 1 T cRaw)
                (dispBits res Q 0 fBranch)).compile QProg.qAssign (parallelMarkingOracle 1 S)
              𝔼[(interp prog).toStateFun Δ,
                  liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
                expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
                  stateMass Δ * ENNReal.ofReal (V r))
          dsimp only
          rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind,
            interp_deflateCirc n 1 hTS cRaw]
          change 𝔼[(interp ((dispBits res Q 0 fBranch).compile QProg.qAssign
                (parallelMarkingOracle 1 S))).toStateFun Δ_att,
              liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧ _
          refine ⟨?_, ?_⟩
          · rw [expect_dispBits]
            have hterm : ∀ v ∈ Finset.range (2 ^ Q), 𝔼[(interp ((fBranch v).compile QProg.qAssign
                    (parallelMarkingOracle 1 S))).toStateFun (sliceState res 0 Q v Δ_att),
                  liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
                (sliceState res 0 Q v Δ_att).trace := by
              intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem
              obtain ⟨hsupp_v, htr_v⟩ := hslice_att v hv
              by_cases hk : keepLoop v = false
              · by_cases hwt0 : wt ⟨v, hv⟩ = 0
                · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 := NNReal.coe_inj.mp
                    (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul, NNReal.coe_zero])
                  rw [expect_eq_zero_of_trace_eq_zero
                    (((interp _).trace_toStateFun_le _).trans_eq htr0 |>.antisymm zero_le),
                    htr0, NNReal.coe_zero]
                · obtain ⟨hH_sub, _⟩ := hsub_wt ⟨v, hv⟩ hwt0
                  have hH1 : 1 ≤ (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                    simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                  have hTU_sub : T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                    Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                  have hrem_u : (S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)).card =
                      r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                    have hsdiff : S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v) =
                        R \ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v := by
                      ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]
                    rw [hsdiff, Finset.card_sdiff_of_subset hH_sub, hrem]
                  dsimp only [fBranch]; rw [ite_eq_left hH1]
                  exact (ih (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)
                    (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)
                    (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).1
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp (by rw [htr_v, ite_eq_right hk, NNReal.coe_zero])
                rw [expect_eq_zero_of_trace_eq_zero
                  (((interp _).trace_toStateFun_le _).trans_eq htr0 |>.antisymm zero_le),
                  htr0, NNReal.coe_zero]
            rw [Finset.sum_congr rfl hterm, ← Fin.sum_univ_eq_sum_range
              (fun v ↦ ((sliceState res 0 Q v Δ_att).trace : ℝ)) (2 ^ Q)]
            have hsum_tr : (∑ o : Fin (2 ^ Q), ((sliceState res 0 Q o.val Δ_att).trace : ℝ)) =
                ∑ o : Fin (2 ^ Q) with keepLoop o.val = false,
                  (wt o / pSucc) * Δ.trace := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun o _ ↦ (hslice_att o.val o.isLt).2
            rw [hsum_tr, ← Finset.sum_mul, ← Finset.sum_div, div_self hsucc_wt_pos.ne', one_mul]
          · let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)
            rw [expectedCost_qSeq, expectedCost_deflateCirc n 1 hTS hcRaw_zero,
              interp_deflateCirc n 1 hTS cRaw]
            change expectedCost _ _ Δ + expectedCost model
                ((dispBits res Q 0 fBranch).compile QProg.qAssign (parallelMarkingOracle 1 S))
                Δ_att ≤ _
            rw [expectedCost_dispBits]
            have hterm_le : ∀ v ∈ Finset.range (2 ^ Q),
                expectedCost model ((fBranch v).compile QProg.qAssign (parallelMarkingOracle 1 S))
                  (sliceState res 0 Q v Δ_att) ≤
                stateMass Δ * ENNReal.ofReal
                  (if hv : v < 2 ^ Q then
                    if keepLoop v = false then
                      (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) /
                        pSucc
                    else 0
                  else 0) := by
              intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem
              obtain ⟨hsupp_v, htr_v⟩ := hslice_att v hv; rw [dite_eq_left hv]
              by_cases hk : keepLoop v = false
              · rw [ite_eq_left hk]
                by_cases hwt0 : wt ⟨v, hv⟩ = 0
                · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 := NNReal.coe_inj.mp
                    (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul, NNReal.coe_zero])
                  rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0, hwt0, zero_mul,
                    zero_div, ENNReal.ofReal_zero, mul_zero]
                · obtain ⟨hH_sub, _⟩ := hsub_wt ⟨v, hv⟩ hwt0
                  have hH1 : 1 ≤ (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                    simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                  have hTU_sub : T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                    Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                  have hrem_u : (S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)).card =
                      r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                    have hsdiff : S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v) =
                        R \ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v := by
                      ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]
                    rw [hsdiff, Finset.card_sdiff_of_subset hH_sub, hrem]
                  dsimp only [fBranch]; rw [ite_eq_left hH1]
                  have hih := (ih (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)
                    (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)
                    (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).2
                  refine hih.trans_eq ?_
                  have hdiv_nn : 0 ≤ wt ⟨v, hv⟩ / pSucc :=
                    div_nonneg (hwt_nn ⟨v, hv⟩) hsucc_wt_pos.le
                  rw [stateMass_eq_ofReal_trace, htr_v, ite_eq_left hk,
                    ENNReal.ofReal_mul hdiv_nn, mul_comm (ENNReal.ofReal (wt ⟨v, hv⟩ / pSucc)),
                    ← stateMass_eq_ofReal_trace, mul_assoc, ← ENNReal.ofReal_mul hdiv_nn,
                    div_mul_eq_mul_div]
              · rw [ite_eq_right hk, ENNReal.ofReal_zero, mul_zero]
                have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp (by rw [htr_v, ite_eq_right hk, NNReal.coe_zero])
                rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0]
            have hdisp_le : (∑ v ∈ Finset.range (2 ^ Q),
                  expectedCost model ((fBranch v).compile QProg.qAssign (parallelMarkingOracle 1 S))
                    (sliceState res 0 Q v Δ_att)) ≤
                stateMass Δ *
                  ENNReal.ofReal ((∑ h ∈ Finset.Icc 1 s.L, pHit h * V (r - h)) / pSucc) := by
              refine (Finset.sum_le_sum hterm_le).trans_eq ?_; rw [← Finset.mul_sum]; congr 1
              have hnn : ∀ v ∈ Finset.range (2 ^ Q),
                  0 ≤ (if hv : v < 2 ^ Q then
                    if keepLoop v = false then
                      (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) /
                        pSucc
                    else 0 else 0) := by
                intro v _; split_ifs with hv hk
                · exact div_nonneg (mul_nonneg (hwt_nn _) (hV_nn _ (by omega))) hsucc_wt_pos.le
                · exact le_rfl
                · exact le_rfl
              rw [← ENNReal.ofReal_sum_of_nonneg hnn]; congr 1
              have hfin_eq : (∑ v ∈ Finset.range (2 ^ Q),
                    if hv : v < 2 ^ Q then
                      if keepLoop v = false then
                        (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) /
                          pSucc
                      else 0 else 0) =
                  ∑ o : Fin (2 ^ Q),
                    if keepLoop o.val = false then
                      (wt o * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw o.val).card)) / pSucc
                    else 0 := by
                rw [← Fin.sum_univ_eq_sum_range]; refine Finset.sum_congr rfl fun o _ ↦ ?_
                rw [dite_eq_left o.isLt]
              rw [hfin_eq, ← Finset.sum_filter, ← Finset.sum_div]; congr 1
              exact hsum_P (fun h ↦ V (r - h))
            refine (add_le_add hcost_att hdisp_le).trans ?_
            have hcs : ∀ w : Fin s.L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦
              Real.cos_sq_add_sin_sq _
            have hout_nn : 0 ≤ out.2.2 := (hdistLEvolutionReal_conservation hL2 hcs hpulses).2.2.2
            have hatt_nn : 0 ≤ (out.2.2 * (K_blk : ℝ) + (s.L : ℝ)) / pSucc :=
              div_nonneg (by positivity) hsucc_wt_pos.le
            have hcont_nn : 0 ≤ (∑ h ∈ Finset.Icc 1 s.L, pHit h * V (r - h)) / pSucc :=
              div_nonneg (Finset.sum_nonneg fun h _ ↦ mul_nonneg
                (GroverFindAll.swLAttemptProbReal_nonneg hL2 _ _
                  (hdistLEvolutionReal_conservation hL2 hcs hpulses).2.1 h)
                (hV_nn _ (by omega))) hsucc_wt_pos.le
            rw [← mul_add, ← ENNReal.ofReal_add hatt_nn hcont_nn, ← add_div]
            refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
            rwa [hpSucc_eq]
        · have hsw_f : B.useSwL r = false := Bool.eq_false_iff.mpr hsw
          unfold hdistL50M1StageLoop; rw [ite_eq_right hr0, ite_eq_right hsw]
          exact hcold hr1 hr_le hsw_f hScard hTS hrem hΔ
/-- Correctness and expected oracle cost of `hdistL50M1FromSetWithColdCircuit` (`128 ≤ n`). -/
theorem hdistL50M1FromSetWithCold_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var)
    (B : SwLM1L50CertBundle) {n k r : ℕ} (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
        (findAllQubits n 1 k) ((n + 1) * 1))
    (hn : 128 ≤ n) (hk1 : 1 ≤ k) (hkMax : k ≤ B.kMax) (hr_le : r ≤ k)
    (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))}, 1 ≤ r' → r' ≤ k → B.useSwL r' = false →
      ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card = r' →
      ∀ {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)))
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (hdistL50M1FromSetWithColdCircuit res B coldCirc r T).compile
      QProg.qAssign (parallelMarkingOracle 1 S)
    𝔼[(interp prog).toStateFun Δ,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
        stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) :=
  hdistL50M1StageLoop_correct_and_cost res B le_rfl coldCirc hn hk1 hkMax hcold r r T le_rfl
    hr_le hScard hTS hrem hΔ
/-- `m = 1` `L ≤ 50` bundle adapter forcing `useSwL 1 = false` for `MHTail` (`r = 1`). -/
def swLM1L50BundleWithR1Cold (B : SwLM1L50CertBundle) : SwLM1L50CertBundle where
  kMax := B.kMax
  vScale := B.vScale
  vTable := B.vTable
  useSwL := fun r ↦ if r = 1 then false else B.useSwL r
  stageOfR := B.stageOfR
  hKMax := B.hKMax
  hScalePos := B.hScalePos
  hV0 := B.hV0
  hMono := B.hMono
  hStageSound {n r} hn hr1 hrMax huse := by
    have hr_ne1 : r ≠ 1 := by intro h1; subst h1; simp at huse
    simp only [hr_ne1, ↓reduceIte] at huse; exact B.hStageSound hn hr1 hrMax huse
/-- Standalone `m = 1` `H_dist(2 ≤ L ≤ 50)` circuit routing `r = 1` to
  `lockSingleFromSetCircuit`. -/
noncomputable def hdistL50M1FromSetCircuit {Var : Type} (res : Var) (B : SwLM1L50CertBundle)
    (n k r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  hdistL50M1FromSetWithColdCircuit res (swLM1L50BundleWithR1Cold B)
    (fun _ T' ↦ lockSingleFromSetCircuit res n 1 k T') r T
/-- Correctness and expected oracle cost of `hdistL50M1FromSetCircuit` (`n ≥ 128`, `2 ≤ k`). -/
theorem hdistL50M1FromSet_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var)
    (B : SwLM1L50CertBundle) {n k r : ℕ} (hScale : B.vScale = 10000000000000000)
    (hUseSwL : ∀ r', 2 ≤ r' → r' ≤ B.kMax → B.useSwL r' = true)
    (hV1 : (6426990820000000 : ℤ) ≤ B.vTable 1)
    (hn : 128 ≤ n) (hk2 : 2 ≤ k) (hkMax : k ≤ B.kMax) (hr_le : r ≤ k)
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (hdistL50M1FromSetCircuit res B n k r T).compile
      QProg.qAssign (parallelMarkingOracle 1 S)
    𝔼[(interp prog).toStateFun Δ,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
        stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) := by
  refine hdistL50M1FromSetWithCold_correct_and_cost res (swLM1L50BundleWithR1Cold B)
    (fun _ T' ↦ lockSingleFromSetCircuit res n 1 k T')
    hn (by omega) hkMax hr_le ?_ hScard hTS hrem hΔ
  intro r' T' hr1' hrk' huse_f S' hS' hT'S' hrem' Δ' hΔ'
  have hr'_eq1 : r' = 1 := by
    by_contra hne1
    have h2 : 2 ≤ r' := (by omega); have htr := hUseSwL r' h2 (hrk'.trans hkMax)
    simp [swLM1L50BundleWithR1Cold, hne1, htr] at huse_f
  subst hr'_eq1; have hk1024 : k ≤ 1024 := hkMax.trans B.hKMax
  have hrem_sub : k - T'.card = 1 := by
    have hs := Finset.card_sdiff_of_subset hT'S'; omega
  obtain ⟨hexp, hcost⟩ := lockSingleFromSet_transition res (by omega : 100 ≤ n) le_rfl
    (by norm_num) hk1024 hS' hT'S' hrem_sub hΔ'
  refine ⟨hexp, hcost.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
  simp only [swLM1L50BundleWithR1Cold, Nat.cast_one, div_one]; rw [hScale]
  have hrel : ((relCostLock : ℚ≥0) : ℝ) = (4091549431 : ℝ) / 5000000000 := by
    unfold relCostLock; push_cast; norm_num
  have hpi : π < 3.14159265359 := Real.pi_lt_d20.trans (by norm_num)
  have hv1_r : (6426990820000000 : ℝ) ≤ (B.vTable 1 : ℝ) := by exact_mod_cast hV1
  have hcoef : ((relCostLock : ℚ≥0) : ℝ) * (π / 4) ≤
      (B.vTable 1 : ℝ) / (10000000000000000 : ℝ) := by
    rw [hrel]; linarith
  exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
/-- Direct `m = 1` `H_dist(2 ≤ L ≤ 50)` circuit on `findAllQubits` (`128 ≤ n`). -/
noncomputable def hdistL50PureM1Circuit {Var : Type} (res : Var)
    (B : SwLM1L50CertBundle) (n : ℕ) : ∀ (m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) * m)
  | 1, k =>
      if 128 ≤ n then hdistL50M1FromSetCircuit res B n k k ∅
      else findAllCircuit res (fun _ _ _ ↦ 0) n 1 k
  | _, _ => .skip
theorem hdistL50PureM1Circuit_m1 {Var : Type} (res : Var) (B : SwLM1L50CertBundle) (n k : ℕ) :
    hdistL50PureM1Circuit (Var := Var) res B n 1 k =
      if 128 ≤ n then hdistL50M1FromSetCircuit res B n k k ∅
      else findAllCircuit res (fun _ _ _ ↦ 0) n 1 k := rfl
/-- End-to-end `ValidFindAllFamily` theorem via `SchurWeylLCert.checkSwLRelCostCell_sound`. -/
theorem validFamily_hdistL50PureM1 {Var : Type} [DecidableEq Var] (res : Var)
    (B : SwLM1L50CertBundle) (hScale : B.vScale = 10000000000000000)
    (hUseSwL : ∀ r, 2 ≤ r → r ≤ B.kMax → B.useSwL r = true)
    (hV1 : (6426990820000000 : ℤ) ≤ B.vTable 1) (prof : FindAllCostProfile)
    (hCells : ∀ m k : ℕ, isGridCell m k = true → prof.validCell m k = true →
      m = 1 ∧ 2 ≤ k ∧ k ≤ B.kMax ∧ 128 ≤ prof.n0 m k ∧ ∃ kIdx relNum relDen : ℕ, k = 2 ^ kIdx ∧
        prof.relCost m k = (relNum : ℚ≥0) / (relDen : ℚ≥0) ∧
        SchurWeylLCert.checkSwLRelCostCell 0 kIdx (B.vTable k) relNum relDen = true) :
    ValidFindAllFamily res prof (hdistL50PureM1Circuit res B) where
  correctness {n m k S} _hn hmk hvalid hkN hS := by
    obtain ⟨rfl, hk2, hkMax, _, _, _, _, _, _, _⟩ := hCells m k hmk hvalid
    have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2
    by_cases hn128 : 128 ≤ n
    · intro Δ
      rw [hdistL50PureM1Circuit_m1]
      rw [ite_eq_left hn128, expect_top, interp_qSeq, QMonad.Q.toStateFun_bind,
        interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
      have hcorr := (hdistL50M1FromSet_correct_and_cost res B hScale hUseSwL hV1 hn128 hk2
        hkMax le_rfl hScard (Finset.empty_subset S) (by simpa using hScard) hsupp).1
      exact (hcorr.trans (congrArg ((↑) : ℝ≥0 → ℝ) (CQState.trace_qSet Δ))).symm.le
    · rw [hdistL50PureM1Circuit_m1]
      rw [ite_eq_right hn128]
      exact findAllProgram_correctness res (fun _ _ _ ↦ 0) le_rfl hScard hkN
        (fun r hr1 hrk ↦ p_succ_set_zero_pos hr1 (hrk.trans hkN))
  costBound_uniform {m k} hmk hvalid n hn0 hkN := by
    obtain ⟨rfl, hk2, hkMax, hn0_cond, kIdx, relNum, relDen, hk_pow, hrel_eq, hcell⟩ :=
      hCells m k hmk hvalid
    have hn128 : 128 ≤ n := hn0_cond.trans hn0
    have hv_nn : (0 : ℝ) ≤ (B.vTable k : ℝ) := by exact_mod_cast swLM1L50_vTable_nonneg B hkMax
    set cVal : ℝ := ((B.vTable k : ℝ) / 10000000000000000) * √(2 ^ n : ℝ)
    let cNN : ℝ≥0 := ⟨cVal, by dsimp [cVal]; positivity⟩; refine ⟨fun _ ↦ cNN, ?_, ?_⟩
    · intro S hS Δ
      have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2; rw [hdistL50PureM1Circuit_m1]
      rw [ite_eq_left hn128, expectedCost_qSeq, expectedCost_qSet,
        CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero, mul_zero, zero_add,
        interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
      have hmass_eq : stateMass Δ.qSet = stateMass Δ :=
        congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
      have hcb := (hdistL50M1FromSet_correct_and_cost res B hScale hUseSwL hV1 hn128 hk2
        hkMax le_rfl hScard (Finset.empty_subset S) (by simpa using hScard) hsupp).2
      have hcNN : (cNN : ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
      rw [hmass_eq, hScale] at hcb; refine hcb.trans ?_; rw [hcNN]; exact le_rfl
    · have hcard_pos : 0 < ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; exact Nat.choose_pos hkN
      have hcard_r : (0 : ℝ) <
          (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card : ℝ) := by
        exact_mod_cast hcard_pos
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_r.ne', hrel_eq]
      change cVal ≤ (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) *
        ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (1 : ℕ)))
      have hrel_cast : (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) =
          (relNum : ℝ) / (relDen : ℝ) := by push_cast; rfl
      rw [hrel_cast]; have hsound_cell := SchurWeylLCert.checkSwLRelCostCell_sound (n := n) hcell
      have hmu : (SchurWeylLCert.multiUnitScale : ℝ) = 10000000000000000 := by
        unfold SchurWeylLCert.multiUnitScale; norm_num
      rw [hmu, pow_zero] at hsound_cell; simpa [cVal, ← hk_pow] using hsound_cell
end QuantumComputation.Specs.GroverFindAll
end
end Sec_SchurWeylL2BallM1L50QHL
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open scoped NNRat
/-- Cell selector claiming `(m = 1, k ∈ {4, 8, 16, 32})`. -/
def isSchurWeylL2BallM1K32OnlyCell (m k : ℕ) : Bool :=
  (m == 1) && ((k == 4) || (k == 8) || (k == 16) || (k == 32))
/-- Certified coprime relative costs across `(m = 1, k ∈ {4, 8, 16, 32})`. -/
def relCostSchurWeylL2BallM1K32Only (m k : ℕ) : ℚ≥0 :=
  if (m == 1 && k == 4) then (1798014765956261 : ℚ≥0) / 2500000000000000
  else if (m == 1 && k == 8) then (173143829619399 : ℚ≥0) / 250000000000000
  else if (m == 1 && k == 16) then (6751273712926893 : ℚ≥0) / 10000000000000000
  else if (m == 1 && k == 32) then (1328876209066213 : ℚ≥0) / 2000000000000000
  else 1
/-- Standalone `FindAllCostProfile` for `(m = 1, k ∈ {4, 8, 16, 32})`. -/
def schurWeylL2BallM1K32OnlyProfile : FindAllCostProfile where
  validCell := isSchurWeylL2BallM1K32OnlyCell
  relCost := relCostSchurWeylL2BallM1K32Only
  n0 _ _ := 600
end QuantumComputation.Specs.GroverFindAll
end
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs.GroverFindAll.MultiTapStage2
open QuantumComputation.Specs.GroverFindAll.SchurWeylM1L50
open scoped QuantumComputation.Specs.GroverFindAll.MultiTapStage2.GF2nForallA
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation BigOperators
section InternalM1K32
private def m1K32P56 : List ℕ → ℕ
  | [] => 0
  | w :: ws => Nat.add w (Nat.mul 72057594037927936 (m1K32P56 ws))
private def m1K32P56Cat (acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | w :: ws => Nat.add w (Nat.mul 72057594037927936 (m1K32P56Cat acc ws))
private def schedBlks1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      2964972955205638, 36043672832161152, 27443881219231624, 40292153666541711,
      49978152865335192, 38204243294818695, 4371381443657744, 36045873667226752,
      67413319335513432, 39556580286933388, 3813245912320049, 38221823552259976,
      1556103350943750, 590147691136]),
  (16,
    m1K32P56 [
      2120612369760259, 36030481879988096, 28288237447318297, 38418585651553672,
      57570873358649532, 38519776103890312, 71082041744326654, 36022787278101887,
      27443846883018649, 38039254022534023, 46310216433633452, 38450500009459848,
      2683429102321663, 586372494464]),
  (16,
    m1K32P56 [
      71363258987544573, 36024984875156607, 27162333245244818, 37487299269249413,
      9997861379278903, 38292162449770888, 1556867740893188, 36033778636061568,
      13651564418401337, 37177236889512836, 30825777000384397, 38092046736556423,
      38710679886594031, 579812434046]),
  (16,
    m1K32P56 [
      59820899410148892, 42619847431125382, 31706116548887406, 37034486269319299,
      46587831014491386, 37226729679348100, 47151544745832516, 49808442592018864,
      55363878705332936, 36655180460301954, 27164593085121508, 36689061363145860,
      24913707294306711, 563538358705]),
  (16,
    m1K32P56 [
      67979864049692979, 49775455297009072, 24964156012856037, 36668372351664002,
      6335569355113267, 36878178856264067, 5491989747118357, 49916190889487025,
      17365169152164417, 36737646197913218, 45179683091088039, 36749539150003842,
      71356812190134751, 560468283825]),
  (16,
    m1K32P56 [
      65445635825578459, 50105305245393329, 6950818345550849, 37200542103137412,
      23789281374208606, 36671478723372418, 6054295477662160, 50027238829147058,
      56490671938633034, 35819555817391998, 4643682967585268, 36575801615972482,
      1268709706936822, 557448125362]),
  (16,
    m1K32P56 [
      55030490386379272, 50116297828023217, 7232619733876522, 35757982193151871,
      62064105772253659, 36582396454378113, 11683146397037060, 50150382688455602,
      48890993592336060, 35640336059558782, 18435020530811219, 36285526486164353,
      67976844651639366, 550351295665]),
  (16,
    m1K32P56 [
      21535689694556577, 49850217674974897, 70844753287413264, 35439118217513341,
      28567316508475793, 36420763295697025, 66288737808658466, 49415905532027567,
      37066003721125261, 35309370057239933, 16744847775924475, 36272327296526721,
      32230016510504955, 554897844400]),
  (8,
    m1K32P56 [
      51088835653447936, 50211951329740465, 48047904386612532, 36615611530418045,
      70232562400788685, 36339432889445760, 142444764125848])]
private def schedBlks2G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      47996691306086276, 37242141126125444, 11689653279229097, 38181087297709444,
      44049749453276224, 35724801540899975, 60662609933862803, 37151966426008190,
      48559112975318724, 37230045491541123, 20415072604488524, 38094223714742660,
      19560975474656332, 35632434091675783, 43209267298469683, 36766038230507646,
      49966603815452315, 37259730241887874, 33478]),
  (16,
    m1K32P56 [
      58410878883888804, 37266326590238338, 29702995217908421, 37893013741158020,
      38420056614143084, 35722594816913542, 71638407452132976, 36805621219481470,
      54751828729888532, 37300408632159618, 38709464337580739, 37704999886833028,
      61501734849512590, 35918308054438533, 50809302127379905, 36816616855807871,
      57848178016157642, 37330092459810178, 33488]),
  (16,
    m1K32P56 [
      58974107984429035, 37337788202350210, 47715688646410963, 37456512859427972,
      70790958837826732, 36029358997286788, 143870745740516, 36833109949599104,
      62070397141942272, 37352079135604866, 50529751219077854, 37283889550647172,
      27162337448395955, 36029359181837188, 143926580380748, 36847403600722048,
      66292517488066560, 37348778201579650, 33518]),
  (16,
    m1K32P56 [
      67981358755905536, 37345479029162114, 47995711924503284, 37092574527420036,
      51369185447085222, 36029359601263491, 144029658350502, 36873791493871488,
      708731940143104, 37314690790981763, 39550994471748357, 36976026294880132,
      22377262846936197, 36029359869689731, 144098375271233, 36893582015280000,
      6056571807629312, 37266310685524099, 33560]),
  (16,
    m1K32P56 [
      7745370126712832, 37252016631709827, 22943468334646047, 36849582457692804,
      62909659495105610, 36029360356213378, 144227220161237, 36925466761940096,
      13937583386230784, 37189343260967043, 6336148355973940, 36778114201892484,
      45458210940355597, 36029360674964610, 144308820476569, 36946356409110912,
      19566803743703040, 37116774520455299, 33607]),
  (16,
    m1K32P56 [
      20974092726796288, 37095883514314883, 54468051545916236, 36697849853070723,
      25192012618630072, 36029361010487426, 988811054580306, 36963947219405952,
      23788580497620993, 37028812499714179, 37297880398070614, 36647272318195843,
      12525638667371386, 36029361211797890, 144441954763302, 36979339291664768,
      27447476019232768, 36956244044415107, 33633]),
  (16,
    m1K32P56 [
      27447394414264320, 36937552195747971, 13935251172655969, 36596694783320451,
      140739692561193, 36029361312440450, 144463424356859, 36983736012765056,
      28291561644261376, 36870481466359939, 69104209168991075, 36562609922859906,
      62909659499037421, 36029361262093697, 144441945784795, 36976038508615040,
      26039534195081216, 36815505297768579, 33627]),
  (16,
    m1K32P56 [
      25758003383074816, 36797912910397571, 50526654547657562, 36508733853096578,
      49117385639756458, 36029361178190209, 144424761459113, 36971639287686016,
      24913337932218368, 36738538644963459, 36171276116591445, 36469151434494338,
      39547236430742138, 36029360909743745, 144343154459015, 36948548939514752,
      18720738118696960, 36701154746302595, 33599]),
  (16,
    m1K32P56 [
      17031832423333888, 36684661920891011, 20971459870491450, 36427369992632450,
      28569712337453631, 36029360507073665, 144235775426911, 36919960295005056,
      11120548672602112, 36605496530043011, 1268065471857445, 36389986597283458,
      19281029515149823, 36028260810881921, 425680684155200, 36913362487033216,
      8587093491810304, 36559316672577667, 33559]),
  (16,
    m1K32P56 [
      4927837190193153, 36532928427065731, 52777934670365453, 36387787607575425,
      21814334368481709, 36029359869501569, 144081146839383, 36874877768131968,
      69948153087164416, 36428476030386306, 23786381436814072, 36488941184157057,
      46586288392470824, 38458180518341761, 44335411961758101, 36428478765169316,
      58689403124539718, 36488947305771905, 33238])]
private def schedBlks2G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      47711758769299194, 36324021065419905, 51370615058760309, 36394220562526081,
      15646142822842867, 25423467167992193, 45177886991221031, 36867179542575737,
      42645591442565812, 36578008220924032, 3801545933619731, 36396677971682945,
      2715061465416023, 45079431907233153, 423893968257311, 36580208819639655,
      46022548135436869, 36518634392284801, 33110]),
  (16,
    m1K32P56 [
      31386171465638275, 36465857649219201, 14778700744065483, 36340327279362177,
      19267904053739993, 45666576686455169, 4927317505179949, 36414182479957665,
      34482340375142266, 36452663526625409, 34481919967592830, 36341739954470017,
      5241107814056304, 44716594496105601, 60940953831702801, 36444968117671582,
      34200693599936221, 36405384274965377, 33141]),
  (16,
    m1K32P56 [
      31948872310300427, 36402085790424449, 23222856479834478, 36321950691323265,
      737959157203280, 44811152244428417, 17312263720108293, 36422977482459295,
      27726700415131462, 36391090539940737, 20408042290970973, 36301060725364865,
      69418063926362439, 44865027827648128, 30541454481064202, 36387792992929951,
      18719471094308726, 36382294128164737, 33087]),
  (16,
    m1K32P56 [
      17030612644241288, 36380095104913537, 17593232398975291, 36303260956572289,
      70825743750889789, 44939794282790016, 48274309293768944, 36374598685616543,
      16467628329901999, 36369099736986241, 14778525583507769, 36298863329491073,
      63507488845562161, 44959585424978048, 53059362422161631, 36366901869338527,
      13934289115258813, 36354806505258881, 33071]),
  (16,
    m1K32P56 [
      12526897051639743, 36348208781180801, 9711838564483369, 36274674224670337,
      62944560365666590, 44963983102385280, 53340734318411996, 36339413743098271,
      6615858115420092, 36333915230681985, 4926802614780180, 36271375605895809,
      59566843463958800, 44959584737103488, 52777707054596305, 36320721844097439,
      2112202652753851, 36316322759425153, 33030]),
  (16,
    m1K32P56 [
      1267760542359486, 36315223163912321, 986054156976387, 36276873331802753,
      59003945049227518, 44976077193411968, 57281255141376193, 36308626964529055,
      71354982498017231, 36302028856611200, 69102951277625595, 36274674660866944,
      61818789305090294, 45001365809854080, 64318090903781577, 36297631613369247,
      68258723394592743, 36294332308777856, 33007]),
  (16,
    m1K32P56 [
      67132789127356399, 36294332342334080, 66851125696299243, 36235092795910784,
      61255985379442916, 45036549896727168, 986143833817303, 36278939781481120,
      63473588660379655, 36278939364100736, 63754973968367840, 36233993636601728,
      57878367262638305, 45058539978285184, 6052659054149838, 36270143520688544,
      61503225170927638, 36269044094998656, 32985]),
  (16,
    m1K32P56 [
      60940266627768344, 36265745358788736, 60377166874509527, 36216401618327168,
      51685947839185110, 45062937873798016, 6615566057111751, 36258048691455392,
      58406948885471254, 36255849385039488, 57843913558622413, 36229595606862720,
      51404442796916939, 45053042051041920, 3800760454840499, 36243754889293216,
      54466260555767819, 36244854184872320, 32959]),
  (16,
    m1K32P56 [
      53340347764547592, 36243754320921984, 54466158002012347, 36214202142079360,
      43523074728427712, 45043146161176448, 71073206873587851, 36226162552249247,
      50244097249353714, 36236057252983424, 53058649974210737, 36175719151218560,
      35078786771812539, 45031051399052160, 69102851971580049, 36218465920515999,
      48273759524921329, 36230559812286336, 32939]),
  (16,
    m1K32P56 [
      48273729462509553, 36229460149663360, 52777050444038314, 36181216742910336,
      42397144755830956, 45035449344898688, 704411156906134, 36212968328828832,
      47147790901157892, 36220664425744256, 55029013467005094, 36194411184432512,
      37612164640702656, 45057439493567104, 7459789120897131, 36206370990617760,
      45177534780842013, 36249250889211264, 32926])]
private def schedBlks2G2 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      44614550468075553, 36226161447021696, 51369666973761692, 36128441141074560,
      37330861461897390, 45102519285761408, 17311357473751186, 36190978213706656,
      41799817880838209, 36239355720779648, 59251095172448402, 36165825056510080,
      36486578265161941, 45138803001707136, 27444417980170379, 36183281967860896,
      39266624694952038, 36249251308660864, 32906]),
  (16,
    m1K32P56 [
      38422216948162661, 36232759489879936, 53058817484619914, 36224099474770304,
      46619741850730699, 45149798017320832, 28851767093395602, 36177783805741728,
      38140544401055847, 36203071518302336, 43769829720096903, 36186715727103872,
      44086321031512201, 45103618495376256, 14496547570876564, 36181081350769056,
      37858781661012013, 36127205316635008, 32904]),
  (16,
    m1K32P56 [
      38140217981902881, 36093121026593920, 13089237641822345, 36196609821804160,
      44367366511296559, 44982672266637696, 51932706583969924, 36176681911747487,
      37858489603956640, 36032647937361792, 69384177139351685, 36173517292602239,
      42396302939684848, 44785859584586880, 704239345238148, 36167885214747551,
      35606500813151972, 36027149959742592, 32893]),
  (16,
    m1K32P56 [
      34480721162444448, 36041443812210816, 2674702129397880, 36191104378370176,
      35920982610247699, 44405428343285376, 41518050842148982, 36155791459250845,
      32229183341632872, 36152494352317056, 36451510333833330, 36142719675953536,
      30852697862275210, 43919444119949184, 48836400243507329, 36155793690620827,
      32792678755048280, 36237156697179008, 32886]),
  (16,
    m1K32P56 [
      34200006394288827, 36249250771404416, 61502654369333372, 36093231787703936,
      17339768677564623, 43504928672500864, 51651291747352655, 36197575115689114,
      44896038326278711, 36222861854738816, 42080769276870820, 36067928977746560,
      2415989983117437, 41307005968737408, 55873699857203188, 36267941326479502,
      47147026383276606, 35986464655720320, 32739])]
private def schedBlks2 : List (ℕ × ℕ) :=
  List.append schedBlks2G0 (List.append schedBlks2G1 (schedBlks2G2))
private def schedBlks3G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      32798876585720865, 39364150786550917, 69106949449221865, 37571991377288828,
      5783291531134053, 35392748307941511, 11686569620310974, 37968935508645252,
      29130944313853223, 37028825368294027, 15066597286182597, 39131065159474565,
      28010374484231966, 37499424062754943, 8596641178092420, 36013968820881031,
      43493637130193505, 38021705473471619, 67695215140177225, 37018929595882633,
      7748449730265258, 38703362853793157, 144416215435088]),
  (16,
    m1K32P56 [
      9437488561357075, 38576920643984773, 31388155811235688, 37509321646985089,
      31112427439031157, 36518644003715975, 42367720048724038, 38141543533633923,
      64037754137904456, 37011233517834631, 25200246143943196, 38121726823061381,
      20129216874121082, 37563197783750786, 39273475198518131, 36686869383446151,
      37020030498866894, 38127243490395267, 38987103981045124, 37084901316981894,
      21822550699180677, 37877637087217029, 144772697720702]),
  (16,
    m1K32P56 [
      31392609714864787, 37799570989877637, 31106753855129451, 37604978839607170,
      28011989345731444, 36727551833768327, 38708850292458702, 38099748300952707,
      70512245540029826, 37112389862637700, 46591919126184542, 37405944988288901,
      17877584568354561, 37626966740097922, 56722501392827226, 36657182854723718,
      54471655135872158, 37891939059765891, 39267947599660475, 37060713487173764,
      58694608677011960, 37250911919383429, 144734053566060]),
  (16,
    m1K32P56 [
      62635086549713322, 37209130309757573, 49402945172309536, 37686336777619073,
      68825049201607611, 36381206493127301, 52501545032975359, 37651142792002947,
      60377763397666270, 37087102135274627, 60945450701783372, 37062892528585093,
      59817497835308423, 37663244550378368, 31669789624730580, 36196489177188997,
      62071445124907868, 37558781315417219, 22940612244964763, 37127783411190403,
      50249547607605338, 36930946804737669, 145030404539892]),
  (16,
    m1K32P56 [
      54753392046080000, 36935344800918405, 69950893349242090, 37667636741614207,
      8588502218343411, 35969990234851460, 69952886186672903, 37216832897140099,
      71916596769621440, 37162967615420546, 45462922517708725, 36902357405276549,
      43492417333068872, 37576377997915519, 19565764311680038, 35885328678349188,
      13938932030800619, 37213532885838212, 44331619560490321, 37212443944165762,
      18441144356142933, 36697847001006469, 145438416667666]),
  (16,
    m1K32P56 [
      9152358451609412, 36621980262485381, 16189580807144433, 37440036777614463,
      59815474794824787, 35802866145097859, 24915953603150250, 37063995143694980,
      42642559248205022, 37267417529032834, 53906372953407280, 36903455121762180,
      15908208903816054, 37334481597827711, 29136076723291243, 35820458599549827,
      32233916443886363, 36958447429700484, 9710141594502278, 37289406301945987,
      30262122723508057, 36888062747507076, 145657446236980]),
  (16,
    m1K32P56 [
      18440109277806450, 36858376352988548, 38989238590931744, 37216832628914047,
      6899188496958588, 35935907555322243, 35611113648652979, 36883679380750724,
      47991309658391569, 37287205315737218, 67416424500396009, 36693451638863747,
      69951430187975384, 37114577107967871, 66571316630029433, 36032664494656898,
      32514459403977220, 36782520267708804, 64880224872072112, 37277308117232001,
      42646390318465109, 36530726048658563, 145623073194653]),
  (16,
    m1K32P56 [
      29979921875697814, 36499940863929731, 61788617199551078, 36983733026399104,
      32229913494848598, 36349323491110274, 33640028589424674, 36619784560920708,
      13934585527174011, 37270710745435520, 47993714768249244, 36106320516245891,
      8871295805391324, 36705554604781442, 59532792988075089, 36895780619054977,
      24631871550161116, 36786914640251780, 18441827284648612, 37226726320970625,
      40394796656199131, 36503267550966146, 145339589034695]),
  (16,
    m1K32P56 [
      48275937098762456, 36667109346120066, 44899637548647063, 36751736274333324,
      25476833566032868, 40762760631575682, 53060754012472185, 36661582797927811,
      28311382945792624, 37004623428586884, 26038868526798663, 37487406810880642,
      707288809570813, 36682466286982811, 58130529550500640, 44385648190312833,
      65445339447985520, 36513154953299586, 2990270095065646, 36795716252858245,
      13934813165953127, 37271936572761218, 143574353150416]),
  (16,
    m1K32P56 [
      21816241351729538, 37109212895149954, 19565034209444251, 36682463736738978,
      53906330532676162, 45821607373060993, 21253901246497653, 36537335837556866,
      24386259557122615, 36651679927605123, 22660442930258772, 36950889814175362,
      40675502846738841, 36598901373095075, 51654230090482198, 46103080655264129,
      8587364088513333, 36545031630481026, 16505866444440069, 36643981785938563,
      66289334901711879, 36926702705849985, 143183501951448])]
private def schedBlks3G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      55311922479014928, 36933300748708481, 22379951474573812, 36503244851334052,
      7462813378118106, 46309786811226242, 53059989504820029, 36662679408254849,
      23824976042754503, 36542827320201859, 52497743946294467, 36967388427708546,
      65445159081968251, 36959544592784548, 43210225623859706, 46450526195483778,
      70794154290152313, 36780328276529537, 35084451856089774, 36568117731833219,
      17032249066300714, 36949797835494786, 142818434319036]),
  (16,
    m1K32P56 [
      62068210980726082, 36962992377681793, 25756959706284720, 36490053446473381,
      41239660275728867, 46561575930251138, 49963322383827825, 36701162768265857,
      17914881999798609, 36507638770584195, 71356275322889603, 36904719234478208,
      39548954378273278, 36261351135570597, 56720509119791508, 46603357170749056,
      38984982206186238, 35945796098954113, 66047197501554879, 36447164322258050,
      42361470794507665, 36778275447602304, 142453339750316]),
  (16,
    m1K32P56 [
      48553825786111364, 36693612884478336, 34482271649693559, 36277834498594469,
      36453421736558955, 46576967566287743, 20689465192776135, 35891914274596225,
      12285210661519632, 36366901986692481, 22658480085837138, 36055894999526017,
      35889534876155867, 36473550202176677, 20968149079261511, 46560474808041088,
      29697690964557215, 36275622978606977, 19322029240123917, 36394394139576188,
      26038318620648761, 34826640697676162, 142199967285785]),
  (16,
    m1K32P56 [
      49965091798623513, 34847530797843074, 69666514925159305, 36874892649182116,
      51646670968422772, 46398846212974470, 32232507760475307, 38178879401412737,
      40432038313952107, 36395499322338174, 45748069632025767, 35973428808865411,
      37578440608810889, 37087107503641508, 41518519601693040, 46276800439109254,
      22099928274927932, 37736895188587905, 8061926366741437, 36406494941788290,
      36738589795329082, 36749682273246083, 142062541571387]),
  (16,
    m1K32P56 [
      6901769814778911, 36426425418468995, 986444513379494, 36716559653246628,
      10557101083885896, 46140460577722756, 4646229114519969, 37074989557735809,
      63512020035338540, 36352606020541057, 13373624100365262, 36536375255829888,
      52777771454857979, 35754481476029603, 47711931149418747, 46070091447439746,
      2390323288637861, 36684661872895873, 29453328807394670, 36310808489235329,
      31668024405435294, 36425323826446460, 141843375358418]),
  (16,
    m1K32P56 [
      43208141964419989, 36317571636588923, 41237116947431749, 34573597985006499,
      63192118563471616, 46045902359131264, 6889267144327402, 36236057873979521,
      21853457191041149, 36316282928268160, 4644549718156189, 35982220791454071,
      46866732370132969, 33322348484477091, 49961424565272877, 46082186494221183,
      11107122573770602, 35775356260827521, 60697235907835282, 36340462805496958,
      15057319943644122, 35475347105455989, 141972105821720]),
  (16,
    m1K32P56 [
      40670520607155186, 35267539927900532, 6334425878461762, 32724201810743460,
      52773000359280926, 46218525801723260, 6883026473548864, 34750597314136193,
      50001800972039211, 36321765352980347, 1822992349373551, 34688099363651956,
      43207463135836486, 32676902409514404, 16741549059506407, 46376854352024183,
      57548208646552125, 32809950231452800, 62105843439727624, 36215112808572793,
      55298109702972634, 34234002688751731, 141405152703989]),
  (4,
    m1K32P56 [
      62617674572014845, 34188923366314099, 21533318702069505, 34193141527252907,
      60377321834512558, 554814207872])]
private def schedBlks3 : List (ℕ × ℕ) :=
  List.append schedBlks3G0 (schedBlks3G1)
private def schedBlks4G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      40962634492248246, 36057953715201414, 45746892953783766, 39883133260435589,
      40116366896302159, 38428539187307140, 55877780165592735, 37842476405190782,
      16183112577418601, 37460938236376973, 14228627473794184, 37299304138166152,
      27171434352180744, 35436729242811014, 70798015562288218, 39436723956244100,
      15627330958100638, 38498901069515140, 56721569426409130, 37928241046719869,
      19278658702771455, 37463138752834955, 29426175972049794, 36993640593543560,
      58978252716998145, 35504894350021766, 9999489319406158, 8614021]),
  (16,
    m1K32P56 [
      25483580880289352, 35593955244842374, 68546237234776490, 38661571798599300,
      28012298652649765, 38585750005930115, 4648273535600277, 37913947949020543,
      30820739064300796, 37467537134900872, 52785588294091651, 37015630960317832,
      60948929695809477, 36032660870856326, 9999854391035854, 38198684281973381,
      32516177457875164, 38510977645313155, 54469198391641808, 37909549248143232,
      40674231559226722, 37544502042869895, 53909731588015018, 37118985086863240,
      54193517335511420, 36513148039405190, 3807812922803604, 8625541]),
  (16,
    m1K32P56 [
      29986493238444528, 36634093529921159, 4370934671443356, 37610454637574789,
      27449572044802129, 38340544182783363, 52780408661051068, 37973317835388034,
      26321112279385434, 37523613603587717, 54752722030003078, 37044218833089415,
      12534026769171261, 36983738714113671, 14785354175382797, 37414746869443973,
      46589780271859551, 38089851958172803, 60661823967889219, 38073369786364291,
      46869979583579366, 37504922593722244, 63196146712150957, 37004637018471558,
      15629302312961058, 37211336346005895, 28859008507020386, 8617093]),
  (16,
    m1K32P56 [
      9999536488612889, 37182749781886087, 26325772367791170, 37208041602657669,
      49123381477672527, 37776488510273667, 2959565418825501, 38027185650667396,
      2396825889310072, 37585185885520260, 68262077817717678, 37077205356313989,
      68827110829753355, 37160760253981062, 39836339312165867, 37124477242551429,
      44338534502401487, 37696222097828739, 58410049935148756, 37938124302839171,
      63758293501969844, 37639060764095875, 39832972021629896, 37076106582865029,
      49685532511142775, 37015624836562822, 57287418479281119, 8641669]),
  (16,
    m1K32P56 [
      38426400299975504, 36910072240393094, 61227909240488918, 37104682023508613,
      65167910403867804, 37333383612905091, 50247443117344327, 37766595103397250,
      40957295675147752, 37681938798258307, 48276607118640074, 37105794051076740,
      59537105143693903, 36601109657545349, 66293608418935480, 36790216899682949,
      64886478362739873, 37315784783015299, 39551625930638687, 37482920516166273,
      17593721559418331, 37669839338492035, 21536329694741496, 37187156888100996,
      15063466112418070, 36287749330155910, 49968381880795846, 8654213]),
  (16,
    m1K32P56 [
      54469769571827927, 36240470447599749, 44338491503182383, 36562612020056709,
      5213572845765550, 37036507420185220, 14781900991530337, 37515901452536192,
      49399023838004668, 37644551929948289, 26038228496319516, 37195953266297219,
      61505875180290030, 35989782182346116, 51937147631272435, 36669261862938757,
      15065179828683565, 36903469902182788, 46870228724319213, 37160757284248191,
      40672663907632538, 37587372694761091, 68825109301789792, 37249828144825730,
      23506246566510463, 35869936304087684, 22100542395614487, 8673925]),
  (16,
    m1K32P56 [
      20973732000923495, 35866637920189572, 12530345962735003, 37452112028002693,
      31108609259635713, 37145371301855620, 20693300693533797, 37270711953580671,
      2110252798870790, 37414750526882693, 49404495544681595, 37293806076594563,
      50528711924219706, 35806165200070276, 63477501422961982, 37509286011894660,
      35893408973357960, 37034323009810564, 13656503581246261, 36948553251504767,
      17309862888834248, 37365267722102149, 31390178640037014, 37310297945631107,
      32232559264628553, 35814961595063939, 40395436633720099, 8687492]),
  (16,
    m1K32P56 [
      35328491949424448, 35838051356016771, 32514244655809804, 37435619068384388,
      42929767993082597, 36767140342092676, 29137708896387969, 37009022112818559,
      62064667653669962, 37221232453762948, 8027321786401946, 37327887984189314,
      30260567973265328, 35975490510784899, 2959273297216690, 37343262675344516,
      43773776309748054, 36408698108642948, 5212348754854749, 36974932168840064,
      39547313762436065, 37087091263351940, 15345314708489372, 37325687199320705,
      17875175072432208, 36162407420379779, 49402352393815142, 8690051]),
  (16,
    m1K32P56 [
      10838828933939365, 36269060031488899, 35047012628071519, 37230018061178755,
      41239956052214248, 36579121135964548, 46870615236051703, 36884775755334785,
      12527876365648767, 36999128772908420, 11404342951904395, 37302596196815234,
      52497486259716890, 37113484626057090, 40676185747588127, 37379567295692419,
      32514309073306170, 36668187232027012, 70514354367988409, 36720949328214918,
      69955669331247916, 36687964985770117, 21539125864203363, 37237719927241858,
      15905812327336850, 39812784380340610, 30823797057422696, 8659586]),
  (16,
    m1K32P56 [
      6335650227326811, 40908996651146370, 36454159879603438, 37304863419525762,
      56719988850983487, 36646190323180163, 52217651932594983, 36823203338996631,
      35634701616906895, 36735245260823426, 6616348183135083, 36956245353167490,
      49964056786607266, 44451619559083649, 40956453833965257, 35205945902702722,
      69104866320613884, 36583481267981442, 62631367079067998, 36475756892352160,
      60131850735157889, 36716548429311867, 64313225263350429, 36768229166794881,
      65726470747824817, 45912867760920449, 33920133464555050, 8551554])]
private def schedBlks4G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      10557366748357494, 46094286676195458, 26601723939946343, 35977824338859138,
      17313316002628060, 36557114547909762, 27446337855586894, 36693459859462052,
      8906634781164104, 36675870039075201, 67977777301258817, 36659376626499457,
      40393808816284872, 46412044630636930, 14498841109496298, 36623241908995714,
      24912981467693571, 36629689730930562, 13935736539939514, 36808910056879781,
      42121373528982038, 36656080490736258, 59534898102436414, 36528534793148545,
      63192577574937912, 46524192904063874, 16188013069304559, 8512130]),
  (16,
    m1K32P56 [
      67976574148978008, 46553880053564802, 20973152091276112, 36980585050272386,
      5209651498811455, 36223975376123778, 34764463907898111, 36878173853693861,
      55069600406209021, 36538433803422083, 50529008819012113, 36580211453790591,
      702469885633926, 46601159842130051, 9714178763359235, 37221378834960003,
      2677261471284852, 35544479656418178, 45178853378589420, 36835281659502757,
      44373710201782984, 36762733135168644, 58974323274777081, 36574715120367742,
      46582843859314092, 46642940495424898, 19565287560807861, 8511362]),
  (16,
    m1K32P56 [
      28005632865379759, 46633044639101570, 21253875429312276, 38018525050295170,
      61222948511842049, 35745704075175809, 47148959157682691, 36370190606738085,
      19040949410562534, 36549415984362887, 64888291377054155, 36528531806608254,
      39827457352770997, 46672626252365951, 49961114712901537, 38276910886795137,
      51652352577928897, 35745707363518849, 54467265593114366, 35709384001078181,
      42121949034086747, 36394378402388104, 71926213767954848, 36476854005046910,
      25754142327481763, 46609953502344062, 9146044789524863, 8492673]),
  (16,
    m1K32P56 [
      12806143088829835, 46584665087213182, 5205193253358198, 39247778160929409,
      29696595705298657, 35721538710104193, 26038082482241003, 35474089637176997,
      1589140069974249, 36292123401596302, 4372979559924078, 36404283251267711,
      71634228457219387, 46494504160637822, 52494608547021260, 36106472081412992,
      27444654197931806, 35841328720189825, 6334606476673389, 37022202595318949,
      65483672018256097, 36297652836448638, 13931751395590466, 36378995876906879,
      44049925447460095, 46435130230777480, 19291285831909007, 8477057]),
  (16,
    m1K32P56 [
      6051001158575348, 46427433280301706, 42373990564724372, 35634780737455489,
      22942171443789669, 35857818425027713, 66288664866294641, 39349869147586468,
      30299149605765693, 36735283563025024, 28007188151566664, 36385600630932351,
      47427809881924851, 46432931224430731, 38715168053100651, 36125162906675331,
      23507496506588997, 35852327460328065, 62348152671406772, 38995826185370276,
      40713762401322199, 37524726368651648, 4082085713183080, 36436190949922687,
      46582199540491498, 46425235834422921, 53349895428341886, 8492678]),
  (16,
    m1K32P56 [
      18434384045188345, 46458221166537865, 41246020465164479, 36231816406993287,
      44622522066828950, 35746775635931009, 16468070835718254, 38337219928323493,
      60980368750446751, 38547262518871424, 1830608030892452, 36495579358410369,
      48838062402807156, 46589063469825671, 56162493503406314, 36303286642517385,
      44343370643506199, 37522488139558017, 54185644735301435, 37986506555604133,
      21011480401447626, 39164083660408449, 57281741091930522, 36461503926687114,
      55887929102280181, 46729800186578310, 69953814083436918, 8481931]),
  (16,
    m1K32P56 [
      37312504787412497, 46755088635277190, 29139899522449910, 36590261492594828,
      10006180840968194, 40519761651967617, 10275118911030907, 37853504823510182,
      39026218206924011, 39720435084928898, 27728358894502141, 36272395761651343,
      37312169807160846, 46718802067286662, 39273007261385623, 37090538192679565,
      40688065694961354, 40027188512538752, 38703348547159684, 37885381919921829,
      57602711958752711, 39937039194227844, 8027700373717052, 36072287984065165,
      22954437772879032, 46284492558439302, 14221704225260947, 8394382]),
  (4,
    m1K32P56 [
      56730863758255128, 46073385235403142, 24355048195982898, 37199424186723982,
      13660777065711505, 36385593185046144, 142032439378314])]
private def schedBlks4 : List (ℕ × ℕ) :=
  List.append schedBlks4G0 (schedBlks4G1)
private def schedBlks5G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56 [
      66023841880506443, 39186092566230156, 17891492005904447, 39177293704912012,
      1847405437616179, 39133311377498764, 16765686564093994, 39032155099775884,
      46039277400195112, 38851833682871692, 67431573181530156, 38565958277282444,
      67994686326014001, 38178927281841036, 67713421784547379, 37802892040215436,
      71091267515809848, 37535709573823884, 6352078689108028, 37412564221199501,
      12826058970464322, 37463142846613133, 19581466984808519, 37596185162868109,
      27462676122730572, 37711634907194253, 33936450248605777, 37762212945386125,
      41817560604573783, 37750118401364877, 54202231934320731, 37705038374298509]),
  (16,
    m1K32P56 [
      58986980110270559, 37701740309182093, 62082822592364642, 37711636433929357,
      67148955552022629, 37723731397382029, 2690734905589864, 37734726563995022,
      11415982434975849, 37741323449217166, 15356172540870762, 37745721327959438,
      17326029220380778, 37741323298229134, 16762593929756777, 37736925385941390,
      13665879553769575, 37734726597573006, 7754419706429540, 37736925822159502,
      71930237650632801, 37741323986113421, 61233720380653660, 37743523093259405,
      48003984154787927, 37744622722334349, 32803970337046609, 37740224843601037,
      17885465855819850, 37734727436460173, 4655811234725955, 37730329507391117]),
  (16,
    m1K32P56 [
      62920783518597179, 37733628310713228, 46031945610919988, 37740225749583756,
      26609867272716331, 37749022278817420, 5780448410894370, 37755619734462092,
      56727182970224666, 37762216921668235, 35616302016856082, 37762217022329227,
      15631325265166344, 37765515758534795, 69111330320187393, 37769914123807370,
      50533758517084153, 37776511445226122, 32800633119014898, 37784208211164042,
      15630487739334635, 37789705937070474, 71362365622878180, 37799601944367241,
      55599599421915103, 37811697025249417, 39836837515722714, 37827090590681481,
      23229654974496726, 37842483971562889, 5496581116493779, 37850180620055177]),
  (16,
    m1K32P56 [
      59258177112604625, 37853479138149256, 43495475336282063, 37860076275012232,
      30266052645191630, 37874370043600776, 19288425472819151, 37896360376806792,
      9718164594327504, 37921649211342472, 71361059938533329, 37944738905182343,
      60101936314679252, 37963430468625031, 49124283372765142, 37978823463629447,
      38709588974206938, 37994216408302215, 28857853119070173, 38010708881380231,
      19569080102322146, 38028300798977671, 9717352837054438, 38042594181692295,
      71923219609845738, 38055788069556358, 61227058824708078, 38071180863235462,
      51375314380161012, 38088772629837958, 42086511299035127, 38109662797106310]),
  (16,
    m1K32P56 [
      34205087396429819, 38126154934641542, 26323659198922750, 38142647105731206,
      18723705977864193, 38155840741937798, 10842286370095108, 38167934883294342,
      2960883942195205, 38180029007874438, 67418563414097927, 38194322071825541,
      60100149594980359, 38207515640926085, 51374369482899463, 38217410691920517,
      42367144458944518, 38229504749391749, 32234036707819524, 38240499261680005,
      21819479748935682, 38251493723637125, 12530861350027262, 38262488118487173,
      4931127170072571, 38269084483604613, 69670444824297462, 38269083879618692,
      60663215502229488, 38265784791079300, 53907743045091310, 38262485618649988]),
  (16,
    m1K32P56 [
      49966998880354280, 38258086917814916, 50248366481833956, 38254787795717764,
      55314804392558561, 38254787325946244, 64040417000325087, 38253687310994052,
      426969183453139, 38256984705016709, 1552783189901258, 38252585920293253,
      70232600197103597, 38236092591551620, 64040077694435358, 38220698640224132,
      56158705331175496, 38238289685414020, 47995857991532629, 38259179265497220,
      41521856217251882, 38185511701243012, 36736700008071682, 38211897648292996,
      32795973024318627, 38227288462279300, 29699670970764103, 38152520547515268,
      26884843893922037, 37896335109988228, 24632966770304533, 37602766998535812]),
  (16,
    m1K32P56 [
      22099614670170971, 37441139594551940, 20129221113261499, 37347681408174468,
      17595869012995683, 37299302846215812, 14781041935953567, 37278412007843460,
      11966214858976957, 37266317262493828, 8306967146770130, 37252023460334468,
      4647719434497769, 37234431106514308, 988467427192577, 37214639679106948,
      68823868094328609, 37192649178111875, 65164624677089097, 37169559115157635,
      60942427011395445, 37153066088415363, 56720233640538017, 37138772101705859,
      51935090316324812, 37125577626624131, 47431426263920627, 37113482696725123,
      43490716460167190, 37102487312008323, 38987056702533682, 37090392415663747]),
  (16,
    m1K32P56 [
      34483396945227850, 37074999017991299, 29698266506440797, 37057406613841027,
      24913140362555504, 37042013249723779, 19283572108669056, 37024420862350723,
      13091058196525197, 37007927969828483, 8024465666257049, 36993634150893699,
      3239360997798051, 36979340331959171, 70230375390949550, 36963947018173826,
      65163791450878137, 36948553704387970, 60941653915840710, 36937558437112706,
      55875087156097240, 36925463674987138, 51089995372736746, 36912269367678850,
      46023428612796670, 36899075110701698, 41519820396540180, 36885880820170114,
      38142129266929977, 36873786058043522, 34764442432418126, 36863890302394754]),
  (16,
    m1K32P56 [
      31668230574551389, 36852895018340994, 28853502283526504, 36840800189105026,
      27446166056120687, 36829804921828738, 26883263348453745, 36822108172658306,
      23787038605357422, 36812212383454338, 20690813862130023, 36803416105878146,
      17313105552126300, 36792420805046146, 22661396387770708, 36609902780873347,
      20409618049904965, 36601106503297411, 18720793960624440, 36594509316086147,
      14498660720750894, 36589011606946435, 9432098255712552, 36584613409433731,
      4365544380739871, 36582414251953795, 2113787518234887, 36583513679690115,
      66008564282339586, 36583513511909250, 55593908539601153, 36585712317050754]),
  (16,
    m1K32P56 [
      44897777819955448, 36590110111893122, 34201655690572005, 36596706963545730,
      24631442058162380, 36602204286793346, 17031604803055828, 36608801172001922,
      8305846166008006, 36616497501728642, 70230280913137834, 36626392804378241,
      59252679511945351, 36638487079951233, 47149161023844444, 36651680816819329,
      34482688287223863, 36663774991728001, 24912483244552237, 36674769705342593,
      13090448323031070, 36686863829920641, 423958405754889, 36701156860311425,
      58689145439760377, 36712151372596352, 49963361032056849, 36719847484220032,
      45741244971986964, 36729742803652224, 40674678211784599, 36746235209628288])]
private def schedBlks5G1 : List (ℕ × ℕ) := [
  (8,
    m1K32P56 [
      34482185774477006, 36764926605304704, 26037850572959322, 36780319398987648,
      15060326479539946, 36782517935702912, 13934134512562236, 36753930096493184,
      64599479994658518, 36763825281702271, 44614468881066021, 36705550175556479,
      16748051043687188, 36570307460294783, 56717038168146143, 36267939397035390])]
private def schedBlks5 : List (ℕ × ℕ) :=
  List.append schedBlks5G0 (schedBlks5G1)
private def schedBlks6G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [2205516834]
    ) [
      64324052533280685, 37162963286971269, 37873457547412320, 37341086989279879,
      44613060163437577, 37522509159495053, 12247891733939370, 37774309368627327,
      29137116196603211, 38448329708733315, 4368018335893153, 39733596591974532,
      50249161122547871, 35673119679320452, 35333010315316467, 36992536484819845,
      19009153950776988, 37177257105934471, 55323535991538543, 37358681759100040,
      13931239730938900, 37710530295157388, 21536626095523011, 38007406303373694,
      32796333845677578, 38542880259586179, 6901525068154633, 39214624016659844,
      71923576144562428, 35490600933661316, 3526312183106305, 37001332712084614,
      9439408435527176, 37188253883171719, 9722291948323700, 37458737619216009]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2201060371]
    ) [
      13943093951692272, 37200348460743815, 14506683651490678, 37484026453766281,
      32508038438421555, 37732521232382601, 62350523490796835, 38063482973267837,
      33922405556127254, 38630829361846147, 19286827769628482, 38446064046668164,
      18161786877020478, 35418033233344389, 4652388186884178, 37005731127699846,
      25483628092816850, 37224537498458503, 14786019733046135, 37499420052775817,
      40389281951614016, 37750114374724487, 60943118543193423, 38129453150720893,
      29981824604014112, 38579144765595267, 19005159520569216, 37972174753194884,
      6902899481807102, 35438923400624005, 13096899475834549, 36956253020563078,
      42653180739550704, 37192652063910023, 54753855815451454, 37487325726875272]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2202043379]
    ) [
      46593641428909565, 37171761695306375, 41242670387266341, 37457639030369672,
      59248337313432610, 37784200409544837, 6055098649969934, 38203117158116222,
      5211816197326402, 38348240562560643, 11405390986446782, 37552162468991364,
      17317636832725022, 35520286103447429, 22385814209987916, 36885884511271302,
      56725860106010170, 37246528318231943, 53626577229218563, 37478530405616263,
      70507619849569361, 37822683702337156, 25195392774538548, 38221805164748670,
      8026724881040996, 38105245204505731, 12812843181836232, 37344355962537604,
      15347458024834880, 35599451896952709, 32518896177087639, 36947457078540678,
      53910152549727875, 37200349282859143, 62914538500948786, 37499421713742470]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2196603959]
    ) [
      50532177948802711, 37138776581375367, 45181443170599750, 37518113663069062,
      14494494623826958, 37879857619042948, 50809654308865354, 38163526300475518,
      6056374275245722, 37798478373371267, 14220325443045256, 37150843342098564,
      24073409931150894, 35692909177350533, 47436696263033841, 36896879292011910,
      26887433788882648, 37201449146822023, 63476865689617179, 37537905476325509,
      60093711431009327, 37917239403726979, 68261141519238495, 38053572101000318,
      5211932166620856, 37603863556979331, 16190744771135264, 37070580033450372,
      29421546150724992, 35759978799446917, 54191606066807715, 36851799516605574,
      65167321946291987, 37208046602470022, 18721953554203381, 37564294074126981]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2197390430]
    ) [
      53626688985595680, 37221240892998790, 8588751314322143, 37575289190394501,
      28287326822302782, 37932629664009603, 15062164763215235, 37858955539734399,
      62069898939631296, 37413646250228098, 18161249996932716, 36957331308862852,
      41524957252453593, 35820452073194373, 51376083194905420, 36849600845682822,
      14501151823134533, 37234435602952582, 47995003242971880, 37611572671422340,
      12524887040623691, 37900741528296067, 24069333953906083, 37708320567665023,
      69388325645420193, 37292698998102146, 22946444857738723, 36910052845745028,
      49406089087648877, 35853437405254789, 39553537165787913, 36868292778243206,
      47151806736596836, 37254227315557509, 20128868881040126, 37644557181358980]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2198635670]
    ) [
      36455676017213270, 37263023542792069, 15343699788399354, 37652253376868484,
      71353350448120934, 37813877257546626, 32232189884663239, 37526899370688127,
      71358770743707211, 37184946036503938, 31109352320435521, 36836386019674500,
      57568455380010004, 35877627197944453, 11686853040571096, 36867193769938566,
      4930190858289022, 37286113538612613, 67134730432119554, 37666545635492227,
      42642928593699964, 37720416890120322, 42646768319432147, 37403752893947007,
      1553071009531379, 37113476337868419, 38427753248490708, 36749525322498692,
      60382797118342102, 35933702190304645, 55877994883744402, 36894681996842629,
      50247438766997429, 37315800419645316, 53060895700386572, 37667643402266499]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2200667341]
    ) [
      44054890496098204, 37325695940401540, 46868514932097803, 37662145357582211,
      50524498525783196, 37574180014888322, 58972389985322442, 37288302679866239,
      4930925347898735, 37006824448183427, 47716345866978412, 36811098778965636,
      53626843619689334, 35986479100767621, 20130226159059657, 36900180142176645,
      21255103852019678, 37353183261309316, 32513364138296093, 37625859880009091,
      47147004964209848, 37471924040988802, 70794390548546982, 37195943468239487,
      9997582300448018, 37027713625621123, 54753039890088983, 36652769993761924,
      41523015888765831, 36044753502258565, 65447358106927628, 36917772714085252,
      144506355613713, 37378471223417476, 26320059954725674, 37571982199618435]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2203944159]
    ) [
      69950120190967826, 37383968513113987, 10276158081172271, 37553290082514563,
      13651594406102227, 37338882077033602, 2959007062263138, 37134368317259648,
      15345714227479706, 36796815697250947, 61789605062476774, 36631879256062340,
      20130428029207231, 36032659226680965, 34484874433036842, 36944161395784836,
      54468343641571329, 37402659120247171, 51371655003407171, 37479621511591554,
      16466288340010210, 37257516991828610, 425826762065181, 37047507267761792,
      21819685931746387, 36901268916011651, 63759612067218323, 36634078228992388,
      71077093866636089, 36033759107408516, 14218414127088156, 36969450179981956,
      36173213181706244, 37401558350309763, 32231060234535772, 37398256392833155]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2207876268]
    ) [
      36736300570607618, 37400458469577603, 29416142963442528, 37371867878881411,
      71353900210619613, 37161858473609601, 71076166175130810, 36985935522558591,
      29700950913418239, 36879277223836803, 61507387046789982, 36527425483664516,
      42929286953927382, 36027162507401604, 66853929822880199, 37001335849389699,
      18439937457487871, 37388362533036163, 7742668541035384, 37288304055630723,
      60657863982154960, 37094787341560705, 426067278726255, 36929860530192000,
      37863639333831612, 36928754525667459, 54751678363108146, 36531823597291908,
      23507161371214626, 36029362050743428, 44617320762474960, 37033221149706371,
      15624762489339904, 37350977963269763, 37016190673060757, 37212436763457666]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2211349565]
    ) [
      14779804986605570, 37337783488191619, 59815706736362396, 37190446480567937,
      1829598146888864, 37037612485152642, 707692576080919, 36913360054395008,
      47152098811216782, 36358110171890051, 40677551567831847, 36652769876355972,
      71076269226426621, 36029362587601795, 28854807933059626, 37068404699689859,
      12244996895244288, 37296000972578179, 47149560417518516, 37120076612301184,
      21814312904918137, 36955146780978306, 144841404220376, 36770420690669696,
      53907309269713727, 36255855640838275, 27447974254183075, 36590097713578628,
      54187500030820600, 36029362973464707, 14780247358538202, 37094792039217027,
      35045883046428672, 37232228274747266, 37297429426504651, 37049707465435010])]
private def schedBlks6G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [2213315509]
    ) [
      22943141945769984, 37212436729901698, 69103698067882961, 37027717065095810,
      11681213745169453, 36925457903605121, 144953068389250, 36596710989949312,
      60943861559493407, 37179438848278403, 6337015990944237, 36165686208486020,
      33358089748710524, 36028263847694211, 65444948655571032, 37118980137382530,
      13094137668665343, 37156360932220546, 11118727584056288, 36989232413304453,
      37013965945078778, 36795717159038848, 426492466135903, 36714363482065280,
      64884279302390465, 37310281973498499, 62631787988812383, 36333911554648195,
      15624831216550971, 36033761623921795, 53623536487334179, 37131073708304002,
      22099691965415428, 37084891233569410, 21534315334960107, 36895773908160131]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2213249832]
    ) [
      23506654535254022, 37064000294533762, 3238639417394156, 36881479988566659,
      40954641389618084, 36778124452755841, 2115385270633216, 36714354976067712,
      67135726923383447, 36796812408915843, 40394942704288383, 36446061807792003,
      71919543094641305, 36035960764598146, 24069011800752523, 37138769014619266,
      52216204517212164, 37002427089709442, 12527678720738288, 36838597374168962,
      65724409275515755, 36679170604007297, 145069019595469, 36870481030278016,
      67416931312304729, 36503243693490563, 22098682666713879, 36521928059776387,
      40675764855734652, 36038159720727938, 32513982635409885, 37133270349152898,
      27726185032548361, 36929857124465283, 6335151923954667, 36700059680863872]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2212594126]
    ) [
      38420340065665026, 36903468694409091, 57845102726382571, 36686865876884349,
      47710027945509646, 36790224583279745, 1552418126856779, 37071679863755648,
      66009096860238537, 36057940880259203, 61504874471523256, 36497738300647554,
      21254545522196738, 36009572317710978, 64884060233630105, 37124472075080066,
      49964439058939919, 36778124352083843, 29415953986388963, 36694563045482114,
      48835906376925855, 36766033381595521, 8870728859157100, 36778126281387392,
      63756798833492595, 36873779044964483, 28291016188264958, 36516430988173954,
      48838358768386835, 36017268831963266, 15623589984305584, 37122270552050818,
      19284525592182820, 36590110095062657, 23786338476721122, 36866085215078275]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2183889481]
    ) [
      55876590393131380, 36490054956377984, 43489827604038623, 36845194879991939,
      55904507713257905, 36741831173852801, 19846990222688975, 35990881710488995,
      8024813575307888, 37322379573259138, 50245849625034628, 36454999919827586,
      22379809697334564, 45033257284310658, 17872288869810605, 36697860338765954,
      24635182967529429, 36686865105037694, 46304556207145570, 36760530974535301,
      66041785857049172, 36620873368973697, 706206480171635, 35215732841248417,
      17313384725316119, 37656632383059330, 31668574171856058, 36594638634759298,
      33919952983459274, 45386200130940290, 66846267649589755, 36642884505730177,
      32516705656348980, 36683566821792892, 43489883766030893, 36730843170652293]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2179891724]
    ) [
      57567566265426225, 36661576220135804, 8305460138050088, 36681364912525189,
      44931866975044155, 36535108442047361, 26038769697587789, 35160751371024289,
      7461537198866873, 37150854467383682, 17313036821232895, 36387931505694082,
      2112997159109526, 45476359530759298, 63751026407866681, 36603301617334913,
      16187832688484761, 36672569725806461, 28289199943680518, 36601101201258882,
      45213715611681354, 36617573743329408, 44897455699755516, 35249800639188385,
      71356399858385453, 36472452236287105, 17312976701127990, 36179024715840130,
      8587608820449640, 45487354244380034, 35321980713271385, 36579111874996354,
      6897277247660443, 36621992996278909, 66850580263502321, 36650582194064256]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2175762950]
    ) [
      704484163297704, 36600002260415869, 37577131147428331, 36614298645890688,
      5807382079242745, 36792395236398464, 57845192953135633, 35214609338073505,
      64319138893234867, 36051337185715329, 66289506690170129, 36032791179288705,
      61786555509669880, 45607200575581313, 35603348292927467, 36549424037606786,
      6895688106091029, 36576911023024765, 22095887176204757, 36538428652591999,
      6652240799564277, 36469139086173312, 16186789026234875, 35233292496146082,
      56437895386923334, 35365241779012481, 70793767713340713, 36028394542056065,
      40110663022312770, 45686364875915138, 2389421253558290, 36512041028182656,
      60372575015576150, 36598903201573244, 1829478403310002, 36594492840377468]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2173206962]
    ) [
      12520720872022619, 36596702685103228, 11963256170119596, 36507628787734139,
      66606634174677503, 35582927982772352, 27727108452614549, 34895732813144738,
      47149186780266016, 35435614985937281, 67977768059960310, 36332959648818561,
      27159691633327943, 45708354638700161, 27439457285472542, 36485651960519037,
      71073593426879079, 36557118068568699, 34763386414137759, 36405366941810049,
      10874623144657355, 35139824495218561, 30823251588841818, 34866072490423458,
      42082491168881835, 36829796115837313, 51933724430334935, 36334059495986049,
      37291476531250030, 45732543575733377, 18713393763549456, 36463661258217596,
      46869747612099201, 36513139180444539, 61503552153485706, 36535104817568387]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2169930110]
    ) [
      39551552837558926, 36499945980419451, 69947968959381893, 36604373328688771,
      33111369641525670, 34790179411856769, 46585760088228396, 35007918248138402,
      36452841326345070, 37215727096343937, 49120082744540445, 36559460403084417,
      42356806413550631, 45801812472736642, 20972864394789491, 36443869881218939,
      51373819725783743, 36506547009570948, 12531793882546549, 36858357948434308,
      22134034527388084, 34673673927658886, 58126152529707776, 37839159817538210,
      30541879712316220, 37114584961831553, 46024485066802990, 37159794322269569,
      41231151440823209, 45836996458938498, 53066092674646902, 36415281236672123,
      19566180981318366, 36386693866850439, 5773130268115287, 36354786001885315]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2167439737]
    ) [
      57564671465661155, 36475752563905158, 27727564271681873, 36236041950470786,
      65199839105614229, 35252010936823169, 66007323024326798, 36788016299229858,
      21534405535694223, 36342714360589441, 28569978535641339, 36404430253411201,
      5205184669712563, 45863384301781632, 37574824188936515, 36391091712292478,
      20969716131799795, 36407578128729469, 29696441705529670, 35955674537836415,
      28326677285405020, 35778642428505984, 70229387543609256, 34902342667079330,
      17593665654652753, 35651113460104577, 27443408641227695, 35787604498659713,
      38139466277420710, 45883175309764735, 54460187434974842, 36366903194656895,
      10271970447696645, 36455956002890619, 19840329281143082, 35929291593810814]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2166063426]
    ) [
      66285387711488778, 36449358614374010, 6610395490844964, 35944685444450430,
      69703619118793091, 36138175315175547, 7178881094418397, 34490019330392739,
      11682884422041758, 35158517403032705, 37014013138664075, 35056429819831681,
      11963848207727742, 45911761957781632, 22371133816208583, 36355908145524609,
      28284118385795868, 36444963101318778, 11397162312958240, 36121714232023164,
      18756695578476917, 36705521654039166, 8867662233829523, 34393255227333027,
      8868018702680814, 34747311227871617, 27726060507527715, 35743624687854721,
      58129356447644433, 45919458790824576, 21244890276527882, 36340514227811717,
      6326033692795680, 36392190486140282, 9428478153490714, 36397715105123193])]
private def schedBlks6G2 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [2163310848]
    ) [
      4919101192643357, 36363604542921594, 20969059572678932, 36490082285908603,
      20726994644664610, 38779198839278719, 5771385944506823, 34278924691132579,
      2112211259328984, 36524124585267841, 71356043504351676, 35887660341986176,
      6906614396650166, 45889771356092546, 34755242630020994, 36306427907816841,
      46869240780530435, 36275647286962809, 36169206529360118, 36725378042659971,
      55348283634647252, 38687937411653247, 69103186980733617, 34140401912761762,
      66569804850760060, 37114564074204544, 60379833670465851, 36002008913736576,
      20417490578801643, 45855686327850883, 52205918106648578, 36284437675327369,
      59817879991788257, 36294343665507960, 9148192878395631, 37028845902667396]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2161475807]
    ) [
      29137210613342933, 36358116698893432, 6052539364507886, 37142096321733764,
      13126839558635850, 38926526468852097, 55029365139801118, 33772066507441570,
      66007460510534242, 37126671704440192, 36737365863528425, 37038847573420417,
      30832760483251173, 45809506604650372, 10265579640554435, 36284440443645322,
      25759154457322205, 36504355268588153, 46868708796432614, 37304820402130307,
      46622409031582146, 38452653147259010, 51933123223716999, 35346564541221538,
      64882024464615372, 36941952106810752, 36174506055663303, 36705696036742529,
      36739985618993935, 45835894783025540, 18155980006130257, 36274541416448134,
      14780122818257624, 36254766095261313, 8587472013197530, 37315799077196674]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2161279006]
    ) [
      63193032830919387, 36282254305336449, 13653781075362000, 37344382403352961,
      65762673086333130, 37223425873324161, 58688385207207070, 36694551334869922,
      55592040269513724, 35819348117610112, 46589208982946450, 36546267270138496,
      43210199277141700, 45850188299940740, 11402620596552140, 36297630472768387,
      48833277820969685, 36189894657370754, 29697378007023877, 37249816484560509,
      36207929381060726, 36730847113324673, 68539927783113782, 36815484544446882,
      48273441758216782, 35153042225688448, 30262895803925201, 36380241014343552,
      51934411732188327, 45860083820679555, 64601764825366800, 36269041291330177,
      69660450399101673, 36073341441916546, 48836976342040791, 36894669447299963]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2160557981]
    ) [
      5483949553197765, 36056846703888771, 47148251036287178, 36751731996173947,
      40711215474966546, 36368010339668864, 44896055501488726, 36965013411332770,
      49398843415363865, 34873757464173952, 69385606854181728, 35658959675238015,
      43489118761876477, 45695156187289985, 71076191797804617, 36197571475102848,
      38980094502740516, 35983172143468931, 20123522226946197, 36284436266073212,
      20444304184147906, 36242667977070206, 62628815821570241, 37100255790913441,
      41798718370906298, 35060670196197504, 47991859349521401, 35600681347881343,
      6615338479549628, 45415880267374720, 41803709058023060, 36218461088639360,
      26032859762958616, 35917195556980356, 5768766546542776, 35923795546242429]),
  (16,
    m1K32P56Cat (
      m1K32P56 [2159706379]
    ) [
      52210805690572960, 35917194063795076, 2109527417716951, 35807246609082750,
      46619363899965341, 36110732168711294, 57281246528765702, 37500489935265439,
      2110592007372877, 35930385219027841, 37575481319130476, 35704025357816703,
      41799328341458971, 44706697263937406, 15909931115904728, 36335008297688960,
      15623053040852605, 35849019997566598, 46301274817200393, 35511477545110913,
      54498090563043154, 36045870126481534, 20970725417582084, 38200893555782557,
      35605676132565007, 36874865690335872, 11115746877671557, 35699616573824383,
      45739759033484111, 45087122163444861, 21258806110486381, 36046937660494720,
      38141592366261336, 36144794950473603, 49681203788546173, 36325119085292672])]
private def schedBlks6 : List (ℕ × ℕ) :=
  List.append schedBlks6G0 (List.append schedBlks6G1 (schedBlks6G2))
private def schedBlks7 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        3823060139474946, 39462085604787093, 60939343331822043, 41065199831356556,
        61513086613950202, 135]
    ) [
      10574293836922880, 39462080655323536, 30258562288552591, 40226251857139362,
      43499474075225500, 42733209837895816, 10570243330118441, 36029383643399308,
      58990515066937089, 38982687059185040, 55904915674925201, 40045934969848727,
      150137199954967, 41494022587120000, 32242171568034011, 43294919620069258,
      67713559212628043, 38424127870872206, 32537347644686337, 39518158499913619,
      70509488250980966, 40697957814156182, 34210610870390371, 42992647790395784,
      54482053418292245, 36030482601366156, 57302670243369318, 38923318045056912,
      66022767702673519, 40084418799654039, 431461849205908, 41963509991242368,
      7471922635968843, 40004081334902666, 44914571459728909, 38363651946342798]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        34209910700408832, 39787550022361486, 31665937141566036, 40688038368059525,
        33366190251217055, 135]
    ) [
      53642030753284098, 39548948634004884, 24066125665831427, 41058601603842699,
      2966531973877585, 40945308988867463, 51104624297546918, 36033774425345420,
      48014266466404881, 38895828945816977, 56164915815483120, 40276838166337680,
      1555892879461629, 41688607706687360, 33087571450565292, 38855091750911882,
      18738601189215004, 38105268290898062, 38435548688515076, 39488480057925266,
      37013970296211891, 41322471408657034, 51944414873161651, 39854593403781510,
      57297352982368461, 36029378576643724, 28868895627774618, 38851848447180691,
      15351697027139409, 40547324905097868, 148642546158821, 40299899019433856,
      17606409107837204, 38424083108935562, 66587620575054487, 38067885533108368]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        33638671530622976, 40030528233798282, 20688413064072036, 39369707954086282,
        53070666993536333, 135]
    ) [
      64611359906299904, 39848021282792077, 1548114640079458, 40430751187806338,
      15633296788459601, 39613757692838023, 70808718732594690, 36029377821701261,
      26333627963899867, 39007984299274382, 2955089971021623, 40440658687379340,
      148668325727753, 38962892460010624, 64332380506263501, 36452658760335242,
      45756230277564997, 38087679863025807, 59260247263903744, 39963466430046090,
      49117385708047088, 39911766180185477, 33648361022853001, 37613776257679495,
      8038965675723269, 36029378979368334, 55602408312899941, 39153120203191180,
      69676702539745158, 40230630458016130, 149037699796538, 38949658961859712,
      16200490182806489, 39292697294901899, 6346383438283220, 38167945436610958]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        22948111216312320, 39115722714923655, 20688413082291148, 38000803847140738,
        59544819033737834, 136]
    ) [
      26606096327737344, 39979948031325066, 60939334733958038, 38390042238432645,
      53915298078231742, 39037621921382535, 55323317116242426, 36029380304814989,
      16476733846880150, 39360925417588362, 60936220754085853, 39285044300593292,
      149450029239654, 37378505330880896, 69398075322436122, 34450448086203531,
      10566545176759795, 38296591316874636, 49133238207610880, 39620394189746050,
      25192012699503625, 39028821618255226, 15072167880133252, 41193732397072520,
      14508036783833373, 36029382385209228, 9149493972991087, 39419192369953675,
      40389191699302497, 39157506219790992, 150051326430129, 37768833569590144,
      68833257037204406, 36095317481394059, 70241490854054620, 38463716564092551]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        28580823302176779, 38164621903464837, 5488888913168654, 39276226498043774,
        65734107364426969, 137]
    ) [
      56150476188123136, 38991473353805447, 140739785296787, 37426859750901636,
      71366488876812605, 37356477668655240, 16757349647681496, 36029385740602762,
      23230234806355260, 39168495715897984, 20131278368049445, 38302034885584774,
      150880238209488, 38137139380399744, 60949758624956029, 36949638016224394,
      2108655118288653, 38667121014159752, 1837689821626367, 38602239123576711,
      7177609917074046, 36755053314814334, 37306762544253052, 38299817071345289,
      16476166805292644, 36027188931861897, 42650200066128105, 38825444648780167,
      10828370614847912, 38757273082133129, 71927544739563058, 37673171242524799,
      37023535175010748, 34507622724519817, 1559599356742629, 38796857396700038]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        66018301296030267, 38127284661574027, 8642309676238020, 36980507774961528,
        64040313993727916, 133]
    ) [
      53910646391734335, 37901832987341444, 29133212159477905, 39479632961361025,
      66859410258232191, 37438933172286601, 9432600940479464, 36517572443107462,
      61506034115773520, 38151430212840843, 62352928652298709, 36636315789483134,
      4373558875096598, 36664810314070917, 67138621717971505, 38403227184108678,
      54744643172203434, 38671502283271042, 141246610902106, 37902931860403585,
      69403181995951798, 34685745201581451, 61509968371025441, 37104730192232584,
      10283979124342737, 44772699771734151, 18154485390938348, 37489529934775674,
      52521272349329439, 40558211337309061, 2963929104615313, 35219035454522795,
      26044868790614939, 42869611641123717, 36167256028972979, 37923827330033552]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        23216710251296293, 40204148696348023, 12585308654306967, 40229440886320022,
        67420221460477345, 131]
    ) [
      64607945187439938, 36846347374369167, 6955349588870098, 37734740623039353,
      15343966122642790, 37685189152218501, 712739192670423, 51277395193607810,
      20976974688844856, 37523593000986758, 52210703542486201, 36342732427660675,
      1553156896555772, 36874882398444214, 4367339590419685, 35823969617869445,
      44617784598954324, 37261921497756537, 38421117428217289, 38153567294588544,
      12021718760654175, 36050235306138497, 24635269037651611, 34714340879080836,
      60084077731741318, 51113566065258892, 38700191335351263, 37780926888278907,
      18443468789613761, 33200275917160819, 54471071016193551, 34883605940012981,
      44348202189879797, 40426525644140422, 66569731654711211, 36961761333524085]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        9706787066328577, 34343831964692600, 11740561586292899, 34188727005197690,
        62921071072741804, 130]
    ) [
      71365419592103520, 40164564315232629, 22437147592066529, 41330047495792530,
      68826372271469828, 38414260874152835, 128241611339184, 51397237246547854,
      4072082244210767, 36950795072329364, 65460630414459808, 32803465415480710,
      44617471073815690, 38438403217404854, 6345545578877788, 34921273373163649,
      25211950116537700, 36750627216888698, 66573867769509486, 37477405996949407,
      53399137299038048, 39002535411037307, 31383323833566490, 36807782916561796,
      2400790209398881, 51240007368666234, 42924055656758223, 36222831872726916,
      42075860622279542, 38376811708299904, 425663513131344, 34453743516494006,
      40103104063962949, 34740951117393284, 6048522870750674, 36823222766391176]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        17595035704866064, 38100920844879230, 46079933202990441, 40107423649868668,
        32233461218710556, 129]
    ) [
      42914563624711654, 34426310821926518, 63531712490605519, 33278325522055545,
      7191795942133972, 33685218748893571, 39574844233119063, 51016803673810042,
      53327140818159965, 39983167781821298, 35054714412172126, 44026029017409165,
      11685049324108513, 32514259934666936, 70504136978886188, 39005966871795085,
      15318243305949853, 37050851369123221, 9158208338770091, 34888139059126898,
      19625056403492087, 39060637661804939, 40123595158360908, 38062398329393027,
      16768869008896280, 52142704352249981, 11104176340306004, 38914457074888596,
      26598310369985332, 41646849550522501, 8025256067366761, 35306986752826036,
      66575036420167821, 35285203450763143, 40137304729813894, 36654997555362965]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        35630900626044796, 32083154319264884, 38499384491209777, 36715452675818114,
        7180002093924928, 130]
    ) [
      14778310239434195, 37065136263524988, 42421565946757872, 37830326461923963,
      52215538786534743, 35854501352475264, 69665965185923704, 51473088818224507,
      71347122678233322, 35890741309723777, 61772086739959834, 34864966586159227,
      30821318797192370, 34013926416107191, 24324686775156618, 35484227923316861,
      37293976145329629, 35832505024839801, 70509539686201285, 30233789854511223,
      10335278288238644, 35265149896160132, 49952210927908898, 37904036325226366,
      66278133517481754, 51749057092545900, 13641372527920562, 33171638551259004,
      36176293575163354, 33412489764292502, 52773368938327777, 33117957299539639,
      53321716020509404, 37924044828926836, 71347328668441059, 34049076126330485])]
private def schedBlks8 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        50254864933883616, 42442861290979976, 69403100582942392, 38470306704937102,
        29156323447701506, 40290031802526872, 994669494635727, 42739754060304000,
        12542543905199164, 586674733965]
    ) [
      62930503586775040, 40004147756447377, 150553819581600, 41048733498336384,
      43221903278641325, 36029385035934092, 46327388138349508, 39567635583559568,
      40110186477882082, 41520401655456417, 62079025887547230, 44870519782694538,
      68560552574360246, 39079445793734544, 5802674763106521, 40820001943685787,
      59825323377528341, 43767829777875336, 43788735942661585, 38508791843288974,
      6082294765027329, 40306520584547479, 431878469618804, 42356057000272512,
      36467448752083815, 36030483960348556, 19025329046196896, 39568738903701907,
      2392543891393208, 41538002649515409, 49975713572294846, 40535145451142282,
      69968576032840013, 39025570613224080, 2690854993168567, 40912365668501912]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        36462835888984108, 39964525507641991, 16486784197562336, 38169040200263312,
        69117253064556544, 40667166555685519, 148904547028324, 40609971079175808,
        23803329687753249, 581490622861]
    ) [
      46605688918409219, 40419773402851479, 1275985569483943, 42585816929382784,
      71371149034099902, 36033780649722764, 61527268705012492, 39740265066443156,
      53058056868235913, 41947013256864394, 45472771075510836, 39023317046774922,
      53081907040915377, 38950805198290833, 48847657342830459, 41044315603214734,
      9441109281574753, 40075595912055175, 24086681640866599, 38048096202855823,
      35059287791206410, 40369201622582674, 3526617151802656, 41058572561991808,
      10853745604203618, 36042573118868621, 65180520542210662, 39716076599336595,
      51932187015285408, 41444514095440777, 48005891271725904, 38496651044157834,
      12264457632058057, 39043164980393107, 9156262537627516, 41362053575749771]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        56729699966685225, 38763867517485191, 62643105369721039, 38222921689122703,
        31678856399257600, 40434048682435723, 149334059159248, 39116832644597120,
        60956377263475740, 583537500302]
    ) [
      52791128845484032, 41061890693116301, 148908842913171, 39782031592337024,
      4380589925568872, 36029378895455374, 3247787871797436, 40008550903334545,
      2111064598153916, 40384564250072449, 62643801247093246, 36654968899859850,
      42377980800632693, 39128931350111889, 20974560836880249, 40916736937814406,
      36181816204300215, 37515915562057863, 52514279745031160, 38155850791899793,
      4367670510714880, 40866171583296652, 149153666207227, 39453241142628736,
      16484885768015124, 36029380153779598, 50819738868550765, 40088815587561356,
      27725287484197672, 39501657737968780, 14230496092655645, 39236622201899403,
      24923761999184930, 39201500778492301, 71927737849251784, 39832606477064070]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        48568278527085359, 39167355166654600, 5783734021426245, 38496704849032843,
        15071248546168832, 39159712792588944, 150485126843513, 40890336511223936,
        17604480566721681, 588235176332]
    ) [
      2690245168562176, 40316401022140810, 149480090668772, 38413158574090624,
      66866501371530947, 36029380690693006, 60382531063349602, 40227343147314061,
      40110186462415845, 39020025844399232, 1282947765407151, 36009555574391436,
      40964511192028210, 39445592460334477, 45739136107186189, 39707249517946511,
      7472566880865640, 39839151419293832, 16478945688782624, 38327379186043277,
      34776150467117056, 39684173195618183, 149793635798546, 38181144088247936,
      62079197601105727, 36029382485902477, 57851614095572996, 39869993848395398,
      51369185538116752, 37799594226840960, 42658223121205379, 36370195388333196,
      68826870383020861, 39575328456931465, 10837991341721748, 39181667625680267]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        7189240686872737, 37409278016880010, 66006554196542229, 38890320565973128,
        428279283613694, 38611011359418242, 1559367504005368, 36244877788964224,
        47438830868594375, 594006371464]
    ) [
      31960155154513920, 39157504138747536, 150691283241991, 40170158676674176,
      58699539408257280, 36029386059437195, 4377055064981023, 39291643249738373,
      53902460342537278, 37981028963111805, 10286320142748283, 35299271062934412,
      4934378576448873, 39414790716238986, 66565698813528426, 38703392600179597,
      36464094283270440, 39938098120884617, 48564035029403754, 38729797824315272,
      47159838233100288, 38364742431283079, 151387054311974, 37983202567984256,
      58977904751051974, 36028289232103817, 46028028546351607, 38735279477262468,
      17310704790637366, 37235534845918597, 71927355733934740, 38216275361132938,
      64039789972587454, 39065139055975552, 23231999942363654, 36055749457346692]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        24636153715853736, 38869402013682568, 54738359497621990, 38242689879573902,
        7751258597010699, 41880904162506113, 54755002702464791, 36116252041239984,
        3261308056599282, 579477005191]
    ) [
      17037141074739222, 38685817694059392, 16477678700628033, 38109660581653632,
      57008945865065466, 36169029438236551, 1843930598177468, 38081073968576647,
      67977282940012826, 38418642443316090, 56161737676853104, 34590093763834248,
      31113097625572151, 38402120256782990, 54741104143665770, 39723746772786063,
      25200890362233526, 40045839472989066, 69114826489497745, 38910100534322305,
      20140559699249130, 36535163857501063, 54195003421066717, 37768834206821515,
      69385984919374086, 40703412958356357, 64322764071205533, 37762190362863239,
      20149991700662098, 37312495459957115, 12814148820828642, 35153158372668039,
      40944389295476488, 37955719710292350, 40391588872423626, 34689002464522635]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        51940532379940807, 36638443697554820, 64602696914534399, 37366387568961398,
        6616570941388631, 33372954104319103, 31671181322458740, 35553259237724087,
        12796591085681450, 570199403158]
    ) [
      36183078863090552, 42465832856140415, 23228821751039707, 35656703845004725,
      37602406240320366, 51370858731843462, 46296893629434547, 37729291717472123,
      11178956007113834, 34966093336929161, 17879667922530916, 36331951086729092,
      24912212515456685, 37210243311539570, 69086343039255864, 32106326288664197,
      1271351198521050, 37557624479657349, 34183977729950556, 37398258120771990,
      59255947793774488, 42154730306756486, 34767397417878327, 37838062871876791,
      14236435851544770, 51614944307007878, 64322630737033177, 38865031127001223,
      1890376246789599, 37931517435160440, 35064798059725118, 33822864193138054,
      16472120888427311, 38025050531183488, 49671858198185137, 35993077730577282]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        36443070280923922, 36479007884568451, 19297350335168033, 37036468396390781,
        41236957965039597, 35782011377297275, 68261716866399248, 34352591567018423,
        24630514422611212, 565819682939]
    ) [
      47156445134763917, 33315808272198525, 48559594024244645, 35215752470050487,
      66276660652045804, 51733690942214804, 60087874718169966, 41674196950989428,
      28912644020340505, 32897908761230989, 4383845030400236, 40695914532441734,
      25743932923613865, 37354335704005265, 42098031277212591, 40995806059749776,
      17877047886115911, 39466484173899907, 49137000606628051, 36806706957624434,
      65171372251920384, 31543416432984440, 67134386833886784, 34101932679158455,
      45718112543736020, 51762276901700492, 2948514467574550, 39034232371272836,
      24690497885666346, 37573039063583605, 48282009914872213, 33257717951074426,
      5212666537935697, 34190986476758673, 31092641435452284, 40592329416973442]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        28575166811051445, 38375651249081986, 23518096833802945, 36659386373608340,
        1554397865753026, 41359839454195828, 56438007083270266, 33041988822835641,
        67151150342184429, 557817495170]
    ) [
      11961829522978806, 37219033329461110, 70795099093957377, 33143122082388151,
      64325873373182991, 51791961551508858, 68527661260044329, 34592339192021371,
      39890309834572182, 34917695497077880, 12801573370886960, 34076854868741507,
      10269835713937119, 37249783434671993, 7455619637347177, 33513650991258250,
      18723718719445092, 39720398345473155, 70496749199914524, 36905681625496217,
      26900357273204728, 43475170202971510, 56157541454478153, 33377405016100791,
      22968988939420136, 51599543258966395, 20115176849573408, 34710041898918790,
      37355433006106068, 39611514412419721, 45453010088790567, 38576050057422213,
      68278784998411925, 37530159520615819, 27423944775467655, 39669949722252171]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        43199671930353202, 40600023569798006, 24061388021724772, 33076030414348918,
        18173185662959731, 33359711108868983, 49104440379076390, 36789121045414362,
        31668724505019049, 559075707778]
    ) [
      69103981359707818, 40628667023002997, 57000501751677935, 33243185106246582,
      63770663196988227, 51487386747688323, 24336721347442228, 36938701821910924,
      41015157431108023, 38056803811841654, 5209574341250812, 33483119025764737,
      66854268911058156, 36141498563654797, 9982881499480140, 38383405522893436,
      57842774820290769, 33880866018716287, 65730177334474323, 35813838041041785,
      28560602581351183, 33497182694635126, 48834342913341138, 33336604638315963,
      38691970958588955, 53003597796696434, 63180624476601526, 31273915758097018,
      39614061718502539, 34257992362137469, 38400909433208339, 35629389663953787,
      11672980064467048, 34541616080742013, 26880747520096951, 35008962410980489])]
private def schedBlks9 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        38720391051121803, 36031597044996495, 25222979725725932, 40541820787393687,
        716776598244966, 43770015095228288, 1849552848590796, 39373023266848400,
        17333360851845122, 41147662968809371, 61236177204449242, 41684204005622667,
        35348193286003290, 39767744887900562, 35791]
    ) [
      170946899968000, 41998693827117466, 16201280503255898, 44335241732554892,
      11424873263110626, 40235052899192725, 10318034010934323, 42450598793624478,
      65743346043491612, 46562668178058126, 35068088415854286, 40866180979036310,
      46021161043398369, 42291173970108066, 10857877390136317, 36029398827063441,
      21560940368732147, 41413738507802774, 435507784880411, 43357727696456320,
      723274978072160, 39424702159065747, 40707548003991553, 41126769227895194,
      2690228213551739, 44632011943444876, 11421909708675827, 40171279983129746,
      22397543631653890, 41724916287605917, 49135888571732510, 41123384172215182,
      28032377961815051, 40651761866906516, 37576916033965733, 42582551228521105]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        29714162486974053, 36053569862573710, 19017546273164510, 40580312116616083,
        5215892225887891, 40550590657192832, 54206222106923801, 38231718386077584,
        68834816175144972, 41721607853619599, 66300068204089782, 39721567847974023,
        13955420644937706, 39234484986513300, 34811]
    ) [
      10858787833151492, 41278505255227801, 54197490308255768, 41476389043438731,
      40414420755585055, 39259770448805522, 30553265620224932, 42021791590738066,
      5222583875048005, 38139309698281355, 8048973108842878, 40048132298523286,
      6896169327168282, 42844217496614533, 27742501894854149, 36038187638545038,
      65466110148184312, 40519833306407063, 2965982202662358, 41559958857023616,
      25775969576326993, 38462615274231952, 18172550205833229, 41481922455975571,
      2123434208759871, 40417569412222856, 2697495391605405, 39181705475551892,
      57577839797569489, 42235084733016718, 11133412362195727, 39590665264814731,
      53363300347645120, 39992059789253526, 2955579729873685, 41643525196539788]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        34219020486676265, 36029381059799695, 60952065036424469, 41033294968460939,
        150210239303587, 39703953869467520, 41253910603139725, 38359263697945233,
        42374639360245760, 40509921561280653, 20138846366568791, 41046471910359176,
        45193263118978447, 39488478883412111, 34902]
    ) [
      46316925404938240, 41688619015056783, 70803650660176214, 39645698039218311,
      70812575647239795, 39333438885573779, 9725173905262616, 41487393236925066,
      22112057455055831, 39623650294913931, 17891083804248700, 40158090004509331,
      64317034466020089, 40377967297904780, 58707253314884374, 36029379835059086,
      25203939881356728, 41041004384578703, 149480089358082, 39116824810564224,
      35064733908307795, 38297689536799121, 28581996287393792, 41305973751487115,
      4938866898800875, 39044326684098696, 71934464006589357, 39423602194576530,
      13121290445555747, 40423048079981450, 65177900700373742, 44387834178067083,
      25487845814536607, 40320819084174991, 23221687866199012, 39753446438018203]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        55323879831932059, 36029385891737998, 13387746104414153, 39605011697432192,
        150854510481003, 40342769705339520, 35339487202475769, 38646242641580172,
        37866358113599488, 39629205650078094, 29147561708588089, 37683040792608905,
        66020826451053994, 39833714410909834, 35204]
    ) [
      16490507789500416, 40343893493644173, 28864841229701268, 43007989145141384,
      71931990075542708, 39565444714091662, 26327631980955745, 39585223491192474,
      50260744802700956, 38287743667173004, 53072732823395110, 40473640731289739,
      22658737915792592, 39807312543295111, 50823273807907335, 36029383693887887,
      18727885359253176, 40304304129221517, 150270386278298, 38121817504112000,
      68271501105990883, 38489010432081038, 12828532700250112, 39484067767142794,
      58701983319428820, 40991484484255880, 22392561661087725, 39746861129461132,
      66585571627141346, 39744633920633743, 20142179227438255, 41407058155205517,
      10561155218640460, 40270217440202636, 9429414018714971, 36849654399018644]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        17039022433994247, 36029393307149450, 57850355614777669, 38294409389151372,
        71647379755338200, 37891942901940607, 25491294587095400, 39119022272905095,
        26603240145190908, 39674270393541254, 2404432368731863, 36760550922780555,
        40133216053593594, 38982673938945420, 35602]
    ) [
      49967630285176832, 38696820545235340, 45754469359061916, 37807276043534473,
      52791459727182707, 39784233753591944, 43210298018007487, 39718267686312334,
      15354226945263746, 36793507365116813, 3816819365155721, 39611600965511050,
      68257684167036181, 40811131124822145, 15633288120141893, 36029390002126989,
      49125039535653181, 38967283594800274, 151919653849826, 38647363643942528,
      40966224972715107, 38922217056816521, 48574201073729536, 39294926216105353,
      28865025834388385, 40892487132250250, 51657992280639674, 39496155549913996,
      19844172689279622, 37831555359616144, 5782381225610700, 36097516521563276,
      12835606444281514, 39026657860698246, 4081393785015260, 41561014479358080]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        48285544983069001, 48736439558914181, 24629114480064939, 39070620004145041,
        45748451999122806, 35921686079196337, 35613956850881077, 38128340988947848,
        66586623958234345, 38209666866678399, 7465669013636369, 37723746717870983,
        28292223242174572, 37688535079390600, 34544]
    ) [
      33920369755914254, 39347757986992261, 7188841248229005, 36872692183349899,
      36753596460598486, 38873819637006986, 35609838002080543, 41323515991032709,
      29140608047548543, 36316325358545034, 32233907837963503, 38196518209297298,
      5491835283540626, 37729183506514815, 57571311482868075, 37452163618143626,
      52491022607023486, 38751734202239629, 32241273800919544, 35237787279847048,
      32788882207379699, 39134403590945674, 57302708415532315, 35342194396147329,
      51941236521601812, 41711602811206794, 27169527454336179, 38261386543597185,
      60933773054544466, 37143223600513683, 37302669483803242, 34487972276065159,
      26336337959949194, 37731441215500162, 2717372275984157, 40801237885739898]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        30556293572236082, 52393399478933130, 28574114751739879, 40724282641366409,
        12812374989441180, 36686882435193530, 26609558161099367, 37339980783281810,
        61507751903345213, 39572017674618240, 38988379485803114, 36727560678822276,
        55036065433616285, 37116747006654094, 33903]
    ) [
      52218472489466031, 37823809369300864, 3806429904928934, 37242180321523847,
      34779191318249697, 37754510306576003, 51107090291459590, 40612107590367876,
      17600563299779162, 41159919462060422, 63189536709576087, 38381170865548432,
      41018984319190543, 35485086263000978, 8293266167075174, 52485761089781897,
      44893568986091606, 33370721678910845, 26324020032866780, 36310895093471674,
      45736688284040484, 37578591684953209, 15636453318572611, 34903527658391427,
      30547656577351902, 39282780101292165, 68841739347723523, 37763325240984954,
      29407343550891345, 41509283812519562, 32241424162191992, 34077963222069893,
      38133891601631598, 39172905270716051, 33137208224351445, 37320197711364472]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        37880359592300552, 52902469251745144, 150686787860019, 41213535653423486,
        989291996674054, 37213520168083644, 60652297885548480, 37015600357669520,
        71071583193119757, 34173421638419584, 14775217774300958, 35629087174955651,
        60102778227556076, 35434470006656890, 33499]
    ) [
      44894088717646439, 40531863508923006, 25478057312225516, 36717731998499460,
      37859812553948633, 37314656666574224, 51393165183190091, 35836949696432260,
      4920793520902279, 42278123693425285, 60941533576791512, 34709956335771773,
      39611987373557154, 36192047409301654, 9998634731207978, 52647383829724539,
      41792207307577075, 37897478628035711, 13656267392318182, 34493356823775419,
      38154194023644901, 37253135352896392, 146027154946902, 39257579292877949,
      28015601276521413, 36898061854407812, 43224076239668899, 38420758184036745,
      23497764929373283, 40616499514389122, 31658708881409879, 33709633889915015,
      21248653104218543, 34055813723365264, 53686801359273568, 35336719167459958]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        57554642892454049, 52268047099889029, 988991362594401, 34452699604487556,
        31387545807193637, 36709935101647801, 29426970518258625, 36760515372298107,
        67128511161743663, 39158557630972544, 30820167896300742, 35019953639321986,
        40957244098379664, 35806180903139210, 33352]
    ) [
      44610431574064144, 35991983739261564, 34196793591433492, 34383433261910146,
      67415934982912377, 35388295752085638, 50825954644754963, 36143727331822715,
      47703718551850109, 41496375740969597, 48842279914144540, 35851208905138558,
      1895263864192414, 37261864623370388, 70503063104748844, 52787008753211524,
      4916618982495321, 34067886372540035, 20689920428967386, 33610504133186747,
      33934817833812446, 36859467828436088, 16485495728028419, 40259138973916023,
      34196630643898442, 39259802949042052, 33909035241928473, 35382859094581134,
      50549148272526354, 33585134900334213, 56160517645110759, 37836094435470717,
      29134710884237901, 37620310313096823, 47492255914032609, 36961742793752695]),
  (12,
    m1K32P56Cat (
      m1K32P56 [29137184893469615, 562733226371]
    ) [
      33350358630512825, 38846305723761534, 12243927560978838, 34819862001387394,
      31667904111082909, 36194314883560585, 20693756820685331, 36388881062229881,
      53632173807470805, 39366606098399873, 63470448966793405, 38979423940650880,
      55934520917459836, 35348731250968718, 32260893199794327, 51822740176785802,
      14209270010318834, 44880441844459133, 69385740170529279, 34492241440436663,
      5775178385226940, 36638565648110751, 45472337310496780, 36302026807479673,
      16503847908253345, 41481896990352002, 62628536590170215, 45125633996384630,
      54483673288770121, 36157972328934291, 49404118109745917, 40680524943087771,
      49957047257829979, 36926680156456832, 19101031718230110, 37048609413547652])]
private def schedBlks10 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        13386371828847566, 36030486309202573, 42955443694637240, 41060798765018263,
        21545362211245801, 43115766282715529, 71657219735985039, 39725970056406163,
        35606591152032606, 42928900343863182, 42381399712175314, 38635238046113167,
        25217804067241986, 41148766607698331, 22954596858695958, 39586266933181835,
        23812259065075566, 40408773320353429, 150875948092665]
    ) [
      23809239978180608, 41048699271658389, 48006299271663746, 47594010084738443,
      2133261220945353, 40260338277534611, 151185191570801, 42837651147376512,
      31403982995624996, 39298252466487440, 33394919062145403, 41362074078049438,
      27741741648351672, 36029387418343309, 52523076129956438, 40635276926951318,
      31678650354732783, 44996003207577737, 41821477780232990, 39779844951659665,
      52776560438774666, 42639723702797726, 62927578348426429, 38674821202922638,
      71670766097563649, 41166356193170330, 35339701977583710, 42111845125415307,
      32536084970446678, 40197668010629269, 432505546575165, 43464372992011904,
      33375871245326190, 39248773570809233, 15922824598358358, 42133935032648604]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        37031025790849957, 36048075760512397, 55889565763994705, 41036605214433939,
        20137398920580930, 40671501485085832, 35069578665168626, 39705082623787669,
        34762264981113568, 41090457912881540, 13108019351557980, 38119564324453264,
        20701504100139036, 41997582940074639, 44347300678308330, 38475760675540106,
        1566849420855780, 40353804064225428, 148835829648828]
    ) [
      5792457243262978, 41346679304702106, 19013633644335242, 39558779159262091,
      19308771076051252, 40232851913012118, 1276732904148145, 42759529532543872,
      23525492616042744, 39174004649412240, 63205458135255337, 42427510693484688,
      70243930577605379, 36034883583941004, 19868057275239703, 40770526369990552,
      8315617393151725, 40315298405942921, 15928305379480843, 39629212395590036,
      16466318502365925, 42765042123147404, 19864114565453444, 38580259746795663,
      45472427413504008, 41796380684458131, 34213394064249400, 38675871439587722,
      68565899764730998, 40522028537895829, 3528326544854313, 41401624820151680,
      6918181225338649, 38973896586678418, 51656836537813223, 42834315130610065]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        70809788238762470, 36029379684007053, 987063177347177, 41207022922560908,
        51381202952687909, 41274016123584647, 21545632768295663, 40039339326060177,
        49680335665990411, 39158587898074495, 9730710399519633, 38192133954231185,
        39851079547060224, 40568187960066957, 15074805067583955, 36446061690597771,
        34772938132001415, 40836487185404557, 149213795749514]
    ) [
      15912250576175139, 42222980290365840, 68554067067966072, 39683024509963658,
      24084521169028737, 40434071315514003, 8874804925664613, 40905702848195712,
      10859462202331369, 39134424814571667, 7474525144188831, 41302678219889028,
      24083687985484847, 36038175944800653, 7478300480015743, 41465417617799057,
      54758889776844833, 37134409991716999, 39285771927915960, 39799642066750611,
      20125463112354539, 40381266688028299, 36753957471883752, 38208625504517520,
      430113213939712, 41336764791413642, 60954251308077900, 37926004341586058,
      3814714904709451, 40802408549483665, 149192313441711, 37053039772959104,
      58426044624047309, 39092645587391122, 45178715889502122, 41927180170684812]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        6913289108687953, 36029381932224911, 35884673029602580, 39798525240112523,
        15916704523194183, 37608230397935752, 23226798936327749, 40271326732972684,
        12807113726463041, 39517041589660539, 40969308847637341, 38366961554359438,
        28015017182461952, 39674233098155403, 32526773266255109, 35409222225648524,
        47162926556940153, 39938164274332288, 149986910965452]
    ) [
      57579081088663552, 40527507606798226, 26896934476747093, 37114564760288907,
      66296318796729645, 40806798274319245, 149321172684463, 41873295225950848,
      64895510823535703, 39276267955086992, 67418692203349992, 40064571303083142,
      57861599973773026, 36029380439022734, 2703361997702405, 40583586760260228,
      66863151317618872, 36502157570080903, 37592940487087830, 40222955452482701,
      26880862557473725, 38502220643276676, 33371644866301606, 38293291876152208,
      49401308750643200, 39729266476822669, 61237298234822394, 36613187458045323,
      48847296763233009, 40559397554673038, 149664777735946, 38901286539616384,
      8598758844435156, 39402713201499790, 12804613916887079, 38552773985820036]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        25485801407153553, 36024989036362380, 24350508416269676, 39401585050025094,
        35339010441513689, 39778663952022665, 48836589316570267, 39344418985878923,
        62909642423372937, 37813821155219320, 64048697945720232, 38757288400088969,
        37031828506378236, 41310342890319986, 18448798102620889, 34256933972724620,
        49125511382537583, 38597844316380555, 151614695705308]
    ) [
      31672843330879488, 40050281040293516, 46037254309252229, 36307523242326412,
      71370358684025814, 39742451355694214, 431603624545906, 39776484960876160,
      61799109880744938, 39630308450820235, 26601719613917341, 38318571617572734,
      70523339566581772, 36029384113314189, 38720631239967316, 39066224290170760,
      56168429328567423, 36205278860935048, 63480967534513423, 39820516781624708,
      20406933812907239, 38132757590933890, 37307028744472275, 38553880896552332,
      63760900519067646, 36963955826436488, 63768412586740408, 36427369942684300,
      64887573613873234, 39329028456526211, 71363997837397203, 37798503572853375,
      25196230248990382, 39630301471406731, 11961262728317256, 35868845952777355]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        31394181872513515, 36237200719449735, 14493571352788339, 41246475284267908,
        56445841155131403, 39687391182670986, 3817665513488158, 37973312836632182,
        47712463306983642, 36830901498148471, 62929970241704528, 39048642556255877,
        71092194770125759, 36644059850536580, 27169978193252988, 33269598888043912,
        71926771575263945, 36915632293812628, 152301825853211]
    ) [
      24371794000969725, 41060765612853375, 64610440872166735, 35304768570784907,
      51103945454358617, 38550549310737804, 71646460637645525, 37299323632768895,
      44347219023203998, 39281747896636036, 43486713523243562, 39532467266555266,
      12535813455317637, 36032689358988682, 35048219219951447, 37044225829511563,
      24922872895998322, 35762163847006346, 27738176644875159, 38689106649396354,
      60094931325127426, 37285001376865151, 49966814009985852, 38989278357299337,
      71924641177239566, 32685777691608705, 37023582474241717, 36030446782027914,
      1552323603368108, 38722098993189514, 16196543035508819, 35954622573043328,
      11383881896920009, 38816642549501842, 71916081314892474, 39691836742073482]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        8889119761011054, 51931607665543045, 37569610278732680, 34288896715273850,
        25760765083423794, 39581881942440581, 40374056159376011, 36878254182392722,
        54245890154202529, 35279434119440500, 66846697374578790, 37453240379623570,
        32248386082945073, 41801782376045951, 39552424995359725, 35108196809246086,
        70516549095952949, 40550611679565702, 146258787535276]
    ) [
      21835589951392168, 39921709315234693, 7467116391404041, 33816092506477960,
      6075504049886049, 37526949854333589, 64891056834774916, 37169619059456404,
      12830061943166529, 37995306725876611, 5483215568931257, 40729851602360463,
      63483432678168054, 46089918006851463, 6899012508941284, 34937624666809237,
      53064752720089801, 31383895746974088, 30274200475369944, 38274635761665940,
      23555952282535364, 39669834177835901, 53052254550985810, 38153626568873620,
      8864659993572316, 41090440580841856, 10563573348989528, 35638153780329093,
      14489615470723794, 41955688855987078, 46028260503881463, 35393855838700471,
      59269429869312479, 37413658398353017, 66005790641128962, 34650533482199176]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        9141921885683180, 51782067893067154, 45169748255212948, 40374625343040640,
        7457650499156904, 41550028526317700, 69667914939791585, 40387799266909317,
        59311954385534287, 35279444739580554, 22677708793938803, 37166226103727232,
        21835023239133154, 39167375652266102, 66300772532523534, 35611772480386683,
        40409038592774722, 40361502725422221, 144970115025456]
    ) [
      64618674094847992, 42608880903962243, 45760254671556972, 34307751790577799,
      57022826996601378, 37215792812067985, 67700266101019755, 36716616762323127,
      19873310089845048, 38429673276247696, 17302506471785731, 41951427056219536,
      18706015202286528, 51797464311180182, 22659867574958238, 40043780305585817,
      59541293063763350, 37423497835188100, 58985322462019684, 42338303400045717,
      63815734410446830, 42399916180264313, 17606447623277633, 37259730209863543,
      12228461150976013, 35198157668484735, 45200104692813036, 35057619056221829,
      33091269145293934, 34003003643784327, 71359152965653591, 35458661442742967,
      57274877191490487, 36642957100162701, 27729046389097596, 37157473445830012]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        2389167990931090, 52243860294787194, 57835773983360035, 38726440803538821,
        29150434724969039, 37254231496356995, 26601573737724287, 34870446261034368,
        31728153976278881, 42215172576124553, 63769404737421812, 36821057650121599,
        20980775909569995, 41303714079228282, 50805767365562064, 36484777917970061,
        33378830032079566, 39546750047075982, 143029068989258]
    ) [
      6071110161643536, 39961273967073413, 42370687974740725, 34638706770164093,
      31973199044317404, 39384037878332563, 61224786732549481, 36154758988935096,
      24646500535145932, 37545585314253970, 16457926946096015, 42527552694063246,
      24075639181643945, 52281243471607680, 41515650145417014, 40279034203473811,
      45755409710417656, 37843499231072131, 24368792166104498, 34320728111964050,
      67195147808116879, 39836943738839413, 17037540735684433, 37103645442520963,
      58670724132027547, 41860106203868281, 71909140659012401, 33932837703114129,
      25201173620026718, 35761068866379656, 35610817544222999, 34160087576504764,
      39549315236202137, 40947434175441281, 13653047064888261, 37112389777836140]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        5209883445138340, 51685281090627977, 5200232461926727, 35831518894345348,
        49123385784369425, 34659370297398908, 39253507898505565, 37860031747066762,
        23281825791640879, 36289901695959173, 14198352219763722, 34712152187405694,
        64330116911642227, 33713720819406712, 13373705616518289, 36931251126046084,
        5210712358486830, 36828704336446339, 143058963301045]
    ) [
      25767271853242075, 41602851890633852, 151696374665057, 34792634002289036,
      41823586197408559, 41111354975956372, 60096327201888266, 36004104135890103,
      64619984508000045, 38950850127817870, 49108590434025699, 42615522214228617,
      14794588470612838, 51951376762774164, 41233762785916420, 39895312513935507,
      6624495576517985, 37103517939846272, 14522897484053676, 40456028597055635,
      27787860726941774, 40264647202167666, 9161094696372910, 35830368348023689,
      3224105019685093, 41408159361554555, 13665643312220869, 32853101379510407,
      26328761465533263, 37588493917169787, 31945694129654681, 34380031979109560,
      9450630882690992, 37787510637852295, 56715742018305525, 33501594246569590])]
private def schedBlks11G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        67701412843129013, 43672133057879940, 34783198884436281, 38553871283173007,
        47997069239158663, 43182881472868479, 10291500031579613, 38247101633330829,
        17310386890245797, 42240597441439888, 21547763155899315, 38000806263885963,
        49415567978628595, 41579777195864727, 55041077727105305, 37762207895279497,
        19024250787102661, 40967338464806041, 28580613108895324, 35977696043805064,
        53085424621489541, 40181179698376598, 8312795553696783, 8782215]
    ) [
      5235211503239054, 39695179502848915, 13945537816398915, 35891955779707531,
      68560522593020025, 39319139345356431, 63202967236021033, 46790264752907146,
      48853722178427982, 39006872154152333, 2122669647039050, 44137297695699083,
      38155723099969159, 38901316705801612, 31396191778998809, 42660626922769535,
      34494851849360020, 38769372693172363, 48835318069496262, 41535803156692381,
      29989796196749226, 38552765261783434, 38450993209182465, 40642986225700509,
      12536857260232069, 38197617905659529, 25505713090822022, 39951378261819032,
      57289836638604218, 35902930477843591, 29159785439008348, 39401610888204437,
      25200138786081314, 41789686406277766, 35911701597035544, 38943105496312978]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        10563856627239978, 39898565715166086, 4386392471081358, 39514863236601235,
        428992202508763, 40803483733489536, 67152894215754892, 38838653032540560,
        15903334140577769, 41651220234701192, 14514659765425477, 38278991027423631,
        51940918558426679, 41968991913110156, 70526182933042043, 37779803973764748,
        33368445014015989, 41544586800321679, 32806298343674162, 36011781290207370,
        20704970238494609, 40900267852733074, 16759462975868721, 8796040]
    ) [
      33377047918510043, 41137764058983832, 39277023010000678, 35997486548461192,
      5515036831550523, 40403282204834199, 18446165304577197, 39316886164734087,
      28313706853012062, 39689689242939796, 3807993314708133, 40972799145144198,
      17333326606997128, 39078349654471570, 69390284180064499, 42158096940450431,
      33656431378798366, 38580261038691472, 25473466167691126, 42494565433749642,
      62083535677527272, 38144846632531085, 42935901147399716, 41960210164892815,
      30555593772602000, 37755612570408331, 38437898023960579, 41286202977316499,
      33649086878683318, 36033771136852873, 2694720708249936, 40730939287228566,
      50535309106712233, 38568119182434695, 27467546671025700, 40216358986903445]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        24357590807842226, 38781450778027910, 8602589944712137, 39895298420645010,
        46309632472288179, 39289440098980223, 4945360898461064, 39319144781322386,
        71634975805507905, 39768834735438213, 13108384361189192, 38649533140162960,
        24072623820277352, 40237233903185545, 66586718683762961, 37839183121461389,
        70519589969756060, 40730921335053194, 51947507312988613, 35920522865372043,
        46314481487939020, 40981617317925772, 33649207131541615, 8814217]
    ) [
      47723067524153320, 41581967511240590, 58139325421687140, 35996388093872778,
      14793110955132714, 40942049395202193, 23515171657191238, 38000770528194440,
      31684311130606431, 40343905825436051, 14223714246495617, 39167382463174022,
      46042073308302737, 39832623590256019, 58131409683385131, 39765534254218879,
      56457218716110807, 39204794296923281, 45176486905809037, 40377971123075206,
      39003944812843556, 38460415932202127, 37021125586028092, 41012398257913738,
      37031146050523961, 37789702430621581, 35617921227784122, 41378545008557708,
      42095436440637963, 35944711349394827, 30834981284709971, 41121265629583758,
      71085237293387724, 37784165898669704, 31681463535766005, 40503337393747088]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        53913116207648464, 38081058129831302, 7190700997970177, 40211956796134797,
        67702164502973534, 38521970228541311, 22391436384766591, 39531355239847054,
        11118233776392639, 38937592435504517, 26051873818643340, 38783677149144463,
        57285756250588871, 39232267876864390, 64333677555387516, 37938141181286030,
        30547338649501707, 39486259576048520, 48007828277267846, 36052465686798732,
        65733497469240572, 39764439708932233, 67145794524909224, 8834697]
    ) [
      42090303787532191, 40527509167304586, 59828965576905061, 35924921230656139,
      16477721635095985, 40862867042191756, 38715859794301061, 37617040047379081,
      39841940022724765, 40682552688594829, 43779858125786702, 38410912960326534,
      71368546191051277, 40077819582130574, 49969112118299633, 38813345876642943,
      27741428060097454, 39403810095923088, 36732173187451276, 39271848382833797,
      32246586782485723, 38717704471743888, 70515492468459182, 39589614256232327,
      45476194179452443, 37912851289741966, 31674522758053831, 39923870472025225,
      10852950985379711, 35975499520514956, 2121269443265888, 40303206748407179,
      46879003495338012, 37527980494731913, 6345112106141558, 40520915687920268]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        7189219275410782, 37531298490761095, 28017130521855635, 39733653198807690,
        17600035275377944, 37846861985625472, 70239287577315388, 39701771237185162,
        68820874591832753, 38307562139229315, 46314541635569976, 39060756142800011,
        69950601197356855, 38596740542512004, 37589508856777208, 38074484985227660,
        6619972738318380, 38790259186058118, 58982539104586381, 36071159666239884,
        41242627549463377, 38956288109503623, 69679043499821851, 8871562]
    ) [
      8029026978267165, 39380705285359752, 58703752829897992, 36070058023844236,
      46874321837589727, 39633596315259017, 1843745954434599, 37380647329127050,
      47438998394078739, 39941463228520074, 63765169900129936, 37701724219126662,
      31114527808456600, 40093200379831179, 15910940594048256, 38119543352370560,
      13663933966813500, 39701777042204300, 40954864778447413, 38587941513441668,
      11131458053507621, 38920019090744461, 42929901082216184, 38837537900796293,
      68834829018499825, 37998616501887117, 68826702817361985, 39065140582731398,
      10288965885135781, 36100845205088397, 48561943324558458, 39257558607310728,
      34776605973908601, 37284990169845898, 39838087378077032, 39479662791525001]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        997426884020787, 37040905953202056, 37022182247466152, 38854032605367688,
        56444630041594605, 37304795404559231, 47437843040208259, 39053046189737096,
        58405793664043789, 37537895762065281, 8312890015188775, 39122318358329737,
        29416048470100032, 37990897891431555, 41245934736869463, 38373552433029513,
        16469969100177342, 38351544416276100, 14506314466953301, 35957914632639114,
        65165994796810653, 38357047896871556, 52224627073583270, 8945290]
    ) [
      58974022048383005, 38692401627750789, 43500951523461696, 36053567866078604,
      13939258451591945, 38870524742904199, 4939532561124042, 36849582692857483,
      39554958820017234, 39022260132586888, 37026180973824888, 37212433240032391,
      1557400353801589, 39203681849691529, 71080770485652525, 37534595733955711,
      47719807660164785, 39407094084554377, 37576851537300271, 37865553683283330,
      10847268619126837, 39180597927273866, 64882625682769851, 38303164109496707,
      51380172081301694, 38222920598399114, 989360787455971, 38472495678238085,
      34210795509942594, 35987599114580619, 71922240353763886, 38593444910188677,
      13101005488949686, 36612087208210315, 45464619057644458, 38720989701902215]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        10002603161257876, 36759427755278217, 15908406452912886, 38116253759953798,
        2121153504512014, 36829802103125632, 49968416248529784, 38240495839209351,
        15058982275549433, 36978237062149761, 66295627072439386, 38503280795918983,
        28852527291926847, 37221231480710018, 5215986648450466, 38639624364977543,
        38423900584640550, 37566481738969986, 12814930560255777, 36083262749699207,
        8306172583379263, 37976604592570499, 15910931955222472, 8998280]
    ) [
      1551679368429503, 38291069565452676, 60949324841781308, 35960114343746953,
      44055143908409731, 38342753255828612, 35898691871934552, 36441662654293386,
      70514393025119008, 38337257006417797, 52225005034834114, 36891369972680840,
      44338671898756020, 38447207498136199, 57852778004580690, 37042009860562815,
      16192991020024887, 38604439154062472, 24347394508098072, 37181649984876161,
      63763108220274024, 38830940931767687, 62348139710613740, 37500510437336194,
      4652967989970701, 38558265604885640, 20410008881954787, 37957911905034115,
      44903941193435177, 36006295845315464, 55313322630349119, 38310861965944707,
      34489968348661726, 36376792273589897, 54187968190055082, 38249295119806340]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        57567828346439334, 36587907333686662, 58127861938618769, 37878753174821251,
        60382810025002687, 36460363847441332, 67980280700895836, 37863360129556100,
        13991382193440288, 36682463115869314, 16753024657097430, 37735816294200198,
        143253084865909, 36810009870432386, 28294937533711229, 37539002001543302,
        33638499582719327, 36987033104827521, 17599154728633470, 51084982168710790,
        18156744497726079, 37254216980540546, 61509079302571469, 8729221]
    ) [
      23224127288999993, 37471922732336770, 47436709174871735, 36101954548006022,
      67978657190871378, 37868851110856834, 52502163537889165, 36414177078235783,
      48839067443429920, 38109650130097539, 23792823992158141, 36614293008961417,
      49402786207203845, 38218505438770052, 24357857019135519, 36572514268313216,
      2679000941429430, 37757812163941510, 38984694600599223, 36774823636107905,
      70234468541498208, 37776498492930950, 71918649705138520, 36954047185537665,
      13659102051337286, 38663800534533255, 52215792199633719, 37198141400975745,
      29140285918053776, 44217448580586631, 35045462142255569, 37552187718705282,
      8593102243923637, 36567193173367173, 4084077986415099, 37886444471315587]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        25760593311729041, 36703360349792132, 47712604897313208, 37565382596441218,
        32796548598367608, 36521938360925878, 8587849424405041, 37547795259069315,
        71132348631450881, 36645081045955202, 68542509094044238, 37422450866468739,
        36172818924536872, 36676968594399874, 8026273871790731, 37180556462867077,
        66008637309302412, 36730844915838593, 13657027548971755, 51385143474312837,
        8868547014394578, 36823204513329538, 56441361466688412, 8648580]
    ) [
      33357089033663902, 36938654190550401, 8591843799761977, 51160847766373766,
      17593811725615791, 37182748036864386, 49124051476514173, 36814629443536773,
      40957089480344118, 37533495769372802, 68263847378585121, 36665976383993220,
      2395331216114058, 37739109661531523, 3242307411936752, 36469161265917878,
      53624236543017535, 37684137553102979, 70006032122348920, 36656075189145474,
      62913640925397620, 37551095857671044, 22943490718532790, 36708854448362626,
      60381568736461521, 37331191485284485, 42364520222733887, 36813308891902849,
      49123707852325746, 51313677315686533, 15342179418735353, 36979336674436738,
      12813285550818423, 36877303720209797, 28009206194864736, 37252017856624770]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        36174201064555406, 36629686796040579, 54185764848304644, 36983733529738881,
        8025857279886434, 36582409923288758, 63192951216505235, 37225629191657089,
        13429420047238174, 36444970399429249, 13371987712442743, 37162960837345666,
        66288554066871152, 36435072815067009, 61223111713063297, 36991436234943874,
        71074559792887206, 36454864041113985, 54186907315765679, 51068481491419523,
        34482907325038832, 36495546172667265, 38425227751817718, 8612739]
    ) [
      63756747297765009, 36683565328633729, 3523636325286586, 51390640529128325,
      705772688540317, 36771526795727234, 49404341015642977, 36740965251406724,
      2394721325187681, 36954047084901250, 57848203775345787, 36702258422257539,
      12246379870716406, 37258614540502146, 42084634411238622, 36593406516027062,
      33357131973362166, 37383963362402178, 19059546650870920, 36572514251595650,
      2395172299506164, 37289407543517315, 24068450033042344, 36563717537794434,
      71638600689811973, 37046414047753091, 1269139246790262, 36575811930805122,
      45743912157938235, 51341161046236548, 55593517698351573, 36632986703218049,
      21819325131489972, 36508967190628484, 52215508736836144, 36761630452863361])]
private def schedBlks11G1 : List (ℕ × ℕ) := [
  (8,
    m1K32P56 [
      1831676864279855, 36444968352576898, 22098424960745884, 50912350873796995,
      28290419180863667, 36461460943102081, 65727729256333765, 36215389197398146,
      11119775588057558, 36488949337772417, 21535432071283235, 36442764802799235,
      16467409291477457, 36576909932451201, 60942972476359222, 36536227834386355,
      13652732534161643, 36606597853698945, 58180724411892143, 36225066798757759,
      10274916850434217, 36447168533464193, 57561059960718183, 36099717205134208,
      60095545338527848, 36497741991434880, 50243779396797409, 36032645334827136,
      4644425163964429, 550955398016])]
private def schedBlks11 : List (ℕ × ℕ) :=
  List.append schedBlks11G0 (schedBlks11G1)
private def schedBlks12G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        62088835707207658, 39583029669108113, 16477352302381959, 37629166904428169,
        69407296756416510, 39661095296671377, 15914389463796614, 37631365877352329,
        70532968980250648, 39673190193015953, 15069951648566175, 37629166786987145,
        67717768195440684, 39684185644843153, 14788459491855309, 37625868252103817,
        58428376688197700, 39729265990688401, 14506971630111781, 37622569717219209,
        43509425521721434, 39795236923239313, 14506975924816999, 37625868201770121,
        61804504429985906, 39860108042164113, 13944013086362778, 37623669144960649]
    ) [
      6912456145928092, 39510456415390606, 16477356598528936, 37623669614727561,
      6352735991660441, 39507157729512078, 16477356598528934, 37625868621205897,
      44353472738459548, 39499461114561166, 17040302256655266, 37623669631504009,
      39850173741498272, 39492863893804943, 16477373778070430, 37628067577351305,
      5229653532442536, 39487366268627856, 17603269389945755, 37623669530840457,
      71939648198246316, 39481870405021840, 17884740071558040, 37629167038646665,
      66873184501071798, 39475275717631889, 17603269389749140, 37628067476687497,
      42666383734505416, 39457683951035025, 17040293666327440, 37624768941803657,
      47170309766610904, 39503864144046225, 17040302255868810, 37625868419877001]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        1562038947512712, 39954667669616017, 5781367613590454, 37606076640141449,
        34212328792293794, 39818328630424720, 5781260232789050, 37603877566554249,
        68833274186990014, 39845816723106703, 4373777975643223, 37603877600107657,
        32804159341101530, 39924981728075407, 1840464536439894, 37600579048446601,
        997297994433018, 39956867582052239, 70239055688404084, 37598379958081672,
        48003400061256210, 39943673509620878, 68832071644515489, 37599479419377288,
        26611052721963563, 39909588766591630, 71365617014705355, 37595081322534280]
    ) [
      64618455326621839, 39916182547962258, 12255141751262396, 37621470054595977,
      60114198563225771, 39901886715779218, 11973658186910938, 37621470021040265,
      52795290816250052, 39806229120294290, 10284808330513628, 37619271014561673,
      48291231620301022, 39619314525952914, 10566296197434561, 37618171469378953,
      40128216769528060, 39636907248881298, 9158964265520144, 37617071890641033,
      28306138891256087, 39665494819648146, 8033133076253670, 37611574298947209,
      12543381274722615, 39702878282108306, 8314706832755749, 37609375258913161,
      64051717165056338, 39742461287915665, 7470329146936338, 37608275730507913,
      35902978245296494, 39850213762985105, 6625874150656990, 37607176185324425]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        67987556400071414, 40094307357404041, 38151470975519743, 37571991477674889,
        57009787491615498, 40126192070511497, 41810473873673265, 37567593481504393,
        38432043893097242, 40165773365016969, 40965963043802290, 37565394626030217,
        12817352867152680, 40202056107864457, 36462324761660742, 37563195669890953,
        49127036466791220, 40206453097395080, 31677177145494895, 37562096191820937,
        37022963950191425, 40192158456364937, 23514342692064710, 37560996529198729,
        46310946719433548, 40170167284274058, 15632991803772382, 37559896866574217]
    ) [
      9440782787445313, 39856812325889166, 8315136336235746, 37595081305756297,
      70802031353168473, 39747961094157965, 15351804597538011, 37592882248946313,
      64327874955281009, 39755658396959629, 17884795921075386, 37588484118549129,
      61512966268027524, 39954671142422669, 13662284723424383, 37582986543633033,
      63483359816483481, 39909592205854861, 152108609997938, 37580787520375433,
      12255060075119278, 39909592541381517, 69958203480247380, 37579687991967368,
      48284063242945222, 39973363796342155, 8878039042853919, 37578588430002313,
      71083716735566552, 40152583302449034, 17603926527609853, 37575289928669833,
      29706972459860712, 40175672157411722, 28018496369167346, 37573090938968201]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        24071576031822722, 39689671894732423, 8596907676306730, 37216847896494473,
        70515995152712579, 39818313144565382, 19293004034903300, 37140981241856905,
        45184445536437127, 39931561516827526, 25485444932209888, 37090403388214409,
        20978920381907845, 40006327250557574, 29426047361715386, 37064014807162505,
        68831002150863753, 39915067047265925, 33648081817996435, 37088203995869321,
        44062363835270022, 39846896772709253, 34211006000958556, 37139881075932553,
        19293527951311745, 39722651589686149, 33085149042478174, 37205851857489033]
    ) [
      4370432193495889, 40142678721820811, 8596044368874769, 37555498652285833,
      34487511699456859, 40104195043095179, 10003290414222632, 37553299578691977,
      65449041897751393, 40056915405565067, 13099485101329771, 37546702391479177,
      26323324357739377, 39997541207236236, 15914462498033041, 37537905996465033,
      52781418114220918, 39926072531979148, 2966733828361626, 37520313156112521,
      6900597471216503, 39853504529637004, 64609882578521495, 37489526411105416,
      3804153674040189, 39783135701541002, 62639695183187336, 37449944009278600,
      57847516695200641, 39721562798697096, 66299007321673067, 37383973596817288,
      65166278396183426, 39689675183083655, 152520938523980, 37305908355125897]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        65729769367962372, 39209182813273733, 41810997883865979, 37291614435559817,
        21537321845097190, 39216876961882500, 38714876217953093, 37283918021939593,
        6336917185594062, 39222370325661315, 38152042226944800, 37283918206488969,
        33639349976597180, 39227862380851330, 37589195350706949, 37283918424592521,
        58127243457954484, 39205868188901509, 38996651836934895, 37292714769271177,
        11965050930102951, 39095915298106504, 41248524663687897, 37307008420430985,
        58126788203217557, 38878211928738441, 44344809535474369, 37325700034216073]
    ) [
      67144789381907330, 39311434291246724, 29144653985385846, 37275121241035657,
      53071104964658047, 39201483212374148, 30552127653252500, 37337793571591817,
      50256084607730548, 39206978891485572, 34211315236244828, 37379575147665033,
      71366003478725486, 39210270061194884, 40122190964559167, 37385072772913801,
      40121241671992168, 39205876527773573, 45188650353003842, 37345490438197641,
      9720780240356187, 39200383398819462, 49129231309507901, 37307007581556873,
      44059494731121485, 39198183234679174, 49692155495157020, 37294912903324041,
      49406359634740021, 39199281538177670, 48003322816466048, 37297111909806729,
      32798223600419617, 39203680758942598, 45188615999818734, 37297111909809545]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        42087224293622252, 38708881317673355, 17322872443079147, 37357585653326986,
        5213731763945946, 38748456572371339, 18730127065975271, 37361983699840906,
        42086584346968516, 38774839600081290, 19292973938805186, 37358685181738890,
        8027631128445362, 38791330395331466, 20700237151963506, 37341093029251978,
        43492988563390880, 38795727988716681, 20700129776339209, 37343292102842250,
        2397173804794258, 38791331133242761, 19574126788774068, 37344391698359178,
        29418350652588419, 38783637353497224, 19292570206308471, 37349889373941386]
    ) [
      25475733860745857, 38347147879669899, 48285532221508261, 37331197693016713,
      23787103049581174, 38232798569818509, 52789174795274883, 37338894274410377,
      31105800341914212, 38331754364775311, 57292800189041243, 37344391832548233,
      11403093142897234, 38431809486740113, 62922295424617011, 37347690317100425,
      17877726281564738, 38631920049408401, 67707335666141713, 37352088296503945,
      17034052975297071, 38735273521742992, 2123618845362676, 37353187808132746,
      62070835231883806, 38505474853461389, 6345657594382819, 37353187724248458,
      59819636717617680, 38551653436084108, 10567692048828893, 37352088179069066,
      11406340159341051, 38644011372884620, 13663805121595872, 37353187640367754]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        63758697141076203, 37849075991103871, 66579378435492087, 37371880848029577,
        18161344352846044, 37537915609719682, 63201541275617554, 37376279045536905,
        22384731730510033, 37232254095100804, 58979274889005353, 37383975727595145,
        61792001571651783, 36962878460690565, 54757004206836029, 37388373874770313,
        63481263755919541, 36817747958996358, 49971744916539715, 37392771988391049,
        52785455165767849, 36770470972288135, 46312385532692801, 37397170118788745,
        30830488592875680, 36832041845095048, 40682697016248628, 37400468787890569]
    ) [
      39269601162527087, 38766048506008711, 17322146584234049, 37352088497862794,
      25758462964105570, 38741862672662918, 15914690096039970, 37352088632083594,
      60661033644032338, 38712180036172420, 14788712880244755, 37352088749526154,
      32513205244690754, 38670407284869762, 11410935852599329, 37354287890224266,
      44053339972337971, 38613235767198335, 8596125944481857, 37355387519294858,
      67978377971400990, 38541767763022716, 7188682327427176, 37358686221951882,
      51371045096882451, 38442811649391995, 4936770847344784, 37361984874277002,
      9712920336367878, 38295477074474876, 1277463005989044, 37365283543379082,
      37016761874481403, 38105261730626685, 69957228475025623, 37369681724109961]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        50807803124809831, 37752327339907465, 43215194412712094, 37454346233372296,
        25193305347883106, 37651175910744713, 35052342781509663, 37460943470907784,
        18156143142010974, 37518139382582154, 26608041943596990, 37463142628377992,
        42925661884940382, 37344421242970509, 17600834101936008, 37469739815581320,
        14496410028114014, 37420273334950027, 8030538867900306, 37477436480856968,
        61221045680636000, 37355389314310280, 71080736085409758, 37484033634505863,
        31666039967285341, 36962859200428168, 63480654019002495, 37491730350112903]
    ) [
      4652791777951898, 37101419039884169, 33364240243394829, 37404866935065481,
      56724296674410640, 37369697561970569, 26608806439061709, 37411464139049865,
      44337318939099275, 37623683305361546, 18727498498082933, 37415862353333129,
      66009698148253827, 37764420089189003, 11409114742425573, 37420260517284233,
      33357862117605500, 37847982452817806, 3527750969427529, 37425758226416265,
      4928481449640056, 37895261234645393, 68829859667084333, 37429056895516808,
      8587359794331762, 37895261284876943, 63200265644835623, 37434554604649096,
      61785851217346666, 37871072414842508, 56726233808208431, 37442251353813640,
      53341331328106602, 37824893647801226, 49407768451776845, 37448848541018760]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        53908133816467616, 39942536970002316, 69954032898182497, 37587387811351174,
        49120963272016043, 39372992681520524, 65732015616920749, 37597283365663622,
        25474668639977658, 38970572566613132, 64324743808453550, 37607178903198598,
        40391579688009924, 38713287164468619, 65732217473370665, 37617074423956102,
        37576555045159123, 38515375172108170, 63480499263211469, 37625870416308102,
        30821155605479650, 38347149859475337, 56725155657778282, 37636865415138182,
        27443434411294960, 38207511815607176, 45747661634961227, 37647860413968518]
    ) [
      30540410652557411, 36581326518083208, 59539759533818384, 37500526493461639,
      36170563036610663, 36366920106479496, 56443332925490202, 37510422114883207,
      46586206641553518, 36363620481059720, 55317244036089500, 37519218241454471,
      63194570314580079, 36658282752187272, 55880082279795228, 37530213357727879,
      9433992239022200, 37004625593040009, 55598529958022223, 37539009484299911,
      37582430520246401, 37413643683688585, 53346704345369936, 37548905072167815,
      21820347229831301, 38107436443572363, 38991523481161141, 37559900138109831,
      15065209789317259, 39440048495881100, 21540139345874392, 37566497157541255,
      38427637157757076, 40785856600333708, 4933210204114376, 37576392711855239]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        39827706164445614, 38867196612448902, 47430159470394157, 37746814061287301,
        11398716363276744, 38955157509056647, 50244462555135008, 37757808925903493,
        37012922098876894, 39058512256291207, 53340326514490685, 37766604800812165,
        56434734165950972, 39193753511713159, 56999312222224033, 37775400658934405,
        2674890527834641, 39358682168350857, 58406639839445064, 37781997426699397,
        24914329980273196, 39548900146219402, 60939991901569654, 37790793234500485,
        37584401905451589, 39778701532913546, 62910595837625824, 37800688503600005]
    ) [
      35043207243333889, 38100858969577863, 32236841289153627, 37657755834061446,
      49679828722811151, 38011798276038534, 17881540185782888, 37665452214121862,
      71071845348114721, 37944727747946885, 4652078868953454, 37676447145842310,
      27161680264331576, 37918338965533573, 65731874000501023, 37689641016933253,
      57560904735818057, 38111852273793924, 57005758941985031, 37701735409952389,
      17872860003926362, 38550556289172356, 49968390658881824, 37712730257791365,
      41516702180606321, 38637412792008835, 46590003746011506, 37722625560450181,
      5487840677298568, 38717670849343364, 44899586222094816, 37733620408291461,
      37857415680000412, 38795729329770885, 44615980938590826, 37738018169590149])]
private def schedBlks12G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        60938101913388006, 39485156255779206, 59546953336785977, 37862256389917316,
        56997825901397061, 38735288604156549, 36465872103115942, 37863355431778180,
        56435283969344690, 38062386984591748, 11414375838485778, 37861155921980036,
        68820685454017869, 37537919770329731, 56168592193981817, 37856757456038275,
        19000306068784661, 37087120103566979, 33931686783651296, 37846861448737155,
        49963537059710729, 36693495192446082, 2124580626140739, 37836965525323395,
        22662311159302225, 36371338822343810, 45471155812535971, 37820472599252865]
    ) [
      46311045310874213, 40055783563756938, 62348191230822278, 37809484210739845,
      52221848026907260, 40372449187595402, 60941576469055622, 37816080877845381,
      54191348232913560, 40735295725851530, 58972325367154997, 37823777056577157,
      47150556807201468, 41156414367179146, 54751768378182070, 37832572679825029,
      33917612245877469, 41566535593413514, 49125271025846826, 37841368252739717,
      11115746836972291, 41940370049724554, 42374922466724498, 37847964819175813,
      41233749734884143, 41922776789697161, 33087506661018360, 37855660880462981,
      60092933952930657, 41387313435613832, 21547663976401763, 37856759888762245,
      66004303601304476, 40315288407236231, 7192667797621709, 37860057869986181]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        58414310380118759, 38448324406547336, 8574737118499370, 37376262721070735,
        31391896575386885, 38704508736976776, 43759684734849613, 37311391014945423,
        991679970518736, 38969488556489608, 60367210872934999, 37247618921109903,
        33078272539731974, 39287244883681671, 57552869127721495, 37189344569956239,
        57844724713171195, 39677569078942854, 47138651471188372, 37133269309161359,
        3515948221049275, 40155854305070470, 28561629424619728, 37082691740717455,
        10272653334129198, 40903520198785669, 2384735761764222, 37037611847841679]
    ) [
      6905394656152046, 36104157949742721, 35337279267573508, 37801780733814657,
      11133064043400152, 35886454764845184, 66017003765206884, 37777591243128705,
      3815272942964269, 35750114819641729, 40401204644777921, 37749003454275202,
      7191413621756135, 36359244043196805, 31109459542380577, 37708320416759427,
      51662720523015137, 37014553493315976, 32793851293044865, 37667637261803140,
      53350586857133854, 37354304498817929, 49675843150778595, 37618158064157829,
      46875910785243740, 37647877156750729, 38975271501074754, 37562082081959303,
      28297862251257210, 37924956586582409, 21240015838810523, 37502707732649866,
      8875427439353969, 38192139337982345, 15610975877501421, 37440034932342926]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        48002751278263075, 37611591142950782, 11112959707612464, 36897979977773193,
        10567017393728304, 37698453668787839, 4924985578784284, 36896881389019528,
        71365895719922496, 37852386638856064, 57008147015173909, 36896882328737926,
        55603344335547218, 38107475467209605, 9158371639789551, 36894684211639173,
        31677885469797219, 38394450468314506, 17602805627062456, 36894685117724547,
        49692052083682169, 38733102834693006, 9158350168885614, 36890287843009665,
        47721267699886986, 39646800168276878, 62638363815414287, 36886989777915006]
    ) [
      6896456854252157, 41735848638834308, 44606252849335398, 37000228637014158,
      69103942832859831, 42174552083890562, 13081321743812761, 36969442613386894,
      56157184827697882, 40650627558487681, 50236254890853909, 36945253760178573,
      51373128132897513, 39489542373573760, 13363282048418799, 36927662144509325,
      56722149125171963, 38605536249567871, 47703469724369550, 36915568154093196,
      8590890182552321, 38120658265487487, 8578688479494888, 36907872294090636,
      58975812957416200, 37845783059669374, 37007905940800331, 36902375507628939,
      56443925435755281, 37667663786578302, 60089098845062081, 36896878687645066,
      6625178118499098, 37588500442548607, 6046130951586903, 36895780048473482]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        6328486070234185, 39415889170050176, 39274063691748269, 36811110254952822,
        1546959112023125, 39353210279520895, 23791952124941352, 36801212116904310,
        6335186224917607, 39282834404940670, 2962949879665414, 36791313978856566,
        24633001039473775, 39226752198317693, 44621538499793310, 36789112422203253,
        49685764334267519, 39145381475947388, 4652456889651221, 36785811437807989,
        11406292811099280, 39043120317903996, 27170897419603562, 36784709510223732,
        32236175533190305, 38531842730231674, 22386402645609796, 36783607716855667]
    ) [
      47157712166693792, 40087707535472525, 63201099018111663, 36886989996034428,
      66297276151409586, 40153681437596555, 2402319360428877, 36888089423783291,
      13097513420958662, 40017344797551498, 45186417026501621, 36896884979925880,
      36740165928659931, 39883206375436936, 38712453892836529, 36905680166961527,
      64886190429219822, 39760062297830022, 12535272450264445, 36907877948680311,
      26603682339335169, 39664404500932229, 994832740552306, 36892483091363191,
      66289004063534100, 39589635646569347, 66297027311734678, 36868291872584310,
      39263931673652263, 39526958467320194, 59823094232879327, 36846299509287030,
      17585367717358652, 39471971678676097, 51097305510089296, 36825406405956982]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        3810557135990286, 40672636413878926, 439948726865374, 36617583054425990,
        3247190580768290, 40467031380197006, 21550013635791772, 36592299303319943,
        31675544760331805, 40209749283228044, 17608328876755455, 36570314338757512,
        9437999403413001, 39912884599871626, 436972321016039, 36552726883839881,
        44620919797493232, 39598427512349831, 51382448461088783, 36542835557337481,
        71921926662696406, 39263079385108100, 26329586401249139, 36526346406101130,
        53341163704135434, 38902441366306946, 4654531439003396, 36518652475399307]
    ) [
      40118866456325309, 38319638227688313, 61230589390261350, 36780306933785969,
      36180179588197598, 38415302534195577, 67142259692833745, 36772608238422383,
      53913382292139266, 38719872355473017, 49410143618698162, 36763810199201132,
      24358715840769309, 39336703646801274, 49973952569641952, 36752813438712426,
      23232940396817721, 40112964224811131, 7190842739756120, 36735219994331755,
      26892140782988630, 40475807759675517, 1282350722354509, 36715428566878582,
      52787799996804478, 40718804191561088, 10290851353956243, 36692339762168701,
      19855128987610546, 40852948737411205, 57860745189560732, 36667052991166337,
      64327986352139756, 40815569200887947, 22676669454389277, 36643966753367172]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        58977904629492593, 38375714126218359, 56162042622935204, 36513162718711680,
        44905856610249327, 39493912720450679, 65451090513984969, 36510963527705727,
        34491497232116389, 40368022417668983, 15630457729416592, 36512062804476543,
        28299146534890201, 40930977253217399, 46874639729524191, 36507664506335614,
        25765906065173263, 41316911807252087, 10001885983047272, 36507664154047870,
        27173255035071295, 41501632797481079, 48845905319460619, 36506564256586877,
        46876438969232241, 41551115015262327, 17884091677835187, 36507663281743997]
    ) [
      55307932311334846, 38520911401820800, 58414894791231146, 36510958125308043,
      7735126491967385, 38114091143148927, 43776989128787551, 36509860375282316,
      64027428892421995, 37670983511101053, 38146660682073641, 36508762054841485,
      9421060075466439, 37221274145228668, 65449209453577720, 36507663516300173,
      66844193006988737, 36777058411637369, 33360813016778193, 36506564793214093,
      22376300675181750, 36425206906062201, 35331378375198144, 36508764269470088,
      58127548331371580, 36321845397469816, 14784052941325783, 36506565548222085,
      27731098414656560, 36484566088680056, 12532665396725183, 36508764756045443,
      4651395870796879, 37309193568346488, 59820835089777592, 36509864284470657]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        7742281882184809, 40350479120523390, 29145246656595764, 36454881875848061,
        51085154806639706, 40213042616477309, 29145272420959922, 36442786878821248,
        28845582223125561, 40078903472921469, 70240601835996757, 36427393397245825,
        9421700021267472, 39951358245022845, 21263900049245709, 36406502391089027,
        65433983458323434, 39816112291761276, 33085750282388943, 36384511822973060,
        51360569634761649, 39684155763358076, 30552312278844830, 36351526222466181,
        38976035736759154, 39541208765969788, 14789490240161140, 36317441194218374]
    ) [
      37024703128775589, 41541223521214840, 58698358417031271, 36505463805611132,
      24639658135432147, 41473057508122746, 28580896655769904, 36502164767574908,
      9721256746134519, 41363109616928125, 69395073195475551, 36499965191112571,
      8876552651582490, 41234469843493247, 38151612751250696, 36493367601529467,
      2120818210155581, 41089337211074176, 7471072199805302, 36488969001413499,
      62355930655665236, 40936507862910335, 54759057253108262, 36485669963168634,
      38711259522706530, 40785877521260415, 39278083847064020, 36480171952002682,
      4088776534633583, 40634147600908415, 36181987943352494, 36474673907286906,
      39833985456581747, 40489014867770238, 12538180086958042, 36465877394805115]),
  (8,
    m1K32P56 [
      26310048337406770, 39372975249290876, 63484373443839308, 36274560072948870,
      14207040956967658, 39151967003197052, 29707002571359522, 36227280955499399,
      65999145347885678, 38664878201483643, 63764976534717676, 36127224642372231,
      64030229270014493, 37532377970070907, 31676073270019242, 36073349679894408,
      55025224756734400, 35425710839112827, 47719597177930830, 36015074892515464,
      53060848470698394, 34442745346715259, 2964139570332613, 35951303268429449,
      50529669637516496, 34793493582649725, 57849243154678522, 36065647796755846,
      68541130395333578, 36608798437281921, 41237915921908209, 36388893628663169])]
private def schedBlks12 : List (ℕ × ℕ) :=
  List.append schedBlks12G0 (schedBlks12G1)
private def schedBlks13G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        4375848182975907, 38406531372958347, 43208038961350467, 40745234180012437,
        58982801146744686, 38679213930910603, 54190236003043438, 41418151016145025,
        42940789080494301, 38925508008464780, 53910431788337514, 42293334504505477,
        43786519704212245, 39145413370759822, 16757006189365830, 40249281940405895,
        47728638290924959, 39341131926782607, 29143013280680720, 36702272562346120,
        64619104021679561, 39804034089986704, 29143949596462016, 37644560285328265,
        40413806375633551, 40198761515892883, 19856138664775062, 38052484149240970,
        28864845301712319, 40320812658729619, 3531363143093920, 38385640517813131, 2243790639]
    ) [
      5787617117240686, 39815025850750863, 8034077975415989, 38125052503873162,
      52245822549296567, 39990949774824338, 69678081437109615, 38418625614979210,
      15620364507318126, 40121796708828572, 60108834183941636, 38662720769949067,
      11687505932290171, 40807915889303679, 46880270497386136, 38899119460963980,
      52221727957879134, 42080071510369669, 23518487411462709, 39131119904137101,
      25201319914605106, 43117898566580359, 32528435491739087, 39359821678201486,
      32802153617066763, 36160213262751368, 45478539339405394, 39572030173950608,
      29706860895243223, 37643461277021577, 56179231336399062, 39738065338537874,
      17604347442924685, 38079972225149322, 68001364666189244, 40360394590713750]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        31961173307985554, 38355953250874763, 7462718373594902, 41092671649645961,
        43502910094020671, 38636332725797516, 21820600793532484, 40744105710011267,
        57296554072314343, 38915613544726669, 51095488744556866, 39430176513411461,
        63772114943840347, 39181701583071118, 4934863891237450, 38680283394193287,
        32811284814728123, 39632506316570256, 15350541854149413, 36950762072771976,
        38720060222376277, 39948068217453969, 17322069299858634, 37635763571536777,
        32522173270754114, 39992057608104847, 30834191055228352, 38015099982135178,
        20979594592421302, 40691350442557578, 52509104303803937, 38333962934456203, 2243266317]
    ) [
      1850158294270678, 40038229781578900, 18448746603580884, 38048086018843018,
      12256627679069628, 40423069672799890, 3250407858408875, 38377943869309067,
      54468730247022377, 40987130177108362, 40969261621022692, 38664920179086220,
      7465398457174104, 41584154169192835, 34777808597651937, 38912313986437260,
      52784398735870299, 40889229785640069, 23801865094927209, 39177301388996494,
      8875608056039994, 38647297793702279, 58425907178737774, 39376315476779407,
      21543098714196802, 36946364076596104, 5790760775944454, 39713874623066258,
      23232906370714541, 37639062290975625, 13385362365252423, 40126195963138706,
      14226974146923898, 38026095467514762, 6906039031662006, 40568208244191373]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        14509239433138174, 38357053517473163, 14217606712559355, 39913963492386437,
        66584055772712888, 38634133903839371, 58130795478026318, 38429623633456514,
        19298591843782025, 38932104155545998, 46873248130435372, 38641818472202629,
        59267334124046591, 39108035310685327, 69674052698802753, 38560434244397446,
        12821347285436541, 39706176951132815, 3247079198657320, 36788034083420552,
        47441914674383503, 40184467327750540, 14225917570616672, 37618171083482249,
        15066391136076454, 40290018749341325, 5220139986489017, 37990909149268106,
        70242229517518245, 40250423848593029, 69117034187099870, 38238305590560651, 2242283260]
    ) [
      7751507725157167, 40280130308881551, 55323128207805732, 38007403316856970,
      62073910399042996, 40799101608986761, 68834459671302039, 38325167026013579,
      21254786073593605, 40768303371252871, 33087524219949350, 38655028500353164,
      4650597148362792, 39576415402105987, 64896580320727144, 39172900960100492,
      49406552983505250, 39049730675902085, 18455283610258307, 39320237984521359,
      71362881089538822, 37524695398330246, 54482203649542942, 39485170164660880,
      13099124301073310, 36861701463145352, 55322367977227466, 40055825927012750,
      48284587322805306, 37625867597787529, 14226969723962091, 40497831698391691,
      17886153138671261, 37994209429003146, 6338429031581097, 40525310261373067]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        18450834009722401, 38258097202559372, 25194666945381996, 39145388741420167,
        720049332652924, 38668220140102797, 30264549435410421, 37570894784528002,
        1843518268410756, 39047557674772111, 24354618628933975, 38349340510677381,
        47159834179634415, 39367521279622028, 30830364181564111, 37382855948840838,
        55041919380850923, 39830424432453259, 5499059411913670, 36712164928944520,
        43210865132995612, 40158067270874252, 32240779942858166, 37361982860957065,
        55039793357357681, 39594015037633923, 55322853349297671, 37871063556258954,
        14217950256071799, 39393906689019785, 66584128744164528, 38314172731798667, 2218165903]
    ) [
      20412689167581844, 40150381041013390, 15916652952063623, 37996407311371402,
      46599259185317281, 40159162219183236, 9725311585193630, 38284483636134540,
      34483457142851323, 39228977679971212, 8319117826559485, 38558269447082125,
      37864562794596352, 39292714156289666, 71652576690670366, 39054154425772173,
      44058408163117345, 37142100936131205, 63767673829821080, 39332336253128335,
      58414735804435074, 38994740213291398, 152280372315186, 39728162301528460,
      64890202182421407, 36720963588895879, 22386466988788170, 39797438798348170,
      11130238291184917, 37596179156430473, 35330991685599861, 40250421667328903,
      43501157715709551, 37856769116557706, 7468061257532812, 39268553975052934]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        58420327897598821, 38337262123672460, 43490823887357618, 36535173839554180,
        52508142175946872, 38677017994779020, 48278226395564089, 39774297077884034,
        53349766754828891, 39154213926505867, 57006046642997609, 36856199425204612,
        67985078181596868, 39621504606641800, 50533758581967669, 37321284069410694,
        60099196327658175, 39495056709193095, 11691633461398702, 36731955165181320,
        2411690753295476, 39225667350925702, 38715318600961082, 37367481257960585,
        50527672527192683, 38756166893491089, 30553746859723589, 37918342673701259,
        50529321761211582, 37995345867782018, 27738528926108154, 38316372510078604, 2227275451]
    ) [
      34490475074191990, 39606108675656067, 46597343819697464, 37883158234499210,
      36172719267349509, 39263055561065096, 10851898664324277, 38315272461525388,
      70230740502480535, 38392213159806082, 48287108488858374, 38713300318175117,
      38425747510822947, 37208055427051138, 51946102754608857, 39031066409679500,
      14503239259556228, 37948009388084356, 48283556419831049, 39515957513457548,
      44904263343770290, 37089287032040582, 20691775996069395, 39915074177769609,
      15632287420615803, 36764939893252232, 44903013437441043, 39480767554324865,
      32803661190761871, 37365281949500553, 20974938866221730, 39447766350515593,
      59264477970992161, 37909547000099210, 71921785069208776, 38461472426889859]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        51944255899536016, 38392240708220555, 66852924831467181, 39544495540527489,
        62919430669043617, 38884827722392970, 26604644598909037, 36483461577545858,
        57573038165953265, 39248766440225160, 57850471577520683, 37082684660538244,
        15631956692205898, 39250961352934794, 51660010688973672, 36354812358742918,
        50534583078912927, 38976075711774089, 38714068745554779, 36693472627309704,
        24630514365530393, 38532975763789704, 19293528006036070, 37378476575593098,
        22943721755607642, 38515387604127105, 23233950026139910, 37934837327873931,
        6334404638835910, 39089318916080259, 3247293930375122, 38453814198225035, 2227996361]
    ) [
      69386684939207233, 38893603179832718, 34775686823840595, 37931536863575435,
      71920960428999876, 37811735914980738, 16479319410313812, 38320771059907724,
      39268274035066549, 41633612495532163, 55041322481190330, 38799065899345035,
      23508475689011244, 39386170312058242, 24922125475156995, 39263062356374155,
      58694862143457765, 37026617771579012, 43491678844979949, 39408195911440266,
      48563485293120380, 36901269570636934, 28873538433942445, 39268548472382339,
      19573499747929076, 36690173807210120, 65452026741818079, 38626438932568211,
      2123691875928923, 37374078159966602, 19285255753466463, 39013439109179782,
      34493666373503262, 37907348564087179, 63193634129544390, 37535742305778563]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        48564125264152466, 38529680886369161, 17031763760940797, 38594551568623233,
        51944560824192826, 38951893519140488, 20130810333989102, 39042023373736578,
        58133548684446380, 38936496111661449, 64043273260927580, 36996920203429508,
        22675969379961615, 38674809156548232, 2965380885940786, 36121715457452167,
        13664612588618606, 38499979660651410, 2122377585723752, 36656089517199753,
        25203974103990160, 37595087647861643, 18166073289246950, 37415861413809290,
        64883652156752433, 38409827424830857, 59260685444285476, 38034894983148681,
        18996496505406703, 38070080781181827, 11128421373151339, 38592351992131721, 2230486823]
    ) [
      12248617535373916, 37778718621874305, 16759724896717157, 37945832662259339,
      6616034234434768, 39425763820260485, 49689986489615592, 38469207562333322,
      22661332013713109, 37396047336966017, 57572436793593089, 38947498358373256,
      25760258326366388, 37026629767223682, 3522597130175014, 39134411660823690,
      59539519010736737, 37571967519447684, 19580431644525945, 38865028543826052,
      64889618065296116, 36430678526842246, 71073627890156712, 38658324266558353,
      57291597588171246, 36681377898752904, 60385670435406187, 39058527961197701,
      29707444990740772, 37389472446861962, 16188631557374544, 37994253049644681,
      46876327633324799, 37988714504939402, 26037893526160602, 40653929717552259]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        48281950105405984, 38620936039631239, 35045835856250735, 37366393188056958,
        44057665178339071, 38652820081584260, 69670638171162931, 38738554087472001,
        10567017673098405, 38470295648187015, 6622897706469694, 36454855149218949,
        39273767295486548, 38217389787574410, 37868449777289312, 35951289611656839,
        15627116302008334, 36834226154920586, 9720870486116322, 36559333450289289,
        2124872785428477, 38571461204219781, 69392564817789481, 37479635269261448,
        58405587372311005, 38823257302189964, 13097573660723544, 38180030417262728,
        4926273831994668, 39195963760116352, 23504000380799420, 38567057000255880, 2234681262]
    ) [
      59253950711562797, 38373534783275655, 40964571446673847, 38050288364033929,
      2104939885659380, 37864465043528579, 69957193980217403, 38605545561222536,
      31949761434584886, 38046983738548601, 69383291984840286, 38834240909533833,
      9153415095486768, 38266864487989378, 13097358993426101, 38616534822304127,
      148724134414816, 36717615661587077, 59257378273200179, 38393341745766792,
      20980011314350358, 34645070552827015, 19569011456180787, 39031011464061830,
      15351027163432996, 36604412940473481, 40964150416407596, 36187722092008581,
      41808927631772320, 37446648863472009, 66008499772424715, 38963971000451720,
      1556674554462908, 38110761906175113, 56714864936322316, 37896338885125506]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        60382182711920668, 38393330975304070, 68259535222179806, 36951873143553148,
        13641123358081954, 38265783012640138, 48841936578054226, 38325134896505217,
        62919855754412767, 37971098109523574, 37867032422680554, 36566970019195781,
        55313743531968560, 36408738524424074, 62074228305266416, 33949077947649927,
        43208477091070465, 40206363775433347, 8311876379574507, 36496663267236488,
        16475539678460485, 34727577763616897, 27170149954523015, 37614876256373639,
        38141905824481705, 39744604106433928, 14777644854574500, 38233901806073991,
        25751324707292589, 36595596496774273, 62365182157295191, 38244893835349119, 2243135445]
    ) [
      63191649825161684, 38713301039151756, 23793979235207518, 38202020280702600,
      56436499512329524, 38970563658282112, 46583544008182104, 38534070611228552,
      55874752207423424, 37515936751747968, 64607687801408053, 38375738822936446,
      55878574771046615, 39044212682962817, 62356566607299855, 38205318361936262,
      20978473699346495, 36394386539528837, 55602180691036646, 38529628440361864,
      60948899634710400, 36022757162832263, 48277973037580648, 35519173120005001,
      44341227453581523, 36510955861433224, 19011180987187126, 35081603764486276,
      4652169131491127, 37544507545782664, 23504897864139188, 38343845720881034,
      149368253151666, 38241600551781255, 47427887211382124, 37096988210706561]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        6892853599964154, 37992001295534471, 34764159032592260, 37398280870498431,
        18167765536573917, 37729218989870460, 61508976243017448, 38607702171030657,
        28018148451386531, 37656680933856908, 9156069378262526, 36410875690738822,
        40683641846532179, 39901805346097289, 23792063778096422, 35904010813056647,
        30544727344382680, 34497783910680201, 51657231749844460, 36584626714002822,
        9154209618689830, 39764422025628036, 71920131696392750, 37783098783870597,
        12532532012548612, 38038195128238468, 29429461554269505, 38040382155916929,
        68819216648799813, 39015637208706183, 60369422732265024, 37899642066762381, 2253227794]
    ) [
      52495007949816234, 40468086113051528, 27161912487281292, 38230602432330631,
      12241762775762362, 36989239275642238, 31965176053141780, 38191017396498559,
      14497818970720203, 37891966104249726, 58692899509535943, 38006300885342604,
      49968184375347092, 39118954022466177, 51389075512723180, 38138208005397893,
      60947825880893142, 34637359425368965, 47438654780443380, 36022767480898961,
      50532839412303737, 35721490926527623, 27450796176604053, 36341639443174794,
      17599330847260861, 36525251995609479, 65736250374127378, 38333985147475845,
      24637072764010345, 37711632256148614, 40388646225150407, 39647883439735946,
      5212232691452209, 38156932049417607, 9147247431091719, 38854014301521022])]
private def schedBlks13G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
      m1K32P56 [
        44628221612755689, 37476327875746939, 64601683393939021, 40306492482233468,
        61802060619220818, 37529122351287693, 4933085723329779, 38902399439287683,
        62645652220186547, 39407023603727760, 46027822413939994, 35803936078380934,
        56443663713405385, 34461504725109137, 67981264281046118, 35386147496961925,
        2684691870284893, 40016243659560327, 34767161323518546, 37099200236082308,
        41808545184710123, 39682006921433478, 12820956170915311, 37909536178464644,
        71633081586320433, 41386195653240199, 43762996113410455, 37600567622878860,
        45174910627710639, 37802873366985599, 16480921375904263, 37260814017401210, 2259387763]
    ) [
      24920746681926178, 37531311728222852, 45754675191582032, 38002998022378624,
      25468183291856471, 36981540496259722, 22933246537860199, 37805084251282061,
      5491229611427570, 37134393382997367, 65176427275190234, 37744585762198649,
      22384298067723812, 38634144119873154, 64038376849900560, 36095365144556173,
      31391931099809296, 39882003818110854, 59815165633071618, 38232753020222593,
      50531233083588720, 34420771841800070, 60097873394634164, 35938150182377091,
      53627513575604882, 36742957696981381, 52226134679190337, 40285575605226883,
      59815440437315103, 37867758176014213, 13666098389877413, 38220702197130379,
      16181562198626212, 37832568854655363, 56994862456800912, 38060193951182476]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        30833984956235521, 37385063948208767, 24937952461292598, 36902401043196285,
        20988626812177363, 37718225819140491, 12250387108431075, 39346619803103132,
        56431457410319015, 36861710053359760, 32514476619302964, 39101345480789893,
        69399170369031252, 40617656940744314, 42930472496103023, 33905236095875203,
        50526951079578362, 39142129430851214, 10007451988627283, 46224039936753029,
        43216470070557028, 40182178730930562, 136187211451094, 37359770398963087,
        53351596174779950, 34744081745928071, 20421704233619071, 36963954300240507,
        67125999436072064, 40143739242849674, 37869566557322970, 37514852557326220, 2219410247]
    ) [
      31104498878481774, 40391135214102406, 38133599647401735, 37529099534788748,
      3517108021986982, 37634645202146947, 30272490824830114, 37276204109952634,
      5215432585807158, 36753945246596479, 26886845490955629, 36734186886436492,
      65731654904939641, 37132181021095048, 12816511063720582, 39482890711211397,
      36738005717189020, 37863331692459398, 34205327893693253, 34689093128763270,
      67136822107474982, 36145950297058948, 5773056717063985, 39319109917504647,
      45741520014506940, 40402131723016580, 47432220933849380, 38055757652421762,
      34493408429968269, 37775391464927106, 37585767786254960, 36232794820756612,
      64596035593144974, 37294905068054922, 25474922421519885, 38950761660844424]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        60379979639392815, 36677014915803522, 45505897962898382, 36715440445199741,
        17878370630206883, 39582944020552075, 32513918256513373, 35732496611938731,
        2686096242606645, 34400976422131587, 15907787935419446, 37663214907655555,
        29980299840486970, 36030530499784587, 12809055110003216, 36268128057111940,
        6617348411328164, 41530210638359425, 2123309322960965, 48321900488970627,
        69942058637951779, 36396637169327233, 30816169183580980, 36921069889993098,
        69957267072658371, 39695105984094841, 61224851460030730, 37332303898842237,
        71079564148507434, 35313570065196937, 60396429280054654, 39227862196491652, 2200339660]
    ) [
      49692202450593963, 36478008613569413, 62077960663961214, 36943063344427386,
      37571998792451094, 39825998333924490, 41527835019543515, 37467572550680970,
      57607908928029499, 39282819155485051, 2127406918044545, 40196473036043913,
      34484810017834208, 36984841714797738, 9718568421919976, 34519752819388303,
      44898898845535881, 35629108581550723, 3810789420270270, 38008500127748488,
      27166748570778262, 35046567903985795, 15356327037402172, 37200391846807433,
      29710966607283662, 48163571787593859, 48556080544906432, 39443370401625738,
      47422509962592839, 36972743094360717, 63751717795113783, 38782556766098304,
      33921769845393587, 37065097139278714, 51647663213282125, 37927117509378687]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        17889898307291789, 39931476238199433, 71966096254338115, 38592318974562169,
        31676739030192542, 33545571273435534, 64038922373533020, 36559350058861484,
        10846096246409663, 36305374819525002, 71076230733068055, 38291018515020418,
        20708071164838244, 39758949734067591, 71648831112052404, 34539702203900802,
        28860610434335544, 39872189901968529, 44885236443811444, 48749608951774091,
        60939858571655920, 39681945668428422, 51929408305401165, 36814406457950582,
        2950661779205465, 37135515174343808, 36750272282136261, 36425215545608573,
        38416445264003779, 39665440057694331, 39274897090249622, 38771486856428944, 2193326293]
    ) [
      60106055178628088, 39921612107130496, 31391128138449137, 37421384892604040,
      18153326408205092, 36184386915650954, 22396366828637707, 39954624853633415,
      4974356013024532, 36771552717064826, 71074186348561300, 36725376198127760,
      17314166455570038, 38478003402466476, 15918516854883142, 38551663519243652,
      10561013443559364, 38924327448237699, 32802003188877270, 38497820130913165,
      10571720497072358, 33963555292390789, 51093040580430399, 40494506336643467,
      61213796048865427, 48561593755437198, 61507808057260305, 38900224140104069,
      13661322595962749, 36907877378465912, 68268739135712410, 39250982861204867,
      68830134674491847, 37320234855010696, 62902779654800155, 40786968392703881]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        33917556584452492, 36848470950439822, 7510194884279639, 35157393277580926,
        51659508308935594, 36715468648485506, 44616221172203996, 33939217708652974,
        28026965913861910, 38348275442997384, 11961864036648325, 38787993442361474,
        42084569947012945, 39763351152688274, 38983809803717291, 34085610159480192,
        16469372124891559, 40084393935679108, 24356959471439052, 49103648491424894,
        13938558456723691, 39667711139437699, 31683168642895097, 36613200174454921,
        34490891517996628, 41293832482207876, 34493623442640132, 37147532442870162,
        133030967869967, 37855655159346057, 10005656925475487, 34585733936355467, 2181924038]
    ) [
      10269505119890860, 37141004326745727, 3818322638509160, 36092058052977022,
      15057299262833333, 39099167846345085, 55874490505331971, 38407545068350608,
      20176014792294297, 34321797340035199, 7476981986986452, 32872644203289984,
      5773129665447878, 35120074842986670, 19573293542897683, 35880983026674060,
      42360113655608300, 38629699788611714, 22667026906118890, 40549433230366348,
      48842906888011807, 37365451533223805, 20397042256939445, 35604974051148422,
      42627355007160239, 49011291175332997, 66842956299143671, 38379070660338039,
      71637458446155416, 36706632692187248, 15914350848290341, 40768257971016056,
      1283011940419571, 35157450738055555, 707869369533016, 37142031511238538]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        15923992906861981, 33455404978227064, 23833565981280176, 35110135583637118,
        34486661292393323, 36513172566751892, 27164566618142457, 34671437440585132,
        52787448071027750, 37984242203162246, 71081006371995765, 37474110685255553,
        9713573124668133, 34270203207020936, 58959333201511715, 37087261417927559,
        10268358328879397, 40105286719466370, 23783649907276971, 48183356521173367,
        30815263104927395, 40075581836097402, 48558502971214852, 36556046339635070,
        69677102139943780, 38459275919089017, 49968012619845702, 38212940838361475,
        50249080132633042, 36830893796061834, 60105149150759385, 33725861735958412, 2177468343]
    ) [
      994673507545156, 41241064212034690, 2966952872347817, 37564236612451218,
      15051432373879308, 38472478363815304, 45752974609257052, 33578585865389961,
      22992147528386056, 36834190922578553, 25198652886518241, 39508269521739660,
      41519824768104171, 35976594417351598, 20426518891758026, 40144850599593093,
      4370341668556040, 36814370842213506, 31677473320894294, 37710557272653201,
      6604313460313462, 34314301816836487, 62346357283389429, 40024991081749895,
      44911182585496555, 48539598976404086, 58122037872065307, 37231182047746174,
      22671609810554718, 36612119972982411, 6608376214039614, 40271283849396860,
      16182395524187205, 38166757642730379, 62906816917963280, 37180524048663673]),
  (16,
    m1K32P56Cat (
      m1K32P56 [
        17327455220043096, 38906755795446160, 17359242068461324, 38337196792851577,
        71084842151346921, 35280636810863762, 2112121151523386, 34584608821037484,
        38717474499298635, 39897493602165641, 60665401761693166, 37051864263154560,
        21252037257231200, 40155900459625869, 55039363786378745, 34221937051873670,
        62349071651078509, 41222370468117884, 60096164042346047, 48257017911355017,
        10269728496646697, 37734745990846593, 63206721087967441, 36132729028977283,
        48270194628078382, 39723680619588220, 13666407952844095, 37845780509747086,
        4078233228902442, 34615373957238652, 15074529979108627, 38633033654217101, 2146403930]
    ) [
      52506518502091716, 39100299805655928, 37879513603412285, 38186554757078916,
      4358028890505659, 37507132990930314, 38430330472139703, 33936966173404567,
      34810587555465116, 39192599106008186, 6638256560964850, 35327884135937160,
      9994107704015332, 32779230508605612, 49975726284901487, 37963479206341269,
      37585119179275603, 38539504065985665, 67981053974967026, 41606105965866892,
      28855430640338887, 34169163278807431, 17327321659312237, 38582496736910980,
      19277765456466608, 48496714935914631, 4633533257709894, 40984902531024784,
      67144536148445702, 36385619605802364, 9437402392734793, 39778697725622392,
      24084692876103531, 38039297357308556, 37850918309036331, 36998067244322438]),
  (8,
    m1K32P56 [
      34474957277014700, 39689602469938045, 7754741914698731, 37787504799872910,
      57842616651972531, 34921033995512441, 44064322255555821, 38532987675870092,
      30586444232623646, 35576340543021441, 29980050909985893, 39620412040830603,
      69663925115455640, 35758840867927465, 6065625485180414, 39896381724999298,
      48561045726399833, 34608800311397246, 25188082628198324, 39354314170393740,
      55318992171076989, 37904193138088325, 30255499843829886, 38780327258972540,
      10289245066005386, 48773777605380488, 44896974678361487, 36222895373824126,
      19010051527116580, 35763282904482698, 13935294148621527, 36600002176492674,
      67133991740342789, 36451565573358977, 33164])]
private def schedBlks13 : List (ℕ × ℕ) :=
  List.append schedBlks13G0 (schedBlks13G1)
private def schedBlks14G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [32517796676995249, 133]
    ) [
      49681284815947473, 39612716265057938, 48849465739152513, 38700104500837003,
      31954902558738612, 40894761703362437, 41249332130254416, 39119024538013580,
      60667428975118908, 36247073473351559, 67992062038544568, 39487361537281420,
      35899318971370406, 37942530671162249, 26898218398680435, 39421395889717905,
      69114903842622324, 38479099492711818, 51375176990623700, 40138296160872320,
      7752993844530427, 38910114275238028, 57007283601901952, 39993089171223174,
      3251245392761143, 39297146495389324, 49972251750664945, 37562095084491656,
      58987748934582447, 39210285680886926, 16196826526354282, 38229506880273802,
      48555178750805701, 39707277201035916, 40685222509644815, 38697905393691275]
    ) [
      38156607987155342, 39721565365865614, 16196942493813885, 38243800481100938,
      43208013186107101, 39981053952140440, 56167978346646940, 38692407885891467,
      29703149990021295, 40618811816237445, 5785177301814893, 39130020090508685,
      62074790973311550, 36381213774502279, 1845210566858606, 39529148297613198,
      34210477701761982, 37955724911358601, 39572095665538412, 39839214502540432,
      153637630872835, 38479099408825995, 5776209289316315, 39974466261201537,
      28302518299889041, 38912313516603532, 60103542705523068, 41861160752213894,
      33650448379384031, 39325735777532045, 50816663796222719, 37558796767713416,
      14796169107833069, 39673184287242126, 17604265836121177, 38238303006849930]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [28858497423673493, 133]
    ) [
      46584974172849845, 39875503620713864, 60951021401181245, 38689109065764233,
      31391823754725540, 39695154520576389, 22672241380331283, 38937597603127691,
      53630477247023654, 36266864598757767, 57859538323474462, 39021166560301965,
      31114136978033144, 37911743909372041, 18163822584104299, 39511559668418956,
      52506067713624919, 38454909901348745, 67137741324715962, 40139372301367680,
      44344805247585772, 38867226929528202, 48562918334957929, 38152507914283654,
      33651625204026251, 38838644559799180, 43498224203827525, 37552199010071944,
      12819448857133316, 39239974524945806, 68267794520181404, 38195421583598985,
      11963856979461800, 39984349936544647, 69395257819565207, 38669316396758921]
    ) [
      440421181063340, 39210285748002959, 15633859391883952, 38225108816984714,
      33355525713594049, 39741362917098123, 30270141565537300, 38695706320103563,
      32517779496994990, 40505505545760133, 24079401507393330, 39095933015327627,
      57571174166137395, 36221784705908359, 22956976266971768, 39000275923245453,
      34210417570056957, 37926037795417225, 7188669310993778, 39435691252205199,
      61795373304482651, 38470303248691594, 50812222741120969, 40329599859139968,
      43218892451057008, 38898019110368394, 52222161752590710, 38635192461914502,
      11977540910747206, 38824350925411980, 47438934010006216, 37559895809574280,
      17325930434101442, 39215783893374607, 13100374118861474, 38213014004528266]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [23510352604727354, 133]
    ) [
      8305197677512342, 39817213968437382, 67988003200142597, 38524174872427657,
      25199249710876801, 38476885621053317, 56168609710246730, 38628634969948299,
      44341639793641587, 36492264146899847, 9441573063460353, 39061850654839949,
      30830819446393329, 37876558966847112, 29139186320901464, 39716064871504520,
      17321648383101921, 38402128007953289, 54752760743036825, 39025551318831489,
      59263606089878723, 38420824252347530, 40399997977987061, 37628044474931078,
      5502602752854038, 38833148008332173, 26326459597687101, 37530208307745416,
      14504738159559132, 39412600064993418, 37868544280070879, 38156937451774856,
      46586224006366861, 39465363620486277, 71365887609834754, 38180028202696329]
    ) [
      48566122354016541, 39253169201352077, 46875765009189536, 38191023469976969,
      66288639153637028, 39977750668925574, 67706412255317171, 38661617986653065,
      28295530290186385, 38868315015296645, 37309459864980776, 38648426128908683,
      48282375378143519, 36384512175153031, 70242169509217974, 39023366556668301,
      21261086851238380, 37889753358044809, 46591322065306978, 39654496347658633,
      21262272284756885, 38436217515709577, 26605301727397800, 39503844044337793,
      48285729808092624, 38409829303840138, 43214812171897139, 37800666105995398,
      69680117241645366, 38824351227422348, 38149877496645955, 37540104063394696,
      59823317521367417, 39319141358605707, 29424307862997684, 38176729567134088]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [16754772757350142, 133]
    ) [
      57564259198404217, 38981572967723909, 11130611964415000, 38222909290399370,
      19569617027499755, 37967811032804997, 18731226576881814, 38642929610999180,
      17599773235120274, 36725360259658887, 10846074585056740, 39210286486113930,
      59259912354302514, 37843571722086791, 64323412394542403, 39309232851930502,
      22669973597228085, 37982113072976521, 40678913121224465, 38324057766466690,
      25768337237445079, 38437317329436555, 30829144371136469, 37506002106794118,
      24076772901095144, 38920011775745419, 70799574637971801, 37506018431126918,
      13658835748291239, 39420288693799304, 39276052313115501, 37900745605371784,
      22661692798174821, 38681403441151876, 24641655654812423, 38235003851202186]
    ) [
      62073798771180026, 39436788985233289, 39838869117504236, 38151439105108872,
      28571937165903496, 39348814079317125, 1278682834963684, 38197620439072650,
      22384439812655103, 38188806679172229, 14228567568845203, 38633033402351500,
      37304060986034316, 36630802410669191, 30831824440755357, 39135519645152651,
      55882178273315341, 37862264862648455, 23508630232991051, 39577519041099399,
      18729165005229119, 38130546958174857, 17035053733349241, 38581344024218498,
      8035521095764744, 38434018509330571, 35896243712985035, 37577468986869894,
      26892776813070090, 38874930758829452, 7749132610210119, 37515914354583687,
      61509981235479127, 39484064864577672, 40120391341083441, 38103055711324808]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [1834962599839457, 133]
    ) [
      39550496342443493, 38407621220680581, 46315228845869500, 38218511445233546,
      12531995263272694, 37974409226682245, 66579425667549046, 38725395147353226,
      1274310484658340, 36880390962915718, 12533751921149631, 39233370039353736,
      49971324027243189, 37582982634470279, 63199234778367270, 38669308947551878,
      45188538669828779, 37985410886445705, 3805553715349006, 38045879462527875,
      20137046664316937, 38472503094067851, 16754437756389298, 38451584119937925,
      8875298781038112, 39061848003864457, 52503765579041201, 37459833272013958,
      68826668517131034, 38921101036226438, 50816934388206372, 37723723209896072,
      66572265903260923, 38284474123074182, 57010848449071331, 38256994738095498]
    ) [
      4932505862374073, 39379605488485512, 38994611697257340, 37811685129966984,
      19565549658474073, 38607735390340739, 29145311114136251, 38230605720807818,
      16191749784438523, 37708313202445701, 52788182614116285, 38683612665316747,
      5214960159197321, 36826515128075654, 68828970584998587, 39274055526410120,
      56445136819882615, 37779795014515079, 2114603573871927, 38914503345665926,
      33929277611674499, 37990908864009097, 64041284643882481, 38089858031550082,
      37307969445791945, 38448313116821899, 6058229728970687, 37298195734541190,
      70237582439646806, 39004674640791689, 68547688925989250, 37490623489896838,
      8592195976332017, 39171793311275143, 44061320195836795, 37708330902734216]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [26323246921254656, 131]
    ) [
      18158655797036275, 38076668673697414, 47158253584615447, 38254796536936586,
      17316150744745712, 38028285581669252, 2682741924071293, 38843042606224777,
      1837247555668205, 36930963900789382, 37585183771559452, 38838637328586631,
      67141632621251216, 37420254796120455, 59257013149205490, 38227302874045319,
      3811472255781075, 38003004263693450, 15344563169625589, 37990909199365507,
      55319438749566830, 38564863849165961, 68545691739326452, 37555482747185796,
      64887951550744415, 38954089186894727, 149492930742805, 37027724329877639,
      48280287952798519, 38430714269990277, 3810999816849805, 37735818877991305,
      49683866057934040, 37913930617979780, 17884048540927980, 38278986530952330]
    ) [
      35892378223477535, 38850731302189446, 52787332239887099, 37688539945098120,
      56157700353656019, 38242690550409861, 57573613714704558, 38211914962686858,
      67418524798715679, 36870497455252612, 55319309897926168, 38801261936168585,
      69672893033449671, 36915574076655493, 33079921930896835, 39044249039705735,
      61793419082566344, 37378473673027463, 38709292603901132, 38435109380428676,
      64328875728603523, 37967819673489545, 12530818422834707, 37795184586917507,
      35898408396818216, 38513186114814090, 64323648691472356, 37755593695731076,
      26325926989366722, 39047550795862920, 70236680524171758, 37298204441963910,
      68264508807283506, 38627528260659846, 62639123926649416, 37713828393772680]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [38708248976000816, 131]
    ) [
      41521083144635633, 38064568257640073, 32238357513209673, 38327365965310601,
      37863836930049818, 37883170179461507, 44621955107948085, 38805653808514183,
      3526260629211469, 36924364364773510, 28858338492582863, 38399926317047687,
      15350627744844099, 37426852083998856, 48568093679190917, 38111852760582022,
      54194028477253519, 38038189894095753, 10277708646155793, 38009595595905667,
      18444941187647176, 38655022175164808, 68827312747350081, 39703927998088836,
      21258136171808381, 38568154263690119, 11690310578309538, 37023326585361799,
      31109953725629199, 38182220783251334, 24358114747844631, 37741317191125897,
      41239384829822195, 37454339824297867, 61511089369810618, 38370247153648776]
    ) [
      8028039124517688, 38377937258834052, 7188686649919830, 37730321386963849,
      56157790519788777, 37756697871470723, 6906279633848239, 38291081393737866,
      21256774649349894, 37522497918416515, 18726308766647433, 38858433218813320,
      3244704045828391, 36933159551823750, 70796340474708728, 38564855980442757,
      4935903286561264, 37418055940640136, 42646467650290521, 38035981743763333,
      2121896529987633, 38016199023997578, 15907087920891404, 37522508689447043,
      60385326891501144, 38624237225362056, 67701395659327514, 37700618282038916,
      70516798234265110, 38746277663999622, 6060643538864637, 37014530408451975,
      48279875682534199, 38249290992646277, 19291986084006065, 37733620257399945]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [37019467837835141, 131]
    ) [
      71637784666342647, 37521414077246592, 10282016530532060, 38424122501944712,
      38426799770273618, 39434538287506563, 66013632396560162, 38492287508370566,
      12252229725948194, 36618700182583686, 31392390771278043, 38071169840521349,
      38431339592779773, 37430151122213768, 61221647135179656, 38020586383293324,
      41807742207952660, 38107460452028296, 1270526571677232, 38054703220698498,
      13377923447621063, 38564857104552583, 71360729276057743, 36194282000058244,
      47435141501914417, 38209709295479942, 32519793856055404, 37022227224737671,
      66301966354973165, 38026086843827846, 65170642024761154, 37783099975177864,
      30542107353842943, 37863361019197056, 42651540062045657, 38448310348433543]
    ) [
      61790305229046509, 38155829786242181, 24639456577423345, 37745715371858057,
      20128576892929267, 37462035415809671, 46874266023265826, 38387839339684744,
      38145299022907193, 37610462707366019, 18161679473214946, 38652818219326855,
      8311472675981653, 36762736189043590, 54190532329767461, 38234997509186181,
      31676180679592050, 37422454305931656, 2675247123760007, 37701728732588166,
      11971875723642611, 38075574262516873, 28292124335441441, 37819381190824322,
      54191507294094741, 38639626378300039, 68545906492344443, 36322926269794948,
      24916511996348546, 38348249740270214, 21260704598100222, 37025525591844231,
      57573046630253115, 37954620030802054, 15068714654336914, 37761108970865033]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [40960237775456196, 131]
    ) [
      36452635188299023, 37508240959081863, 8873722517030131, 38414222887462791,
      38708382125361062, 37164080095653507, 38989762597260328, 38166827687649926,
      30829947554727977, 36419688594739846, 50256999388252512, 37911738892753285,
      29423023627732716, 37457640037003656, 71645996607046538, 37520309784204419,
      33643816825620098, 38199818673718407, 21255258509772403, 39756708331480705,
      64605493012956679, 38266884722181510, 6340297424078933, 38407595786210437,
      64042332743959556, 37945824743138181, 54193049217304398, 37029924259134599,
      39833186827600179, 37675342282243981, 59821389092652707, 37858967468654983,
      34763433141306651, 37798511710054277, 62353847817045619, 38340553611881862]
    ) [
      35618681335480791, 37792988415804806, 57007713078904660, 37791896336636040,
      25756933965448451, 37658849909920896, 34488632587290102, 38446110855406727,
      37019480723261329, 37579660023938691, 6339739039729166, 38299870272361606,
      21259699564546222, 36506549946221958, 20694889824813211, 37972209951946885,
      40682615409051500, 37444445360593288, 26037588572210056, 37563187868364932,
      65732535400629789, 38171232126406791, 44336193714423382, 38349334537955969,
      44057617843782943, 38419718683973766, 3525427395987591, 37000222278386821,
      3524074516284459, 38079964071215237, 44904619807836097, 37017829446672519,
      66854823216775559, 37818273492184202, 24074565273421453, 37829280101072776]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [47997378485979026, 131]
    ) [
      5771003734820156, 38425202820650624, 8873189923587371, 38202012479179654,
      44619562799695801, 39865542584083587, 33360662550381714, 37924930935216005,
      52222084426139413, 36195388608562822, 5212190002479064, 37867753679718025,
      41806771536889372, 37519213980004999, 984911171912610, 37631375138118796,
      42931730845959538, 38189919394791558, 34203210521478849, 37230052118608512,
      50812171186506099, 37993102568735878, 23229131032856437, 35944686183228805,
      69112511411029556, 37817181177991557, 45184879284029044, 37057413056481415,
      8307740203253854, 37504917376163460, 64324056705369707, 37941430152813702,
      53621333164590424, 38534051702902143, 38427993754469918, 38087661860574342]
    ) [
      26322619818279192, 37515914807496585, 52221444463298145, 37868863106853767,
      45740832679101729, 37803991132043138, 64323966492509847, 38316363903079814,
      41523213499271110, 37355366043942787, 47154138958300816, 38011795742805125,
      41526108332722074, 36297642988611462, 23228267702747498, 37700628432441734,
      1837878900524753, 37482929492313736, 58970113590199190, 37747911358254469,
      69672429142181241, 38216309620045958, 61787710992320158, 37499422535363456,
      35612505263146721, 38110752091310981, 14221790046029800, 36148097495308677,
      10563792123693043, 37827072756114821, 54192563876366054, 37043118901996423,
      61231851947000000, 37547794084933252, 16755305328838118, 37911743926094215])]
private def schedBlks14G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [57849316203857622, 131]
    ) [
      2955485170599291, 37523617227029646, 20131411601361849, 37931529313590917,
      53627041230587692, 36415340946652291, 31116988756625508, 37721518146677893,
      64887818412262998, 36023865331517574, 24357332939214723, 37529104384035205,
      47153980037629303, 37595080936592774, 48570640541385666, 39339999229457537,
      57004865476920726, 38011794534841989, 70795103527405281, 38638495762010239,
      10280002257454426, 37773196837374597, 43776907401070213, 38646184390412165,
      68263576844534277, 37688531757667977, 69109204319307193, 37094797693344390,
      17313187228647422, 37585192713805192, 8591302638929179, 37954621272385414,
      32510357726266785, 37544505632786052, 67700420672390961, 37820477313763205]
    ) [
      2957052768911429, 37451041910241668, 54472320854754692, 37948026970915206,
      50525001046852959, 37765493158906240, 37301080232068678, 38053576362578310,
      49123308457985922, 36258053741358467, 66575835029341225, 37823776553226628,
      60947546702317211, 36067845528184454, 29700345257231303, 37326791576549765,
      3525650713970104, 37553299360541831, 59819121236870066, 37949117120693120,
      31672121849971954, 38105254717719430, 4929885959980767, 37557671872103040,
      3242474949608788, 37854563617046148, 32236454836143850, 38660478276449925,
      51656493045219586, 37540094584101000, 19570050804909653, 37077204819436935,
      22659962041303044, 37495039991304071, 30546891977164066, 37971115322560134]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [4650777526175227, 132]
    ) [
      12525630086481355, 38484564905950848, 42369884692906683, 37690733700141188,
      65730800232138327, 40046963395133571, 47712961503789527, 37432344088894089,
      43494788160259539, 36030463173055366, 24912393241788513, 38118477277602698,
      62353100476613848, 37673144852822661, 59251111810466805, 36764966400921483,
      49685704357874906, 37767699816105092, 426595577333381, 36434009491820928,
      3813181530606375, 37624758841698950, 61509410012497365, 36340508540535173,
      41530145488603107, 37427949314195586, 6621042219844858, 37162968404095366,
      14502418808143868, 38959556311360385, 32797519260386594, 37832571807448709,
      68257662592910810, 39301498068570497, 5775255852581527, 37628059624758149]
    ) [
      30824630286188544, 37414756029917318, 1554514118411594, 37946924137338502,
      18436613185963433, 37558789385436801, 44901261069681753, 37806183159289477,
      58975254764816054, 37118965205434499, 35892008845149232, 37666542531750019,
      55598633072428518, 36028263696807046, 41802927509110848, 37686324563753861,
      16191238676186357, 37640160292543878, 8866597057758165, 36890288949760390,
      50248237690880776, 37877652287507333, 71358135087761081, 36794642108256127,
      31387683325576685, 37650051031632006, 54754255390934550, 36043640367471749,
      61227952153594496, 37113494105172610, 33361405528671627, 37118987620233094,
      15354510232485885, 37148661582900610, 53627058366482170, 37904041606772101]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [26605739797415222, 132]
    ) [
      61220809652405736, 37787473107018381, 55590373795923544, 37520306847569030,
      15909810946409881, 36291088046096516, 28860292690903747, 36941971062855298,
      62915788448564490, 36028265525534085, 49684664880368651, 37107976129616261,
      13375389358720739, 37673141765769861, 1840653331694663, 39245441665413249,
      62354019637363112, 37576381722567811, 71358637600310736, 37852341676252543,
      38141407860720954, 37280609605106824, 58412403572901148, 37446617254875781,
      6901658232193313, 37408175384768394, 26886458837992601, 37250929099389317,
      42644771124838400, 36306464767530119, 18441762858109425, 37624760888529540,
      41799027672188362, 37337797614453376, 38713883884554528, 37451033789903235]
    ) [
      71357718422257659, 38499960702586752, 17598291427034090, 37813879556119429,
      14777425608279517, 38995832980267395, 20973439984894642, 37591775086755205,
      6339648860030425, 36439481800195972, 21817392492740809, 37678637662767495,
      18161499084457261, 36029364366075014, 42644212754449658, 36558240414364808,
      35612299106747814, 37691834956626821, 62353512717059099, 36921085022738048,
      57568085947090442, 37630259218431109, 71639915010164256, 36168988367532671,
      53627036879259514, 37512611507869312, 66575495728760178, 38934256453690501,
      8311223436017878, 37809457065158020, 46027109458085117, 37201451596251013,
      60377321162244094, 37197049372252032, 19567224718065586, 37702827606629509]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [50530588820210824, 132]
    ) [
      33636240466478480, 36885872918159232, 38431781831280271, 37277318032792960,
      43775451376420066, 37463113787768196, 14221390530707799, 37850139733868928,
      5494051372172830, 36029366630974597, 31667247084241260, 38524140193707650,
      29139414039822423, 37575281556635780, 31668110280983712, 37609353968161157,
      69665724741288153, 37350978701623430, 145829263869166, 36299846541538688,
      67697242394952191, 37618169204035974, 31671327289410673, 36840786331214469,
      56156759686808432, 37066208948024196, 44337228801672645, 37336689311803012,
      56438312013889532, 38052466515979392, 12812503870636946, 37411452545695620,
      54746863721153883, 37434525629915011, 28290372083483565, 37294897400908168]
    ) [
      142199918264312, 36215201829517703, 34204383006919203, 37592874413786756,
      17592128135857604, 37241035222510207, 21262529812924523, 37433443097033858,
      28294555296236825, 36461451665207940, 29704554381870281, 37375157186732672,
      33923307497096294, 36019470137145733, 70513529701826396, 38869386693958531,
      66292208262807958, 37632458107456388, 984619104961649, 38166813745535362,
      2675440523837501, 37448837031566469, 145661763356010, 36691262983614336,
      70228202233496485, 37444440746429577, 45182654458791098, 35998560441107589,
      6336994498740990, 36275679683159943, 71921935438677372, 37310301854848388,
      55595338729750524, 36067859016926081, 50249637758798257, 37511509647328389]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [66855295641224151, 132]
    ) [
      51087706206209287, 37488397740142479, 55871861780086291, 37266314812829321,
      59537457352049687, 35998619781824388, 15901521644650407, 36454899440889994,
      15626398910481423, 36026069069132420, 67133038220839705, 35805089746558340,
      9715385696553375, 37397157049017220, 57852051983140066, 35710509265458047,
      3528953423104505, 37188250510831745, 70233411985441818, 38304235317953663,
      15351224565662922, 37253106497061247, 47714494713857190, 36684655596203652,
      21256568540463034, 38691260928213119, 146172846440561, 37419149194171012,
      49398525556719612, 38745138323042185, 67131883035131684, 37172855720719748,
      49398860643009677, 37333411429329790, 26879853266239413, 37564288050641033]
    ) [
      44896536610635771, 39264122558599808, 50809976518508758, 37410352597856642,
      69102091829544254, 37808358928992900, 71635362440905226, 37254214262645641,
      55597000961131624, 36171208177220996, 19000645517082743, 36725381331377035,
      57847873051525862, 36027168362667652, 45458627503883946, 35801795389252998,
      10277511032965667, 37457632671581060, 15912675590505679, 35588471259154560,
      11410823999949539, 37210239736719490, 146031120254116, 36078825310441600,
      6626462340449952, 37125568651199359, 2679026722636814, 39751193643503493,
      53909478165086219, 38825400977758333, 7463641763643887, 37381767711455620,
      66005867261231104, 38974929223662719, 4927811565027104, 37264115873632644]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [144115548587079, 133]
    ) [
      64598414897218557, 37274002854537855, 8028764909569550, 36962842809166728,
      426496750027905, 36294330394071429, 20694494685659609, 38256989100771712,
      25478654425924070, 36030467769879427, 62067081376334094, 38121718820427652,
      35045449361032704, 37071698302132865, 64881689379833086, 37059614897964930,
      22382653109207151, 37429030236030088, 146215779795832, 36419690825903488,
      65162099245287224, 36432903705719431, 37299353654886703, 36650570047879811,
      71362971145766106, 36904592599991936, 58689059528149115, 37430139176594820,
      11122056225456131, 36336111802857601, 25764304110520355, 37111285871127425,
      58124219849671486, 37849043057120642, 56444758730833869, 36581307325120641]
    ) [
      44050436535582720, 38686866253584266, 64879254291578625, 37158561364945541,
      67131728341075077, 37310315964112765, 21531639726899775, 37658851436075401,
      67418198348235700, 35919387886085252, 15345486580123339, 35840270511562633,
      60380426314024746, 36009576814112899, 34204825333431935, 35731417770377092,
      57006686461069619, 37258616654508165, 44331001015534837, 37968904370517375,
      15631896387356772, 37087101078390914, 6338652393669517, 36918850196806272,
      56442551209722985, 37651143748813440, 13092376790992201, 35851225832684420,
      60944149308866492, 38517555287203206, 6338463415698859, 37434540192650884,
      25473504713080831, 36333939371303298, 20695766063351000, 36958452563844995]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [56439239734559843, 130]
    ) [
      63793791395201900, 37843540515945354, 23221881227476767, 37600548916577664,
      1270328979981229, 35719333059760003, 63753139589382067, 38353717518408332,
      55032612216078282, 46247121258761603, 45739127497394876, 36044792878016646,
      55027930736197985, 36948555398903686, 53630293020017399, 35800677305240190,
      17876368998894580, 37083809069370504, 69949725074949139, 35842424085756068,
      5220144040740569, 36210801652336768, 13093141294384787, 36502296334620547,
      18444266749984409, 38315231927829119, 6339288016390211, 36816610614582148,
      9146332556862764, 39234420192253569, 61511394353381418, 37150866981303171,
      20166217973596964, 38061257458088829, 5770497057718111, 37154169341628811]
    ) [
      68540194116697997, 36672558770563200, 20416275239766082, 37238826585966721,
      40954967825547968, 37743489034759043, 66577939529957187, 36758328193873792,
      9150507352425387, 35960094882587781, 37575975337427132, 38403195089208453,
      62069014131671325, 44126170224170371, 6896817674421403, 38177828071479174,
      11963779720380520, 36819910609028995, 30546011992458196, 35768788917976703,
      26318208903187608, 36926563236763784, 35891725335954263, 36130498816674724,
      35623264043959862, 36216299545702018, 21255035139163105, 38254916862675075,
      6340095434653485, 36064534998284415, 17034040019683406, 36860592321160579,
      5487742151861380, 40093137901083520, 17601302114500688, 37006827367756416]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [32513892496736730, 130]
    ) [
      51692171277664913, 39468646904246654, 8309818988529686, 36365829117622155,
      45460895288688909, 35546656365995138, 44059610772047451, 36962874065182591,
      26036407448209255, 46712212814985091, 33643129493880585, 38956242743846021,
      14222627469428812, 36773733016221825, 25191115551572615, 38227284016374143,
      10563040602783424, 35795156158867841, 63756820315604084, 37721497543856549,
      49960208620618137, 38118421107696266, 13938343541375312, 35875577441449859,
      47992014056686111, 37381790544847239, 8586518070329376, 36720954042549376,
      57847237318387118, 35538997212067717, 33354765476727275, 37408138156144775,
      55069703490798432, 35720408460279167, 3247538558568315, 36470283124628611]
    ) [
      54182195642672358, 39201435531304836, 10001538065268822, 37009030786539910,
      59290891844223816, 38155826547809148, 47147589217255324, 36834217732627851,
      57565354379478134, 35553246171147906, 38984608675366436, 38382352082186891,
      60662678622996204, 46363668535014018, 6621767946960265, 36299877109554824,
      5778086215191509, 36993629386192770, 15619506036114114, 36850718208336510,
      20138575539178465, 37135463030933384, 4647345795662414, 37898508732078501,
      60107322231851261, 38092065376829569, 5491182318158220, 35557816517441411,
      46032469599419945, 39387267089343623, 59814955240556372, 36789121364148610,
      39263738444424588, 37389477949979526, 28295006371546112, 36725346317452423]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [10839760887908032, 130]
    ) [
      40433532980462253, 36657182417997444, 13097973037957396, 37024439401546623,
      21254257753294281, 35394952181984386, 35607767865328375, 38689060713697406,
      15628451908585441, 46797973463666308, 22380157565175363, 38450466857753731,
      30829758592220835, 36766039908169861, 46028338373427778, 36361414847399805,
      26597588000800689, 37843569171938185, 30542485298316451, 36896851106288806,
      56718524236399560, 37421368618129032, 63194171071498185, 36724403437974402,
      31388714129587595, 35408161217462657, 49689402270910801, 36641787275763846,
      20404184869611148, 38244869625604228, 10847002141034799, 36416403867718274,
      40715562005463770, 37125581401060987, 13943407512158674, 38302041714017405]
    ) [
      41517565506921874, 35495015303994757, 38704649730820444, 37121173540153735,
      17352048021635827, 35070596031100032, 53912506083215082, 36521960607573377,
      32794796216910720, 35591743506589826, 71360918045623629, 38167902167823485,
      70232535763355560, 46652838616664449, 9153543794032894, 38513134792917370,
      70517987999383758, 36741835015881857, 10838442947871337, 36897936357251710,
      38984754719718898, 37387252787564937, 64038162144002156, 37312468447531429,
      46300380990045121, 38254800311161480, 57843277450936914, 36794769833350786,
      28568698741947892, 35959014898400129, 24913376693946798, 36682468652255109,
      58403723412416001, 35483993931598723, 3810445583812748, 36474672883367048]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [62068052093861525, 129]
    ) [
      42122919706264063, 35760003964824701, 50249392967290317, 37807257035533445,
      70511785986916452, 35310256249016193, 69397950563453146, 38506573206939520,
      38421254964937161, 46880435459995012, 46312514199059913, 37095874572833663,
      37298958578583181, 36680278302758021, 46300304295887347, 39023315838901885,
      18162654393892826, 35825957113982600, 39830837401126145, 38631881880500134,
      70508865498873805, 37568696767944066, 33641883960247133, 35480856156039810,
      61220599286169209, 38075549934888072, 60096266988717895, 36562620744279678,
      38421430926681752, 35721519229290377, 49405462049686213, 37465303331905158,
      17634648270078603, 35949124008395390, 41520713696839653, 35922724388103047]
    ) [
      24626240743581342, 39681933739017350, 19009729211501019, 36436194238126976,
      3560912323838600, 37001346569562492, 14507353931481772, 38184388030708349,
      8587561651701235, 35294857566528386, 3522107307231216, 38620887318719886,
      2960914072108836, 46904625303005314, 37304468833991864, 39187201204179073,
      22657385012166507, 36597804562632071, 27159005153493523, 37634628542553725,
      11963835596507870, 36851812216503433, 44616040846426816, 38409778182826918,
      993677319109686, 35553297490424970, 65164890971801341, 35275247582316673,
      47425168612293986, 37138790422503562, 38428818273831190, 36595603559646337,
      46299779620513429, 37011265729467784, 64889892851451633, 37124464374617214])]
private def schedBlks14G2 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [42082667223090001, 129]
    ) [
      17353529774211495, 35812787703535488, 35336484765206138, 35789689050690184,
      55593006587215849, 35002406767360129, 13095692460460604, 35088201522172286,
      11963921299638372, 47005778829219969, 42091463271416236, 38491146506631043,
      15631140424091799, 36542821683065215, 27728101211603380, 37866650578027388,
      15349871807987423, 36824290502932860, 1549952797605948, 38550511477237927,
      22376884950304056, 38422966635636360, 68820440729091919, 36389054689944961,
      59819658245340267, 38465900017413766, 2673323079597045, 36485652497267331,
      43483977615451910, 36855110835766919, 39824309155694668, 35808358451605640,
      8627891392315890, 37820480970586749, 45467449455839158, 35895243156762504]
    ) [
      60378012416583336, 35620360871190921, 24350830462599965, 37358649932206983,
      31145537345979030, 35893050240620414, 60380293045389124, 35797382310508423,
      60097804557188727, 35310259940015489, 19851727526005282, 36204203307465086,
      3516742829246401, 46944206530456708, 11973975779606192, 37763268752105855,
      6341869246908433, 36775930898578303, 43205166183317968, 37932596579688572,
      65451906567142934, 35619225003885182, 61222793899574086, 38974923065988262,
      39263579666939533, 38311925373223563, 26602544224829207, 35841497245011074,
      40952657225481305, 38379063009474182, 56997697226636716, 36534031445292926,
      37291407877383913, 35456529192589194, 20122469531421653, 36607685872787336]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [29134131234308936, 129]
    ) [
      52538043593097760, 36266871309018236, 46024962128249008, 37545610094057095,
      40393937661101137, 35372924653737345, 50243981284181807, 38394429211573643,
      71921523138594957, 47034365343038849, 22103866628668641, 36528564320901760,
      35615971348940763, 36561521954005894, 14211126168158604, 36200871017021567,
      48563549570893548, 37154174962008712, 8586672594191221, 38177791077581479,
      52219060651261927, 38412025810442368, 47433217301972582, 35207080109506945,
      47428226615705626, 38645086338369408, 47153988669507745, 36444968772246147,
      61503079079716638, 36634081399638919, 15912576959479814, 37736903222900616,
      15101918933188973, 35849060984426877, 62064963949920493, 37758911172291720]
    ) [
      20966048132278020, 38578050002495878, 41513803260135571, 35731394315394952,
      23546056567521788, 37891944981761403, 37868106237838839, 35966711479788424,
      40112398219510719, 35072752778412929, 34203420988900797, 35913934284852879,
      4930139271760021, 47012375076932991, 14502216864332790, 38617672266682245,
      17320149286488148, 36619781323102080, 51364994163835276, 36430683207754108,
      25201027853488616, 37216821841532036, 2394240292388742, 37765461869091751,
      63211316488929902, 38444998895078535, 10836668563882314, 35043252524649858,
      65444849896750308, 38251486627645568, 24350083152905948, 36466961638511748,
      54743590821209870, 40885892931467142, 41525945118655665, 36259163386647432]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [25757092940906693, 129]
    ) [
      14538685509501401, 36303161853290110, 39544470379398594, 37656635568555399,
      21816507809169548, 35151929997184641, 54189870883309713, 35882044571316861,
      29696149157937891, 46942005292572558, 67985653600452312, 34969407960978310,
      52780090726516613, 36650631317975941, 38139097637028175, 37371883683355260,
      35051891596099033, 36153616092084094, 49118828730289393, 38432863934219174,
      67692715485005940, 37289378737258874, 17604914187961775, 36002024952779394,
      59542070215736420, 38141488537706115, 38709030649167264, 36404289627367552,
      12521635680659101, 35806159395485320, 44610715180498063, 38479061408128902,
      66329784872436244, 39082723876036218, 37295196045214234, 37606082058439559]
    ) [
      1552070138701595, 36154696225729672, 51939471298101122, 38297652374672518,
      25516445825663302, 35741309499416445, 13369264673948049, 37723718411447688,
      24067474312889023, 36840775327617921, 24350409405466668, 37303715085881983,
      2394583954261227, 47016772083204234, 33363853578632580, 35709384302782334,
      67980903483803608, 36398829582497413, 34478058929094986, 37579650109034879,
      58696034509422227, 36274563226774146, 69384992679758776, 38388892847421862,
      30819639606476219, 36919959808878718, 39279423702664671, 35423683161966465,
      62343724628278779, 38170088070582918, 50249706514055493, 36389993879243392,
      35885304275511007, 35436736657858696, 47429201570135520, 39858948433891202]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [9149205811529162, 129]
    ) [
      10879124261273761, 37216837309528956, 45457996264930872, 37528017034808711,
      4363504181412670, 35969956934222209, 28849413501191275, 35429046384832391,
      11966644411467846, 46863938943489148, 21537918813699148, 35906232384391555,
      19571536745498553, 36198653102388869, 27158348020678930, 35655525530389888,
      55881349180131066, 37246528687449472, 31104172496091980, 37424629790043558,
      25199421361390264, 38305344074015359, 53333969805215036, 35039951053723008,
      65445820535832792, 38289939469075838, 5494506699588331, 36338313224435589,
      10556404637869634, 37809451914407045, 426462473912104, 34486755306845832,
      44374229878931710, 36846306202817148, 44612763857092387, 37496129537229448]
    ) [
      4640396380513937, 36397681568622983, 71349936025076106, 37632438796915592,
      29456515678175685, 39460949299330426, 38142365502831808, 37589592890408327,
      15342123615944999, 35072750396015489, 3794769160668515, 34792428565316484,
      59252009551038733, 46863939312639874, 26885921840200552, 36461477820620426,
      34771988576634764, 36358107152098949, 66564045896646975, 35115690067495548,
      69673369658689124, 36573628426932090, 34763579126939716, 37112353505660582,
      31955108539959103, 38473538969506432, 60375512811210091, 34886019979485568,
      48561101484031428, 38165698631391613, 41242017729248002, 36330616039295874,
      70226432517645950, 38150296056434307, 33631193930629112, 35313577179307400]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [29697231419507118, 129]
    ) [
      22134391006659348, 37266319476597117, 35041875930415833, 37430158387196286,
      20129229569689956, 35383922504404353, 53062841398232354, 40129417992623239,
      9721287041648607, 45569814680554362, 16190435385834921, 35540101153335684,
      53066694140395019, 37212396213336452, 3516215120396614, 38287761450800510,
      29130355809159684, 38686885782479756, 55029747446741554, 37434514657406112,
      11412546435843082, 38227317234719870, 2386316197069874, 35833788399433349,
      70513409486126848, 35670901580774278, 37299319320840270, 36371313857395079,
      12244691924134413, 37788584715144579, 9997771190337659, 35696214305578372,
      44666347787617016, 36610997225646977, 67696898743566860, 36529632492775041]
    ) [
      15623014350104060, 37718193472759941, 68545339591524092, 34411991502500487,
      50847772091842903, 37216841805912188, 49679128750227306, 37488432754622602,
      12245829983897204, 36152478179626113, 60375925178336572, 38109674993537925,
      7466562360215529, 46518692778981498, 15627614301420754, 35675329154502533,
      12252852494174259, 36580176658144645, 58965591594402100, 36054657109670013,
      35048043362092521, 38385622314378377, 41518905574193679, 37492782532458916,
      43494504601257153, 38248206982735230, 34192670733337888, 35202669245185410,
      64885043837762601, 35858916206589568, 12249768698743799, 36382301843229833,
      12240345361130412, 37884230264716677, 62361269408726648, 34360328062307463])]
private def schedBlks14 : List (ℕ × ℕ) :=
  List.append schedBlks14G0 (List.append schedBlks14G1 (schedBlks14G2))
private def schedBlks15 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        157666429737054, 46115244136726656, 66618248507795430, 50604778338966966,
        19878902451711097, 616371061657]
    ) [
      3003014092143355, 42457205007361444, 157142405518300, 49877853205954688,
      55679001886837830, 46905916699089852, 29440156588286056, 36029411527594644,
      28623627539873792, 54516918238433462, 25237625951729547, 41921735110224034,
      140739888845262, 49584323851797120, 17111303647382639, 46316568148403641,
      6356824756821603, 36029346784157074, 59867251343203221, 53328332428177078,
      67456007662777340, 41219136643826335, 33073311911022391, 49128033976033945,
      31178790402050886, 45508413528993205, 16486947461176231, 42501072224256143,
      38755077641774759, 51997891649541302, 69422759027191884, 40337315634587036,
      45762281685942272, 48584878553909413, 28638669414386280, 44541926802470065]
    ) [
      22186802471272384, 46527663676903100, 62379772679987732, 43700757590706844,
      69414065748941624, 56878738280808575, 5814237607672376, 43727152698333347,
      10582935135820331, 36028359328234137, 1363277981057024, 46925703714204614,
      2422458695590329, 41965704736888473, 140735677895795, 57005148872028032,
      22424405233156085, 42890417605142436, 37877469380253109, 36029346784074895,
      18250329076057280, 47257765856061891, 50553124925448703, 40345005353860502,
      11118263727590717, 56308041152058288, 62113485070581302, 42846437173601188,
      71653981248066926, 48873841618845838, 795603411192877, 47243472674575296,
      4109100925100465, 40224056658844310, 68304705301807104, 55520780407773877]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        160831955904756, 39820424036483200, 2984429238652973, 44383578101900702,
        16213323757037909, 628920983209]
    ) [
      14259543390856558, 47034593701665697, 159620732657515, 41862234091028608,
      14253238206045007, 44329752951406757, 55355362702832282, 36029421678325919,
      22116966195429376, 46307726940109977, 41836145445675999, 45169777823092388,
      140739932363162, 42593508308587136, 31986393676619152, 43544682741350307,
      49435703590303076, 36029346784338841, 58429682416252877, 46014158862270619,
      63500484471661408, 43312662300466090, 25473487539835403, 43311497623879543,
      7497490886336176, 44597976091994273, 10584210934837735, 33582933411365010,
      33099670435892997, 45285181713538973, 38445053939655950, 41152086618353837,
      21804670641012736, 43901945400871310, 9465977476980455, 46397829516322208]
    ) [
      8320491966201856, 49537029652304290, 7264124517722882, 45375368024889528,
      157967095077443, 45157545433628800, 16799247710135791, 53659262290230953,
      34800379069640401, 36029414816166555, 20722691227746304, 48839943894046372,
      44409140577544766, 44046039055382961, 140739904247220, 45746958090254464,
      49169406905263825, 51263399509214885, 29728177238157759, 36029346784230038,
      45494731464868688, 47601899555725989, 33139167847033473, 42539686046218923,
      50524760467083384, 46151588353033344, 28619792287966871, 49052242702809250,
      49988031810217120, 35600537248333968, 62384583025989712, 45983423120421285,
      42698635392363885, 40787038858857893, 30254778277724160, 46357202278885270]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        137948623110020, 37523608234360960, 42652158539629995, 41686399355448201,
        57019820851697411, 538240699263]
    ) [
      57590750859858457, 44787041457329562, 166960594066332, 38254747429372032,
      47724570818414795, 43332414182110352, 34503429008038466, 36029450265332134,
      16193033855074304, 40346081980707976, 49708291897267199, 48264769489537945,
      140740022272621, 38200912530904192, 22111335790512457, 43079523622162322,
      28332187890128771, 36029346784484998, 47155015137263962, 40715521259894920,
      20433790513878503, 40560560266044311, 42643461119184676, 38300966982140034,
      10572017103440319, 42465990916206484, 45771069457600376, 37091475015598216,
      7467382719153639, 41208106462157961, 1572944123631460, 36596862085823890,
      41804383423332352, 38418615934254725, 62646571436902991, 41412653223476885]
    ) [
      37003885591691264, 42885982765121676, 29731033301032188, 40806882245554077,
      161278670513878, 39339937891352704, 62934579138563607, 44539701874245531,
      68836397206904088, 36029428188259488, 7752615540195328, 43419253789969805,
      25506971614944468, 42861794836506777, 140739961659428, 39486255883880064,
      11145438310272837, 43033365072143772, 71651924137059365, 36029346784477599,
      16478834048071894, 43715031628634510, 53086421188058182, 44476932756576923,
      60657859628668108, 39780926376983161, 34509570807664797, 42067980306916251,
      59278548211837934, 34613175806591125, 28864815359756481, 43605088804252559,
      28027649212980170, 42483560402128808, 24061925063163904, 40050310198683016]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        27679043630566171, 37062899457327340, 46025455872541632, 37463130078721155,
        49130493966845563, 424573458315]
    ) [
      15630960213263927, 40583597984140170, 53907841792119178, 37590687906005223,
      1554338019116404, 38708890309144966, 57860646482775077, 64174535993696401,
      30546114625110016, 37662145340862085, 9720621364446823, 40984914661665419,
      250243470887805, 37491719931342208, 709681156490542, 38902405597160070,
      34780471487008198, 36029781193308812, 70515007226873314, 37624760435539332,
      53068433499850344, 39341140114132108, 9992365557243333, 37383966080430213,
      71922751475647696, 39331218000908421, 40966452702973715, 37227814464377436,
      35611521695319194, 37584077397991556, 3530164752451205, 25258576294160270,
      6055613977127793, 37238827324286852, 64604238867039257, 39713852006819717]
    ) [
      11970140425977856, 38122844135454853, 32525695176444155, 41414852649301394,
      144257615102916, 37460943319335040, 28014463307908435, 40777093156059528,
      8607189986678017, 36029411946299016, 14501504091652096, 38243791790263173,
      61519391614470539, 39291693112251027, 141556201977494, 37489520186789504,
      63199234834138537, 41224599774103432, 68555402908701514, 36029472330162026,
      46026941953509588, 38396625584272005, 13107542473214538, 28921085933355411,
      69102110706415816, 37621462739543688, 38430072545707537, 41355449274723977,
      55854016312414726, 38488954301964210, 61508379207435624, 38516474012661381,
      67714817557891844, 45332278914663568, 33927022560473219, 37641254418605701]),
  (4,
    m1K32P56 [
      36172208124521579, 37102486540243331, 40959468935086983, 39018950776174980,
      44878923109928030, 36923258947240171, 28010636449907588, 37140970101522051,
      60948714917561571, 65830496504699787, 53060672395378688, 36830901379975042,
      57846477163496195, 38508771206775683, 54508570360514647, 36288834211717248,
      985920490668270, 36398786330815361, 40394302738039095, 8663169])]
private def schedBlks16 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        5510587210235904, 38828749877972117, 41013542098086735, 57161170887296433,
        20737612715377033, 41348855106633887, 39557037732369998, 49133283431881100,
        62408789678795360, 48675070704529096, 40830]
    ) [
      26342548753711104, 51120305977086355, 70903883842961768, 55849479002469596,
      35655906683960343, 42449470993989796, 13958796453778644, 64543325661940903,
      34566394313695023, 48551910302459334, 60675945735955501, 39917285902022293,
      15960312040101775, 58326718663842522, 35384061198321307, 41024428110503340,
      66022033649210835, 50660703355135636, 63006791678082778, 51167693227150031,
      37295437158198337, 39801867212336275, 13387934988079451, 61060053128293043,
      26106386538549456, 36029497176991158, 22118534356702233, 39055319502862476,
      41575896313143108, 54001177692627921, 175911865136828, 41613864085788032,
      29716090840845336, 48936742388129418, 40191830717743240, 44771755016254400]
    ) [
      32085336858525696, 65160279280250877, 53438115677725448, 55274417257682132,
      62962209296662061, 42378051828318374, 21670764255247729, 61027145662994932,
      52857306988205037, 49357862458988995, 37046964113680004, 71338502455474070,
      5879900151739960, 56504787596943833, 66065662564811544, 45343309784557998,
      32006833275377284, 65602291712344061, 4447983379277134, 51194070802004168,
      35606587335880316, 48703495969589152, 25032851769640909, 58618099395531751,
      27791151781955471, 36029507763573173, 5790636341173431, 69284481725689755,
      8683890777254447, 52737806434964948, 181581245756647, 41115780940096640,
      60994963873567805, 61933172554602985, 68049881886676091, 46393537754066874]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        66553170049350123, 34182211558711191, 60089046859548314, 27378252144762751,
        31955760753368661, 37724595565471858, 50260521611002116, 38075487187818362,
        37841717982887106, 32229322155777635, 29430]
    ) [
      58984266004791296, 34205306352146326, 66856665722879356, 40683811269377908,
      26080130598873633, 39339002964213923, 7189923679476172, 34379004056238455,
      22672709341777967, 44604545562495374, 44616590569808687, 39805164287301009,
      49110848595849220, 44456949261592960, 53095504713584639, 40194296831362963,
      27464961169919859, 35505986277186705, 29690415224029100, 46438374089332117,
      52776560756231042, 41483032921675674, 71362111990697217, 34071070671243888,
      37272269298489128, 36029431509032086, 40125910448695095, 35840192229699479,
      26310722523327408, 32360305066847367, 7186960285137708, 41046529068507776,
      17021730787727300, 33344323935441284, 71629001211812380, 34841984299140727]
    ) [
      54204856180899840, 38874926262773397, 32511316360596720, 54251733868659113,
      45226528421823291, 41819447173841055, 20978671381222440, 24293340510259595,
      2999105489778836, 48960952435023795, 29981128731434971, 37333434516010903,
      34217465659688166, 48016369655409541, 55092768401172141, 37389442668838318,
      22115025279095781, 38194331332722567, 28613023087761543, 52159382148164002,
      18999563622395831, 40958532909111186, 8311103322884625, 47149970477500292,
      19600683154578131, 36029489627559604, 45761878233088020, 37204763519746703,
      62953060493788365, 44596928169991313, 178063712955183, 41762270505667712,
      37574790016372812, 29171792417775485, 12275616633626759, 45849280788837541]),
  (6,
    m1K32P56 [
      17626710216210597, 36529719986752143, 162214491878668, 32395399630751376,
      33914503000781300, 36456851981161860, 31681747196281476, 38001923456785795,
      49679226751582086, 40170375955644738, 69345790171191063, 40073433111881630,
      59539514384613039, 31134193810150521, 63316142407693422, 22720259162691999,
      53359417923255337, 32625290508789395, 18394883358226454, 66638334835274563,
      33765467539082805, 41560994196528983, 438092901096321, 33091547292698987,
      24295308863235129, 71337944021959845, 63458977462250970, 38454941407870335,
      65135281291035982, 15299125095400640, 162648847988970])]
private def schedBlks17 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        58469372686875449, 64586389508447968, 39053642739011702, 44791520304264631,
        25530193991401472, 43783637927960482, 65857141697532337, 56406960559341305,
        42977601923432358, 36000759482813606, 46053270998854777, 52781655399801016,
        28710168447340325, 51906572540688349, 170826533548068]
    ) [
      15121990349605141, 45246725500080820, 69382611092275200, 71281328420605138,
      29515766443474878, 54793927656473046, 66056690223724925, 71985576036827303,
      45244008776893715, 68027882831593174, 55116807810834269, 50580542575618506,
      176208140348893, 47625884051422848, 53761439889082865, 61012880081782271,
      10067595716251900, 47097226789736382, 60708802235768836, 57219301863067322,
      61361098214327811, 57170010889258997, 15119499247862869, 36029483285154734,
      12635182285619256, 68049525351774643, 39375456936984481, 53467897557421524,
      39590161072305886, 51007994460111007, 6929504236379089, 70617206269307088,
      48076931256088972, 49312783354723781, 10273839322933084, 58258250474536832]
    ) [
      43062860378046464, 62547788397390073, 46112125406337664, 54379396572274638,
      12016385257618475, 36054635552854954, 48127956072136638, 60224492276161009,
      23865736560366088, 51319411822340293, 178179567562865, 71958636624102528,
      34037014300392817, 57800027528622820, 15129429328251174, 47709665201873595,
      69434908765888969, 69753016458113222, 32897825535487162, 55228231024736470,
      48613213242900382, 36029490734378159, 60514321812029374, 65174581555376382,
      14025038983061496, 52428833768583113, 18763005660345608, 35719833152651425,
      23080308127805488, 61686867219250166, 46096354165708148, 49240204967005630,
      53620985764620424, 60423258758845439, 1669183178538754, 58305817003931107]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        32521662020616946, 24144918861874374, 31145271209684727, 45209481089380765,
        66291808752336896, 44979380209047452, 15150660035650606, 33009354118451350,
        10902841589278571, 36087620901766079, 24405346846011290, 52227495331092166,
        53416244908425269, 47500700346439011, 185893432371363]
    ) [
      69514337138614900, 44079052004049612, 10314774134685696, 32866236197036711,
      63810977380812629, 51452375201366947, 57355649740568179, 36125004296687787,
      1587250661598421, 58647762865930925, 8862849426472831, 66686351166356917,
      173287684099132, 35576536769775488, 7516350428256500, 63635923309146773,
      69703293552724419, 50786239250415289, 50806566156279358, 38215161489476779,
      64407795365601902, 42218847523021785, 37154416183389249, 36029479612335315,
      66043138752872484, 58739830843984510, 31626698837317542, 44578271315211514,
      14571586388940714, 37230014470553759, 48615347453009739, 54396745119041710,
      20721201078970288, 60619041942995374, 4362864817588748, 42953052236093056]
    ) [
      36787092818919424, 70699343625666221, 19892234714453042, 58711667357236982,
      10327140298834463, 35979868761711527, 5271396418368584, 43297419644968361,
      64449238847697654, 52355189995563512, 171028407365867, 49368839820925568,
      50023298285674442, 47772436146320890, 12347296406952487, 47194000187973320,
      26599297252367286, 56275745595488172, 31181898826700895, 69695526302609815,
      16254436053282619, 36029466440887986, 57605341057417211, 46380465230543017,
      49758615737531814, 62280700518978981, 8629391176877037, 50469233661837468,
      30800970028912760, 50925544434117073, 1029274658317597, 51494286167090423,
      28569712758597907, 45920683145505920, 778512709885954, 54744128184559703]),
  (12,
    m1K32P56Cat (
      m1K32P56 [
        69628552951161578, 39845835866669791, 4903699456978322, 58470711249729880,
        50494064381024329, 33863621893544123, 30562329260736356, 36081516241490341,
        39338208877837861, 64323192481546749, 34251131108249670, 54759753601736579,
        15349692116936221, 47251034078193399, 6967290971732529, 67300912653041857,
        62124216865940556, 51170920675616709, 53902642638064723, 57606395113481086,
        51629122268948859, 52924256598564213, 37020091363224015, 71338034891742884,
        27429089210958218, 43937359504311443, 16731716800893777, 42372725653109606,
        8905097501560915, 146]
    ) [
      56708937850847234, 37435788217120136, 18253986887071786, 62886968367505095,
      8045885409366054, 36073327385721504, 48869089561381598, 56509020550654832,
      45112414817213388, 48152562063477144, 55092398325472213, 45268549417053312,
      27231572875603255, 31808518109822132, 40111587969954829, 38115281018642372,
      38984484579360389, 56499335281911671, 63458946872622729, 40812490419017593,
      49419336129466167, 62002258942338737, 35594526303944752, 35987529140392835,
      61871090557818431, 55877586483746708, 54761330039360516, 41709424613671849,
      61290797052502440, 59953908880678552, 24039487771288079, 50037325412026569,
      10669779373493678, 57863551649867392, 29744215169869667, 40742824483858327])]
private def schedBlks18 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        58478701817286628, 44173585525060023, 40673136282211971, 53463429916611437,
        44981706835280175, 59171179094747354, 21879326884874646, 42473713385759152,
        2094674877644800, 53604189216021926, 33182808864965215, 57174425546054617,
        44388773637505874, 36029447129748392, 41559007495618560, 53786721366912685,
        16849035475140656, 55273332762561758, 51416430935981301, 9949088]
    ) [
      66960111798449396, 52156177165958876, 4121693989613778, 42053676404839072,
      32540572757557248, 64227857982628286, 33176878183216719, 51073138465461719,
      2148019025325420, 36029438908499869, 60999009091747840, 65935360836754114,
      66103458870848659, 49880147276771281, 46898756395772309, 36029346784582809,
      37651116519292721, 67373521074549184, 2484238516413508, 48589297976123084,
      50553648944686445, 33270672109076629, 19638492052237829, 66597290594207431,
      51173357778099452, 47189595849900229, 164830560297163, 47891910894813312,
      66922444214680863, 63640729143621593, 68055594220246609, 45727220822688190,
      140740007992299, 52228625338809472, 24983149449756496, 61259207040316386]
    ) [
      31240911358820280, 53072075351586793, 52264536589055566, 47078512223961771,
      12567476527998608, 36026216056522150, 52914486077325312, 54038573940054772,
      31433906545670052, 45859137722429353, 10309405972930997, 36029346768500128,
      46440562011920440, 54381630896208626, 60424059609266151, 44150475966317990,
      62933660121406023, 61056430454603923, 30390290854041484, 54303563725036269,
      10039411705100176, 43838210570335398, 162794669512957, 65759254706913408,
      3923684507249001, 53878044554376680, 54510950469056045, 43451176471023524,
      140739992131502, 63221626316661632, 29812158100664886, 53125964289721314,
      47471778207675355, 42802455148145570, 28569712283653433, 63128318420532652]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        55358291654257995, 51140245131885480, 46584110793137843, 40053652155770034,
        53643903452745419, 47943830625902490, 43247918381837421, 45273195251033278,
        14551961231720448, 39837012526967476, 24654506311126929, 48435310931333789,
        24959616841460308, 36029502630893766, 49455653669863424, 39962352187892116,
        66035262101360876, 47284129068723360, 38771630286940212, 11100353]
    ) [
      53954825073696501, 50348525991914419, 39358431063034187, 43704105653365696,
      4669786944471040, 43789800768622252, 756956504498614, 51330378886367157,
      20764336591723080, 36029464427604148, 21299990865608704, 44577054784853144,
      32565123571492284, 55921911291788211, 41297814747665537, 36029346784979368,
      52521001891632748, 45374213281160595, 30594781552225077, 59975834587383730,
      5535095029092401, 43747918410154140, 21834276235751020, 46667250766716308,
      29186131076426943, 60414642335977394, 172179545637352, 49631558507692160,
      42100564650727029, 48085633920066965, 15112304940067919, 55666991829503658,
      140740128387207, 42226409974572672, 43228027915767689, 47980102748597655]
    ) [
      13087222764961792, 52026355720156838, 68042309647777022, 59145915626641111,
      15118640249423362, 36029451290687917, 37056855550361600, 52700367337371044,
      65513501588438262, 56452061320759515, 55361113600278175, 36029346784798115,
      28888219142426638, 52708075814090407, 47517055957581314, 54136433746819799,
      33114200789137184, 42434002014961817, 61540634843064690, 52576143713462188,
      23885488802872077, 51823019254081755, 169361938034484, 48063617932722304,
      39589800029953297, 52656407223557808, 43584579933287951, 49487617297126366,
      140740082116222, 43866853841064064, 71402545526905974, 51754803695950513,
      59912061572921444, 46894929518827467, 6333189123513096, 43255451272086426]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        9445189479860289, 42157042493292177, 29977089259177199, 37628070932838542,
        27449864080688441, 38092059655460997, 24926386207033939, 38783694984014742,
        67141061222399291, 37366372703241605, 10842264906204267, 38038180297236869,
        22395954673715147, 59896506304098966, 37015666715165104, 36473557550748801,
        66852289130234273, 36836398652880257, 70800403520455691, 9045890]
    ) [
      25483490661730394, 40783696467048074, 59000616931137142, 45775484845447073,
      67161281928424692, 38313073539352477, 11128623336359982, 41939285922631819,
      61257265726397038, 67869070654038175, 11428932108517376, 38322962248066448,
      60388350580328567, 42273553681068171, 67725520889420442, 36029848254465173,
      58140785836924825, 38189920133026696, 29988271425488986, 43083895227259276,
      60967445615057639, 44547263371393919, 26608351263822655, 38254788114573447,
      35055954873125011, 42828825038527117, 2109870934301704, 40359337306095866,
      40398997233896300, 38196512790332294, 46597897795569922, 44158139613056912,
      276705431034336, 38731996630115200, 70797435692811876, 38278978460821637]
    ) [
      8623957175468032, 39124521425580466, 23523241926954210, 47104886761604503,
      11999969616635705, 36029552610255282, 52547763502415872, 39340020050084243,
      10858564512550238, 47155466377136793, 11722196878468101, 36029346786768059,
      19583760992080283, 39471963055950474, 1010140096466595, 46040564925500060,
      49173456866420090, 39902926247821500, 64609457492109930, 39694067827325576,
      53929703499927693, 45793167494296737, 209983782820489, 47135573495775360,
      27734641956131490, 40310896769792393, 21564711191089450, 43814031632600224,
      140770710298207, 41185113556462976, 48564425866250685, 40335091394368137,
      46055297655083914, 41812911477368223, 68820634896872472, 38752913306241173])]
private def schedBlks19 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        3292786067341312, 57926261783924161, 22503085720256044, 56887427458515185,
        61563961336644677, 44215364181650608, 8364120241438720, 54736603768850857,
        29536983384833875, 57019379407252465, 14558250115253426, 44163686178877874,
        37620423851081728, 43037989579926939, 47263987951455056, 57457018019993327,
        27787930510476554, 44109809773670066, 66334247319470080, 50932526702783398,
        22453490812106374, 58723710779979500, 57061590084470212, 44053736408717746]
    ) [
      29421513815785472, 70854714374031016, 30921753937243536, 54620214349066200,
      13428239834398054, 44547422917689520, 12590111157092352, 70694150440566485,
      45276179028310252, 56007806109790676, 62123011366960510, 44490247256061615,
      56790559409864704, 69664879295724473, 28678570079025179, 56676300555775703,
      38760201751413185, 44434171089284271, 12645536923877376, 67488801938419879,
      30649689599440781, 55775801573130715, 15960475274298111, 44378094939284399,
      32596725161689088, 56469604833309886, 65007216088969528, 56425629638540251,
      68034312368603684, 44325317374500014, 23272398403960832, 53096288494955996,
      18565167711838511, 56859934550570725, 5831275981358055, 44269241241278127]
    ) [
      34900086828662784, 62066192741112052, 19371994018666836, 55201840228971215,
      18215818446028815, 44906970014864818, 32042908450193408, 63673734543213821,
      49770625772869935, 55064399027316430, 64940235076124569, 44845396172506545,
      31093918246273024, 66201524174082303, 8674699399652038, 54928057404398542,
      39607066258358052, 44786021437289649, 62342605643350016, 66097092581341949,
      68071984122488194, 54792815242777037, 14273888850591408, 44723348100081073,
      68818398418468864, 66740342887441657, 6151539357509244, 54658672727036883,
      62124222567661120, 44663973364865200, 13658885055217664, 68811830461208513,
      29235459628197558, 54534428668372181, 37635491565190608, 44605698141277360]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        13169497152651264, 55012686896046747, 58745942606977984, 49438023510398393,
        36241117222582903, 43638155005845470, 1868347277279232, 49335803068721826,
        28363459756007645, 34923705882686137, 43818100979580229, 43821793681588699,
        62687141479088128, 37876510028127149, 13989167278573567, 35609828150770867,
        33672829924324845, 44115388184012237, 18507239562772480, 45711734223815569,
        4095830363320741, 54774968914173628, 30294795287632650, 44578307074068664]
    ) [
      6361724889300992, 49305045398469295, 67540507068249375, 53874633912793474,
      5001536230909495, 43173029927010231, 56181627535196160, 43193965660749708,
      39960855692030866, 49726199525590416, 8668819813621247, 43204916703797178,
      68047118933655552, 39347927321658294, 26598082777953006, 49381005618301677,
      24724627168347388, 43251097819652031, 19054061913473024, 47712958181787341,
      60147811522422243, 49974735253028606, 27269042788544548, 43328066670456518,
      19340712325185536, 46699121705634229, 46100820682972501, 51900924121140859,
      26989096514530195, 43399539305425103, 65508857680461824, 48803648482705560,
      64373733374010148, 52915611944016994, 51182621304795946, 43488608102780376]
    ) [
      71978431347720192, 58917051664113589, 62965602709379761, 60871082473559761,
      2737022666393672, 43983367731657907, 50840045425819648, 66222183347860143,
      41033266053558914, 64311453517788862, 71980322224524450, 43823937723560882,
      53923488349126656, 53948258944421301, 57942057759987022, 66178416811109297,
      11463962471945237, 43306067243565747, 9170474585063424, 51345734971411603,
      23559113726217181, 66031067168780731, 49464437306219755, 43030090110215091,
      55073392828907520, 49429303132794026, 19855735934858175, 65484483959392972,
      24415127321568352, 43192818837778612, 12025459607175168, 52637655646776261,
      26919016287484625, 62755411307478968, 10626040547043232, 43170830014531765]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        58424343493342905, 44606824325699445, 33119011482414173, 41295851657438133,
        35025302837242191, 32563814647321816, 1556060209019347, 47086187814983532,
        5205615506721774, 55411576865597631, 14160969247018747, 34217506139978190,
        36716097015839720, 41512555336289391, 66550903402747186, 48999454264950007,
        53073329465823016, 36714513689663683, 22923531097734424, 45253207408883602,
        56778843414365314, 34802534426044622, 51729472891012558, 39242300568391093]
    ) [
      34497978334740491, 56507876866220691, 27234278341191238, 35663430572130950,
      47707615704999947, 47949193596990628, 56717506309685256, 38594587019943561,
      39092979706340120, 27936908038321846, 60383197832910056, 45493968144297635,
      51957587327815578, 31115733370170487, 63255985055253048, 44995759923738814,
      1364663818437611, 41850206994111902, 57289600248039571, 40184538378772077,
      40707071627147974, 50016437672110010, 29227863988474374, 37386230922758796,
      19259954060061877, 43056404183755399, 53133807389801471, 37756917000935360,
      70030169269885181, 33838149983528579, 47967519760249447, 40417571359491477,
      24136662441297462, 19500553188874704, 4707162455172681, 32281229069649335]
    ) [
      5829273498648576, 50632197103290507, 63529076389023870, 67552226521918921,
      33112783505813848, 45205045008810404, 35362301849075712, 51788798292608657,
      67797157329544485, 60663908681559717, 44091269599497299, 46004390162419610,
      51159891649593344, 46805566429864094, 17370027678151582, 33875654511864712,
      8063807891102417, 47080789915552156, 16819944490237952, 32666002823577228,
      42397502938519433, 28355876930181043, 39591624520036990, 48140675033119648,
      23283638341500928, 37890992757727359, 16811914191605495, 39267495584478152,
      67456827439108098, 48932262989948324, 46348338567479295, 50605782199274872,
      71732326354167378, 52921352847511215, 22971687762358828, 49008068793997476]),
  (2,
    m1K32P56 [
      69372090575551874, 51551358894962858, 12588595294683028, 16145930126123710,
      2742334607993206, 40836599239864990, 66592976849403249, 44967471976261538,
      5538895651516462, 25854394644288680, 9756940095733504, 40977297335196031])]
private def schedBlks20 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        44122739240980172, 46357243887781562, 23247616901226384, 36043640435464596,
        63812346327640535, 63975935602628282, 46101289183732407, 48946640748084162,
        20438154337953513, 36029421510240408, 53102725050499066, 54691636717220274,
        49222497953829169, 51915358935966156, 37052286270484712, 40962945787165341,
        31706644726710272, 52350728042187430, 55414023488062474, 53843935047702240,
        48602587373877760, 42070174280368036, 8021965969330597, 50522207203620515,
        34834812208068315, 56903975917625288, 26376707267412116, 43562239426739630, 2447021584]
    ) [
      43231244989733710, 36029420318935956, 59040203178639294, 60842481514255337,
      41023589647896695, 46063663126030261, 7487264493707206, 40781516721411735,
      58746557013852160, 65505498648600257, 12046351716835116, 48281421314979524,
      48305804832056848, 41423642786521754, 70509608367591708, 61288715527062195,
      20784076496627025, 51561323171410638, 24949682602225454, 42191115760943263,
      16184813596742505, 54810329346075520, 26710577276830944, 55053414111954656,
      60987451981872041, 43192789342683301, 159612051691106, 49984548145992576,
      70313587201915727, 57307466939317731, 3579089649124767, 44524322888893615,
      21554802713533005, 48439534542651537, 7250161258245796, 63264673786300099]
    ) [
      23634005377581126, 50228686255016661, 70271040817376652, 45302773732034980,
      4397233145421868, 44845364613678239, 5066268260999078, 56493840465271524,
      29183206286474401, 45369849511538601, 66038324583899031, 44071297086165916,
      53620998588177630, 64851359002052607, 56785269249792109, 46455092218304948,
      17061176139162071, 42613327387015067, 164194818823815, 67711693026737792,
      23314688257356318, 48756417133081032, 11716600515700725, 42229596621014429,
      66305540065498128, 39068945570857102, 5038876817550386, 52653161807121370,
      62108111910515351, 43304937381127842, 50827689165100938, 71985576035745425,
      52329507082829085, 57559249514822381, 29467537490231881, 44523218075485354]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        12294230864932076, 53803157334400695, 66609443812195054, 36065630668285597,
        37313793334940151, 46428660451312020, 66618540527888560, 48345231592984237,
        33406868692645426, 36029439831571877, 33921576814477337, 44043785571864719,
        47756053404361262, 51844906170050219, 28635696611897323, 42175746472823218,
        4097237739405312, 41972282461928322, 8625684281596376, 48124163821053608,
        17353736824794933, 44626598341999029, 51369219756955116, 40596774389344140,
        38453411678753662, 47855870316815266, 4987752643865489, 47705296313474985, 2516295408]
    ) [
      63517741694956725, 36029429915990177, 14794777608159242, 48842131743349147,
      22153027710005317, 58048449760151487, 31436324696409068, 41574300223995817,
      26061451383177216, 46928940758523533, 19898539169655603, 51140194832300210,
      66350784150554925, 43894306987686575, 49961836283466762, 44108655381655701,
      28619324141904811, 53379856296191663, 5568093279269913, 46190114915833022,
      7459089372454090, 41864494637691520, 183840179198525, 49555747405420971,
      3574403756111824, 48053827642996163, 163537816101949, 38131697706864512,
      31417280296882981, 49086238072309924, 12592396103299188, 51509660216819888,
      5802997498227613, 41356480737181845, 26060639933531679, 47999898471199899]
    ) [
      23539412225458176, 51165434273837985, 42149201706727626, 54892916083978196,
      70281404784556982, 42392339911660456, 71916862992060937, 49280837402656158,
      33141190482244478, 61077720762824897, 61281541443733296, 44143894785099953,
      64598509608671018, 46917927573477247, 27783897303198950, 57485475061060279,
      62135037615004922, 46496889431034807, 161098181352969, 42810154512547200,
      13985314023121935, 54106674938847411, 37387045366971662, 48892752917238979,
      59277573628929757, 43446652207366290, 32554544837924142, 51140160321022381,
      60453746572509479, 50581638027456213, 28887016552115764, 36013953621627545,
      50276060694812936, 50263827893913253, 209271118345181, 53786790943774905]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        15365037500763831, 44670540167682971, 46345998091853447, 36055735064416145,
        45745191934786939, 38830939002337414, 16765802351332211, 44494611713446292,
        46604563912957703, 36029472831885469, 60934537078931465, 38296570126818436,
        64330799873886523, 43697440264721806, 41828659086007769, 42398952247624086,
        68254282386276352, 37934826774643579, 40965572159506331, 41882120495152779,
        42675068268943707, 46627578237752218, 51087774845013793, 37712719301595516,
        25763896168842886, 40377970082883977, 62658052060779197, 38059152070397339, 2318116002]
    ) [
      19883343542066829, 36029450536087199, 59246838359228429, 39830407856385159,
      60120658328850420, 46047144345400220, 43808394234864573, 43223624304853163,
      24912023646339072, 39036550797279356, 29433550713949285, 45459990875118229,
      19882557385515600, 46648529425157275, 23784697809116059, 38458196708034432,
      155690609379809, 44204318983948432, 56754284663906442, 43977892485944226,
      1829590002671610, 37774253516353152, 30551762535090192, 42166896993151884,
      17908869535275828, 44660626410210209, 176718987568267, 34783594337536128,
      62919069841655235, 40567089622904201, 36201495924806643, 44360478660490655,
      11701615477560614, 35471894773760162, 711420620340091, 39555526426174344]
    ) [
      65173532410478592, 41100359473304959, 64633707007415736, 47973517775813796,
      29185220579272581, 44901494653476003, 26880922552931868, 40001930377763465,
      52803219480219820, 47290707481899165, 61546377379948650, 49035664026627764,
      2111064847130738, 38954040902012544, 19582871434071320, 46345104110873750,
      45503046704342607, 46117534062260643, 165492100214575, 35430140091568000,
      5504647187237286, 44564963126456209, 68018278843654881, 49074133813995174,
      59289801633733925, 37424627374358678, 27174896035134832, 42453874997450637,
      8905707578629146, 45502904645530533, 1309971958378810, 36041441412598182,
      48563656875344814, 40922236609913482, 47462324662605059, 46713457283925666]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        44901518784693444, 39602799654703238, 61798517333921963, 36045268694913156,
        16470690663989071, 37226732780269188, 24915683031811177, 38382329970161541,
        26053493055916917, 71045430376753292, 58690403836198928, 37139870388582531,
        27166847185093651, 37611566061117316, 49130429557409576, 35386163989395597,
        29978354184092960, 36903471865333122, 21536419923133226, 37129974196701827,
        15066116150494292, 37997525512928648, 64599498013968328, 36284437339628928,
        71354961026318570, 36355906400749440, 66852065781317954, 37156360948974209, 2252767697]
    ) [
      68844351153870037, 70686093514688400, 42081056579092497, 37780895146845573,
      57006536243185247, 39503848708564871, 55615954904321899, 38847430553278867,
      53899333452100969, 37658847980375936, 44902158750025166, 38745176474595718,
      42663776554945328, 39667707164134548, 33354861845967480, 37630258177980029,
      3806288158688672, 38247091197591174, 44909782390573260, 41385147598302352,
      4209829789076819, 37437827721313920, 35049486582383970, 37830371743996549,
      62920143591671588, 41388444035769739, 66526593312133805, 36514223055965174,
      66292732249932963, 37528002908978052, 46592163963635139, 40990402018969992,
      49124932114354881, 35587343167075931, 28011624302936529, 37315794329427844]
    ) [
      61780095929843712, 37827074031145084, 66578437817403119, 40860660804600969,
      1578244136080716, 43598429440921500, 52495141138631458, 37744606598497660,
      17037488985572958, 39662179741949576, 55898662527274989, 40220784900882586,
      2392591318158327, 37507082609281408, 14503376668624425, 38866124850850439,
      14515381240237093, 42626521643967126, 37333142029308756, 35667593482208717,
      36457926631720268, 38358145042934918, 12258633568192880, 42494576037232784,
      60365132202153784, 35148638312435373, 20976734181949277, 38087661961244806,
      996507724580822, 42188890446945420, 44634797317265180, 36045273145662841,
      19287197035232522, 37912837699814534, 34771374601766648, 40735314868384905])]
private def schedBlks21 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        22658789312336351, 54587144574939824, 56833179817199250, 55920941403169257,
        39601800603025566, 43810727091547306, 160453885597709, 49081845123385216,
        59892274097403531, 63575860709919684, 19635554453082140, 46956488294724796,
        13397268346282331, 36032645319228309, 60714184575396579, 56968753132325048,
        15435923072542620, 51729540581671114, 60414855363604563, 41127874813062813,
        62954189662093312, 52308952623413161, 42177527017817657, 55488839524940262,
        39603376862510945, 43405004163564459, 422214918510079, 49220356814535040,
        41022459812492252, 64567609441609159, 9781787069437369, 46948794716469179,
        32535213094772872, 146]
    ) [
      18482505640621630, 43801924857857701, 20430105398974769, 71985576035852435,
      14329023476431763, 60197019535345392, 61849752869129751, 46041671131806899,
      41546179062243307, 40951943456448407, 8876804043341824, 67336210288616900,
      3326490171336983, 49873541918724554, 8622012190665455, 42194412970379678,
      1266639839138739, 55934057006587311, 18838963185701986, 55738424167230431,
      26368765780016584, 43929473189645224, 54487349209372943, 51224597948792977,
      53415936014202351, 60766624104050664, 62419196876214084, 46635421487199161,
      62093654801031451, 36029423020158614, 40168096221724705, 65964965693496250,
      66095972747700996, 51177583630668234, 31141251608784461, 41802982921777566]
    ) [
      44751710241062985, 51192975283763931, 13415749856505996, 45783268282683047,
      19035383657505216, 45085062275799200, 55591344956547171, 62942596271142830,
      49460936825818772, 46665097882149297, 7494475829650288, 44332986557944223,
      22691547523554669, 61522072521671326, 22199590414187819, 50201200410474960,
      59290866703379634, 43820612394641825, 11426123108162108, 36029441089371031,
      54316009504505790, 58137615213635831, 69438362882196239, 45071882464478635,
      31974354783149384, 40839790720223638, 36872940628774784, 67304361045345394,
      23305058783125451, 48170364046944705, 47463132267062918, 42193311780973724,
      158963488297988, 57088347641724544, 45007297091203281, 53730696506779354]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        64035632363640264, 42250461302946451, 35649167559465701, 50116492832653226,
        11171801556300004, 48725657282581691, 165058252481907, 40075630858998144,
        27470931145691401, 48301172190334622, 21583441990954470, 54374904152757688,
        42403669589540559, 36048038482306206, 2128476495122732, 45448981699286419,
        3849143948191430, 53616237068892846, 3027340831468498, 42380258152194226,
        28586552851333120, 41940396742182540, 20164947136715049, 49313836979369896,
        11735966889847564, 47238000081283500, 4081389689872156, 39800721445332352,
        11143750387011670, 47506213975459484, 56484071289826204, 51214868442409646,
        51122315670043045, 150]
    ) [
      56234980593747119, 50910400258747610, 55628999079997219, 36031545807733658,
      9177982541601048, 49902079676321954, 25822192529945700, 58788501834542016,
      63806432342819236, 41761219583108265, 32818104955404288, 46761814320012947,
      10610036750134095, 51733956947936693, 32307073950336151, 46208806932200888,
      3236964727233665, 42445074475700608, 2438049509973171, 50469452540564141,
      13429562770438988, 49903243329495501, 4676577901390509, 42151427694395541,
      17902315248259259, 49191785584821920, 17085331381268620, 57298575514980800,
      57046119406420326, 36029438808160676, 29712843946754064, 46009740783242899,
      192597816486244, 53046734220226226, 65519819615548207, 44573810844491957]
    ) [
      68296630761324544, 51487595123434916, 3310894791244042, 57419660225990605,
      24126153009447413, 43969066564120752, 69665059196081956, 47672221272980095,
      37357534068649951, 61555881250584507, 67770223789007709, 48130785940047804,
      61528342615991207, 44825439721488530, 11449178728144581, 54404625494073778,
      45285588716012324, 51838393323698908, 31707044909920978, 36029428976347294,
      71666136180162544, 50525514916075171, 51164694373971876, 58476295244255676,
      65218115127329101, 43116934885478573, 61220809582089075, 47406134156950427,
      42420840916954458, 53616319647379638, 41312920365161364, 47413890282427578,
      162408181178621, 42550663728593792, 1032598812401130, 51516201971666096]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        49961883528111764, 38041477641006462, 11692715756718086, 41950289712807052,
        65477814152894902, 41211483264060319, 184213563091493, 37608237696029824,
        37585196642764130, 39746844536450184, 48861259823812468, 45017985288415643,
        37053832050483098, 36045839459991441, 31671658015653356, 38594541754200454,
        8882170811419285, 44164744853395345, 67444724538121779, 44386844742783636,
        31663523256565760, 37963414647415173, 18165832758101906, 41545663544898699,
        31135951401949090, 39492917900529822, 3236964713014061, 37464232861483648,
        2400493839615518, 39434579945789832, 25778207179509362, 43840400332209561,
        71959950215518973, 138]
    ) [
      37053866685603197, 45120281695830181, 45501547603604134, 36044739947567274,
      1838574703903574, 40463734288386186, 45206444576117385, 46394596110061471,
      65209984320120407, 43358884317717157, 47430915136323584, 39028854736002695,
      51106475373857876, 45424802258266260, 68296627072443003, 42362729937325986,
      4081389786016884, 38023891762878336, 14789992780695735, 42398898040330125,
      22696035794525079, 43218113325586594, 47472211629747800, 36067829824356511,
      20134405214471865, 40103090028448393, 60966801268707567, 45749170503480733,
      15101253605696323, 36029498904223646, 8310437436555274, 38781461465636998,
      55889965114100574, 44801371615451538, 63789380980613159, 42128505187263644]
    ) [
      63767214088683520, 41066274847747978, 62099787954689389, 48008706023456675,
      62129827199823025, 48479368806827177, 6051714529796096, 39280646908696448,
      53361139969199643, 46693653893927575, 33683532975679428, 45701966582600360,
      739854010398313, 38501049241174167, 35058106672449992, 43393969871269007,
      56478041003892606, 47009251413499560, 28619092092499871, 36029446324637618,
      71645648814833678, 40792492744659337, 34794344366380049, 47149974087366305,
      51144464719915376, 46289109196603304, 66850347771008872, 39259752161145477,
      29434375362481492, 46039436271200662, 33960493893199124, 43817396521726630,
      166896647450510, 38435098005080192, 30272237499484354, 42884889679303822]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        69383641768024686, 37369671254850687, 58692740365780149, 37614865418073732,
        10283403817485843, 41203727910974346, 65973556014190302, 37256404259573754,
        11404686582187035, 37311397155337348, 67701034850026736, 39742437883085446,
        56449685305594077, 36048572582414466, 19285315907584322, 37224534008676996,
        60099866144572535, 37798484916910980, 7473799474415651, 35051903478706318,
        16186655850429731, 36889179455706499, 44617389486343012, 37242123610988163,
        29420811667997713, 39330129159723143, 67191084831966801, 36338313543609984,
        58970255322218704, 36294334286452864, 25193326846836990, 36764929960831873,
        24631545169675217, 134]
    ) [
      34773796993402918, 42161401683199116, 69683639303641136, 36045275259459709,
      26887468191547139, 37866657976572294, 38711332779820748, 39938161338076040,
      23810966185808067, 42078886083643285, 13931948343752126, 37718222598161030,
      55035287979132421, 38648417169653126, 22394563134065400, 40625388100394900,
      3926894963559468, 37614868487947648, 60382779956233694, 37935928081523077,
      31676859277739893, 41644632023416459, 11977571032470194, 35882012450762598,
      39834848950715839, 37674239985548165, 71643076111336973, 39784224408526983,
      51109005183389789, 69335593830223507, 8309333635268619, 37492817932909189,
      62352610859975935, 38355942882309253, 59267033448221141, 37729268382532242]
    ) [
      44329961633316864, 37866656953088389, 66859921381689095, 40527506382202761,
      53650208563237695, 38293349842354331, 4362864417939823, 37565389776754048,
      35332705337050686, 38976077456499335, 39285565736717382, 44119672443422613,
      69967764105041816, 35548860419934861, 40961616445998622, 38256988765213318,
      47722388961724598, 42675978678352781, 18743166852373249, 58097772674551187,
      54190759840219151, 37907340376561285, 15631076185573119, 40266919626569609,
      50270816604623332, 33528055391005847, 44332377406942845, 37833670782247806,
      28014274339309186, 38818844777124487, 25491672657923001, 42712279020927636,
      30317128180012113, 37865526336163837, 40117363327862285, 38167927937482886])]
private def schedBlks22 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [48590565547814378, 631588201883]
    ) [
      57628117821475416, 45859151916418484, 4107679259336379, 36048038482047893,
      39611219340931677, 66623641072543938, 17120842932547021, 51907668008647884,
      4121788482040052, 42051477364804768, 44895346832216706, 52975259773494191,
      17427314135975736, 58061740053363180, 17657666076985326, 45484214005337780,
      40697025313414431, 48700118831988882, 39611953813695676, 65880314555560128,
      40481208743160645, 51567910979877321, 14816119588761577, 41292803906070174,
      66897248814792704, 52881802644275881, 49221084396438909, 57349254589039849,
      46928825932367105, 44867379794766258, 161437461420714, 47104900332513920,
      46085792388329350, 65249162165636798, 44138382007134427, 50943376664602566]
    ) [
      51747238629600681, 50792747631977678, 42402754663525948, 43235666001040545,
      14517769359300480, 36744577989738642, 26164717048545174, 59602170355774453,
      34544253424028501, 46032873696558514, 2140107529429013, 41111374991319192,
      30532849488527360, 68619350877352388, 52590847499891351, 51556921803000271,
      56195758687629358, 43004766294270369, 160801767790185, 52942092447497856,
      21093142004286970, 59312992456043762, 15406317269339081, 46046070000424116,
      63500643124158397, 36029425486429846, 2735888664866572, 67529720073561540,
      34011493289554003, 51921964310713038, 20729799959032084, 42603439634353313,
      5770239477585081, 52993944777434240, 9830414715373509, 58735743650830063]
    ) [
      3093413687230539, 52191349776963042, 33684705595143078, 46286852929841321,
      39584603171169127, 45353347710011041, 2711162159735102, 71130692641101440,
      69743108446217742, 48342983664570300, 7216905048795246, 44799188346655650,
      38173276848168626, 36031680210719902, 46159628384382657, 56735720758608883,
      48889310854954752, 45573264766387371, 57592606393671597, 42736473561735322,
      53620985590945579, 70973461860954367, 8115043820694567, 49587659500089801,
      8060720109300476, 43014660137249440, 40412775716198095, 71985576035745425,
      42496948841181861, 59071107615294711, 38199150259259260, 45776681346688431,
      24376729470869396, 41312588219701912, 2532993470075166, 69842029533984125]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [59034582437120608, 650446376105]
    ) [
      26382591320044739, 55165646121145013, 68017600365769961, 36034844342779294,
      6634854990189946, 46768415835854742, 15392908010891905, 49946122570142388,
      21898620307883097, 44783821625575864, 30258635158361813, 41824947014608788,
      55066907926894715, 49920776977754024, 37918710244618930, 53316242246427570,
      8337805623865056, 41256425514598551, 50264266675686681, 46749725581060246,
      23272596731898328, 48811418449975986, 36526209436009900, 42586968955489201,
      1566462620762112, 41899715013298316, 11156747141880005, 49502955479160232,
      42416537427816647, 51142462912730801, 166445547104284, 39175114142518400,
      64056630733147561, 46634276390399894, 57610761459247361, 47786655912831664]
    ) [
      3293413947779909, 52483821462441656, 17980338924409270, 49429323651486919,
      47740054578112954, 43831481411305620, 459521157928293, 50908152680249513,
      2179776375207965, 58505980884916412, 24681956041932449, 41947039464149418,
      44924161768128512, 46663957046950547, 66061174103321435, 51853789807218614,
      63574401741212697, 48071407161556418, 164255069480096, 41120192842957696,
      17630207720920822, 50573896850413481, 35954986834966194, 56909480790501560,
      6662180154489383, 36029440200664229, 14795834166706198, 46742025543479957,
      55926747782228758, 51042340914438837, 234513243686753, 46541964894721214,
      5770239541223052, 41548962130718848, 11156596800657349, 50262730278203561]
    ) [
      68018003349766144, 51743784906281636, 7532100306778953, 60603876468287953,
      46368805186095370, 45696429027503798, 161897041992869, 45598551316620672,
      12301901693299111, 54030849237894842, 43316913712522396, 51729536068577997,
      48030970032730596, 36029430368844957, 13122609574150136, 51540376278615463,
      40182544730405480, 60301501492712903, 5269442733327874, 44715650243678387,
      68539159307983091, 46166965225550207, 15397688354122438, 53172124750905529,
      64144816413333864, 50642102811357130, 52530399184530975, 36011754598438297,
      30576076623027923, 51247904776360360, 55662126519728460, 59660477170673600,
      70285747063014026, 43486378090608302, 18718066623943769, 46503423282474909]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [64917522766208381, 740505426594]
    ) [
      17343381180880288, 46490239444871841, 20992188122833293, 36049137995670204,
      17035637837692936, 38945290912797319, 1847375190461424, 44966296614853012,
      3555617135304888, 49003676050230947, 26036519097645317, 37944719476887679,
      15069474868856724, 41121249086981003, 66601321707705693, 46530913254816927,
      68008563502523081, 35724782280376510, 16473486738752888, 38961783385882759,
      50824029724445622, 44895926612384147, 2995570520596475, 54017426490463902,
      35605079168483328, 37978808279970437, 69957082443843487, 41202612813212810,
      26632420472755578, 44601278602205342, 204245212636992, 37591745977912448,
      22103145202943274, 38943091302336647, 26336282279250849, 44263707543857043]
    ) [
      64054066603134061, 45121329901824659, 40715287721845853, 46371550137949354,
      7230520676102324, 37492796944285849, 37869514916136912, 41105858692463755,
      46617749407700389, 46900381273560482, 49729496405158121, 43543649048671393,
      28855576717983744, 39037651214913927, 61239093495630924, 45091645101144723,
      50564347795383053, 43664560848439208, 173292258507470, 37991987269340800,
      26328860489516864, 41087166692789131, 58439114321663397, 46742041700527777,
      32262822246393209, 36029493990951851, 51376379497381897, 38983774423760518,
      54483371931634728, 45006981413962131, 30577957985231344, 44069144519551398,
      2955490088436748, 37784193798821760, 19573263477147575, 41045383707417739]
    ) [
      32806577263181824, 41054180370854538, 65194986191557933, 48131851761987746,
      64374570485591709, 54840157374055084, 166634539756721, 38808963248034176,
      32247162304564170, 45187298888205203, 15105334078776701, 50049421818150571,
      15421392750094195, 36029448623058865, 69112399846539281, 41099261136157066,
      52810052860614020, 47582090730327458, 12861905217433136, 51659237452647079,
      5770239569994490, 38912304658057856, 50261762679868511, 45180702707641491,
      42406263612024151, 48908121919973034, 44401469803571637, 36048038482412453,
      40402218478897083, 41123450861737355, 56187911498536388, 47118090145980834,
      21305402860809383, 47821907294211233, 33073354860697682, 39072833573762438]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [4648342220866097, 577983634820]
    ) [
      4934090753279598, 40645153723699081, 32814725137797668, 36041966153329309,
      53344531135037434, 37308099694224772, 42930407970145504, 38247091080159621,
      34778375481559523, 43388478134900624, 42924989699230736, 37289405765170048,
      56158958772782244, 37515906116809348, 13377764519609887, 40369172379270793,
      45479982470566863, 36380091235434888, 27448455305462876, 37324590456002948,
      41241648294691995, 38265780093418629, 58984467525568708, 38527492852882834,
      26882713555172575, 37010125566984067, 21536879490335530, 37126676970453123,
      22664712148386872, 40036011967206534, 61515083681271604, 36299830770857655,
      59532861683958006, 36283339103088256, 36170713498288451, 36616492334271361]
    ) [
      24636707764405939, 38614333584282759, 53073342717594144, 42493474478785168,
      71096000817698523, 35773160817052839, 39272998520981198, 37975511271903110,
      38149091506161452, 40472527277590921, 40416250348409727, 49595201225510296,
      38420327152090739, 37777597165590662, 59539046523045431, 38604436452878214,
      56733651283642911, 42948668484180369, 39036573690795439, 37823746773356540,
      71360531685344697, 37880951392830597, 13942522678838967, 40485726248951689,
      49423887694860833, 70525597399931025, 34487365460262927, 37622563660482693,
      20132133167072703, 38380135812371846, 20704167077972485, 41056402245152913,
      4215409968258140, 37455437422902912, 33360344663426418, 37609367725768325]
    ) [
      54463614845681664, 37896344438131077, 49408442761512729, 40238333045693065,
      40700826299765207, 46316488757140124, 170242213452790, 37737981276065664,
      711034090980743, 38576951195572103, 44628887259482690, 43766712366240144,
      41837854545058650, 36037090645121431, 54472406618898446, 37990904350804869,
      48282461254158192, 40328493368270985, 59841433970446852, 43210387048025497,
      4148472483259848, 37668746453490048, 8592505241241224, 38557159768167559,
      53354633019951688, 43027837465446288, 56188950865615320, 36046361816875424,
      45464808068185796, 37995302732869254, 61793105518692225, 40365874448379273,
      18463242278834814, 43701888257221528, 70228075376711816, 37913936104183934])]
private def schedBlks23 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        46360292234078164, 57949514367011514, 67497927138857747, 51493136689611974,
        59572590831710490, 41721619849899423, 37162]
    ) [
      70296712024730443, 62178328463995335, 70027765921404682, 49640437450651587,
      36768895672560229, 41973408029368477, 26317912751641308, 52472756837066910,
      40767579590410945, 57383315909955035, 37359338164110852, 45810771894805171,
      38447978608107195, 36029419228436885, 48324354874383492, 58214493531824310,
      68631966124726057, 53118241266455245, 44096938987992716, 43054248042175908,
      159380119131655, 48479273024668032, 1620296724951934, 60112323801606345,
      39903324758462428, 48528812924268990, 54216259652265623, 40807908641245593,
      66888173967474688, 53470038127063977, 19653709339280473, 55543802773989589,
      62686558352162804, 44640873252173742, 4666239688415893, 45150995423953041]
    ) [
      30918442026905135, 60762177369943530, 53971215215611779, 46817938420802486,
      38453098281280172, 41883243462028698, 158641356444466, 57238078081369728,
      42472188169149958, 55227146411678427, 24117300963753027, 44586989464652457,
      30565674206600127, 40708946017890965, 18495536441556992, 64491722839852227,
      29782956099493538, 50244080038380488, 67170714339748991, 42781560702562207,
      41537593274963427, 49993302279192720, 61035740678307198, 59154659710902497,
      41022498666695546, 46593636001903030, 54213961787744662, 41231223855936920,
      18192826483380409, 58228775824455854, 49499828264295155, 54404693023910612,
      60707570444253799, 44009737857228199, 49421675812657543, 45091521620396690]
    ) [
      13506615583932488, 51222662802366427, 71117999822385300, 45643628661769894,
      11434537071124766, 44603469790630047, 68572913636712051, 72057548865277342,
      68341884082385072, 48617868836223936, 37052921868232926, 44428648280751265,
      16778945205148966, 44126272566871196, 54833845320719670, 61568154139692793,
      54529062680317457, 46571639947475634, 58158021701182119, 43182882547266972,
      22403230571993257, 53065179945443735, 24187924206313664, 54693884581056994,
      10041520567204241, 44638665689032104, 53366319859801155, 41271903621824406,
      21532838140875127, 67664943495623347, 61030861914171165, 49954903799409353,
      24386655314881499, 43052044103029920, 58427414746797814, 36029410436991377]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        36753334650834413, 46240647888958358, 42129964132575183, 51408439530880175,
        68597395397982540, 43966868933352878, 38160]
    ) [
      26342432744181494, 47885544077719195, 69722131224178032, 54194641338747574,
      15400999976091830, 45306091527708849, 47147061075679838, 41866727483385739,
      18476067205716298, 50042823036875432, 67196072095102171, 51781213332943549,
      25797616578114060, 36029432298406561, 23520841013365540, 45497363264398227,
      55922152082482762, 51796573192112559, 50029143755373363, 47038949233974456,
      162957963862428, 40298805245686400, 25220827862307343, 48193416376628639,
      62121885949472241, 53090725087713717, 36219578184743234, 41800803226343847,
      31679474940280832, 42833211273837454, 35367117074504963, 49961459579103401,
      14840205985100755, 49053286882968251, 58155500585396233, 39421384966799508]
    ) [
      8051142028070899, 49539234463680161, 25539828551169059, 56291459623886528,
      62408240224584542, 45756900824712882, 160849059945593, 42916770382552960,
      71118467844185783, 52295753232667821, 28365139796540772, 52069292040270279,
      55918497143960461, 41243332627494307, 47729862279659520, 47235717471690646,
      27219001705344022, 54797178760778935, 3307089460643268, 47918568552288954,
      53647700418602185, 40783693396050066, 39582408299812087, 49894385091484069,
      20190910639486181, 54210063929385919, 56206796935052060, 43065256983236522,
      63486748428112648, 44364847815820431, 18484932177273672, 52114334720107951,
      69456908665273433, 49665722879312832, 49152939961330477, 39466420132860825]
    ) [
      60409619473924096, 51656919226259365, 20205603895295285, 56442116356810703,
      70289904638018198, 45372063668304050, 20711047820057700, 43916231048167569,
      50858338396382152, 55322749043353524, 69470270565305021, 52182540093754057,
      53102802487587949, 41960219996948642, 58145479854166390, 48755265476062361,
      56501835450069534, 58015506741206976, 21039897046272789, 48016430338503098,
      36479397585986662, 41060711993024917, 12285640654231521, 52157208744416939,
      68336527827254724, 54325524277455307, 3572801668168531, 43516058562590892,
      62065234810869230, 46015234516067728, 45794803946531102, 55112741651417014,
      19641331226822846, 50155009127249346, 36769028851871020, 36029424211491227]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        64887775457609178, 39268551240507783, 10294257333996880, 44712314713793686,
        68294101567512469, 45590857405116065, 38797]
    ) [
      38149177403737839, 40050313956872073, 11143806227288231, 45836033884861851,
      71115212271428628, 47163185407040167, 10836789114740597, 38292172952741766,
      21545551139277052, 42087733833724813, 53374656439490908, 46592510384072097,
      45785299085141640, 36029440435686311, 44058429611345377, 39069537320597895,
      65461402832637025, 44644138114062483, 8904775589339305, 47277515221575332,
      164989569116003, 37871054596969344, 8031866002769713, 40402161670785674,
      10020595007525472, 45485287528171165, 25513933847438008, 42348382834313894,
      13376317101932544, 38392229534288262, 26612981198719351, 42758444567031950,
      36485964583967630, 45976776473666720, 69139153658160318, 37545594692042902]
    ) [
      4091860578305848, 40911242315747723, 33667490976928869, 47242329641432992,
      58455620174326206, 48444142341124270, 164555723810054, 38579148222300544,
      15355721613609582, 43484131972283536, 29172915242901149, 48283584366650790,
      37348205319007486, 42143858907516332, 46873982545592320, 39717157537964424,
      48577379642609455, 45944882113332888, 5251820087321884, 49184097744672426,
      53091158684642474, 38115149130760341, 22389044048791628, 41486293960373900,
      58721366700693228, 47005931973894305, 12854736886737051, 44611201152087981,
      13940233334724018, 38877120285899143, 157662029908878, 44197726410588562,
      37053660548407382, 47745916083837861, 66330447010835314, 37824849272744350]
    ) [
      17323314815074304, 41941497411489933, 6089411572898054, 48911411126530982,
      6672251864002610, 49427125282296759, 18467730742225203, 38983772527394965,
      40691471737785420, 45098237238391699, 4127350415926344, 50198961305054380,
      16525078718231759, 44048235813783984, 51659645445510494, 40402161804995721,
      6361269979746860, 47366573415096222, 37065390272260709, 50970838047039408,
      51408300375322824, 38228370040123292, 38998021907056934, 42688074799445390,
      55630983204543493, 48723392943676070, 12581680159960793, 46172526001334964,
      33917737201474798, 39329024329686663, 67715156882263460, 45678791273087893,
      27770737358644542, 49760248565411499, 39032189018092209, 36029439378533540]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        38990458385958363, 37609368732402053, 5214423259186634, 39007962521920903,
        32811400766065838, 40978330292560531, 36496]
    ) [
      3806575929820719, 37830373472082054, 39555740530345652, 39706161314374280,
      69688410931367833, 42338445285620118, 35449155080786738, 37764402958982022,
      23509961738782238, 38120647628853382, 8596387932702753, 41666616887242636,
      58430799207175687, 70698130514068885, 16754738397349538, 37761103903992198,
      9999742682236478, 38756172396215431, 53075550357523260, 42132829749180306,
      3255780949202218, 37781995715464446, 68827179584226842, 37830373253973125,
      2682840706418372, 40178956515306377, 65466032900051325, 40546219991530644,
      710471449116511, 37635758068457606, 3524860428584368, 38140438502596486,
      46315142923257961, 41711703558213261, 17330543410713654, 37722621306994575]
    ) [
      28575407494431972, 37866656701460101, 5217034630039331, 40568189067434378,
      33664548900213575, 43425877569809563, 171341779540821, 37537899302171008,
      28576318039295361, 38393329264027526, 62642014441867638, 42835414105570958,
      16495232521706069, 44020719030978201, 43212518609027072, 37730316320092549,
      3245013261977178, 39335621969902216, 48857402898943437, 43346708840124054,
      57309348895758571, 37678639524872604, 8873031017792987, 38038183216568710,
      714263942432705, 41145439903078795, 33100946129196350, 42718870772434329,
      1273331391569217, 37717122734225542, 64324194141242902, 38572551991421318,
      61236318908942917, 42778245591194256, 20150236763297911, 37799875984553108]
    ) [
      39834333543694336, 38118447548600453, 22951976822409298, 41756775951523468,
      53090810614487061, 45179618883212446, 18755467790098842, 37411452511846552,
      710651828143438, 38841935343374983, 52512321230965621, 44105371158468242,
      11714787947355641, 45518277037792159, 57566582687176955, 37732514152129668,
      26327017924626088, 40101990852374665, 29440847961362745, 44328587169178779,
      9746314247904733, 37317974412606881, 63760080232547538, 38241594495101317,
      29989748899023061, 42386804653941133, 43238056863898098, 44666135611484060,
      52213610771750982, 37552192416442500, 34488134372132292, 39059641296509319,
      64617755297156216, 43949245037304724, 6926492075203589, 36029463588188061]),
  (8,
    m1K32P56Cat (
      m1K32P56 [
        51654779311129557, 37062903500877955, 60943470721139630, 37275111308654723,
        52220572560164051, 40110786676899719, 18169011092623033, 36828704000893432,
        61223923480822485, 36862789096234882, 32795431874495240, 37350977392851331,
        8313504173098400, 39697353510970507, 55873635441159392, 36251451487471232,
        61503195105427660, 36302029626335872, 28571065217089801, 36750635101693313,
        32794104728027926, 133]
    ) [
      45183092560953343, 37524705749860229, 36175420848637253, 37897443278700165,
      54757682806425440, 41292781121844619, 69402430528721675, 37546696661532557,
      69670595182363968, 37432344793378180, 8872674525873437, 38567052772297094,
      58141885186935503, 40719937577306513, 64885514049654124, 37322392556849028,
      39552188548220042, 37468628274423940, 7466712699798919, 40100889545522568,
      3817807457194150, 37313024881388432, 16189529255740534, 37197045949541764,
      46588959882773551, 37768797683514500, 8033751504684849, 40438459127525261,
      24486886517935933, 37193747615990404, 2678451195577367, 37220135593054596,
      42648997410210919, 38660510790870917, 33090672406203303, 71310529180601999])]
private def schedBlks24 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        68312153696025577, 44397874974725035, 71939356124551738, 42810034992691857,
        56486248750620812, 56050629650057652, 12891120193621440, 51901060654238408,
        28051289027883875, 42730986674254499, 158078724248798]
    ) [
      42952243956981309, 40834293162088086, 27760282747047809, 56130880895465386,
      15435244219322922, 53775760209171921, 70840682483661097, 44054818437956007,
      5511931637307834, 36029413641502611, 46075196495535644, 59830800270615737,
      9232972031841931, 51183072078539207, 16788905464016880, 42761770768379041,
      41255199164831110, 46700229822513295, 10341614297460306, 59430617331207110,
      45813491810750061, 48633265555782589, 39018268787713910, 41567681376721819,
      985164828021136, 50506803940939675, 62990148220402266, 57112822845483472,
      69166199496688966, 46350641667198900, 40982520436138064, 40448360419954838,
      31703432520171520, 53267728776069801, 9518690329609299, 54394794969637584]
    ) [
      58985537076171176, 54329803586666637, 14322250903508827, 54405798894339034,
      9197387701926323, 44458343768793256, 40980274112928634, 40813400981499797,
      59531959962734502, 62134274965970087, 25848916478059149, 51648178315191245,
      70270680065618176, 43520444076114082, 25496478879225985, 40338404022544787,
      7797507317596160, 62500494078244290, 53138936621029347, 49270993792526530,
      34517637024098748, 42599037980625310, 53078028661593461, 46153649852735888,
      59612706116644906, 59552682181738454, 64105276429683875, 47201676384436408,
      26631243755660161, 41698523243614362, 157662089941616, 51776746447568000,
      17408845951713943, 56435523951329242, 54524625864081983, 45483109007376559]
    ) [
      59096864502284358, 50460687738402773, 2998787678645802, 45137845494687653,
      22691543244775255, 44030615810271389, 35356297957055570, 68026234966945948,
      34855067955363750, 49135750490105286, 39023616084388370, 44232933180948129,
      50554486397836349, 43501741472908186, 1296872271747777, 67555045986410368,
      55388584693588233, 47981241755351997, 66886576415614613, 43533633131985822,
      62936408917055925, 42582536397229463, 52278807930967892, 61773752193469150,
      47777563127500899, 46728875445536181, 26631741969179298, 42390124613964443,
      24931690639889753, 36029419027008402, 33747180682064164, 57639518695566824,
      24686813744120847, 45513893571282862, 4391499307654856, 41401649114530456]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        55937352205579534, 48932331627938490, 53935901395626062, 38954047714260376,
        19863453046115441, 45730467698809237, 21299535926765040, 51158846499021743,
        40171257441859765, 46051571048270770, 161295771803300]
    ) [
      67178475473122434, 42221913361144485, 15636217135665476, 44535275658156688,
      23831522199773980, 51687720047770286, 64950757803211533, 49538175621218749,
      6370160847661820, 36029421795575452, 6916780946263147, 46569407704214423,
      39881703401367798, 52913690327220403, 48618032252894921, 46986167424448437,
      51394577728512571, 40106386767478929, 21843239809159590, 48011993803900063,
      29471274000297498, 53379901343498422, 20461583731309194, 44341803505634220,
      22940213050644388, 41708395795693963, 63228556962797709, 49526041817450661,
      35385899276415652, 51298517963804090, 71679051408585243, 41148776791804066,
      46316968303624192, 43738120550797711, 23546499528957966, 50291322697660842]
    ) [
      24369324857990111, 42268047615983760, 56197618274704522, 52003281143099051,
      64393704881110168, 52633344172854470, 30025878815421837, 42833248386155943,
      63472609672139802, 45223577436601999, 6384029356565952, 53540417843954355,
      52570029356794553, 49983483669111999, 57881838260170012, 40716652984721309,
      51953438641061888, 47369863913448600, 55086673680378934, 54997294155254967,
      64101840365667337, 47662376454092471, 1576345858188383, 40065653969837973,
      3831422599402038, 49063139855473314, 39328142411150025, 54350796552182972,
      31722562827631762, 45024611433839022, 159521888901754, 42087729672860288,
      58446652091046597, 50791598357504936, 11186181019383483, 52084678374531009]
    ) [
      42677456165044224, 51808652535505317, 6413806781250743, 55331585788814798,
      64375253575778030, 45109273107788975, 32252303553305624, 41995296876518034,
      16230538130791710, 53739430253777839, 39068692372899045, 52654240279388105,
      62676903109768760, 43122421420634022, 158267711329732, 45643593931813504,
      70846626615961550, 55990161208240567, 60171679164582671, 50288050856292033,
      16504909310504401, 41384064159710622, 42382662115037197, 48138431903070105,
      68321070027681823, 56820322820895165, 26667412252903050, 47859194572023736,
      66598396926928032, 36029416359553430, 16499772248134056, 50357279167946404,
      41305983520454537, 54842296520684996, 5546553946914557, 45261010443659440]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        51687705006939763, 46912474089581475, 58726632553818191, 37679713737710235,
        39555654627526232, 39548930430181512, 6354913350487663, 44789281316301207,
        20727849900482687, 47152173093836964, 161763976192996]
    ) [
      56486502238759638, 43564442543692204, 27451010741998574, 39156399343168647,
      9729778358062282, 44632042831846292, 29736316183224610, 48116456283995559,
      31991539244903630, 36029432164184225, 12815969930020451, 39939261923492233,
      47171331922497563, 45549055175889305, 7502464540582805, 48375948393408168,
      52524849996408962, 37979907321495699, 29143623140607937, 40991507771890059,
      39296092862387371, 46278042290534046, 44376365111944792, 45745905641120169,
      11681214008236857, 38392229450400390, 17324302672955774, 42407696884861326,
      20441701915138594, 46699167004952481, 41563402071156434, 41451156498749352,
      16192033249722368, 38901309877258375, 5787247464713122, 43875567540712594]
    ) [
      53649564457739731, 38685801118171283, 16201087153769220, 43876663814273425,
      42121502918221745, 48806962152500391, 46921451239288630, 45104879104641712,
      37295436894214697, 39410389498781063, 21272150801944042, 45432499326299542,
      12851876376847356, 49440286302806187, 12010994969981322, 41619376929021094,
      56726465730543616, 40313100473948809, 31692935541854654, 46394591949091484,
      15387728208766748, 49594228030696364, 33109454705241211, 37982079435399834,
      27455576447027190, 41512682725987212, 21566175849977578, 47319293509208225,
      15951958077778413, 46998267135742894, 162631530750224, 38507678859180928,
      48850797160204842, 43102597360536207, 19037329259076812, 47719529482456228]
    ) [
      5783317513535488, 42752945884803214, 25513525774228578, 49578823694031527,
      52555061097050495, 49111555814960568, 36766404568000910, 38777026342219929,
      45194057737931637, 44712303808362386, 32273396362027707, 50079112876692651,
      61844547129226315, 46281374078772659, 161845536661267, 39680873083811200,
      54488298317057804, 46270340105308824, 64084823322765061, 50932343681068974,
      28621497580566110, 43297253081019818, 67142259518247788, 40736417970423946,
      30851572962923419, 47312696892386719, 48042905791015684, 50722348503070128,
      39306933668589504, 36029430989710495, 47441571121432795, 42140511532731277,
      21569530269768095, 48460602433513892, 27216218553167248, 48061510197691059]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        11416764174732085, 42686986965007762, 13111137536481376, 37602753594938520,
        39834771643401610, 37722619537368197, 10563422786258520, 39467564657092744,
        39568711496535656, 42639711337358741, 169954365051966]
    ) [
      56184131944487418, 44406648333868442, 40396506028611549, 37514808383553412,
      29702978162034087, 39047546433718919, 24366631763283056, 43343406211477396,
      21279525430336129, 36029451843990939, 70514753816462474, 37699528702638212,
      61510934741681777, 39865592832464264, 19305163202531359, 43310424285344664,
      2141855530850384, 37397159850541209, 37019751286146292, 37949121013077893,
      63483037717006211, 40998104002768266, 8611983193379976, 42899196064908697,
      6051714576128704, 37500515437058437, 12532033910572380, 38287774805566598,
      71085516409637122, 42187794341201293, 23249017012197277, 43353303175026327,
      27449713752244224, 37615965684722565, 3807091326354903, 38769366703520647]
    ) [
      3833634700108160, 37382864756539541, 63760926350476597, 38775963840392326,
      61518884823599910, 43553408754714257, 41832232477891633, 45450100371038366,
      21532838226665197, 37553291324071812, 9437398321169900, 39413688453115272,
      58427607943843335, 43967938379226006, 64912751083625763, 42226327396307870,
      58410986212786176, 37780893150294916, 59259998226777828, 40363677790716809,
      39292613893853761, 44170252042077082, 59003254042565787, 37206923737993886,
      34486253151356014, 38086561291958405, 14789043581650991, 41663317127613836,
      25221472172414747, 44077890330693275, 166252252011997, 37357576073267328,
      23509527934305537, 38487888136436102, 50257901455378923, 42889292943628175]
    ) [
      47153778170494976, 38593442796228742, 53072908926356045, 43070712311871375,
      2145721069575165, 46213174879504545, 64356686111483238, 37562065993554076,
      51658326997239260, 39137707880390535, 20707366873107629, 44228519849861012,
      22695670731153053, 46578216061829282, 162425419375632, 37728116172729728,
      8030955458102937, 39869991600411273, 20994137613307893, 44674933986161049,
      46902600356634677, 44455058051701666, 21819724501390393, 37974409797287557,
      5780925193095086, 40960720322216587, 52524536296084644, 45132336829681564,
      17911940479819911, 36029435469517987, 69952546899002543, 38319660776984709,
      62922789332027690, 42369213575220877, 70541370117101968, 45155428671116445]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        51935811894543080, 37836966011881603, 15632326055200786, 36207626950544007,
        45740381658316962, 36215167033320576, 53058812658090155, 36274541382649216,
        30259876421468402, 36736342037741185, 145936576316012]
    ) [
      66303035995818494, 40262533509036175, 22100634488114234, 37173956138252164,
      145111979426820, 37261917320123012, 30546226253431978, 39125610383509382,
      62082242833648941, 68525464180654734, 66291731507545122, 37099188022140291,
      69669310964990923, 37344381329743235, 9436865733231909, 39977744897536136,
      47725154997145321, 37115681106484619, 50810337200735183, 37071699627454595,
      7463405536445374, 37504911638026628, 56726817916487172, 40018436592299914,
      25880637746023586, 36948552630620803, 18158698727637824, 36978239545230979,
      2396688448193398, 37673138074708612, 64329223592838943, 39275150575467660,
      31387150741597270, 36713253434453378, 38987035242431090, 36808912003045762]
    ) [
      62365843892900754, 37640156591897230, 22101689196053909, 37544496573269893,
      46590862578713992, 38716588752852870, 48853155124775742, 41307083581336977,
      54029844862177519, 37528004519630469, 8872090407503161, 37584079042195333,
      55035966587176407, 39537933367700359, 14515802184388286, 39870011196704914,
      19005498813445192, 37429046745048453, 6338660994548974, 37708324896327045,
      58696739029157512, 40552797364269449, 65180494847119736, 37505391617972623,
      55878136637326619, 37341084187407748, 15345834477192370, 37944722228352133,
      3530413878314953, 40816692553531533, 26050310497407106, 37325691242731252,
      23789439527322753, 37277311170794116, 42367621220041875, 38377934188591749]
    ) [
      43775588824942888, 37613766997021573, 40116976771237308, 38461499756712326,
      62642950754503124, 42147117695921039, 7763392143595112, 37695361176482962,
      46590347181786577, 37678638803822981, 30829019807319570, 39040949011626375,
      44632894515022991, 42248277010479763, 447353342497984, 37672042690384870,
      51938384623732162, 37784193010618245, 55881396553615005, 39932663444409224,
      56176482474823762, 40966241620670868, 428972487512519, 37633559045202054,
      61227101804201385, 37951320506110085, 67705085056616307, 40984911188650122,
      65183849256555355, 68272592562270611, 46308962402141708, 37573084748025477,
      6058100857537926, 38225101753580934, 19857229561235667, 41468710280535950])]
private def schedBlks25 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        1303752786149376, 53165469295722153, 14863356215411759, 53327149884951243,
        48605774240725104, 44199958049778857, 35910803917937120, 36029409765917074,
        62389685472761974, 54065983344875949, 44697083831043877, 52337574035036615,
        46631991901926710, 43553434357604262, 49138061910906819, 9352592]
    ) [
      4430828986288632, 47280842010154168, 37890436101022658, 41760096716864410,
      29994396173374130, 47723887965765774, 26396193561359142, 57308541065928913,
      24693771667752546, 46713484312827573, 7770951413178868, 41402749834158745,
      156691411603827, 49635972360301952, 31748921190430861, 56346451765202130,
      30601365983183530, 46084552940919218, 39857273366814708, 41009118514079383,
      22658738016981008, 50998293960148636, 14581674980064465, 55378867120891601,
      46923714829795125, 45486408465023151, 69973274779164169, 40585800027724949,
      37043661283823249, 52190186610314403, 41886019094233317, 54326620265784526,
      42416644814322607, 44832187872683180, 17616940508683248, 40140490872599188]
    ) [
      17333322292238232, 40491237548099219, 48272960887295710, 63081000548202154,
      10638869473188636, 49494198042022852, 26355794721221261, 42898109438409119,
      1287990176421526, 40048128171226002, 33115716123135269, 62013392491816888,
      4723703002158579, 49019200244176065, 30295280438716707, 42692497374961310,
      33656963947337191, 39928279407276433, 1885729620721664, 60708274270478786,
      71147768758456720, 48465036535377341, 18190430486374258, 42429709834439581,
      51951965541143814, 36029408323009424, 66352768009216666, 59440527163337160,
      7530751761108414, 47914171596350139, 70824734982317498, 42114145031133339,
      45195367785993196, 45386190736482959, 37368331668335664, 58286024183665614]
    ) [
      7297596112470082, 49947206781917138, 42685110101060734, 44744214292052899,
      59844646713794030, 43571013188543387, 39576386763594400, 36053651149203098,
      42186461401837301, 49954904084697294, 10877196474362916, 44179057278978978,
      49990651670993877, 43046537619132057, 36478731770173675, 57453330935964569,
      59349730296393235, 50413408536966349, 8062760251272521, 43962451139477154,
      7204921887595226, 42428603494269592, 37601565026850438, 62236458961863318,
      44988446136592401, 50242980157683658, 22417262499769543, 43568820909949601,
      44357217894766901, 41441228546684053, 441692593492643, 63393219889645184,
      31472673578475848, 49936210138715847, 23542170254552026, 43171891893873568]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        6911583972392960, 44394539646244753, 54228105229935032, 50503528727119531,
        56218925991310907, 48628859573414072, 51122337046898702, 36029418154852762,
        44913059502000905, 45118030913978771, 40156396532179906, 50757519184745389,
        14558520614303579, 47456765296568757, 68569086843135000, 9491093]
    ) [
      53118603758645569, 53542644248124602, 54239354040793635, 45278599391582125,
      52234905168485379, 40905739656495247, 64351939976598989, 49387499577376931,
      4424755656045159, 52579463707159740, 12576818299188926, 44160380026886314,
      158224779614234, 41797455314755200, 3556304294156624, 49806423154592422,
      767032676430685, 51563501960690109, 43534882375906180, 42995979949072806,
      40673136551760943, 42707863139750540, 67172041373621381, 50053821038829479,
      67196372738880593, 50599214962157244, 67737684447309834, 41829379824576674,
      57856351245733947, 43601778994981006, 61826095619022687, 50285822723598505,
      37642200283854152, 49667912842631867, 179648407776277, 40648485495247775]
    ) [
      9188479785217547, 41854662535269280, 42080511418077628, 45870103930579345,
      71408103383148413, 54637744407235508, 67764751739569437, 49232502161141179,
      53376116879436461, 41108081993103772, 69964705866747689, 46647473298209941,
      15959405620275712, 54802676788628150, 63820494239941526, 48328689140914104,
      42394894763992933, 40331814670550169, 33659055520514048, 47401751680110746,
      64937713762348242, 54789490047966391, 20469894612697345, 47354507175171509,
      16776668909708207, 36029412903395990, 11426973418032893, 48066966600207518,
      15680950072422216, 54326598253236409, 38762259054181814, 46351738024563889,
      71379017578291185, 40062355434868114, 23534580778963546, 48783858147351201]
    ) [
      21285267750158336, 51507385963611301, 24146442551475339, 54144094054157259,
      23558203625094006, 44869573533002925, 10579134073576371, 36029410067929491,
      31142209210193399, 52246270528423849, 3317990100942632, 53161117169813961,
      6666183094679527, 44110897758945962, 2413963118745917, 41867753527626385,
      13695034224253971, 52900489745053869, 64678431243420033, 52146254330835909,
      59861401701692556, 43355520687544742, 62084184240854719, 43531398908215438,
      45505597897351349, 53534917450338224, 28647104496321451, 51125892641886914,
      31428709557055805, 42590247894048419, 157155293697079, 44810154286416256,
      6946992178766937, 54075885140497331, 4718256827253976, 50173699952440255]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        62354315979292672, 39342219459099527, 10575272749141380, 44484709129412501,
        53097880238792712, 47632663248804261, 33394769428916886, 36029426141012638,
        43214739126846982, 39641290564554120, 8888428664491722, 44761792435075991,
        44654219365163217, 47704132628680357, 48306822792456440, 9588376]
    ) [
      46055426560071836, 47488622074780065, 63521916344314336, 47155495889231534,
      39855357827064469, 38332853691351186, 41249972048923008, 42533043022392206,
      39582863628802710, 47510616434599330, 37908178797898216, 45815172071991982,
      161166908759522, 38576948846707840, 2126286038534769, 43145479907881616,
      44932069327805582, 47532608646949283, 45508260876298777, 44466050030922668,
      35888061989886062, 38802351800675206, 35341660452522838, 43633671056682129,
      41836656348208621, 47489726770752164, 63239741302155822, 42932209902125736,
      11969642209776279, 39077233499321735, 23521395079154798, 44129559625760147,
      41837871839878966, 47551299656794021, 65488130904533683, 41256530592280995]
    ) [
      25806571699942523, 44080114168120234, 7177614353799106, 40000835077965961,
      53364704837668983, 46185679589106842, 10321947425547954, 50441956075952557,
      32557315335303911, 42749685468871846, 22387162695635477, 40445043731582602,
      67722501372023381, 46516638326992796, 31714238943897625, 50209961504891565,
      7220018989871045, 41168566977624482, 25765880468897792, 40917839704293259,
      62376955048858715, 46887178644595614, 60143473589332301, 49522766032930733,
      13126354862320547, 36029425805427869, 22952002590705666, 41421422254238604,
      28320638976956020, 47252221454370208, 26366725493926345, 48440839377011118,
      8617347799361309, 38110722295758744, 29426932090570927, 41977782184410765]
    ) [
      20139451867889664, 43477533828735887, 19040576293084836, 49616211585776808,
      38201327660085870, 48820177616616120, 48871306044549436, 36029419966853531,
      25207968570772007, 44213118751265937, 71115074805932247, 49781140343299497,
      1046364461118257, 47775625430297270, 62940433427637489, 38775926830481302,
      35343069213789085, 44826656926812307, 33117503455601294, 49915282338982571,
      33977042659488747, 46576042825873074, 34506276683358394, 39172891111063697,
      66307580129086759, 45387418259022485, 37341492146119700, 50145082651578796,
      30032995653104812, 45318183806707886, 160174758075497, 39573119065207680,
      22962808863166138, 45815136838761112, 61831202418894166, 50341897397234860]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        28574277900075008, 37563187113275268, 11407744633374196, 39456569758922888,
        3821320730807869, 43310420208383126, 70257455566002751, 36029437700744347,
        46870426268369927, 37652248796656516, 55036915786352209, 39791924848752264,
        8045116150878130, 43260942839470487, 51680291785840891, 9809563]
    ) [
      34212887175072126, 42383509340353166, 3548886825277685, 44725513903524765,
      67162489358163982, 37310296032805010, 30827924573029610, 38551660649717894,
      60109779047647787, 42765046821063055, 453095878662594, 44731010270440605,
      161961543049152, 37359774677079680, 57005428123796766, 38734181861659014,
      28867495464110843, 43050926353954705, 21000940982934064, 44742005151824796,
      69946534190750831, 37414751013453699, 13377176105354585, 38937594012633991,
      1847482562481125, 43202663958300307, 69695304503695985, 44053711577468059,
      11685517238244393, 37481822128730756, 46310160702866848, 39177290449983367,
      46603756229070076, 43269737221135252, 57028260526791339, 41839288280483995]
    ) [
      14252241798340814, 45266501860890275, 20688413230995933, 37927130310749829,
      40683388508342131, 40578086098177930, 69692134722736856, 44977301445451674,
      31422022100426962, 43412709401963171, 32234466143408589, 38021689451603077,
      22669664317245405, 40990408075706763, 51679136399463550, 45005891247606939,
      19881548049784930, 41119100665148579, 45745424020897792, 38132741501756549,
      16478017998391385, 41458806203230604, 12836629019924019, 44882747455279260,
      11155961209593895, 36029425570749601, 60663760997156001, 38249291177159045,
      15915927048915162, 41914010459662733, 37325463112095659, 44792585639556508,
      40990758259433439, 37276192970285723, 8872605803381955, 38395528069169542]
    ) [
      22384448375455744, 39024456605646215, 59268274734205995, 43846981647718290,
      51687726474305023, 46894881718970275, 13410883590006833, 36029424379412383,
      66576616727414225, 39279546675556231, 45196243907218748, 44186737820808340,
      54221963350679238, 46978444317458595, 65759143236315085, 37639031807397272,
      38992657428153914, 39547830985663368, 31405812613156451, 44417640899896726,
      36489288939773801, 46968549450994595, 42389667743966557, 37735812871225489,
      12816090192381602, 39850200475001225, 14800768994086839, 44586969767533464,
      24104115094921261, 46495760306693283, 159994401955953, 37828173022720896,
      59260066947827462, 40181157535098761, 51394414370197802, 44760695104594841]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        68544738226530998, 37346582114654084, 53344629912863907, 37556590362289028,
        26888864055985631, 39850199485108104, 24365854404218716, 66118635223975056,
        44900457924494584, 37275112650869124, 46026117306418282, 37587376771749508,
        15067554990491159, 40169063343385481, 48853172349669340, 9174926]
    ) [
      28013355200775556, 38446106140929158, 42658240293997016, 41500597292205711,
      37876039149720537, 37604971547803537, 19568358569772411, 37547795108152453,
      44902017013679502, 38637423244559238, 49696506300435138, 41413735689097616,
      55607755751461518, 37542298422453480, 8872111883060550, 37535700094362501,
      64605445773428112, 38878218925092486, 28305722352045023, 41115766863567761,
      36285831719129134, 37470828975446917, 67981637945165064, 37522505535390084,
      16473443800876438, 39154199481036935, 33936063719312654, 40478046059349393,
      17598108440497507, 37411454391229829, 60944608905823447, 37537898664620420,
      53628522982442423, 39500549905247623, 14514603875143253, 39657801375611025]
    ) [
      40133882000151026, 41763392516992662, 12525639013275468, 37474127074108549,
      43775301054072109, 37937026418730117, 55038646679930734, 40814484436847498,
      42667367254692646, 42210882827431062, 18160975010568253, 37493918568625797,
      54471474724701506, 38029386452440453, 55602438456510428, 41154239368382603,
      44919205725705178, 42934365186078613, 22383168467536313, 37514809541215365,
      67700957545727319, 38143737003922053, 69395760299411558, 41398336486319500,
      5230555405587485, 48982798179058323, 25197965480002969, 37533501473771397,
      10843188345865582, 38280078006065798, 19294429935143180, 41498396205281934,
      62086391865119778, 37634998715924879, 25197956889937303, 37547795259150981]
    ) [
      31389156519477248, 37493917259965316, 29702956686607769, 39061840219098503,
      58987890690395264, 42934381393093011, 60121899658811693, 36029442280854425,
      46307557921883200, 37567585545673092, 66295158931424741, 39346617119731079,
      15642505238973894, 42989358518042517, 28034040059107343, 37293785156596890,
      65166673423926411, 37648950580550788, 31111263590123064, 39633593127506056,
      69405548663115523, 42695788494005397, 17620080103757322, 37361975109353623,
      10560789938930888, 37743509838848389, 8593871051327131, 40018426978791305,
      27748450430849166, 42099851245601942, 166703123633715, 37434544034741632,
      29701358942520584, 37843566739171973, 62919194399639301, 40409858268948105]),
  (8,
    m1K32P56Cat (
      m1K32P56 [
        70799935384552871, 39670985347814793, 1382088444447580, 36858391267835011,
        67134996777566958, 36880381567497090, 37017616655680279, 37359773720758147,
        15068126219830671, 38708906348485514, 7461414242912994, 36617594479974530,
        10557645976666648, 36672570648571522, 56157116195897949, 37134370531903362,
        13659402700948665, 39217957683333768, 40673759061974977, 36189877913555072,
        43770013870817427, 36216266511392640, 62347581379674290, 36398787438114432,
        9994807690035612, 567598493570]
    ) [
      30826490042378979, 37209141030442372, 16189387518084135, 37372969370277252,
      19850954537272612, 39423582782654599, 69400493447548398, 66041666071318158,
      2397057825604684, 37120079112173188, 2115389570057181, 37364172857814916,
      61228149778842929, 39713858415845255, 64614237720055408, 37153503487677069,
      51654805081719785, 37051908250381443, 65165603961406373, 37370769759803523,
      38429170590778704, 39875490718829192, 7192285893332524, 37078297173658763,
      39551170626159532, 37022220882773635, 63476706855388047, 37404854871923843,
      23793098873144712, 39891986463536265, 10285852031880564, 36992533850719209,
      23788309933032292, 36977140167824515, 57565620673217388, 37412551319096451])]
private def schedBlks26 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        61548821318316984, 43706267128156837, 31406766190794918, 39894195335380370,
        46339388282011648, 53021429883435432, 70310336016270328, 52438729624850886,
        64365920466744726, 44033927868029607, 57584505972234639, 39901892470438546,
        64352313600868352, 52189089867081894, 61302466693808168, 52837856489740999,
        34812765922899697, 44308811043114921, 8326866093840977, 39915087163634067]
    ) [
      9195351572119552, 59433885112581302, 67489985615941531, 49438118318329279,
      5808022638602925, 42708990955374239, 15642333507261913, 39845814776883601,
      2718519394664448, 58440995259008690, 37092539282935944, 50249569744515266,
      59290613308042618, 42965182030130848, 38723766938408594, 39859009486857105,
      35086178897264640, 57199624770294959, 9227341241962450, 50829020626868932,
      21574916377849755, 43179590908043426, 58990373291398957, 39878801249818257,
      62387056884416512, 55518449479474348, 21613498653592772, 51461249224997061,
      17355278554280453, 43462170815526564, 11421613338761208, 39893095454642322,
      69140815628304384, 54291380393080234, 65524698815449360, 51909856998864069]
    ) [
      54776151507312446, 41751298274958488, 8322248910476066, 39893092770202256,
      6403369593831424, 58232152056938197, 63254005224294251, 46262675082920114,
      38733233203814648, 41782085976303513, 26899021842584327, 39482969765595791,
      13149131049238528, 58787414203143625, 18504260001254174, 47123608256994999,
      736026938286975, 42047072925968795, 69120989916009437, 39597320954630031,
      32565582935326720, 59226117865789121, 23855527305989333, 47840502337534394,
      17907619750192548, 42276874815666332, 42100096537891993, 39777643529203344,
      24116454520946688, 59610929503395258, 44688188907441725, 48738818101603005,
      56471761772390505, 42518771819821981, 71936989540029776, 39849113043322512]
    ) [
      3068986061193281, 49352360270447566, 14535967429929639, 44406658870308002,
      47739951385451714, 43216965209830042, 5516364075669844, 43149892215446169,
      51773944942723096, 50976373237993434, 3560251564338860, 44220840264378019,
      12835555309689803, 42778253309027737, 67720907975792594, 43017947716266135,
      52611746441822213, 53937408585324769, 469816551978857, 44646360475211431,
      70819563729951944, 42471486075183256, 63215289686922871, 42263672085930389,
      33455925749710850, 55739534567602659, 35659050633641340, 45038894598996138,
      47457200800177582, 42081155001315736, 5791714343425212, 41160846706128531,
      12325803164205057, 57376724326541278, 8924906540483469, 45652434536234415]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        68883977124362615, 48173655384023477, 5804767005484826, 40271342906814875,
        30274986301751296, 44735395515502994, 50288473470378586, 50639869024602284,
        41299459447502625, 48377066343807926, 58159786991593386, 40314225521283227,
        38155602742837248, 44395641020180881, 24109694298923325, 50212153464846507,
        69446523301836108, 48506809403778742, 23257340857067562, 40350510780764316]
    ) [
      57020198674202624, 46618888613243032, 7794548224272845, 53689958488573620,
      34260321607532171, 47468856552233908, 15089988036568262, 40108609615731608,
      17612387662397440, 46186774335857047, 14829717507450840, 53075319677337778,
      57060391731576324, 47656876614185908, 70541619321415054, 40147093881692824,
      3537672450113536, 45864612362117526, 62679097721726585, 52512361033212848,
      1328943347186952, 47799816078615221, 45491166744126996, 40183379006953881,
      46883727931441152, 45468781750341780, 27774289316193516, 51794370444250799,
      33699248564779832, 48001030112293045, 32262770563524266, 40233958169260954,
      44349654269329408, 45146619575276691, 17076556549563329, 51250105527860654]
    ) [
      21027651880991781, 46126334651158704, 21841036594356128, 39979961772319381,
      7486113271283712, 48612327739811742, 38765188137726192, 54155084455610557,
      10614134313696390, 46433102673553841, 53929871148097702, 39995355673324949,
      50831661939720192, 47985598276922780, 27221952394211104, 54301314502300602,
      17933557456551230, 46788249627009202, 28316610359042544, 40026143156560022,
      39852875114971136, 47517200820488091, 12864765758320020, 54290312490423480,
      10334269961715167, 47038941465863091, 69975748741604078, 40054731549427862,
      2978137027739648, 46998225057404826, 57617122364271488, 54053906484404405,
      1327448674713200, 47292931940274100, 47458785710679047, 40083319975853719]
    ) [
      66602434061893632, 51312769066818724, 21893530338901019, 53251275713975240,
      24400081596430481, 44672756220354219, 38726799246793556, 39930481047861907,
      36764858153664512, 50716826533463971, 58482322316900714, 53467881568296135,
      49171193826556366, 44983923631473836, 65186009709648948, 39934879631260051,
      63503537811914752, 50087896554102689, 69455607213962888, 53618518469759173,
      10610578035030801, 45392948969989806, 28313543690198371, 39943676428946068,
      48021263025602560, 49648084101485472, 48341633844491402, 53740567330649795,
      11174631813266353, 45723907321958575, 57024614097788511, 39959070212508820,
      15931616717733888, 49095020323807903, 21316295118795370, 53965969294620608]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        70552331036107505, 48583754732087975, 63231069711674434, 40953057094896031,
        55881138845745152, 39757840290288776, 49140016063418181, 44871745023946391,
        65766135421706633, 48198919370832806, 3277367829113800, 40956355931776416,
        29985131747704832, 39595110488975496, 44353859113422483, 44618853222293910,
        8907236624343174, 47873459231333286, 17632978190576423, 40956356099549344]
    ) [
      14225247508070400, 40889251865090187, 67161368222864441, 46607897725008285,
      31994545672464425, 49332545035081132, 29171674085501871, 40850801188067487,
      60386877397958656, 40630863696517258, 44360361783366414, 46170286543815068,
      3001308793775817, 49256673045179307, 46623238612429849, 40894781921625247,
      31113058906832896, 40431849675940234, 39292592414364204, 45849225038022555,
      2437379573720477, 49118129429391786, 54504709765180500, 40922269963988127,
      56726551631200256, 40183356826793353, 13395382707261720, 45480883659803034,
      62671894994068512, 48855339422594728, 58727156546120808, 40943161121137055,
      20978714185400320, 39986541678472073, 4949917913419839, 45203802686226329]
    ) [
      2728599958039901, 48889448208031412, 7496674934565373, 40606705445897118,
      69677145077022720, 42100928023580812, 40426747376671042, 48086764990318498,
      46918534899018834, 49005997514280626, 21289335343983143, 40652886175789982,
      24640637696704512, 41720492319472780, 19314625154947011, 47726117978885281,
      59864515493866276, 49148934193590960, 40148622642227832, 40710062072292510,
      65172686447149056, 41435715385287307, 17906026185725594, 47406154508318880,
      28056507373431364, 49246789688200623, 57318883986025168, 40755142787238302,
      33647184110518272, 41115753793798795, 69695871392847163, 46970741377299614,
      49728577321478437, 49323752566026157, 10031298355571533, 40810118955841183]
    ) [
      36184479033425920, 43964625784671376, 35929796461567956, 49733859699104425,
      14276285370118956, 48603567567912375, 62664310050695380, 40403289167654812,
      53353847015702528, 43613876374407055, 1588513549754026, 49382011515396776,
      5267758941647273, 48644250907454391, 16502727409314123, 40448370637595805,
      62360337592909824, 43177364050533262, 21290215708400942, 48976286372705702,
      30598509651341308, 48699228787347126, 42961740301314479, 40504447609692573,
      16479400987230208, 42835411270173326, 3556123925978106, 48686010806587301,
      37915128148635334, 48767400404100277, 60694985963907543, 40549529079624605,
      36182056645001216, 42419790438991757, 45212985936288375, 48351752913065123]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        6640408489333406, 44197738289192089, 59565710077107541, 40817827919087007,
        61788715998281728, 37802883668066948, 61511866761185017, 40268019826114441,
        17335345188802939, 43963538051008664, 57312780672408699, 40893695966218142,
        49122165950152704, 37733613512757636, 28297394301994673, 40044816063181193,
        39007990667251863, 43767821843884695, 68007966486535136, 40960767484112541]
    ) [
      68826672763076608, 38275679858885253, 9160536198842608, 41700703039596173,
      16495700640831167, 45034482106762140, 30859742163083424, 40601218206020002,
      51937959409254400, 38163528246770309, 23515021267208311, 41375242967200908,
      22124220905264540, 44789287020718491, 69420555528806332, 40656195280602273,
      38145496569249792, 38077765232493189, 51943435562092570, 41119053217889675,
      44078478800622770, 44603466133017242, 30857465798631171, 40704575084082337,
      20693807491547136, 37974409780509573, 995807639013293, 40807887148983179,
      55054967787000715, 44379161264592537, 42678169264102932, 40763950440042912,
      6619861084635136, 37896343414736005, 34490840234952538, 40562692767612810]
    ) [
      25507787641101201, 46206578329823905, 182594743084395, 40788130837331618,
      52501755480997888, 38722087116309894, 29429766807653084, 42898089170892176,
      26914166079068858, 45980075679674272, 21011459536102506, 40713364415760034,
      37301952118292480, 38591243605195654, 30836239736605259, 42564931980219791,
      9461544980617638, 45713989956595871, 39869655889716029, 40625404307647138,
      25198399269404672, 38490087310688902, 49412900995959260, 42297746611304846,
      11712464312834245, 45505079760916638, 47187305187746399, 40582524226600354,
      9717090864627712, 38369139521665926, 57574854971328854, 41965689200701837,
      2704221364524969, 45241193279188125, 44652969520111966, 40574828836414626]
    ) [
      148414845386752, 39415887728029064, 26619698614275534, 44315382912670357,
      13972489102270308, 47467734088683429, 40432910864656925, 40954157176959392,
      51939574334455808, 39276247956116615, 27181690777865526, 44066889056866964,
      32267228699664006, 47154369382400676, 61825335508183331, 40946460545238432,
      28858372838490112, 39106921017928583, 13106799466482814, 43744726781135763,
      30013917036715378, 46788227547547811, 19041431096305617, 40916773697747617,
      12251164527132672, 38980475553324423, 20142827764943861, 43485237792280466,
      37612568866626714, 46517744281291938, 43248364981495485, 40869494597103777,
      65731216826662912, 38833139149686150, 15919719554321238, 43161976139145617]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        34491583271765935, 40866164318754699, 18740667069797006, 42412093723449236,
        4931457914536414, 37433444556670085, 32797609456076038, 37901841442652037,
        56446000087402322, 40636362714286474, 60116560920613332, 42501141766977171,
        10279581257996569, 37440041810989957, 27449533358638344, 37844666183689093,
        19009364322780943, 40452741403503754, 26338876511392066, 42218559510815123]
    ) [
      33922598817857536, 37382865578920836, 6057911873275140, 38340551749575814,
      27738889693989197, 41753484563878798, 30282923575186809, 42106448533375124,
      48559555309305856, 37408154933573508, 69389717208597775, 38238295993774981,
      38434144230213845, 41509388855255693, 71378201444717748, 42213097117874835,
      57566917775687680, 37421349391880580, 61508344845862162, 38158030705412741,
      63484807264438393, 41308175006099340, 3260922062083081, 42285661227783316,
      64040966796312576, 37420249997697156, 48841837748651273, 38053575842467717,
      5781689705007107, 41057482361930892, 22400554743141167, 42362621521918612,
      69107615163121665, 37423548666801796, 40678977523909893, 37979907674204037]
    ) [
      66305497047665709, 42684787774002578, 19589412823013547, 41503927888928409,
      9996718981545984, 37415850759969412, 992131099821392, 38855129516462983,
      3254174539090832, 42522057318353042, 37321430111655957, 41619375418610072,
      12811550354931712, 37390561791203716, 50249972848100652, 38692399765483654,
      69118210973272793, 42337335824827024, 37602084743452528, 41764508789149847,
      15626373138055168, 37372969504496516, 32798318131184914, 38569252919649414,
      8318769884334672, 42187799240273040, 41823822841747183, 41876656794090902,
      25196711328055296, 37375168729084804, 17035547635057927, 38437309947239046,
      9162249909668284, 41954698614366863, 20149931796895267, 42009694462978965]
    ) [
      35048223838470144, 37653348090173828, 62073888989611612, 39782029428657288,
      45762200383295366, 43518229130782870, 62940390392175407, 41057525916603292,
      25477945779519488, 37592874178883972, 32800122039666204, 39584114835821192,
      62368253331672755, 43320314403719829, 2703967974169256, 41143288645613980,
      15063247085666304, 37524703568758148, 71361760051693011, 39354314003120775,
      61522604317511098, 43082816754727572, 2140034459408894, 41263135832414875,
      9996650259906560, 37480722566769796, 47154602812999073, 39184987115264903,
      441550809763073, 42901394853070484, 17338807019477356, 41366489774381722,
      8870771828817920, 37441139745513092, 20414145013908849, 38994769254819975]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        40958240558514938, 37523602412925571, 45187168517785201, 38903507491394442,
        59252494820694635, 36542826548417153, 65163520871465431, 36605499415851393,
        38142451394445856, 37044209370449026, 6621639215711316, 39090411079658375,
        30821980255918599, 36150294890966400, 33073801544630383, 36170086335149952,
        45458850845589637, 36280038756233344, 48837585665556751, 37049699311655809]
    ) [
      53062222915953373, 37032116906863491, 40395539720012681, 37127774955348099,
      39271173132485668, 38539564025274757, 43221035640720018, 39005780376900493,
      38143804333089341, 36983737606699395, 28291931035108190, 37061803368477059,
      3523412997997533, 38304265449883781, 9161798939937195, 38956299786708621,
      30543855405687198, 36963946045072003, 23225308438823757, 37027718105357699,
      50529437752460213, 38108549930636420, 57293379994683620, 38933207089717644,
      9151409277821235, 36891377119992195, 6055081452339982, 36948552160845699,
      10559492837049187, 37814976618210180, 1841628445837231, 38896917568812428,
      50246266243637656, 36779225172323714, 51653615356248746, 36839698899058818]
    ) [
      52221105148167581, 39444474577349255, 25209630775086561, 39469781296879504,
      51937448308368086, 37287207563992964, 35611457268319341, 37447737335389060,
      26606551550690661, 39292739858759047, 64334205853535577, 39368624952027023,
      36737563339055900, 37231131615324804, 19848626640880698, 37369670902505348,
      64886705995810069, 39099223127880326, 21267933111094440, 39250975697865359,
      20974715531223861, 37173956121474180, 4648758851830791, 37298201656829828,
      36457351090767054, 38937592687197574, 55607334799576081, 39161914098351758,
      71076909192831777, 37094790042740867, 56439849619325889, 37203642314644611,
      70796787141477488, 38723184966951557, 6911399311543108, 39066255009631630]
    ) [
      14220312537779550, 37443340446539397, 20694060902548741, 37776495657451397,
      47156325116446401, 40222940000367753, 51670812655325317, 40747414647338386,
      12531445497519463, 37427947099199109, 11686749977281780, 37716021762939525,
      13378902704096895, 40038219345732745, 11982200979886057, 40028336173452178,
      3805592368701761, 37386165070132613, 68544489111520459, 37632457738362500,
      44059142582797862, 39811716662032264, 33936493237800742, 39728169280930449,
      67981771092845045, 37352079723124868, 57003856150299818, 37568685208301700,
      13940933522654692, 39641289926998408, 68275899222167185, 39605022820964752,
      59818872212284033, 37317994342562692, 45463218894111882, 37501614126580100])]
private def schedBlks27 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        12290524091816662, 56300220265818801, 6969382338808319, 49936201196145343,
        65201716667329796, 42891514079979168, 2131513153001018, 39692980764776337,
        21006322550669312, 52999438040224424, 26396447166219253, 51653665135524035,
        24112855570232082, 43871196506385574, 70250897101330739, 40066821194337426,
        53366529873448199, 50280309528623775, 35683626600347855, 53271065748852935,
        13704715390531852, 45108168797717420, 24936440971566323, 40517628729712021, 2366410353]
    ) [
      8887861792249489, 40159180053602962, 48835910820138410, 54358434730621086,
      60740809666841655, 51651469216204742, 67458374170948208, 43808521575291556,
      445957583706460, 40541816592961684, 154874605571816, 50032898121525376,
      38788411330968540, 53742770246369740, 16800394674944430, 44945437083756971,
      15085435265653961, 40967334891126678, 62924975548174400, 46683739211694220,
      6967715637735090, 55366771083617738, 6674944969261249, 46422106902985138,
      70539557679374660, 41486313388959384, 2690756485616098, 43909546620283534,
      17930817040131104, 56840126059596988, 55659107213100425, 48161562350065592,
      34515287637010134, 42117444119683740, 30276996449539033, 36029402534783119]
    ) [
      3276873890573543, 43368707310637985, 30845250765756514, 40987123969647508,
      71933961528185051, 47640189573431182, 68072379026685748, 53152332368226768,
      2721848293635705, 44296712422113447, 53928088678079249, 41059694304056725,
      67429558735245514, 36029399565146253, 57641947398972663, 56008901460671700,
      68596733989863553, 45652434989224878, 17902500056964892, 41514900120829592,
      53075421569520171, 39354324690516110, 66060357826609152, 57993548000080576,
      31451773907880156, 47383096759287479, 35358080445621332, 42147130077959067,
      26337205778814006, 39752354208105104, 30575114118532168, 58785148488537517,
      70304443318062951, 49477700703373247, 45496557002926845, 42897010111339423]
    ) [
      27270744522063935, 48995012683065803, 15660746332350848, 44141672507864993,
      49146269691124689, 42918993129452185, 60121199573375034, 42750763672784535,
      45009154877265914, 52859876167524841, 3563215152788375, 44434150167552421,
      2421028420361289, 42584737047924889, 40135037390919413, 42474781472626582,
      13933043953407783, 58494963270669515, 12583050439804105, 45661229152816046,
      31133610687045545, 42630918818054298, 40978650564499148, 42006383277989269,
      727484067714379, 62477379099453568, 66079380936447097, 47645885440723642,
      2426916937639232, 42847528212441245, 35629917334116113, 41357663263776916,
      1005102111625878, 57021425231331730, 34004556764666592, 50216588774717895]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        14518830132792604, 46162586288075673, 32842402313775059, 52234183584725680,
        3575644957227523, 46904798010541745, 55621749010572078, 39963472000460695,
        54764327191871488, 44926715454557075, 64363360486400721, 50858673449149100,
        36230942765856744, 48107681230175668, 23819964383733540, 40866186868055452,
        10005742643875356, 43596283936685711, 43809923261832828, 49599716378000296,
        66630815719011038, 49151131321172663, 46060864183446388, 41955821698739872, 2386530682]
    ) [
      37611362062083831, 41155359969642651, 46302636042457022, 44496796240879759,
      71682092127134198, 51796567772949933, 54250143123880965, 49270983205691576,
      16787419360766780, 42070169783917216, 155656325206674, 42876088922068864,
      38179779464895680, 50152776514957736, 25821406622758259, 50432081460294844,
      68302146240425959, 43219179400150692, 48009301519472146, 41220202397958285,
      5804921494935345, 48989475327899299, 54807629707391155, 51352389537233338,
      1597331362394977, 44503428694903721, 28027992732047925, 39882035527794576,
      31413590888518025, 47720614833809054, 15395442063027416, 52395831071394741,
      31438124238288634, 45763486804452013, 50268707853344469, 36029406259486611]
    ) [
      55662105108201571, 50213280491879100, 62952330658295410, 42902512216247202,
      4663100003358127, 41337788922935439, 54222156582983930, 50755313802712743,
      51440839371176115, 51551401863377600, 66616844079772524, 44038327491627175,
      22398845379385635, 36029403793143185, 38734714864177667, 49237964888614561,
      21316260758336125, 52495899498151871, 37911546202601361, 45363260176260012,
      165745369128281, 39779846864342676, 60964365961822208, 47631550247879579,
      20464396848442727, 53619606521953976, 23561429166766887, 46755262113868721,
      27754635374731845, 40402181283936151, 48572401478307172, 45919587641509269,
      34532639456601990, 53465652563153330, 28068606566973045, 48003227038392501]
    ) [
      61254327903027200, 51259990344409252, 499757073873991, 52435425654024389,
      35938206255134193, 44479237677476521, 54489445184477933, 40126196399332243,
      17054114689092886, 49153295027223709, 30328098621731745, 53591029974377924,
      69721156378737474, 45859147822593454, 31693403811192629, 40633080051151254,
      47428535943532207, 47152151484176021, 61562067039137003, 54802702223381179,
      19624554835590908, 47370999363023284, 56467509690147913, 41242220146658969,
      155205334175894, 45182897368645504, 13704075284686298, 54843359020780468,
      15969563501249259, 48800385954309049, 66042838714591616, 41980005468248733,
      12823524939961053, 43351079655571597, 8912102843653951, 52759749656190638]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        57010079632951309, 41110256789323147, 23251168783406317, 46346210132331165,
        30303522527028881, 48437530926538154, 26917172691118224, 40624296189048477,
        1839322022903808, 40209745592409482, 51957239768191275, 45247783386238361,
        66048538137633632, 48579357339892135, 8344097792961541, 41963519890784417,
        30548124544045167, 39517044425201032, 55612110848691758, 44357165143075221,
        743964070682547, 47792094716560550, 17918967217564554, 43201588086522021, 2424608037]
    ) [
      66611836065721917, 42930003261793443, 39828711613437014, 39873289648735368,
      21838558249324550, 45408313728061337, 3281740067218454, 49454579282841770,
      20172669748228218, 44048224472009639, 158040109389999, 39203678578038912,
      71092152218324250, 44453921914630804, 63232654452760653, 48481498657530023,
      22428519737110114, 45232414265934763, 64058374631890099, 38694598184272015,
      2690060635310825, 43378581439768977, 31702925810375903, 47711830602605732,
      36502423144606459, 46229687267732398, 63781529699131614, 38316330969992340,
      71930224813443403, 42202086314622093, 38173139365107965, 47112586313015456,
      41846998791071880, 47346808714567853, 6928231625565286, 36029416359655833]
    ) [
      9194638741775548, 50348493879771564, 48044495025648771, 45753592407761580,
      3544123719261934, 38775926830329235, 58424309364263851, 44457218620741779,
      28612142859329706, 49184096268260521, 45233159757148473, 46915790794719920,
      53369880471577331, 36029411578045847, 55324438147926378, 43238939671315343,
      10311403111226574, 48314371078107557, 63809073637666149, 47832799246348722,
      63507244605220574, 40321924938076315, 51381039659712512, 41943696250176396,
      3551992104982635, 47616167285868449, 37627640138803863, 48938923546778032,
      58445307880253999, 41673244391774623, 27734981094707049, 40779298470899594,
      30569161683538921, 46577110006888605, 56201642778798109, 49800940343983532]
    ) [
      54481293126631424, 44275794068218513, 31145864328421502, 49871299709548458,
      31727093987718164, 48375963862562997, 34798540757641288, 41035515735675549,
      60951777125633632, 42915676357191565, 41273865295207468, 48868531750116261,
      68034806106992586, 49263285332454582, 32551031687064602, 42220808799382689,
      65442934475887123, 41504983678271370, 15655171278608188, 48014193699597985,
      37630487739935865, 50351815618056371, 34525973672472409, 43508355102265765,
      156820302042747, 40328491707302016, 9739175868142186, 46754133056690845,
      17923373848701269, 51015915238704559, 34248072167404350, 44659560386262953,
      56174854754573054, 39456568047042702, 40977619692326550, 45538056754431640]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        19850301696541936, 38437310148569222, 14509578676767133, 41954695124636302,
        15932475809240890, 44838765882898844, 27199566728765404, 40263659848184736,
        41241764263264256, 38101954790297989, 56728608952059954, 41042086967738507,
        56180957894186032, 44503408175701145, 9183149554769564, 42236210183163297,
        427359983406882, 37829272433681029, 62074859665327886, 40170162519486601,
        36756182266056938, 43987725813616023, 9181362827206002, 43995446235906719, 2403767886]
    ) [
      28328408726479447, 43429194493042853, 20125463250834726, 38041480577010053,
      42936167586957317, 40937631886687115, 36478100365939689, 45055367190424986,
      37051689141379311, 44928946791556259, 158014349875847, 37784191685178496,
      55037886461413097, 40086598746574473, 52800118494367888, 44226323309768343,
      33672361605242656, 45996573236297121, 29156083143450605, 37595073369604239,
      23792828294727189, 39410390455114888, 38441222431673788, 43505033296666772,
      9464104824773688, 45840433324015264, 32540135210525459, 37448816295619989,
      12814251922720113, 38868324243209607, 13949476323232622, 42805731318274449,
      57312265247168966, 45234595655805086, 27760828787368418, 36029411427197339]
    ) [
      69129236313576285, 45375328161161882, 51972435629417213, 46905888613024677,
      23531467043218096, 37630235714294677, 30267663301576295, 39960153281967753,
      54207171247640592, 44457223989631383, 65763017243992104, 47142274955792547,
      58158004565747353, 36029417802515865, 69672785633969554, 39314731618077575,
      12826484147064148, 43694150538152340, 29732167178558727, 46493553314178466,
      48874690510694038, 40656182881939102, 56723862950477824, 38788058619291526,
      51103679321574176, 42842014228884368, 10869735916280400, 45900909617717408,
      36774225729922072, 41987712401473955, 65730301904588863, 38373537333286789,
      63204479061428586, 41896419464835725, 4111411558979410, 45495183669667997]
    ) [
      7467812223877120, 39840304920683401, 45762518211268499, 44688124065503127,
      14536933738127625, 47972416737461158, 31144305353927487, 42002003921835937,
      35050719149068433, 39191584520576135, 47165769871363286, 43816196479809939,
      25229752974941632, 47145573926917796, 67740287181760809, 43266459692020645,
      14777438703162698, 38677006116137606, 12541062044093115, 42840913375047312,
      11152151503411894, 46581517029436833, 19889665654105731, 44406671873031849,
      158989309680063, 38253688435116416, 29989985126549766, 41795262230785677,
      66599612308100923, 46132907141502109, 40715966327661751, 45684323661705128,
      42948399934053864, 37887546432159888, 11410506331424646, 40765006078065803]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        8870853435753424, 37365272688216452, 38146394228688145, 38615432978448006,
        6348599669590658, 41945903796460432, 62933118932457006, 41413757030027413,
        8307963613708288, 37297102296200580, 54752752126821559, 38204210562878085,
        12819655058688181, 41357653885004429, 68563473145238589, 42528653935167124,
        13656112658158486, 37267415331257220, 19005009173120137, 37918334049952901,
        62920079173060464, 40655054294518922, 50266083505443385, 41957998541986965, 2481821316]
    ) [
      30848695349253845, 43509434514210456, 37013961874380981, 37197044892545667,
      47434226635080816, 38192115733641349, 997542826444964, 41472003413052813,
      17617902533776643, 43030041589174680, 160088878324190, 37126675359829888,
      3805064072234014, 37896343364402565, 51098005595850592, 40655053573085834,
      53644758196195983, 42647407616835222, 68566247757289509, 37090391123558545,
      43492644941956075, 37662144418082180, 64607180960007776, 39822711946092936,
      69968043352821643, 42504470316586132, 30003832320071323, 37077181365640600,
      21537356237800404, 37489518978566788, 39836171813422496, 39141006079720839,
      60113447001623749, 42413203804938386, 40135041671403208, 36029427315382935]
    ) [
      63766393913378989, 41482997942116492, 46047768547267941, 43733740036995225,
      60970722711739373, 37084877946888599, 1834683399439362, 37899641899285381,
      43498129684924259, 40594579443690890, 39008780966007421, 43404982838942871,
      16215698873490090, 36029417064506780, 33922306751497123, 37654447601800836,
      61792418307933788, 39768835289123976, 42383731857198940, 43188370642758293,
      18184151084210600, 40710072608474779, 2959651285925888, 37459831510292100,
      38428771159410062, 39104721860457351, 70527922352589976, 42640806084142738,
      51115387612534985, 42951988980905881, 51654517254557929, 37305897902666627,
      33924179381748968, 38582447310843782, 63487732175047254, 42129523714693519]
    ) [
      14219805716873216, 37930428778520709, 44342614745909114, 40544001321606538,
      24372563214504538, 44121869872903832, 25225299057941798, 42385746130086559,
      47433333201735532, 37689632594657412, 66577587402933881, 39739148340958344,
      65464675650015026, 43481943871299733, 34794056676449281, 44113089953427613,
      13933013756057313, 37491717901154948, 42932456687633832, 39091527771258503,
      62364911801437303, 42859611297222546, 19030208123607459, 44601266338052252,
      158057333300424, 37330087527581824, 39272294134940926, 38590144110346118,
      48850844405893711, 42255967870645391, 20154484493555606, 44105380000400283,
      67720611706346930, 37198144336822415, 51374932144194677, 38207509164869509]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        17033988546593928, 37170657452370308, 11122747741209609, 37360874541041796,
        429009344038166, 39099223547318407, 52792430415088756, 39116832561328782,
        9152577527864512, 37131074496892036, 64321273523307488, 37223433926604419,
        60663640735450237, 38529668957511045, 69679597547588190, 39700676054236045,
        70232481454197420, 37084894337426563, 46306638787347378, 37109083240901763,
        66292315625718782, 38034882534143364, 46033577753872467, 39804028939234188, 2321714370]
    ) [
      11697921335069730, 40725435202466960, 1365896471547447, 37353179368973957,
      39833710770881698, 37377368054338948, 7465265281402108, 38460399506865286,
      43783822374177271, 40738625332158350, 37309313842516019, 37348781322463963,
      30826417025746073, 37298202277604228, 27449352965096607, 38052475726845061,
      39840737418971184, 40481334259223180, 6067313732390963, 37353179492122508,
      26322774448506008, 37246524643889796, 62070332713567330, 37756703525383044,
      29424002884273882, 40152573420502922, 64333905220964183, 37353555481047181,
      22945040367912086, 37208041317482628, 34203975007765555, 37533499997334916,
      37585046315894234, 39686371648595592, 66022626218511923, 62098816082220686]
    ) [
      15065239979132199, 38419717425646214, 47724179984648628, 41221315567304590,
      61238333367685995, 37432324158469009, 54189192285422824, 37386164583579012,
      44901102173717742, 38066769981998981, 20418641900111904, 40784801800521612,
      25775608739893720, 40628695895890320, 60100295647855891, 37370771420793220,
      15627382469985486, 37810580752792709, 7750244993566452, 40258125966322314,
      24649043087102036, 41887603776093586, 66574353258494163, 37367473020131972,
      67700042705962174, 37624761106635652, 26889014383248922, 39611603196941960,
      39002634786475619, 39840327318753425, 71359519369630026, 37364174535582852,
      52500230753191089, 37487320542531972, 6058749401728378, 38990370772089479]
    ) [
      27448605633445888, 37324590791552388, 40115920193225920, 38052476163062917,
      68550557971810309, 40957425344169355, 63777440742085361, 42179002006440340,
      38426340105425985, 37321292474779524, 11968126166533290, 37806182639171205,
      60948830906910444, 40231736277947273, 43227735890956476, 41404939277485716,
      48272960998380812, 37325690772955524, 65166699194713249, 37630258698328196,
      18726192813999647, 39526939543298696, 52514400041209408, 41315886737647762,
      163610676269534, 37345482452026752, 54189089203258536, 37504912946683012,
      5214354537285002, 38907906561139335, 65178338705116108, 41669923760640400,
      1006300378010368, 37385065591734677, 51374356617004225, 37426846832574852]),
  (8,
    m1K32P56Cat (
      m1K32P56 [
        71638596404282073, 36984836195554946, 13937948479095717, 38527469028255621,
        43500122598574662, 36711435321588361, 26883478098575976, 36698959548407682,
        35327800414732901, 36795717662182530, 48839548495299292, 37711620864226435,
        24639392149112638, 59591923027389833, 47148881840538027, 36497745850247041,
        54467299955147182, 36563717336451713, 28009193316581882, 37007924933075586,
        33361272372495400, 38939776493443206, 27162749723317908, 36136001021698176,
        29133091740287074, 36151394369038464, 37858927688777843, 36227261560557952,
        26037717409759442, 36371301056739969, 33573]
    ) [
      46869674642431142, 37007927265170563, 32795607973069683, 37080495351366275,
      4649364445430766, 38207507705215621, 62359912396720414, 39532446262044300,
      37017897324284452, 36971642827797635, 19284624404874062, 36989234745395587,
      19285371736261511, 37751204809586308, 27736243957368620, 39553336227945099,
      30077976116104211, 36948552731286659, 11684701248062266, 36934258509687427,
      51936005172855624, 37407053643513731, 15630410449913243, 39506053268417929,
      5218117022354482, 36918865430789851, 4366244477764384, 36893576042581379,
      25195568848929562, 37168456868790915, 1836100751885435, 39178390548800647,
      57573429063551982, 36849595113455753, 60098036459471587, 36826504843416450])]
private def schedBlks28 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        40128607747281828, 39577528789006991, 44343628403018695, 42045874410944905,
        11731053106994590, 50017560509787317, 11443264627519191, 43597413061024932,
        44354585051568219, 40185569054109074, 10005489455566269, 38571459308316043,
        32260081681268736, 51478800825490595, 19051868027532654, 45606253252620972,
        66596614456647392, 40984927882503574, 70806317845876802, 38972787679564684,
        53902460339259834, 47385248385421460, 47487631073521538, 47776723113083826,
        69981688756545114, 42097653346611868, 25491767223554991, 39468675728553359,
        3247697679584088, 137]
    ) [
      66313726410136895, 40893666202756757, 10289275161841686, 39071745001148557,
      17320432885008927, 46573772999753864, 41299785879826845, 47793219361195701,
      51402974477460948, 41919528687966107, 29432335289324357, 39559936267411343,
      38714060148411322, 36029382150119305, 42974998820001794, 50401296778928823,
      47471808244854633, 43415990605722275, 31124947606804435, 40189966932841362,
      19012808970833355, 38605544705656203, 58712570156058754, 52183595110510240,
      45230088857564979, 45486405562449836, 43515189616287322, 40981628911399062,
      15918903547891795, 39071745085037453, 150416355527195, 47143343814469760,
      5550024245620867, 47856990213457332, 42115288101856867, 42056970325842588]
    ) [
      65482302581091785, 42746375105719711, 25494803808359958, 40561605570820498,
      33933967776386962, 39957962244898190, 437539289009638, 54409031122706048,
      8919756777503537, 44639769143434411, 20432231442127763, 40965134341100693,
      38437979732349087, 39733659675001486, 9442951814679763, 45123407474064780,
      19910526697386699, 47467761251817655, 27757384189387860, 41766693182637978,
      49417157418193653, 39799632620869263, 19012448182439112, 38882624454449547,
      6101325808107520, 50708067670372539, 27204476039769946, 43113619522509218,
      6354604184147701, 40194364576685458, 48005070878051817, 38804558894007947,
      22658737920837972, 53096199441925275, 31438339009984791, 45179637875615404]
    ) [
      24702778796113972, 45101573137379763, 57026413693214018, 41892035746504343,
      45479162064835620, 41013510151488914, 4381745253290366, 40779309661616529,
      21532958407758043, 49172055111236562, 35639972055459678, 42237290316645275,
      30279556277966049, 40818894143871890, 15358333028241592, 40586891838367888,
      57579867296337992, 56732330043116944, 13418649084804588, 43690872740615590,
      33097153663244540, 41064090370797716, 13388171405988176, 40463745177090448,
      721136011153341, 36034914907337360, 19914057295639434, 46510073705442232,
      40421129572294914, 41661136576625816, 60114061238571772, 40434058900035984,
      8601653666221931, 40343895725253263, 10883406326042496, 50655299954101953]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        60404349655228082, 40622085169768854, 31960292830842526, 39995285225161098,
        2420392680002130, 46674968303383197, 44946500641728797, 47033435569206189,
        46899903125562499, 41915133057435548, 19578851363623589, 38638532973810829,
        24367190092578816, 44884934432169365, 18480379456365077, 48290197358370219,
        21292041184913724, 43513847727764130, 69686022978115576, 39390611577445264,
        14495963604093585, 42770541862540685, 62946304618568532, 48662915307709347,
        39311348917841313, 45081775418207143, 66595785514393000, 40350501771115925,
        23514853806149023, 137]
    ) [
      31709188052593661, 43970152653498788, 41821722591467907, 39900792421926546,
      14507186387061879, 41765567312429193, 42678933734266996, 49289642421723043,
      19611167204094085, 45676620990113962, 41827830134513558, 40846388863773335,
      28302105990434673, 36029386378069387, 55617432371629941, 46702454852515739,
      8074794832144793, 47392981777161391, 38738202560669098, 42139436835330461,
      11698492627456884, 38936504903189646, 22393755470432572, 44665026754583699,
      3281143031177663, 48697023002516908, 31426488988707487, 43765640034566307,
      60679764335433938, 39668792045863569, 150905997659035, 42360415519149184,
      59849658953865755, 48968582308490915, 66897447143386893, 45398439917696680]
    ) [
      11737332524100193, 48032909020322994, 53376477630670738, 42435209825347742,
      38440032774427796, 39390609782224783, 150798617250545, 43807390169160832,
      50287988117839883, 49497480704941997, 20732742017854807, 44113091765625765,
      10015617166842363, 40095408765100179, 3812030638230835, 40912277922719626,
      5804479098951220, 49635991218498211, 41004760107364882, 45910821010210731,
      9177347026690125, 41030009939672472, 13947724004036642, 38607744920132236,
      70814675882442752, 46682661160111001, 44386681752496647, 47728338611863472,
      17909951947712177, 42317560386649758, 66868395528328223, 39179500529750158,
      27725287507462694, 44321971694270096, 61828264601755932, 49099450751152044]
    ) [
      37605941564702720, 50461729249194656, 66340484473664917, 46198898777830317,
      39295599039586563, 41243317930180760, 26896758360084737, 39015669589368973,
      71072433919003088, 46391278901500051, 54804962486299291, 48292399233939635,
      70546854945859651, 42494584174678942, 70810088893486297, 39557737898489743,
      6906992638790549, 43026722483863689, 41562259530817095, 49893312038141102,
      68302915043372719, 44191158668289701, 36756087851227706, 40244944410103443,
      56730077889793481, 36029385958616458, 10587577973969651, 50019723276385442,
      57613269816816573, 46090044744266156, 32821601559093452, 41159754073381272,
      62362098612605094, 38836446627091340, 36189765950802212, 46592496877992599]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        19878846525514664, 42230697323841437, 70806644292490099, 38466964062595211,
        54483019728652986, 43243343036364434, 39019475600907323, 47096091625339809,
        56193701326989253, 43638094185881505, 5791954898753706, 38836452029529233,
        54195364213915648, 41844741847872652, 63784278411613913, 45737076261354397,
        26361305170551917, 45034492542590374, 38167212301458895, 40167983126153110,
        17029238406876226, 40224036508800392, 26623916342153625, 44746400413169048,
        46060275674095694, 46261567098389413, 39861714418901510, 41738108799620251,
        6909771553477026, 138]
    ) [
      28052628955440489, 45927309523769257, 54214833672069398, 41127871222599833,
      48004095926374312, 39481854717329545, 28311344538423118, 44772786175594647,
      62949783606239426, 47171975024017062, 65761045872026942, 42681503919662238,
      46320146707682582, 36029388525639053, 53918682477857121, 43108100723733905,
      60411771397905365, 47329190456043937, 25796186280143117, 44100995711597987,
      57585193181878855, 39324642574349970, 32801869977913798, 41629233223448715,
      53087791202473547, 45854725196719261, 65487593960678639, 45488597706850471,
      13962176808722299, 40673766075121304, 151554562166285, 39886481154171776,
      68563077973708950, 44781583896040343, 19039197607534738, 46724467801983142]
    ) [
      13968404524145308, 47770099048015010, 26644025759935352, 44953130410216102,
      52240359833771323, 40161383606856341, 151185182264522, 40978309454683008,
      67723184299086993, 46040544003985052, 59297519612700124, 46350627993346986,
      13965531230479005, 41540194273902235, 14228752308408610, 38992530620648587,
      47450552011165096, 44727704084886678, 33676845594091739, 47608486911667111,
      31985740909225674, 43097125623292832, 12826308131853973, 38726497276338831,
      32524844758761472, 42944270387345296, 4679811904609105, 47552393598209698,
      63797039033526855, 44537508572367524, 25780208761215949, 39768851999738004,
      66850309277715295, 41348852221785481, 30287738258822545, 45956980650519709]
    ) [
      18173628193800192, 44453918794012308, 42684800766746784, 48454022611057064,
      18759591033350595, 43800824255651235, 45761586277423368, 39457683296721809,
      25473487696726709, 42435186235820940, 15656988085819843, 47986704851969954,
      59015293078711465, 45332467944913575, 66033947973230212, 40495640258829462,
      27174191716273661, 40464828027895945, 18464157119779634, 46098818120237212,
      16514474214991430, 46760752172394156, 33951719184049164, 41886545738333596,
      32525974434714204, 36029387183414668, 47167586650590098, 44618849346675605,
      2996485452243154, 48034003548820136, 64356982458263627, 43467666880417185,
      33656882359212000, 39115730080132752, 49692653503154547, 42721065215074702]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        56754327632781510, 43004764297708703, 22114587221202515, 37695106899970446,
        52223750878627552, 40743015744833162, 7202181613654740, 44128469090183320,
        33953020512804272, 44317602639617953, 55615993641540358, 39157519206132883,
        55317239692492800, 39432379865560711, 13108697873157649, 43208159217965460,
        11994811194055515, 45425914302918558, 63220954874159123, 40881576960495256,
        54746885305503354, 38486787903364997, 47724944497281554, 42041560855068815,
        70257477024519930, 44700222854316955, 58722874337108025, 42398924666518941,
        19297019915834364, 139]
    ) [
      11995747508722534, 46003162923953311, 57314271099921237, 42152631562057884,
      52791708910588747, 38162426956349578, 33649799776667876, 41923910057378190,
      41265464223897269, 44978403540835740, 45778349742989645, 43569921528903585,
      59271809625069695, 36029393189858704, 8594489528780362, 40589081432548234,
      69126517571818089, 44245018044139671, 12561480636931620, 44871764251173538,
      2982565327183098, 39988760851742358, 15065682269997794, 39260853568563079,
      64899616837373302, 43167476750856851, 49149993457785711, 45739277750890398,
      64630515929162188, 41541293852637338, 152787257233668, 38329555307858048,
      7754836369443201, 41994280546422159, 23814110159738588, 44840962557293724]
    ) [
      39571048002457915, 44409944503066007, 25510403323305706, 45897622038570659,
      11712567454245034, 41304894708620954, 152203124117510, 38857326962611328,
      1003478545239032, 43054225392214163, 43521344335223615, 46232963135891103,
      43524024495219890, 42726585288924062, 22113620840715610, 37971084318507149,
      51663365050501173, 41824951796242317, 48583611751437948, 45114744761088668,
      25513491461415376, 44099894035682723, 3823537055439490, 39006882103322259,
      31674716053536768, 40402161335216777, 55896940257055201, 44341775184812183,
      56753597449608844, 45397337855751586, 11710492955025114, 40690258950856344,
      41517561391058335, 39068436248643206, 36751522154843330, 43117998022948243]
    ) [
      64046314082041856, 41528077516168843, 35916645084665285, 45366535876670620,
      29456387423707847, 45078474383462822, 66596635929321005, 40292230205047446,
      60376384822283402, 39927164829269639, 17897006634078320, 44446227531125911,
      64917411170656059, 46374815873220003, 2425851756651115, 41861255679017116,
      15354334394946082, 38624227040952458, 28024208711322393, 42982755861311378,
      70824764969425671, 46436375018430111, 24667155293513193, 43269752119780000,
      42945118497969991, 36029390924862863, 62639982890944371, 41696306201055116,
      47175983460816431, 45246687750276508, 67735923389538894, 44600179443293604,
      5233068045737061, 39685290860908437, 49969794857863770, 40183354998022792]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        3265741089970446, 43508346394516635, 58707051469969326, 37167341318677390,
        45746115515483276, 38767167395038598, 20985839634778912, 41844746914754448,
        15930512989132333, 43796410907870105, 55617518385470476, 39300457311617684,
        2115960802279424, 38084361715036805, 22952036952344646, 40948629720926860,
        20712211688755950, 43171881055444119, 49710825963887120, 41037711923478170,
        66287359357324987, 37590674400632451, 8030856670512708, 39852399817025161,
        56456071933628246, 42777147304386963, 39012440352069758, 42826642205924250,
        38437490139960577, 139]
    ) [
      16208534751122090, 43495142104560535, 59001175249689390, 42538567156406173,
      47163356150797423, 37448835101884555, 34770369564083654, 39612702775683976,
      51389174450589327, 42896993669158803, 40984036518238605, 44082296514195611,
      57021203834968610, 36029396847351185, 27168496465577035, 38661612903021702,
      66865779794676404, 41835950402286479, 54493070130255384, 43944847292915097,
      27754197257723151, 40204268754733207, 56440364952751015, 38006295265374852,
      63765474777860089, 40878259382885515, 19586247356945105, 43341208194956439,
      33949185054251676, 41827172647334556, 153547477127617, 37518105509109376,
      57851622601229827, 39738048896436872, 55892993126928122, 42865108150721939]
    ) [
      11977248789793286, 41811759804260239, 55056492528309766, 44231824575786650,
      4396318310964839, 41762298407770268, 153457280586135, 37904039358572672,
      8877141345798025, 40705632735382411, 11141955104117365, 43638080478446487,
      58720292987182016, 43203781388559262, 52514490308204255, 37403736318646926,
      18726089730393503, 39506048704931208, 44915005167603245, 42902491059525011,
      7207666387032560, 44550692175426460, 28313462080117858, 39302656301315476,
      12250082177417216, 38584646082430598, 42095556636084832, 41834850420880527,
      21279362180617749, 44087786136595866, 58437404991004111, 41026714760316569,
      35606586896781003, 37939224066208388, 35336119873013686, 40796893895013259]
    ) [
      33361976758992896, 39213574501467783, 11981616832679199, 42849713863844243,
      13119731834853941, 45213703005419165, 70258117060698146, 40916762272116376,
      50806235633979029, 38377935144908933, 46598061030934920, 41771076615713166,
      9176071322899957, 44375862931090075, 11153491588521708, 42422014914038942,
      29148730002019378, 37829271661576331, 46875803634140984, 40582485268777098,
      4667953327542821, 43775520673428631, 42676777669205064, 43831611420040351,
      34502982351296798, 36029396025255057, 71080216353146260, 39375205059595911,
      31403849795997106, 42878301468164499, 46333255093623331, 44922329991329180,
      55900513801379428, 40158088242943382, 8027983218510725, 38506579867657350]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        69969074171777555, 42281262761988244, 19302350054856434, 36940841923281039,
        25759360625181555, 37676437817575044, 39274952752268939, 39975547501735305,
        60395862608809850, 41931613987412114, 18461404038862149, 39001392783001494,
        44336017589305344, 37334485288871555, 8591946879304988, 38994769170928007,
        24645641411595273, 41566566463135376, 28029783700837472, 41561084726223509,
        6333189301702530, 37098087201851779, 35612037090542623, 38219603473997957,
        12538412014274782, 40821087076789645, 19866055870419461, 42139423077605012,
        49697532917487081, 138]
    ) [
      8601052332854124, 41577561931737232, 46045646815925532, 42843123488337558,
      27741647198852676, 37082693921407114, 24915854829847564, 38134940105568901,
      40966736113469560, 40821085902351500, 42384685367857697, 42437396332408213,
      66311922482845584, 36029391327655570, 22100142977811312, 37653347788175236,
      22667731555616369, 39896381339116681, 60958864100855625, 42106438785707666,
      47735411511825913, 40266946504450711, 43773071877769829, 37322390509969795,
      71923717853775117, 38918901929076614, 18734430672554939, 41579760720111504,
      71377711809271010, 42330748083414933, 152220337738555, 37095888212152192,
      31108385922974746, 38176722050747013, 63203585695320235, 40828783188406668]
    ) [
      59821994684155427, 39713859590295432, 67995725628870338, 42445090262888338,
      1856167150589752, 42146035733736601, 152671300325954, 37255319310805120,
      50531327561729231, 38764968405339270, 66303091840486170, 41585258731231631,
      22683898067195182, 43150988975522455, 48574639523469467, 37048594062815118,
      15627038862312427, 38087660484808581, 17322503058065476, 40797995201846924,
      444948198429227, 42605624480403350, 2700987238553617, 38996991934627990,
      14781686207578112, 37620361952795524, 5497556110313040, 39808419033143945,
      64899543837740811, 42287859596799890, 33662225327429279, 41274112443180696,
      38984286597123789, 37298200918609539, 62353444089857270, 38843034704002182]
    ) [
      57847821505495040, 37965612932491140, 36180592048637895, 40690240428253835,
      13674229154943505, 42965169832693654, 43236025308715307, 41070698379628186,
      58687534983712422, 37512608152303235, 39555530069280237, 39606105856916104,
      68277076047335017, 42536349593775506, 38167083401910223, 42908005177129881,
      23800696863954247, 37195944793473163, 35612930454357146, 38680304902689414,
      47443890437589697, 41587457720923791, 66313172296439076, 43348903299931799,
      4386418298886723, 36029394817291922, 1834550251848634, 38030485058068357,
      64046997000128520, 40754013562308491, 12829821404418598, 42784847425906070,
      43516469484755098, 40136100661269400, 2115118921976582, 37571982702964356]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        36748614438587457, 40678154658934415, 9167631604879581, 36739631295509393,
        2395696296395423, 37079395235740291, 32515752216069134, 38251489478974597,
        15634890165487889, 40558300442285709, 63772226587300023, 39513772516281744,
        54186847195136000, 36927660735258498, 24070476404458344, 37695129615910276,
        2683618100872878, 39971151082648458, 6351327034969830, 40866169385654672,
        43769361236857091, 36838599219654274, 43210109092528897, 37335584766944131,
        24917637263492387, 39139906702305927, 34215275224796273, 40442855043385231,
        55046940404977703, 140]
    ) [
      37867500557403750, 39926069361045385, 54202451035393796, 41154247438483345,
      41254718125150913, 36764930665349259, 31387958203876039, 37290504119106435,
      71642182746146036, 38994769003150214, 44066976715541507, 40964029879975823,
      64055750290149771, 36029397099153810, 66290374273368693, 37054106065641346,
      24915824764224505, 38193214658050949, 4375624804632787, 40578092121347213,
      38158742458831133, 40841989005114001, 42646171243547615, 36896873872800386,
      17877928131068750, 37659944807607684, 55882126702839430, 39961254723007369,
      10010806675934974, 40984919560737425, 153968422523458, 36797916584771200,
      36736072957199073, 37312494670433667, 11688154442401034, 39070636379222151]
    ) [
      15627038862312424, 38105252737961861, 42374158241728618, 40614376021823116,
      66871024051065145, 41751289701547410, 152946208183256, 36877082327950464,
      11403917766198077, 37611565725553284, 21260275065652813, 39872192183970697,
      68557713503325941, 41356560430175889, 40413359814841159, 36756123969860496,
      29699086868382401, 37278409356981379, 62634880411010279, 38922200296181638,
      47726056920026049, 41186131782437775, 39568032919163460, 39213604181087891,
      63475572965736448, 37044210309994114, 19849215053169647, 38147034649584773,
      60388853108017308, 40595684458379660, 19863766632730931, 41487404746575762,
      35888061869953237, 36879281401538178, 13937222621627200, 37632456681364868]
    ) [
      31106508997623808, 37261916531569283, 46590626347779280, 38783660119785862,
      43785042165467957, 41323571037908879, 45199057189245889, 41614958900103316,
      66850309296787401, 37042011337072258, 11686350533264358, 38067868906404997,
      23233567763761212, 40629768832276620, 46323986407330120, 41900825900219283,
      60393908452431201, 36883679548539018, 9715059315999552, 37592873809774980,
      5497487389197877, 39808419351914889, 70809582036881111, 41556674885128593,
      66873459332977640, 36029393693317267, 29417616186901189, 37268513651667075,
      54190536619295962, 38850731151173254, 47725898002172795, 41293884005850255,
      2977003217720089, 40604500181169300, 63757056489851650, 37039812229928578]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        22668801015449340, 39652289640355466, 28300083049958800, 37023305295638156,
        25758682015630201, 36979339207858051, 60098925528777583, 37372968799834755,
        52783977788835145, 39138808633547143, 13947599414332376, 40181152183162765,
        32795693874905284, 36972742238759043, 35891819831067482, 37154163402186115,
        54189578829464648, 38436209798055557, 19012289244006835, 39320240870192780,
        43496609378175502, 36991434355869827, 26040114041553761, 37034315292566915,
        38988890692682680, 37803982475033988, 33365116422686517, 39590716351663754,
        69111768513875130, 142]
    ) [
      36456466316035120, 38294370919001989, 40122942556834102, 40098700723052940,
      21548703694490847, 36955149834387598, 20691999288099652, 37016722838082691,
      30263067629159335, 37712721986507396, 7750343777814217, 39697370103628938,
      33087605802503663, 36029408675235468, 20692046534050656, 36966144833439875,
      57002653539599203, 37350978298840451, 35332318776952110, 39109120846501511,
      8318426300058604, 39848000982166926, 27729058334805635, 36959547864340611,
      33358506385310543, 37142068606506115, 44056372292453434, 38363641023977093,
      29145444238002550, 39771044345361804, 156798737025802, 36982638095072128,
      24632717682770778, 37028817650540931, 34485243820147634, 37754503898130308]
    ) [
      44899036264235820, 37302599099341955, 3525259857134840, 38998067890360455,
      54480648902511575, 40003044033649294, 155802351275750, 36893576042581376,
      22662272583631641, 37107983209165443, 27730634662315034, 38222901790771077,
      45470838261319920, 40304310018215052, 36185454032031367, 36915553156062863,
      14499442424382244, 37001329390076291, 26603841391526810, 37677537245315716,
      62637680764815004, 39751246425039497, 12260149753515547, 39977758185359757,
      14499489670332416, 36951850930615939, 54750819365585752, 37337784008310147,
      20413973210760475, 39065139357964167, 46317745727572977, 39851304634189198,
      19843988243320527, 36939756319490179, 30543709372711744, 37132172867636099]
    ) [
      56720190706450432, 36913367000211842, 9433601519813458, 37591774231037316,
      22667649948681790, 39778733209070217, 64334682601393747, 40653960487324047,
      50243285707755711, 36841897939091330, 35047248867853054, 37267414207151235,
      60101541194990808, 38923299891695494, 64613924157688746, 40237245681093006,
      11136466068213613, 36822106595393677, 9995688174650078, 37069499664648323,
      17315918788002809, 38152532157389957, 42655869446228135, 40376878255418764,
      48289505113903019, 36029404078429583, 70512696497504988, 36952950089911682,
      16752066880308082, 37629158112927620, 41808218951419496, 39777634368547209,
      38719858423533106, 40555002310073742, 69386822312037766, 36899073483275650]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        64041112815371228, 38482390997719941, 60667995910015286, 36765191652192392,
        31387180807258768, 36695661063858050, 32794482674008669, 36816608466995330,
        10840808895382273, 37869953256573572, 14787274041100171, 38021699165814409,
        30261268015398685, 36682466773328258, 21253875483378253, 36714352694416002,
        8869616464790153, 37303697621088131, 8029967597667659, 38508784108745352,
        31172161934493826, 36682466790105986, 17313187154395722, 36667073174322306,
        41801737763193422, 36956247886577794, 63759582002381751, 38410922490257285,
        66014989662193871, 134]
    ) [
      34484277439333119, 37327887749333635, 71643028863092028, 38911208736751495,
      55038668187535998, 36883680676757127, 59253633005028089, 36808912422488706,
      143926549054153, 37047508945544835, 56722741946975225, 38488987480273797,
      71083699633949065, 53848064871972489, 58409212370060031, 36786921988604802,
      52498040286380717, 36881480710015618, 18159325796729656, 37842465298109060,
      53912665171920755, 38593449691839625, 58409217678280564, 36777026283290754,
      41238916662526622, 36783623017502338, 23225072209068741, 37325688424080259,
      12533511389676878, 38763872920338824, 21822353171974520, 36770429146414783,
      35046394159661717, 36726447741761666, 55594222078755458, 37003527658336386]
    ) [
      7462490696483617, 36959547377787779, 18722387422249843, 37723716901451140,
      69674971801224939, 39239968719807881, 47156368107604748, 36943055206704830,
      4084782386479919, 36895775032281987, 40113888644793123, 37313594114952835,
      49969159300285725, 38962885548360327, 57855032878271213, 36972997688969353,
      6055163059209030, 36871585608698499, 11684593870930687, 37070599176276611,
      45182177707328515, 38423015574632069, 68832393744976252, 38309775356372618,
      10277369315770115, 36868287140926595, 68823859522863859, 36930959572140418,
      20129740830049119, 37786389684996228, 71927020728125236, 38969486946760841,
      15128345975884163, 36874884378468995, 62068395656905459, 36851793828961154]
    ) [
      33640144575309603, 36968344175470979, 30262251576656722, 37109082871792515,
      28293558845473814, 38274579390928773, 49410985423440151, 39415896049735563,
      41861635545270555, 36980439105372547, 20129066515202900, 36996931410677123,
      20692785275241361, 37683034652455044, 62637852566128309, 39414792058487177,
      64890777729928235, 37003529289549961, 17595791725331300, 36939756218824835,
      46024979121931079, 37305897617448067, 30547145386591496, 38979377602002823,
      37027048546994978, 53522615386118283, 19847655964902269, 36917765852051843,
      19847509931885350, 37084893146210947, 33923084149097479, 38341650506202245,
      31677898682763594, 38865035640678027, 26321697383680171, 36922164083116675]),
  (8,
    m1K32P56Cat (
      m1K32P56 [
        47993306770538918, 36514238709214849, 67978257752818114, 36701157783112833,
        24070081257374378, 37918333680824708, 31955061433468612, 36406485042944702,
        24912006487638358, 36417480243108481, 35889659429814630, 36506541758712961,
        34201599852577231, 37189346364941442, 22664600492278984, 36257170320735620,
        58406948886773967, 36262446737969280, 64317992117960919, 36307527301917568,
        20126755785900298, 36551621668334209, 11965944286315056, 38215188213876867,
        140739635871879, 36029346783166592, 140739635871744, 36029346783166592,
        140739635871744, 36029346783166592, 140739635871744, 36073327248277632, 2150334507]
    ) [
      21816876977798812, 36657177586452098, 15342810776830519, 36681366909369218,
      61786675860308581, 37162958371103618, 34769325869728947, 38431816784820615,
      20475331133671420, 36650580416020866, 11120638880940592, 36642883549407106,
      29698163438879285, 36862788274129538, 11967494789104460, 38261385888930949,
      63199475385927789, 36625291283398022, 4083661382451737, 36605499667516546,
      10276149524660742, 36701158168998786, 31669274263126666, 37613763322707331,
      15912405133854369, 53457735878391944, 64882084550574569, 36558219962868609,
      66008104715387361, 36600001807380609, 35327658677010968, 37029915568290946,
      66293964907185205, 37853469423928454, 48556287808866051, 36494447315364481])]
private def schedBlks29G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        55067573748344331, 42042677463233693, 54483062751400789, 39344428649652622,
        4373477323475712, 38142642458493577, 57286971837220621, 43558880877215877,
        21015273526240022, 44983919956988070, 70533767968561944, 40293323844493459,
        13946216440958453, 38608843089540491, 4652632980162711, 37644555839249031,
        4672329860415488, 46914689370153889, 10311171239486547, 41835965586156700,
        22957332774621876, 39244371480885902, 53068287511595688, 38050282089230216,
        147160717166263, 44832141415080832, 51975261807355442, 44358296079091108,
        20430328744876524, 40161380200973971, 62359525881712010, 38530776505656970,
        60665895643416660, 575349875846]
    ) [
      39306611487124126, 42405523095304865, 44913901401969774, 39606116225547919,
      22952092819557373, 38605543313105546, 10283017286551770, 36030479866525576,
      20174039655814865, 46260462167757227, 17336638078229916, 40547315224885397,
      4658478526533330, 38895819734867340, 32238580876937647, 38142641602829192,
      24347587750758208, 48253897870972053, 44372357879801835, 42237294611742623,
      13669702238049259, 39462078172236687, 40965743994440558, 38320765858811273,
      48562136629872572, 41691831666629766, 31432046661115452, 45656825267590824,
      46327770390371410, 40423068397646740, 42094147910536802, 38725393033386379,
      41244908241127685, 37819380671128967, 22116811684218367, 47579899508384156]
    ) [
      26925401987003203, 42520974718757540, 5789296256455871, 39820523794795408,
      43782503833439455, 39103628959241099, 48003215412136652, 39083836290281866,
      8623012282927866, 47029035895467697, 66032784028114854, 40717741993479829,
      1281702236491644, 39280654022373773, 37307200660409141, 38910111439807114,
      25766262747073078, 48960833094419082, 24108603462823541, 42522073777377443,
      68276655186482370, 39735860359256719, 5219908031188099, 38898017432680843,
      46313321860073982, 38730887990974601, 28897633490731009, 46711268142873518,
      51395771698552535, 40653969496973461, 42658120080723768, 39102530739500172,
      39839509069859456, 38556063729537929, 431779651750107, 48887201703438720]
    ) [
      36221695942295595, 42484690549869220, 63492297847706830, 40178969518016912,
      10007151624883774, 39533544632803213, 67989442021198921, 39344425092767627,
      8316420534143937, 47077454136798080, 29440457232785466, 40754025491299477,
      55888547806351312, 39565431577333133, 51663704391781449, 39258661927492491,
      38996913818012532, 36049188291321227, 42409562355644444, 42376936782911650,
      2411411847287889, 39877698986645904, 71367433808350498, 39231174170360971,
      11412005318658884, 39221277340938379, 38702854589549429, 47430371363786927,
      42388533795135388, 40705646778355861, 18170394114625415, 39387308076350093,
      6626999437527970, 39110225425006731, 18167374692256505, 47353217139042187]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        62949693405109880, 44738717556012451, 60402751920512658, 40642975202797717,
        25487102813507297, 38521980899192715, 26325523278170154, 40678134944628870,
        41265154967442504, 46164799102460829, 6930245958476366, 42293370191409566,
        12262559288955982, 39268562062133903, 15631681812990607, 37821580550049672,
        64897825779712000, 44118564694065043, 36771988012376099, 44512212674452386,
        50831159565000145, 40382386635199892, 49974644090375689, 38357051571294090,
        147744844318615, 41513779217577088, 13400854584858264, 45776670642295967,
        61535459411468476, 41962410799162781, 21268701964374836, 39076144356326798,
        45467363613968873, 577145076615]
    ) [
      39866988611934847, 45385241046874533, 15652100458258444, 41165251899954072,
      47162222234275986, 38832048127584140, 26608119258777914, 36029373912372359,
      54489775792557222, 46424274199475609, 57879935502755106, 43010270143924895,
      67996730721539721, 39652297945344144, 23232760334748628, 38114055172956809,
      35043636854228698, 43089404093372300, 4965483102903435, 45060879479443621,
      168812048981754, 40903563787173015, 718082264960954, 38679213578587532,
      63480795738507444, 39520296201771142, 55336739101249843, 46382499049204891,
      9464731948524467, 42635326360837791, 4100845838767467, 39460979767941520,
      56164714124708659, 37972215975124104, 60671461790090843, 43651264350039696]
    ) [
      39862014954476673, 46118629462695587, 10309427448750605, 41685329590635675,
      64896644735865406, 39121224333053325, 20979646237805111, 37928234402692488,
      68836284814100042, 45638103957280403, 25231814668232220, 44022936744553378,
      51110362458069219, 40021740059951250, 24922791330024714, 38380141130915722,
      21258801894295497, 41495078442631302, 8339574977697755, 45759082415936421,
      39861645699555547, 41425840484330649, 20422855373721961, 38979385051331725,
      60385640458258875, 37801788652866439, 19020363826298880, 46154885008933783,
      1023274428573188, 43458881491299489, 59835025861482416, 39838118531052689,
      60669533542321265, 38249297217135241, 147671827187540, 42412091022045568]
    ) [
      50550423170613248, 47158777344189341, 37332738939266281, 42197710750268319,
      3817987858076637, 39376315208293263, 3247581712124690, 38122851014310281,
      147431304234743, 44012997283140736, 12287783985324706, 45390734444145317,
      31972185791765438, 40372490208447892, 19294361260166700, 38613241236717963,
      4934112251840664, 36029373341933191, 2422497211551553, 46623311910033313,
      8621960582439809, 41942619673688221, 35905447996461841, 39255366932715918,
      50534986951133867, 38039286788400264, 58687534896416430, 44922309707111310,
      49722130525365498, 44714530716118947, 41822753396398645, 40200963475229075,
      59826246796938655, 38504387874264714, 52221517491111992, 40119530038904966]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        28597870489736733, 45212604097728667, 18749635138854840, 42170228915458459,
        32528087587394470, 38936505121303438, 33925785748015419, 39454365685121158,
        62368545398558367, 43594094845858709, 60411981862771946, 43743643728500639,
        66874924009822819, 40161381811626387, 22670214121557275, 37854567660538505,
        23797750368206848, 42104233084922254, 24095168524883784, 44989404478864284,
        30288661757271665, 41721617568100762, 21549227740009058, 38672618052376717,
        147882290350167, 39983240777888384, 66592160434262195, 43854682742352790,
        38737755829018079, 43420382679325598, 45199336427264403, 39827124941545106,
        28580127758257151, 577715530376]
    ) [
      33662186648671029, 45118038061316249, 47181270710264198, 43466560607367325,
      55611690009073293, 39458781768128400, 2402345025833721, 36029374432490888,
      1284274898635318, 43060823535729555, 14812193789549300, 44383570753542049,
      11992341570624604, 40828795889166487, 8035632786345817, 38303175467990923,
      71635383828449084, 41315865883107977, 34789246218507476, 45249984120786842,
      24661756428263633, 42762871789806236, 43788413821490428, 39197093655347087,
      19008501054671387, 38782523899540359, 29997398323793061, 43358795549012372,
      53374982876535800, 44083397686955424, 26063672326593334, 40494539102970261,
      15634396283113017, 38081070629463690, 29424655588689526, 41683113235902348]
    ) [
      4385503358914158, 44503400927799447, 5807365445099744, 43986637341759648,
      8045081871883039, 40000849959801747, 36462518042463422, 38028292578124425,
      10848995047933546, 42395605679576974, 8617309017970879, 45132349026995616,
      62096300502261411, 41498409073888411, 67710509728436642, 38730892319633804,
      30547875568191668, 39937057832829062, 25779349672137025, 44854150455521688,
      50560435032990087, 43909668340057246, 67716436879382682, 39727067051340945,
      55883441018145753, 37839173642088328, 62361681923702784, 42758451731066768,
      67446884839627252, 44707931901506976, 38733160156798349, 41163052675370905,
      999832128229500, 38518683152864908, 147813567465467, 40660547171676288]
    ) [
      4098582266544128, 43731531886631827, 58726439167237717, 44462736328951714,
      33099296925457752, 40555012930376341, 69396791152643725, 38388938096379018,
      147753434908587, 41281779680406400, 39013746010002854, 45861329816297885,
      10588527286329683, 42174621509521821, 59268502436746222, 39154211191876750,
      51096996294920736, 36029374197597831, 20708599534095293, 44131760645589653,
      33956065705107393, 44268117032937377, 20431368153963773, 40276831925072788,
      17041599361944997, 38209714865656970, 38702811552450316, 41928304463100555,
      64910865525348202, 45483096709111198, 50838289295646666, 41832666413798812,
      63208026810847944, 38942001991552653, 5497328501885291, 39216830992508807]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        58428582948278418, 43108105790616981, 61534372731067019, 42959679539345308,
        60962111192602426, 39554442383590801, 54474197801077468, 38391126364782726,
        11415411248368230, 42117429825039760, 8893745943058109, 44149364273948314,
        15367533007903641, 41124574717686679, 71086375473090605, 37937034019041674,
        10564329020162048, 40473632845866890, 35067169212043887, 43271935103559830,
        55060031662496564, 42604532552316059, 24086355198187064, 39157512495077776,
        148225899858313, 38814444146813568, 66585825260375009, 42269165902628497,
        53930322046261038, 43867888290637978, 20714071485094485, 40671565575461014,
        45752051291819713, 579124865929]
    ) [
      18457001595866562, 42800238155906708, 62378063200295259, 43610602133640861,
      7484764751370677, 40343903661127062, 3529881349295510, 36029375439163529,
      35900658972198708, 41693008639256717, 1292804864447863, 44336277492491929,
      53650844305497551, 42381325433854361, 55045411403830091, 38595652070674829,
      4644339375441883, 39752341205353607, 8888402900782873, 42976162348424597,
      49712316325206520, 43281842855270813, 51112750471813227, 39952471649512851,
      64608615538854967, 37977681388025223, 57857360746285261, 41874435221817230,
      38448124569163274, 44320886795994521, 28879525914320094, 41712819763632792,
      26614901134561696, 38264693735472524, 42932400749053627, 40117385525111176]
    ) [
      33652591544142447, 42463780802914961, 65754190940837923, 44372573305078428,
      24938309293153288, 41094882753207960, 22954334845374529, 38173431938282635,
      13660149927413399, 40807886846984586, 60682586108236724, 44011915488864151,
      18469384237850131, 42883811492152988, 34219243888089039, 39257568892074640,
      44059271466355218, 38827636809531526, 29432300870143039, 42645203459550867,
      40422237616117967, 44022924614467485, 64062420500781764, 40723241128751511,
      13382841290755823, 37896350696269194, 71364573273358336, 41380739065709963,
      31128538202608748, 44199934896486552, 58718819834371632, 42684795223377562,
      9729439121249670, 38928809513019535, 148058390563066, 39329021829798272]
    ) [
      56448310788980736, 41887627398365837, 19590671238731399, 44958614395110299,
      19874452696768178, 41929431490057626, 49978698611987165, 38719898042247309,
      147908061268084, 39834804560629376, 14799952960393178, 43558910758992534,
      60411084206087335, 43472060212400542, 8045635952417124, 39939277073766035,
      37306045313813585, 36029374835162248, 35339701912045661, 42214186596595087,
      5799153306212211, 44715622862292636, 31694949997452653, 41479720664624281,
      35059133255291279, 38445015672490380, 13088588674402182, 40295507784544136,
      13675436052812280, 43787612046518679, 36203428759969141, 43152097429673629,
      56175872658151579, 39594024919632273, 41245599753341741, 38282246108909959]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        69400020972899306, 41888730030754448, 9454831859045799, 43299430091804568,
        58711041530370163, 40153689323903891, 17039168386534604, 37717118774411399,
        46876585322972958, 40672647386577803, 33096032619303672, 42727669784515733,
        42390354835904751, 41638047604209304, 63770366887891613, 38075577030871692,
        69671527187251200, 39232266081681798, 41535230949428472, 42014076705150354,
        41261916548339161, 42967375550190744, 48013386073937679, 39679789796270994,
        148771378727713, 37948019353902720, 51099934057138191, 41130048602645900,
        48859022166889332, 42844219426365077, 6923266519701828, 41279600421333655,
        15636221685961108, 581289197963]
    ) [
      38717105285925264, 41641335300574862, 30846281540408574, 43563310684598423,
      41544070181329620, 41377456821969814, 38997906000941096, 36029377284718730,
      23793201953277286, 40047016948729993, 58146364926889961, 42549546635861908,
      51116766298347548, 42374732340378778, 30279500444112154, 39024470128478096,
      22377262915684562, 38591241575095685, 40688542538959557, 41813961981686927,
      55335008245749077, 43503938784781207, 13394884563868098, 40735337786631573,
      64047375015644772, 37498294318344840, 37023724170479165, 40318600716497034,
      2977759135895922, 42622115762266773, 57309177138157695, 42038275071299993,
      37314167228175308, 38550573520040846, 8590628229252914, 38915602018420614]
    ) [
      27455417525307183, 41159735567584908, 56178359415051256, 43350001368674454,
      21280844009020231, 41981098738558617, 50541747359618136, 38418629054425229,
      2680366682900222, 39437877054573703, 58988487703367116, 42371422648316307,
      62656312615016296, 43158695422164634, 12830289606186928, 39919485898067860,
      1276041397767177, 37970009200263303, 38434350387988570, 41545670541121677,
      9453899833775201, 43475347606863767, 55337774283987788, 41647941313004439,
      11415067706823282, 38012902770890124, 11407169091371008, 39763337949072776,
      8887677038202574, 42450589414925460, 4672982815905714, 42771661809443227,
      56739050216199816, 39484072666329234, 148517967333999, 38272378941570432]
    ) [
      47155676556656640, 40293310640397193, 60962162689347946, 43048731642619285,
      62377994495564360, 42616627264118939, 48012621570151994, 39232280611186320,
      148290326464955, 38680302218260608, 67148122369854295, 42107534958628240,
      60684879663568546, 43872284441264793, 8329464569436789, 40776023005277334,
      59826096485076748, 36029376412273545, 5498866082219541, 40668248987724683,
      30282116084110126, 43190570219683478, 43237056133438166, 42266977734559130,
      13388862949922062, 38824355371511695, 70509483929798748, 39072833489819525,
      52512767924669606, 42277962599634834, 30849086189573882, 43557822370916250,
      7483587921025329, 40340606485287573, 30551062499265937, 37683012271797896]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        16196701935863843, 40815584569294988, 10576784636088951, 42208693115460756,
        60401115464767197, 40461553284351892, 58417068019650122, 37323489216036999,
        68828214671279425, 39400494833677191, 22395456521080132, 41640237500389778,
        39571026550166630, 41930522478715542, 14794713077289771, 38236109721582478,
        13656546516893696, 38220702499072389, 2405433114724605, 41125652317748877,
        12828812083630748, 42285659634053524, 21274534615357156, 40012945141371027,
        149394163731539, 37471925433531264, 56725589547255250, 39631396184660360,
        29152269025512956, 41646835694241426, 46326756706653309, 41481915711516566,
        29711173122560399, 583721948044]
    ) [
      26609227345594012, 40114089305560970, 52234595848327266, 42076750461822099,
      46891931488720446, 41357668515202711, 58421728120246596, 36029379700710027,
      34205370882229294, 38878218908304006, 67991868691680149, 41546777200049039,
      70532865962054710, 42661702610118293, 22116592987510358, 39371923805686929,
      9429413996497383, 37814977306084996, 23232549841504088, 40401065095248779,
      1288054563770846, 42142721847360660, 26625204887852696, 40895866467562390,
      67989351864700883, 37178336434699401, 13376905514943669, 39144304648148103,
      32808505932942459, 41597356613998481, 20430526268937301, 42340644073973654,
      58425164147496124, 38837551188828047, 46588556084283334, 38008493953078148]
    ) [
      31392373483734340, 39653386014547080, 12827154170547768, 41988788491388051,
      33099215237780946, 42194409631553688, 7478120343114799, 38734195082500496,
      12811979785799556, 38348247039084933, 69960411086096800, 41390641901432973,
      42666559795598293, 42834323989483157, 16490400627202178, 40542916222040468,
      40120825157946817, 37462029157531783, 28578560031884780, 39891984215367561,
      42945741208063770, 42041565737394835, 29440392732710403, 41741404264178840,
      66586332124910300, 38165739702300813, 58411566035140608, 38609934329757829,
      57294977748339358, 41470910377548430, 52518325717537764, 42848619049946261,
      64620985238067118, 39996452617924498, 149127871368127, 37634654916066432]
    ) [
      48560659117998080, 39084929493491846, 46319510975974513, 41865640739558801,
      60964473420092792, 42983867217932695, 41539659179136808, 39729269799219090,
      148848690563916, 37868853593945472, 12537295304492978, 40855167893873548,
      17333227765928745, 42640807057285781, 20152680614566041, 41243317544261527,
      27176893307654474, 36029378610161291, 37583951081342113, 39381802179680391,
      66305690330697059, 41948104984070802, 17617653426918815, 42621025327320472,
      17612641165022655, 39250973164563345, 40391661430409593, 38099754122828932,
      9723692311021731, 41268589383023245, 26059360071684949, 42755157625539733,
      61528140676110529, 40891467380831893, 39278418893115408, 37292685643971465]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        37022152197244355, 39445576437839240, 13951413381926193, 41199327901757073,
        31124848779760318, 40666066524043668, 42654593880788595, 36992531854000263,
        46308120563647460, 38369138783446149, 69678158713424251, 40819989544852876,
        40693151129506202, 41724901405687186, 30839667234214895, 38131656469271950,
        58972707784916992, 37584077213422467, 19571442385323585, 39618202951122313,
        35906620501888517, 41201527109561489, 65464950560559812, 40089914260490899,
        148810049096794, 37082693116292224, 9435366772343869, 38580247868143238,
        51101501752969796, 40910150874151565, 39285746182164855, 41618249331450002,
        27741187600913055, 580785937548]
    ) [
      13377004301944047, 39026655796672135, 29992798376266729, 41180636338287248,
      17050747755598537, 41655638447945364, 23800310285505042, 36029380841581196,
      58692199188562747, 38004096158233220, 48565877576599555, 40531906962182027,
      43226292775915858, 41644635681123730, 12547680735499438, 39495069057691282,
      11399738836355624, 37353176583873155, 58976538947192147, 39246561477718151,
      12261283603844247, 41205924367540881, 28028396401103550, 41178445905187476,
      10568817392848972, 36900159992876170, 15063972941038478, 38176721715192965,
      26330217717926073, 40808988892033164, 40411671856124263, 41693014628953234,
      29434353960850592, 38882632155425680, 35046982527518644, 37463129273399427]
    ) [
      5776166305432645, 38567053426615686, 70523592975813194, 41128957546844813,
      64901382126277254, 42176807731233427, 4101043411981649, 38880433434139792,
      12811180921882626, 37707224227033988, 4654028838635200, 39890885760736906,
      29152346364481382, 41576465641432210, 19304806753735746, 40557212775733653,
      714843825933866, 37172854243983496, 44057252770645143, 38796854527756166,
      71931689426848545, 41186132420010638, 2414001721086647, 41999786879271828,
      13950670407177186, 38280090690015118, 34203549792763904, 37847963527351684,
      64327600086550363, 40147074771854730, 37878409947418828, 41601754727640722,
      66592108923098242, 40026140539225491, 149505834585170, 37255318690027136]
    ) [
      5212219905703936, 38131641033801093, 40685488773761175, 40956323919937164,
      56457038333121083, 42128427340548499, 29718878403597929, 40019542412462483,
      149462883667061, 37440039311111040, 29140711113393576, 39498353180518280,
      6914959873510787, 41557773541099666, 12830628879569940, 41501707239575446,
      33651861451805075, 36029380975794572, 41523007304795116, 38343849579794053,
      20420222473308527, 41088271506116237, 62649595195003543, 42195498573257875,
      45761165351425592, 39531352119310737, 62909659576306204, 37574181591996803,
      16475136035751474, 39705065024030089, 26056039996755521, 41564371063845522,
      4386611509498909, 41025612077683862, 8598608515141640, 37096972574261386]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        69107915804607539, 38480191135596421, 69115127158770127, 40547306450117516,
        55046476540121083, 40873871134510480, 17040633003806563, 36808911499559047,
        9152010575643401, 37669840345144452, 43497244908750488, 39598411557286537,
        58423570654072462, 40686948017253007, 31684869537370378, 38066786357016207,
        71919878101696512, 37169555994528642, 32235153423107205, 38673707983917702,
        14509617341434492, 40431858937183630, 56172234709766135, 40393382321803920,
        148668319501565, 36862788290905472, 31107359410914112, 37802882980181380,
        20135564881790758, 39924968809252746, 52512123699629854, 40686947463592591,
        3254084406972699, 580702069645]
    ) [
      6619646330045339, 38107451660549509, 50536468707444839, 40478032469469579,
      66305630227304500, 41144350357398928, 48008060244890217, 36029377872018060,
      39550741116977824, 37433442224568195, 15348325584438687, 39266353861447304,
      69963726848560239, 40749620767242127, 18456353083068668, 39618217950396818,
      43769361146808902, 37012323684244098, 36456389003740133, 38288873495083141,
      16478713797118236, 40467041983765644, 60113154969407531, 41119062344936336,
      22954321973317948, 36757223481225098, 60098693593531091, 37546693432199299,
      65451562937845270, 39414790783370376, 9165084654669126, 40717734930031504,
      15641551779303673, 38942008484517777, 57564460973328181, 37089290555167362]
    ) [
      25477735320027919, 37789688639317892, 26609502230382362, 39915074546794890,
      159294168338381, 41084976880506001, 1568614718739095, 38873837421385105,
      1551108111632165, 37231129300001155, 67982939327726798, 38885916613797766,
      34214025366309706, 40766114951605647, 24930049915195700, 40834292608329106,
      15632991826054876, 36868285731438727, 51373789664740179, 37939224200433028,
      5499677852731321, 40283413844596619, 3818206877749263, 41117961910565777,
      64617351636161192, 38073382453679246, 20128701432430592, 37328987193846659,
      39836012894782770, 39086030850660487, 67710934879538149, 40769412077219215,
      29715197532147983, 40242749245654930, 148732740734108, 36939754910164352]
    ) [
      48276525524549632, 37522503740172163, 62355252293240322, 39503851879534216,
      10010660638788972, 41093773460063121, 54768338795663956, 40116303227433107,
      148578120731764, 37044209722775680, 64041280322896915, 38468096222473605,
      12257508282960343, 40789203470971277, 9167550005023002, 41551176873974418,
      37311508611437240, 36029377133812108, 144635223966415, 37652247857104260,
      45186051818358408, 39668781526208905, 159088009907852, 41083877603758993,
      50827624700088927, 39559941820836498, 55872785142876696, 37135470446188930,
      28294443618567279, 38678105845875590, 11695185406298775, 40797999513736334,
      11982248232063273, 41285095177506962, 7191435506520314, 36803402969585290]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        12529770426893084, 37700626972715396, 53067613163587265, 39763337865241225,
        13666919038422452, 40235041104479374, 42937202755866387, 36663774102421639,
        3802993868112489, 37177252726921091, 42368355664823438, 38715490264646022,
        44346561870793334, 39973354501720461, 71370109600173588, 38182238819315854,
        26601822728060928, 36871584501369730, 32514751474664262, 37836968142634884,
        20417211660339026, 39839208881986442, 64332157136375308, 40224045921081485,
        149209500978682, 36683565546736768, 15062143262229120, 37253120002328707,
        10280723722437857, 38873822640218247, 55606097827039977, 39900785123635341,
        1001404076690923, 583050943630]
    ) [
      50246979213755092, 37468627099981955, 33081506818524613, 39216876073091720,
      39281571410775218, 40229544687200910, 56171427248967472, 36029378878687629,
      56438569696854596, 37048608222282882, 45745179201012738, 38354845115508101,
      27456066091518287, 40125088381402508, 2408817621110346, 39922783963020943,
      16747763387370202, 36799015827955842, 66572738319123191, 37576380598476163,
      7749437528573501, 39430183375740809, 14793454592101833, 40219648579237262,
      68554410662661965, 36647272318468746, 65727359893865046, 37110181645200514,
      6339090488591428, 38536267134594182, 38997261699418606, 39999745767100557,
      8882647593422415, 39141024350548111, 21253738006087564, 36833101107852418]
    ) [
      21536153627296405, 37283906764120195, 15910322042668285, 38932097243034503,
      42658884551609144, 40325203054509198, 29431837036220249, 39032171088815760,
      39831339872061285, 36940854673456770, 63477406940169103, 38012892402252932,
      2966604930320386, 40107494282622347, 11979284660064020, 40606681755774095,
      31677709760565166, 36738541916520583, 35610087148782260, 37371868835207811,
      59258043989132635, 39086031672761223, 62644015939423162, 40251535238540686,
      50823935265640251, 38122863010358159, 47712742338297856, 36993631919464578,
      17034366499587014, 38177821344262533, 37307179165190313, 40145979689470091,
      4660703333617301, 40445053798145935, 148930318863797, 36767129588092032]
    ) [
      67134747662450688, 37127774049350786, 11405734560105560, 38559357147217286,
      34493842465458706, 40366985788193677, 25491084286922628, 40425267420784784,
      148711269960994, 36844096375127168, 18722301519889192, 37722617591153028,
      62637843977176787, 39723756386182793, 26334813418852045, 40583592112272783,
      17890856205914295, 36029378207578509, 8025178649231991, 37203641358313859,
      48279424666666151, 38748475932250758, 42094581672872629, 40318607595331214,
      38157471121444744, 39789743710451344, 31947412127320714, 36891375995886978,
      40114683221476186, 37862257329511044, 36742884864919397, 40060210048099722,
      27741909134053045, 40625373403121807, 44347098814124174, 36709944481241738]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        71638390239691349, 37168456432568962, 49405290212394122, 38701196999369094,
        15353230530742881, 39434585197250957, 37590110184770638, 36536228991991944,
        21816670813454823, 36856191086918530, 31388817207296825, 37863356673360516,
        11972936590919537, 39685272908838282, 14509028935502849, 38465916208180876,
        64600489311371264, 36670371205874049, 11965862683050611, 37249821333225091,
        19006546785633508, 38833140709997191, 71367777388104561, 39410395018663563,
        150399219174467, 36562617673825152, 30542519647240703, 36904570252861058,
        56158928694444909, 38022787973344900, 11691955544688650, 39418093713990539,
        10286736776006481, 587933154956]
    ) [
      50246017128104484, 37034314302681730, 48841403944436727, 38391129552878469,
      37870936579934554, 39441186763347340, 30554352457714803, 36029382133543053,
      8024207973384640, 36774826152706946, 63476453444715236, 37586276186347139,
      12534653868607057, 39530239638502793, 25768174054706242, 39767741079253388,
      52776560419703796, 36614295341094529, 60379245140410939, 37096987270781826,
      11124190862279740, 38558257920805254, 71367442367941075, 39470869802463371,
      69397972257311830, 36514231411561867, 14216747656577489, 36813309563002242,
      9996444095972108, 37717119731017092, 47438208120751835, 39349924060110217,
      17042458349964612, 39401604160185484, 58407945305622632, 36639584460860033]
    ) [
      33357295184347646, 36926560753855362, 63195906192999299, 38050276149921412,
      67424305879353385, 39904080537883018, 31117499987692802, 39334537440639117,
      69385611131258864, 36709954111019137, 31669373049143967, 37369669677731459,
      69954226249303394, 39046449119951239, 66020805115415627, 39747950893394572,
      1279627751820699, 36573612840321160, 41520172589482512, 36978238471458178,
      18160253521003450, 38218503727479173, 433772532435143, 39642399052178316,
      34213484208819373, 38309784886021005, 2113156152000512, 36740740839255170,
      46869215067603648, 37470826039348867, 42370331375470034, 39324627491195272,
      26894967313108118, 39766641634744460, 149724907277696, 36592304806544768]
    ) [
      20409287339835392, 36839698227950722, 18159342976336677, 37747906526364548,
      66860149019412214, 39783131071036041, 48006097385262462, 40132784543352973,
      149299697323524, 36660475467004288, 6336294428508776, 37199243227915139,
      56723751277855911, 38769367341055366, 16762276152773261, 39840310742598797,
      70525246576496045, 36029380321575053, 26601809842831856, 36880380678278530,
      39270232521081681, 37891944428674692, 28017259373758349, 39695174486158986,
      41250770949410260, 39938171119451533, 65442934364212118, 36683565496403841,
      18158398071145089, 37278409071761027, 26325003555996926, 38904609871780743,
      60672003170863916, 39806225865316493, 48288104940801433, 36556012853387403])]
private def schedBlks29G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        35046243831415351, 36882579869311362, 38988727479075662, 37910636378007172,
        60386623994103692, 38808965362528138, 67706390745090318, 36630788820697225,
        17031647751471653, 36728646379129986, 19002857362195102, 37280608061461379,
        27732468634977545, 39046445663793543, 1559547922647249, 38883722690898569,
        13090980897914880, 36664874033623426, 43772088370233935, 36934257586914434,
        66573623093461892, 38062371180485252, 7189193434105865, 38565966800164489,
        152039859063048, 36650580332132480, 22942708162921016, 36758333612515970,
        33076795178648254, 37383963429556611, 63198904119428473, 38692408154171783,
        65734244871997935, 593888912776]
    ) [
      19283421794173448, 36793518253040514, 66009758300406512, 37619261904282499,
      2964539022149236, 38966188344765833, 42935845481384854, 36029388559156106,
      3802126274494966, 36667072872323970, 64882943554060897, 37110181594867842,
      21820381712843851, 38523073766828934, 64046202459621921, 38948591612051083,
      140739798731509, 36613196215354498, 26883353541050911, 36836399776956802,
      14781578830381852, 37761100749782916, 60667403178247936, 39468658246476169,
      68831689357429120, 36603291853500554, 10276145229627917, 36695660577305218,
      4928928135611006, 37188247910308227, 60664461081740451, 38722087317649286,
      38153536814680803, 39086030766814857, 6898432589466054, 36638485368675202]
    ) [
      6053904612360669, 36723148552548226, 32232327297794726, 37382863917928835,
      4089219139863927, 39227868370758280, 45188920946494044, 39312536755691914,
      63474628030400809, 36614295542427521, 44334991077507628, 36980437545046914,
      24071275276895164, 38244892560201349, 26611684099524799, 38958493860660362,
      25486179352545984, 36562617891815561, 11964969318908401, 36756134337595266,
      47713652882965192, 37492816456455299, 41807493093361135, 38971686993357704,
      38432641011518457, 38719900508410250, 69104213495545856, 36637385622160001,
      53623789864714819, 37038712416303490, 56441309920723965, 38395528052382853,
      18166777686427962, 38914509184393355, 151395636906677, 36587907062033536]
    ) [
      64881981468344320, 36659375988932225, 4365948116370022, 37199243144027523,
      65449574341051563, 38728685578607238, 13945778332928736, 39249864492252300,
      150562426162184, 36564816780968576, 26883306294968830, 36877082109840770,
      40677607404372813, 37923830601428100, 43216766383130538, 39525841524990858,
      66018198041823939, 36029385203767435, 71637479695221191, 36691262262351745,
      17595443822822021, 37285006175081859, 35050856684356876, 38936495239228551,
      53916388946709398, 39337824701047178, 57561635035122632, 36590105934289537,
      35609150833721878, 36926560787411074, 66573627388494723, 38084361513704068,
      35899134256187454, 39098138816576139, 53070697004698316, 36540619690673547]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        25194572402623062, 36742940349064066, 20410258015945385, 37319091320758147,
        26606744825267512, 37391689606271111, 23230303568890426, 36720950354563718,
        23505739723080298, 36685765157212290, 44898014047535709, 36935357098542466,
        6901056880870283, 38063471430323589, 28293962685319233, 37812783517479818,
        29135350928553120, 36679168171335042, 24631600973840971, 36755035060855938,
        33921207223550649, 37427944314101379, 71080224945178026, 38932083771111047,
        60945583893874350, 36700059311700917, 19565025623573080, 36679167936447618,
        48557218809676379, 36983736130263682, 38989616547857351, 38210807716529541,
        8032389978622627, 573722533254]
    ) [
      23787193224233561, 36716551784782210, 70512546169455238, 37136570192705922,
      36457321022981231, 38824339617300870, 17601392445196656, 36029391494782857,
      26320541030646391, 36685765241100418, 36735158117827161, 36856191355362690,
      24351822529069868, 37820475300440964, 6625212670904092, 39741319966860938,
      35111166695212209, 36696760659374466, 24913101721076314, 36729746075312002,
      8869650825380503, 37222333106317443, 70234846516643021, 39017859066079366,
      146941776070169, 36733262529638536, 25757578192126581, 36687964264355714,
      40675855036875357, 36893575186919810, 49966367535956824, 37952418725845380,
      9441487169554305, 38302079529946501, 33076065836697183, 36691263000570754]
    ) [
      20690929825186386, 36691262715349890, 53905320677573225, 37002428146708098,
      38426679479796691, 38231699058216069, 54754444439161049, 38278978310079882,
      24631669654719148, 36675869502230914, 29135243551277645, 36793518437595778,
      54187667543130852, 37549991748973187, 42933375823152679, 38810043231673736,
      37866967978903972, 36694561619181706, 22379801160548950, 36703357494252162,
      61505239539221111, 37064001552847234, 990967144678426, 38384533053557894,
      61512158822894198, 38917796327272841, 25757586782191616, 36681367144256898,
      32512990516970067, 36822106092243842, 1270603852514053, 37683034417564036,
      16475260595832486, 38837535753419146, 152288910018487, 36697860187779712]
    ) [
      16750220020842496, 36670371725983106, 41238796399903313, 36907869005854594,
      50810822531646309, 37973309480327300, 60387401385215928, 38524187337864585,
      71083600845899955, 36662675178145407, 22942721048281664, 36747338395574146,
      24069484253512367, 37322389989862275, 40680558085440823, 38893616299002759,
      26046200145676199, 36029389918034312, 19002054194725452, 36680267464852610,
      47149839631221341, 36950750479437954, 6901074061329304, 38112949638123141,
      69113598125443105, 38252598117758854, 23221687895820672, 36669272348576898,
      25757505175519814, 36768229368163202, 37861921323057863, 37429043926395267,
      70235980404262315, 37918353360756871, 49407059808914252, 36690153272143240]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        61504324699652580, 36569215062367361, 22661117219078650, 36899072342393474,
        24071228030026627, 38197611647597701, 44334419600838084, 36584608815809924,
        60659912654881263, 36537328923169409, 66289407893012943, 36660475483783041,
        29135956521878127, 37490617164753539, 32518320638821850, 36475759358403724,
        63474713962592019, 36532930893437057, 55030288564322758, 36553821614360449,
        25757354847535600, 36956247534245762, 51374738863588299, 39115705517751173,
        20972357709300951, 36541727171012023, 52215521617347019, 36510940207888001,
        63193123018408378, 36670371105208961, 47994986122019457, 37597271436837251,
        33646780350498328, 581743379351]
    ) [
      2676277909094944, 36600001991935618, 19283430384239118, 36814409108186498,
      35329419634836245, 37851262632666500, 14506408984676126, 51112466050437772,
      6335529917186617, 36592305410542978, 1268830009328124, 36652779003056002,
      706683223507543, 37261915726240899, 67701722054165766, 37779823267527302,
      12866182351718110, 36605499835294082, 68259840106660354, 36584608527151489,
      20690792382497283, 36853991895888514, 65166149422711622, 37939225274194052,
      64032909593839864, 36628812532157060, 69667257940869653, 36564817183633537,
      69667176334262758, 36656077470828417, 13373194615751265, 37374067321576835,
      20414239506007414, 36643931069254536, 2113346011694778, 36569215364365698]
    ) [
      13935465959162450, 36628589814360706, 17313114137985570, 36757233933111938,
      57002391539188424, 37611565188665219, 6060832478824018, 37628076485483148,
      21816899307013451, 36640684727484546, 8024358301631012, 36650580114022274,
      52779352049680969, 37071697966463618, 14502006547907637, 39424672664048262,
      37865477683904566, 36670372064899205, 8587346910872122, 36615395423164546,
      18157526182822424, 36782522952211074, 8307495449297642, 37741309490148996,
      27456731765704373, 37586287612173954, 14498437387892163, 36617594597419138,
      4646594155545105, 36652779053389954, 61505170817843792, 37159659920107394,
      42650015327552665, 37652274046522502, 43493345091948016, 36639585249412277]
    ) [
      26320562506085845, 36664874318844546, 19846457649365566, 36729745941090690,
      22662057829368479, 37360873232380035, 39273260514444648, 38156939330991239,
      6058281274672563, 36687964499243445, 15624320114197068, 36659376458708354,
      41238770629575240, 36941954134752642, 20412018973442970, 38101954941288325,
      6901684047808952, 50784819252485766, 19846534960874091, 36645082790771842,
      17876089861866030, 36739641596071810, 37580394805428911, 37480721509775491,
      15629787679720926, 38066752416582793, 28908714150168082, 36662675329144962,
      11402118152880695, 36652779221166466, 45742408911848006, 36998029848532610,
      53626530087601120, 38486785638429061, 36741690731105216, 36698076395955077]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [
        68258714807664878, 36306427874178432, 7178778007011585, 36395489373005441,
        8586973238559083, 36979337546858882, 64602529438466967, 36223963330937988,
        49962570734403761, 36228361390961280, 54747688288878776, 36265745256073344,
        6615763627507938, 36481251984619137, 47712780991234533, 37061799845181058,
        27444233290036785, 36137100566880640, 29133096035319907, 36149195329005952,
        36451535625224305, 36205271109896576, 5208289957216434, 36442769195090049,
        25476773208752462, 36029346783166592, 140739635871744, 36029346783166592,
        140739635871744, 36029346783166592, 140739635871744, 36029346783166592,
        64879962804420608, 549830567551]
    ) [
      28571254200566123, 36422977935467905, 35045234499748201, 36499944571504513,
      32231257835405770, 37145365480396674, 44056831864046750, 50899163880991361,
      23786115170861400, 36398788344107649, 24067564377309520, 36422977834801537,
      48837637208768881, 36665972605702017, 22944254365565599, 36646195036480132,
      17368824207147409, 36372399662381953, 15341719838425398, 36376797708892033,
      24349013583495488, 36463660100576129, 27446075855241641, 37137668831890818,
      53905376550421627, 36339631528365956, 6334383142764825, 36336115191453057,
      9712112928260376, 36370200437794433, 35889595003470146, 36623090947564673,
      71357752788943483, 36925461041004931, 67695765673772170, 36291034543615872]
    ) [
      42082267834515876, 36464760065200513, 42082224883663240, 36515338053066113,
      24912865491321298, 37025517354001538, 62634120190985251, 49931580109889669,
      44334107156578969, 36468058683971457, 38141545144746380, 36468058482641025,
      56156124044493208, 36664873312183425, 69950257645585033, 37645651424878979,
      9170556194883057, 36471357289208711, 37015636648034702, 36451565690782081,
      39830390709649792, 36516437531138177, 30542416565600724, 37093687880238722,
      57567785363080303, 37118879960445317, 35889723856172015, 36441669968690305,
      33074909663232373, 36454864158554241, 54748719095513483, 36674768950387585,
      15344305439408798, 37618164322065540, 67136190594908473, 36430674667861172]
    ) [
      55593290058609840, 36505442683305089, 47993311065702829, 36524134364196737,
      14498201158189522, 36893574532590466, 30545268459799435, 38403219986445701,
      28295435709685978, 36509840880814257, 45741498367181233, 36486750566195329,
      55593186976563620, 36628589092920193, 29980338501157461, 37512607749634435,
      60384665453954513, 50579208730161813, 47148911906095548, 36479053968024193,
      43771109104320918, 36514238574993537, 18438876601942478, 36954048292881282,
      48841541383652308, 38899101626408581, 50584752629774771, 36486750700416129,
      40956342157345179, 36474655770513537, 55030219842748826, 36643982373150081,
      49683810211562093, 37587376083848067, 19004863172806142, 36499076535216018])]
private def schedBlks29 : List (ℕ × ℕ) :=
  List.append schedBlks29G0 (schedBlks29G1)
private def schedBlks30G0 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [56722651764327765, 37265217213998212, 33865]
    ) [
      30827512259118485, 36030469531593093, 67442495334486135, 41136671107197079,
      39561251091091404, 38557165623609739, 4933996284774498, 37779797044543111,
      38146089292039681, 37506013766970245, 427853991085361, 43488536662344064,
      71940374016464937, 39705076466464402, 8877313181846481, 38137144715804041,
      12251237558617878, 37591777402023814, 3242616644797796, 37393861735413381,
      19587587294330881, 41992094559526810, 27178671439909865, 38859536908162701,
      38993112723982661, 37834773833915783, 31672139058677280, 37425748445053573,
      40678238782719191, 42129497306169732, 22964973647993320, 40307620129844885,
      17604519250464175, 38311970353015434, 28858604788746136, 37593976777610886]
    ) [
      22947080506017320, 44210909056336774, 10861485201922518, 39583028712818322,
      1558761919187827, 38173428851177609, 42369442323400522, 37771000230079878,
      710312530511388, 37741312325584006, 25496096247875108, 42283469352083868,
      1564066301449002, 38812256851183501, 49126289194846511, 37935930128422023,
      7747410291951247, 37686336291209862, 63197568378045914, 41370774304844677,
      70535382908574574, 40239449184163477, 7189713179479400, 38333960585566346,
      55317574725765054, 37763303799687046, 53627376221259269, 37620364435894917,
      44332319664801193, 42708993874483857, 27462981172762145, 39203690205005967,
      20698141196323409, 38015096576266120, 6058611973260993, 37625862514142342]
    ) [
      40954667205756573, 42370336626133920, 12822004496306609, 38711099600345484,
      51659521033472242, 37995304444194183, 35613815243507409, 37825976247676806,
      35332189938222690, 36040370404363910, 22967666676899255, 39992055192269975,
      53069584616492188, 38318566818781833, 70235915996661699, 37866659268447110,
      22665700021667440, 37820478404317062, 2118284421662314, 43136717436946048,
      46883852602611467, 39072845771118478, 17320295443040762, 38062375995692680,
      35895346056496892, 37792990563296390, 19287897219434045, 37844667844677510,
      37327894041690117, 40911271290679449, 9442861637734203, 38524179385563787,
      18444924016691290, 37889749599846535, 14221373410477687, 37756705907812742]
    ) [
      31414918363381794, 39820528140266389, 62921183028218933, 38448310784712329,
      45748288817432652, 38059076739365255, 64324679485589276, 37937028683716742,
      53628394142598850, 43882231734738054, 59549238683735707, 38992579408981389,
      34490427936573915, 38183323918936200, 1837440818579316, 37938128363121799,
      47998821593155259, 37915037914278790, 25515367767377595, 40603397649898396,
      42374626443562544, 38499989206981770, 35333615894562910, 37988707022096519,
      44339642601735895, 37872156423918470, 47717282189969039, 46005216084408710,
      63776766508375253, 39340032230600336, 57853370705808069, 38188821913296008,
      61228506284066665, 37873256237546118, 32235973785323135, 37873255700658310]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [43493276320957844, 37099189012025988, 33680]
    ) [
      66573429829305534, 36029361530580099, 6633686738897286, 42006389334689173,
      60396923510494252, 39353226168779407, 20698304410061504, 37895248567314824,
      7183588450403889, 37216838652054149, 144557924058102, 40769398654983552,
      24654068295111812, 41406042077413781, 155235393376308, 38597848745045132,
      50532676221962341, 37573086241243782, 18723074636809509, 37016724297744004,
      29991436807536640, 42442895517807760, 20146933864174963, 39797436282086291,
      18729212250262577, 38077770685252233, 38427830565045958, 37315796292415621,
      38988439722886218, 39631385715015811, 57867638745436167, 41522594286243734,
      42096935408210736, 38921110784074125, 26045177896339813, 37706129396390023]
    ) [
      22944112643310602, 40276804862214275, 11707288818652062, 41543483413292182,
      9725577879064701, 38623137915144076, 57006699472062587, 37597275882936454,
      24352660071810363, 37034316785783172, 48284144748233557, 42701281287141518,
      59835541246547531, 39854612044380051, 26047681905921113, 38106358407011465,
      45183333086955231, 37338886422480773, 42929158117491806, 38828703387703939,
      45764150304804425, 41677628328275351, 58704285457945529, 38957395288559501,
      34208076776900995, 37736916208514183, 50248787432867247, 37121179596908932,
      52213610384294818, 42129513765531785, 3823141894657917, 40396684749143700,
      41530330364349961, 38329563176610442, 9436625235445649, 37451038437260678]
    ) [
      42080511225004985, 42986053859099787, 22118530034734922, 39886498653349268,
      29143949600132201, 38129448436411017, 54753615440873207, 37389464645234053,
      60943814328550544, 36029361480245635, 36193511441206079, 41848055818318488,
      69400562209821776, 38971689208162189, 39556174349830544, 37765503896717703,
      60100549058725323, 37167359756373892, 144437662811087, 41951385382220416,
      48859988589123630, 40463756183213460, 46315499459743288, 38349354671126922,
      15910639895414692, 37479626159019398, 2397255400195288, 36966145940769156,
      22394361239601152, 42230694035310484, 6917098851505361, 39382913620277392,
      26046410573187797, 37919438175452808, 13657611700438600, 37241028276969349]
    ) [
      29155322708656129, 42047071164349593, 71089510854137085, 38968390572614285,
      48000513846249875, 37831475433255303, 19005614781335059, 37337786390743685,
      4367468564022396, 41558845855629700, 24654137045653704, 40496741683089301,
      46315490870070857, 38368046536572298, 29703089850058686, 37565389190074246,
      37863587803530545, 37153065517995396, 55886378596139991, 42495681538561938,
      17331840504141182, 39387311884899472, 30268578173913816, 37955722528936840,
      31109292187813487, 37336687114003845, 60099324972336236, 39393852364401027,
      9738196637880828, 41631446793033879, 12540417842909351, 38634133148864140,
      64888097605453962, 37645655032101254, 43493224779646316, 37133274224811140]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [69670947380627010, 37139871831464324, 33702]
    ) [
      15345370622035261, 36029362369456772, 62079300705486680, 41981086104876686,
      32813045823935829, 40203167330324626, 14789752301915496, 38221809476783498,
      48561165954811691, 37309199340094853, 144734021256249, 39587410686197632,
      62930473133444773, 41475315588223124, 8604355244167824, 39221282357481871,
      62919108528343638, 37764404770978695, 40960018711610806, 37053008986783108,
      35617770916642816, 41256495442981260, 29999627512222869, 41022306110314899,
      34494495344660338, 38475801075283595, 15347780139386867, 37419152365174662,
      46588440191468693, 38854022756565123, 16202551762324566, 41816167447545746,
      50263046946919293, 39603918762659985, 57009285088381854, 37938130611341448]
    ) [
      44618055223575671, 39138799573270659, 58426250722446735, 41658937217769108,
      49418892596581153, 39314742439705487, 9157680039168675, 37831476020476808,
      58130254287963635, 37124478299568772, 64607021927793566, 41091565292969098,
      6356528340571247, 41167444044358036, 59546189186109457, 38554967187572619,
      33080978554390583, 37488422637927814, 64884588559697107, 38167896899428227,
      45193598171974333, 42018479315095185, 7479383072543786, 39714971450375826,
      5781178635029497, 38009600008015753, 15346547462538883, 37211341161027973,
      33354786948547559, 40276815902316679, 23245198707233096, 41210328202362517,
      18171175837209067, 38865034768294029, 7467567436761392, 37615968167825287]
    ) [
      22658737833280476, 40862862059223432, 57022870263272466, 41294989574256788,
      9162546318905509, 38620938958998924, 48562342795315314, 37549996211844230,
      9715746531280140, 36029362302344836, 58140227302885435, 42228487160044944,
      37597738166752481, 39818327439253394, 23514394230361164, 38073372655520905,
      31390865951917755, 37277312848565125, 144712545633317, 39967846306423680,
      1571780110880888, 41364262464322454, 45756238962135642, 38944200914138765,
      24356323741567347, 37680840326957703, 32515597608322423, 37047511210535044,
      55603636738686976, 41988780370962573, 4947723221833207, 40348305683796883,
      35900723453464014, 38291079816647306, 65449922259486568, 37375171044409477]
    ) [
      48286773416787968, 42437394553824911, 69967931729941933, 39907389542083730,
      38151324951547025, 38125050507345033, 44620391723796201, 37332289268827269,
      42084711712130137, 39501641749102723, 48296536038018902, 41533590123956630,
      70526505074135764, 39007973679087757, 38148816647129514, 37733617690409863,
      47715469692339626, 37110184296078980, 8594351965897625, 41937100002494348,
      48014141996242565, 40479150134451859, 53352472662412843, 38349354822126986,
      7747766785443740, 37435645056365702, 61506802937988270, 38393296783121027,
      38440651183786986, 41855753154614932, 14798063176094639, 39395008181067408,
      24639052870355685, 37890850537582728, 1835490877605415, 37190449987105925]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [25761417960458004, 37169559467516549, 33710]
    ) [
      28856470158214587, 36029362537235844, 19011172517906121, 40670450041073804,
      26902900229444127, 40794705659848851, 12540306181361797, 38620939260994700,
      22103390038755418, 37387266293089414, 144776972698730, 38974975327517312,
      19297410694810665, 41655631015434384, 63773467869418348, 39833724158763152,
      22107058002168905, 37989808899387273, 60945162973316698, 37062905061207428,
      28016095405965312, 40175662812369290, 65745459139022864, 41002517350546067,
      51386674777592038, 38944200880580237, 1838085084383591, 37529105709032839,
      48840355972416733, 38390026584719491, 41250736569813585, 41347758934712206,
      50545183363929036, 40561603842734737, 33085913554980334, 38224008953036682]
    ) [
      47714400229557436, 38584641753448579, 58703271767083801, 41754586525038735,
      30841526965408788, 40011848548929169, 51943882282601671, 38089866068153481,
      12813307033650866, 37155265430470789, 71080057333908393, 40016230371488392,
      13109445214441372, 41164148462328468, 28869501283570054, 39069547219445902,
      28015678832019923, 37624764697067399, 708500032750899, 37968885294803332,
      1280400799140067, 41289483258129038, 21272533120160767, 40738627781759378,
      66019014120017582, 38333961894227594, 50250127487371124, 37264118910368133,
      60939334666912771, 39512645455891078, 29432519929335259, 41466518018707090,
      47728664037462618, 39422496290569616, 19572533356038919, 37791893366998408]
    ) [
      3799914394452984, 39790825924292999, 22397793020382981, 41334575717461140,
      7759513695326740, 39188296421435791, 52222917677451833, 37710527946232711,
      22945362500420993, 36029362486901380, 15915974282282762, 41196022706132365,
      66027793160442897, 40861775399359378, 24924174335184754, 38437317631432331,
      992358755895244, 37353180694415750, 144759792108628, 39231164405712512,
      3254827394501913, 41653437075804050, 1004324719006456, 39554440068320913,
      46594560623938423, 37885353315000456, 51937770441180686, 37059606308214660,
      17602268597682176, 40540705169144203, 2696520382648767, 40923351053698964,
      47162381165891805, 38734190787401612, 46592090975799484, 37479626679130502]
    ) [
      12255047200636928, 41064078743834764, 40132855519745014, 40965131505673619,
      54198052958081077, 38530777646545035, 21821829160142878, 37432346756371078,
      46869928053474462, 38780355276177539, 41534767084440577, 41846952699339665,
      26619058710614944, 39681985782782353, 71646241579633634, 37968917540910216,
      709642512205402, 37143170450236037, 47436309614068647, 40372476635241353,
      50266096385691975, 41081683194394004, 8600957909700941, 38840845143377037,
      68547491352185111, 37562091309524358, 69669783425484040, 38016164294797187,
      15918220590090635, 41809560982323087, 3539102776136883, 40194370515851922,
      7752761917934915, 38183326032933258, 34205735981319939, 37242128157707909]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [61790940842985502, 37209142943105413, 33719]
    ) [
      45745355315775066, 36029362705016708, 46593796066477485, 39952459703764106,
      29433052517600999, 40940944078593170, 2409341628747937, 39043158453848207,
      7749257168325051, 37487323914855815, 144815629698215, 38474691580894336,
      57575696802876042, 40813389690094989, 36752711924355638, 40348297144084881,
      57574623087988508, 38274587628786314, 14783803674363690, 37073900747926405,
      41243920348971008, 39601709504948616, 57297340022951340, 41211425365033872,
      28868788316574096, 39382915029604751, 3528279292611297, 37668746470832520,
      51373785385764155, 38012889281331331, 44626340317923446, 40384574669034124,
      30278997897023640, 40531918823988370, 1563168631721832, 38570361038239628]
    ) [
      50247816757544207, 38165723477966979, 29709132930910550, 40741920276639373,
      11702070361625112, 40514325664843666, 24642716547714966, 38413128291735947,
      44902098636343202, 37191550270510469, 36738959123973043, 39459869753422471,
      39001170178379085, 41366457410510224, 65179635848286774, 39561039939859855,
      39839126822947695, 37791893719331720, 9997427672843688, 37667619108795524,
      4093273636374382, 40307607479332236, 68278300138770519, 40694649178964626,
      49696437626572763, 38719896968464012, 22384950917761185, 37330091067682950,
      54183935226446886, 39051942601120645, 3533910047362025, 41260897902012047,
      44351441071018729, 40215253116509072, 46877263980825818, 38013998926968201]
    ) [
      17873663230510102, 39200380680662150, 16764269053709481, 41501697659478672,
      26618221179015902, 39750159882505872, 2684983956638715, 37908443830954377,
      38145350552225295, 36029362637904260, 11128971212588589, 40213047449259403,
      26901500033077257, 40857379567496083, 29712672065556587, 38863935239886221,
      52503267354904862, 37440043941763462, 144802743813259, 38734178690669440,
      51947086340918032, 41251001223600782, 13389902313132871, 40430759895400593,
      11974950993890720, 38141544322643338, 2680126267688648, 37069502449749637,
      34207647234818048, 39829312170032777, 23521798829084307, 41125664649325202,
      47446029402411322, 39195993103523471, 40963837004646978, 37602774464517511]
    ) [
      17601302222045184, 40088800454236554, 47730506570698672, 41023408675457171,
      13106391479062795, 39001376391209870, 10001014030633368, 37544499173817735,
      49403327401198824, 38335050399350915, 20702792682670634, 41204820476920206,
      57300733129102209, 40581395572132753, 48004319253073524, 38264691604697226,
      29702144945325874, 37175057159876229, 7466115596845999, 39668779898770824,
      10010673523559977, 41310384934836370, 4099462818075096, 39343330211840144,
      1276380692712131, 37712727338598792, 5775182760478064, 37807257085522052,
      56729747131631619, 40656156859696268, 58990433386861026, 40641871446401938,
      63205479862210535, 38547270841064843, 1555403201677334, 37299304054225030]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [35333190697060669, 37264119917033606, 33741]
    ) [
      66574967458727710, 36029362973463428, 36459060501382311, 39500554049294472,
      30837554032774431, 41026701774319247, 67711897011589454, 39515958151105934,
      5780169302248189, 37609372272504200, 144892942058738, 38066767381436800,
      14508461968820329, 40103096437506444, 49980743002263368, 40432961670173329,
      41532855831138030, 38591252111495820, 46591141775902757, 37094792257403013,
      11687669093072896, 39210275698135431, 26051431440223248, 40829883606049678,
      49135553585910174, 39917281304571279, 12255300671933636, 37842472764192393,
      57284966060361135, 37659941804179587, 15350906891175699, 39837010445987723,
      64053044412780097, 40690251031742864, 51666337255428022, 38899120501224589]
    ) [
      54188633939740021, 37814974671749251, 45469983541725093, 40049219193318283,
      67995055609122588, 40608886298894481, 42377650136452995, 38763878071126669,
      13377713009232065, 37235531910052998, 19286350926742465, 39001364630049158,
      11977429196966799, 40801295498410894, 21833202408526290, 40023936079989648,
      56729034199567811, 38001904500396937, 21538202372572729, 37372949992555140,
      28579294481253936, 39780934295978378, 55890081106988558, 40879369229545360,
      14512284584874072, 39077244807538318, 4653075375950299, 37409257700082823,
      51650660437099600, 38452702220786564, 17042926491568698, 40414262355424909,
      19863573350682778, 40225150046594449, 65174889853193792, 38285583147724170]
    ) [
      10273838860043323, 38702293843356293, 67146133781908259, 40759513234457229,
      69121724352598496, 40198761280970640, 28019273784069773, 38162435714673546,
      56723124225935043, 36029362839240324, 24919222120776980, 39668781660442249,
      44912346558336462, 41056392212231056, 62363726420480258, 39257568590072718,
      46030549797538422, 37551096948248455, 144854285845709, 38228397973111936,
      59263494384879925, 40360385446784652, 62929605564338286, 40382382893764241,
      41250564813000414, 38452711498877323, 31109700223010738, 37083796738462341,
      52783621290098688, 39327928223863431, 17889498940738748, 41109164928286351,
      34217066283700704, 39796335243613583, 49127985740811180, 37758908253061768]
    ) [
      25762624828899328, 39562126381686664, 29149511635012988, 41212523937110160,
      26616992799297959, 39446688750822799, 13661554550672140, 37687438554388104,
      52218231791256903, 37970007740645507, 33930158053820483, 40302110189643660,
      29715785943584823, 40548411817178002, 19578078238445396, 38615441736409484,
      66857589209925697, 37214640635465093, 58974807974249402, 39194882887658374,
      2689571020967007, 41153144789404303, 6070247228543588, 40069015788279440,
      19292286759636075, 37906245143254153, 16190036078003702, 37496095294864260,
      14225101471057598, 39983247220555659, 3537122730348261, 40788109563157138,
      35622804756271129, 38931006489400462, 51377444760226136, 37370773954232454]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [17882699933780532, 37333390877674631, 33769]
    ) [
      22665489579542532, 36029363426463877, 8591573203518431, 39087128298660999,
      42939290085526432, 40451646472204685, 24928349096022135, 39733660765554063,
      2403534756285624, 37768804663038601, 145013205140823, 37691828967036288,
      50816251442661127, 39680878066767498, 40126408656588163, 40594590600812175,
      11414908772847458, 38861738112493197, 15911198258006293, 37124480111566470,
      59537160990785536, 38559357264654725, 63486121556609672, 40147077858946700,
      17047492121366374, 39916182984158096, 9442213080632608, 38054682300064138,
      65166531702982210, 37344378796114051, 63199806073046463, 39457673464929416,
      36466271874092230, 40684748037635982, 60955385157357631, 39345527490156941]
    ) [
      61225761766802942, 37471923403227267, 60104251354285650, 39602810962795145,
      29993176349314392, 40758419058086287, 49133264332361742, 39087142526062221,
      65451567264991686, 37300404706740102, 4085787356333019, 38394427970305413,
      44626817075808683, 40116291130704268, 57580146465083205, 40096505642621328,
      69960458363047351, 38254796436264330, 38145646914471668, 37142052550729092,
      22666752284984573, 39338924632016264, 29992240033008783, 40735325337625486,
      33653038277431495, 39612711382664590, 69393398072838934, 37517012222017671,
      66005884251112588, 38055772785273987, 49129493253621819, 39879892859126411,
      42942378209873486, 40336203287936912, 54198370781073021, 38556067202545548]
    ) [
      16466288349250675, 38225100109342852, 31960129578698984, 40082205683031948,
      16484881468067624, 40272430472675729, 66302039591784034, 38448313402034315,
      10561794992605090, 36029363241908101, 51939363870114863, 39274050023378055,
      20703428359851095, 40748518973834638, 7758100639945003, 39766645845941903,
      47157626543967253, 37698434492772744, 144957368861996, 37856757724488576,
      35054820988651425, 39844707547494539, 44912561310895661, 40527520945216400,
      13385143412690723, 38749584436773005, 69391078754584758, 37111285502259589,
      29419849588899840, 38844133460642950, 32242953201617774, 40412063499949197,
      1285103892861048, 39880997924186512, 52225451760389401, 37960122706216073]
    ) [
      71641663036948480, 39154199279707014, 10851555061566418, 40734224618021262,
      53076284864434543, 39870002069700239, 22107070889168159, 37868861546583945,
      58410904622761409, 37614861357678723, 70519684495935209, 39787531818744458,
      39564364952538634, 40714440270762640, 45473900653612996, 38936504886444685,
      42370189671041374, 37272916228164230, 40396424424227792, 38604437241386117,
      20420772244261591, 40373580106427789, 49980846097141859, 40061320431653008,
      28582490035293609, 38145943040257930, 31671546352535202, 37234411527459460,
      1838256853321083, 39554430907625353, 21267327514610998, 40891460434803343,
      27178877585232058, 39340033757263502, 41808416556943990, 37470831693442695]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [67423064652745535, 37424652490306183, 33808]
    ) [
      57569099668555967, 36029364080795781, 55596605809525581, 38448305499719045,
      19293867308059087, 39894187030398348, 47164236572823120, 39782040787159439,
      70803491704310940, 37951326697081225, 145180714173909, 37368568907777408,
      36177924838032817, 39288347063592584, 46035617912884279, 40397770402444173,
      25770574975242143, 39230076286179725, 62636821792918036, 37167362424036486,
      50247576217026560, 38152532073487748, 37307548528838761, 39707267537054603,
      29711830223326603, 40034932387452559, 22671824749366626, 38251497884626827,
      4086813952411368, 37115678045503620, 33361946691077282, 39091526848500359,
      71649230898301814, 40143779307287436, 19016163384856397, 39371916289337486]
    ) [
      71359178763699873, 37206938450133123, 3807735570728213, 39258657498137480,
      41813441720978459, 40408765149618573, 2408920718151676, 39357622084519310,
      47719494149770032, 37383969603759239, 9996096147325952, 38006294510371716,
      31395809503643640, 39691873753497483, 31119114911452542, 40233946693232783,
      58419799638183438, 38469204844431755, 60382689776535476, 36976026294944388,
      67982728866530326, 38884816246530694, 66301004473338723, 40123987863104140,
      70245266280845132, 39559935696967310, 51098486683962323, 37652254937300616,
      24066112723715291, 37675336644954755, 70519040246646490, 39499456047698569,
      31118182892014807, 40442853986347406, 42376615038062338, 38812259652983948]
    ) [
      40673136348464310, 37838066429486211, 8032518844745589, 39667683927238539,
      26333962997173612, 40427462786550415, 39561770778529475, 38681414782948492,
      41806187435165813, 36029363795573637, 24634882363130759, 38673707916812422,
      62923218848549625, 40105295964100236, 46601857865125688, 39746855576194447,
      34211113373961356, 37871061106721161, 145103402403228, 37498312705932928,
      18727124832192066, 39484061895021449, 26051577475468492, 40560502082835086,
      15637248176656298, 39111329181369997, 42651789204097415, 37149769633997958,
      11122919530201088, 38319660424637829, 14508616600684833, 39876594592691852,
      3535683900575294, 39974458341961360, 5501816808639806, 38173431334279051]
    ) [
      47996558095319040, 38498883403695493, 48004748727978544, 40078907332705676,
      18736187358285594, 39932675843128720, 20420029228158232, 38082170510195082,
      66573949537191510, 37311393111736451, 48844388984391062, 39391702314255240,
      19859054971358353, 40637467846441102, 63488711488671809, 39408199468392589,
      24919681727367775, 37344386245616007, 36173535269389294, 38176721329292164,
      60107360950585491, 39861200876240267, 19298248235126316, 40162477833469584,
      5221003268296163, 38383441209358732, 49967875115222884, 37043096504234372,
      38991446223586417, 39190484321074311, 37309717536476091, 40394471162909325,
      52230760403800104, 39552238796794254, 29705911699606551, 37589581532983688]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [40402514864212809, 37525809640467848, 33852]
    ) [
      21822366046325189, 36029364768684422, 46306965199553237, 38064570052736388,
      12818439565969418, 39529144036076683, 25770081023069389, 39911784820163982,
      31959760236940510, 38097564209894538, 145356813731413, 37124474574917248,
      10280723720340628, 38883716718130823, 25768105310718756, 39868897742863244,
      59266466564902460, 39201489571079821, 27171623284935288, 37215742479195015,
      60942933834629120, 37768796978840963, 69956081704601359, 39370811912165257,
      38435673281760328, 40115194739694989, 20983155283365336, 38421926515474059,
      16190633096152935, 36940853733752964, 7183373679625164, 38445007317170822,
      58137091967977934, 39677580421117835, 35904026306383212, 39431291410439566]
    ) [
      10279482488162101, 37012322811641988, 49405200014083107, 38684703318315398,
      26612508762147556, 39855703620106124, 37030454507900464, 39398305323394958,
      16758243158821685, 37479629313228168, 33076515956622376, 37630256466892419,
      20979001958631065, 39375209170125705, 35620919219489870, 40239439956284301,
      71930933534494344, 38736389441531787, 13095452044265541, 36842985387993733,
      44056075930534763, 38338352994747269, 59825804382472487, 39675381364308875,
      65177501193178469, 39636903373212814, 50254774715386883, 37795193797758857,
      62065234582275379, 37352076384363138, 8593029223843208, 39186089596487048,
      62923412131318722, 40104196402138508, 60672986747604695, 38966190425245068]
    ) [
      4644339332056330, 37484019323217795, 54474098977768983, 39319133909291400,
      33932069358439461, 40307609610094477, 50258159204208413, 39031061594502284,
      6341014689777973, 36029364449906822, 7463804964995848, 38229499363852677,
      42092812118165671, 39676480674599819, 8038046560390498, 39846913231493007,
      48003821023497400, 38041487975991434, 145270911698463, 37222332233875840,
      53065573024498952, 39156399678721927, 62923373474515837, 40091002027724172,
      42940849202433796, 39191593580543629, 13097565203303077, 37192652030355335,
      13655421218291712, 37934825533142916, 714225286088614, 39524745670781323,
      22110850491256010, 40107499987069582, 16479431099190688, 38336162746243467]
    ) [
      41240282472022016, 38105252335286148, 30270360573741116, 39666585036394379,
      13667473079242075, 40052524758040463, 13664569660771693, 38272389008221579,
      5494236081653498, 37091488538034308, 20976858734756996, 39005763817449351,
      61515955640765282, 40074509151978636, 23801276641873681, 39364219909271950,
      150656891325223, 37436747403429000, 52779991959634965, 37789687716541827,
      29705477865703220, 39501655574272394, 18733103525694661, 40290020343345806,
      62642113270484574, 38583557694367115, 1554737477289992, 36899060481005701,
      12531402531111857, 38523073448058246, 17042204934441533, 39845807948345228,
      9727699594677796, 39597319981524879, 10285525590707177, 37733620223840649]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [61794449887431559, 37617070414232200, 33900]
    ) [
      46592687993227710, 36029365557236614, 58128209838506614, 37691830326028675,
      17601224929085113, 39234470104700297, 49130923521706942, 39921676666613388,
      42937546327756108, 38238304013499018, 145562977994410, 36947451139223936,
      59537513187607491, 38318561886119045, 25485440609519898, 39474167984926859,
      56732135185484953, 39261964321247629, 64326818424326812, 37266321456934535,
      16469367817273344, 37431242580539523, 3807988981663167, 39076137930389128,
      11975749848238926, 39821618122097548, 36183233529089468, 38526379381923723,
      29701797055727600, 36811109885280388, 66010552877351730, 38074466211048580,
      56728437147404281, 39357618057855370, 27176493820906520, 39544542718700941]
    ) [
      23790676513949606, 36862787518988420, 29137769020097392, 38230599362034309,
      18448587656431768, 39487362208339339, 2970423223159966, 39488467155938446,
      1558809165335397, 37580786043957129, 67416029323625559, 37320190362609282,
      53628651830609236, 39079433713778311, 15634941723577129, 39822717516286604,
      22954768626912757, 38772673694362252, 38428612272687364, 36733034225228421,
      38144143630697192, 37968911333147268, 55320332112136106, 39362015735255946,
      27176472346594340, 39761148891750029, 54195553242680407, 37896350864048009,
      34762161844487566, 37113479559307650, 58412639791842424, 38672608405198470,
      57292718576994990, 39622604000858507, 20140706052279623, 39005773951163789]
    ) [
      45458210958116200, 37208038666605698, 28295444357678310, 38980474915792007,
      17042355262884622, 39819418981404556, 8037376552177157, 38976086650662541,
      37866693130750383, 36029365204905606, 9996267997135516, 37851261709899140,
      24638889630074702, 39364214993388682, 26050576735046699, 39956863555332493,
      35619059491245349, 38163537222806922, 145472781256331, 37017820688717440,
      28012861263807511, 38510978803382662, 54196506717817391, 39625902653184395,
      68273283552611649, 39226779143843213, 44060706000046727, 37244330637168519,
      34202497510899712, 37569782790490755, 50533445010753102, 39223475038717832,
      50256866378681258, 40003040610952844, 27175819523952111, 38564862288891787]
    ) [
      54750411331633152, 37722616886487171, 46874914568242916, 39336726246388617,
      23235848443104298, 40104198851650189, 20420252575501793, 38454911696536715,
      17879534496876402, 36922161834754180, 67418859780015031, 38393329582788229,
      51100037158701437, 39632499773283723, 32526120423689529, 39443386273228430,
      49409636809411401, 37537904486480520, 10276785145021506, 37444436686515075,
      22385565080585691, 39167399106795400, 51945720534567852, 40034926347493772,
      10851125585284714, 38775971860139916, 28013887806867648, 36775915178706309,
      69388248302060316, 38132741031970692, 6907821542311993, 39490660927775115,
      9162855530728611, 39708372551753614, 51662171076332586, 37858966462058633])]
private def schedBlks30G1 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [69957456145386479, 37644559379332232, 33942]
    ) [
      68266424407984608, 36029366328999302, 18439782850921031, 37378465552641667,
      46591777414219132, 38961785751495047, 38152274131520201, 39575323843217547,
      62359762107272429, 38267990894568586, 145751958980342, 36836399273624960,
      53062587983954746, 37970011213884036, 27172782899431314, 39189390044083338,
      36745719598910327, 39376314604248204, 69393441022773988, 37315800033852295,
      61223601348771840, 37182749983060866, 59257163508974765, 38660513240416390,
      12256082346871380, 39395001872639883, 65738333707930731, 38554967590234763,
      42086820589897721, 36740740486791300, 4085323553145556, 37718219326529412,
      14786329131714238, 39066243147908489, 63766810550766365, 39589620010996619]
    ) [
      37020253827205123, 36763830415523972, 27729496477827829, 37868854516713860,
      13942754613823304, 39210281234764938, 36464296162921349, 39598418016662924,
      63764912165718978, 37642359903091848, 43208932218406021, 37095887373267074,
      33079574056764501, 38486789061031046, 16759832296589842, 39408196280613003,
      49694736778169447, 38803460976265868, 53065624598317282, 36672561085712517,
      54187568755606166, 37611565104777347, 43777925310350945, 39104725870309512,
      67144583286983463, 39700670987390603, 62077127474973872, 37978815058208393,
      20406938035258812, 36951849504510850, 39834045772497847, 38200912531312005,
      62076732304033917, 39289447514837386, 71086384025603034, 39080542436372364]
    ) [
      23784637754475952, 37010124258323330, 5494596836164607, 38361443510705286,
      11411670300592498, 39422490233766539, 20703058990500966, 39043158202162061,
      57570508436769229, 36029366010229638, 32795165578461778, 37503811404952707,
      14222743512253951, 39060745405155976, 71085301681261341, 39753447629410699,
      52507918878149956, 38297677557517962, 145674649044689, 36873783021293440,
      12249098617389931, 38121746150583173, 50254723141634075, 39303741434434698,
      10287801941461993, 39321338922220685, 2683807116397246, 37296008740657032,
      70512370070224896, 37278408601985922, 25762233994216730, 38929897095694215,
      41530055457606306, 39576423522621323, 52509009809476876, 38532977005347211]
    ) [
      11965716649705472, 37394958227055491, 64324932878042521, 39055246001485447,
      2405467493337904, 39766641668283020, 39842476945870237, 38521981536740235,
      31109206299543555, 36797915594752132, 56721766975374114, 38028286034806404,
      51098611191678929, 39320233907526794, 13102521644387320, 39561035342777741,
      62638939242531732, 37624767129848712, 51090300285781106, 37181650253323138,
      1836440060396730, 38775963286748551, 45189144255040171, 39568727109003659,
      41250723710340373, 38788067293371276, 49124820307183843, 36687954248496261,
      3522313468543664, 37761100682668676, 43497107472615153, 39186091643412105,
      35056968525187984, 39773241439222924, 58136336063892630, 37937034119669641]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [11692496749497302, 37631365038478985, 33912]
    ) [
      67422111150082603, 36029366362551174, 52779214606205403, 37134370867450754,
      32798163506332790, 38475793273658758, 44625163493542359, 39190489857705354,
      17605322402532246, 38297678446735499, 145734778390256, 36700057885594752,
      63194896861332146, 37629157710259843, 40118583108011616, 38937598022500488,
      11693213999401617, 39382908268150667, 4935860339772227, 37302605692989832,
      25475763902775296, 36980437209491842, 43774789937497042, 38156931713879173,
      22669681511467116, 39084935432798858, 63204114001595158, 38604446972462987,
      35894323856902164, 36604399031681156, 24632313943982675, 37400456171079299,
      35051217469605256, 38815550252010631, 57573321666103883, 39331228839249034]
    ) [
      43494173997500418, 36667072100434052, 47150621322740367, 37536797424886659,
      4933949021455886, 38952991453693320, 16759883841047173, 39477466586908043,
      4655450530876418, 37636862495950985, 16749915040416921, 36929859003516290,
      20693519720350619, 38090959808232325, 22106813153445881, 39115722161026186,
      13383103254072106, 38880428451168396, 51095316942522643, 36569206992705157,
      11402822532497970, 37319091236867971, 18725355282466103, 38836438540214919,
      64891761254238778, 39342224173636234, 10849102623247388, 37978815477651338,
      64035559426000309, 36807811535088001, 37862763145757469, 37867755256751492,
      66015599533000496, 39031058087945865, 48848340427377365, 39188295095945611]
    ) [
      10555313851434427, 36880380376279426, 69106893587841894, 38017291119862660,
      16195598114064303, 39141011247243914, 21264394013084480, 39142115792156812,
      67984975202650628, 36029366563879558, 71638317222953500, 37238825847839874,
      71079340167759077, 38755072146381958, 152572448442927, 39340025418822027,
      6346400651250742, 38274588283111819, 145803498325742, 36770427686753152,
      17877782097986293, 37776494365562244, 39837808219293418, 39034357310694793,
      48848409148492530, 39411497667666315, 71363843171781405, 37324596042984583,
      43208945137451008, 37069498876095362, 9435379656918065, 38328457675331206,
      42936442482887017, 39209182008369802, 998702504971161, 38575859015820172]
    ) [
      58408817221599232, 37157460930406018, 47998001229563025, 38576949584944006,
      4937634165393972, 39353219860350091, 68834519794355259, 38556067252860043,
      42649770543319038, 36729745236295812, 69668915816399561, 37676437314241667,
      65733110935357079, 39046451301064328, 53070615404645125, 39575325638402699,
      71083394707655674, 37643459817373320, 33920154907739289, 37006825891218306,
      56441327100199916, 38236097574503045, 50536107938842821, 39231172526143626,
      40405358158187433, 38838646237560460, 52784218341411071, 36640675248511621,
      31387825055957617, 37443337644662915, 54754732130928054, 38920005467284359,
      22670939957856939, 39512650925446539, 71928987886128260, 37986511740273289]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [37025558181087947, 37635763588320137, 33783]
    ) [
      2401584808561285, 36029363879522183, 19846208533856669, 36939754759163522,
      22382412531073958, 38044779950765445, 62357133527058400, 38910110701578121,
      8878593080527464, 38348257340589963, 145094828132106, 36592304403880832,
      14217610955031103, 37331186066103171, 6903324655977790, 38688004436903047,
      13381131836819922, 39112422904715402, 18447020004510485, 37142076995341448,
      71074379413880832, 36819906397878913, 40959039429968681, 37849063508749700,
      29705336125097736, 38847436961727369, 63202713823447586, 38700105792686730,
      69108375405561926, 36523034315587715, 56438453729329655, 37148664719941506,
      28576030266328194, 38482389739435910, 68268322796374368, 38974982340613513]
    ) [
      9435671752116268, 36553820943155332, 425148115026457, 37249821115114115,
      62916518598640877, 38697897390731142, 20136625769187758, 39119020326810762,
      24922056877640532, 37630265812070537, 60941147081573398, 36771527198381185,
      20692570520191736, 37765499299618180, 28578757608310478, 38872726517685897,
      64610174608181819, 38982683250606474, 49688049435773278, 36488942643841925,
      44334862224556500, 37081593621442690, 7183597023691836, 38310864751082886,
      3247869462153550, 38995873564865162, 36744800467126993, 38006303956231050,
      45176735976883631, 36675868378124417, 50246880426754709, 37542295167577987,
      71361854545102343, 38815550134629255, 34210524932114938, 39170699218828938]
    ) [
      51369185469695410, 36725347055693953, 989060154032842, 37675337936834436,
      65169989180753542, 38863930676327816, 69113855842093659, 39211383246246538,
      69955476137478756, 36029365137813894, 32512749991657906, 37014522539721346,
      56159877894013943, 38187718475674757, 1277536036817091, 39020063357554058,
      22108471046212324, 38322967935609227, 145386885973755, 36634086349058176,
      33358162777768555, 37449934898981507, 42651162102629814, 38795759294390407,
      40966044633762299, 39257560788423306, 11691448763124556, 37205848669748872,
      9150009092898816, 36884778406012290, 71358736351855468, 37982106546447748,
      54194427911767937, 38938698356225417, 28863346493131395, 38655025446865035]
    ) [
      21253583416885248, 36957347163314562, 33078599086670777, 38115149634479493,
      18165974506047532, 39051949714857866, 57292971984194290, 38613243300367499,
      31672190616242200, 36592304252780676, 18721266417566276, 37364171800817027,
      24636484414965092, 38792459484401543, 49410444259658292, 39287247703040394,
      14507306646342592, 37630265510075017, 70792870050694247, 36833100654853761,
      49121908245037880, 37908437891633540, 56445823989614406, 38978280808391817,
      35618784589941410, 38940902127547531, 49969442806597945, 36514231411301765,
      59253237856371189, 37172854277746050, 43212922331104414, 38573650412516486,
      30269703458032063, 39133314263192970, 26611817277524840, 37986512361045642]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [55602459949369765, 37667650348294793, 33808]
    ) [
      14786835976391250, 36029364114410375, 69104058872267132, 36788020191571073,
      24070321781179141, 37750106136831620, 69111218676598443, 38678109654432648,
      9721716618267015, 38440617592375434, 145167844411192, 36525233439603584,
      48275593504457202, 37093688433900674, 3524422326977607, 38325157680814982,
      24920570783500524, 38782565037472137, 42654181529324048, 37164067714448520,
      54467171102392320, 36695659990085249, 52780202462511779, 37542295301798275,
      2400296270267899, 38591247816385416, 51661131662068042, 38777070113389961,
      3524830389438620, 36477953852309636, 24912861195764157, 36949650531589506,
      22663921868178352, 37996400935824005, 6906021944920040, 38695702629006729]
    ) [
      7465424227108979, 36494446677721220, 37579394063499731, 37031015465800066,
      55596975186150406, 38163528531992965, 31676356770498755, 38806754930828937,
      49410328297835036, 37654455738988937, 46585764355539991, 36658276074639489,
      37580347559019135, 37460930233366915, 34769690954925492, 38684706237621895,
      58416702904961373, 38954092173331337, 56162149998758322, 36451559248499333,
      15624053818491298, 36899072325613698, 1834472939750266, 37939225324528517,
      27453729599424355, 38739683916204681, 25766267037845952, 38052484770018698,
      35606586769376713, 36585707334115457, 4084387237954097, 37264114984382595,
      52501884330738935, 38559359160503174, 41809455934376271, 38902413230977673]
    ) [
      38984286490035643, 36621991637267329, 22661980517139034, 37377366192012419,
      12251465180153193, 38645124120972679, 67705497396873607, 39042053304885129,
      8312744006617739, 36029364315733383, 6053767169474952, 36850693142893698,
      52781151662736198, 37879850488649860, 16476231267354394, 38771570139301769,
      46032512606964194, 38397736236254858, 145245152970528, 36551622003885696,
      63756914794529296, 37190446715452802, 37020451369092268, 38550560483773062,
      51098233250089260, 38914508194436489, 31113604409297553, 37183858705638536,
      60659689310224384, 36746238145727617, 5211249230185178, 37672039552949636,
      62355166396450418, 38705598904737672, 13099502240565678, 38751782520389514]
    ) [
      68259603876642816, 36803413488578433, 32514682753024791, 37808380974533252,
      24638498778351335, 38811152507575433, 51380618770614791, 38713299999322762,
      70797238150989904, 36516437161934979, 51934802561630703, 37121176576921218,
      18442780778595429, 38406522682136198, 59542486846441803, 38936498930317449,
      40121795808103073, 37640161718720137, 51933844747617281, 36705555645066113,
      59817167075705520, 37589574872225411, 22385307383334447, 38717693280993160,
      18729134920862150, 39002472748584330, 52502880809879956, 36465852899657861,
      27164673894154677, 36972740560988546, 34486016920814536, 38066770636315781,
      38713106635917357, 38841939806239369, 40403502706035249, 38028294893443466]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [21261366016510142, 37721527810580873, 33835]
    ) [
      37023715614886240, 36029364600959623, 52215362698838372, 36665972840587393,
      37298872582308481, 37455432675228547, 38991622330156455, 38460403667726215,
      3809694121167025, 38529676809424521, 145300991149960, 36473555789111936,
      17312950924313013, 36897972797209218, 427093761295224, 37889746831513221,
      46874888809580395, 38519778134500744, 64045897490467068, 37197053801500040,
      40956217599688704, 36595603173651073, 3521428694663735, 37261915944348803,
      39553923732047089, 38391133495578246, 57571187036424363, 38660517485144968,
      11406327311206626, 36437271452319876, 71637389498286478, 36785821185093761,
      23225888260850434, 37724817151287684, 24075188042892925, 38463702269734536]
    ) [
      7747053827295438, 36457062896500868, 10275977721053603, 36853991795219842,
      53344118796288842, 37841367330017924, 63200553416886006, 38569257013393032,
      42372508968323357, 37694039382348681, 36734041386419231, 36572513110696321,
      64601365495120414, 37192645789040514, 27731712712803502, 38432913142243974,
      69956279286270155, 38705597763882888, 66577050560334222, 36424071457809029,
      65726337676902785, 36751735871641985, 6055687045350109, 37656646306275204,
      36741038002374227, 38505484063913352, 31957501033416938, 38138248136590985,
      28851187329893871, 36518636336283009, 38705324035899877, 37032114977428354,
      51656299742397448, 38185518043120773, 53349002256550010, 38595645359577992]
    ) [
      32228887049700828, 36546124479303297, 54468128892682757, 37127773764129922,
      12250301226386539, 38410920443423622, 10846654443129008, 38722090824185993,
      26608999746210260, 36029364382850951, 59533797993775472, 36717650541412481,
      61506042706231992, 37581878357941379, 26044383293638170, 38536272184649608,
      35616787402623262, 38496692416922761, 145240860297059, 36496645835288448,
      30260963063923152, 36979337731420290, 32515713559069646, 38037083151272581,
      60104814014466113, 38625332911739272, 56727810096728429, 37181660286380168,
      47148740102684672, 36637385152384129, 23787901899276901, 37381764322410883,
      3244107010573667, 38548364832810119, 12254140994521285, 38735286289128585]
    ) [
      52778304062062592, 36682465682777473, 46024712826028693, 37506010881203843,
      56161866496116185, 38589048122034311, 41809391511046450, 38779268666874505,
      6339597337069735, 36473555755466884, 21535118525039032, 36928759542222466,
      13093639514260376, 37956817997121669, 7468808687552426, 38666015362066057,
      55039381144635779, 37672048562580873, 41237688258429977, 36607697918997633,
      11402835418055238, 37304797485043075, 56724129242842398, 38501086034103174,
      22950331844954395, 38833143142773385, 61228871381649856, 36438365108968069,
      2957525245919632, 36813309311336578, 34203562678518558, 37783092089654916,
      52785966383859386, 38612138403109512, 64609105144416580, 38098665130801801]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [22949116351318014, 37813888012024712, 33872]
    ) [
      60104418876688472, 36029365121072775, 35045157188174137, 36561517860198785,
      60942130667487763, 37182750016615042, 15065239975658659, 38250394128147846,
      12534512147859520, 38453806480509320, 145442730117078, 36414181372671616,
      62911544959533432, 36736342490746241, 3240890032685774, 37631357303952516,
      60103499723802151, 38292175922414727, 41526851364489247, 37235538033891720,
      25756358401032192, 36506541540603009, 34764622821556698, 37020020114638210,
      45463794419532796, 38207508074338693, 993862013519818, 38388933767730056,
      21539778664958087, 36383394627584132, 48837615733014871, 36651678971319681,
      34202583412998771, 37441138839515011, 47717277885957521, 38240500134166919]
    ) [
      16754536556300484, 36408683747344516, 58407889496932720, 36706655290915457,
      59817145600541357, 37565385498973315, 4933880296670717, 38331759129539720,
      54474769015408717, 37768807766867592, 24348970612458558, 36493347250072705,
      27446174641652170, 36967242902185346, 28575016639955910, 38061271685655941,
      9438394780059657, 38409825226866056, 14504570708723889, 36380090992705670,
      45741348039000403, 36627489430291841, 20691621320098393, 37369669560285315,
      8028992634324308, 38333957649464967, 29141759114971158, 38232805364769416,
      16747763333301817, 36451565254561665, 7461193593684382, 36840797420802690,
      50529330373886781, 37792988382184580, 15912087313286912, 38343853623217032]
    ) [
      22658737843045911, 36480152959542657, 20409214323360188, 36918863803352962,
      10278863976956817, 37923831993972357, 18727481329158089, 38448308922382216,
      53912154079922370, 36029364835851143, 42363609663308110, 36605498895743105,
      8588046995784257, 37299299826238851, 47153825414808851, 38412023444778374,
      39556539415365685, 38507684412567944, 145374008346566, 36440570020842368,
      1831621044175250, 36802314044062338, 32514682752893716, 37745708409095044,
      27734216717403796, 38395531525368968, 57008451831761022, 37217945227086984,
      32511856627712000, 36543925456048001, 51653340470477312, 37121176526588546,
      3243033251513444, 38308666365346438, 25764025034246219, 38510981320044680]
    ) [
      39267346264260608, 36584607906376065, 69949454477984298, 37230029670930050,
      31109541284644049, 38361446060857478, 50252764625799342, 38629730572356488,
      12813745145284830, 36431773810294916, 68822596780917128, 36767129235760257,
      15062997970617069, 37689632208765572, 17319608209802847, 38450507643661448,
      13098445661112486, 37732523161738121, 30260026727760942, 36527432546747521,
      42646029545144813, 37061802143704450, 60663649323353126, 38278977219350917,
      41245294790608950, 38534071601109896, 5215737565710624, 36402081225256838,
      54185713306009960, 36679167131117697, 44617307877245583, 37493916169410691,
      64324520559019463, 38369144471039879, 59822939604748423, 38200920181903752]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [26607401977874228, 37919440155154055, 33934]
    ) [
      55599891520063356, 36029366094176647, 19000864469188876, 36476854323993729,
      22661035612078524, 36951849470956674, 22101019160249270, 38097555384812933,
      26044499279251268, 38210810249965447, 145700434839486, 36360304531147392,
      41237683986006337, 36609896975808385, 16750907220525641, 37350977627728259,
      19850868639106366, 38081069337492359, 50532994043250518, 37303709466080903,
      11963891265863680, 36433972783300225, 3239004517597582, 36823204966318466,
      46025666320892719, 37768798505610884, 17882296173823792, 38119549895659911,
      39273127396476837, 36335015411318916, 30541488840278312, 36545024934120321,
      56438462319591940, 37167356585386882, 7465256689239188, 38222903384676998]
    ) [
      30828659054839820, 36353707360649348, 38141416291991866, 36589005986441345,
      4084374352921137, 37283906428565379, 52501660991980801, 38211909660938630,
      55036769767163766, 37866664419130503, 10275019913462897, 36422977532803201,
      69667030300918147, 36784721589578369, 28855447925195524, 37698428972888452,
      57851287605511840, 38165730038345607, 40681739234609077, 36328413946214022,
      27726700417941793, 36528532041596801, 46868192850903537, 37104683634063746,
      63197095915586646, 38103057808393861, 38710984892254168, 38225105276872583,
      4081389384926872, 36388892219350657, 54467175397425503, 36689062853208961,
      55313485842580125, 37538996951467907, 22385419046847953, 38108554930413959]
    ) [
      9147938963949168, 36414181322338945, 64600411999863161, 36749536764499329,
      11403771732787934, 37652248544982148, 66295786008708665, 38220706508941191,
      64889012434798559, 36029365624403079, 25474879129157918, 36510939637446017,
      38142356902347231, 37046408729252994, 51374897781572633, 38182220800075909,
      52784935595378641, 38325161153778567, 145575877511140, 36381195554069376,
      49963524229792087, 36661574693411457, 40958068754449022, 37473025230375811,
      45184363873732008, 38154735710615175, 7749227086448557, 37270723244843400,
      17311993133826048, 36463659999908993, 15905545975595436, 36901271332091778,
      4930783583961988, 37951319046461829, 36178010753042330, 38229502669069959]
    ) [
      23786007793860608, 36496645818510721, 30260963063857616, 36992531971617666,
      36737936995484640, 38158029312884101, 69673636071049147, 38351549885840519,
      23510167926966381, 36376797440376964, 46304302287389008, 36636285623978881,
      26884148118061667, 37407053458952835, 33924819341772147, 38210812951115143,
      13378855472564204, 37830380787097480, 15904601052054615, 36451565237784193,
      9431544200724897, 36858389824953474, 59818133455995731, 37821576003281540,
      50815143335003998, 38269085876214919, 30548730273957919, 36349304667134854,
      35045152893075766, 36568114997075073, 65445786130088475, 37215735801661314,
      20976296092927172, 38284478099440262, 66014504316012459, 38254793802125191]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [36176713656796993, 37928232909449094, 34036]
    ) [
      8311077510416028, 36029367721578375, 10275032815730941, 36416380395926913,
      66289283335160187, 36769328191905153, 24351792462398198, 37678637176381060,
      51658966951757528, 37950222152144774, 146117049091854, 36335015478493056,
      26600796216197412, 36517536791099777, 43208962318303718, 37091489276423298,
      56441546149364808, 38136039483032453, 55598564357932719, 37410362563690118,
      6334335896551424, 36388892252906369, 51933870541930845, 36674769000718721,
      51935734581592721, 37502712748980611, 28014042411795894, 37872156457478535,
      66857756705916599, 36322920699527300, 19563831602938134, 36470257187117953,
      19564763623031220, 36937555618466178, 12812263323501482, 37896345813886085]
    ) [
      56443186868684567, 36320721592385668, 22941565683532055, 36497745313360769,
      33920172121227730, 37029915803174274, 40115799927784460, 37946925462729861,
      65450377524905851, 37940329147992454, 2393621781316816, 36373498872010625,
      46867252240679246, 36645081800887681, 36454404701520495, 37449935200976515,
      53347241277818241, 37917237340244614, 57569567806555863, 36306423713683078,
      15623126093562120, 36453764261039489, 11964840466219426, 36885877934418050,
      71358805072380790, 37994199932826244, 47154495462082223, 38046980383360390,
      71353908825130702, 36351508354238592, 35608111436431670, 36574712133951105,
      143668843414052, 37266314024413571, 66293887603737837, 37926036906091910]
    ) [
      71635383798171328, 36362503587958144, 42645071754723651, 36619792697900161,
      22380479770165844, 37385062991512451, 12532897202734423, 37975513301991047,
      31673921491339013, 36029366849159815, 12808329081094398, 36438370880143745,
      5209355124769171, 36840797387246722, 54470048767968068, 37857859182348420,
      61791739704215337, 38056876659111302, 145915184908131, 36339413525003648,
      31667405927186731, 36552721616179073, 60942122077225484, 37200342387210370,
      28857419345462449, 38093160190518406, 10563044831037137, 37365282486310791,
      7178752236486656, 36402086543436161, 60659710785454445, 36733043855197825,
      7744528315089614, 37608267660436100, 29421726540334669, 37992004399320199]
    ) [
      10556499202179072, 36426276101240961, 71637376613056903, 36802313976951681,
      37581292463817496, 37725917099134852, 12252646315427585, 38086564160945287,
      40962003025561478, 36330617314476164, 28571138233106722, 36534029666845569,
      51371844018471416, 37135470328745090, 69389635599434869, 38172325782677637,
      18726003843696421, 37924937411294599, 4645443069838485, 36391091259384193,
      55874571756011874, 36701157615334273, 63194879680938668, 37563186710603139,
      35895960237147622, 38039284456301959, 53629278916740919, 36309722248551302,
      20126777261129999, 36481252404059777, 25757294716092865, 36973840005505922,
      28575072475579346, 38050277928326533, 6059406553352032, 38138241542991239]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [55879665670129176, 37787491310605957, 34178]
    ) [
      14502461830170172, 36029369432831622, 11682459240202520, 36392190922011265,
      47148748692750683, 36638484664011649, 34202574822670953, 37412551486861955,
      8873000961607017, 37665444714658439, 146580899137057, 36351508505238656,
      20971249437212970, 36459261970176641, 10557452697698724, 36880380258837122,
      62351528507573101, 37714925254432388, 52219915443734255, 37542302147022725,
      11119513581879296, 36378996648258689, 37578479224127818, 36571413582291329,
      71356812181078559, 37247622158967426, 2962331374224590, 37648954170979206,
      31954348476761509, 36351508555497605, 17874994628297001, 36429574820678273,
      65726333382001027, 36763830549879169, 19566679203152626, 37753403346305412]
    ) [
      17599421024011830, 36333916050686085, 17312018904482076, 36441669549247873,
      3801963061084563, 36832001143227522, 48559014126781242, 37899640657748356,
      66575628900664824, 37872155517920901, 6615836626289983, 36363603233807745,
      33074819466297660, 36548323519336833, 58408808631599623, 37184949039869826,
      43775567338898589, 37777601846439302, 37583839422612956, 36331712481148806,
      13652796962210072, 36413081894599809, 59533797993841011, 36724247627956609,
      3803839985910469, 37595072916917892, 16474354332829325, 37789690669419910,
      6333189211653758, 36352608033643137, 25756375581491505, 36497745346916737,
      31386862970765775, 37020020047527042, 35330579293504511, 38072264805481605]
    ) [
      2392539535279788, 36349309381316737, 29415588933697841, 36528532058374785,
      47994105642648049, 37122276021437570, 6902010379404387, 37979907909137542,
      42087499181557291, 36029368929527942, 10275049996189962, 36399887553736833,
      54748663259365734, 36692361388092545, 59817137010148002, 37517006802802051,
      3243845029758464, 37805084352324487, 146452053657218, 36340513187630208,
      22660103592247588, 36480152942765185, 23786939813953981, 36963944249858434,
      17034499645211590, 37755608795309957, 19287691059431208, 37500521728602502,
      7741749435662336, 36378996581147777, 42645088934986062, 36613195544246657,
      19847166324408908, 37359773972412803, 2681354622895406, 37713825021509766]
    ) [
      6615815168360448, 36385593684468609, 49682044958114137, 36660475148228737,
      44335811424912001, 37471925886524547, 7184924196832659, 37845767809313159,
      70798350543521430, 36325119773114500, 19000877354549527, 36463660033464193,
      15624066703786412, 36912266532256130, 4930830829716368, 37905141084816261,
      29421176777443053, 37916137845327494, 4082514591253765, 36365802223507585,
      38422899859030338, 36586806946408833, 7180620571705905, 37297100853314691,
      49124304867329282, 37807286076751494, 49687722989094489, 36318518341603462,
      13934263348527375, 36427375679979905, 69385551029305733, 36789119669644161,
      32233216366052110, 37772095882851460, 17036745951577778, 37901842583537542]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [146022543427000, 37513706724467590, 34245]
    ) [
      8871785477998200, 36029371479597189, 20971305273360717, 36402086845434753,
      37859984266330459, 36553821228473473, 59534717128507913, 37173953957147266,
      27168964617667714, 37401562897062277, 147036151252227, 36394390230486912,
      23504601538658636, 36435072563370881, 61222690804629891, 36725347173139329,
      1270569490678473, 37697326894314628, 67419817580004743, 37639055294651524,
      21815747383754752, 36397688765369473, 31667466058498387, 36506541658046849,
      31949821514187220, 37022219137892482, 59537255490487288, 37710522543877765,
      53345407302665478, 36398788377575557, 22378693041946958, 36419679216030593,
      49119120775414127, 36639584192417665, 34765533366092393, 37368570669427587]
    ) [
      46309065471984906, 36382295434723461, 21252763069743425, 36426276319351425,
      56156076798542201, 36692361404870785, 58691237103305378, 37508210122573443,
      53910255636350541, 37655547163767173, 19563908893279669, 36389992049755265,
      29697106861326668, 36492247822334081, 23786944109183428, 36965043778263682,
      12530753987969988, 37991996581101701, 51937890688599507, 36389986597454213,
      20689821706387783, 36411982517194113, 45741378104623464, 36614295139762561,
      20410124867830349, 37325688893847683, 55033978015483160, 37489519012209798,
      21251362985903532, 36391091611715969, 25756418532344138, 36460361599248257,
      4083459513221536, 36833100671633026, 39833238309143357, 37501619109430660]
    ) [
      14777438517757461, 36374598635304065, 25474922080207166, 36473555856222593,
      15061116750496177, 36910067492222338, 65166385650762637, 37491724461121156,
      42930816000165588, 36029370489769093, 17030582583722296, 36397688647926145,
      41237718346858842, 36589006003220353, 6617670618087983, 37276209964614019,
      4369847996024027, 37508213931178373, 146821410162048, 36376797759224960,
      22660146543165759, 36446067746757505, 70229993139765649, 36789119669643905,
      27448111697134349, 37817176010575492, 10561490055824633, 37597275815766405,
      17875033284116480, 36392191073010049, 34482237300506962, 36534029767511937,
      47994105642648052, 37115678934893442, 24353458933040211, 37625868251885958]
    ) [
      12245434963951616, 36381195721846913, 36452570727285067, 36561517876976769,
      65445764654793236, 37215735885548162, 11124886653338802, 37654452098181254,
      40116989655352715, 36357006231076997, 18156478195204398, 36427375780646017,
      63474503503217023, 36745138634100609, 11966747456340703, 37695128693154948,
      54190983304283702, 37758903538516357, 13089877054752146, 36373499090120833,
      29697093975966017, 36510939704557185, 37016435520340444, 37054105394533762,
      59255999560057884, 37868853862482821, 8309840538928564, 36362498806747270,
      17030573993460016, 36408683881644929, 50807979225481577, 36657176613345409,
      43209894338003581, 37425746012278403, 49123308449269175, 37628059926767494])]
private def schedBlks30G2 : List (ℕ × ℕ) := [
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [20976721296524386, 36324045091895428, 34310]
    ) [
      12250107947943240, 36029372687403653, 26037953640169836, 36406485042944385,
      30260082585141592, 36488949253896577, 22098072773624254, 36965043761485954,
      59818434109932477, 37433442996424325, 147362526758286, 36418579939290496,
      24630540101124445, 36417480209553537, 44896944584622442, 36607697935776641,
      20410116277830215, 37292703243022723, 3804982491973043, 37689619693045892,
      28008312837406720, 36407584588128129, 27445302753001815, 36457063064365185,
      2676050269602205, 36833100638077058, 31388920288019262, 37305905670623620,
      4927377717363372, 36426276638032006, 24912023668097379, 36409783577827201,
      37015555041362271, 36546124546414977, 58971754289791491, 37156361670439810]
    ) [
      60662579867911639, 36416380865609861, 24067581557637468, 36413082129487489,
      41519210503962981, 36582408883121793, 6899141299700269, 37244323993190531,
      35892927980405972, 37177255512095877, 27445354270066156, 36406485076499841,
      26319394256093526, 36449366382306689, 68259655417823633, 36788020074129025,
      19848252966142733, 37354284685508740, 57285142164702503, 36426270481185667,
      24912027962999139, 36408684049421953, 35045208729289053, 36529631670669185,
      47712609190838765, 37107982353499010, 71923511679878202, 37385068444180356,
      30258562244445054, 36411982718526849, 25193485759381849, 36429574971677825,
      54748693324988795, 36685764251216001, 57002387243041441, 37702823278030723]
    ) [
      26317912568726795, 36402086962878849, 25193472874152274, 36440570188619649,
      63193037116768647, 36745138617322625, 8589039146009312, 37799582767546500,
      69671475670975417, 36029372066750851, 24067585852735839, 36403186407395969,
      33074858122248537, 36513138794923649, 36734951953498587, 37053005933237890,
      22664329894855698, 37690735813971078, 147173575197694, 36407584638460288,
      23786097990730070, 36424077329652097, 50807987815809396, 36653878011352961,
      42646952974582395, 37435641096832387, 65168172356306510, 37666538790326661,
      25474990801649664, 36403186457728897, 28852686226555221, 36475754980143745,
      14498145322041777, 36912266498700162, 65729206754575244, 37670935561913988]
    ) [
      22378714517307392, 36398788293774977, 31104503220109651, 36497745464360321,
      27727641028297163, 36996930018127234, 44056007215580127, 37733608781641349,
      57848843715118406, 36402086979567749, 22660176608788817, 36417480175997825,
      47148774463340908, 36625290373482369, 28291518706254426, 37337783924413315,
      10278352910058880, 37488416564538246, 24067594419996116, 36398788344107649,
      27163819186028881, 36464759712869249, 6898239345426852, 36858389757842306,
      43492516087432024, 37121188337902724, 9996817795286588, 36410877318388869,
      22941664470663511, 36408683982311809, 38985897058402656, 36561517893755265,
      65727239631438355, 37201442200833410, 54190802905695373, 37151972700606595]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [48841416822653875, 37126674319523718, 33599]
    ) [
      25197183797200315, 47353230476417412, 21815773154148706, 36382295451584641,
      19845371006058815, 36425176740613761, 64318924138119548, 36784721455356545,
      13092784805413646, 37142078136093572, 11966073151194153, 36399887989956776,
      17875046169477452, 36380096310885761, 28289706207445316, 36507641085786497,
      46868158490051037, 37092589140379010, 11688111488336928, 36908971420023683,
      22660210969454613, 36381195956734337, 17312066150564157, 36402086727991681,
      49119090709987682, 36679166963341441, 53343208251032221, 37864453920003459,
      15344464365322855, 36404286106107523, 17593571192897870, 36373499174009729,
      22660137952969019, 36462560555392641, 20127687805927850, 36965043828594306]
    ) [
      30544400888727058, 36418579958561667, 21534280997241179, 36392191140121217,
      28852673341129036, 36496645885622145, 35890496957940174, 37045309335065730,
      16191668150633465, 37128879198308484, 27163884257706862, 36396589354408321,
      20126863163097418, 36406484891945345, 46304323762880867, 36643982205372545,
      40958098819220087, 37740205616394115, 59537165319177391, 36423144382358147,
      21534285292339550, 36385594003245185, 23786063630139717, 36455963468849025,
      11401864742666656, 36911166953516930, 65729133738820486, 37310300730762373,
      28332484114744247, 36397688899591553, 18438000417800522, 36391091544605313,
      36171100045738321, 36567015435115393, 6899128414470689, 37222333458644099]
    ) [
      31146963296748643, 36410883240454273, 22941660175696215, 36413082079155073,
      44896940289458535, 36617593657867649, 27728573047669334, 37381763886205315,
      50249311379424922, 46955207955080324, 25474999391781230, 36398788360885889,
      25474943555764559, 36455963485627265, 4927871558123930, 36859489219137154,
      50529270245524311, 37635746727104644, 43773183617107128, 36414181842447782,
      22097230950596953, 36399887805402497, 36171104340967768, 36549423081297537,
      65445756064465417, 37171755235888514, 67979967228249243, 37000232898447493,
      26319441502119677, 36396589337630593, 22097209475170635, 36427375847756929,
      59815281560748412, 36741839948219265, 1270655391793886, 37096999920895108]
    ) [
      28008317132524680, 36407584588128129, 26600869232804182, 36451565439116929,
      71355905931706774, 36812209648710273, 24070467812819752, 37113492628917380,
      31676275066176548, 36427376169030781, 24630548691386723, 36406484992611713,
      35326683706065244, 36535129295917953, 53623661011960310, 37133271540374914,
      28858325582644296, 37299286773753219, 29978668345754482, 36408684166865793,
      24349047944151382, 36429574954900353, 56156081093575034, 36704456133439873,
      63476419083272885, 37878746983971971, 18441861667521305, 36434143944640131,
      24912036553195881, 36402086929323393, 29697119746556245, 36490048782301057,
      26883190327837122, 36992531971615874, 43774768460104660, 37342186869814918]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [10840830372250384, 36770406950376324, 33416]
    ) [
      45185295861318620, 47390613083290753, 9993639445889333, 36337214786969217,
      6897324505989398, 36361404176997505, 38141407701991740, 36635185843909249,
      38706324775797367, 38171215483097219, 9714363553120134, 36351508706570664,
      5771437484507423, 36329518037799553, 11963921331683603, 36418579419182977,
      8587037664510337, 36916664595541378, 14782351930590079, 36878190949296007,
      9149201630668779, 36330617650092929, 3801069697007888, 36339413692780417,
      25756354105999654, 36545024766344065, 7743570524209685, 37238825562633091,
      46589032777680554, 36348210107109250, 4364041125855516, 36320721827335041,
      6334357372109065, 36380096042443137, 57844875117494614, 36786920377944961]
    ) [
      62631289841354057, 36378996936064898, 11682510781186360, 36348210037466753,
      14497247662604579, 36419679014698881, 1550094526611839, 36868285396044674,
      43773780609237852, 36857307107580293, 16749146925335184, 36357006331819393,
      8867700883489062, 36354807090454657, 26600804806590767, 36529631452559745,
      67979048034402812, 37145366772273794, 28012788289602908, 36379166366657923,
      10838077261054263, 36342712412218241, 10275071471681820, 36386693279984769,
      54185670355419481, 36744038887585153, 66009857085899495, 37084910829510019,
      16510895858942973, 36354807275008897, 7178833843159330, 36341612783147137,
      18156456719647008, 36465859023164545, 36171941868831161, 37035413814304130]
    ) [
      23265835744855009, 36378996916702081, 13371373526483257, 36365802424839809,
      26600821986787640, 36512039149073793, 55312497986732519, 37110181812970114,
      37016177896883287, 47385116078740868, 16749146262765903, 36362503940290177,
      13652827027767596, 36393290450417025, 49963519934824794, 36702256942408065,
      58128407411065530, 36862803658948483, 36735965586752899, 36378996950257064,
      12526935711383864, 36357006231153025, 20126815917080876, 36461460959876993,
      25757251765240236, 36996930152345986, 7465780659192772, 36904570890643844,
      16749146262841507, 36359205371852417, 10838051490529576, 36371299982977409,
      37296978477154627, 36606598239594369, 28854507314643540, 37676432767564419]
    ) [
      21534293882546151, 36376797843113601, 16186149063590201, 36395489574337665,
      46585785854296411, 36662674070818177, 48276572769714829, 37932622231633539,
      13656018222678339, 36400987504105859, 16467658400891211, 36369101060388993,
      20971262322573622, 36452664816523393, 15905511614939552, 36943053277267330,
      56159426913272737, 37200339853705606, 22660211615630096, 36377897371519105,
      14497282023326008, 36378996698592385, 35326649345278279, 36579110146907521,
      15062031589540401, 37314692687042691, 6899665262184124, 36403352434833284,
      16467662695989581, 36364702980322945, 16749090426683696, 36418579553404033,
      67133691085226361, 36817707173292673, 32233147648082731, 37068391093543556]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [15906572486017602, 34027138508308867, 33631]
    ) [
      62068249636143910, 47282857219419008, 66006902109077747, 36280039276341120,
      64318009298354403, 36292133988132480, 10556490612179192, 36470256918675841,
      57282831412920783, 36796820294408834, 29134938772439126, 36287735991955623,
      63755063640031464, 36275641145942400, 67414255517139170, 36327318729323904,
      38422835432751393, 36696759099048833, 52780206759183037, 36750649043445634,
      65162464293922584, 36276740691125632, 62910617234669792, 36282238249263232,
      2956571750596844, 36403185920842625, 22942394621657471, 36949650900692866,
      70503071427429055, 36283337880833410, 62629146553123044, 36270143537470848,
      63755046459637981, 36300930148264320, 21252655692546310, 36573612202882433]
    ) [
      55593517740229395, 36304228970950274, 66851339924373751, 36286636429994880,
      68540181194178794, 36329517802912128, 37015443369263394, 36672569574799233,
      36173144477696675, 37227823718658435, 69947612578808465, 36289935065543552,
      65162455703716075, 36288835436472448, 3801013860925680, 36402086409215617,
      17031359980470651, 36940854589560450, 17875089145496438, 36303300047574402,
      66288381380886772, 36282238333151616, 66006876338684133, 36307527318695552,
      21534143554421001, 36561517457535873, 14217675379671601, 36342719525907843,
      69428148529365479, 36288835553915520, 64318022183518441, 36281138771190912,
      70791998187798760, 36357005912376960, 61504049814208838, 36830901430264961]
    ) [
      4407755320231827, 36311925650426497, 69384644780065021, 36300930265707904,
      6052852329906427, 36402086459548545, 10275883229348214, 36926560418298242,
      66009990236636020, 47346630118607759, 71355012567433482, 36297631764380032,
      68821673351151859, 36315224051087232, 21815631416295696, 36541726080462465,
      10276896854868506, 37005728694888835, 55594320856452773, 36307527553582759,
      67977252716249337, 36292134072020864, 423284075364592, 36359204985965441,
      56718945145028934, 36797915628441473, 17877601710146328, 36853973089096835,
      70510574752212995, 36294333162387072, 66569847767335150, 36298731175341440,
      11119453450764541, 36463659781800065, 49682899666239936, 37026618123947394]
    ) [
      6615888184911860, 36322920917701505, 1549235522994440, 36330617448761473,
      22660082116886812, 36527432328637825, 1269551569207811, 37159660339551619,
      66006103212852605, 36337214823094402, 1830727680164115, 36310826088465281,
      4082518903193858, 36368001246762625, 53059736088052042, 36762730753030529,
      65728352045204216, 35932598132077443, 5771446739960627, 36317423292452481,
      71354999682072834, 36314124573015424, 13371291919876361, 36457062712034433,
      40675580151038387, 37027717417462914, 60383716236166099, 36332988019159426,
      423335616479503, 36304228901257089, 71917936750199033, 36338314080486784,
      35326593509261609, 36642882425301889, 36173088641090181, 39491726381137795]),
  (16,
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
    m1K32P56Cat (
      m1K32P56 [1266665312845828, 31544438333374336, 32919]
    ) [
      58126358686433644, 46204238627452545, 25473874092785755, 36129403851266688,
      26881266156404828, 36141498630168704, 33918222179532905, 36194275825844096,
      704638789517479, 36402086795094913, 56720040360247674, 36099716601102506,
      18436888004165696, 36103015169540480, 20688713587982404, 36118408533658496,
      30540458033446999, 36203071918864768, 67695747672670393, 36650575416331904,
      9429555603417316, 36065631220539776, 9711034875084833, 36070029317383040,
      11962864753934374, 36085422681501056, 23221992672886840, 36162389552423040,
      34199752992522362, 36031545840170370, 703698179358722, 36031545839977088,
      703698179358722, 36031545839977088, 985173156069378, 36033744880010112]
    ) [
      71920578179465844, 36205271347232386, 44614464571408543, 36204171782823552,
      47147765131608224, 36226162300595072, 63754986328457403, 36382294713366656,
      20690646347972986, 36790219013507714, 41236718233420487, 36188778401927552,
      41236709015388305, 36195375555581056, 46866277269864602, 36242655092452736,
      11119354664222928, 36549422611520129, 39831172403724822, 36174644755199618,
      36733044962590851, 36173385004253824, 38703391274598532, 36190977391627392,
      49681044216905879, 36284436953742720, 47711578383417609, 36617593657875329,
      31706103601463868, 36151394436149120, 31666418071076975, 36156892044620160,
      35888589966966902, 36187678756078464, 56717983059574937, 36373498402235776]
    ) [
      56761267763119135, 36245953912556416, 55029197625852100, 36245953862222720,
      59532848793288903, 36293233399093888, 27726623106695426, 36651678434433153,
      15906314791846541, 47282858125198978, 53340326290489536, 36236058123353216,
      53621796972036284, 36249252363550848, 65162399867633867, 36357005744601216,
      8024006104285521, 36775926905860738, 31950298308903516, 36227261929666471,
      50244050006278323, 36227261879333504, 53903259063582901, 36260247597269888,
      7178704990798044, 36505441492090753, 40394526087610879, 36845204258580610,
      47992211537503886, 36211868548770432, 48555165785620649, 36223963277340032,
      55873605375459510, 36294332826833280, 42644942902558986, 36718749935591809]
    ) [
      63192109391652662, 36270143520693888, 61503216580919514, 36274541567203968,
      423262600003813, 36384493988286337, 14216545787937130, 36923262135078530,
      68820492238619331, 36272342596806274, 60377308084142298, 36263546333484416,
      61784687262466261, 36291034409394560, 16186041686327544, 36538427394580097,
      7743656425062943, 37326777131124867, 60658792301036080, 36260247765046656,
      58688415273615569, 36261347243118720, 65443900614803670, 36333915815867520,
      53622643090424111, 36800114735582081, 66007881392489223, 36260415268840324,
      57562515366445264, 36251451521026944, 57843986048188618, 36269043908399488,
      3519508818788577, 36437271049741441, 47149599105188267, 36600005162890370])]
private def schedBlks30 : List (ℕ × ℕ) :=
  List.append schedBlks30G0 (List.append schedBlks30G1 (schedBlks30G2))
private def schedBlocksA (sidx : ℕ) : List (ℕ × ℕ) :=
  if Nat.blt sidx 16 then
    if Nat.blt sidx 8 then
      if Nat.blt sidx 4 then
        if Nat.blt sidx 2 then
          if Nat.blt sidx 1 then
            []
          else
            schedBlks1
        else
          if Nat.blt sidx 3 then
            schedBlks2
          else
            schedBlks3
      else
        if Nat.blt sidx 6 then
          if Nat.blt sidx 5 then
            schedBlks4
          else
            schedBlks5
        else
          if Nat.blt sidx 7 then
            schedBlks6
          else
            schedBlks7
    else
      if Nat.blt sidx 12 then
        if Nat.blt sidx 10 then
          if Nat.blt sidx 9 then
            schedBlks8
          else
            schedBlks9
        else
          if Nat.blt sidx 11 then
            schedBlks10
          else
            schedBlks11
      else
        if Nat.blt sidx 14 then
          if Nat.blt sidx 13 then
            schedBlks12
          else
            schedBlks13
        else
          if Nat.blt sidx 15 then
            schedBlks14
          else
            schedBlks15
  else
    if Nat.blt sidx 24 then
      if Nat.blt sidx 20 then
        if Nat.blt sidx 18 then
          if Nat.blt sidx 17 then
            schedBlks16
          else
            schedBlks17
        else
          if Nat.blt sidx 19 then
            schedBlks18
          else
            schedBlks19
      else
        if Nat.blt sidx 22 then
          if Nat.blt sidx 21 then
            schedBlks20
          else
            schedBlks21
        else
          if Nat.blt sidx 23 then
            schedBlks22
          else
            schedBlks23
    else
      if Nat.blt sidx 28 then
        if Nat.blt sidx 26 then
          if Nat.blt sidx 25 then
            schedBlks24
          else
            schedBlks25
        else
          if Nat.blt sidx 27 then
            schedBlks26
          else
            schedBlks27
      else
        if Nat.blt sidx 30 then
          if Nat.blt sidx 29 then
            schedBlks28
          else
            schedBlks29
        else
          if Nat.blt sidx 31 then
            schedBlks30
          else
            []
private def schedLA (sidx : ℕ) : ℕ :=
  if Nat.blt sidx 16 then
    if Nat.blt sidx 8 then
      if Nat.blt sidx 4 then
        if Nat.blt sidx 2 then
          if Nat.blt sidx 1 then
            2
          else
            3
        else
          if Nat.blt sidx 3 then
            4
          else
            5
      else
        if Nat.blt sidx 6 then
          if Nat.blt sidx 5 then
            6
          else
            7
        else
          if Nat.blt sidx 7 then
            8
          else
            9
    else
      if Nat.blt sidx 12 then
        if Nat.blt sidx 10 then
          if Nat.blt sidx 9 then
            10
          else
            11
        else
          if Nat.blt sidx 11 then
            12
          else
            13
      else
        if Nat.blt sidx 14 then
          if Nat.blt sidx 13 then
            14
          else
            15
        else
          if Nat.blt sidx 15 then
            16
          else
            17
  else
    if Nat.blt sidx 24 then
      if Nat.blt sidx 20 then
        if Nat.blt sidx 18 then
          if Nat.blt sidx 17 then
            18
          else
            19
        else
          if Nat.blt sidx 19 then
            20
          else
            21
      else
        if Nat.blt sidx 22 then
          if Nat.blt sidx 21 then
            22
          else
            23
        else
          if Nat.blt sidx 23 then
            24
          else
            25
    else
      if Nat.blt sidx 28 then
        if Nat.blt sidx 26 then
          if Nat.blt sidx 25 then
            26
          else
            27
        else
          if Nat.blt sidx 27 then
            28
          else
            29
      else
        if Nat.blt sidx 30 then
          if Nat.blt sidx 29 then
            30
          else
            31
        else
          if Nat.blt sidx 31 then
            32
          else
            33
private def m1K32VScaleNat : ℕ := 10000000000000000
private def m1K32TauDen : ℕ := 100000000
private def m1K32VTableNat (r : ℕ) : ℕ :=
  if Nat.blt r 16 then
    if Nat.blt r 8 then
      if Nat.blt r 4 then
        if Nat.blt r 2 then
          if Nat.blt r 1 then
            0
          else
            6426990820000000
        else
          if Nat.blt r 3 then
            10180815029781160
          else
            13173474631417317
      else
        if Nat.blt r 6 then
          if Nat.blt r 5 then
            15728367572132778
          else
            18012357865391713
        else
          if Nat.blt r 7 then
            20086573770690204
          else
            22007385106004426
    else
      if Nat.blt r 12 then
        if Nat.blt r 10 then
          if Nat.blt r 9 then
            23778316079166753
          else
            25500454327756943
        else
          if Nat.blt r 11 then
            27106707716832731
          else
            28640748900283013
      else
        if Nat.blt r 14 then
          if Nat.blt r 13 then
            30102803536464998
          else
            31507986440847640
        else
          if Nat.blt r 15 then
            32809407050701037
          else
            34115805278727449
  else
    if Nat.blt r 24 then
      if Nat.blt r 20 then
        if Nat.blt r 18 then
          if Nat.blt r 17 then
            35335418074029581
          else
            37008975084134163
        else
          if Nat.blt r 19 then
            38508764101141750
          else
            40379272425417532
      else
        if Nat.blt r 22 then
          if Nat.blt r 21 then
            41922215675298076
          else
            43663671949425039
        else
          if Nat.blt r 23 then
            45308912503669651
          else
            46917990986188154
    else
      if Nat.blt r 28 then
        if Nat.blt r 26 then
          if Nat.blt r 25 then
            48493189445287926
          else
            51037731870039215
        else
          if Nat.blt r 27 then
            51037731870039215
          else
            51037731870039215
      else
        if Nat.blt r 30 then
          if Nat.blt r 29 then
            51037731870039215
          else
            51353784004859405
        else
          if Nat.blt r 31 then
            51353784004859405
          else
            if Nat.blt r 32 then
              51353784004859405
            else
              51879628875056110
private abbrev m1K32VTable (r : ℕ) : ℤ := (m1K32VTableNat r : ℤ)
private def m1K32SidxOfR (r : ℕ) : ℕ :=
  if Nat.blt r 3 then 0 else if Nat.blt r 33 then r - 2 else 30
private def m1K32TauNumOfR (r : ℕ) : ℕ :=
  if Nat.blt r 16 then
    if Nat.blt r 8 then
      if Nat.blt r 4 then
        if Nat.blt r 2 then
          if Nat.blt r 1 then
            1
          else
            1
        else
          if Nat.blt r 3 then
            1
          else
            6876170
      else
        if Nat.blt r 6 then
          if Nat.blt r 5 then
            3246839
          else
            4904329
        else
          if Nat.blt r 7 then
            5583123
          else
            10457444
    else
      if Nat.blt r 12 then
        if Nat.blt r 10 then
          if Nat.blt r 9 then
            5554557
          else
            14669640
        else
          if Nat.blt r 11 then
            16275217
          else
            18446661
      else
        if Nat.blt r 14 then
          if Nat.blt r 13 then
            18486217
          else
            16892980
        else
          if Nat.blt r 15 then
            12089032
          else
            12805772
  else
    if Nat.blt r 24 then
      if Nat.blt r 20 then
        if Nat.blt r 18 then
          if Nat.blt r 17 then
            9886992
          else
            1713823
        else
          if Nat.blt r 19 then
            14702973
          else
            3132064
      else
        if Nat.blt r 22 then
          if Nat.blt r 21 then
            2428465
          else
            2696763
        else
          if Nat.blt r 23 then
            2037070
          else
            2037134
    else
      if Nat.blt r 28 then
        if Nat.blt r 26 then
          if Nat.blt r 25 then
            2036942
          else
            71943238
        else
          if Nat.blt r 27 then
            67016781
          else
            62957494
      else
        if Nat.blt r 30 then
          if Nat.blt r 29 then
            59579260
          else
            56754581
        else
          if Nat.blt r 31 then
            40056487
          else
            if Nat.blt r 32 then
              28637701
            else
              16473911
private def m1K32RawStageOfR (r : ℕ) : M1L50RawStageSpec :=
  m1L50BuildRawStage m1K32SidxOfR m1K32TauNumOfR schedLA schedBlocksA m1K32TauDen r
private def M1K32RangeSound (rLo rHi : ℕ) : Prop :=
  ∀ r, rLo ≤ r → r ≤ rHi → M1L50StageSoundAt (m1K32VScaleNat : ℤ) m1K32VTable (m1K32RawStageOfR r) r
private abbrev m1K32CheckSingle (sidx r : ℕ) (bkt : M1L50BktRec) : Bool :=
  checkSchedChunkL50 sidx m1K32TauDen m1K32VScaleNat r r
    m1K32SidxOfR m1K32TauNumOfR schedLA schedBlocksA m1K32VTableNat [bkt]
private theorem m1K32BoolAnd1 {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1
private theorem m1K32BoolAnd2 {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2
private theorem m1K32RangeSound_and {a b c : ℕ} {x y : Bool} (hxy : (x && y) = true)
    (hx : x = true → M1K32RangeSound a b) (hy : y = true → M1K32RangeSound (b + 1) c) :
    M1K32RangeSound a c :=
  m1L50StageSound_join (hx (m1K32BoolAnd1 hxy)) (hy (m1K32BoolAnd2 hxy))
private def m1K32Bkt3 : M1L50BktRec := ⟨3, 3, 6876170, 66341284000, [
  m1K32P56 [
    43528545357181447, 23577083642683707, 35087479032162272, 43240762214293310,
    48500483101052639, 70259322604012722, 31565],
  m1K32P56 [
    51882817092080414, 58710049241962930, 12299980361005709, 34220305588339800, 2039689208]]⟩
private def m1K32Bkt4 : M1L50BktRec := ⟨4, 4, 3246839, 193749149381, [
  m1K32P56 [
    43566139205929468, 7819982696211515, 53386598439074711, 45417715194319891,
    836726760877023, 23419138160001685, 45768],
  m1K32P56 [
    10391886825542453, 24169984912228729, 16240655766368970, 34026119426007699,
    57518269452277902, 62575923636877746, 30867],
  m1K32P56 [58084200113134404, 20301898851027378, 30765]]⟩
private def m1K32Bkt5 : M1L50BktRec := ⟨5, 5, 4904329, 164145755378, [
  m1K32P56 [
    43540927747901635, 34512826479204923, 14983597013547929, 48560430207763828,
    27298948051958844, 6032594698595237, 40168],
  m1K32P56 [
    62351232389186586, 1464217668759441, 63184679595913918, 50315509232181662,
    59306839862521961, 25808260153179257, 45765],
  m1K32P56 [
    34086993764113330, 1985140210931833, 33410623728431817, 34074739613437643,
    57617152484356733, 15840082124094386, 30852]]⟩
private def m1K32Bkt6 : M1L50BktRec := ⟨6, 6, 5583123, 176099837052, [
  m1K32P56 [
    43526380693670276, 61426672106311995, 6539451996715929, 48869864743072588,
    63142494679786003, 12346037579794087, 41307],
  m1K32P56 [
    44823226300967903, 68646469258608537, 30275649468141450, 50305506458384535,
    38577385423572340, 39872357825618554, 45756],
  m1K32P56 [
    17714087857155715, 37140071497068410, 66562152993764032, 50318575503273196,
    40481143505844820, 31748920355949945, 45768],
  m1K32P56 [9386469341294796, 29091398898225273, 33410638228992716, 33936802594722135]]⟩
private def m1K32Bkt7 : M1L50BktRec := ⟨7, 7, 10457444, 111275972299, [
  m1K32P56 [
    43528218939672933, 44687707085022267, 60864130184395674, 16735480313518648,
    28280288100776130, 43858048168218030, 43413],
  m1K32P56 [
    19179282295432049, 57676661537957284, 33098674740567610, 39895623596970430,
    35186728108874683, 25254349668251058, 32110],
  m1K32P56 [
    38536067886767283, 42016404633326770, 24344255134858488, 50266164776047823,
    33896669967313676, 51568962054855548, 45728],
  m1K32P56 [
    66019215696104152, 44956499325200507, 1542929976898220, 50305444362275170,
    38860575034870020, 32398735926359418, 45764],
  m1K32P56 [40681916047061789, 522115887993]]⟩
private def m1K32Bkt8 : M1L50BktRec := ⟨8, 8, 5554557, 242131972679, [
  m1K32P56 [
    43561152748898791, 54510743969718331, 60019705891797914, 16777129668352704,
    69487250384342850, 5553285186342062, 43732],
  m1K32P56 [
    23843762917872573, 12346030942439846, 59287158059409755, 43828336658199971,
    836739438672127, 27004608087846293, 35912],
  m1K32P56 [
    52026204575290759, 50604449369117618, 32003191925865092, 34425752480037830,
    53681853391833732, 21757903794299058, 31251],
  m1K32P56 [
    54509772758797722, 29999843005455538, 27718496654555603, 50318708952974489,
    39614443915361527, 38977355544950649, 45767],
  m1K32P56 [
    17029177995460561, 34791514827364473, 46013313087091402, 50328412924468557,
    27363849527979207, 517027092088]]⟩
private def m1K32Bkt9 : M1L50BktRec := ⟨9, 9, 14669640, 104269126364, [
  m1K32P56 [
    43507319628810392, 36697556084450875, 51856930445081498, 16776073844595183,
    39241304707268974, 50616771143782459, 44903],
  m1K32P56 [
    55891138154238126, 23580847392408491, 61541464573192160, 44739242649428686,
    44823226260527788, 46135068191522713, 37710],
  m1K32P56 [
    5584782806131690, 34120642166478731, 32565526424367660, 36006805620386807,
    17636972658862020, 19823642430899122, 32621],
  m1K32P56 [
    22756457712769060, 13598205328141490, 63809483181686502, 35559156432921354,
    33001156432421310, 48082409953870002, 32182],
  m1K32P56 [
    38126929306889785, 34103219423837106, 67409990525680903, 50271510164838827,
    18123033201893692, 64604772101354876, 45739],
  m1K32P56 [23626153307926271, 9241063413829755, 9985899539641022, 8003435]]⟩
private def m1K32Bkt10 : M1L50BktRec := ⟨10, 10, 16275217, 105311114633, [
  m1K32P56 [
    43491058882628042, 32292912502986299, 13857808394238874, 16776796523174505,
    43220424403296087, 24243387650089275, 44993],
  m1K32P56 [
    37563945833289252, 71839532197361836, 17074401954277651, 46550007673086204,
    25662462365477852, 6032594698595233, 40168],
  m1K32P56 [
    61688373007034684, 37187209249692311, 51943192017605085, 50109930707488468,
    62495363441277257, 60679301683646080, 45594],
  m1K32P56 [
    27074514749413653, 70361598966483840, 16521463501271598, 35988107882912502,
    18893486816435870, 68490225557223858, 32588],
  m1K32P56 [
    24565476463428994, 10142439442404018, 7514523881995956, 35480947595045743,
    35916670422597586, 32176874920235186, 32085],
  m1K32P56 [
    41596335162750242, 71482216928497586, 37291603299695747, 50287227698325495,
    39184788305425756, 11724860147999355, 45756],
  m1K32P56 [19858985935342916, 122]]⟩
private def m1K32Bkt11 : M1L50BktRec := ⟨11, 11, 18446661, 102961652771, [
  m1K32P56 [
    43455079941589482, 26334658989959995, 30183356603841434, 16776688712784466,
    43346481693465536, 46218227250132027, 15242],
  m1K32P56 [
    2888690582569788, 48435330275872944, 14542185100782879, 46938020437953105,
    16590327590805893, 3718149882041251, 40805],
  m1K32P56 [
    10970242501381432, 15910599627727771, 42668018543203926, 40708260970405874,
    13025581548324527, 35362157117473929, 45517],
  m1K32P56 [
    10257066986070033, 69474505763078786, 1831389114511844, 50098633399444368,
    7826060464648992, 67812934161138817, 45587],
  m1K32P56 [
    39435701209789067, 32605469917105280, 40165346410476075, 36014391304385245,
    18853023929530833, 72013060830216370, 32589],
  m1K32P56 [
    25477315200451291, 29128805799066802, 25810425827655322, 35416841684939279,
    38735929901543836, 18297739810855346, 31985],
  m1K32P56 [
    45370632156824401, 39544702901449650, 46298117741706212, 50305704983181509,
    37666311190728919, 122]]⟩
private def m1K32Bkt12 : M1L50BktRec := ⟨12, 12, 18486217, 112773292305, [
  m1K32P56 [
    43409385784527329, 15733167872318267, 23709431586765722, 16776511646046768,
    43313534999335333, 41318803428396603, 15255],
  m1K32P56 [
    19916150897025678, 63631694023992752, 52545243577560478, 48083927292367891,
    63142507468313539, 48336338191890087, 42171],
  m1K32P56 [
    25662462365477852, 6063384362846113, 35916231269457327, 41943039993290558,
    39111696979261698, 29622559275476111, 34922],
  m1K32P56 [
    57525102034184512, 22220794123905713, 8305892831035946, 50069550820090363,
    50732624027856478, 43968035334785665, 45559],
  m1K32P56 [
    15881455493734245, 17257599724130433, 50807015045902861, 50140889938441742,
    12382857559466253, 37825949513230720, 45624],
  m1K32P56 [
    43017025332217710, 13422286465604735, 25247321817330254, 35741288342944381,
    28108038504438676, 5617947381828018, 32334],
  m1K32P56 [
    34210658752498194, 5328772619291058, 25247601169825167, 35102960961883963,
    46424505458226954, 4390017689382322, 31668],
  m1K32P56 [52535900306149557, 34491347887269298, 134567682800227]]⟩
private def m1K32Bkt13 : M1L50BktRec := ⟨13, 13, 16892980, 134051480514, [
  m1K32P56 [
    43164078727414966, 19555070275347003, 48197750404561817, 16775217300609321,
    43038193235848937, 69991867654578491, 15255],
  m1K32P56 [
    51805973831993057, 53934002322512186, 28620328999759993, 48269023823923615,
    57887593567382501, 40140596000094376, 42487],
  m1K32P56 [
    68248716745084574, 63696507961334690, 29167517545963443, 43959219696446637,
    19599510284378531, 47797504949472408, 37847],
  m1K32P56 [
    42381021682241869, 43580825880154510, 47764946141677501, 36375140341249833,
    2203054103006226, 18533033121776306, 32983],
  m1K32P56 [
    6897655214460186, 10933209030389170, 46021636250632303, 50147840205400368,
    593618167534432, 63743852583939968, 45625],
  m1K32P56 [
    40334392204149929, 41822889541092735, 11117255485272650, 50202909148648902,
    41721783457105989, 71233503970113150, 45675],
  m1K32P56 [
    2509105707875719, 50675932728259966, 13425572576932476, 35308909706965313,
    39807542306368651, 23458616532088754, 31945],
  m1K32P56 [
    44515608147928727, 35647799236050354, 17084962791455754, 34665272353926882,
    53936897154081392, 16717742507775666, 31232],
  2046835625]⟩
private def m1K32Bkt14 : M1L50BktRec := ⟨14, 14, 12089032, 203005179708, [
  m1K32P56 [
    43477972117276501, 30141168246528059, 24272382385601434, 16776712452545124,
    43278844548491424, 4613806772646715, 15257],
  m1K32P56 [
    42899890993918822, 22709568654715195, 54800369551782053, 49087115823047800,
    3110031655111819, 43858048168218028, 43413],
  m1K32P56 [
    72008870435738540, 9979873051505062, 62946332756452420, 44537698020580139,
    59798999820586216, 53606254889853594, 38673],
  m1K32P56 [
    57709382146834037, 61845960544117650, 15918440975666620, 38038331611095977,
    27304037806309457, 53735875145256626, 32357],
  m1K32P56 [
    29540513177203316, 8335939404922290, 25528945851072035, 35428264888660197,
    34014249015432540, 39554597829222322, 32149],
  m1K32P56 [
    36251957036683192, 62848851308658610, 35885078321069385, 50252898611923134,
    70446047095833587, 50261642460684668, 45712],
  m1K32P56 [
    46742401756564991, 46936719431736444, 40669063997993624, 50279134248324186,
    66405050706074443, 40565914234280571, 45736],
  m1K32P56 [
    36873942206025777, 37547753055823483, 54239666751320752, 34637800934149860,
    51926694477986566, 2641553248545714, 31371],
  m1K32P56 [
    54167456226242816, 39262984409398450, 24121946817133038, 34096397744785511, 2032303710]]⟩
private def m1K32Bkt15 : M1L50BktRec := ⟨15, 15, 12805772, 206258737484, [
  m1K32P56 [
    43450686190045369, 20028959804321083, 34968430911372186, 16776569560996417,
    43329005471540027, 61299128744833595, 15257],
  m1K32P56 [
    42601438011569196, 8214707306207547, 2727660581436281, 49173170089937656,
    37563945815555290, 30581457876695212, 43584],
  m1K32P56 [
    63142494623263912, 70998385851877031, 46906682101441888, 45806778245627141,
    66798379202334914, 6032594698595231, 40168],
  m1K32P56 [
    44823239056113276, 13182689103237785, 8323154914743805, 39680605085097348,
    43172773106371797, 30454851165055878, 45651],
  m1K32P56 [
    59179292211506407, 53453302477928574, 54520777613357659, 35624763866910851,
    28165668375629823, 26618619443686322, 32332],
  m1K32P56 [
    30508061935035000, 35308058648873394, 50861710136016389, 35390570745722037,
    35193788766588108, 8031599531188402, 32110],
  m1K32P56 [
    37537530940104578, 47806432805679282, 13648360986803484, 50258334597680560,
    55875928886509753, 1332275602297724, 45718],
  m1K32P56 [
    30039858054084439, 25180682948532348, 70505118190449310, 50285814247852045,
    44106091606748820, 1135226909839739, 45743],
  m1K32P56 [
    10664260764894229, 25318983169464699, 26092198415807159, 34514725961899765,
    53955529654906944, 59175140261492146, 31230],
  m1K32P56 [56302626203502319, 627242090766514, 31022]]⟩
private def m1K32Bkt16 : M1L50BktRec := ⟨16, 16, 9886992, 285866432700, [
  m1K32P56 [
    43528760105552380, 46493105178094907, 12731909334186906, 16777057828313765,
    43528755810575660, 46450224224607035, 15258],
  m1K32P56 [
    43526659866534985, 34264336853773883, 21176101926353818, 49798901576821718,
    69487265205116489, 47899867307714990, 44271],
  m1K32P56 [
    59694400398431162, 35861296003900586, 56759353076000929, 46137343994123445,
    25662449523469186, 22943102644510625, 40610],
  m1K32P56 [
    51127095784526213, 36065749670024603, 71943826799106183, 41943040043320056,
    1358857071023068, 27004608087846289, 35912],
  m1K32P56 [
    7958825757591167, 61150105928531846, 13366864892375685, 50254830001526724,
    65324067565764770, 11245241886976124, 45711],
  m1K32P56 [
    51444107654932516, 58435180612169596, 63809692652384915, 35047649295762340,
    42915612570711905, 36387771702552242, 31822],
  m1K32P56 [
    44226088697405254, 5566260822825650, 28062430597315607, 34864463558648263,
    46847353564236991, 1289394924257458, 31648],
  m1K32P56 [
    48158250593420714, 34265947742649778, 3231874753461087, 50295785437441984,
    7526189222247492, 29435793318119803, 45748],
  m1K32P56 [
    58789656142076997, 4835320236418682, 60651812321342137, 50311151903998080,
    11143188274067942, 27790681042256250, 45762],
  m1K32P56 [
    54785390351114942, 3293560281709433, 19336866381017799, 34140774181980890,
    57338207243318474, 50364747948938162, 30894]]⟩
private def m1K32Bkt17 : M1L50BktRec := ⟨17, 17, 1713823, 68000000000, [
  844461612,
  m1K32P56 [0, 0, 0, 49830722256502784, 14274906598983462, 50695935091996335, 44364],
  m1K32P56 [
    23925955748475934, 37842627558673067, 13978407112321353, 47050018991318974,
    66578721773750523, 70471697026407076, 41619],
  m1K32P56 [
    7042812748563811, 70216588333773472, 22406529345690996, 42653154853691046,
    8775827613864322, 39750180545598612, 36927],
  m1K32P56 [
    47090646623685947, 27242099897054347, 24916764765423018, 50329184193662496,
    16627877709288175, 18603405194958456, 45774],
  m1K32P56 [
    14430538080404575, 28100986637898872, 37849773869150926, 50329618954595126,
    9818912418858388, 47095897533863544, 45774],
  m1K32P56 [
    7389348203767634, 56594578341415288, 8922325484417742, 33795999020880200,
    58242022981429966, 67000356079259058, 30727],
  m1K32P56 [
    58279127203908749, 10139112084597682, 21588701134682110, 33763636681035566,
    58353326071470474, 69710904694934450, 30696],
  m1K32P56 [
    58390430293227474, 27522643539380914, 38130914568337373, 50330778415058835,
    58810194625359689, 51025804099143287, 45775],
  m1K32P56 [
    55000111956321832, 60524485053711735, 23494039878677199, 50331213192737901,
    46002238066260164, 7461799749169527, 45776],
  m1K32P56 [40328139591654019, 16960480363317879, 57336027706208976, 33624169408591104]]⟩
private def m1K32Bkt18 : M1L50BktRec := ⟨18, 18, 14702973, 38000000000, [
  m1K32P56 [35122126127687281, 56359019596404795, 61123866050508538, 4900860053089, 442],
  m1K32P56 [0, 0, 0, 0, 9698404198413474, 50616771143782577, 44903],
  m1K32P56 [
    44721620465410576, 40727747975229101, 12290190888971206, 47252971480276238,
    57961952275616710, 58220952326773157, 41890],
  m1K32P56 [
    25662449518825178, 7504859878907809, 61817782566428402, 44016864398696730,
    44823239056113276, 47998727522780057, 38559],
  m1K32P56 [
    22135276072510439, 68649724503384467, 24641240307109770, 37508859720045527,
    12308674131401718, 71917621787486386, 32752],
  m1K32P56 [
    14878885551343568, 32528717387226546, 23221352638021554, 50170712550424062,
    32095107330211677, 9484053487081343, 45639],
  m1K32P56 [
    13364523019760809, 19298294429897087, 4643145755112016, 50200845886614179,
    45943719129081830, 39170645644191358, 45666],
  m1K32P56 [
    25047732572031924, 49405998141621886, 16521724232970859, 35478552308485002,
    32884995621442649, 32352570134463666, 32186],
  m1K32P56 [
    35459188565866914, 8938468589490610, 45232289690582373, 35196299426039583,
    40608917881543551, 49277579546708146, 31914],
  m1K32P56 [
    43184712841867537, 22034980098828210, 28847076169186371, 50281300240802451,
    59342199406645808, 52653080704647035, 45739],
  m1K32P56 [
    24299419496502100, 63920876019715451, 5201552993465012, 50311502765934831,
    9319820038114199, 14793353981638010, 45767],
  m1K32P56 [19779044657018000, 520869975417]]⟩
private def m1K32Bkt19 : M1L50BktRec := ⟨19, 19, 3132064, 44000000000, [
  m1K32P56 [663199630067485, 98956047340800, 393216],
  m1K32P56 [0, 0, 0, 0, 16154630425673728, 68281532768620721, 44950],
  m1K32P56 [
    65303116665778840, 26515469825530285, 54795447746079787, 47955911631331237,
    36927723616285070, 2454825401365928, 42644],
  m1K32P56 [
    40469280567838357, 33667743764421028, 46056598172377715, 44440927273499493,
    27953784409999798, 19982092197680283, 39092],
  m1K32P56 [
    56624812737709824, 56975136853326485, 25493889883148942, 40221021676954830,
    39458021491617497, 13290367775356042, 34018],
  m1K32P56 [
    56543681243046444, 29936923106230194, 478052526029075, 34065810782865735,
    56765395075771594, 41387485068776626, 30969],
  m1K32P56 [
    56876252475790107, 5956822381930674, 34472902524106988, 50325151806573173,
    62533205439162742, 61450273760628344, 45770],
  m1K32P56 [
    58481857277183172, 17773273865462648, 66842339164402379, 50326450946490585,
    49918818743198713, 2476618557231480, 45772],
  m1K32P56 [
    45368846353959117, 30858311933812088, 47765862146552524, 33935618106495043,
    57652311086649974, 34377848072040882, 30846],
  m1K32P56 [
    57763177077487436, 48233893289739186, 10048220342417515, 33873362894900636,
    57984908078327018, 9319129005750706, 30786],
  m1K32P56 [
    58095782657663318, 52804813890899890, 46294021112559658, 50329915613171402,
    4743849227377248, 13366431327419000, 45775],
  m1K32P56 [
    68533150182242871, 41749224493437303, 71344907057279695, 50331214887243937,
    45941898070718761, 513839486839]]⟩
private def m1K32Bkt20 : M1L50BktRec := ⟨20, 20, 2428465, 48000000000, [
  844652632,
  m1K32P56 [0, 0, 0, 0, 0, 436168122534144, 45390],
  m1K32P56 [
    54419386072651297, 35060875295231151, 15952287876099625, 48083927242147188,
    5628647701746621, 43749194342546601, 42819],
  m1K32P56 [
    27298935198686064, 57570039615471525, 62104169674875753, 45417715244030763,
    13928800655080488, 6032594698595231, 40168],
  m1K32P56 [
    34002038903327913, 11610395494661274, 726789953394651, 41057431074439929,
    21189915091764253, 59872317815660686, 35342],
  m1K32P56 [
    38716057293083832, 62547387701006212, 42699310159606475, 33961821047662616,
    57447067484428236, 51628086541111986, 30878],
  m1K32P56 [
    57510383892320610, 6220455175648178, 70565335752341653, 33930031431601290,
    57637015730728727, 71045711768359090, 30848],
  m1K32P56 [
    57700332137938051, 33431418985916338, 53049745819138166, 50328185144003895,
    30282566588929461, 31899799295972216, 45773],
  m1K32P56 [
    27108774735007547, 48108799716419960, 42635026195788493, 50328927146103959,
    20371393662018689, 8470054679074168, 45774],
  m1K32P56 [
    16772176708247064, 24680154392843896, 35380971392971470, 33827731984100900,
    58143578036015429, 66909097016792498, 30751],
  m1K32P56 [
    58206898738875100, 57219100787286706, 32847699501086736, 33777583379369732,
    58333534863001773, 61302939276151730, 30702],
  m1K32P56 [
    58396859859655187, 21027828354491314, 16175857408374747, 50330905955454897,
    55476445304395601, 66095710472949879, 45775],
  m1K32P56 [48064220808004013, 10249315878725751, 70500172050379472, 7833711]]⟩
private def m1K32Bkt21 : M1L50BktRec := ⟨21, 21, 2696763, 50000000000, [
  m1K32P56 [297195401762331, 410117837877504, 524288],
  m1K32P56 [0, 0, 0, 0, 0, 45501089692254208, 45408],
  m1K32P56 [
    65184420979581354, 33991057965639087, 31998418914487908, 48649487361300083,
    17040826785630855, 43858048168218027, 43413],
  m1K32P56 [
    63142507468313539, 9309178860474279, 32831709857818139, 45696889460638755,
    24528552361268274, 57673372068518304, 40506],
  m1K32P56 [
    71918877838855400, 17588458004535707, 32257056572414367, 42522231197602238,
    21140132166572755, 4299714192163732, 37177],
  m1K32P56 [
    53158894204935096, 39104722045168269, 46307269308156314, 50325547729041233,
    58834359100821932, 5995056297516408, 45771],
  m1K32P56 [
    56043974683202894, 25032000454515064, 38195708296147659, 33984743170686193,
    57311569856142480, 36575772688901042, 30898],
  m1K32P56 [
    57385932919922737, 56037128320509618, 60150759883503783, 33949319072762915,
    57534649481345531, 23302717860968370, 30865],
  m1K32P56 [
    57609012544361207, 38472679793826226, 52486860590643333, 50327871577836782,
    34147229702377641, 14176771363724408, 45773],
  m1K32P56 [
    30572910673173960, 33214815203098232, 37849997912486605, 50328743016161120,
    22945599490734498, 71288452662231672, 45773],
  m1K32P56 [
    18844687407119685, 18267802703178616, 48891769892877006, 33833673047946123,
    58129576442627209, 10444776937943986, 30755],
  m1K32P56 [
    58203943801374764, 37723660127429042, 58743397481936913, 33775194605801227,
    58352673237130355, 11846906259927986, 30697],
  m1K32P56 [
    58427040594471499, 7588497729984178, 52204610680879057, 50331067016728534,
    50824944182137079, 7421371971427447, 45776],
  m1K32P56 [40356231978639217, 119]]⟩
private def m1K32Bkt22 : M1L50BktRec := ⟨22, 22, 2037070, 64000000000, [
  m1K32P56 [139548627103837, 4398046725888],
  0,
  m1K32P56 [
    31959670670330659, 18928848758586545, 52827796585099274, 48729994845657569,
    43573025943038995, 22852986708259499, 43530],
  m1K32P56 [
    30711312531738931, 63475529656551848, 18479225128724161, 46451180559468314,
    16590340416532688, 12349308110888099, 41307],
  m1K32P56 [
    28443509491305781, 9543337155617951, 28036614389275989, 43018058127320825,
    24268998737965612, 66319888544205206, 37791],
  m1K32P56 [
    45021254127709088, 18691219319331472, 49413393696329016, 38612952987283014,
    66079886538359627, 14511022898646147, 45773],
  m1K32P56 [
    30508851235939211, 24879417550987896, 41509197810479821, 50328483573294398,
    26437927593409850, 45615955873445496, 45773],
  m1K32P56 [
    24326074994106896, 55985449909131128, 32847694173549261, 33863551558373048,
    57961570206870460, 57713881925869490, 30790],
  m1K32P56 [
    58002076043448467, 46380115929904562, 30032946260441150, 33836620724751925,
    58083078143621730, 37869047938433458, 30765],
  m1K32P56 [
    58123583979620006, 36532041801472178, 66841667672504356, 50329749334183587,
    7637836846801503, 56512367106245752, 45774],
  m1K32P56 [
    4887129336405169, 66881861270215544, 36160769057075918, 50330223974549282,
    71039062723465842, 15560803891670391, 45775],
  m1K32P56 [
    67838929835865929, 25930297862479479, 19055427113235151, 33747209199019240,
    58407121524326646, 65024532878385842, 30679],
  m1K32P56 [
    58447627360904653, 54734203316755890, 46639976685008841, 33700158675013578,
    58528633747807663, 25900863896648882, 30632],
  m1K32P56 [
    58569135288245258, 21399463294948018, 11390473598498707, 50331489785794617,
    33735067443910906, 119]]⟩
private def m1K32Bkt23 : M1L50BktRec := ⟨23, 23, 2037134, 64000000000, [
  m1K32P56 [142950241228572, 123145302428928, 327680],
  0,
  m1K32P56 [
    36301321283829760, 61674568598151089, 65214413436596265, 49199266629864056,
    27637657897152586, 21069580282288045, 44016],
  m1K32P56 [
    32642763626641512, 20752907981404074, 33679519323039980, 46643839706290217,
    1486001335063355, 16727574856566180, 41539],
  m1K32P56 [
    30964625277401968, 66701462427806880, 20721958458728066, 44049306132184732,
    26098637651884175, 36423075411092378, 38935],
  m1K32P56 [
    47024465563291773, 1819223592956821, 62645847231009536, 39613650370040046,
    56618559064532921, 18416307743902344, 33699],
  m1K32P56 [
    57758992988062064, 28723310199275698, 53049702586873964, 50328318287990102,
    28588786105815365, 34334118040435064, 45773],
  m1K32P56 [
    26621746918364228, 44252812436911736, 13643115753485005, 50328772309178220,
    22541687881318516, 64088850499477624, 45773],
  m1K32P56 [
    20421047778927537, 1949950729318008, 53676843524338382, 33848250116620493,
    58030212374211114, 59544568551663282, 30776],
  m1K32P56 [
    58068957274197351, 42878171159734194, 46639970880092208, 33821069554142832,
    58146446090179998, 18945353316557746, 30751],
  m1K32P56 [
    58185190989579093, 6908999529603250, 26027734155229206, 50329983124688602,
    3529348439902660, 71383261875378552, 45774],
  m1K32P56 [
    713829872994555, 9245461745555320, 45730853339902671, 50330437162629124,
    66680946523325461, 29081498118659447, 45775],
  m1K32P56 [
    63348468513466194, 39001291825831799, 56773074771555023, 33728991726130262,
    58456419158961612, 36583465310862258, 30662],
  m1K32P56 [
    58495168353915145, 15019843010225586, 20462804549466039, 33677865294942196,
    58572652866295628, 17285090784019890, 30609],
  m1K32P56 [58611402059890182, 28316490947806130, 131350384768886]]⟩
private def m1K32Bkt24 : M1L50BktRec := ⟨24, 24, 2036942, 64000000000, [
  m1K32P56 [143731925197071, 130841883842048, 196608],
  0,
  m1K32P56 [
    0, 6742967911444736, 46637189100122511, 49248080527115969, 44721607603052108,
    13344418809648045, 44094],
  m1K32P56 [
    59694387537260395, 54960921928514986, 55073849221687647, 47252971530477651,
    23843775727318470, 48336338191890086, 42171],
  m1K32P56 [
    5557114891386407, 12349308110888099, 54781585563558235, 44384078348128211,
    51127095768585610, 17588456765248923, 39327],
  m1K32P56 [
    28785332956642943, 70086819945127575, 2134164837143810, 41212148412738107,
    39111709772411873, 27004608087846287, 35912],
  m1K32P56 [
    29952073418828093, 19126569020944520, 47202915515269984, 33896150531755315,
    57796281705979558, 59554715755965106, 30821],
  m1K32P56 [
    57833407402857414, 10070095438491314, 67686344429566047, 50328602628246936,
    24854221846760598, 52554125228553336, 45773],
  m1K32P56 [
    22882234856983339, 62057204229633912, 38131381553902285, 50329037657623068,
    18784471965630012, 9006616258838648, 45774],
  m1K32P56 [
    16650135212531712, 18509695130484600, 3292823680168654, 33833451236373336,
    58093279674000262, 20673533747746994, 30763],
  m1K32P56 [
    58130405371315530, 68868426788283826, 4137250309634082, 33805937998483111,
    58204647191106177, 25096021365805746, 30737],
  m1K32P56 [
    58241772887824715, 71527297897371314, 24901773675100167, 50330197805944588,
    71551563004261241, 12980502745980023, 45775],
  m1K32P56 [
    68653791518648323, 22484681258688631, 55582413116650191, 50330632852072709,
    62327786715443621, 41491685601898871, 45775],
  m1K32P56 [
    58823140646556521, 50995863903499127, 11174129259360975, 33710413324993393,
    58501653754533616, 33549912427144626, 30644],
  m1K32P56 [
    58538779451848884, 33588395048914866, 33973604072257443, 33653083904069658,
    58613021262433753, 1608253997595826, 30581],
  2004158116]⟩
private def m1K32Bkt25 : M1L50BktRec := ⟨25, 25, 71943238, 65831429697, [
  m1K32P56 [
    39844455554605237, 40059853834441273, 10477854279219597, 16196297735900487,
    36714798750780754, 24735959724894265, 14697],
  m1K32P56 [
    13101940432447078, 57361767158554937, 38061670346012940, 15967799268139689,
    45170094692906505, 61576192645168440, 14456],
  m1K32P56 [
    39977328890579397, 5550520860821047, 26935406691594652, 49646572307243339,
    8892101364258638, 35259885507396015, 44502],
  m1K32P56 [
    37563958663935029, 63559104330845100, 3282905883781931, 47389278726637847,
    64347817033616455, 70998381628752550, 42336],
  m1K32P56 [
    58605982579751999, 61060982309771171, 27762878399488560, 45178028252234029,
    53793746491219229, 6032594698595230, 40168],
  m1K32P56 [
    70045498949032447, 18210768394694554, 15928349087340781, 41773555684655045,
    62351219546969054, 6754926416108945, 36621],
  m1K32P56 [
    61749331330144258, 29932605723947915, 71925727441356817, 36909875242148181,
    3883391921978883, 18826518729117348, 40575],
  m1K32P56 [
    44581260782836830, 17557679499234724, 38180726994542039, 44231537702809477,
    53307057950525672, 1590605724849829, 40049],
  m1K32P56 [
    22529829101751433, 20023920617910438, 61532775232871351, 46977978380772150,
    70568995332731728, 39680994389199002, 42873],
  m1K32P56 [
    14207762991862421, 30657304946511258, 731583755888653, 47463531881783918,
    37994413105993900, 5254121707335576, 43317],
  m1K32P56 [
    46650357060128807, 60173624218932375, 35089592147749322, 42429022706514580,
    27692276945854023, 51175212939990186, 38342],
  m1K32P56 [
    70083084476214381, 39283990358629290, 63239026533766340, 41574250899542049,
    11006899851177390, 46770665513221292, 37525],
  m1K32P56 [
    53897379553151618, 1621422095957676, 53640122318164327, 48792853034129506,
    10767764602307593, 11996418945388944, 44530],
  m1K32P56 [
    58009905164797940, 2593398087655054, 16199495567519372, 49300192956865441,
    56510871926895399, 20393242537588363, 44993],
  m1K32P56 [
    4114109171853428, 60028430275429258, 193913094713436, 38316348568772673,
    70075383700580955, 18709864999545776, 34281],
  m1K32P56 [
    42094436281583616, 16571303475824305, 42698652228354881, 35960124194566831, 2143392429]]⟩
private def m1K32Bkt26 : M1L50BktRec := ⟨26, 26, 67016781, 72815847676, [
  m1K32P56 [
    8697906774790577, 64936306851361594, 37500076286229022, 16357304349368035,
    6285281885369746, 25153776888907066, 14846],
  m1K32P56 [
    67918084055985074, 7040421383482425, 56077029745703382, 16233151893974225,
    38490522915017180, 38597503209698361, 14716],
  m1K32P56 [
    65870492748561185, 11518728026549048, 19617108728098493, 49673459725346829,
    19443929795116956, 44863026214742447, 44553],
  m1K32P56 [
    55988685489413989, 30367054207478956, 30869323335969660, 47896442088073615,
    57887606407276661, 68458511972119464, 42855],
  m1K32P56 [
    69681131287973531, 33178469814099109, 61822182176105595, 45417715193803383,
    50632835288738783, 40376951912943263, 40442],
  m1K32P56 [
    12575559518949237, 4491076252297884, 46050051205077575, 42860757047068065,
    9844595842283928, 47797504949472406, 37847],
  m1K32P56 [
    25051219531202544, 40902444964728209, 11412332540694166, 38207594494129339,
    64759751094672084, 21505910133401986, 42474],
  m1K32P56 [
    15979123665927386, 54736558899371420, 16508514692867684, 43805514393164941,
    63781323707225169, 39950321128624294, 39679],
  m1K32P56 [
    26310212253827613, 11870990391954087, 45783485067270745, 43252566161086650,
    23136098048633208, 57963677451395496, 39160],
  m1K32P56 [
    58112164211979737, 39151035580804264, 57588314940676161, 47653690670664467,
    37833982905402992, 40031748550006935, 43465],
  m1K32P56 [
    54442982203393558, 51267659977212054, 70252139026557510, 48065279281198313,
    8536014142586673, 13715948536465557, 43841],
  m1K32P56 [
    18307674634594648, 45277426095763860, 8351617402514367, 41477540028832271,
    17769055687437939, 54084506275301804, 37481],
  m1K32P56 [
    53531032166439336, 3546549562719660, 39315499848470892, 40638009265962396,
    53209257035764624, 15313644647344557, 36678],
  m1K32P56 [
    17256296235865421, 10578050217167790, 51384696143318555, 49185749377924593,
    62105779219204879, 9032141185961100, 44863],
  m1K32P56 [
    37624306695745420, 32511114656049803, 43217479142977472, 49612241943269852,
    34238653312149490, 13476200671060872, 45252],
  m1K32P56 [
    50235478057958764, 48561609075539078, 56771387543695686, 37340900191676729,
    56729898123364435, 36492250723684273, 33337],
  m1K32P56 [21607841723630446, 22011668825916338, 32517]]⟩
private def m1K32Bkt27 : M1L50BktRec := ⟨27, 27, 62957494, 80016262951, [
  m1K32P56 [
    35715256816393953, 63848891461850682, 1190216552823422, 16465044124106464,
    34773602397996787, 38242365097028154, 14967],
  m1K32P56 [
    30135492983721285, 32370972623366458, 35529967714384466, 16381240017568537,
    8443996874603516, 65304643116090938, 14867],
  m1K32P56 [
    2808140786446482, 23203241491319354, 38616117603285401, 50018027553534753,
    40632257598216911, 50616771143782576, 44903],
  m1K32P56 [
    15988551258262909, 17547849151435950, 50009940197027075, 47993960461485712,
    15122526875304119, 23577554585247401, 42976],
  m1K32P56 [
    36396371726586822, 57603029801521574, 60698641629226263, 46059430518956750,
    9334293799184762, 34512160608131490, 41105],
  m1K32P56 [
    68146273067342505, 2186504516911518, 3830130636660033, 43240762164083656,
    47121961387507327, 70127502968303511, 38286],
  m1K32P56 [
    22135263225379111, 65963633764723347, 23240222294446299, 40011985484392112,
    5584795552962388, 35633554507339147, 34670],
  m1K32P56 [
    49014216219042344, 11324589149088386, 10021276564891492, 47228906710388730,
    52539027782166034, 49171919825374873, 43059],
  m1K32P56 [
    10397719213763128, 13326738732463769, 12007350758582429, 42940210385292006,
    2468780102316749, 4267857131651753, 38895],
  m1K32P56 [
    32259948879608101, 27646770130579369, 25519507082221387, 42397388579134649,
    19649254568136591, 5941392662372778, 38386],
  m1K32P56 [
    49713840945119106, 5898513498378154, 23245050462115134, 48163787410971569,
    37594933565309811, 66230919115540628, 43911],
  m1K32P56 [
    55242988531655134, 29015750855438739, 52515948626291699, 48517592974031766,
    11701692829477108, 44824418314288274, 44234],
  m1K32P56 [
    22580707558371561, 1078145530986641, 4131103538457911, 40653560636009771,
    46182828469365820, 16681307221583533, 36736],
  m1K32P56 [
    4764405846808721, 13486122238265262, 30872627726421638, 39826287156428301,
    66214095837099529, 34834379154110126, 35942],
  m1K32P56 [
    25040314526272157, 63777925083697583, 71366264700177212, 49477003173152498,
    71483389290321635, 21108081525282697, 45109],
  m1K32P56 [
    46221057352526786, 56736658166001288, 57850981100794019, 49841431615318369,
    36886002447584827, 41574207589618309, 45441],
  m1K32P56 [
    45121005244487935, 65180714137955203, 20461846597186032, 36415191981842271,
    27163291727986765, 61777703259788722, 32361]]⟩
private def m1K32Bkt28 : M1L50BktRec := ⟨28, 28, 59579260, 87335485786, [
  m1K32P56 [
    54756917013804123, 38597508553318458, 9071806453398210, 16539373365019273,
    54616883885930738, 36324817974890298, 15039],
  m1K32P56 [
    51636133632534147, 51957674139355962, 63396366503590578, 16501513245075568,
    42604968457796437, 25403368110880058, 14986],
  m1K32P56 [
    37837322829953039, 21008620032745786, 3160221408442948, 50029331043507298,
    46532082393770332, 56098941448532400, 44935],
  m1K32P56 [
    28280275234965328, 2171184963175854, 39315490807065915, 48425844555385612,
    59694400398431162, 43858048168218026, 43413],
  m1K32P56 [
    22257317920576230, 59584351877442728, 35085034351863551, 46236815201773345,
    60198526369670004, 12346015929483426, 41307],
  m1K32P56 [
    59304043546880991, 57673369846331807, 54498645888245306, 44070108672070023,
    59799012648448735, 35914005436404890, 39168],
  m1K32P56 [
    4994486859054706, 70090108224208791, 28027431967298818, 40644099729181958,
    53158881364645865, 13636751966583693, 35512],
  m1K32P56 [
    10037684495462517, 15722497184447367, 45742403367109241, 47441965862128168,
    47855249727617815, 23159738819676312, 43239],
  m1K32P56 [
    9528786930303591, 45455637142392216, 58150504920099138, 47741432657057317,
    1191070291338510, 31995337509302935, 43512],
  m1K32P56 [
    31814573664886007, 36280131850180246, 24957083375086164, 42181432337357222,
    50078084584489527, 59201645562020778, 38207],
  m1K32P56 [
    4009492279539124, 10735170316608683, 54513141646333087, 41649258476825287,
    55929320014181537, 61483228988780459, 37708],
  m1K32P56 [
    10060271872533231, 10327352554218668, 37034427276497564, 48556206711406842,
    64868594326253936, 69552549504072337, 44254],
  m1K32P56 [
    11433647758867066, 37602942195038353, 49416873193876796, 48864357476492138,
    42004387930458199, 64958664156645775, 44535],
  m1K32P56 [
    53804849237081943, 9137554732695438, 65493880775618134, 39934121535725354,
    50887703167012074, 48727662198324142, 36084],
  m1K32P56 [
    5451209789090866, 63855838529150639, 61554449056697340, 39114246456308261,
    58832107869741973, 12926613824085423, 35295],
  m1K32P56 [
    13576355281078991, 10150348560966320, 59823003600455860, 49697613849595814,
    31800885024702496, 22650699460717447, 45295],
  m1K32P56 [
    4209272062658657, 8387836232774790, 4086355166015823, 50013603482600659,
    54746542353882984, 23530110444602242, 45583],
  m1K32P56 [47573066507572558, 53784263376377472, 26373365858087535, 35439476293363712]]⟩
private def m1K32Bkt29 : M1L50BktRec := ⟨29, 29, 56754581, 94753556012, [
  m1K32P56 [
    64921734508870369, 46717402530314554, 70152031502416614, 16579065707947685,
    64865118238175867, 63136409656943418, 15075],
  m1K32P56 [
    63616120273463001, 32022429456642874, 63959522136832731, 16554273277661323,
    54860533086143770, 9186672023295290, 15034],
  m1K32P56 [
    51404888297971445, 7895845148029242, 65366526588107445, 14698198379164936,
    56006969227934215, 57882349635739825, 45240],
  m1K32P56 [
    46606213494182935, 585689876009391, 42411937762619021, 48495609135328964,
    8952445607247846, 17449984505820843, 43502],
  m1K32P56 [
    51034990400388609, 32946491011109032, 37338815547811700, 46772170359450378,
    60894354031007508, 37623791031265188, 41851],
  m1K32P56 [
    5523167453093703, 36890404494445730, 31981622952632479, 44346670122474971,
    66199540462325698, 61074142542177435, 39477],
  m1K32P56 [
    29846507716204797, 63897673350594712, 1009918123808387, 41797140071349831,
    23129655474269257, 32098661247878802, 36853],
  m1K32P56 [
    24924651072818387, 23048557079682957, 37021504545786465, 36669882787880123,
    33540570031263852, 9954606642194345, 38719],
  m1K32P56 [
    56172548362186893, 58933452959872425, 49705356793714367, 47878773649578014,
    17912266707788694, 5651122158251414, 43626],
  m1K32P56 [
    52296520740352233, 59285300717691797, 1571402039274170, 48143970363322499,
    45533476615338321, 60694779764703636, 43867],
  m1K32P56 [
    4823203903752231, 10764854807055252, 42410010304555949, 41515347015335018,
    71879712263019389, 57496292919144363, 37604],
  m1K32P56 [
    22770270226888553, 69797626364723628, 56484807026971206, 40993035020706452,
    68648491959987072, 65842797641219244, 37114],
  m1K32P56 [
    19689640050820910, 7631354907578285, 46602036343246925, 48862930207086634,
    43332949660731726, 63973632003050383, 44522],
  m1K32P56 [
    62757596374639590, 25665548764142734, 4659849498504765, 49134671259114621,
    22830923792775984, 39380715422481037, 44770],
  m1K32P56 [
    35260907045176142, 37639085448661388, 70279914381160245, 39300508313952028,
    38504754120795805, 48313136670837167, 35509],
  m1K32P56 [
    61938039858654881, 21511437083061935, 63807062220376510, 38481764774063988,
    36860236261703977, 25086115900133552, 34717],
  m1K32P56 [
    60431154202645967, 4071151563071152, 52502149418026605, 49867934552631958,
    9122121928164565, 47388613979338373, 45438],
  m1K32P56 [
    49025194172224241, 61235864832217475, 6335418210234834, 50145639769704336,
    4337430331601635, 50678140450737280, 45691],
  m1K32P56 [34547019116426334, 538930275197]]⟩
private def m1K32Bkt30 : M1L50BktRec := ⟨30, 30, 40056487, 137671395657, [
  m1K32P56 [
    33681250499346529, 47546436730547003, 66212004648139639, 16738591010682792,
    33681250497046763, 47546436730547003, 15223],
  m1K32P56 [
    33681250497046763, 47546436730547003, 66212004648139639, 16738591010682792,
    33681250497046763, 47546436730547003, 15223],
  m1K32P56 [
    33681250497046763, 47546436730547003, 52982680742738807, 16709727723157129,
    58518273249641881, 69813154991182513, 45258],
  m1K32P56 [
    54419373205157897, 53154445484500143, 4695682323230386, 48869864800886498,
    37563958663935029, 7069496407300780, 43878],
  m1K32P56 [
    18133870176136357, 71842815943850410, 55916627308554515, 46906116716093523,
    27298935188282715, 70416733474406309, 42003],
  m1K32P56 [
    53204983873796654, 12346015512635810, 54783558432039259, 45015452465753424,
    32128342307251339, 6032594698595230, 40168],
  m1K32P56 [
    21739374711225301, 17591746334456987, 17899891078240671, 42218149073378089,
    76976920276693, 37183919887877524, 37341],
  m1K32P56 [
    39111696926475293, 21623612183405711, 51101973148437753, 38859853577981652,
    43172785884324200, 31643403874756742, 33303],
  m1K32P56 [
    6916313311624938, 11276103564069806, 71686233995972212, 39992170671652941,
    29215503802524938, 1929292465500334, 36276],
  m1K32P56 [
    40425875244889734, 26376934176927662, 67146427836042577, 49178649998309243,
    66761321905689514, 43228050718050956, 44767],
  m1K32P56 [
    37748444152302161, 37076283830613132, 33931049632968455, 49310110103379112,
    49592882204473130, 20745085845997963, 44887],
  m1K32P56 [
    18456473845068777, 23587321547341963, 29184884643049343, 39072816293400599,
    47157292158117622, 68294559977531055, 35419],
  m1K32P56 [
    58443392472810291, 6680125369913007, 65214197839268324, 38676823649810371,
    8962035683996452, 12592363611301808, 35049],
  m1K32P56 [
    20282044754524836, 59188567559353776, 71644616171685989, 49663160242696270,
    62535215735499687, 47490864701287815, 45208],
  m1K32P56 [
    22868353774323069, 70139705398359431, 24917951094436032, 49796088555028170,
    10694755002962674, 48512128695115142, 45329],
  m1K32P56 [
    37847297732752900, 7449764767267973, 32564485564969274, 37400073113755401,
    27751749475537331, 46230633617797297, 33838],
  m1K32P56 [
    39150369343476240, 35812757805168561, 24965182917542771, 36780452529419167,
    61975267877041095, 29441287248736689, 33236],
  m1K32P56 [
    1347939009329113, 53184142020171954, 61221811525222633, 50152505177419118,
    64597293825095347, 8326267994433407, 45654],
  m1K32P56 [
    53272049161682266, 59788910415584382, 30537135493591678, 50286801989754092,
    40673600988484749, 530705380731]]⟩
private def m1K32Bkt31 : M1L50BktRec := ⟨31, 31, 28637701, 198484922273, [
  m1K32P56 [
    40213642353494031, 62514088908822587, 6820884238580622, 16764108166368990,
    40213642352713240, 62514088908822587, 15246],
  m1K32P56 [
    40213642352713240, 62514088908822587, 6820884238580622, 16764108166368990,
    40213642352713240, 62514088908822587, 15246],
  m1K32P56 [
    40213642352713240, 62514088908822587, 53827205348146062, 16763715294301917,
    41644403332450282, 17314773439709242, 45528],
  m1K32P56 [
    61908249982267702, 18410977993254320, 22428757059743707, 48919189933446641,
    53022907488255613, 37649119541465260, 43943],
  m1K32P56 [
    39642757180392900, 67820808731812778, 12008230091073899, 47363001730745446,
    6117144334285695, 28802419507220647, 42463],
  m1K32P56 [
    45257533448833401, 13987588993035940, 61539699375186777, 45224803415754704,
    19087524553799705, 58050499937567647, 40398],
  m1K32P56 [
    21154086674943551, 71007132197554844, 65753780280859318, 43083250412359676,
    23434598236242337, 3657617722112919, 38269],
  m1K32P56 [
    38397924929465010, 39656710503981203, 54763537372778862, 39580985885402535,
    54146289987662446, 22656028728215177, 34393],
  m1K32P56 [
    65903857344532608, 62367056529668225, 34252411179020386, 38293883457113043,
    33454456711858304, 62203254487796656, 34759],
  m1K32P56 [
    39061854345672104, 28937529024276144, 52267066111723394, 38064450954108596,
    50268187832066765, 20920067141479600, 34547],
  m1K32P56 [
    55884312833392476, 51583247751571376, 39836036036789929, 49779894635256448,
    26682151573298255, 37207133887453318, 45294],
  m1K32P56 [
    5082237050675768, 35394039548436102, 36457346428285186, 49845741698794392,
    32412596440562067, 31273982393942149, 45354],
  m1K32P56 [
    9264247429822383, 31617028641882245, 60149051900014910, 37379774326557843,
    23215898937684933, 7801603914280369, 33910],
  m1K32P56 [
    28850831606839667, 5766406397782961, 64371434404480029, 37085778969459334,
    40122835070446457, 57929632222045105, 33634],
  m1K32P56 [
    45765945349825840, 11137716215097521, 35891363379315457, 50021913022543526,
    43946953672494721, 52503543348156546, 45514],
  m1K32P56 [
    14412800033235814, 57739418056420994, 26882809996227038, 50088113682368003,
    23634396266553858, 69610636614859905, 45574],
  m1K32P56 [
    62067477324429611, 4813115850841984, 32002501714293275, 36133010499722942,
    13280248027098401, 45397185199159730, 32729],
  m1K32P56 [
    18942720026561382, 48525293398643634, 41009960165343051, 35662589932492652,
    30274672544380151, 46964206465916082, 32268],
  m1K32P56 [
    35944841113021134, 34400087433277362, 62625246658133332, 50265114824315866,
    36917917467748046, 1242115950794364, 45736],
  m1K32P56 [38991403107911030, 13530258241227899, 6326890834473660, 8013329]]⟩
private def m1K32Bkt32 : M1L50BktRec := ⟨32, 32, 16473911, 355432061111, [
  m1K32P56 [
    42588084958317012, 21853049543566139, 45945942232480663, 16773383332796237,
    42588084958088611, 21853049543566139, 15255],
  m1K32P56 [
    42588084958088611, 21853049543566139, 45945942232480663, 16773383332796237,
    42588084958088611, 21853049543566139, 15255],
  m1K32P56 [
    42588084958088611, 21853049543566139, 37783167907871639, 16773371588745037,
    39041434108999931, 4054150925377595, 45536],
  m1K32P56 [
    66382240122146410, 36932255936302768, 20741133713321971, 49248080577361630,
    69150209039772604, 47899867307714989, 44271],
  m1K32P56 [
    64336645882941907, 5556565957655211, 41000504470186708, 47465364609154520,
    35637554097258343, 51165393470631335, 42580],
  m1K32P56 [
    9926140363060681, 48272568255498405, 34238696182162409, 45782824458037052,
    25662462365477852, 40126264615275425, 40964],
  m1K32P56 [
    45688580561064322, 13407020446097054, 60125374479244595, 43390946768565667,
    38140003664516627, 55701914171483288, 38609],
  m1K32P56 [
    836726584100327, 16084296091107989, 62086218533802774, 40819179658478803,
    55491138773394658, 27004608087846286, 35912],
  m1K32P56 [
    33104008200952808, 19846760881356681, 70229926438405660, 50104496180805369,
    70915015464568846, 15558643516480640, 45576],
  m1K32P56 [
    59920367338666269, 47480763950332800, 50861271866126862, 36219241816436010,
    5941686514817619, 58255976557761458, 32900],
  m1K32P56 [
    7755614413098034, 49581928636386226, 49453979994390619, 36083523369705983,
    11382833716252435, 6837528484243890, 32775],
  m1K32P56 [
    13197642079609056, 40993857309270194, 70509325331562459, 50161193946592597,
    49307107168560373, 56858710802759551, 45627],
  m1K32P56 [
    36533401980879823, 17216918683139967, 60657116031922754, 50182465439880036,
    10100340142157968, 9975315550464383, 45647],
  m1K32P56 [
    68464251295966258, 42609919358247806, 46076501897032277, 35678439230849364,
    25909071082949517, 6717460083570098, 32398],
  m1K32P56 [
    27725833659645939, 26515265568747442, 4981238453861977, 35504361374378229,
    31359658583329644, 68967633225637554, 32234],
  m1K32P56 [
    33177254379583684, 69076484985120946, 61781218940976560, 50239246840265811,
    32886193028125388, 56768552040491389, 45698],
  m1K32P56 [
    15287203751415034, 17851338083742077, 27721939796341385, 50260554286953752,
    49766020982748517, 12229303866488700, 45718],
  m1K32P56 [
    29550305705601946, 45576390820337788, 24684708777144988, 34934807938735364,
    45907602753919135, 7529987332212402, 31692],
  m1K32P56 [
    47727195714064271, 9457429756553906, 55647039508806517, 34646173037015046,
    51367115140531067, 58345252582205106, 31405],
  m1K32P56 [
    53187494072405964, 66148486713033650, 43200047731997238, 50317421385532269,
    47803189909116047, 64652051604680569, 45769],
  m1K32P56 [68083896619753951, 120]]⟩
private theorem m1K32Sound1 {s0 r : ℕ} {b0 : M1L50BktRec}
    (h : m1K32CheckSingle s0 r b0 = true) : M1K32RangeSound r r :=
  checkSchedChunkL50_sound h
private theorem m1K32Sound2 {s0 s1 r : ℕ} {b0 b1 : M1L50BktRec}
    (h : (m1K32CheckSingle s0 r b0 && m1K32CheckSingle s1 (r + 1) b1) = true) :
    M1K32RangeSound r (r + 1) :=
  m1K32RangeSound_and h
    (fun h0 ↦ checkSchedChunkL50_sound h0) (fun h1 ↦ checkSchedChunkL50_sound h1)
private def m1K32ChkBool00 : Bool :=
  m1K32CheckSingle 1 3 m1K32Bkt3 &&
    m1K32CheckSingle 2 4 m1K32Bkt4
private theorem cert_m1K32_aux : m1K32ChkBool00 = true := by decide +kernel
private def m1K32ChkBool01 : Bool :=
  m1K32CheckSingle 3 5 m1K32Bkt5 &&
    m1K32CheckSingle 4 6 m1K32Bkt6
private theorem cert_m1K32_c01 : m1K32ChkBool01 = true := by decide +kernel
private def m1K32ChkBool02 : Bool :=
  m1K32CheckSingle 5 7 m1K32Bkt7 &&
    m1K32CheckSingle 6 8 m1K32Bkt8
private theorem cert_m1K32_c02 : m1K32ChkBool02 = true := by decide +kernel
private def m1K32ChkBool03 : Bool :=
  m1K32CheckSingle 7 9 m1K32Bkt9 &&
    m1K32CheckSingle 8 10 m1K32Bkt10
private theorem cert_m1K32_c03 : m1K32ChkBool03 = true := by decide +kernel
private def m1K32ChkBool04 : Bool :=
  m1K32CheckSingle 9 11 m1K32Bkt11 &&
    m1K32CheckSingle 10 12 m1K32Bkt12
private theorem cert_m1K32_c04 : m1K32ChkBool04 = true := by decide +kernel
private def m1K32ChkBool05 : Bool :=
  m1K32CheckSingle 11 13 m1K32Bkt13 &&
    m1K32CheckSingle 12 14 m1K32Bkt14
private theorem cert_m1K32_c05 : m1K32ChkBool05 = true := by decide +kernel
private def m1K32ChkBool06 : Bool :=
  m1K32CheckSingle 13 15 m1K32Bkt15 &&
    m1K32CheckSingle 14 16 m1K32Bkt16
private theorem cert_m1K32_c06 : m1K32ChkBool06 = true := by decide +kernel
private def m1K32ChkBool07 : Bool :=
  m1K32CheckSingle 15 17 m1K32Bkt17 &&
    m1K32CheckSingle 16 18 m1K32Bkt18
private theorem cert_m1K32_c07 : m1K32ChkBool07 = true := by decide +kernel
private def m1K32ChkBool08 : Bool :=
  m1K32CheckSingle 17 19 m1K32Bkt19 &&
    m1K32CheckSingle 18 20 m1K32Bkt20
private theorem cert_m1K32_c08 : m1K32ChkBool08 = true := by decide +kernel
private def m1K32ChkBool09 : Bool :=
  m1K32CheckSingle 19 21 m1K32Bkt21 &&
    m1K32CheckSingle 20 22 m1K32Bkt22
private theorem cert_m1K32_c09 : m1K32ChkBool09 = true := by decide +kernel
private def m1K32ChkBool10 : Bool :=
  m1K32CheckSingle 21 23 m1K32Bkt23 &&
    m1K32CheckSingle 22 24 m1K32Bkt24
private theorem cert_m1K32_c10 : m1K32ChkBool10 = true := by decide +kernel
private def m1K32ChkBool11 : Bool := m1K32CheckSingle 23 25 m1K32Bkt25
private theorem cert_m1K32_c11 : m1K32ChkBool11 = true := by decide +kernel
private def m1K32ChkBool12 : Bool := m1K32CheckSingle 24 26 m1K32Bkt26
private theorem cert_m1K32_c12 : m1K32ChkBool12 = true := by decide +kernel
private def m1K32ChkBool13 : Bool := m1K32CheckSingle 25 27 m1K32Bkt27
private theorem cert_m1K32_c13 : m1K32ChkBool13 = true := by decide +kernel
private def m1K32ChkBool14 : Bool := m1K32CheckSingle 26 28 m1K32Bkt28
private theorem cert_m1K32_c14 : m1K32ChkBool14 = true := by decide +kernel
private def m1K32ChkBool15 : Bool := m1K32CheckSingle 27 29 m1K32Bkt29
private theorem cert_m1K32_c15 : m1K32ChkBool15 = true := by decide +kernel
private def m1K32ChkBool16 : Bool := m1K32CheckSingle 28 30 m1K32Bkt30
private theorem cert_m1K32_c16 : m1K32ChkBool16 = true := by decide +kernel
private def m1K32ChkBool17 : Bool := m1K32CheckSingle 29 31 m1K32Bkt31
private theorem cert_m1K32_c17 : m1K32ChkBool17 = true := by decide +kernel
private def m1K32ChkBool18 : Bool := m1K32CheckSingle 30 32 m1K32Bkt32
private theorem cert_m1K32_c18 : m1K32ChkBool18 = true := by decide +kernel
private def m1K32CellsBool : Bool :=
  ((((checkSwLTableMonoNatL50 32 m1K32VTableNat &&
      SchurWeylLCert.checkSwLRelCostCell 0 2 (m1K32VTable 4) 1798014765956261 2500000000000000) &&
     SchurWeylLCert.checkSwLRelCostCell 0 3 (m1K32VTable 8) 173143829619399 250000000000000) &&
    SchurWeylLCert.checkSwLRelCostCell 0 4 (m1K32VTable 16) 6751273712926893 10000000000000000) &&
   SchurWeylLCert.checkSwLRelCostCell 0 5 (m1K32VTable 32) 1328876209066213 2000000000000000)
private theorem cert_m1K32_cells : m1K32CellsBool = true := by decide +kernel
private theorem sound_m1K32_r3_32 : M1K32RangeSound 3 32 :=
  m1L50StageSound_join
    (m1L50StageSound_join
      (m1L50StageSound_join
        (m1L50StageSound_join
          (m1K32Sound2 cert_m1K32_aux)
          (m1K32Sound2 cert_m1K32_c01))
        (m1L50StageSound_join
          (m1K32Sound2 cert_m1K32_c02)
          (m1K32Sound2 cert_m1K32_c03)))
      (m1L50StageSound_join
        (m1L50StageSound_join
          (m1K32Sound2 cert_m1K32_c04)
          (m1K32Sound2 cert_m1K32_c05))
        (m1L50StageSound_join
          (m1K32Sound2 cert_m1K32_c06)
          (m1L50StageSound_join
            (m1K32Sound2 cert_m1K32_c07)
            (m1K32Sound2 cert_m1K32_c08)))))
    (m1L50StageSound_join
      (m1L50StageSound_join
        (m1L50StageSound_join
          (m1K32Sound2 cert_m1K32_c09)
          (m1K32Sound2 cert_m1K32_c10))
        (m1L50StageSound_join
          (m1K32Sound1 cert_m1K32_c11)
          (m1L50StageSound_join
            (m1K32Sound1 cert_m1K32_c12)
            (m1K32Sound1 cert_m1K32_c13))))
      (m1L50StageSound_join
        (m1L50StageSound_join
          (m1K32Sound1 cert_m1K32_c14)
          (m1K32Sound1 cert_m1K32_c15))
        (m1L50StageSound_join
          (m1K32Sound1 cert_m1K32_c16)
          (m1L50StageSound_join
            (m1K32Sound1 cert_m1K32_c17)
            (m1K32Sound1 cert_m1K32_c18)))))
private theorem cert_m1K32_mono_le : ∀ r : ℕ, r < 32 → m1K32VTable r ≤ m1K32VTable (r + 1) := by
  have h := checkSwLTableMonoNatL50_sound
    (m1K32BoolAnd1 (m1K32BoolAnd1 (m1K32BoolAnd1 (m1K32BoolAnd1 cert_m1K32_cells))))
  unfold SchurWeylLCert.checkSwLTableMono at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h; exact h.2
private def m1K32StageSpecOfR (r : ℕ) : SwLM1StageSpec :=
  let s := m1K32RawStageOfR r; ⟨s.L, s.tauNum, s.tauDen, s.pulses⟩
private def m1K32Bundle : SwLM1L50CertBundle where
  kMax := 32
  vScale := (m1K32VScaleNat : ℤ)
  vTable := m1K32VTable
  useSwL r := decide (3 ≤ r)
  stageOfR := m1K32StageSpecOfR
  hKMax := by omega
  hScalePos := by unfold m1K32VScaleNat; omega
  hV0 := rfl
  hMono := cert_m1K32_mono_le
  hStageSound {n r} hn128 _hr1 hrk huse :=
    sound_m1K32_r3_32 r (of_decide_eq_true huse) hrk hn128
private theorem m1K32_hseed (n k : ℕ) (hk2 : 2 ≤ k) : 2 * n ≤ findAllQubits n 1 k :=
  (by have := Nat.mul_le_mul_left n hk2; unfold findAllQubits; omega)
private def m1K32Sub2Reg (n k : ℕ) (hk2 : 2 ≤ k) :
    QRegister (findAllQubits n 1 2) (findAllQubits n 1 k) :=
  QRegister.block 0 (findAllQubits n 1 2)
    (by have := Nat.mul_le_mul_left n hk2; unfold findAllQubits; omega)
private def m1K32MemKReg (n k : ℕ) : QRegister (n * k) (findAllQubits n 1 k) :=
  QRegister.block 0 (n * k) (by unfold findAllQubits; omega)
private theorem hm1_grid : 1 ∈ GroverSol.groverGrid := by
  unfold GroverSol.groverGrid; exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩
private theorem hk_grid_of_idx {k idx : ℕ} (hi : idx < 11) (hk : 2 ^ idx = k) :
    k ∈ GroverSol.groverGrid := by
  unfold GroverSol.groverGrid; exact Finset.mem_image.2 ⟨idx, Finset.mem_range.2 hi, hk⟩
private noncomputable def m1K32BranchFn {Var : Type} (res : Var) {n k : ℕ} (hk_grid : k ∈
  GroverSol.groverGrid) (hk2 : 2 ≤ k)
    (T : Finset (Fin (2 ^ n))) (hn0 : n ≠ 0) (uVal : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  let hm1 : 1 ∈ GroverSol.groverGrid := hm1_grid
  let sub2 := m1K32Sub2Reg n k hk2
  let memK := m1K32MemKReg n k
  let cAvg2 := longTailM1K2OnlyCircuit res n 1 2
  if hu : uVal < 2 ^ (2 * n) then
    let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
    if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
      stage2Fuel0Circuit res n 1 k (findAllQubits n 1 k) hm1 hk_grid le_rfl T
    else
      let perm := GF2nForallA.finAffinePerm hn0
        (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
        (GF2nForallA.seedToGFPair hn0 u).2
      .seq (resetAllCircuit res)
        (.seq (deflateCirc n 1 T (permOracleCirc n 1 perm (embedOracleCirc sub2 cAvg2)))
          (dispBits res (2 * n) 0 fun wVal ↦
            let R_dec := (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
            setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))))
  else OracleDynamicCircuit.skip
private noncomputable def m1K32R2FromSetCirc {Var : Type} (res : Var) (n k : ℕ) (hk_grid : k ∈
  GroverSol.groverGrid) (hk2 : 2 ≤ k)
    (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  let hm1 : 1 ∈ GroverSol.groverGrid := hm1_grid
  if hn0 : n = 0 then stage2Fuel0Circuit res n 1 k (findAllQubits n 1 k) hm1 hk_grid le_rfl T
  else .seq (resetAllCircuit res)
      (.seq (sampleSeedCircuit res n (findAllQubits n 1 k) ((n + 1) * 1) (m1K32_hseed n k hk2))
        (dispBits res (2 * n) 0 (m1K32BranchFn res hk_grid hk2 T hn0)))
private theorem m1K32R2FromSet_transition {Var : Type} [DecidableEq Var] (res : Var) {n k : ℕ}
  (hn : 600 ≤ n)
  (hk_grid : k ∈ GroverSol.groverGrid) (hk2 : 2 ≤ k) {S T : Finset (Fin (2 ^ n))} (hS :
    S.card = k) (hTS : T ⊆ S) (hST2 : (S \ T).card = 2)
  (Ξ : CQState (Store Var) (2 ^ findAllQubits n 1 k)) :
    let prog := (m1K32R2FromSetCirc res n k hk_grid hk2 T).compile QProg.qAssign
      (parallelMarkingOracle 1 S)
    𝔼[(interp prog).toStateFun Ξ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Ξ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Ξ ≤
      stateMass Ξ * ENNReal.ofReal (((m1K32VTable 2 : ℝ) / (m1K32VScaleNat : ℝ)) * √(2 ^ n : ℝ)) :=
      by
  have hm1 : 1 ∈ GroverSol.groverGrid := hm1_grid
  have hn0 : n ≠ 0 := (by omega)
  have hn1 : 1 ≤ n := by omega
  dsimp only [m1K32R2FromSetCirc]; rw [dite_eq_right hn0]; let Q := findAllQubits n 1 k
  have hkN2 : 2 ≤ 2 ^ n := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num)
    hn1); have hgrid12 : isGridCell 1 2 = true := rfl
  have hval12 : longTailM1K2OnlyProfile.validCell 1 2 = true := rfl
  have hn0_lt : longTailM1K2OnlyProfile.n0 1 2 ≤ n := by change 100 ≤ n; omega
  obtain ⟨q, hq_bound, hq_avg⟩ := (validFamily_longTailM1K2Only (Var := Var) res).costBound_uniform
    hgrid12 hval12 n hn0_lt hkN2
  let cAvg2 := longTailM1K2OnlyCircuit (Var := Var) res n 1 2
  have horacle : IsRealMatrix (parallelMarkingOracle 1 S).1 := isRealMatrix_parallelMarkingOracle S
  let sub2 : QRegister (findAllQubits n 1 2) Q := m1K32Sub2Reg n k hk2
  let memK : QRegister (n * k) Q := m1K32MemKReg n k; let R := S \ T
  let unit : ℝ := (π / 4) * √((2 ^ n : ℝ) / (1 : ℝ))
  let uAvg : ℝ :=
    (379666241046199 / 500000000000000 : ℝ) * (∑ r ∈ Finset.Icc (1 : ℕ) 2, (1 : ℝ) / √(r : ℝ))
  have hrst0 := resetAllCircuit_transition res horacle Ξ
  let Ξ₁ := (interp ((resetAllCircuit res).compile QProg.qAssign
    (parallelMarkingOracle 1 S))).toStateFun Ξ
  let Ξ₂ := (interp ((sampleSeedCircuit res n (findAllQubits n 1 k) ((n + 1) * 1)
    (m1K32_hseed n k hk2)).compile QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun Ξ₁
  have hΞ₁ : (interp ((resetAllCircuit res).compile QProg.qAssign (parallelMarkingOracle 1
    S))).toStateFun Ξ = Ξ₁ := rfl; have hΞ₂ : (interp ((sampleSeedCircuit res n (findAllQubits n 1
    k) ((n + 1) * 1) (m1K32_hseed n k hk2)).compile QProg.qAssign (parallelMarkingOracle 1
    S))).toStateFun Ξ₁ = Ξ₂ := rfl
  let postS : CQAssertion (Store Var) (2 ^ findAllQubits n 1 k) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  have hpostS : liftPureProp (fun τ : Store Var ↦ decodeTargetsLocal n k (τ res) = S) = postS :=
    rfl
  let modelS := CostModel.ofEmbeddedOracle (n := findAllQubits n 1 k)
    (parallelMarkingOracle 1 S)
  let branchFn := m1K32BranchFn (Var := Var) res hk_grid hk2 T hn0
  have hbranch (uVal : ℕ) (hu : uVal < 2 ^ (2 * n)) :
      let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩; let Δ_sl := sliceState res 0 (2 * n) uVal Ξ₂
      𝔼[(interp ((branchFn uVal).compile QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun
          Δ_sl, postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace ∧
        expectedCost modelS
          ((branchFn uVal).compile QProg.qAssign (parallelMarkingOracle 1 S)) Δ_sl ≤
          stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) *
            if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
              (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit
            else
              (q (R.map (GF2nForallA.finAffinePerm hn0
                (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
                (GF2nForallA.seedToGFPair hn0 u).2).toEmbedding) : ℝ)) := by
    intro u Δ_sl
    have htr_sl : (Δ_sl.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
      have hs := sampleSeed_sliceState_trace res n (findAllQubits n 1 k) ((n + 1) * 1) (m1K32_hseed
        n k hk2) (parallelMarkingOracle 1 S) hrst0.2.2.2 hu; rw [hrst0.2.1] at hs; exact hs
    have hmass_sl : stateMass Δ_sl = stateMass Ξ * ENNReal.ofReal (1 / (2 ^ (2 * n) : ℝ)) := by
      rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_sl, mul_comm,
        ENNReal.ofReal_mul Ξ.trace.coe_nonneg]
    dsimp only [branchFn, m1K32BranchFn]; rw [dite_eq_left hu]
    by_cases ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0
    · rw [dite_eq_left ha, dite_eq_left ha]
      obtain ⟨hc_f0, hcost_f0⟩ := stage2Fuel0_transition res hn hm1 hk_grid le_rfl hS hTS Δ_sl
      rw [hST2] at hcost_f0; refine ⟨hc_f0.trans htr_sl, hcost_f0.trans ?_⟩; rw [hmass_sl,
        mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) (by positivity)
      dsimp only [unit]; push_cast; ring
    · rw [dite_eq_right ha, dite_eq_right ha]
      let perm := GF2nForallA.finAffinePerm hn0
        (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
        (GF2nForallA.seedToGFPair hn0 u).2
      let B := R.map perm.toEmbedding
      have hB_mem : B ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2 :=
        (by rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, by simp [B, R, hST2]⟩)
      have hrst_u := resetAllCircuit_transition res horacle Δ_sl; set Δ_u := (interp
        ((resetAllCircuit res).compile QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun Δ_sl
      let cEmb := embedOracleCirc sub2 cAvg2; let γ_u := marginalState sub2 Δ_u
      have hγ_supp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 2))) γ_u :=
        supportedOn_zero_marginalState sub2 hrst_u.2.2.2
      have hγ_qset : γ_u = (interp QProg.qSet).toStateFun γ_u :=
        (by rw [interp_qSet]; exact cqState_eq_qSet_of_supportedOn_zero hγ_supp)
      let postB_loc : CQAssertion (Store Var) (2 ^ findAllQubits n 1 2) :=
        liftPureProp (fun τ ↦ decodeTargetsLocal n 2 (τ res) = B)
      let postB_glob : CQAssertion (Store Var) (2 ^ Q) :=
        liftPureProp (fun τ ↦ decodeTargetsLocal n 2 (τ res) = B)
      have hliftB : liftAssertion sub2 postB_loc = postB_glob := liftAssertion_liftPureProp sub2 _
      let afterC := (interp ((deflateCirc n 1 T (permOracleCirc n 1 perm cEmb)).compile
        QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun Δ_u
      have hafterC_B : 𝔼[afterC, postB_glob] = (Δ_u.trace : ℝ) := by
        dsimp only [afterC]; rw [interp_deflateCirc n 1 hTS, interp_permOracleCirc n 1 perm R cEmb,
          ← hliftB, expect_liftAssertion_eq_marginalState, marginalState_interp_embedOracleCirc]
        let pSol := QProg.qSet ;; cAvg2.compile QProg.qAssign (parallelMarkingOracle 1 B)
        have hprog_qset : (interp (cAvg2.compile QProg.qAssign (parallelMarkingOracle 1
          B))).toStateFun γ_u = (interp pSol).toStateFun γ_u :=
          (by dsimp only [pSol]; rw [interp_qSeq, QMonad.Q.toStateFun_bind, ← hγ_qset])
        rw [hprog_qset]; have hcorr_lt := (validFamily_longTailM1K2Only (Var := Var)
          res).correctness hn1 hgrid12 hval12 hkN2 hB_mem γ_u; have hge : (γ_u.trace : ℝ) ≤
          𝔼[(interp pSol).toStateFun γ_u, postB_loc] := (expect_top γ_u).symm.trans_le hcorr_lt
        have hle1 : 𝔼[(interp pSol).toStateFun γ_u, postB_loc] ≤ (((interp pSol).toStateFun
          γ_u).trace : ℝ) := (by rw [← expect_top _]; exact expect_mono le_rfl le_top)
        have hle2 : (((interp pSol).toStateFun γ_u).trace : ℝ) ≤ γ_u.trace :=
          NNReal.coe_le_coe.mpr ((interp pSol).trace_toStateFun_le γ_u)
        have htr_γ : (γ_u.trace : ℝ) = Δ_u.trace :=
          congrArg ((↑) : ℝ≥0 → ℝ) (trace_marginalState sub2 Δ_u); linarith
      let writeDisp := dispBits (Q := Q) (w := (n + 1) * 1) res (2 * n) 0 fun wVal ↦
        let R_dec := (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
        setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))
      have hwp_write : postB_glob ≤ wp (writeDisp.compile QProg.qAssign (parallelMarkingOracle 1 S))
        postS := by
        intro τ; rw [wp_dispBits]
        open Classical in
        by_cases hBτ : decodeTargetsLocal n 2 (τ res) = B
        · have hw_dec : decodeTargetsLocal n 2 ((((τ res).toNat / 2 ^ 0) % 2 ^ (2 * n) : ℕ) : ℤ) = B
            := by
            rw [pow_zero, Nat.div_one, show 2 * n = n * 2 by ring, decodeTargetsLocal_mod_pow, hBτ]
          have hset_eq : T ∪ B.map perm.symm.toEmbedding = S :=
            (by rw [finset_map_symm_map perm R]; exact Finset.union_sdiff_of_subset hTS)
          dsimp only; rw [hw_dec, hset_eq]
          have hwp_top : (⊤ : CQAssertion (Store Var) (2 ^ Q)) ≤ wp ((setClassicalValCircuit res
            memK
            (encodeFinsetVal n k S)).compile QProg.qAssign (parallelMarkingOracle 1 S)) postS := by
            have hmeas_le : diagAssertion (Var := Var) (fun z : Fin (2 ^ Q) ↦ memK.extractIndex z =
              encodeFinsetVal n k S) ≤ wp (QProg.measureRegister res memK) postS := by
              intro σ; rw [QProg.measureRegister, wp_qMeasure]; change (diagObs _).1 ≤ ∑ o : Fin (2
                ^ (n * k)), HermitianMat.conj (memK.basisOutcomeProjector o)ᴴ (postS (Store.subst σ
                res ↑o.val)).1; refine le_trans ?_ (Finset.single_le_sum (fun o _ ↦
                HermitianMat.conj_nonneg _ (postS _).2.1) (Finset.mem_univ (encodeFinsetVal n k
                S))); have hpS : decodeTargetsLocal n k (Store.subst σ res ↑(encodeFinsetVal n k
                S).val res) = S := (by simp [Store.subst, decodeTargetsLocal_encodeFinsetVal hS])
              have h1 : (postS (Store.subst σ res ↑(encodeFinsetVal n k S).val)).1 = 1 :=
                (by dsimp only [postS]; rw [liftPureProp_apply, ite_eq_left hpS]; rfl); rw [h1];
                apply le_of_eq; apply HermitianMat.ext
              rw [diagObs_mat, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
                memK.basisOutcomeProjector_conjTranspose, HermitianMat.mat_one, Matrix.mul_one,
                basisOutcomeProjector_eq_diagProj, diagProj_mul_self]
            let U_v := permutationUnitary
              (xorBitsPerm (regMaskVec memK (encodeFinsetVal n k S).val))
            have hxor_le : diagAssertion (Var := Var) (fun z : Fin (2 ^ Q) ↦ memK.extractIndex z =
              0) ≤ wp (QProg.qAssign (phaseI U_v)) (diagAssertion (fun z ↦ memK.extractIndex z =
              encodeFinsetVal n k S)) := by
              rw [wp_qAssign, qAssign_phaseI, wp_qAssign_permutationUnitary_diagAssertion]; intro σ;
                refine diagObs_mono fun z hz0 ↦ ?_; rw [xorBitsPerm_regMaskVec_of_clean memK _ z
                hz0]; exact memK.extractIndex_replaceIndex z _
            dsimp only [setClassicalValCircuit]; simp only [OracleDynamicCircuit.compile_seq,
              OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_measure, wp_qSeq]
            exact (wp_resetRegCircuit_top_le res memK _).trans (wp_mono _ (hxor_le.trans (wp_mono _
              hmeas_le)))
          exact le_top.trans (hwp_top τ)
        · have h0 : (postB_glob τ).1 = 0 :=
            (by dsimp only [postB_glob]; rw [liftPureProp_apply, ite_eq_right hBτ]; rfl)
          change (postB_glob τ).1 ≤ _; rw [h0]; exact (wp _ postS τ).2.1
      have hcorr_u : 𝔼[(interp (OracleDynamicCircuit.compile QProg.qAssign (parallelMarkingOracle 1
        S) (.seq (resetAllCircuit res) (.seq (deflateCirc n 1 T (permOracleCirc n 1 perm cEmb))
        writeDisp)))).toStateFun Δ_sl, postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
        simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
        change 𝔼[(interp (writeDisp.compile QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun
          afterC, postS] = _
        have hge : (Δ_u.trace : ℝ) ≤ 𝔼[(interp (writeDisp.compile QProg.qAssign
          (parallelMarkingOracle 1 S))).toStateFun afterC, postS] := by
          rw [← hafterC_B, ← wp_expectation_eq (writeDisp.compile QProg.qAssign
            (parallelMarkingOracle 1 S)) afterC]; exact expect_mono le_rfl hwp_write
        have hle1 : 𝔼[(interp (writeDisp.compile QProg.qAssign (parallelMarkingOracle 1
          S))).toStateFun afterC, postS] ≤ (((interp (writeDisp.compile QProg.qAssign
          (parallelMarkingOracle 1 S))).toStateFun afterC).trace : ℝ) :=
          (by rw [← expect_top _]; exact expect_mono le_rfl le_top)
        have hle2 : (((interp (writeDisp.compile QProg.qAssign (parallelMarkingOracle 1
            S))).toStateFun afterC).trace : ℝ) ≤ afterC.trace :=
          NNReal.coe_le_coe.mpr ((interp _).trace_toStateFun_le afterC)
        have hle3 : (afterC.trace : ℝ) ≤ Δ_u.trace :=
          NNReal.coe_le_coe.mpr ((interp _).trace_toStateFun_le Δ_u)
        have htr_u : (Δ_u.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace :=
          (by rw [hrst_u.2.1, htr_sl]); linarith
      refine ⟨hcorr_u, ?_⟩
      simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]; rw [hrst_u.1, zero_add]
      have hcost_write : expectedCost modelS (writeDisp.compile QProg.qAssign (parallelMarkingOracle
        1 S)) afterC = 0 := by
        dsimp only [writeDisp]; rw [expectedCost_dispBits]
        refine Finset.sum_eq_zero fun wVal _ ↦ ?_; exact (setClassicalValCircuit_transition res memK
          _ horacle (P := fun _ ↦ True) (fun _ ↦ trivial) _).2
      change expectedCost modelS ((deflateCirc n 1 T (permOracleCirc n 1 perm cEmb)).compile
        QProg.qAssign (parallelMarkingOracle 1 S)) Δ_u + expectedCost modelS (writeDisp.compile
        QProg.qAssign (parallelMarkingOracle 1 S)) afterC ≤ _; rw [hcost_write, add_zero]
      have hzc_perm := zeroStepCost_permOracleCirc n 1 perm (zeroStepCost_embedOracleCirc sub2
        cAvg2); have hcost_def := congrFun (expectedCost_deflateCirc n 1 hTS hzc_perm) Δ_u
      have hcost_perm := congrFun (expectedCost_permOracleCirc n 1 perm R
        (zeroStepCost_embedOracleCirc sub2 cAvg2)) Δ_u; dsimp only [modelS]; rw [hcost_def,
        hcost_perm]; have horB : IsRealMatrix (parallelMarkingOracle 1 B).1 :=
        isRealMatrix_parallelMarkingOracle B
      have hcost_emb := expectedCost_embedOracleCirc_le sub2 cAvg2 horB Δ_u
      refine hcost_emb.trans ?_
      have hcost_qset : expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 B))
        (cAvg2.compile QProg.qAssign (parallelMarkingOracle 1 B)) (marginalState sub2 Δ_u) =
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 B)) (QProg.qSet ;;
        cAvg2.compile QProg.qAssign (parallelMarkingOracle 1 B)) γ_u := by
        dsimp only [γ_u]; rw [expectedCost_qSeq, expectedCost_qSet,
          CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero, mul_zero, zero_add]
        dsimp only [γ_u] at hγ_qset; rw [← hγ_qset]
      rw [hcost_qset]; have hcb := hq_bound B hB_mem γ_u
      have hm_γ : (γ_u.trace : ℝ≥0∞) = stateMass Ξ * ENNReal.ofReal (1 / (2 ^ (2 * n) : ℝ)) := by
        change stateMass γ_u = _; dsimp only [γ_u]
        rw [stateMass_marginalState, hrst_u.2.2.1, hmass_sl]
      have hqB : ((q B : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (q B : ℝ) := ENNReal.ofReal_coe_nnreal.symm
      rw [hm_γ, hqB, mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hcb; exact hcb
  refine ⟨?_, ?_⟩
  · simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]; rw [hΞ₁,
      hΞ₂, hpostS, expect_dispBits]
    have hterms : ∀ uVal ∈ Finset.range (2 ^ (2 * n)), 𝔼[(interp ((m1K32BranchFn res hk_grid hk2
      T hn0
      uVal).compile QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun (sliceState res 0 (2 * n)
      uVal Ξ₂), postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := fun uVal hu ↦ (hbranch uVal
      (Finset.mem_range.mp hu)).1; rw [Finset.sum_congr rfl hterms, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc]; have hpow_ne : (2
      ^ (2 * n) : ℝ) ≠ 0 := (by positivity); rw [mul_one_div_cancel hpow_ne, one_mul]
  · simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]; rw [hΞ₁, hΞ₂, hrst0.1,
      expectedCost_sampleSeedCircuit res n (findAllQubits n 1 k) ((n + 1) * 1) (m1K32_hseed n k hk2)
      horacle Ξ₁, zero_add, zero_add, expectedCost_dispBits]
    let termR (u : Fin (2 ^ (2 * n))) : ℝ := (1 / (2 ^ (2 * n) : ℝ)) *
        if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
          (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit
        else
          (q (R.map (GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
            (GF2nForallA.seedToGFPair hn0 u).2).toEmbedding) : ℝ)
    have hterm_nn (u : Fin (2 ^ (2 * n))) : 0 ≤ termR u := by
      dsimp only [termR]; refine mul_nonneg (by positivity) ?_; split_ifs
      · have hh2 : 0 ≤ GroverSol.groverHarmonicSqrtSum 2 :=
          Finset.sum_nonneg fun _ _ ↦ by positivity
        have hu_pos : 0 ≤ unit := (by dsimp [unit]; positivity); positivity
      · exact NNReal.coe_nonneg _
    calc (∑ uVal ∈ Finset.range (2 ^ (2 * n)),
            expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S))
              ((m1K32BranchFn res hk_grid hk2 T hn0 uVal).compile QProg.qAssign
                (parallelMarkingOracle 1 S))
              (sliceState res 0 (2 * n) uVal Ξ₂))
        ≤ ∑ uVal ∈ Finset.range (2 ^ (2 * n)), stateMass Ξ * ENNReal.ofReal
              (if hu : uVal < 2 ^ (2 * n) then termR ⟨uVal, hu⟩ else 0) := by
          refine Finset.sum_le_sum fun uVal hu ↦ ?_
          have hlt := Finset.mem_range.mp hu; rw [dite_eq_left hlt]; exact (hbranch uVal hlt).2
      _ = stateMass Ξ * ∑ u : Fin (2 ^ (2 * n)), ENNReal.ofReal (termR u) := by
          rw [← Finset.mul_sum]; congr 1
          refine Finset.sum_bij (fun uVal hu ↦ ⟨uVal, Finset.mem_range.mp hu⟩)
            (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ congrArg Fin.val h)
            (fun u _ ↦ ⟨u.val, Finset.mem_range.mpr u.isLt, rfl⟩)
            fun uVal hu ↦ by simp [Finset.mem_range.mp hu]
      _ = stateMass Ξ * ENNReal.ofReal (∑ u : Fin (2 ^ (2 * n)), termR u) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun u _ ↦ hterm_nn u]
      _ ≤ stateMass Ξ * ENNReal.ofReal
            (((m1K32VTable 2 : ℝ) / (m1K32VScaleNat : ℝ)) * √(2 ^ n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
          dsimp only [termR]; rw [← Finset.mul_sum]
          let fPair (p : GaloisField 2 n × GaloisField 2 n) : ℝ :=
            if ha : p.1 = 0 then
              (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit
            else
              (q (R.map (GF2nForallA.finAffinePerm hn0 (Units.mk0 p.1 ha) p.2).toEmbedding) : ℝ)
          have hsum_pair : (∑ u : Fin (2 ^ (2 * n)), if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0
            then (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit else (q
            (R.map (GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
            (GF2nForallA.seedToGFPair hn0 u).2).toEmbedding) : ℝ)) = ∑ p : GaloisField 2 n ×
            GaloisField 2 n, fPair p := Fintype.sum_equiv (GF2nForallA.seedToGFPair hn0) _ fPair fun
            _ ↦ rfl; rw [hsum_pair, Fintype.sum_prod_type]; rw [← Finset.add_sum_erase _ _
            (Finset.mem_univ (0 : GaloisField 2 n))]
          have h0_sum : (∑ b : GaloisField 2 n, fPair (0, b)) = (2 ^ n : ℝ) * ((818309887 / 10 ^ 9 :
            ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit) := by
            dsimp only [fPair]; simp only [↓reduceDIte, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]; rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]; push_cast;
              rfl
          have hunit_sum : (∑ a ∈ (Finset.univ : Finset (GaloisField 2 n)).erase 0, ∑ b :
            GaloisField 2 n, fPair (a, b)) = ∑ p : (GaloisField 2 n)ˣ × GaloisField 2 n, (q (R.map
            (GF2nForallA.finAffinePerm hn0 p.1 p.2).toEmbedding) : ℝ) := by
            rw [Fintype.sum_prod_type]; symm; refine Finset.sum_bij (fun a _ ↦ (a : GaloisField 2
              n)) ?_ ?_ ?_ ?_
            · intro a _; exact Finset.mem_erase.mpr ⟨Units.ne_zero a, Finset.mem_univ _⟩
            · intro _ _ _ _ h; exact Units.ext h
            · intro a ha; exact ⟨Units.mk0 a (Finset.mem_erase.mp ha).1, Finset.mem_univ _, rfl⟩
            · intro a _; refine Finset.sum_congr rfl fun b _ ↦ ?_
              have hne : (a : GaloisField 2 n) ≠ 0 := Units.ne_zero a; dsimp only [fPair]
              rw [dite_eq_right hne, show Units.mk0 (a : GaloisField 2 n) hne = a from Units.ext
                rfl]
          rw [h0_sum, hunit_sum, GF2nForallA.sum_finAffinePerm_eq_two_mul_sum_targetSets hn0 (show
            R.card = 2 from hST2) (fun B ↦ (q B : ℝ))]
          have hcard2_pos : (0 : ℝ) < (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card :
            ℝ) := by
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
            exact_mod_cast Nat.choose_pos hkN2
          have hrel2 : ((longTailM1K2OnlyProfile.relCost 1 2 : ℚ≥0) : ℝ) = 379666241046199 /
            500000000000000 := by
            unfold longTailM1K2OnlyProfile relCostLongTailM1K2Only; simp only [beq_self_eq_true,
              Bool.and_self, ↓reduceIte]; push_cast; norm_num
          have hq_avg' : (∑ B ∈ GroverSol.groverTargetSets n 2, (q B : ℝ)) / (((Finset.univ :
            Finset (Fin (2 ^ n))).powersetCard 2).card : ℝ) ≤ uAvg * unit := by
            change (∑ B ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2, (q B : ℝ)) / _ ≤ _
            refine hq_avg.trans_eq ?_; rw [hrel2]; dsimp only [uAvg, unit]; push_cast; ring
          have h2card : (2 : ℝ) * (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card : ℝ) ≤
            (2 ^ (2 * n) : ℝ) := by
            have hnat : 2 * ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card ≤ 2 ^ (2 * n)
              := by
              rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
                two_mul_choose_two_two_pow_all, two_mul, pow_add]
              exact Nat.mul_le_mul_left (2 ^ n) (Nat.sub_le (2 ^ n) 1)
            exact_mod_cast hnat
          have hu_nn : 0 ≤ uAvg * unit := by
            dsimp only [uAvg, unit]
            have hs_nn : 0 ≤ ∑ r ∈ Finset.Icc (1 : ℕ) 2, (1 : ℝ) / √(r : ℝ) :=
              Finset.sum_nonneg fun _ _ ↦ by positivity
            positivity
          have hsum_q_le : 2 * ∑ B ∈ GroverSol.groverTargetSets n 2, (q B : ℝ) ≤ (2 ^ (2 * n) :
            ℝ) * (uAvg * unit) := by
            have h1 := (div_le_iff₀ hcard2_pos).mp hq_avg'
            calc 2 * ∑ B ∈ GroverSol.groverTargetSets n 2, (q B : ℝ)
                ≤ 2 * (uAvg * unit * ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card) :=
                  mul_le_mul_of_nonneg_left h1 zero_le_two
              _ = (2 * ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card) *
                    (uAvg * unit) := by ring
              _ ≤ (2 ^ (2 * n) : ℝ) * (uAvg * unit) :=
                  mul_le_mul_of_nonneg_right h2card hu_nn
          have hh2_ub : (∑ r ∈ Finset.Icc (1 : ℕ) 2, (1 : ℝ) / √(r : ℝ)) ≤ 1 + 707106781186547525 /
            10 ^ 18 := by
            have h12 : Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) :=
              (by ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega)
            rw [h12, Finset.sum_pair (by omega), Nat.cast_one, Real.sqrt_one, div_one,
              Nat.cast_ofNat]; have hs2_pos : (0 : ℝ) < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
            have hsq2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num); have hmul2 : (1 : ℝ) ≤
              (707106781186547525 / 10 ^ 18 : ℝ) * √(2 : ℝ) := (by nlinarith [hsq2, hs2_pos])
            linarith [(div_le_iff₀ hs2_pos).2 hmul2]
          have htail_le : (2 ^ n : ℝ) * ((818309887 / 10 ^ 9 : ℝ) *
            GroverSol.groverHarmonicSqrtSum 2 * unit) ≤ (2 ^ (2 * n) : ℝ) * ((1 / 10 ^ 16 : ℝ)
            * unit) := by
            have hh2_eq : GroverSol.groverHarmonicSqrtSum 2 = ∑ r ∈ Finset.Icc (1 : ℕ) 2, (1 :
              ℝ) / √(r : ℝ) := rfl
            have hpow_big : (2 * 10 ^ 16 : ℝ) ≤ (2 ^ n : ℝ) := by
              calc (2 * 10 ^ 16 : ℝ) ≤ (2 ^ 55 : ℝ) := by norm_num
                _ ≤ (2 ^ n : ℝ) := pow_le_pow_right₀ (by norm_num) (by omega)
            have h2n_2 : (2 ^ (2 * n) : ℝ) = (2 ^ n : ℝ) * (2 ^ n : ℝ) := by rw [two_mul, pow_add]
            have hu_pos : 0 ≤ unit := by dsimp only [unit]; positivity
            have hcoef : (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 ≤ 2 :=
              (by rw [hh2_eq]; nlinarith [hh2_ub]); rw [h2n_2]
            calc (2 ^ n : ℝ) *
                  ((818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit)
                ≤ (2 ^ n : ℝ) * (2 * unit) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hu_pos)
                    (by positivity)
              _ ≤ (2 ^ n : ℝ) * (((2 ^ n : ℝ) / 10 ^ 16) * unit) := by
                  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hu_pos)
                    (by positivity); linarith
              _ = (2 ^ n : ℝ) * (2 ^ n : ℝ) * ((1 / 10 ^ 16 : ℝ) * unit) := by ring
          have htot_le : (1 / (2 ^ (2 * n) : ℝ)) * ((2 ^ n : ℝ) * ((818309887 / 10 ^ 9 : ℝ) *
            GroverSol.groverHarmonicSqrtSum 2 * unit) + 2 * ∑ B ∈
            GroverSol.groverTargetSets n 2, (q B : ℝ)) ≤ (uAvg + 1 / 10 ^ 16) * unit := by
            have hadd := add_le_add htail_le hsum_q_le
            have hpow_pos : (0 : ℝ) < (2 ^ (2 * n) : ℝ) := by positivity
            calc (1 / (2 ^ (2 * n) : ℝ)) * _
                ≤ (1 / (2 ^ (2 * n) : ℝ)) * ((2 ^ (2 * n) : ℝ) * ((1 / 10 ^ 16 : ℝ) * unit) +
                      (2 ^ (2 * n) : ℝ) * (uAvg * unit)) :=
                  mul_le_mul_of_nonneg_left hadd (by positivity)
              _ = ((1 / (2 ^ (2 * n) : ℝ)) * (2 ^ (2 * n) : ℝ)) *
                    ((uAvg + 1 / 10 ^ 16) * unit) := by ring
              _ = (uAvg + 1 / 10 ^ 16) * unit := by rw [one_div_mul_cancel hpow_pos.ne', one_mul]
          refine htot_le.trans ?_; have hunit_eq : unit = (π / 4) * √(2 ^ n : ℝ) :=
            (by dsimp only [unit]; rw [div_one]); rw [hunit_eq, ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          have hpi : π < ((314159265358979 : ℝ) * 1000000 + 323847) / 10 ^ 20 :=
            (by have hp := Real.pi_lt_d20; norm_num at hp ⊢; linarith); have hv2_eq : ((m1K32VTable
            2 : ℝ) / (m1K32VScaleNat : ℝ)) = 10180815029781160 / 10000000000000000 :=
            (by have hv : m1K32VTableNat 2 = 10180815029781160 := rfl
                unfold m1K32VTable m1K32VScaleNat; rw [hv]; norm_num)
          rw [hv2_eq]; dsimp only [uAvg]; nlinarith [hh2_ub, hpi, Real.pi_pos]
private noncomputable def m1K32ColdCirc {Var : Type} (res : Var) (n k : ℕ) (hk_grid : k ∈
  GroverSol.groverGrid) (hk2 : 2 ≤ k) (r' : ℕ)
    (T' : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  if r' = 1 then lockSingleFromSetCircuit res n 1 k T' else m1K32R2FromSetCirc res n k hk_grid
    hk2 T'
private noncomputable def m1K32FromEmptyCirc {Var : Type} (res : Var) (n k : ℕ) (hk_grid : k ∈
  GroverSol.groverGrid) (hk2 : 2 ≤ k) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  hdistL50M1FromSetWithColdCircuit res m1K32Bundle (m1K32ColdCirc res n k hk_grid hk2) k ∅
private theorem m1K32FromEmpty_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var) {n k :
  ℕ} (hn : 600 ≤ n)
  (hk_grid : k ∈ GroverSol.groverGrid) (hk2 : 2 ≤ k) (hk32 : k ≤ 32) {S : Finset (Fin (2 ^
    n))} (hScard : S.card = k) {Δ : CQState (Store Var) (2 ^
  findAllQubits n 1 k)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (m1K32FromEmptyCirc res n k hk_grid hk2).compile QProg.qAssign
      (parallelMarkingOracle 1 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (((m1K32VTable k : ℝ) / (m1K32VScaleNat : ℝ)) * √(2 ^ n : ℝ)) :=
      by
  refine hdistL50M1FromSetWithCold_correct_and_cost res m1K32Bundle (m1K32ColdCirc res n k
    hk_grid hk2)
    (by omega : 128 ≤ n) (by omega : 1 ≤ k) (hk32 : k ≤ m1K32Bundle.kMax) le_rfl ?_ hScard
    (Finset.empty_subset S) (by simpa using hScard) hΔ
  intro r' T' hr1' _hrk' huse_f S' hS' hT'S' hrem' Δ' hΔ'; have hr_lt3 : r' < 3 :=
    (by simpa [m1K32Bundle] using huse_f); have hr12 : r' = 1 ∨ r' = 2 := (by omega)
  rcases hr12 with rfl | rfl
  · dsimp only [m1K32ColdCirc]; rw [ite_eq_left rfl]; have hrem_sub : k - T'.card = 1 :=
      (by have hs := Finset.card_sdiff_of_subset hT'S'; omega)
    obtain ⟨hexp, hcost⟩ := lockSingleFromSet_transition res (by omega : 100 ≤ n) le_rfl
      (by norm_num) (by omega : k ≤ 1024) hS' hT'S' hrem_sub hΔ'; refine ⟨hexp, hcost.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
    simp only [Nat.cast_one, div_one]; have hrel : ((relCostLock : ℚ≥0) : ℝ) = (4091549431 : ℝ) /
      5000000000 := (by unfold relCostLock; push_cast; norm_num); have hpi : π <
      ((314159265358979 : ℝ) * 1000000 + 323847) / 10 ^ 20 :=
      (by have hp := Real.pi_lt_d20; norm_num at hp ⊢; linarith)
    have hv1 : ((m1K32Bundle.vTable 1 : ℝ) / (m1K32Bundle.vScale : ℝ)) = 6426990820000000 /
      10000000000000000 := by
      change ((m1K32VTable 1 : ℝ) / (m1K32VScaleNat : ℝ)) = _
      have hv : m1K32VTableNat 1 = 6426990820000000 := rfl
      unfold m1K32VTable m1K32VScaleNat; rw [hv]; norm_num
    have hcoef : ((relCostLock : ℚ≥0) : ℝ) * (π / 4) ≤ (m1K32Bundle.vTable 1 : ℝ) /
      (m1K32Bundle.vScale : ℝ) := (by rw [hrel, hv1]; linarith)
    exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
  · dsimp only [m1K32ColdCirc]; rw [ite_eq_right (by omega : ¬ (2 = 1))]
    exact m1K32R2FromSet_transition res hn hk_grid hk2 hS' hT'S' hrem' Δ'
private theorem m1K32_cell_cases {k : ℕ} (hc : isSchurWeylL2BallM1K32OnlyCell 1 k = true) :
    k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 := by
  simp only [isSchurWeylL2BallM1K32OnlyCell, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    true_and] at hc; rcases hc with ((rfl | rfl) | rfl) | rfl <;> omega
private theorem m1K32_grid_of_cell {k : ℕ} (hc : isSchurWeylL2BallM1K32OnlyCell 1 k = true) :
    k ∈ GroverSol.groverGrid := by
  rcases m1K32_cell_cases hc with rfl | rfl | rfl | rfl
  · exact hk_grid_of_idx (by omega : 2 < 11) rfl
  · exact hk_grid_of_idx (by omega : 3 < 11) rfl
  · exact hk_grid_of_idx (by omega : 4 < 11) rfl
  · exact hk_grid_of_idx (by omega : 5 < 11) rfl
private theorem m1K32_ge2_of_cell {k : ℕ} (hc : isSchurWeylL2BallM1K32OnlyCell 1 k = true) :
    2 ≤ k := by rcases m1K32_cell_cases hc with rfl | rfl | rfl | rfl <;> omega
private theorem m1K32_le32_of_cell {k : ℕ} (hc : isSchurWeylL2BallM1K32OnlyCell 1 k = true) :
    k ≤ 32 := by rcases m1K32_cell_cases hc with rfl | rfl | rfl | rfl <;> omega
private theorem m1K32_cell_cert {k : ℕ} (hc : isSchurWeylL2BallM1K32OnlyCell 1 k = true) :
    ∃ kIdx relNum relDen : ℕ, k = 2 ^ kIdx ∧
      schurWeylL2BallM1K32OnlyProfile.relCost 1 k = (relNum : ℚ≥0) / (relDen : ℚ≥0) ∧
      SchurWeylLCert.checkSwLRelCostCell 0 kIdx (m1K32VTable k) relNum relDen = true := by
  rcases m1K32_cell_cases hc with rfl | rfl | rfl | rfl
  · exact ⟨2, 1798014765956261, 2500000000000000, rfl, rfl,
      m1K32BoolAnd2 (m1K32BoolAnd1 (m1K32BoolAnd1 (m1K32BoolAnd1 cert_m1K32_cells)))⟩
  · exact ⟨3, 173143829619399, 250000000000000, rfl, rfl,
      m1K32BoolAnd2 (m1K32BoolAnd1 (m1K32BoolAnd1 cert_m1K32_cells))⟩
  · exact ⟨4, 6751273712926893, 10000000000000000, rfl, rfl,
      m1K32BoolAnd2 (m1K32BoolAnd1 cert_m1K32_cells)⟩
  · exact ⟨5, 1328876209066213, 2000000000000000, rfl, rfl, m1K32BoolAnd2 cert_m1K32_cells⟩
end InternalM1K32
public section
/-- Native-`findAllQubits` circuit for `(m = 1, k ∈ {4, 8, 16, 32})` (`600 ≤ n`). -/
noncomputable def schurWeylL2BallM1K32OnlyCircuit {Var : Type} (res : Var) (n : ℕ) : ∀ (m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | 1, k =>
      if hk : isSchurWeylL2BallM1K32OnlyCell 1 k = true ∧ 600 ≤ n then
        m1K32FromEmptyCirc res n k (m1K32_grid_of_cell hk.1) (m1K32_ge2_of_cell hk.1)
      else findAllCircuit res (fun _ _ _ ↦ 0) n 1 k
  | m, k => findAllCircuit res (fun _ _ _ ↦ 0) n m k
private theorem schurWeylL2BallM1K32OnlyCircuit_m1 {Var : Type} (res : Var) (n k : ℕ) :
    schurWeylL2BallM1K32OnlyCircuit (Var := Var) res n 1 k =
      if hk : isSchurWeylL2BallM1K32OnlyCell 1 k = true ∧ 600 ≤ n then
        m1K32FromEmptyCirc res n k (m1K32_grid_of_cell hk.1) (m1K32_ge2_of_cell hk.1)
      else findAllCircuit res (fun _ _ _ ↦ 0) n 1 k := rfl
/-- End-to-end `ValidFindAllFamily` certificate for `schurWeylL2BallM1K32OnlyCircuit`. -/
theorem validFamily_schurWeylL2BallM1K32Only {Var : Type} [DecidableEq Var] (res : Var) :
    ValidFindAllFamily res schurWeylL2BallM1K32OnlyProfile
      (schurWeylL2BallM1K32OnlyCircuit res) where
  correctness {n m k S} _hn _hmk hvalid hkN hS := by
    have hm1 : m = 1 := by
      simp only [schurWeylL2BallM1K32OnlyProfile, isSchurWeylL2BallM1K32OnlyCell,
        Bool.and_eq_true, beq_iff_eq] at hvalid; exact hvalid.1
    subst hm1; change isSchurWeylL2BallM1K32OnlyCell 1 k = true at hvalid
    have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2
    by_cases hn600 : 600 ≤ n
    · intro Δ
      rw [schurWeylL2BallM1K32OnlyCircuit_m1, dite_eq_left ⟨hvalid, hn600⟩, expect_top,
        interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
      have hcorr := (m1K32FromEmpty_correct_and_cost res hn600 (m1K32_grid_of_cell hvalid)
        (m1K32_ge2_of_cell hvalid) (m1K32_le32_of_cell hvalid) hScard hsupp).1
      exact (hcorr.trans (congrArg ((↑) : ℝ≥0 → ℝ) (CQState.trace_qSet Δ))).symm.le
    · have hnot : ¬ (isSchurWeylL2BallM1K32OnlyCell 1 k = true ∧ 600 ≤ n) := fun h ↦ hn600 h.2
      rw [schurWeylL2BallM1K32OnlyCircuit_m1, dite_eq_right hnot]
      exact findAllProgram_correctness res (fun _ _ _ ↦ 0) le_rfl hScard hkN
        (fun r hr1 hrk ↦ p_succ_set_zero_pos hr1 (hrk.trans hkN))
  costBound_uniform {m k} _hmk hvalid n hn0 hkN := by
    have hm1 : m = 1 := by
      simp only [schurWeylL2BallM1K32OnlyProfile, isSchurWeylL2BallM1K32OnlyCell,
        Bool.and_eq_true, beq_iff_eq] at hvalid; exact hvalid.1
    subst hm1; change isSchurWeylL2BallM1K32OnlyCell 1 k = true at hvalid
    change 600 ≤ n at hn0
    set cVal : ℝ := ((m1K32VTable k : ℝ) / (m1K32VScaleNat : ℝ)) * √(2 ^ n : ℝ)
    have hv_nn : (0 : ℝ) ≤ (m1K32VTable k : ℝ) :=
      by unfold m1K32VTable; push_cast; exact Nat.cast_nonneg _
    have hsc_pos : (0 : ℝ) < (m1K32VScaleNat : ℝ) := by unfold m1K32VScaleNat; positivity
    let cNN : ℝ≥0 := ⟨cVal, mul_nonneg (div_nonneg hv_nn hsc_pos.le) (Real.sqrt_nonneg _)⟩
    refine ⟨fun _ ↦ cNN, ?_, ?_⟩
    · intro S hS Δ; have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2
      rw [schurWeylL2BallM1K32OnlyCircuit_m1, dite_eq_left ⟨hvalid, hn0⟩, expectedCost_qSeq,
        expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero, mul_zero,
        zero_add, interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
      have hmass_eq : stateMass Δ.qSet = stateMass Δ :=
        congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
      have hcb := (m1K32FromEmpty_correct_and_cost res hn0 (m1K32_grid_of_cell hvalid)
        (m1K32_ge2_of_cell hvalid) (m1K32_le32_of_cell hvalid) hScard hsupp).2
      have hcNN : (cNN : ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
      rw [hmass_eq] at hcb; refine hcb.trans ?_; rw [hcNN]
    · have hcard_pos : 0 < ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        exact Nat.choose_pos hkN
      have hcard_r : (0 : ℝ) < (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card : ℝ) :=
        Nat.cast_pos.2 hcard_pos
      obtain ⟨kIdx, relNum, relDen, hk_pow, hrel_eq, hcell⟩ := m1K32_cell_cert hvalid
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_r.ne', hrel_eq]
      change cVal ≤ (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) *
        ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (1 : ℕ)))
      have hrel_cast : (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) =
          (relNum : ℝ) / (relDen : ℝ) := by push_cast; rfl
      rw [hrel_cast]
      have hsound_cell := SchurWeylLCert.checkSwLRelCostCell_sound (n := n) hcell
      have hmu : (SchurWeylLCert.multiUnitScale : ℝ) = (m1K32VScaleNat : ℝ) := by
        unfold SchurWeylLCert.multiUnitScale m1K32VScaleNat; norm_num
      rw [hmu, pow_zero] at hsound_cell; simpa [cVal, ← hk_pow] using hsound_cell
end
end QuantumComputation.Specs.GroverFindAll
