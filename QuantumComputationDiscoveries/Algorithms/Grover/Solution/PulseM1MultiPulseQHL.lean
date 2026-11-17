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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLQHL
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistOverlap2L
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylL2BallCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PulseM1Grover1Step
/-
# Multi-Pulse `m = 1` Conveyor QHL Transition, Cascade Bundle & `RelCost` Bridge
Extends `SchurWeylHdistLQHL`, `SchurWeylHdistOverlap2L`, and `SchurWeylL2BallCertDefs` to
high-rank `2 ≤ L ≤ 1024` multi-pulse harmonic distinct-tuple (`H_dist`) conveyors at
fixed-point scale `swScale = 10^9`:
1. **Multi-pulse-rank zero-ancilla wire & overlap bounds (`2 ≤ L ≤ 1024`, `1152 ≤ n`)**:
   `swLWireBound_m1_le_findAllQubits_pulse` and `isValidSwLOverlap_swLOverlapMatFn_pulse`.
2. **Atomic GMP WHNF forcing, Heron `isqrt`, & `1`-ULP `2^16`-subdivision bucket angle
   checkers**: `solLitNat`, `solSeqInt`, `solFloorIsqrt`, `solCeilIsqrt`,
   `checkPulseTrigRat24`, `checkPulseStratumRatio`, `checkPulseBucketAngles`, and
   `checkPulseSingletonAngles`.
3. **Window-sparse zero-skip `L2Ball` trajectory & `O(L)` Parseval suffix `L^2` norm**:
   `SolSparsePulse`, `solEvolutionL2`, `swLOrbitProj_sub_id_normSq_le`,
   `solTerminalBoundsL2`, and `checkPulseBucketCertL2` (`≤ 66` ULPs overlap slack,
   `1 ≤ P ≤ 5120`).
4. **Non-monotone + dyadic landing credit Bellman cascade & `ValidFindAllFamily` splice**:
   `checkPulseCascadeStep`, `checkPulseCascadeStage_sound`, `PulseM1CertBundle` (`hNonneg`),
   `pulseM1FromSetWithColdCircuit`, and `validFamily_pulseOverColdM1`.
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
namespace PulseM1
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert hiding
  solIntAdd_eq solIntSub_eq solIntMul_eq solIntEdiv_eq
  solNatAdd_eq solNatSub_eq solNatMul_eq solNatDiv_eq
  solForceIntList solForceIntList_eq solBleZ solMinZ solMinZ_eq solMaxZ solMaxZ_eq
  solIsqrtInit solIsqrtLoop solFloorIsqrt solFloorIsqrt_eq solCeilIsqrt solCeilIsqrt_eq
  solSumSqAbs solSumSqAbs_eq checkPulseBucketAngles checkPulseBucketAngles_sound
open scoped BigOperators Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation
/- ## 1. Multi-pulse-Rank (`2 ≤ L ≤ 1024`, `1152 ≤ n`) Wire & Overlap Bounds -/
theorem swLWireBound_m1_le_findAllQubits_pulse {n L k : ℕ} (hL2 : 2 ≤ L) (hLk : L ≤ k) (hLn : L ≤
  n) : swLWireBound n 1 L ≤ findAllQubits n 1 k := by
  unfold swLWireBound findAllQubits; have h1 : (L - 1) * 1 * n + 1 * L ≤ (L - 1) * n + n :=
    (by have : 1 * L ≤ n := (by omega); linarith [show (L - 1) * 1 * n = (L - 1) * n by ring])
  have h2 : (L - 1) * n + n = L * n := by
    calc (L - 1) * n + n = (L - 1 + 1) * n := by ring
      _ = L * n := by rw [Nat.sub_add_cancel (by omega)]
  have h3 : L * n ≤ n * k := (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hLk); omega
theorem isValidSwLOverlap_swLOverlapMatFn_pulse {L n r : ℕ} (hL : 2 ≤ L) (hL1024 : L ≤ 1024) (hn :
  1152 ≤ n) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hr1024 : r ≤ 1024) (hR : R.card = r) :
  IsValidSwLOverlap (swLOverlapMatFn L R) :=
  GroverFindAll.isValidSwLOverlap_swLOverlapMatFn_pulse hL hL1024 hn hrL hr1024 hR
/- ## 2. Atomic GMP WHNF Primitives, Heron `isqrt`, & `1`-ULP `10^24` Angle Checkers -/
theorem solIntAdd_eq (a b : ℤ) : Int.add a b = a + b := rfl
theorem solIntSub_eq (a b : ℤ) : Int.sub a b = a - b := rfl
theorem solIntMul_eq (a b : ℤ) : Int.mul a b = a * b := rfl
theorem solIntEdiv_eq (a b : ℤ) : Int.ediv a b = a / b := rfl
theorem solIntNeg_eq (a : ℤ) : Int.neg a = -a := rfl
theorem solNatAdd_eq (a b : ℕ) : Nat.add a b = a + b := rfl
theorem solNatSub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem solNatMul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem solNatDiv_eq (a b : ℕ) : Nat.div a b = a / b := rfl
/-- Atomic GMP literal WHNF forcing on `ℕ` via `Nat.add 1 x` and `Nat.casesOn`. -/
def solLitNat {α : Type*} (x : ℕ) (k : ℕ → α) : α :=
  @Nat.casesOn (fun _ ↦ α) (Nat.add 1 x) (k 0) k
theorem solLitNat_eq {α : Type*} (x : ℕ) (k : ℕ → α) : solLitNat x k = k x := by
  unfold solLitNat; rw [solNatAdd_eq, Nat.one_add]
/-- Atomic GMP literal WHNF forcing on `ℤ` via `Int.casesOn` and `solLitNat`. -/
def solSeqInt {α : Type*} (x : ℤ) (k : ℤ → α) : α :=
  @Int.casesOn (fun _ ↦ α) x
    (fun n ↦ solLitNat n fun v ↦ k (Int.ofNat v))
    (fun n ↦ solLitNat n fun v ↦ k (Int.negSucc v))
theorem solSeqInt_eq {α : Type*} (x : ℤ) (k : ℤ → α) : solSeqInt x k = k x := by
  cases x <;> simp [solSeqInt, solLitNat_eq]
/-- Atomic WHNF forcing for `IvInt`. -/
def solSeqIv {α : Type*} (iv : IvInt) (k : IvInt → α) : α :=
  solSeqInt iv.1 fun lo ↦ solSeqInt iv.2 fun hi ↦ k (lo, hi)
theorem solSeqIv_eq {α : Type*} (iv : IvInt) (k : IvInt → α) : solSeqIv iv k = k iv := by
  rcases iv with ⟨lo, hi⟩; simp [solSeqIv, solSeqInt_eq]
/-- Head-constructor WHNF forcing for `List α` via `@List.casesOn`. -/
def solSeqList {α β : Type*} (xs : List α) (k : List α → β) : β :=
  @List.casesOn α (fun _ ↦ β) xs (k []) (fun hd tl ↦ k (hd :: tl))
theorem solSeqList_eq {α β : Type*} (xs : List α) (k : List α → β) : solSeqList xs k = k xs := by
  cases xs <;> rfl
/-- Tail-recursive spine + atomic element WHNF accumulator for `List ℤ`. -/
def solRevForceIntList : List ℤ → List ℤ → List ℤ
  | [], acc => acc
  | x :: xs, acc =>
      solSeqInt x fun x' ↦ solRevForceIntList xs (x' :: acc)
theorem solRevForceIntList_inv : ∀ (xs acc : List ℤ), solRevForceIntList (solRevForceIntList xs acc)
  [] = solRevForceIntList acc xs
  | [], _ => rfl
  | x :: xs, acc => by
    change solRevForceIntList (solSeqInt x fun x' ↦ solRevForceIntList xs (x' :: acc)) [] =
      solRevForceIntList acc (x :: xs); rw [solSeqInt_eq, solRevForceIntList_inv xs (x :: acc)]
    change (solSeqInt x fun x' ↦ solRevForceIntList acc (x' :: xs)) = solRevForceIntList acc (x ::
      xs); rw [solSeqInt_eq]
/-- CPS spine + element WHNF materializer for `List ℤ`. -/
def solWithIntList {α : Type*} (xs : List ℤ) (k : List ℤ → α) : α :=
  solSeqList (solRevForceIntList (solRevForceIntList xs []) []) k
theorem solWithIntList_eq {α : Type*} (xs : List ℤ) (k : List ℤ → α) : solWithIntList xs k = k xs :=
  by unfold solWithIntList; rw [solSeqList_eq, solRevForceIntList_inv xs []]; rfl
/-- Tail-recursive spine + atomic element WHNF accumulator for `List IvInt`. -/
def solRevForceIvList : List IvInt → List IvInt → List IvInt
  | [], acc => acc
  | iv :: ivs, acc =>
      solSeqIv iv fun iv' ↦ solRevForceIvList ivs (iv' :: acc)
theorem solRevForceIvList_inv : ∀ (ivs acc : List IvInt), solRevForceIvList (solRevForceIvList ivs
  acc) [] = solRevForceIvList acc ivs
  | [], _ => rfl
  | iv :: ivs, acc => by
    change solRevForceIvList (solSeqIv iv fun iv' ↦ solRevForceIvList ivs (iv' :: acc)) [] =
      solRevForceIvList acc (iv :: ivs); rw [solSeqIv_eq, solRevForceIvList_inv ivs (iv :: acc)]
    change (solSeqIv iv fun iv' ↦ solRevForceIvList acc (iv' :: ivs)) = solRevForceIvList acc (iv ::
      ivs); rw [solSeqIv_eq]
/-- CPS spine + element WHNF materializer for `List IvInt`. -/
def solWithIvList {α : Type*} (ivs : List IvInt) (k : List IvInt → α) : α :=
  solSeqList (solRevForceIvList (solRevForceIvList ivs []) []) k
theorem solWithIvList_eq {α : Type*} (ivs : List IvInt) (k : List IvInt → α) : solWithIvList ivs k =
  k ivs := by unfold solWithIvList; rw [solSeqList_eq, solRevForceIvList_inv ivs []]; rfl
/-- Atomic WHNF forcing for `(IvInt × IvInt)` trig interval pairs. -/
def solSeqTrig {α : Type*} (p : IvInt × IvInt) (k : IvInt × IvInt → α) : α :=
  solSeqIv p.1 fun c ↦ solSeqIv p.2 fun s ↦ k (c, s)
theorem solSeqTrig_eq {α : Type*} (p : IvInt × IvInt) (k : IvInt × IvInt → α) : solSeqTrig p k = k p
  := by rcases p with ⟨c, s⟩; simp [solSeqTrig, solSeqIv_eq]
/-- Tail-recursive spine + atomic element WHNF accumulator for `List (IvInt × IvInt)`. -/
def solRevForceTrigList : List (IvInt × IvInt) → List (IvInt × IvInt) → List (IvInt × IvInt)
  | [], acc => acc
  | p :: ps, acc =>
      solSeqTrig p fun p' ↦ solRevForceTrigList ps (p' :: acc)
theorem solRevForceTrigList_inv : ∀ (ps acc : List (IvInt × IvInt)), solRevForceTrigList
  (solRevForceTrigList ps acc) [] = solRevForceTrigList acc ps
  | [], _ => rfl
  | p :: ps, acc => by
    change solRevForceTrigList (solSeqTrig p fun p' ↦ solRevForceTrigList ps (p' :: acc)) [] =
      solRevForceTrigList acc (p :: ps); rw [solSeqTrig_eq, solRevForceTrigList_inv ps (p :: acc)]
    change (solSeqTrig p fun p' ↦ solRevForceTrigList acc (p' :: ps)) = solRevForceTrigList acc (p
      :: ps); rw [solSeqTrig_eq]
/-- CPS spine + element WHNF materializer for `List (IvInt × IvInt)`. -/
def solWithTrigList {α : Type*} (ps : List (IvInt × IvInt))
    (k : List (IvInt × IvInt) → α) : α :=
  solSeqList (solRevForceTrigList (solRevForceTrigList ps []) []) k
theorem solWithTrigList_eq {α : Type*} (ps : List (IvInt × IvInt)) (k : List (IvInt × IvInt) → α) :
  solWithTrigList ps k = k ps := by
  unfold solWithTrigList; rw [solSeqList_eq, solRevForceTrigList_inv ps []]; rfl
theorem natBle_eq_decide : ∀ (a b : ℕ), Nat.ble a b = decide (a ≤ b)
  | 0, _ => (by simp [Nat.ble]) | _ + 1, 0 => (by simp [Nat.ble])
  | a + 1, b + 1 => by simp only [Nat.ble, natBle_eq_decide a b, Nat.add_le_add_iff_right]
/-- Pure-GMP `min` on `ℕ` via `bif` and `Nat.ble`. -/
def solMinNat (a b : ℕ) : ℕ :=
  cond (Nat.ble a b) a b
theorem solMinNat_eq (a b : ℕ) : solMinNat a b = min a b := by
  unfold solMinNat; rw [natBle_eq_decide]; by_cases h : a ≤ b
  · rw [decide_eq_true h, min_eq_left h]; rfl
  · rw [decide_eq_false h, min_eq_right (by omega : b ≤ a)]; rfl
/-- Pure-GMP `max` on `ℕ` via `bif` and `Nat.ble`. -/
def solMaxNat (a b : ℕ) : ℕ :=
  cond (Nat.ble a b) b a
theorem solMaxNat_eq (a b : ℕ) : solMaxNat a b = max a b := by
  unfold solMaxNat; rw [natBle_eq_decide]; by_cases h : a ≤ b
  · rw [decide_eq_true h, max_eq_right h]; rfl
  · rw [decide_eq_false h, max_eq_left (by omega : b ≤ a)]; rfl
/-- Pure-GMP constructor-matched `≤` on `ℤ`. -/
def solBleZ : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m
theorem solBleZ_eq_decide (a b : ℤ) : solBleZ a b = decide (a ≤ b) := by
  rcases a with m | m <;> rcases b with n | n
  · simp only [solBleZ, natBle_eq_decide]; congr 1; exact propext Int.ofNat_le.symm
  · simp only [solBleZ, Int.ofNat_eq_natCast]; symm; rw [decide_eq_false_iff_not]; omega
  · simp only [solBleZ, Int.ofNat_eq_natCast]; symm; rw [decide_eq_true_eq]; omega
  · simp only [solBleZ, natBle_eq_decide]; congr 1; exact propext (by omega)
/-- Pure-GMP constructor-matched `=` on `ℤ`. -/
def solBeqZ : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.beq m n
  | .negSucc m, .negSucc n => Nat.beq m n
  | _, _ => false
theorem solBeqZ_eq_decide (a b : ℤ) : solBeqZ a b = decide (a = b) := by
  rcases a with m | m <;> rcases b with n | n
  · simp only [solBeqZ, natBeq_eq_decide, Int.ofNat.injEq]
  · simp [solBeqZ]
  · simp [solBeqZ]
  · simp only [solBeqZ, natBeq_eq_decide, Int.negSucc.injEq]
/-- Pure-GMP structural equality check on `List ℤ`. -/
def solListIntBeq : List ℤ → List ℤ → Bool
  | [], ys =>
      match ys with
      | [] => true
      | _ :: _ => false
  | x :: xs, ys =>
      match ys with
      | [] => false
      | y :: ys' => solBeqZ x y && solListIntBeq xs ys'
theorem solListIntBeq_eq_true : ∀ (xs ys : List ℤ), solListIntBeq xs ys = true → xs = ys
  | [], [], _ => rfl | [], _ :: _, h => (by simp [solListIntBeq] at h)
  | _ :: _, [], h => by simp [solListIntBeq] at h
  | x :: xs, y :: ys, h => by
    simp only [solListIntBeq, Bool.and_eq_true, solBeqZ_eq_decide, decide_eq_true_eq] at h; rw [h.1,
      solListIntBeq_eq_true xs ys h.2]
/-- Pure-GMP `min` on `ℤ` via `bif` and `solBleZ`. -/
def solMinZ (a b : ℤ) : ℤ :=
  cond (solBleZ a b) a b
theorem solMinZ_eq (a b : ℤ) : solMinZ a b = min a b := by
  unfold solMinZ; rw [solBleZ_eq_decide]; by_cases h : a ≤ b
  · rw [decide_eq_true h, min_eq_left h]; rfl
  · rw [decide_eq_false h, min_eq_right (by omega : b ≤ a)]; rfl
/-- Pure-GMP `max` on `ℤ` via `bif` and `solBleZ`. -/
def solMaxZ (a b : ℤ) : ℤ :=
  cond (solBleZ a b) b a
theorem solMaxZ_eq (a b : ℤ) : solMaxZ a b = max a b := by
  unfold solMaxZ; rw [solBleZ_eq_decide]; by_cases h : a ≤ b
  · rw [decide_eq_true h, max_eq_right h]; rfl
  · rw [decide_eq_false h, max_eq_left (by omega : b ≤ a)]; rfl
/-- Initial Heron overestimate `g₀ ≥ ⌊√n⌋` for `1 ≤ n ≤ 2^64`. -/
def solIsqrtInit (n : ℕ) : ℕ :=
  cond (Nat.ble n 256)
    16
    (
    cond (Nat.ble n 65536)
    256
    (
    cond (Nat.ble n 16777216)
    4096
    (
    cond (Nat.ble n 4294967296)
    65536
    (
    cond (Nat.ble n 281474976710656)
    16777216
    (
    cond (Nat.ble n 18446744073709551616)
    4294967296
    n)))))
/-- Structural-fuel Heron loop (`O(1)` GMP divisions, zero `WellFounded.fix`). -/
def solIsqrtLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
      solLitNat (Nat.div (Nat.add g (Nat.div n g)) 2) fun g' ↦
        cond (Nat.ble g g') g (solIsqrtLoop fuel n g')
/-- Self-certifying pure-GMP `⌊√n⌋` (`= Nat.sqrt n`, zero binary-search unfolding in WHNF). -/
def solFloorIsqrt (n : ℕ) : ℕ :=
  Nat.casesOn n 0 fun nPred ↦
    solLitNat (Nat.add 1 nPred) fun n1 ↦
      solLitNat (solIsqrtLoop 40 n1 (solIsqrtInit n1)) fun s ↦
        cond
          (Nat.ble (Nat.mul s s) n1 &&
             Nat.ble (Nat.add 1 n1) (Nat.mul (Nat.add 1 s) (Nat.add 1 s)))
          s
          (Nat.sqrt n1)
theorem solFloorIsqrt_eq (n : ℕ) : solFloorIsqrt n = Nat.sqrt n := by
  cases n with
  | zero => rfl
  | succ nPred =>
    unfold solFloorIsqrt; dsimp only; rw [solLitNat_eq, solLitNat_eq]
    set s := solIsqrtLoop 40 (Nat.add 1 nPred) (solIsqrtInit (Nat.add 1 nPred))
    cases hcond : (Nat.ble (Nat.mul s s) (Nat.add 1 nPred) && Nat.ble (Nat.add 1 (Nat.add 1 nPred))
      (Nat.mul (Nat.add 1 s) (Nat.add 1 s)))
    · change Nat.sqrt (Nat.add 1 nPred) = Nat.sqrt (nPred + 1); rw [solNatAdd_eq, Nat.add_comm]
    · change s = Nat.sqrt (nPred + 1)
      simp only [Bool.and_eq_true, natBle_eq_decide, decide_eq_true_eq, solNatAdd_eq,
        solNatMul_eq] at hcond; exact Nat.eq_sqrt.mpr ⟨by omega, by nlinarith⟩
/-- Self-certifying pure-GMP `⌈√n⌉` (`= ceilIsqrtNat n`). -/
def solCeilIsqrt (n : ℕ) : ℕ :=
  solLitNat (solFloorIsqrt n) fun s ↦
    cond (Nat.beq (Nat.mul s s) n) s (Nat.succ s)
theorem solCeilIsqrt_eq (n : ℕ) : solCeilIsqrt n = ceilIsqrtNat n := by
  unfold solCeilIsqrt ceilIsqrtNat; rw [solLitNat_eq, withForcedNat_eq, solFloorIsqrt_eq]
/-- Constructor-matched tail-recursive sum of squared magnitudes (`= swLSumSqAbs`). -/
def solSumSqAbs : List ℤ → ℕ → ℕ
  | [], acc => acc
  | .ofNat n :: cjs, acc =>
      solLitNat (Nat.add acc (Nat.mul n n)) fun acc' ↦
        solSumSqAbs cjs acc'
  | .negSucc n :: cjs, acc =>
      solLitNat (Nat.add 1 n) fun m ↦
        solLitNat (Nat.add acc (Nat.mul m m)) fun acc' ↦
          solSumSqAbs cjs acc'
theorem solSumSqAbs_eq : ∀ (xs : List ℤ) (acc : ℕ), solSumSqAbs xs acc = swLSumSqAbs xs acc
  | [], _ => rfl
  | .ofNat n :: cjs, acc => by
    unfold solSumSqAbs swLSumSqAbs; simp only [solLitNat_eq, withForcedNat_eq]
    exact solSumSqAbs_eq cjs _
  | .negSucc n :: cjs, acc => by
    unfold solSumSqAbs swLSumSqAbs; simp only [solLitNat_eq, withForcedNat_eq, Int.natAbs_negSucc]
    rw [show Nat.add 1 n = n + 1 from Nat.add_comm 1 n]; exact solSumSqAbs_eq cjs _
/-- Atomic-WHNF `10^9`-scale interval multiplication (`= ivMulInt`). -/
def solIvMul (a b : IvInt) : IvInt :=
  solSeqInt (Int.mul a.1 b.1) fun p1 ↦
    solSeqInt (Int.mul a.1 b.2) fun p2 ↦
      solSeqInt (Int.mul a.2 b.1) fun p3 ↦
        solSeqInt (Int.mul a.2 b.2) fun p4 ↦
          solSeqInt (solMinZ (solMinZ p1 p2) (solMinZ p3 p4)) fun lo ↦
            solSeqInt (solMaxZ (solMaxZ p1 p2) (solMaxZ p3 p4)) fun hi ↦
              (Int.ediv lo swScale, ceilDivScaleP hi)
theorem solIvMul_eq (a b : IvInt) : solIvMul a b = ivMulInt a b := by
  unfold solIvMul ivMulInt; simp only [solSeqInt_eq, withForcedInt_eq, solMinZ_eq, solMaxZ_eq]; rfl
/-- Fast `2`-product `10^9`-scale interval-by-scalar multiplication (`= ivMulInt a (c, c)`). -/
def solIvScaleZ (a : IvInt) (c : ℤ) : IvInt :=
  solSeqInt (Int.mul a.1 c) fun p1 ↦
    solSeqInt (Int.mul a.2 c) fun p2 ↦
      cond (solBleZ p1 p2)
        (Int.ediv p1 swScale, ceilDivScaleP p2)
        (Int.ediv p2 swScale, ceilDivScaleP p1)
theorem solIvScaleZ_eq (a : IvInt) (c : ℤ) : solIvScaleZ a c = ivMulInt a (c, c) := by
  rw [← solIvMul_eq]; unfold solIvScaleZ solIvMul; dsimp only; simp only [solSeqInt_eq, solMinZ_eq,
    solMaxZ_eq, min_self, max_self]; rw [solBleZ_eq_decide]
  by_cases h : Int.mul a.1 c ≤ Int.mul a.2 c
  · rw [decide_eq_true h, Bool.cond_true, min_eq_left h, max_eq_right h]
  · have h' : Int.mul a.2 c ≤ Int.mul a.1 c := (not_le.mp h).le; rw [decide_eq_false h,
      Bool.cond_false, min_eq_right h', max_eq_left h']
/-- Atomic-WHNF `10^9`-scale interval squaring (`= ivSqInt`). -/
def solIvSq (a : IvInt) : IvInt :=
  cond (solBleZ 0 a.1)
    (Int.ediv (Int.mul a.1 a.1) swScale, ceilDivScaleP (Int.mul a.2 a.2))
    (
    cond (solBleZ a.2 0)
    (Int.ediv (Int.mul a.2 a.2) swScale, ceilDivScaleP (Int.mul a.1 a.1))
    (
      solSeqInt (solMaxZ (Int.neg a.1) a.2) fun m ↦
      (0, ceilDivScaleP (Int.mul m m))))
theorem solIvSq_eq (a : IvInt) : solIvSq a = ivSqInt a := by
  unfold solIvSq ivSqInt; rw [solBleZ_eq_decide, solBleZ_eq_decide, solMaxZ_eq]; by_cases h1 : 0 ≤
    a.1
  · simp only [h1, decide_true, Bool.cond_true, ↓reduceIte]; rfl
  · simp only [h1, decide_false, Bool.cond_false, ↓reduceIte]; by_cases h2 : a.2 ≤ 0
    · simp only [h2, decide_true, Bool.cond_true, ↓reduceIte]; rfl
    · simp only [h2, decide_false, Bool.cond_false, ↓reduceIte, solSeqInt_eq, withForcedInt_eq]; rfl
/-- Atomic-WHNF `10^9`-scale outward rational interval (`= ivRatDiv`). -/
def solIvRatDiv (num den : ℤ) : IvInt :=
  solSeqInt (Int.mul num swScale) fun sc ↦
    (Int.ediv sc den, Int.neg (Int.ediv (Int.neg sc) den))
theorem solIvRatDiv_eq (num den : ℤ) : solIvRatDiv num den = ivRatDiv num den := by
  unfold solIvRatDiv ivRatDiv; rw [solSeqInt_eq, withForcedInt_eq]; rfl
/-- Atomic-WHNF `10^9`-scale Pythagorean `(cos, sin)` intervals (`= ivPythag`). -/
def solIvPythag (uNum uDen : ℤ) : IvInt × IvInt :=
  solSeqInt (Int.add (Int.mul uDen uDen) (Int.mul uNum uNum)) fun d ↦
    solSeqIv (solIvRatDiv (Int.sub (Int.mul uDen uDen) (Int.mul uNum uNum)) d) fun cu ↦
      solSeqIv (solIvRatDiv (Int.mul (Int.mul 2 uNum) uDen) d) fun su ↦
        (cu, su)
theorem solIvPythag_eq (uNum uDen : ℤ) : solIvPythag uNum uDen = ivPythag uNum uDen := by
  unfold solIvPythag ivPythag; rw [solSeqInt_eq, solSeqIv_eq, solSeqIv_eq, withForcedInt_eq,
    solIvRatDiv_eq, solIvRatDiv_eq]; rfl
/-- Atomic-WHNF midpoint and half-width (`= ivMidRad`). -/
def solIvMidRad (iv : IvInt) : ℤ × ℕ :=
  solSeqInt (Int.ediv (Int.add iv.1 iv.2) 2) fun mid ↦
    solLitNat (solMaxZ (Int.sub mid iv.1) (Int.sub iv.2 mid)).toNat fun rad ↦
      (mid, rad)
theorem solIvMidRad_eq (iv : IvInt) : solIvMidRad iv = ivMidRad iv := by
  simp [solIvMidRad, ivMidRad, solSeqInt_eq, solLitNat_eq, withForcedInt_eq, solMaxZ_eq, maxZ_eq]
/-- Atomic-WHNF `O(L)` recentering and squared-radius sum (`= swLRecenterAndRadSq`). -/
def solRecenterAndRadSq : List IvInt → List ℤ × ℕ
  | [] => ([], 0)
  | iv :: ivs =>
      match solIvMidRad iv, solRecenterAndRadSq ivs with
      | (mid, rad), (cs, acc) =>
          solSeqInt mid fun mid' ↦
            solLitNat (Nat.add (Nat.mul rad rad) acc) fun acc' ↦
              (mid' :: cs, acc')
theorem solRecenterAndRadSq_eq : ∀ (ivs : List IvInt), solRecenterAndRadSq ivs = swLRecenterAndRadSq
  ivs
  | [] => rfl
  | iv :: ivs => by
    unfold solRecenterAndRadSq swLRecenterAndRadSq; rw [solIvMidRad_eq, solRecenterAndRadSq_eq ivs];
      rcases ivMidRad iv with ⟨mid, rad⟩; rcases swLRecenterAndRadSq ivs with ⟨cs, acc⟩
    simp [solSeqInt_eq, solLitNat_eq, withForcedInt_eq, forceListId_eq, withForcedNat_eq]
/-- Internal `10^24` scale for `1`-ULP `2^16`-subdivision trig bounds across all `L ≤ 1024`. -/
def solS24 : ℤ := 1000000000000000000000000
/-- Ratio `solS24 / swScale = 10^15`. -/
def solScale15 : ℤ := 1000000000000000
/-- Structural `k`-step `10^24`-scale `(sin, cos)` double-angle lower-bound loop. -/
def solDoubleSinCosLo : ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, s, c => (s, c)
  | k + 1, s, c =>
      solSeqInt (solMaxZ 0 (Int.ediv (Int.mul 2 (Int.mul s c)) solS24)) fun s' ↦
        solSeqInt (solMaxZ 0 (Int.sub (Int.ediv (Int.mul 2 (Int.mul c c)) solS24) solS24))
          fun c' ↦ solDoubleSinCosLo k s' c'
/-- Structural `k`-step `10^24`-scale `cos` double-angle lower-bound loop. -/
def solDoubleCosLo : ℕ → ℤ → ℤ
  | 0, c => c
  | k + 1, c =>
      solSeqInt (solMaxZ 0 (Int.sub (Int.ediv (Int.mul 2 (Int.mul c c)) solS24) solS24))
        fun c' ↦ solDoubleCosLo k c'
theorem solDoubleCosLo_sound : ∀ (k : ℕ) (c : ℤ) (θ : ℝ), 0 ≤ c → 0 ≤ θ → (2 : ℝ) ^ k * θ ≤ 1 → (c :
  ℝ) / (solS24 : ℝ) ≤ Real.cos θ → 0 ≤ solDoubleCosLo k c ∧ (solDoubleCosLo k c : ℝ) / (solS24 : ℝ)
  ≤ Real.cos ((2 : ℝ) ^ k * θ)
  | 0, c, θ, hc0, _, _, hcos => by simpa [solDoubleCosLo] using ⟨hc0, hcos⟩
  | k + 1, c, θ, hc0, hθ0, hθ1, hcos => by
    have hs24_pos : (0 : ℤ) < solS24 := (by unfold solS24; norm_num); have hs24_r : (0 : ℝ) <
      (solS24 : ℝ) := (by unfold solS24; norm_num); have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
      one_le_pow₀ (by norm_num)
    have h2θ_le1 : 2 * θ ≤ 1 := by
      have h1 : 1 * (2 * θ) ≤ (2 : ℝ) ^ k * (2 * θ) := mul_le_mul_of_nonneg_right h2k_ge1
        (by linarith); have h2 : (2 : ℝ) ^ k * (2 * θ) = (2 : ℝ) ^ (k + 1) * θ := (by ring);
        linarith
    have hcos2_nn : 0 ≤ Real.cos (2 * θ) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    set raw : ℤ := Int.sub (Int.ediv (Int.mul 2 (Int.mul c c)) solS24) solS24
    set c' : ℤ := solMaxZ 0 raw; have hc'0 : 0 ≤ c' :=
      (by dsimp [c']; rw [solMaxZ_eq]; exact le_max_left 0 raw)
    have hraw_le : (raw : ℝ) / (solS24 : ℝ) ≤ Real.cos (2 * θ) := by
      have hd := ediv_pos_le_real (2 * (c * c)) solS24 hs24_pos
      have hsub : (raw : ℝ) ≤ ((2 * (c * c) : ℤ) : ℝ) / (solS24 : ℝ) - (solS24 : ℝ) := by
        change (((2 * (c * c)) / solS24 - solS24 : ℤ) : ℝ) ≤ _; rw [Int.cast_sub]; linarith [hd]
      have hdiv := div_le_div_of_nonneg_right hsub hs24_r.le; have halg : (((2 * (c * c) : ℤ) : ℝ) /
        (solS24 : ℝ) - (solS24 : ℝ)) / (solS24 : ℝ) = 2 * ((c : ℝ) / (solS24 : ℝ)) ^ 2 - 1 :=
        (by push_cast; field_simp [hs24_r.ne']); have hc_r : 0 ≤ (c : ℝ) / (solS24 : ℝ) :=
        div_nonneg (by exact_mod_cast hc0) hs24_r.le; have hsq : ((c : ℝ) / (solS24 : ℝ)) ^ 2 ≤
        (Real.cos θ) ^ 2 := pow_le_pow_left₀ hc_r hcos 2; have h2c : Real.cos (2 * θ) = 2 *
        (Real.cos θ) ^ 2 - 1 := Real.cos_two_mul θ; linarith
    have hc'_le : (c' : ℝ) / (solS24 : ℝ) ≤ Real.cos (2 * θ) := by
      dsimp [c']; rw [solMaxZ_eq, Int.cast_max, Int.cast_zero]
      rcases le_total (0 : ℝ) (raw : ℝ) with h | h
      · rw [max_eq_right h]; exact hraw_le
      · rw [max_eq_left h, zero_div]; exact hcos2_nn
    unfold solDoubleCosLo; rw [solSeqInt_eq]
    have hpow2 : (2 : ℝ) ^ k * (2 * θ) = (2 : ℝ) ^ (k + 1) * θ := (by ring); have hih :=
      solDoubleCosLo_sound k c' (2 * θ) hc'0 (by linarith) (by linarith [hpow2]) hc'_le
    rwa [hpow2] at hih
theorem solDoubleSinCosLo_sound : ∀ (k : ℕ) (s c : ℤ) (θ : ℝ), 0 ≤ s → 0 ≤ c → 0 ≤ θ → (2 : ℝ) ^ k *
  θ ≤ 1 → (s : ℝ) / (solS24 : ℝ) ≤ Real.sin θ → (c : ℝ) / (solS24 : ℝ) ≤ Real.cos θ → 0 ≤
  (solDoubleSinCosLo k s c).1 ∧ 0 ≤ (solDoubleSinCosLo k s c).2 ∧ ((solDoubleSinCosLo k s c).1 : ℝ)
  / (solS24 : ℝ) ≤ Real.sin ((2 : ℝ) ^ k * θ) ∧ ((solDoubleSinCosLo k s c).2 : ℝ) / (solS24 : ℝ) ≤
  Real.cos ((2 : ℝ) ^ k * θ)
  | 0, s, c, θ, hs0, hc0, _, _, hsin, hcos => by
    simpa [solDoubleSinCosLo] using ⟨hs0, hc0, hsin, hcos⟩
  | k + 1, s, c, θ, hs0, hc0, hθ0, hθ1, hsin, hcos => by
    have hs24_pos : (0 : ℤ) < solS24 := (by unfold solS24; norm_num); have hs24_r : (0 : ℝ) <
      (solS24 : ℝ) := (by unfold solS24; norm_num); have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
      one_le_pow₀ (by norm_num)
    have h2θ_le1 : 2 * θ ≤ 1 := by
      have h1 : 1 * (2 * θ) ≤ (2 : ℝ) ^ k * (2 * θ) := mul_le_mul_of_nonneg_right h2k_ge1
        (by linarith); have h2 : (2 : ℝ) ^ k * (2 * θ) = (2 : ℝ) ^ (k + 1) * θ := (by ring);
        linarith
    have hsin2_nn : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_gt_three]); have hcos2_nn : 0 ≤ Real.cos (2 * θ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    set sRaw : ℤ := Int.ediv (Int.mul 2 (Int.mul s c)) solS24; set cRaw : ℤ := Int.sub (Int.ediv
      (Int.mul 2 (Int.mul c c)) solS24) solS24
    set s' : ℤ := solMaxZ 0 sRaw; set c' : ℤ := solMaxZ 0 cRaw; have hs'0 : 0 ≤ s' :=
      (by dsimp [s']; rw [solMaxZ_eq]; exact le_max_left 0 sRaw); have hc'0 : 0 ≤ c' :=
      (by dsimp [c']; rw [solMaxZ_eq]; exact le_max_left 0 cRaw); have hs_r : 0 ≤ (s : ℝ) / (solS24
      : ℝ) := div_nonneg (by exact_mod_cast hs0) hs24_r.le
    have hc_r : 0 ≤ (c : ℝ) / (solS24 : ℝ) := div_nonneg (by exact_mod_cast hc0) hs24_r.le
    have hsRaw_le : (sRaw : ℝ) / (solS24 : ℝ) ≤ Real.sin (2 * θ) := by
      have hd := ediv_pos_le_real (2 * (s * c)) solS24 hs24_pos; have hdiv :=
        div_le_div_of_nonneg_right hd hs24_r.le
      have halg : ((2 * (s * c) : ℤ) : ℝ) / (solS24 : ℝ) / (solS24 : ℝ) = 2 * ((s : ℝ) / (solS24 :
        ℝ)) * ((c : ℝ) / (solS24 : ℝ)) := (by push_cast; field_simp [hs24_r.ne'])
      have hm : ((s : ℝ) / (solS24 : ℝ)) * ((c : ℝ) / (solS24 : ℝ)) ≤ Real.sin θ * Real.cos θ :=
        mul_le_mul hsin hcos hc_r (hs_r.trans hsin); have h2s : Real.sin (2 * θ) = 2 * Real.sin θ *
        Real.cos θ := Real.sin_two_mul θ; change (((2 * (s * c)) / solS24 : ℤ) : ℝ) / (solS24 : ℝ) ≤
        _; linarith
    have hcRaw_le : (cRaw : ℝ) / (solS24 : ℝ) ≤ Real.cos (2 * θ) := by
      have hd := ediv_pos_le_real (2 * (c * c)) solS24 hs24_pos
      have hsub : (cRaw : ℝ) ≤ ((2 * (c * c) : ℤ) : ℝ) / (solS24 : ℝ) - (solS24 : ℝ) := by
        change (((2 * (c * c)) / solS24 - solS24 : ℤ) : ℝ) ≤ _; rw [Int.cast_sub]; linarith [hd]
      have hdiv := div_le_div_of_nonneg_right hsub hs24_r.le; have halg : (((2 * (c * c) : ℤ) : ℝ) /
        (solS24 : ℝ) - (solS24 : ℝ)) / (solS24 : ℝ) = 2 * ((c : ℝ) / (solS24 : ℝ)) ^ 2 - 1 :=
        (by push_cast; field_simp [hs24_r.ne']); have hsq : ((c : ℝ) / (solS24 : ℝ)) ^ 2 ≤ (Real.cos
        θ) ^ 2 := pow_le_pow_left₀ hc_r hcos 2; have h2c : Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 -
        1 := Real.cos_two_mul θ; linarith
    have hs'_le : (s' : ℝ) / (solS24 : ℝ) ≤ Real.sin (2 * θ) := by
      dsimp [s']; rw [solMaxZ_eq, Int.cast_max, Int.cast_zero]
      rcases le_total (0 : ℝ) (sRaw : ℝ) with h | h
      · rw [max_eq_right h]; exact hsRaw_le
      · rw [max_eq_left h, zero_div]; exact hsin2_nn
    have hc'_le : (c' : ℝ) / (solS24 : ℝ) ≤ Real.cos (2 * θ) := by
      dsimp [c']; rw [solMaxZ_eq, Int.cast_max, Int.cast_zero]
      rcases le_total (0 : ℝ) (cRaw : ℝ) with h | h
      · rw [max_eq_right h]; exact hcRaw_le
      · rw [max_eq_left h, zero_div]; exact hcos2_nn
    unfold solDoubleSinCosLo; rw [solSeqInt_eq, solSeqInt_eq]; have hpow2 : (2 : ℝ) ^ k * (2 * θ) =
      (2 : ℝ) ^ (k + 1) * θ := (by ring)
    have hih := solDoubleSinCosLo_sound k s' c' (2 * θ) hs'0 hc'0 (by linarith)
      (by linarith [hpow2]) hs'_le hc'_le
    rwa [hpow2] at hih
/-- `1`-ULP `10^24`-scaled `2^16`-subdivision trig checker on `[a / d, b / e] ⊆ (0, 1]`,
  checking Pythagorean upper bounds before truncating to `swScale = 10^9`. -/
def checkPulseTrigRat24 (a d b e cLo cHi sLo sHi : ℤ) : Bool :=
  let mSq6 : ℤ := 25769803776
  let mCu6 : ℤ := 1688849860263936
  let mSq2 : ℤ := 8589934592
  solSeqInt (Int.ediv (Int.mul a solS24) d) fun qLoLo ↦
    solSeqInt (Int.neg (Int.ediv (Int.neg (Int.mul a solS24)) d)) fun qLoHi ↦
      solSeqInt (Int.neg (Int.ediv (Int.neg (Int.mul b solS24)) e)) fun qHiHi ↦
        solSeqInt
          (solMaxZ 0
            (Int.ediv
              (Int.mul qLoLo
                (Int.sub (Int.mul mSq6 (Int.mul solS24 solS24)) (Int.mul qLoLo qLoLo)))
              (Int.mul mCu6 (Int.mul solS24 solS24))))
          fun sBase ↦
            solSeqInt
              (solMaxZ 0
                (Int.sub solS24
                  (Int.neg (Int.ediv (Int.neg (Int.mul qLoHi qLoHi)) (Int.mul mSq2 solS24)))))
              fun cBaseLo ↦
                solSeqInt
                  (solMaxZ 0
                    (Int.sub solS24
                      (Int.neg (Int.ediv (Int.neg (Int.mul qHiHi qHiHi)) (Int.mul mSq2 solS24)))))
                  fun cBaseHi ↦
                    match solDoubleSinCosLo 16 sBase cBaseLo with
                    | (s1Lo, _) =>
                        solSeqInt (solDoubleCosLo 16 cBaseHi) fun c1H ↦
                          solBleZ 1 a && solBleZ 1 d && solBleZ 0 b && solBleZ 1 e &&
                          solBleZ b e &&
                          solBleZ 0 cLo && solBleZ 0 cHi && solBleZ 0 sLo && solBleZ 0 sHi &&
                          solBleZ 1 qLoLo && solBleZ qLoHi solS24 && solBleZ qHiHi solS24 &&
                          solBleZ (Int.mul sLo solScale15) s1Lo &&
                          solBleZ (Int.mul cLo solScale15) c1H &&
                          solBleZ (Int.mul solS24 solS24)
                            (Int.add (Int.mul c1H c1H)
                              (Int.mul (Int.mul sHi solScale15) (Int.mul sHi solScale15))) &&
                          solBleZ (Int.mul solS24 solS24)
                            (Int.add (Int.mul s1Lo s1Lo)
                              (Int.mul (Int.mul cHi solScale15) (Int.mul cHi solScale15)))
theorem checkPulseTrigRat24_sound {a d b e cLo cHi sLo sHi : ℤ} {φ : ℝ} (hlo : (a : ℝ) / (d : ℝ) ≤
  φ) (hhi : φ ≤ (b : ℝ) / (e : ℝ)) (hchk : checkPulseTrigRat24 a d b e cLo cHi sLo sHi = true) :
  memIvInt (Real.cos φ) (cLo, cHi) ∧ memIvInt (Real.sin φ) (sLo, sHi) := by
  unfold checkPulseTrigRat24 at hchk; simp only [solSeqInt_eq, solIntAdd_eq, solIntSub_eq,
    solIntMul_eq, solIntEdiv_eq, solIntNeg_eq] at hchk; set mSq6 : ℤ := 25769803776; set mCu6 : ℤ :=
    1688849860263936; set mSq2 : ℤ := 8589934592
  set qLoLo : ℤ := (a * solS24) / d; set qLoHi : ℤ := -((-(a * solS24)) / d); set qHiHi : ℤ :=
    -((-(b * solS24)) / e); set sBase : ℤ := solMaxZ 0 ((qLoLo * (mSq6 * (solS24 * solS24) - qLoLo *
    qLoLo)) / (mCu6 * (solS24 * solS24))); set cBaseLo : ℤ := solMaxZ 0 (solS24 - (-((-(qLoHi *
    qLoHi)) / (mSq2 * solS24)))); set cBaseHi : ℤ := solMaxZ 0 (solS24 - (-((-(qHiHi * qHiHi)) /
    (mSq2 * solS24))))
  rcases hsc : solDoubleSinCosLo 16 sBase cBaseLo with ⟨s1Lo, _⟩; rw [hsc] at hchk
  dsimp only at hchk; simp only [Bool.and_eq_true, solBleZ_eq_decide, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_ha1, hd1⟩, hb0⟩, he1⟩, _hbe⟩, _hcLo0⟩, hcHi0⟩, _hsLo0⟩, hsHi0⟩,
    hqLoLo1⟩, hqLoHi_le⟩, hqHiHi_le⟩, hs_ineq⟩, hc_ineq⟩, hcs_hi⟩, hsc_hi⟩
  have hs24_pos : (0 : ℤ) < solS24 := (by unfold solS24; norm_num); have hs24_r : (0 : ℝ) < (solS24
    : ℝ) := (by unfold solS24; norm_num); have hS : (0 : ℝ) < (swScale : ℝ) :=
    (by unfold swScale; norm_num)
  have hsc15_eq : (solScale15 : ℝ) * (swScale : ℝ) = (solS24 : ℝ) :=
    (by unfold solScale15 swScale solS24; norm_num)
  set qLo : ℝ := (a : ℝ) / (d : ℝ); set qHi : ℝ := (b : ℝ) / (e : ℝ); set xLo : ℝ := (qLoLo : ℝ) /
    (solS24 : ℝ); set xHi : ℝ := (qLoHi : ℝ) / (solS24 : ℝ); set yHi : ℝ := (qHiHi : ℝ) / (solS24 :
    ℝ); have hxLo_le_qLo : xLo ≤ qLo := ediv_scale_le_div a d solS24 (by omega) hs24_pos
  have hqLo_le_xHi : qLo ≤ xHi := div_le_ceil_ediv_scale a d solS24 (by omega) hs24_pos
  have hqHi_le_yHi : qHi ≤ yHi := div_le_ceil_ediv_scale b e solS24 (by omega) hs24_pos
  have hxLo_pos : 0 < xLo := div_pos (by exact_mod_cast (by omega : 0 < qLoLo)) hs24_r
  have hxHi_le1 : xHi ≤ 1 := (div_le_one hs24_r).2 (by exact_mod_cast hqLoHi_le)
  have hyHi_le1 : yHi ≤ 1 := (div_le_one hs24_r).2 (by exact_mod_cast hqHiHi_le)
  have hpi : (3 : ℝ) < π := Real.pi_gt_three; have hsBase0 : 0 ≤ sBase :=
    (by dsimp [sBase]; rw [solMaxZ_eq]; exact le_max_left _ _); have hcBaseLo0 : 0 ≤ cBaseLo :=
    (by dsimp [cBaseLo]; rw [solMaxZ_eq]; exact le_max_left _ _); have hcBaseHi0 : 0 ≤ cBaseHi :=
    (by dsimp [cBaseHi]; rw [solMaxZ_eq]; exact le_max_left _ _)
  have hsBase_le : (sBase : ℝ) / (solS24 : ℝ) ≤ Real.sin (qLo / 65536) := by
    have hsin_mono : Real.sin (xLo / 65536) ≤ Real.sin (qLo / 65536) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have hcube : xLo / 65536 - (xLo / 65536) ^ 3 / 6 ≤ Real.sin (xLo / 65536) :=
      Real.sin_ge_sub_cube (by positivity); have hsin_nn : 0 ≤ Real.sin (qLo / 65536) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith); have hd_pos : (0 : ℤ) < mCu6 *
      (solS24 * solS24) := (by unfold mCu6 solS24; norm_num); have hdiv := ediv_pos_le_real (qLoLo *
      (mSq6 * (solS24 * solS24) - qLoLo * qLoLo)) (mCu6 * (solS24 * solS24)) hd_pos; have hdiv2 :=
      div_le_div_of_nonneg_right hdiv hs24_r.le
    have halg : ((qLoLo * (mSq6 * (solS24 * solS24) - qLoLo * qLoLo) : ℤ) : ℝ) / ((mCu6 * (solS24 *
      solS24) : ℤ) : ℝ) / (solS24 : ℝ) = xLo / 65536 - (xLo / 65536) ^ 3 / 6 :=
      (by dsimp [xLo, mSq6, mCu6]; push_cast; field_simp [hs24_r.ne']; ring)
    dsimp [sBase]; rw [solMaxZ_eq, Int.cast_max, Int.cast_zero]
    rcases le_total (0 : ℝ) _ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h, zero_div]; exact hsin_nn
  have hcBaseLo_le : (cBaseLo : ℝ) / (solS24 : ℝ) ≤ Real.cos (qLo / 65536) := by
    have hcos_mono : Real.cos (xHi / 65536) ≤ Real.cos (qLo / 65536) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    have hcos_nn : 0 ≤ Real.cos (qLo / 65536) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith, by linarith⟩; have hd_pos : (0 : ℤ) < mSq2 * solS24 :=
      (by unfold mSq2 solS24; norm_num)
    have hceil := real_le_neg_ediv_neg_pos (qLoHi * qLoHi) (mSq2 * solS24) hd_pos
    have hsub : ((solS24 - (-((-(qLoHi * qLoHi)) / (mSq2 * solS24))) : ℤ) : ℝ) / (solS24 : ℝ) ≤ 1 -
      (xHi / 65536) ^ 2 / 2 := by
      have h1 : ((solS24 - (-((-(qLoHi * qLoHi)) / (mSq2 * solS24))) : ℤ) : ℝ) ≤ (solS24 : ℝ) -
        ((qLoHi * qLoHi : ℤ) : ℝ) / ((mSq2 * solS24 : ℤ) : ℝ) :=
        (by rw [Int.cast_sub]; linarith [hceil])
      have hdiv := div_le_div_of_nonneg_right h1 hs24_r.le; have halg : ((solS24 : ℝ) - ((qLoHi *
        qLoHi : ℤ) : ℝ) / ((mSq2 * solS24 : ℤ) : ℝ)) / (solS24 : ℝ) = 1 - (xHi / 65536) ^ 2 / 2 :=
        (by dsimp [xHi, mSq2]; push_cast; field_simp [hs24_r.ne']; ring); linarith
    dsimp [cBaseLo]; rw [solMaxZ_eq, Int.cast_max, Int.cast_zero]
    rcases le_total (0 : ℝ) _ with h | h
    · rw [max_eq_right h]; exact (hsub.trans Real.one_sub_sq_div_two_le_cos).trans hcos_mono
    · rw [max_eq_left h, zero_div]; exact hcos_nn
  have hcBaseHi_le : (cBaseHi : ℝ) / (solS24 : ℝ) ≤ Real.cos (yHi / 65536) := by
    have hyHi_nn : 0 ≤ yHi := (div_nonneg (by exact_mod_cast hb0)
      (by exact_mod_cast (by omega : 0 ≤ e))).trans hqHi_le_yHi; have hcos_nn : 0 ≤ Real.cos (yHi /
      65536) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hd_pos : (0 : ℤ) < mSq2 * solS24 := (by unfold mSq2 solS24; norm_num); have hceil :=
      real_le_neg_ediv_neg_pos (qHiHi * qHiHi) (mSq2 * solS24) hd_pos
    have hsub : ((solS24 - (-((-(qHiHi * qHiHi)) / (mSq2 * solS24))) : ℤ) : ℝ) / (solS24 : ℝ) ≤ 1 -
      (yHi / 65536) ^ 2 / 2 := by
      have h1 : ((solS24 - (-((-(qHiHi * qHiHi)) / (mSq2 * solS24))) : ℤ) : ℝ) ≤ (solS24 : ℝ) -
        ((qHiHi * qHiHi : ℤ) : ℝ) / ((mSq2 * solS24 : ℤ) : ℝ) :=
        (by rw [Int.cast_sub]; linarith [hceil])
      have hdiv := div_le_div_of_nonneg_right h1 hs24_r.le; have halg : ((solS24 : ℝ) - ((qHiHi *
        qHiHi : ℤ) : ℝ) / ((mSq2 * solS24 : ℤ) : ℝ)) / (solS24 : ℝ) = 1 - (yHi / 65536) ^ 2 / 2 :=
        (by dsimp [yHi, mSq2]; push_cast; field_simp [hs24_r.ne']; ring); linarith
    dsimp [cBaseHi]; rw [solMaxZ_eq, Int.cast_max, Int.cast_zero]
    rcases le_total (0 : ℝ) _ with h | h
    · rw [max_eq_right h]; exact hsub.trans Real.one_sub_sq_div_two_le_cos
    · rw [max_eq_left h, zero_div]; exact hcos_nn
  have h2_16 : (2 : ℝ) ^ 16 = 65536 := (by norm_num)
  have hdbl_sc := solDoubleSinCosLo_sound 16 sBase cBaseLo (qLo / 65536) hsBase0 hcBaseLo0
    (by linarith) (by rw [h2_16]; linarith) hsBase_le hcBaseLo_le
  rw [hsc] at hdbl_sc; rcases hdbl_sc with ⟨hs1Lo0, _, hs1Lo_sin, _⟩; rw [h2_16, mul_div_cancel₀ _
    (by norm_num)] at hs1Lo_sin; set c1H : ℤ := solDoubleCosLo 16 cBaseHi; have hyHi_nn : 0 ≤ yHi :=
    (div_nonneg (by exact_mod_cast hb0) (by exact_mod_cast (by omega : 0 ≤ e))).trans hqHi_le_yHi
  obtain ⟨hc1H0, hc1H_cos⟩ := solDoubleCosLo_sound 16 cBaseHi (yHi / 65536) hcBaseHi0 (by linarith)
    (by rw [h2_16]; linarith) hcBaseHi_le; rw [h2_16, mul_div_cancel₀ _ (by norm_num)] at hc1H_cos
  have hs1Lo_φ : (s1Lo : ℝ) / (solS24 : ℝ) ≤ Real.sin φ := hs1Lo_sin.trans
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hlo); have hc1H_φ : (c1H :
    ℝ) / (solS24 : ℝ) ≤ Real.cos φ := hc1H_cos.trans (Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith) (hhi.trans hqHi_le_yHi))
  have hsLo_φ : (sLo : ℝ) / (swScale : ℝ) ≤ Real.sin φ := by
    have hc : (sLo : ℝ) * (solScale15 : ℝ) ≤ (s1Lo : ℝ) := (by exact_mod_cast hs_ineq)
    have h1 : (sLo : ℝ) / (swScale : ℝ) ≤ (s1Lo : ℝ) / (solS24 : ℝ) := by
      rw [div_le_div_iff₀ hS hs24_r, ← hsc15_eq]
      exact (mul_assoc _ _ _).symm.le.trans (mul_le_mul_of_nonneg_right hc hS.le)
    exact h1.trans hs1Lo_φ
  have hcLo_φ : (cLo : ℝ) / (swScale : ℝ) ≤ Real.cos φ := by
    have hc : (cLo : ℝ) * (solScale15 : ℝ) ≤ (c1H : ℝ) := (by exact_mod_cast hc_ineq)
    have h1 : (cLo : ℝ) / (swScale : ℝ) ≤ (c1H : ℝ) / (solS24 : ℝ) := by
      rw [div_le_div_iff₀ hS hs24_r, ← hsc15_eq]
      exact (mul_assoc _ _ _).symm.le.trans (mul_le_mul_of_nonneg_right hc hS.le)
    exact h1.trans hc1H_φ
  have hcs_r : 1 ≤ ((c1H : ℝ) / (solS24 : ℝ)) ^ 2 + ((sHi : ℝ) / (swScale : ℝ)) ^ 2 := by
    have hc : ((solS24 * solS24 : ℤ) : ℝ) ≤ ((c1H * c1H + (sHi * solScale15) * (sHi * solScale15) :
      ℤ) : ℝ) := (by exact_mod_cast hcs_hi); push_cast at hc
    have hs_eq : (sHi : ℝ) / (swScale : ℝ) = ((sHi : ℝ) * (solScale15 : ℝ)) / (solS24 : ℝ) := by
      rw [← hsc15_eq, mul_comm (solScale15 : ℝ), mul_div_mul_right _ _
        (by unfold solScale15; norm_num)]
    rw [hs_eq, div_pow, div_pow, ← add_div, one_le_div (sq_pos_of_pos hs24_r)]; nlinarith
  have hsc_r : 1 ≤ ((s1Lo : ℝ) / (solS24 : ℝ)) ^ 2 + ((cHi : ℝ) / (swScale : ℝ)) ^ 2 := by
    have hc : ((solS24 * solS24 : ℤ) : ℝ) ≤ ((s1Lo * s1Lo + (cHi * solScale15) * (cHi * solScale15)
      : ℤ) : ℝ) := (by exact_mod_cast hsc_hi); push_cast at hc
    have hc_eq : (cHi : ℝ) / (swScale : ℝ) = ((cHi : ℝ) * (solScale15 : ℝ)) / (solS24 : ℝ) := by
      rw [← hsc15_eq, mul_comm (solScale15 : ℝ), mul_div_mul_right _ _
        (by unfold solScale15; norm_num)]
    rw [hc_eq, div_pow, div_pow, ← add_div, one_le_div (sq_pos_of_pos hs24_r)]; nlinarith
  have hsin_ub : Real.sin φ ≤ (sHi : ℝ) / (swScale : ℝ) := sq_bound_of_sin_cos_ge (div_nonneg
    (by exact_mod_cast hc1H0) hs24_r.le) (div_nonneg (by exact_mod_cast hsHi0) hS.le)
    (Real.cos_sq_add_sin_sq φ) hcs_r hc1H_φ
  have hcos_ub : Real.cos φ ≤ (cHi : ℝ) / (swScale : ℝ) := sq_bound_of_sin_cos_ge (div_nonneg
    (by exact_mod_cast hs1Lo0) hs24_r.le) (div_nonneg (by exact_mod_cast hcHi0) hS.le)
    (Real.sin_sq_add_cos_sq φ) hsc_r hs1Lo_φ; exact ⟨⟨hcLo_φ, hcos_ub⟩, ⟨hsLo_φ, hsin_ub⟩⟩
/-- Pure-GMP ratio-bound check for stratum `1 ≤ shiftW ≤ 1023` on `[rMin, rMax]`. -/
abbrev checkPulseStratumRatio (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  checkSwLStratumRatioPulse rMin rMax shiftW ratioLo ratioHi
theorem checkPulseStratumRatio_sound {N r rMin rMax shiftW : ℕ} {ratioLo ratioHi : ℤ} (hN96 :
  (79228162514264337593543950336 : ℝ) ≤ (N : ℝ)) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkPulseStratumRatio rMin rMax shiftW ratioLo ratioHi = true) :
    let α₀ := Real.arcsin (1 / √((N : ℝ) / (r : ℝ))); let θ := swLThetaShiftReal N r shiftW
    ((ratioLo : ℝ) / (swScale : ℝ)) * (2 * α₀) ≤ θ ∧ θ ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * (2 * α₀)
      := stratum_angle_ratio_boundsPulse hN96 hmin hmax hchk
/-- `O(L)` linear-scan shifted-stratum angle walk (`w = shiftW.. L - 1`). -/
def checkPulseAnglesWalk (rMin rMax tauNum tauDen : ℕ) (q1HiNum q1HiDen : ℤ) :
    ℕ → List IvInt → List (IvInt × IvInt) → Bool
  | _, [], [] => true
  | shiftW, rat :: rats, (cw, sw) :: trigs =>
      checkPulseStratumRatio rMin rMax shiftW rat.1 rat.2 &&
      checkPulseTrigRat24
        (Int.mul (Int.ofNat tauNum) rat.1) (Int.mul (Int.ofNat tauDen) swScale)
        (Int.mul q1HiNum rat.2) (Int.mul q1HiDen swScale)
        cw.1 cw.2 sw.1 sw.2 &&
      solLitNat (Nat.add 1 shiftW) fun nextW ↦
        checkPulseAnglesWalk rMin rMax tauNum tauDen q1HiNum q1HiDen nextW rats trigs
  | _, _, _ => false
theorem checkPulseAnglesWalk_spec (rMin rMax tauNum tauDen : ℕ) (q1HiNum q1HiDen : ℤ) : ∀ (shiftW
    : ℕ) (rats : List IvInt) (trigs : List (IvInt × IvInt)), checkPulseAnglesWalk rMin rMax tauNum
    tauDen q1HiNum q1HiDen shiftW rats trigs = true → rats.length = trigs.length ∧ ∀ idx <
    rats.length,
        let w := shiftW + idx; let rat := rats.getD idx (0, 0)
        let cs := trigs.getD idx ((0, 0), (0, 0))
        checkPulseStratumRatio rMin rMax w rat.1 rat.2 = true ∧
        checkPulseTrigRat24
          (Int.mul (Int.ofNat tauNum) rat.1) (Int.mul (Int.ofNat tauDen) swScale)
          (Int.mul q1HiNum rat.2) (Int.mul q1HiDen swScale)
          cs.1.1 cs.1.2 cs.2.1 cs.2.2 = true
  | _, [], [], _ => ⟨rfl, fun _ h ↦ by simp at h⟩
  | _, [], _ :: _, h => by simp [checkPulseAnglesWalk] at h
  | _, _ :: _, [], h => by simp [checkPulseAnglesWalk] at h
  | shiftW, rat :: rats, (cw, sw) :: trigs, h => by
    unfold checkPulseAnglesWalk at h; simp only [solLitNat_eq, Bool.and_eq_true] at h
    rcases h with ⟨⟨h1, h2⟩, hrest⟩; have hw : Nat.add 1 shiftW = shiftW + 1 :=
      (by rw [solNatAdd_eq]; omega); rw [hw] at hrest
    rcases checkPulseAnglesWalk_spec rMin rMax tauNum tauDen q1HiNum q1HiDen (shiftW + 1) rats
      trigs hrest with ⟨hlen, hspec⟩; refine ⟨by simp [hlen], fun idx hidx ↦ ?_⟩
    cases idx with
    | zero => simpa using ⟨h1, h2⟩
    | succ i =>
        have hi : i < rats.length := (by rw [List.length_cons] at hidx; omega)
        have hs := hspec i hi; have hadd : shiftW + 1 + i = shiftW + (i + 1) := (by omega)
        simpa [hadd] using hs
/-- `O(L)` `1`-ULP bucket angle checker for `2 ≤ L ≤ 1024` and `r ∈ [rMin, rMax]`. -/
def checkPulseBucketAngles (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := 100000000000
  solSeqInt (Int.add (Int.mul (Int.ofNat tauNum) s11) (Int.ofNat tauDen)) fun q1HiNum ↦
    solSeqInt (Int.mul (Int.ofNat tauDen) s11) fun q1HiDen ↦
      Nat.ble 2 L && Nat.ble L 1024 && Nat.ble L rMin && Nat.ble rMin rMax &&
      Nat.ble rMax 1024 && Nat.ble 1 tauNum && Nat.ble 1 tauDen &&
      Nat.beq ratios.length (Nat.sub L 1) && Nat.beq trigIvs.length L &&
      match trigIvs with
      | [] => false
      | (c0, s0) :: restTrig =>
          checkPulseTrigRat24 (Int.ofNat tauNum) (Int.ofNat tauDen) q1HiNum q1HiDen
            c0.1 c0.2 s0.1 s0.2 &&
          checkPulseAnglesWalk rMin rMax tauNum tauDen q1HiNum q1HiDen 1 ratios restTrig
/-- Singleton (`rMin = rMax = rGrid`) wrapper around `checkPulseBucketAngles`. -/
def checkPulseSingletonAngles (L rGrid tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  checkPulseBucketAngles L rGrid rGrid tauNum tauDen ratios trigIvs
theorem checkPulseBucketAngles_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkPulseBucketAngles L rMin rMax tauNum tauDen ratios trigIvs = true) : 2 ≤ L ∧ L ≤ 1024 ∧ L ≤
  r ∧ r ≤ 1024 ∧ 1 ≤ tauNum ∧ 1 ≤ tauDen ∧ trigIvs.length = L ∧
    let K_blk := swLKBlk n r tauNum tauDen; let N : ℕ := 2 ^ n
    ∀ w : Fin L, memIvInt (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N r w.1)) (trigIvs.getD w.1
      ((0, 0), (0, 0))).1 ∧ memIvInt (Real.sin ((K_blk : ℝ) * swLThetaShiftReal N r w.1))
      (trigIvs.getD w.1 ((0, 0), (0, 0))).2 := by
  unfold checkPulseBucketAngles at hchk; simp only [solSeqInt_eq, Bool.and_eq_true,
    natBle_eq_decide, natBeq_eq_decide, decide_eq_true_eq, solNatSub_eq, solIntAdd_eq, solIntMul_eq,
    Int.ofNat_eq_natCast] at hchk; rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hL2, hL1024⟩, hLrMin⟩, _⟩, hrMax1024⟩,
    htau1⟩, hden1⟩, hlen_rat⟩, hlen_trig⟩, hm⟩
  have hLr : L ≤ r := hLrMin.trans hmin; have hr1024 : r ≤ 1024 := hmax.trans hrMax1024
  rcases trigIvs with _ | ⟨⟨c0, s0⟩, restTrig⟩
  · simp at hm
  simp only [Bool.and_eq_true] at hm; rcases hm with ⟨htrig0, hwalk⟩
  rcases checkPulseAnglesWalk_spec rMin rMax tauNum tauDen _ _ 1 ratios restTrig hwalk with ⟨_,
    hrest⟩; refine ⟨hL2, hL1024, hLr, hr1024, htau1, hden1, hlen_trig, ?_⟩
  intro K_blk N w; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r))
  have hN96 : (79228162514264337593543950336 : ℝ) ≤ (N : ℝ) := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ (N : ℝ) := (by exact_mod_cast hpow); have hval : ((2 ^ 96 : ℕ) : ℝ) =
      79228162514264337593543950336 := (by norm_num); linarith
  set c₁ : ℝ := (N : ℝ) / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]; have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
    calc (8796093022208 : ℝ) ^ 2 * (r : ℝ)
      _ ≤ (8796093022208 : ℝ) ^ 2 * 1024 := mul_le_mul_of_nonneg_left hr_le (by norm_num)
      _ = 79228162514264337593543950336 := by norm_num
      _ ≤ (N : ℝ) := hN96
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ :=
    (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]; exact Real.sqrt_le_sqrt hc1_ge)
  set α₀ : ℝ := Real.arcsin (1 / √c₁); rcases arcsin_small_boundsL (by positivity)
    (one_div_le_one_div_of_le (by norm_num) (by linarith : (8000000000000 : ℝ) ≤ √c₁)) with
    ⟨_, hα_le, _, _⟩; set tauR : ℝ := (tauNum : ℝ) / (tauDen : ℝ); have htau_nn : 0 ≤ tauR :=
    (by positivity); set K₀ : ℕ := (round (tauR / (2 * α₀))).toNat; have hK_eq : K_blk = K₀ + 1 :=
    (by simp only [K_blk, swLKBlk, K₀, tauR, α₀, c₁, N, Nat.cast_pow, Nat.cast_ofNat])
  have hα_pos : 0 < α₀ := by
    rcases arcsin_small_boundsL (by positivity) (one_div_le_one_div_of_le (by norm_num)
      (by linarith : (8000000000000 : ℝ) ≤ √c₁)) with ⟨hp, _, _, _⟩; exact hp
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩; have hφ0_lo : tauR ≤ 2 *
    (K_blk : ℝ) * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith); have hφ0_hi : 2 *
    (K_blk : ℝ) * α₀ ≤ tauR + 3 * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  set s11 : ℤ := 100000000000; set q1HiNum : ℤ := (tauNum : ℤ) * s11 + (tauDen : ℤ)
  set q1HiDen : ℤ := (tauDen : ℤ) * s11
  have hq1_eq : (q1HiNum : ℝ) / (q1HiDen : ℝ) = tauR + 1 / (100000000000 : ℝ) := by
    dsimp [q1HiNum, q1HiDen, s11, tauR]; have hden_ne : (tauDen : ℝ) ≠ 0 :=
      (by exact_mod_cast (by omega : tauDen ≠ 0)); push_cast; field_simp [hden_ne]
  have hφ0_hi_q1 : 2 * (K_blk : ℝ) * α₀ ≤ (q1HiNum : ℝ) / (q1HiDen : ℝ) :=
    (by rw [hq1_eq]; linarith [hφ0_hi, hα_le]); rcases w with ⟨_ | idx, hw_lt⟩
  · have hN_pos : (0 : ℝ) < (N : ℝ) := (by linarith)
    have hθ0_eq : swLThetaShiftReal N r 0 = 2 * α₀ := by
      unfold swLThetaShiftReal; simp only [Nat.cast_zero, mul_zero, sub_zero, α₀, c₁]; congr 2
      rw [Real.sqrt_div hr_pos.le, Real.sqrt_div hN_pos.le, one_div_div]
    have hφ_eq : (K_blk : ℝ) * swLThetaShiftReal N r 0 = 2 * (K_blk : ℝ) * α₀ :=
      (by rw [hθ0_eq]; ring)
    rw [hφ_eq]; change checkPulseTrigRat24 (tauNum : ℤ) (tauDen : ℤ) q1HiNum q1HiDen
      c0.1 c0.2 s0.1 s0.2 = true at htrig0
    simpa using checkPulseTrigRat24_sound (by simpa [tauR] using hφ0_lo) hφ0_hi_q1 htrig0
  · have hidx_rat : idx < ratios.length := (by rw [hlen_rat]; omega); rcases hrest idx hidx_rat with
      ⟨hrat_w, htrig_w⟩; have hw_eq : 1 + idx = idx + 1 := (by omega); rw [hw_eq] at hrat_w
    rcases checkPulseStratumRatio_sound hN96 hmin hmax hrat_w with ⟨hr_lo, hr_hi⟩; set rat :=
      ratios.getD idx (0, 0)
    have hrat_chk : checkSwLStratumRatioPulse rMin rMax (idx + 1) rat.1 rat.2 = true := hrat_w
    unfold checkSwLStratumRatioPulse at hrat_chk
    simp only [SchurWeylLCert.solBleZ_eq, bleZ_eq_decide, SchurWeylLCert.solNatBle_eq_decide,
      Bool.and_eq_true, decide_eq_true_eq] at hrat_chk; rcases hrat_chk with ⟨⟨⟨⟨⟨⟨⟨_, hrat_lo1⟩,
      hrat_hi2⟩, _⟩, _⟩, _⟩, _⟩, _⟩
    have hrat_lo_nn : 0 ≤ (rat.1 : ℝ) / (swScale : ℝ) := div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ rat.1)) hS.le; have hrat_hi_nn : 0 ≤ (rat.2 : ℝ) / (swScale
      : ℝ) := div_nonneg (by exact_mod_cast (by omega : 0 ≤ rat.2)) hS.le
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
    let cs := restTrig.getD idx ((0, 0), (0, 0))
    change checkPulseTrigRat24 ((tauNum : ℤ) * rat.1) ((tauDen : ℤ) * swScale) (q1HiNum * rat.2)
      (q1HiDen * swScale) cs.1.1 cs.1.2 cs.2.1 cs.2.2 = true at htrig_w; simpa [cs, solIntMul_eq,
      Int.ofNat_eq_natCast] using checkPulseTrigRat24_sound hφ_lo hφ_hi htrig_w
/-- Singleton (`r = rGrid`) soundness wrapper around `checkPulseBucketAngles_sound`. -/
theorem checkPulseSingletonAngles_sound {L n rGrid tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} (hn96 : 96 ≤ n) (hchk : checkPulseSingletonAngles L rGrid
  tauNum tauDen ratios trigIvs = true) : 2 ≤ L ∧ L ≤ 1024 ∧ L ≤ rGrid ∧ rGrid ≤ 1024 ∧ 1 ≤ tauNum ∧
  1 ≤ tauDen ∧ trigIvs.length = L ∧
    let K_blk := swLKBlk n rGrid tauNum tauDen; let N : ℕ := 2 ^ n
    ∀ w : Fin L, memIvInt (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N rGrid w.1)) (trigIvs.getD w.1
      ((0, 0), (0, 0))).1 ∧ memIvInt (Real.sin ((K_blk : ℝ) * swLThetaShiftReal N rGrid w.1))
      (trigIvs.getD w.1 ((0, 0), (0, 0))).2 :=
  checkPulseBucketAngles_sound hn96 le_rfl le_rfl hchk
/- ## 3. Window-Sparse Causal `L2Ball` Trajectory, WKB Unroller & `O(L)` Parseval Bounds -/
/-- Window-sparse conveyor pulse active on interior strata `[wLo, wLo + uWin.length)`. -/
structure SolSparsePulse where
  /-- First active interior stratum index (`1 ≤ wLo`). -/
  wLo : ℕ
  /-- Active window of `u_w` numerators for `w = wLo,..., wLo + uWin.length - 1`. -/
  uWin : List ℤ
  /-- Top weak-measurement Cayley numerator `v`. -/
  vNum : ℤ
/-- Lookup interior Pieri numerator `u_w` (`1 ≤ w`) of a `SolSparsePulse`. -/
def solSparseUNum (sp : SolSparsePulse) (w : ℕ) : ℤ :=
  cond (Nat.ble sp.wLo w) (sp.uWin.getD (Nat.sub w sp.wLo) 0) 0
/-- Embed `SolSparsePulse` at shared denominator `uvDen` into `SwLPulseRat L`. -/
def solToSwLPulse (L uvDen : ℕ) (sp : SolSparsePulse) : SwLPulseRat L :=
  ⟨fun i ↦ solSparseUNum sp (i.1 + 1), sp.vNum, uvDen⟩
/-- Embed a list of `SolSparsePulse` at shared denominator `uvDen` into `List (SwLPulseRat
  L)`. -/
def solToSwLPulses (L uvDen : ℕ) (sps : List SolSparsePulse) : List (SwLPulseRat L) :=
  sps.map (solToSwLPulse L uvDen)
/-- Boolean check that `1 ≤ sp.wLo` on a `SolSparsePulse`. -/
def solSparsePulseValid (sp : SolSparsePulse) : Bool :=
  Nat.ble 1 sp.wLo
/-- Atomic WHNF forcing for `SolSparsePulse` (`wLo`, `uWin` spine + elements, `vNum`). -/
def solSeqPulse {α : Type*} (sp : SolSparsePulse) (k : SolSparsePulse → α) : α :=
  solLitNat sp.wLo fun wLo' ↦
    solWithIntList sp.uWin fun uWin' ↦
      solSeqInt sp.vNum fun vNum' ↦
        k ⟨wLo', uWin', vNum'⟩
theorem solSeqPulse_eq {α : Type*} (sp : SolSparsePulse) (k : SolSparsePulse → α) : solSeqPulse sp k
  = k sp := by
  rcases sp with ⟨wLo, uWin, vNum⟩; simp [solSeqPulse, solLitNat_eq, solWithIntList_eq,
    solSeqInt_eq]
/-- Tail-recursive spine + element WHNF accumulator for `List SolSparsePulse`. -/
def solRevForcePulseList : List SolSparsePulse → List SolSparsePulse → List SolSparsePulse
  | [], acc => acc
  | sp :: sps, acc =>
      solSeqPulse sp fun sp' ↦ solRevForcePulseList sps (sp' :: acc)
theorem solRevForcePulseList_inv : ∀ (sps acc : List SolSparsePulse), solRevForcePulseList
  (solRevForcePulseList sps acc) [] = solRevForcePulseList acc sps
  | [], _ => rfl
  | sp :: sps, acc => by
    change solRevForcePulseList (solSeqPulse sp fun sp' ↦ solRevForcePulseList sps (sp' :: acc)) []
      = solRevForcePulseList acc (sp :: sps); rw [solSeqPulse_eq, solRevForcePulseList_inv sps (sp
      :: acc)]; change (solSeqPulse sp fun sp' ↦ solRevForcePulseList acc (sp' :: sps)) =
      solRevForcePulseList acc (sp :: sps); rw [solSeqPulse_eq]
theorem solRevForcePulseList_id (sps : List SolSparsePulse) : solRevForcePulseList
  (solRevForcePulseList sps []) [] = sps := solRevForcePulseList_inv sps []
/-- CPS spine + element WHNF materializer for `List SolSparsePulse`. -/
def solWithPulseList {α : Type*} (sps : List SolSparsePulse)
    (k : List SolSparsePulse → α) : α :=
  solSeqList (solRevForcePulseList (solRevForcePulseList sps []) []) k
theorem solWithPulseList_eq {α : Type*} (sps : List SolSparsePulse) (k : List SolSparsePulse → α) :
  solWithPulseList sps k = k sps := by
  unfold solWithPulseList; rw [solSeqList_eq, solRevForcePulseList_inv sps []]; rfl
theorem solToSwLPulses_valid (L : ℕ) {uvDen : ℕ} (hden : 1 ≤ uvDen) (sps : List SolSparsePulse) :
  (solToSwLPulses L uvDen sps).all swLPulseValid = true := by
  unfold solToSwLPulses
  induction sps with
  | nil => rfl
  | cons sp rest ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true]; refine ⟨?_, ih⟩
    unfold swLPulseValid solToSwLPulse; dsimp only; rw [decide_eq_true_eq]; omega
/-- Compact pure-integer WKB spline schedule (`~743` integers/rung) unrolling to sparse
  pulses. -/
structure SolWkbSched where
  /-- Target count `r` for this schedule. -/
  r : ℕ
  /-- Conveyor register rank `L` (`2 ≤ L ≤ r`). -/
  L : ℕ
  /-- Number of conveyor pulses `K`. -/
  K : ℕ
  /-- Grover block angle numerator `tauNum`. -/
  tauNum : ℕ
  /-- Grover block angle denominator `tauDen`. -/
  tauDen : ℕ
  /-- Shared Cayley denominator `uvDen` (`65536`). -/
  uvDen : ℕ
  /-- Scaled bulk multi-pulse speed `vBulkQ`. -/
  vBulkQ : ℤ
  /-- Scaled initial multi-pulse offset `sOffQ`. -/
  sOffQ : ℤ
  /-- Scaled quadratic chirp `accelQ`. -/
  accelQ : ℤ
  /-- Bulk `65`-point profile `rBulkQ`. -/
  rBulkQ : List ℤ
  /-- Launch `18 × 18` bilinear corner table `uLnchQ`. -/
  uLnchQ : List ℤ
  /-- Landing `18 × 18` bilinear corner table `uLandQ`. -/
  uLandQ : List ℤ
  /-- Drain `24`-point top profile `vDrainQ`. -/
  vDrainQ : List ℤ
/-- Balanced binary lookup tree of `(ℤ × ℤ)` adjacent pairs for `O(log n)` spline lookup. -/
inductive SolPairTree where
  /-- Leaf holding an adjacent `(xs[i], xs[i + 1])` pair. -/
  | leaf (v : ℤ × ℤ)
  /-- Internal split node routing `idx < mid` left and `mid ≤ idx` right. -/
  | node (mid : ℕ) (l r : SolPairTree)
/-- Recursively WHNF-force every `.node`, `.leaf`, split index, and payload of a
  `SolPairTree`. -/
def solWithPairTree {α : Type*} : SolPairTree → (SolPairTree → α) → α
  | .leaf v, k =>
      solSeqIv v fun v' ↦ k (.leaf v')
  | .node mid l r, k =>
      solLitNat mid fun mid' ↦
        solWithPairTree l fun l' ↦
          solWithPairTree r fun r' ↦
            k (.node mid' l' r')
theorem solWithPairTree_eq {α : Type*} : ∀ (t : SolPairTree) (k : SolPairTree → α), solWithPairTree
  t k = k t
  | .leaf v, k => by dsimp only [solWithPairTree]; rw [solSeqIv_eq]
  | .node mid l r, k => by
    dsimp only [solWithPairTree]; rw [solLitNat_eq, solWithPairTree_eq l, solWithPairTree_eq r]
/-- Tail-recursive tagged leaf builder `[(0, (xs[0], xs[1])),...]` (reversed, WHNF-forced). -/
def solPairLeavesRev : ℕ → List ℤ → List (ℕ × SolPairTree) → List (ℕ × SolPairTree)
  | _, [], acc => acc
  | lo, x :: tl, acc =>
      let y := match tl with | y0 :: _ => y0 | [] => 0
      solLitNat lo fun lo' ↦
        solSeqInt x fun x' ↦
          solSeqInt y fun y' ↦
            solLitNat (Nat.add lo' 1) fun loNext ↦
              solPairLeavesRev loNext tl ((lo', .leaf (x', y')) :: acc)
/-- Tail-recursive list reverser for tagged `SolPairTree` level spines. -/
def solRevNodeList : List (ℕ × SolPairTree) → List (ℕ × SolPairTree) → List (ℕ × SolPairTree)
  | [], acc => acc
  | p :: rest, acc => solRevNodeList rest (p :: acc)
/-- Tail-recursive adjacent-pair merge pass (reversed, WHNF-forced split indices). -/
def solMergePairLevelRev :
    List (ℕ × SolPairTree) → List (ℕ × SolPairTree) → List (ℕ × SolPairTree)
  | (loL, tL) :: (loR, tR) :: rest, acc =>
      solLitNat loL fun loL' ↦
        solLitNat loR fun loR' ↦
          solMergePairLevelRev rest ((loL', .node loR' tL tR) :: acc)
  | [x], acc => x :: acc
  | [], acc => acc
/-- Iterate eager `solMergePairLevelRev` for `fuel` levels (`O(n)` total work, `1`
  self-call). -/
def solBuildTreeLevels : ℕ → List (ℕ × SolPairTree) → SolPairTree
  | 0, ts =>
      match ts with
      | (_, t) :: _ => t
      | [] => .leaf (0, 0)
  | fuel + 1, ts =>
      match ts with
      | [] => .leaf (0, 0)
      | [(_, t)] => t
      | _ => solBuildTreeLevels fuel (solRevNodeList (solMergePairLevelRev ts []) [])
/-- Build a fully WHNF-materialized balanced `SolPairTree` over `(xs[i], xs[i + 1])` in
  `O(n)`. -/
def solBuildPairTree (xs : List ℤ) (fuel : ℕ) : SolPairTree :=
  solBuildTreeLevels fuel (solRevNodeList (solPairLeavesRev 0 xs []) [])
/-- `O(log n)` lookup of `(xs[idx], xs[idx + 1])` in a `SolPairTree`. -/
def solLookupPair : SolPairTree → ℕ → ℤ × ℤ
  | .leaf v, _ => v
  | .node mid l r, idx =>
      cond (Nat.ble mid idx) (solLookupPair r idx) (solLookupPair l idx)
/-- Pure-GMP WKB coordinate `2048 * r - ⌊√(4194304 * r * (r - w))⌋`. -/
def solWkbSScaled (r w : ℕ) : ℤ :=
  let rw := Nat.sub r w
  let prod := Nat.mul (Nat.mul 4194304 r) rw
  solLitNat (solFloorIsqrt prod) fun sq ↦
    Int.sub (Int.ofNat (Nat.mul 2048 r)) (Int.ofNat sq)
/-- Pure-GMP WKB coupling `⌊(⌊√(1048576*(r-w+1)/r)⌋ + ⌊√(1048576*(r-w)/r)⌋) / 2⌋`. -/
def solWkbGScaled (r w : ℕ) : ℤ :=
  cond (Nat.beq w 0)
    0
    (
    let q1 := Nat.div (Nat.mul 1048576 (Nat.add (Nat.sub r w) 1)) r
    let q0 := Nat.div (Nat.mul 1048576 (Nat.sub r w)) r
    solLitNat (solFloorIsqrt q1) fun s1 ↦
      solLitNat (solFloorIsqrt q0) fun s0 ↦
        Int.ofNat (Nat.div (Nat.add s1 s0) 2))
/-- Tail-recursive builder for `(s_w, g_w)` table `w = idx,..., idx + rem - 1` (reversed). -/
def solBuildWkbSGRev (r : ℕ) : ℕ → ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | _, 0, acc => acc
  | idx, rem + 1, acc =>
      solSeqInt (solWkbSScaled r idx) fun sw ↦
        solSeqInt (solWkbGScaled r idx) fun gw ↦
          solLitNat (Nat.add idx 1) fun idxNext ↦
            solBuildWkbSGRev r idxNext rem ((sw, gw) :: acc)
/-- Tail-recursive list reverser for `List (ℤ × ℤ)`. -/
def solRevSGList : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | [], acc => acc
  | p :: rest, acc => solRevSGList rest (p :: acc)
/-- Structural `O(k)` prefix drop on `List (ℤ × ℤ)`. -/
def solDropSG : ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, xs => xs
  | _ + 1, [] => []
  | k + 1, _ :: xs => solDropSG k xs
/-- Clamped `1024`-scale linear interpolation index and fractional weight `(idx, frac)`. -/
def solLinIdxFrac (x span nM1 : ℤ) : ℕ × ℤ :=
  let xc := cond (solBleZ x 0)
              0
              (cond (solBleZ span x) (Int.sub span 1) x)
  solSeqInt (Int.ediv (Int.mul (Int.mul xc nM1) 1024) span) fun sc ↦
    solLitNat (Int.ediv sc 1024).toNat fun idx ↦
      solSeqInt (Int.emod sc 1024) fun frac ↦ (idx, frac)
/-- Evaluate `1024`-scale linear interpolation on `(y0, y1)` with weight `wx`. -/
def solLerp1024 (p : ℤ × ℤ) (wx : ℤ) : ℤ :=
  Int.ediv (Int.add (Int.mul (Int.sub 1024 wx) p.1) (Int.mul wx p.2)) 1024
/-- Walk active strata `w = wLo,..., wLo + count - 1` to emit `uWin: List ℤ`. -/
def solEvalWkbWindow (tauNumZ tauDenZ scQ sMaxQ : ℤ) (hasLnch hasLand : Bool)
    (ilp : ℕ) (wlp : ℤ) (idp : ℕ) (wdp : ℤ)
    (rbTree ulnTree uldTree : SolPairTree) :
    ℕ → List (ℤ × ℤ) → List ℤ
  | 0, _ => []
  | count + 1, sgList =>
      let sg := match sgList with | x :: _ => x | [] => (0, 0)
      solSeqList (match sgList with | _ :: rs => rs | [] => []) fun restSG ↦
        let swQ := sg.1
        let gwQ := sg.2
        solSeqInt (Int.sub swQ scQ) fun xiQ ↦
          let inBulk : Bool := solBleZ (-32767) xiQ && solBleZ xiQ 32767
          solSeqInt
            (cond inBulk
               (
              let sh := Int.add xiQ 32768
              let ix := (Int.ediv sh 1024).toNat
              let wx := Int.emod sh 1024
              solLerp1024 (solLookupPair rbTree ix) wx)
               0)
            fun ru0 ↦
              let inLnch : Bool := hasLnch && solBleZ swQ 37887
              solSeqInt
                (cond inLnch
                   (
                  let (ils, wls) := solLinIdxFrac (Int.sub swQ 1024) 36864 17
                  let r0 := Nat.add (Nat.mul ilp 18) ils
                  let r1 := Nat.add (Nat.mul (Nat.add ilp 1) 18) ils
                  let v0 := solLerp1024 (solLookupPair ulnTree r0) wls
                  let v1 := solLerp1024 (solLookupPair ulnTree r1) wls
                  Int.add ru0 (solLerp1024 (v0, v1) wlp))
                   ru0)
                fun ru1 ↦
                  solSeqInt (Int.sub sMaxQ swQ) fun dsQ ↦
                    let inLand : Bool := hasLand && solBleZ dsQ 36863
                    solSeqInt
                      (cond inLand
                         (
                        let (ids, wds) := solLinIdxFrac dsQ 36864 17
                        let r0 := Nat.add (Nat.mul idp 18) ids
                        let r1 := Nat.add (Nat.mul (Nat.add idp 1) 18) ids
                        let v0 := solLerp1024 (solLookupPair uldTree r0) wds
                        let v1 := solLerp1024 (solLookupPair uldTree r1) wds
                        Int.add ru1 (solLerp1024 (v0, v1) wdp))
                         ru1)
                      fun ru2 ↦
                        let active : Bool := inBulk || inLnch || inLand
                        let uVal : ℤ :=
                          cond (active && !solBeqZ ru2 0)
                            (
                              solSeqInt
                              (Int.ediv (Int.mul (Int.mul tauNumZ gwQ) ru2)
                                (Int.mul 2048 tauDenZ))
                              fun thH ↦
                                Int.add thH
                                  (Int.ediv (Int.mul (Int.mul thH thH) thH) 30000000000))
                            0
                        solSeqInt uVal fun uVal' ↦
                          let tail := solEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
                            ilp wlp idp wdp rbTree ulnTree uldTree count restSG
                          uVal' :: tail
/-- Evaluate single WKB pulse `t` into a `SolSparsePulse` (`1 ≤ wLo`). -/
def solEvalWkbPulse (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (t : ℕ) : SolSparsePulse :=
  let tauNumZ := Int.ofNat q.tauNum
  let tauDenZ := Int.ofNat q.tauDen
  let rZ := Int.ofNat q.r
  let tZ := Int.ofNat t
  solSeqInt (Int.ediv (Int.mul (Int.mul tZ tauNumZ) 1024) tauDenZ) fun phiQ ↦
    solSeqInt (Int.sub phiTotQ phiQ) fun dPhiQ ↦
      let accTerm := Int.ediv
        (Int.mul (Int.mul (Int.ediv (Int.mul q.accelQ sMaxQ) 1024) tZ) tZ) km1Sq
      solSeqInt (Int.add (Int.add q.sOffQ (Int.ediv (Int.mul q.vBulkQ phiQ) 1024)) accTerm)
        fun scQ ↦
          let hasLnch : Bool := solBleZ phiQ 36863
          let hasLand : Bool := solBleZ dPhiQ 36863
          let sLoQ : ℤ :=
            cond hasLnch
              0
              (
              cond hasLand
              (solMinZ (Int.sub scQ 32768) (Int.sub sMaxQ 36864))
              (Int.sub scQ 32768))
          let sHiQ : ℤ :=
            cond hasLand
              sMaxQ
              (
              cond hasLnch
              (solMaxZ (Int.add scQ 32768) 37888)
              (Int.add scQ 32768))
          let lM1 := solMaxNat 1 (Nat.sub q.L 1)
          let twoKR := Int.mul 2048 rZ
          let den4M := Int.mul 4194304 rZ
          let wLo : ℕ :=
            cond (solBleZ sLoQ 0)
              1
              (
              cond (solBleZ twoKR sLoQ)
              lM1
              (
              let remLo := Int.sub twoKR sLoQ
              let qLo := Int.ediv (Int.mul remLo remLo) den4M
              let cand := Int.sub (Int.sub rZ qLo) 2
              solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let wHi : ℕ :=
            cond (solBleZ sHiQ 0)
              0
              (
              cond (solBleZ twoKR sHiQ)
              lM1
              (
              let remHi := Int.sub twoKR sHiQ
              let qHi := Int.ediv (Int.mul remHi remHi) den4M
              let cand := Int.add (Int.sub rZ qHi) 2
              solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let (ilp, wlp) := cond hasLnch (solLinIdxFrac phiQ 36864 17) (0, 0)
          let (idp, wdp) := cond hasLand (solLinIdxFrac dPhiQ 36864 17) (0, 0)
          solLitNat wLo fun wLo' ↦
            solLitNat (cond (Nat.ble wLo' wHi) (Nat.sub (Nat.add wHi 1) wLo') 0)
              fun count ↦
                let vNum : ℤ :=
                  cond hasLand
                    (
                    let (ivd, wvd) := solLinIdxFrac dPhiQ 36864 23
                    let rv := solLerp1024 (solLookupPair vdTree ivd) wvd
                    solSeqInt
                      (Int.ediv (Int.mul (Int.mul tauNumZ gTopQ) rv) (Int.mul 2048 tauDenZ))
                      fun thHv ↦
                        Int.add thHv (Int.ediv (Int.mul (Int.mul thHv thHv) thHv) 30000000000))
                    0
                solSeqInt vNum fun vNum' ↦
                  solSeqList (solDropSG wLo' sgArr) fun sgSub ↦
                    solWithIntList
                      (solEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
                        ilp wlp idp wdp rbTree ulnTree uldTree count sgSub)
                      fun uWin' ↦
                        ⟨wLo', uWin', vNum'⟩
/-- Structural loop unrolling `rem` WKB pulses starting at pulse index `t`. -/
def solUnrollWkbLoop (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) :
    ℕ → ℕ → List SolSparsePulse
  | _, 0 => []
  | t, rem + 1 =>
      solSeqPulse
        (solEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t)
        fun sp ↦
          solLitNat (Nat.add t 1) fun tNext ↦
            let rest := solUnrollWkbLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
              rbTree ulnTree uldTree vdTree tNext rem
            sp :: rest
theorem solUnrollWkbLoop_succ (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ ×
  ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) (t rem : ℕ) : solUnrollWkbLoop q sMaxQ gTopQ
  phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t (rem + 1) = solEvalWkbPulse q sMaxQ gTopQ
  phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t :: solUnrollWkbLoop q sMaxQ gTopQ phiTotQ
  km1Sq sgArr rbTree ulnTree uldTree vdTree (t + 1) rem := by
  simp only [solUnrollWkbLoop, solSeqPulse_eq, solLitNat_eq, solNatAdd_eq]
theorem solUnrollWkbLoop_add (q : SolWkbSched) (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ ×
  ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) : ∀ (t a b : ℕ), solUnrollWkbLoop q sMaxQ gTopQ
  phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t (a + b) = solUnrollWkbLoop q sMaxQ gTopQ
  phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t a ++ solUnrollWkbLoop q sMaxQ gTopQ phiTotQ
  km1Sq sgArr rbTree ulnTree uldTree vdTree (t + a) b
  | t, 0, b => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | t, a + 1, b => by
    have h1 : a + 1 + b = (a + b) + 1 := (by omega); have h2 : t + (a + 1) = (t + 1) + a :=
      (by omega); rw [h1, solUnrollWkbLoop_succ, solUnrollWkbLoop_succ, List.cons_append,
      solUnrollWkbLoop_add q sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree (t + 1) a
      b, h2]
/-- Unroll `len` pulses starting at pulse index `t0` from `q: SolWkbSched` in `O(L + len)`
  with strict `solWithPairTree` tree forcing. -/
def solUnrollWkbSlice (q : SolWkbSched) (t0 len : ℕ) : List SolSparsePulse :=
  solSeqList (solRevSGList (solBuildWkbSGRev q.r 0 (Nat.add q.L 1) []) []) fun sgArr ↦
    solSeqInt (sgArr.getD (Nat.sub q.L 1) (0, 0)).1 fun sMaxQ ↦
      let gTopNat := solFloorIsqrt
        (Nat.div (Nat.mul 1048576 (Nat.sub q.r (Nat.sub q.L 1))) q.r)
      solSeqInt (Int.ofNat gTopNat) fun gTopQ ↦
        let km1 := Int.ofNat (solMaxNat 1 (Nat.sub q.K 1))
        solSeqInt (Int.mul km1 km1) fun km1Sq ↦
          solSeqInt
            (Int.ediv
              (Int.mul (Int.mul (Int.ofNat (Nat.sub q.K 1)) (Int.ofNat q.tauNum)) 1024)
              (Int.ofNat q.tauDen))
            fun phiTotQ ↦
              solWithPairTree (solBuildPairTree q.rBulkQ 8) fun rbTree ↦
                solWithPairTree (solBuildPairTree q.uLnchQ 10) fun ulnTree ↦
                  solWithPairTree (solBuildPairTree q.uLandQ 10) fun uldTree ↦
                    solWithPairTree (solBuildPairTree q.vDrainQ 6) fun vdTree ↦
                      solRevForcePulseList
                        (solRevForcePulseList
                          (solUnrollWkbLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
                            rbTree ulnTree uldTree vdTree t0 len) []) []
theorem solUnrollWkbSlice_zero (q : SolWkbSched) (t0 : ℕ) : solUnrollWkbSlice q t0 0 = [] := by
  unfold solUnrollWkbSlice; simp only [solSeqList_eq, solSeqInt_eq, solWithPairTree_eq,
    solRevForcePulseList_id, solUnrollWkbLoop]
theorem solUnrollWkbSlice_add (q : SolWkbSched) (t0 a b : ℕ) : solUnrollWkbSlice q t0 (a + b) =
  solUnrollWkbSlice q t0 a ++ solUnrollWkbSlice q (t0 + a) b := by
  unfold solUnrollWkbSlice; simp only [solSeqList_eq, solSeqInt_eq, solWithPairTree_eq,
    solRevForcePulseList_id]; exact solUnrollWkbLoop_add q _ _ _ _ _ _ _ _ _ t0 a b
/-- Unroll a `SolWkbSched` into its exact `K`-pulse `List SolSparsePulse` trajectory. -/
def solUnrollWkbPulses (q : SolWkbSched) : List SolSparsePulse :=
  solUnrollWkbSlice q 0 q.K
/-- Zero-test on `IvInt` via `solBeqZ`. -/
def solIvIsZero (iv : IvInt) : Bool :=
  solBeqZ iv.1 0 && solBeqZ iv.2 0
theorem memIvInt_zero_of_solIvIsZero {x : ℝ} {iv : IvInt} (hz : solIvIsZero iv = true) (hm :
  memIvInt x iv) : x = 0 := by
  unfold solIvIsZero at hz; rw [Bool.and_eq_true, solBeqZ_eq_decide, solBeqZ_eq_decide,
    decide_eq_true_eq, decide_eq_true_eq] at hz; unfold memIvInt at hm; rw [hz.1, hz.2,
    Int.cast_zero, zero_div] at hm; linarith [hm.1, hm.2]
/-- Zero-skip causal Grover `SO(2)` walk on `k` active pairs. -/
def solGroverWalk : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, ts, cs =>
      let ce := headZP cs
      let co := secondZP cs
      solSeqList (drop1TrigP ts) fun ts' ↦
        solSeqList (drop2ZP cs) fun cs' ↦
          cond (solBeqZ ce 0 && solBeqZ co 0)
            (
            let rest := solGroverWalk k ts' cs'
            (0, 0) :: (0, 0) :: rest)
            (
            match headTrigP ts with
            | (cw, sw) =>
                solSeqIv (ivSubIntP (solIvScaleZ cw ce) (solIvScaleZ sw co)) fun e' ↦
                  solSeqIv (ivAddIntP (solIvScaleZ sw ce) (solIvScaleZ cw co)) fun o' ↦
                    let rest := solGroverWalk k ts' cs'
                    e' :: o' :: rest)
theorem solGroverWalk_length : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ), (solGroverWalk k
  ts cs).length = 2 * k
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
    unfold solGroverWalk; rw [solSeqList_eq, solSeqList_eq]; dsimp only; by_cases hz : (solBeqZ
      (headZP cs) 0 && solBeqZ (secondZP cs) 0) = true
    · simp only [hz, Bool.cond_true, List.length_cons, solGroverWalk_length k]; omega
    · have hzf : (solBeqZ (headZP cs) 0 && solBeqZ (secondZP cs) 0) = false := Bool.eq_false_iff.mpr
        hz; rcases headTrigP ts with ⟨cw, sw⟩; simp only [hzf, Bool.cond_false, solSeqIv_eq,
        List.length_cons, solGroverWalk_length k]; omega
theorem solGroverWalk_getD : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ) (j : ℕ), j < 2 * k
    → (solGroverWalk k ts cs).getD j (0, 0) =
      let w := j / 2; let ce := cs.getD (2 * w) 0; let co := cs.getD (2 * w + 1) 0
      if ce = 0 ∧ co = 0 then (0, 0)
      else
        match ts.getD w ((0, 0), (0, 0)) with
        | (cw, sw) =>
            if j % 2 = 0 then ivSubInt (ivMulInt cw (ce, ce)) (ivMulInt sw (co, co))
            else ivAddInt (ivMulInt sw (ce, ce)) (ivMulInt cw (co, co))
  | 0, _, _, _, hj => by omega
  | k + 1, ts, cs, j, hj => by
      unfold solGroverWalk; rw [solSeqList_eq, solSeqList_eq, headZP_eq, secondZP_eq, headTrigP_eq]
      dsimp only; by_cases hz : cs.getD 0 0 = 0 ∧ cs.getD 1 0 = 0
      · have hbt : (solBeqZ (cs.getD 0 0) 0 && solBeqZ (cs.getD 1 0) 0) = true := by
          rw [solBeqZ_eq_decide, solBeqZ_eq_decide, decide_eq_true hz.1,
            decide_eq_true hz.2]; rfl
        rw [hbt, Bool.cond_true]; rcases j with _ | _ | j'
        · rw [List.getD_cons_zero, show (0 : ℕ) / 2 = 0 from rfl, Nat.mul_zero, zero_add,
            ite_eq_left hz]
        · rw [List.getD_cons_succ, List.getD_cons_zero, show (1 : ℕ) / 2 = 0 from rfl, Nat.mul_zero,
            zero_add, ite_eq_left hz]
        · have hj' : j' < 2 * k := (by omega); have hd : (j' + 1 + 1) / 2 = j' / 2 + 1 := (by omega)
          have hm : (j' + 1 + 1) % 2 = j' % 2 := (by omega); have hc0 : 2 * (j' / 2 + 1) = 2 * (j' /
            2) + 2 := (by omega); have hc1 : 2 * (j' / 2) + 2 + 1 = (2 * (j' / 2) + 1) + 2 :=
            (by omega); rw [List.getD_cons_succ, List.getD_cons_succ, solGroverWalk_getD k
            (drop1TrigP ts) (drop2ZP cs) j' hj']; dsimp only; rw [hd, hm, hc0, hc1, drop1TrigP_getD,
            drop2ZP_getD, drop2ZP_getD]
      · have hbf : (solBeqZ (cs.getD 0 0) 0 && solBeqZ (cs.getD 1 0) 0) = false := by
          rw [Bool.eq_false_iff]; intro hb; rw [Bool.and_eq_true, solBeqZ_eq_decide,
            solBeqZ_eq_decide, decide_eq_true_eq, decide_eq_true_eq] at hb; exact hz hb
        rw [hbf, Bool.cond_false]; rcases j with _ | _ | j'
        · rw [show (0 : ℕ) / 2 = 0 from rfl, Nat.mul_zero, zero_add, ite_eq_right hz]
          rcases ts.getD 0 ((0, 0), (0, 0)) with ⟨cw, sw⟩; dsimp only; rw [solSeqIv_eq, solSeqIv_eq,
            List.getD_cons_zero, ivSubIntP_eq, solIvScaleZ_eq, solIvScaleZ_eq, ite_eq_left (rfl : (0
            : ℕ) % 2 = 0)]
        · have hm1 : ¬((1 : ℕ) % 2 = 0) := (by omega); rw [show (1 : ℕ) / 2 = 0 from rfl,
            Nat.mul_zero, zero_add, ite_eq_right hz]; rcases ts.getD 0 ((0, 0), (0, 0)) with ⟨cw,
            sw⟩; dsimp only; rw [solSeqIv_eq, solSeqIv_eq, List.getD_cons_succ, List.getD_cons_zero,
            ivAddIntP_eq, solIvScaleZ_eq, solIvScaleZ_eq, ite_eq_right hm1]
        · have hj' : j' < 2 * k := (by omega); have hd : (j' + 1 + 1) / 2 = j' / 2 + 1 := (by omega)
          have hm : (j' + 1 + 1) % 2 = j' % 2 := (by omega); have hc0 : 2 * (j' / 2 + 1) = 2 * (j' /
            2) + 2 := (by omega); have hc1 : 2 * (j' / 2) + 2 + 1 = (2 * (j' / 2) + 1) + 2 :=
            (by omega); rcases ts.getD 0 ((0, 0), (0, 0)) with ⟨cw, sw⟩; dsimp only
          rw [solSeqIv_eq, solSeqIv_eq, List.getD_cons_succ, List.getD_cons_succ, solGroverWalk_getD
            k (drop1TrigP ts) (drop2ZP cs) j' hj']; dsimp only; rw [hd, hm, hc0, hc1,
            drop1TrigP_getD, drop2ZP_getD, drop2ZP_getD]
theorem memIvInt_solGroverWalk {L hNext : ℕ} (_hhL : hNext ≤ L) {csR : Fin L → ℝ × ℝ} {trigIvs :
  List (IvInt × IvInt)} (htrig : ∀ w : Fin L, memIvInt (csR w).1 (trigIvs.getD w.1 ((0, 0), (0,
  0))).1 ∧ memIvInt (csR w).2 (trigIvs.getD w.1 ((0, 0), (0, 0))).2) {cPref : List ℤ} (hclen :
  cPref.length ≤ 2 * hNext) :
    let naR := swLGroverRotVec L csR (decodeCenterReal L cPref)
    let naIv := solGroverWalk hNext trigIvs cPref
    (∀ j : Fin (2 * L), memIvInt (naR j) (naIv.getD j.1 (0, 0))) ∧ (∀ j : Fin (2 * L), cPref.length
      ≤ 2 * (j.1 / 2) → naR j = 0 ∧ naIv.getD j.1 (0, 0) = (0, 0)) := by
  intro naR naIv; have hvan : ∀ j : Fin (2 * L), cPref.length ≤ 2 * (j.1 / 2) →
      naR j = 0 ∧ naIv.getD j.1 (0, 0) = (0, 0) := by
    intro j hge; have hce0 : cPref.getD (2 * (j.1 / 2)) 0 = 0 :=
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl)
    have hco0 : cPref.getD (2 * (j.1 / 2) + 1) 0 = 0 :=
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl)
    have hnaR0 : naR j = 0 := by
      dsimp only [naR]; unfold swLGroverRotVec decodeCenterReal; dsimp only; rw [hce0, hco0]; simp
    refine ⟨hnaR0, ?_⟩; by_cases hj_lt : j.1 < 2 * hNext
    · dsimp only [naIv]; rw [solGroverWalk_getD hNext trigIvs cPref j.1 hj_lt]; dsimp only
      exact ite_eq_left ⟨hce0, hco0⟩
    · dsimp only [naIv]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [solGroverWalk_length]; omega)]; rfl
  refine ⟨fun j ↦ ?_, hvan⟩; by_cases hj_lt : j.1 < 2 * hNext
  · dsimp only [naIv]; rw [solGroverWalk_getD hNext trigIvs cPref j.1 hj_lt]; set w : Fin L := ⟨j.1
      / 2, by omega⟩; have hw_val : j.1 / 2 = w.1 := rfl; dsimp only
    rw [hw_val]; by_cases hz : cPref.getD (2 * w.1) 0 = 0 ∧ cPref.getD (2 * w.1 + 1) 0 = 0
    · rw [ite_eq_left hz]
      have hna0 : naR j = 0 := by
        dsimp only [naR]; unfold swLGroverRotVec decodeCenterReal; change (if j.1 % 2 = 0 then (csR
          w).1 * ((cPref.getD (2 * w.1) 0 : ℝ) / (swScale : ℝ)) - (csR w).2 * ((cPref.getD (2 * w.1
          + 1) 0 : ℝ) / (swScale : ℝ)) else (csR w).2 * ((cPref.getD (2 * w.1) 0 : ℝ) / (swScale :
          ℝ)) + (csR w).1 * ((cPref.getD (2 * w.1 + 1) 0 : ℝ) / (swScale : ℝ))) = 0; rw [hz.1,
          hz.2]; simp
      rw [hna0]; exact memIvInt_zero
    · rw [ite_eq_right hz]; rcases htrig w with ⟨hcw, hsw⟩; generalize trigIvs.getD w.1 ((0, 0), (0,
        0)) = p at hcw hsw ⊢; rcases p with ⟨cwIv, swIv⟩
      dsimp only at hcw hsw ⊢; have hae : memIvInt (decodeCenterReal L cPref ⟨2 * w.1, by omega⟩)
          (cPref.getD (2 * w.1) 0, cPref.getD (2 * w.1) 0) := ⟨le_rfl, le_rfl⟩
      have hao : memIvInt (decodeCenterReal L cPref ⟨2 * w.1 + 1, by omega⟩) (cPref.getD (2 * w.1 +
        1) 0, cPref.getD (2 * w.1 + 1) 0) := ⟨le_rfl, le_rfl⟩
      dsimp only [naR]; unfold swLGroverRotVec; dsimp only; split_ifs
      · exact memIvInt_ivSubInt (memIvInt_ivMulInt hcw hae) (memIvInt_ivMulInt hsw hao)
      · exact memIvInt_ivAddInt (memIvInt_ivMulInt hsw hae) (memIvInt_ivMulInt hcw hao)
  · rcases hvan j (by omega) with ⟨hr0, hi0⟩; rw [hr0, hi0]; exact memIvInt_zero
/-- Window-sparse zero-skip Pieri + weak-measurement walk on `2 * m + 1` tail intervals. -/
def solPieriWalkAux (uvDenZ : ℤ) (cv : IvInt) :
    ℕ → ℕ → List ℤ → List IvInt → List IvInt
  | 0, _, _, ss =>
      let lastIv := headIvP ss
      (cond ((solBeqZ cv.1 swScale && solBeqZ cv.2 swScale) || solIvIsZero lastIv)
         lastIv
         (solIvMul cv lastIv)) :: []
  | m + 1, sk, us, ss =>
      let lv := headIvP ss
      let rv := secondIvP ss
      solSeqList (drop2IvP ss) fun ss' ↦
        match sk with
        | s + 1 =>
            let rest := solPieriWalkAux uvDenZ cv m s us ss'
            lv :: rv :: rest
        | 0 =>
            match us with
            | [] =>
                let rest := solPieriWalkAux uvDenZ cv m 0 [] ss'
                lv :: rv :: rest
            | u :: us' =>
                cond (solBeqZ u 0)
                  (
                  let rest := solPieriWalkAux uvDenZ cv m 0 us' ss'
                  lv :: rv :: rest)
                  (
                  cond (solIvIsZero lv && solIvIsZero rv)
                  (
                  let rest := solPieriWalkAux uvDenZ cv m 0 us' ss'
                  (0, 0) :: (0, 0) :: rest)
                  (
                  match solIvPythag u uvDenZ with
                  | (cu, su) =>
                      solSeqIv (ivSubIntP (solIvMul cu lv) (solIvMul su rv)) fun l' ↦
                        solSeqIv (ivAddIntP (solIvMul su lv) (solIvMul cu rv)) fun r' ↦
                          let rest := solPieriWalkAux uvDenZ cv m 0 us' ss'
                          l' :: r' :: rest))
/-- Full `2 * hNext`-element sparse Pieri + weak-measurement walk (`1 ≤ hNext`). -/
def solPieriWalk (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse)
    (naIv : List IvInt) : List IvInt :=
  match hNext with
  | 0 => []
  | m + 1 =>
      solSeqList (drop1IvP naIv) fun ss ↦
        headIvP naIv ::
          solPieriWalkAux (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin ss
theorem solPieriWalkAux_length (uvDenZ : ℤ) (cv : IvInt) : ∀ (m sk : ℕ) (us : List ℤ) (ss : List
  IvInt), (solPieriWalkAux uvDenZ cv m sk us ss).length = 2 * m + 1
  | 0, _, _, _ => rfl
  | m + 1, s + 1, us, ss => by
    simp only [solPieriWalkAux, solSeqList_eq, List.length_cons, solPieriWalkAux_length uvDenZ
      cv m]; omega
  | m + 1, 0, [], ss => by
    simp only [solPieriWalkAux, solSeqList_eq, List.length_cons, solPieriWalkAux_length uvDenZ
      cv m]; omega
  | m + 1, 0, u :: us', ss => by
    unfold solPieriWalkAux; rw [solSeqList_eq]; dsimp only; by_cases hu0 : solBeqZ u 0 = true
    · simp only [hu0, Bool.cond_true, List.length_cons,
        solPieriWalkAux_length uvDenZ cv m]; omega
    · have hu0f : solBeqZ u 0 = false := Bool.eq_false_iff.mpr hu0; simp only [hu0f,
        Bool.cond_false]; by_cases hzv : (solIvIsZero (headIvP ss) && solIvIsZero (secondIvP ss)) =
        true
      · simp only [hzv, Bool.cond_true, List.length_cons,
          solPieriWalkAux_length uvDenZ cv m]; omega
      · have hzvf : (solIvIsZero (headIvP ss) && solIvIsZero (secondIvP ss)) = false :=
          Bool.eq_false_iff.mpr hzv; rcases solIvPythag u uvDenZ with ⟨cu, su⟩; simp only [hzvf,
          Bool.cond_false, solSeqIv_eq, List.length_cons, solPieriWalkAux_length uvDenZ cv m]; omega
theorem solPieriWalkAux_mem (uvDen : ℕ) (hden : 0 < uvDen) (cv : IvInt) (cReal : ℝ) (hcv : memIvInt
  cReal cv) (hcv_one : cv = (swScale, swScale) → cReal = 1) : ∀ (m sk : ℕ) (us : List ℤ) (ss : List
  IvInt) (naF : ℕ → ℝ) (idx : ℕ), idx < 2 * m + 1 → (∀ t < 2 * m + 1, memIvInt (naF t) (ss.getD t
  (0, 0))) →
      let uAt : ℕ → ℤ := fun k ↦ if sk ≤ k then us.getD (k - sk) 0 else 0
      let rVal : ℝ :=
        if idx < 2 * m then
          let k := idx / 2; let cuR := swLCayleyCos (uAt k) uvDen
          let suR := swLCayleySin (uAt k) uvDen
          if idx % 2 = 0 then cuR * naF (2 * k) - suR * naF (2 * k + 1)
          else suR * naF (2 * k) + cuR * naF (2 * k + 1)
        else cReal * naF (2 * m)
      memIvInt rVal ((solPieriWalkAux (Int.ofNat uvDen) cv m sk us ss).getD idx (0, 0))
  | 0, _, _, ss, naF, idx, hidx, hna => by
      have hi0 : idx = 0 := (by omega); subst hi0; have h0 := hna 0 (by omega)
      unfold solPieriWalkAux; rw [headIvP_eq]
      dsimp only; simp only [Nat.lt_irrefl, ↓reduceIte, Nat.mul_zero, List.getD_cons_zero]
      by_cases hc : ((solBeqZ cv.1 swScale && solBeqZ cv.2 swScale) ||
          solIvIsZero (ss.getD 0 (0, 0))) = true
      · simp only [hc, Bool.cond_true]; rw [Bool.or_eq_true] at hc; rcases hc with hc1 | hcz
        · rw [Bool.and_eq_true, solBeqZ_eq_decide, solBeqZ_eq_decide, decide_eq_true_eq,
            decide_eq_true_eq] at hc1; have hcv_eq : cv = (swScale, swScale) := Prod.ext hc1.1 hc1.2
          rw [hcv_one hcv_eq, one_mul]; exact h0
        · have hz0 : naF 0 = 0 := memIvInt_zero_of_solIvIsZero hcz h0; rw [hz0, mul_zero]
          rw [hz0] at h0; exact h0
      · have hcf : ((solBeqZ cv.1 swScale && solBeqZ cv.2 swScale) ||
            solIvIsZero (ss.getD 0 (0, 0))) = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.cond_false, solIvMul_eq]; exact memIvInt_ivMulInt hcv h0
  | m + 1, sk, us, ss, naF, idx, hidx, hna => by
      have hd_ne : (uvDen : ℝ) ^ 2 ≠ 0 := (by positivity)
      have hcay0 : swLCayleyCos 0 uvDen = 1 ∧ swLCayleySin 0 uvDen = 0 := by
        refine ⟨?_, ?_⟩
        · unfold swLCayleyCos; simp [div_self hd_ne]
        · unfold swLCayleySin; simp
      have hlv := hna 0 (by omega); have hrv := hna 1 (by omega)
      have hna' : ∀ t < 2 * m + 1, memIvInt (naF (t + 2)) ((drop2IvP ss).getD t (0, 0)) := by
        intro t ht; rw [drop2IvP_getD]; exact hna (t + 2) (by omega)
      rcases idx with _ | _ | idx'
      · -- idx = 0
        have hlt0 : 0 < 2 * (m + 1) := (by omega)
        dsimp only; simp only [hlt0, ↓reduceIte, Nat.zero_div, Nat.mul_zero, zero_add]
        rcases sk with _ | s
        · rcases us with _ | ⟨u, us'⟩
          · simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self, List.getD_nil, hcay0.1, hcay0.2,
              one_mul, zero_mul, sub_zero, solPieriWalkAux, solSeqList_eq, headIvP_eq,
              List.getD_cons_zero]; exact hlv
          · simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
            unfold solPieriWalkAux; rw [solSeqList_eq, headIvP_eq, secondIvP_eq]; dsimp only
            by_cases hu0 : solBeqZ u 0 = true
            · have hu_eq : u = 0 := (by rwa [solBeqZ_eq_decide, decide_eq_true_eq] at hu0)
              simp only [hu_eq, hcay0.1, hcay0.2, one_mul, zero_mul, sub_zero]; exact hlv
            · have hu0f : solBeqZ u 0 = false := Bool.eq_false_iff.mpr hu0
              simp only [hu0f, Bool.cond_false]
              by_cases hzv : (solIvIsZero (ss.getD 0 (0, 0)) &&
                  solIvIsZero (ss.getD 1 (0, 0))) = true
              · rw [Bool.and_eq_true] at hzv
                simp only [hzv, Bool.and_self, Bool.cond_true, List.getD_cons_zero,
                  memIvInt_zero_of_solIvIsZero hzv.1 hlv, memIvInt_zero_of_solIvIsZero hzv.2 hrv,
                  mul_zero, sub_zero]; exact memIvInt_zero
              · have hzvf : (solIvIsZero (ss.getD 0 (0, 0)) &&
                    solIvIsZero (ss.getD 1 (0, 0))) = false := Bool.eq_false_iff.mpr hzv
                rw [hzvf, Bool.cond_false, solIvPythag_eq, Int.ofNat_eq_natCast]
                rcases memIvInt_ivPythag u hden with ⟨hcu, hsu⟩
                generalize ivPythag u (uvDen : ℤ) = py at hcu hsu ⊢; rcases py with ⟨cu, su⟩
                dsimp only at hcu hsu ⊢
                simp only [solSeqIv_eq, List.getD_cons_zero, ivSubIntP_eq, solIvMul_eq]
                exact memIvInt_ivSubInt (memIvInt_ivMulInt hcu hlv) (memIvInt_ivMulInt hsu hrv)
        · have hnle : ¬(s + 1 ≤ 0) := (by omega)
          simp only [hnle, ↓reduceIte, hcay0.1, hcay0.2, one_mul, zero_mul, sub_zero,
            solPieriWalkAux, solSeqList_eq, headIvP_eq, List.getD_cons_zero]; exact hlv
      · -- idx = 1
        have hlt1 : 1 < 2 * (m + 1) := (by omega); have hd1 : 1 / 2 = 0 := rfl
        have hm1 : ¬(1 % 2 = 0) := (by omega)
        dsimp only; simp only [hlt1, ↓reduceIte, hd1, hm1, Nat.mul_zero, zero_add]
        rcases sk with _ | s
        · rcases us with _ | ⟨u, us'⟩
          · simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self, List.getD_nil, hcay0.1, hcay0.2,
              one_mul, zero_mul, zero_add, solPieriWalkAux, solSeqList_eq, secondIvP_eq,
              List.getD_cons_succ, List.getD_cons_zero]; exact hrv
          · simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
            unfold solPieriWalkAux; rw [solSeqList_eq, headIvP_eq, secondIvP_eq]; dsimp only
            by_cases hu0 : solBeqZ u 0 = true
            · have hu_eq : u = 0 := (by rwa [solBeqZ_eq_decide, decide_eq_true_eq] at hu0)
              simp only [hu_eq, hcay0.1, hcay0.2, one_mul, zero_mul, zero_add]; exact hrv
            · have hu0f : solBeqZ u 0 = false := Bool.eq_false_iff.mpr hu0
              simp only [hu0f, Bool.cond_false]
              by_cases hzv : (solIvIsZero (ss.getD 0 (0, 0)) &&
                  solIvIsZero (ss.getD 1 (0, 0))) = true
              · rw [Bool.and_eq_true] at hzv
                simp only [hzv, Bool.and_self, Bool.cond_true, List.getD_cons_succ,
                  List.getD_cons_zero, memIvInt_zero_of_solIvIsZero hzv.1 hlv,
                  memIvInt_zero_of_solIvIsZero hzv.2 hrv, mul_zero, add_zero]; exact memIvInt_zero
              · have hzvf : (solIvIsZero (ss.getD 0 (0, 0)) &&
                    solIvIsZero (ss.getD 1 (0, 0))) = false := Bool.eq_false_iff.mpr hzv
                rw [hzvf, Bool.cond_false, solIvPythag_eq, Int.ofNat_eq_natCast]
                rcases memIvInt_ivPythag u hden with ⟨hcu, hsu⟩
                generalize ivPythag u (uvDen : ℤ) = py at hcu hsu ⊢; rcases py with ⟨cu, su⟩
                dsimp only at hcu hsu ⊢
                simp only [solSeqIv_eq, List.getD_cons_succ, List.getD_cons_zero,
                  ivAddIntP_eq, solIvMul_eq]
                exact memIvInt_ivAddInt (memIvInt_ivMulInt hsu hlv) (memIvInt_ivMulInt hcu hrv)
        · have hnle : ¬(s + 1 ≤ 0) := (by omega)
          simp only [hnle, ↓reduceIte, hcay0.1, hcay0.2, one_mul, zero_mul, zero_add,
            solPieriWalkAux, solSeqList_eq, secondIvP_eq, List.getD_cons_succ, List.getD_cons_zero]
          exact hrv
      · -- idx = idx' + 2
        have hidx' : idx' < 2 * m + 1 := (by omega)
        have hd : (idx' + 1 + 1) / 2 = idx' / 2 + 1 := (by omega)
        have hmod : (idx' + 1 + 1) % 2 = idx' % 2 := (by omega)
        have hk0 : 2 * (idx' / 2 + 1) = 2 * (idx' / 2) + 2 := (by omega)
        have hk1 : 2 * (idx' / 2) + 2 + 1 = (2 * (idx' / 2) + 1) + 2 := (by omega)
        have htop : 2 * (m + 1) = 2 * m + 2 := (by omega)
        have hrVal_eq (sk' : ℕ) (us_next : List ℤ)
            (hu_at : (if sk ≤ idx' / 2 + 1 then us.getD (idx' / 2 + 1 - sk) 0 else 0) =
              if sk' ≤ idx' / 2 then us_next.getD (idx' / 2 - sk') 0 else 0) :
            (if idx' + 1 + 1 < 2 * (m + 1) then
              let k := (idx' + 1 + 1) / 2
              let cuR := swLCayleyCos (if sk ≤ k then us.getD (k - sk) 0 else 0) uvDen
              let suR := swLCayleySin (if sk ≤ k then us.getD (k - sk) 0 else 0) uvDen
              if (idx' + 1 + 1) % 2 = 0 then cuR * naF (2 * k) - suR * naF (2 * k + 1)
              else suR * naF (2 * k) + cuR * naF (2 * k + 1)
            else cReal * naF (2 * (m + 1))) =
            (if idx' < 2 * m then
              let k := idx' / 2
              let cuR := swLCayleyCos (if sk' ≤ k then us_next.getD (k - sk') 0 else 0) uvDen
              let suR := swLCayleySin (if sk' ≤ k then us_next.getD (k - sk') 0 else 0) uvDen
              if idx' % 2 = 0 then cuR * naF (2 * k + 2) - suR * naF (2 * k + 1 + 2)
              else suR * naF (2 * k + 2) + cuR * naF (2 * k + 1 + 2)
            else cReal * naF (2 * m + 2)) := by
          by_cases hlt : idx' < 2 * m
          · have hlt2 : idx' + 1 + 1 < 2 * (m + 1) := (by omega)
            rw [ite_eq_left hlt2, ite_eq_left hlt]; dsimp only; rw [hd, hmod, hk0, hk1, hu_at]
          · have hnlt2 : ¬(idx' + 1 + 1 < 2 * (m + 1)) := (by omega)
            rw [ite_eq_right hnlt2, ite_eq_right hlt, htop]
        rcases sk with _ | s
        · rcases us with _ | ⟨u, us'⟩
          · have hih := solPieriWalkAux_mem uvDen hden cv cReal hcv hcv_one
              m 0 [] (drop2IvP ss) (fun t ↦ naF (t + 2)) idx' hidx' hna'
            dsimp only at hih ⊢; rw [hrVal_eq 0 [] rfl]; unfold solPieriWalkAux; rw [solSeqList_eq]
            dsimp only; rw [List.getD_cons_succ, List.getD_cons_succ]; exact hih
          · have hih := solPieriWalkAux_mem uvDen hden cv cReal hcv hcv_one
              m 0 us' (drop2IvP ss) (fun t ↦ naF (t + 2)) idx' hidx' hna'
            have hu_at : (if 0 ≤ idx' / 2 + 1 then (u :: us').getD (idx' / 2 + 1 - 0) 0 else 0) =
                if 0 ≤ idx' / 2 then us'.getD (idx' / 2 - 0) 0 else 0 := by
              rw [ite_eq_left (Nat.zero_le _), ite_eq_left (Nat.zero_le _),
                Nat.sub_zero, Nat.sub_zero, List.getD_cons_succ]
            dsimp only at hih ⊢; rw [hrVal_eq 0 us' hu_at]
            unfold solPieriWalkAux; rw [solSeqList_eq]; dsimp only
            by_cases hu0 : solBeqZ u 0 = true
            · rw [hu0, Bool.cond_true, List.getD_cons_succ, List.getD_cons_succ]; exact hih
            · have hu0f : solBeqZ u 0 = false := Bool.eq_false_iff.mpr hu0
              rw [hu0f, Bool.cond_false]
              by_cases hzv : (solIvIsZero (headIvP ss) && solIvIsZero (secondIvP ss)) = true
              · rw [hzv, Bool.cond_true, List.getD_cons_succ, List.getD_cons_succ]; exact hih
              · have hzvf : (solIvIsZero (headIvP ss) && solIvIsZero (secondIvP ss)) = false :=
                  Bool.eq_false_iff.mpr hzv
                rw [hzvf, Bool.cond_false]; rcases solIvPythag u (Int.ofNat uvDen) with ⟨cu, su⟩
                dsimp only; rw [solSeqIv_eq, solSeqIv_eq, List.getD_cons_succ, List.getD_cons_succ]
                exact hih
        · have hih := solPieriWalkAux_mem uvDen hden cv cReal hcv hcv_one
            m s us (drop2IvP ss) (fun t ↦ naF (t + 2)) idx' hidx' hna'
          have hu_at : (if s + 1 ≤ idx' / 2 + 1 then us.getD (idx' / 2 + 1 - (s + 1)) 0 else 0) = if
            s ≤ idx' / 2 then us.getD (idx' / 2 - s) 0 else 0 := by
            by_cases hs : s ≤ idx' / 2
            · have hs1 : s + 1 ≤ idx' / 2 + 1 := (by omega)
              have hsub : idx' / 2 + 1 - (s + 1) = idx' / 2 - s := (by omega)
              rw [ite_eq_left hs1, ite_eq_left hs, hsub]
            · have hns1 : ¬(s + 1 ≤ idx' / 2 + 1) := (by omega)
              rw [ite_eq_right hns1, ite_eq_right hs]
          dsimp only at hih ⊢; rw [hrVal_eq s us hu_at]; unfold solPieriWalkAux; rw [solSeqList_eq]
          dsimp only; rw [List.getD_cons_succ, List.getD_cons_succ]; exact hih
/-- Trim trailing `(0, 0)` midpoint pairs from an even-length `List ℤ`. -/
def solTrimZeroPairs : List ℤ → List ℤ
  | x :: y :: rest =>
      let rTrim := solTrimZeroPairs rest
      match rTrim with
      | [] =>
          cond (solBeqZ x 0 && solBeqZ y 0)
            []
            (solSeqInt x fun x' ↦ solSeqInt y fun y' ↦ [x', y'])
      | z :: zs =>
          solSeqInt x fun x' ↦ solSeqInt y fun y' ↦ x' :: y' :: z :: zs
  | _ => []
theorem solTrimZeroPairs_spec : ∀ (cs : List ℤ), (∃ k, (solTrimZeroPairs cs).length = 2 * k ∧ 2 * k
  ≤ cs.length) ∧ (∀ j : ℕ, cs.length % 2 = 0 → (solTrimZeroPairs cs).getD j 0 = cs.getD j 0)
  | [] => ⟨⟨0, rfl, le_rfl⟩, fun _ _ ↦ rfl⟩
  | [_] => ⟨⟨0, rfl, by simp⟩, fun _ hmod ↦ by simp at hmod⟩
  | x :: y :: rest => by
    rcases solTrimZeroPairs_spec rest with ⟨⟨kr, hlen_r, hle_r⟩, hget_r⟩; unfold solTrimZeroPairs
    rcases htr : solTrimZeroPairs rest with _ | ⟨z, zs⟩
    · rw [htr] at hlen_r hget_r; by_cases hz : (solBeqZ x 0 && solBeqZ y 0) = true
      · simp only [hz, Bool.cond_true]; rw [Bool.and_eq_true, solBeqZ_eq_decide, solBeqZ_eq_decide,
          decide_eq_true_eq, decide_eq_true_eq] at hz; refine ⟨⟨0, rfl, by simp⟩, fun j hmod ↦ ?_⟩
        have hmod_r : rest.length % 2 = 0 :=
          (by rw [List.length_cons, List.length_cons] at hmod; omega); rcases j with _ | _ | j'
        · simp [hz.1]
        · simp [hz.2]
        · simpa using hget_r j' hmod_r
      · have hzf : (solBeqZ x 0 && solBeqZ y 0) = false := Bool.eq_false_iff.mpr hz; simp only [hzf,
          Bool.cond_false, solSeqInt_eq]; refine ⟨⟨1, rfl, by simp⟩, fun j hmod ↦ ?_⟩
        have hmod_r : rest.length % 2 = 0 :=
          (by rw [List.length_cons, List.length_cons] at hmod; omega); rcases j with _ | _ | j'
        · rfl
        · rfl
        · simpa using hget_r j' hmod_r
    · rw [htr] at hlen_r hget_r; simp only [solSeqInt_eq]
      refine ⟨⟨kr + 1, by simp only [List.length_cons] at hlen_r ⊢; omega,
          by simp only [List.length_cons]; omega⟩,
        fun j hmod ↦ ?_⟩
      have hmod_r : rest.length % 2 = 0 :=
        (by rw [List.length_cons, List.length_cons] at hmod; omega); rcases j with _ | _ | j'
      · rfl
      · rfl
      · change (z :: zs).getD j' 0 = rest.getD j' 0; exact hget_r j' hmod_r
/-- Non-empty causal center padding: maps `[]` to `[0, 0]` and preserves non-empty lists. -/
def solPadEmptyPair : List ℤ → List ℤ
  | [] => [0, 0]
  | x :: xs => x :: xs
theorem solPadEmptyPair_cases : ∀ l : List ℤ, (l = [] ∧ solPadEmptyPair l = [0, 0]) ∨ ∃ z zs, l = z
  :: zs ∧ solPadEmptyPair l = z :: zs
  | [] => Or.inl ⟨rfl, rfl⟩ | z :: zs => Or.inr ⟨z, zs, rfl, rfl⟩
/-- One causal window-sparse `L2Ball` pulse step `(cPref, hAct, rho, survUb) ↦...`. -/
def solPulseStepL2 (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) (sp : SolSparsePulse) :
    List ℤ × ℕ × ℕ × ℤ :=
  solLitNat (solSumSqAbs cPref 0) fun normSqC ↦
    solLitNat (solCeilIsqrt normSqC) fun normCUb ↦
      solLitNat (Nat.add normCUb rho) fun sumR ↦
        solSeqInt
          (solMinZ swScale (ceilDivScaleP (Int.ofNat (Nat.mul sumR sumR))))
          fun oneMinusCumUb ↦
            solSeqInt (Int.add survUb oneMinusCumUb) fun survUb' ↦
              solLitNat (solMinNat L (Nat.add hAct 1)) fun hNext ↦
                solWithIvList (solGroverWalk hNext trigIvs cPref) fun naIv ↦
                  solSeqIv
                    (cond (!Nat.beq hNext L || solBeqZ sp.vNum 0)
                       (swScale, swScale)
                       ((solIvPythag sp.vNum (Int.ofNat uvDen)).1))
                    fun cv ↦
                      solWithIvList (solPieriWalk hNext uvDen cv sp naIv) fun nxtIv ↦
                        match solRecenterAndRadSq nxtIv with
                        | (cNextRaw, radSqSum) =>
                            solWithIntList (solTrimZeroPairs cNextRaw) fun cTrim ↦
                              solWithIntList (solPadEmptyPair cTrim)
                                fun cOut ↦
                                  solLitNat (solMaxNat 1 (Nat.div cOut.length 2)) fun hAct' ↦
                                    solLitNat (Nat.add rho (solCeilIsqrt radSqSum)) fun rho' ↦
                                      (cOut, hAct', rho', survUb')
/-- Multi-pulse causal window-sparse `L2Ball` loop. -/
def solEvolutionL2Aux (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) :
    List SolSparsePulse → List ℤ × ℕ × ℤ
  | [] => (cPref, rho, survUb)
  | sp :: sps =>
      match solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with
      | (cNext, hAct', rho', survUb') =>
          solWithIntList cNext fun cNext' ↦
            solLitNat hAct' fun ha ↦
              solLitNat rho' fun rh ↦
                solSeqInt survUb' fun sv ↦
                  solEvolutionL2Aux L uvDen trigIvs cNext' ha rh sv sps
/-- Multi-pulse causal window-sparse `L2Ball` trajectory starting from `([swScale, 0], 1, 0,
  0)`. -/
def solEvolutionL2 (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (sps : List SolSparsePulse) : List ℤ × ℕ × ℤ :=
  solWithTrigList trigIvs fun trigIvs' ↦
    solEvolutionL2Aux L uvDen trigIvs' [swScale, 0] 1 0 0 sps
/-- Checkpointed 4-tuple causal `L2Ball` segment loop returning `(cOut, hOut, rhoOut,
  survOut)`. -/
def solEvolutionL2Seg (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt))
    (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) :
    List SolSparsePulse → List ℤ × ℕ × ℕ × ℤ
  | [] => (cPref, hAct, rho, survUb)
  | sp :: sps =>
      match solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with
      | (cNext, hAct', rho', survUb') =>
          solWithIntList cNext fun cNext' ↦
            solLitNat hAct' fun ha ↦
              solLitNat rho' fun rh ↦
                solSeqInt survUb' fun sv ↦
                  solEvolutionL2Seg L uvDen trigIvs cNext' ha rh sv sps
theorem solEvolutionL2Seg_append (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) :
    ∀ (sps1 sps2 : List SolSparsePulse) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      solEvolutionL2Seg L uvDen trigIvs cPref hAct rho survUb (sps1 ++ sps2) =
        let s1 := solEvolutionL2Seg L uvDen trigIvs cPref hAct rho survUb sps1
        solEvolutionL2Seg L uvDen trigIvs s1.1 s1.2.1 s1.2.2.1 s1.2.2.2 sps2
  | [], _, _, _, _, _ => rfl
  | sp :: sps1, sps2, cPref, hAct, rho, survUb => by
    dsimp only [List.cons_append, solEvolutionL2Seg]
    rcases solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with ⟨cNext, hAct', rho',
      survUb'⟩; dsimp only; simp only [solWithIntList_eq, solLitNat_eq, solSeqInt_eq]
    exact solEvolutionL2Seg_append L uvDen trigIvs sps1 sps2 cNext hAct' rho' survUb'
theorem solEvolutionL2Aux_eq_seg (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) :
    ∀ (sps : List SolSparsePulse) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      solEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb sps =
        let s := solEvolutionL2Seg L uvDen trigIvs cPref hAct rho survUb sps
        (s.1, s.2.2.1, s.2.2.2)
  | [], _, _, _, _ => rfl
  | sp :: sps, cPref, hAct, rho, survUb => by
    dsimp only [solEvolutionL2Aux, solEvolutionL2Seg]
    rcases solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with ⟨cNext, hAct', rho',
      survUb'⟩; dsimp only; simp only [solWithIntList_eq, solLitNat_eq, solSeqInt_eq]
    exact solEvolutionL2Aux_eq_seg L uvDen trigIvs sps cNext hAct' rho' survUb'
theorem solEvolutionL2Aux_append (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) (sps1 sps2 : List
  SolSparsePulse) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ) {c1 : List ℤ} {h1 rh1 : ℕ} {sv1 : ℤ}
  (hseg1 : solEvolutionL2Seg L uvDen trigIvs cPref hAct rho survUb sps1 = (c1, h1, rh1, sv1)) :
  solEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb (sps1 ++ sps2) = solEvolutionL2Aux L uvDen
  trigIvs c1 h1 rh1 sv1 sps2 := by
  rw [solEvolutionL2Aux_eq_seg, solEvolutionL2Seg_append]; dsimp only; rw [hseg1]; dsimp only
  rw [solEvolutionL2Aux_eq_seg L uvDen trigIvs sps2 c1 h1 rh1 sv1]
theorem swLCenter_normSq_le_len {L : ℕ} {cPref : List ℤ} (hclen : cPref.length ≤ 2 * L) : swLNormSq
  (decodeCenterReal L cPref) = (solSumSqAbs cPref 0 : ℝ) / (swScale : ℝ) ^ 2 := by
  rw [solSumSqAbs_eq]; unfold swLNormSq decodeCenterReal; simp_rw [div_pow, div_eq_mul_inv, ←
    Finset.sum_mul, ← div_eq_mul_inv]; congr 1
  have hf := swLSumSqAbs_eq cPref 0; rw [zero_add] at hf; rw [hf, Nat.cast_sum,
    Fin.sum_univ_eq_sum_range (fun i ↦ ((cPref.getD i 0 : ℝ)) ^ 2) (2 * L)]
  have hsplit : ∑ i ∈ Finset.range (2 * L), ((cPref.getD i 0 : ℝ)) ^ 2 = ∑ i ∈ Finset.range
    cPref.length, ((cPref.getD i 0 : ℝ)) ^ 2 := by
    symm; refine Finset.sum_subset (Finset.range_mono hclen) fun i _ hi_not ↦ ?_
    have hge : cPref.length ≤ i := (by simpa using hi_not); rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none hge]; simp
  rw [hsplit]; refine Finset.sum_congr rfl fun i _ ↦ ?_; rcases cPref.getD i 0 with n | n
  · simp
  · simp [Int.negSucc_eq]
theorem solPulseStepL2_sound {L uvDen : ℕ} (hL : 2 ≤ L) (hden : 1 ≤ uvDen) {cs : Fin L → ℝ × ℝ}
  {trigIvs : List (IvInt × IvInt)} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (htrig : ∀ w
  : Fin L, memIvInt (cs w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt (cs w).2 (trigIvs.getD
  w.1 ((0, 0), (0, 0))).2) {sp : SolSparsePulse} (hsp : solSparsePulseValid sp = true) {st : Fin (2
  * L) → ℝ} {cum surv : ℝ} {cPref : List ℤ} {hAct rho : ℕ} {survUb : ℤ} (hh1 : 1 ≤ hAct) (hhL : hAct
  ≤ L) (hclen : cPref.length = 2 * hAct) (hin : swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧ cum ≤ 1 ∧ 0 ≤
  surv) (hball : swLNormSq (fun j ↦ st j - decodeCenterReal L cPref j) ≤ ((rho : ℝ) / (swScale : ℝ))
  ^ 2) (hsurv : surv ≤ (survUb : ℝ) / (swScale : ℝ)) :
    let p := solToSwLPulse L uvDen sp; let outR := swLPulseStepReal L hL cs st cum surv p
    let outL2 := solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp
    1 ≤ outL2.2.1 ∧ outL2.2.1 ≤ L ∧ outL2.1.length = 2 * outL2.2.1 ∧ (swLNormSq outR.1 + outR.2.1 =
      1 ∧ 0 ≤ outR.2.1 ∧ outR.2.1 ≤ 1 ∧ 0 ≤ outR.2.2) ∧ swLNormSq (fun j ↦ outR.1 j -
      decodeCenterReal L outL2.1 j) ≤ ((outL2.2.2.1 : ℝ) / (swScale : ℝ)) ^ 2 ∧ outR.2.2 ≤
      (outL2.2.2.2 : ℝ) / (swScale : ℝ) := by
  intro p outR outL2; have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; norm_num); have hS : (0
    : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hp_val : swLPulseValid p = true :=
    (by unfold swLPulseValid p solToSwLPulse; dsimp only; rw [decide_eq_true_eq]; omega)
  have hwLo1 : 1 ≤ sp.wLo :=
    (by unfold solSparsePulseValid at hsp; rwa [natBle_eq_decide, decide_eq_true_eq] at hsp)
  have hin_next := swLPulseStepReal_normSq_add_cum hL hcs st cum surv hp_val hin
  -- Survival step bound using causal prefix normSq
  set normCUb : ℕ := ceilIsqrtNat (solSumSqAbs cPref 0)
  set oneMinusCumUb : ℤ := min swScale (-((-(((normCUb + rho : ℕ) : ℤ) ^ 2)) / swScale))
  have hcum_step : 1 - cum ≤ (oneMinusCumUb : ℝ) / (swScale : ℝ) := by
    have hc_norm : swLNormSq (decodeCenterReal L cPref) ≤ ((normCUb : ℝ) / (swScale : ℝ)) ^ 2 := by
      rw [swLCenter_normSq_le_len (by omega), div_pow]; exact div_le_div_of_nonneg_right
        (by exact_mod_cast le_ceilIsqrtNat_sq (solSumSqAbs cPref 0)) (sq_nonneg _)
    have hst_norm : swLNormSq st ≤ (((normCUb + rho : ℕ) : ℝ) / (swScale : ℝ)) ^ 2 := by
      have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg normCUb) hS.le) (div_nonneg
        (Nat.cast_nonneg rho) hS.le) hc_norm hball
      have heq_v : st = fun j ↦ decodeCenterReal L cPref j + (st j - decodeCenterReal L cPref j) :=
        (by ext j; ring); have heq_r : (normCUb : ℝ) / (swScale : ℝ) + (rho : ℝ) / (swScale : ℝ) =
        ((normCUb + rho : ℕ) : ℝ) / (swScale : ℝ) := (by push_cast; ring)
      rwa [← heq_v, heq_r] at htri
    set q : ℤ := ((normCUb + rho : ℕ) : ℤ) ^ 2; set ceilZ : ℤ := -((-q) / swScale)
    have hceil_ub : (((normCUb + rho : ℕ) : ℝ) / (swScale : ℝ)) ^ 2 ≤ (ceilZ : ℝ) / (swScale : ℝ)
      := by
      rw [div_pow, sq (swScale : ℝ), ← div_div]; refine div_le_div_of_nonneg_right ?_ hS.le
      have hd := real_le_neg_ediv_neg_pos q swScale hS_pos
      have hq_eq : (((normCUb + rho : ℕ) : ℝ)) ^ 2 = (q : ℝ) := (by dsimp [q]; push_cast; rfl)
      rwa [hq_eq]
    have heq1 : 1 - cum = swLNormSq st := (by linarith [hin.1]); rw [heq1, show oneMinusCumUb = min
      swScale ceilZ from rfl, Int.cast_min]; rcases le_total (swScale : ℝ) (ceilZ : ℝ) with h | h
    · rw [min_eq_left h, div_self hS.ne']; linarith [hin.1, hin.2.1]
    · rw [min_eq_right h]; exact hst_norm.trans hceil_ub
  set hNext : ℕ := min L (hAct + 1); have hhNext1 : 1 ≤ hNext := (by dsimp [hNext]; omega)
  have hhNextL : hNext ≤ L := min_le_left _ _; have hclen_le : cPref.length ≤ 2 * hNext :=
    (by dsimp [hNext]; omega); rcases memIvInt_solGroverWalk hhNextL htrig hclen_le with ⟨hna_mem,
    hna_van⟩; set naR := swLGroverRotVec L cs (decodeCenterReal L cPref)
  set naIv := solGroverWalk hNext trigIvs cPref
  set cv : IvInt := if hNext ≠ L ∨ sp.vNum = 0 then (swScale, swScale) else (ivPythag sp.vNum (uvDen
    : ℤ)).1; set cReal : ℝ := if hNext ≠ L ∨ sp.vNum = 0 then 1 else swLCayleyCos sp.vNum uvDen
  have hcv_mem : memIvInt cReal cv := by
    dsimp [cReal, cv]; by_cases hcond : hNext ≠ L ∨ sp.vNum = 0
    · simp [hcond, memIvInt_one]
    · simp only [hcond, ↓reduceIte]; exact (memIvInt_ivPythag sp.vNum (by omega : 0 < uvDen)).1
  have hcv_one : cv = (swScale, swScale) → cReal = 1 := by
    intro hcv_eq; dsimp [cReal]; by_cases hcond : hNext ≠ L ∨ sp.vNum = 0
    · simp [hcond]
    · push Not at hcond
      -- Even if ivPythag gives (swScale, swScale), memIvInt cReal (swScale, swScale) forces 1
      have hm := hcv_mem; rw [hcv_eq] at hm; unfold memIvInt at hm; rw [div_self hS.ne'] at hm
      linarith [hm.1, hm.2]
  set nxtIv := solPieriWalk hNext uvDen cv sp naIv
  have hnxt_len : nxtIv.length = 2 * hNext := by
    dsimp [nxtIv]; obtain ⟨m, hm⟩ : ∃ m, hNext = m + 1 := ⟨hNext - 1, by omega⟩; rw [hm]
    simp only [solPieriWalk, solSeqList_eq, List.length_cons, solPieriWalkAux_length]; omega
  set fc := (swLPulseStepReal L hL cs (decodeCenterReal L cPref) 0 0 p).1; have hfc_eq : fc =
    swLPieriAndWeakVec L hL p naR := rfl
  have hpt : ∀ j : Fin (2 * L), memIvInt (fc j) (nxtIv.getD j.1 (0, 0)) := by
    rintro ⟨jVal, hjL⟩
    obtain ⟨m, hm⟩ : ∃ m, hNext = m + 1 := ⟨hNext - 1, by omega⟩; by_cases hj_lt : jVal < 2 * hNext
    · rcases jVal with _ | j'
      · rw [hfc_eq]; dsimp [swLPieriAndWeakVec, nxtIv]; rw [hm]; simp only [solPieriWalk,
          solSeqList_eq, headIvP_eq, List.getD_cons_zero]; exact hna_mem ⟨0, hjL⟩
      · have hj'_lt : j' < 2 * m + 1 := (by omega); have hna_shift : ∀ (t : ℕ) (ht : t < 2 * m + 1),
            memIvInt (naR ⟨t + 1, by omega⟩) ((drop1IvP naIv).getD t (0, 0)) := by
          intro t ht; rw [drop1IvP_getD]; exact hna_mem ⟨t + 1, by omega⟩
        have hmem_aux := solPieriWalkAux_mem uvDen (by omega) cv cReal hcv_mem hcv_one
          m (sp.wLo - 1) sp.uWin (drop1IvP naIv)
          (fun t ↦ if ht : t + 1 < 2 * L then naR ⟨t + 1, ht⟩ else 0) j' hj'_lt
          (fun t ht ↦ by
            have htL : t + 1 < 2 * L := (by omega)
            simpa [htL] using hna_shift t ht)
        dsimp [nxtIv]; rw [hm]; simp only [solPieriWalk, solSeqList_eq, List.getD_cons_succ]
        by_cases hj'_in : j' < 2 * m
        · -- Interior Pieri coordinate
          have hj_top : j' + 1 < 2 * L - 1 := (by omega); have h1 : j' + 1 ≠ 0 := (by omega)
          have hu_eq : (if sp.wLo - 1 ≤ j' / 2 then sp.uWin.getD (j' / 2 - (sp.wLo - 1)) 0 else 0) =
            p.uNum ⟨j' / 2, by omega⟩ := by
            dsimp [p, solToSwLPulse]; unfold solSparseUNum; rw [natBle_eq_decide]
            by_cases hle : sp.wLo ≤ j' / 2 + 1
            · have hle' : sp.wLo - 1 ≤ j' / 2 := (by omega); have hsub : j' / 2 + 1 - sp.wLo = j' /
                2 - (sp.wLo - 1) := (by omega); simp [hle, hle', hsub]
            · have hle' : ¬(sp.wLo - 1 ≤ j' / 2) := (by omega); simp [hle, hle']
          have ht0 : 2 * (j' / 2) + 1 < 2 * L := (by omega); have ht1 : (2 * (j' / 2) + 1) + 1 < 2 *
            L := (by omega); dsimp only at hmem_aux; simp only [hj'_in, ↓reduceIte, ↓reduceDIte,
            hu_eq, ht0, ht1] at hmem_aux; rw [hfc_eq]
          unfold swLPieriAndWeakVec; have heq_sub : j' + 1 - 1 = j' := (by omega); have ha2 : (⟨2 *
            (j' / 2) + 2, by omega⟩ : Fin (2 * L)) = ⟨(2 * (j' / 2) + 1) + 1, ht1⟩ := rfl
          simp only [h1, ↓reduceDIte, hj_top, heq_sub, ha2]; exact hmem_aux
        · -- j' = 2 * m, so j' + 1 = 2 * hNext - 1
          have hj'_eq : j' = 2 * m := (by omega); subst hj'_eq; have ht_last : 2 * m + 1 < 2 * L :=
            hjL; dsimp only at hmem_aux
          simp only [Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte, ht_last] at hmem_aux
          by_cases hh_eq : hNext = L
          · -- Top weak-measurement coordinate 2 * L - 1
            have hj_last : 2 * m + 1 = 2 * L - 1 := (by omega)
            have hcr : cReal = swLCayleyCos sp.vNum uvDen := by
              dsimp [cReal]; by_cases hv0 : sp.vNum = 0
              · simp only [hv0, or_true, ↓reduceIte]; have hd_ne : (uvDen : ℝ) ^ 2 ≠ 0 :=
                  (by positivity); unfold swLCayleyCos; simp [div_self hd_ne]
              · simp [hh_eq, hv0]
            rw [hcr] at hmem_aux; rw [hfc_eq]; unfold swLPieriAndWeakVec; have h1 : 2 * m + 1 ≠ 0 :=
              (by omega); have hnlt : ¬(2 * m + 1 < 2 * L - 1) := (by omega); have hfin : (⟨2 * L -
              1, by omega⟩ : Fin (2 * L)) = ⟨2 * m + 1, hjL⟩ := (by ext; exact hj_last.symm)
            simp only [h1, ↓reduceDIte, hnlt, hfin]; exact hmem_aux
          · -- hNext < L, so hNext = hAct + 1 and pair hAct of naR/naIv is identically zero
            have hh_act : hNext = hAct + 1 := (by dsimp [hNext]; omega); have hm_act : m = hAct :=
              (by omega); subst m; have hv1 := hna_van ⟨2 * hAct + 1, hjL⟩ (by dsimp; omega)
            have hv2 := hna_van ⟨2 * hAct + 2, by omega⟩ (by dsimp; omega)
            rw [hv1.1, mul_zero] at hmem_aux
            have hfc0 : fc ⟨2 * hAct + 1, hjL⟩ = 0 := by
              rw [hfc_eq]; unfold swLPieriAndWeakVec; have h1 : 2 * hAct + 1 ≠ 0 := (by omega)
              have hlt_top : 2 * hAct + 1 < 2 * L - 1 := (by omega)
              have hm0 : (2 * hAct + 1 - 1) % 2 = 0 := (by omega); have hf1 : (⟨2 * ((2 * hAct + 1 -
                1) / 2) + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * hAct + 1, hjL⟩ :=
                (by ext; dsimp; omega); have hf2 : (⟨2 * ((2 * hAct + 1 - 1) / 2) + 2, by omega⟩ :
                Fin (2 * L)) = ⟨2 * hAct + 2, by omega⟩ := (by ext; dsimp; omega); simp only [h1,
                ↓reduceDIte, hlt_top, hm0, ↓reduceIte, hf1, hf2, hv1.1, hv2.1, mul_zero, sub_zero]
            rw [hfc0]; exact hmem_aux
    · -- jVal >= 2 * hNext: out-of-bounds of nxtIv is (0, 0) and fc ⟨jVal, hjL⟩ = 0
      have hget0 : nxtIv.getD jVal (0, 0) = (0, 0) :=
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hnxt_len]; omega)]; rfl)
      rw [hget0]; have _hh_lt : hNext < L := (by omega); have hh_act : hNext = hAct + 1 :=
        (by dsimp [hNext]; omega)
      have hfc0 : fc ⟨jVal, hjL⟩ = 0 := by
        rw [hfc_eq]; unfold swLPieriAndWeakVec; have h1 : jVal ≠ 0 := (by omega); simp only [h1,
          ↓reduceDIte]; by_cases hjl : jVal < 2 * L - 1
        · simp only [hjl, ↓reduceDIte]; set w0 : ℕ := (jVal - 1) / 2; have hw0_ge : hAct ≤ w0 :=
            (by dsimp [w0]; omega); have hv1 := (hna_van ⟨2 * w0 + 1, by omega⟩ (by dsimp; omega)).1
          have hv2 := (hna_van ⟨2 * w0 + 2, by omega⟩ (by dsimp; omega)).1
          dsimp only [w0] at hv1 hv2; simp only [hv1, hv2, mul_zero, sub_zero, add_zero, ite_self]
        · simp only [hjl, ↓reduceDIte]; have hv_top := (hna_van ⟨2 * L - 1, by omega⟩
            (by dsimp; omega)).1; rw [hv_top, mul_zero]
      rw [hfc0]; exact memIvInt_zero
  -- Recenter, trim, and bound radius
  have hrec_eq := solRecenterAndRadSq_eq nxtIv; rcases swLRecenterAndRadSq_eq nxtIv with ⟨hrec1,
    hrec2⟩; rcases hrec : solRecenterAndRadSq nxtIv with ⟨cNextRaw, radSqSum⟩; rw [hrec_eq] at hrec
  rw [hrec] at hrec1 hrec2; dsimp only at hrec1 hrec2
  have hraw_len : cNextRaw.length = 2 * hNext := (by rw [hrec1, List.length_map, hnxt_len])
  rcases solTrimZeroPairs_spec cNextRaw with ⟨⟨kTrim, htrim_len, htrim_le⟩, htrim_get⟩; set cTrim :=
    solTrimZeroPairs cNextRaw; set cOut : List ℤ := solPadEmptyPair cTrim
  set hAct' : ℕ := max 1 (cOut.length / 2)
  have hcOut_spec : 1 ≤ hAct' ∧ hAct' ≤ L ∧ cOut.length = 2 * hAct' ∧ ∀ j : ℕ, cOut.getD j 0 =
    cNextRaw.getD j 0 := by
    have hcOut_cases : (cTrim = [] ∧ cOut = [0, 0]) ∨ ∃ z zs, cTrim = z :: zs ∧ cOut = z :: zs :=
      solPadEmptyPair_cases cTrim; rcases hcOut_cases with ⟨hct, hcOut_eq⟩ | ⟨z, zs, hct, hcOut_eq⟩
    · have hhAct'_eq : hAct' = 1 := (by dsimp [hAct']; rw [hcOut_eq]; rfl)
      refine ⟨by omega, by omega, by rw [hcOut_eq, hhAct'_eq]; rfl, fun j ↦ ?_⟩; rw [hcOut_eq]
      have hraw0 : ([] : List ℤ).getD j 0 = cNextRaw.getD j 0 :=
        (by rw [← hct]; exact htrim_get j (by rw [hraw_len]; omega)); rcases j with _ | _ | j' <;>
        simpa using hraw0
    · have hk1 : 1 ≤ kTrim := (by have h := htrim_len; rw [hct] at h; simp at h; omega)
      have hlen_out : cOut.length = 2 * kTrim := (by rw [hcOut_eq, ← hct]; exact htrim_len)
      have hhAct'_eq : hAct' = kTrim := (by dsimp [hAct']; rw [hlen_out]; omega)
      refine ⟨by omega, by omega, by rw [hlen_out, hhAct'_eq], fun j ↦ ?_⟩; rw [hcOut_eq, ← hct];
        exact htrim_get j (by rw [hraw_len]; omega)
  have hdec_eq : decodeCenterReal L cOut = decodeCenterReal L cNextRaw :=
    (by ext j; unfold decodeCenterReal; rw [hcOut_spec.2.2.2 j.1])
  set drho : ℕ := ceilIsqrtNat radSqSum
  have hpt_err : swLNormSq (fun j ↦ fc j - decodeCenterReal L cOut j) ≤ ((drho : ℝ) / (swScale : ℝ))
    ^ 2 := by
    rw [hdec_eq]
    have hcoord : ∀ j : Fin (2 * L), (fc j - decodeCenterReal L cNextRaw j) ^ 2 ≤ (if j.1 < 2 *
      hNext then (((ivMidRad (nxtIv.getD j.1 (0, 0))).2 : ℝ) / (swScale : ℝ)) ^ 2 else 0) := fun j ↦
      by
      by_cases hj_lt : j.1 < 2 * hNext
      · simp only [hj_lt, ↓reduceIte]; have hj_nxt : j.1 < nxtIv.length :=
          (by rw [hnxt_len]; exact hj_lt)
        have hc_get : cNextRaw.getD j.1 0 = (ivMidRad (nxtIv.getD j.1 (0, 0))).1 := by
          rw [hrec1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simp [hj_nxt]), List.getElem?_eq_getElem hj_nxt,
            List.getElem_map]; simp
        unfold decodeCenterReal; rw [hc_get]; exact memIvInt_sub_center_sq_le (hpt j)
      · simp only [hj_lt, ↓reduceIte]; have hm := hpt j
        have hn0 : nxtIv.getD j.1 (0, 0) = (0, 0) := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by rw [hnxt_len]; omega)]; rfl
        rw [hn0] at hm; have hfc0 : fc j = 0 := memIvInt_zero_of_solIvIsZero rfl hm
        have hc0 : cNextRaw.getD j.1 0 = 0 :=
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hraw_len]; omega)]; rfl)
        unfold decodeCenterReal; rw [hfc0, hc0]; simp
    have hsum_le : swLNormSq (fun j ↦ fc j - decodeCenterReal L cNextRaw j) ≤ (radSqSum : ℝ) /
      (swScale : ℝ) ^ 2 := by
      refine (Finset.sum_le_sum fun j _ ↦ hcoord j).trans ?_; rw [Fin.sum_univ_eq_sum_range (fun i ↦
        if i < 2 * hNext then (((ivMidRad (nxtIv.getD i (0, 0))).2 : ℝ) / (swScale : ℝ)) ^ 2 else 0)
        (2 * L), hrec2, hnxt_len, Nat.cast_sum]; push_cast; rw [sum_div_const]
      have hsub_sum : ∑ i ∈ Finset.range (2 * L), (if i < 2 * hNext then (((ivMidRad (nxtIv.getD i
        (0, 0))).2 : ℝ) / (swScale : ℝ)) ^ 2 else 0) = ∑ i ∈ Finset.range (2 * hNext), (((ivMidRad
        (nxtIv.getD i (0, 0))).2 : ℝ)) ^ 2 / (swScale : ℝ) ^ 2 := by
        symm; refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans (Finset.sum_subset
          (Finset.range_mono (by omega : 2 * hNext ≤ 2 * L)) fun i _ hi_not ↦
          by simp [show ¬(i < 2 * hNext) by simpa using hi_not])
        rw [Finset.mem_range] at hi; simp [hi, div_pow]
      exact hsub_sum.le
    refine hsum_le.trans ?_; rw [div_pow]
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_ceilIsqrtNat_sq radSqSum) (sq_nonneg _)
  have hlip : swLNormSq (fun j ↦ outR.1 j - fc j) ≤ ((rho : ℝ) / (swScale : ℝ)) ^ 2 :=
    (swLPulseStepReal_distSq_le hL hcs hp_val st (decodeCenterReal L cPref) cum surv 0 0).trans
    hball; have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg rho) hS.le) (div_nonneg
    (Nat.cast_nonneg drho) hS.le) hlip hpt_err; have heq_vec : (fun j ↦ outR.1 j - decodeCenterReal
    L cOut j) = (fun j ↦ (outR.1 j - fc j) + (fc j - decodeCenterReal L cOut j)) := (by ext j; ring)
  have heq_rad : (rho : ℝ) / (swScale : ℝ) + (drho : ℝ) / (swScale : ℝ) = ((rho + drho : ℕ) : ℝ) /
    (swScale : ℝ) := (by push_cast; ring); rw [← heq_vec, heq_rad] at htri
  have houtL2_eq : outL2 = (cOut, hAct', rho + drho, survUb + oneMinusCumUb) := by
    have hcond_cv (b1 b2 : Bool) (hb1 : b1 = true ↔ min L (hAct + 1) = L)
        (hb2 : b2 = true ↔ sp.vNum = 0) :
        cond (Bool.not b1 || b2) (swScale, swScale)
          (solIvPythag sp.vNum (Int.ofNat uvDen)).1 = cv := by
      rw [solIvPythag_eq, Int.ofNat_eq_natCast]; dsimp [cv, hNext]
      cases b1 <;> cases b2 <;>
        simp only [Bool.false_eq_true, false_iff, true_iff] at hb1 hb2
      · rw [ite_eq_left (Or.inl hb1)]; rfl
      · rw [ite_eq_left (Or.inl hb1)]; rfl
      · rw [ite_eq_right (by tauto)]; rfl
      · rw [ite_eq_left (Or.inr hb2)]; rfl
    have hb1 := Bool.eq_iff_iff.mp (natBeq_eq_decide (min L (hAct + 1)) L)
    rw [decide_eq_true_eq] at hb1
    have hb2 := Bool.eq_iff_iff.mp (solBeqZ_eq_decide sp.vNum 0)
    rw [decide_eq_true_eq] at hb2
    have hcv_b := hcond_cv _ _ hb1 hb2
    dsimp only [outL2]; unfold solPulseStepL2; simp only [solLitNat_eq, solSeqInt_eq,
      solSeqIv_eq, solWithIvList_eq, solWithIntList_eq, solCeilIsqrt_eq, solMinZ_eq,
      solMinNat_eq, solMaxNat_eq, ceilDivScaleP_eq, solNatAdd_eq, solNatDiv_eq,
      solIntAdd_eq, ofNat_mul_self_eq_sq]
    rw [hcv_b]; change (match solRecenterAndRadSq nxtIv with | (cNextRaw, radSqSum) => _) = _
    rw [hrec_eq, hrec]
  rw [houtL2_eq]; refine ⟨hcOut_spec.1, hcOut_spec.2.1, hcOut_spec.2.2.1, hin_next, htri, ?_⟩
  have h2 : outR.2.2 = surv + (1 - cum) := rfl; rw [h2, Int.cast_add, add_div]
  exact add_le_add hsurv hcum_step
theorem solEvolutionL2Aux_sound {L uvDen : ℕ} (hL : 2 ≤ L) (hden : 1 ≤ uvDen) {cs : Fin L → ℝ × ℝ}
  {trigIvs : List (IvInt × IvInt)} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (htrig : ∀ w
  : Fin L, memIvInt (cs w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt (cs w).2 (trigIvs.getD
  w.1 ((0, 0), (0, 0))).2) (sps : List SolSparsePulse) (hsps : sps.all solSparsePulseValid = true)
  {st : Fin (2 * L) → ℝ} {cum surv : ℝ} {cPref : List ℤ} {hAct rho : ℕ} {survUb : ℤ} (hh1 : 1 ≤
  hAct) (hhL : hAct ≤ L) (hclen : cPref.length = 2 * hAct) (hin : swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧
  cum ≤ 1 ∧ 0 ≤ surv) (hball : swLNormSq (fun j ↦ st j - decodeCenterReal L cPref j) ≤ ((rho : ℝ) /
  (swScale : ℝ)) ^ 2) (hsurv : surv ≤ (survUb : ℝ) / (swScale : ℝ)) :
    let outR := swLEvolutionRealAux L hL cs st cum surv (solToSwLPulses L uvDen sps)
    let outL2 := solEvolutionL2Aux L uvDen trigIvs cPref hAct rho survUb sps
    outL2.1.length ≤ 2 * L ∧ (swLNormSq outR.1 + outR.2.1 = 1 ∧ 0 ≤ outR.2.1 ∧ outR.2.1 ≤ 1 ∧ 0 ≤
      outR.2.2) ∧ swLNormSq (fun j ↦ outR.1 j - decodeCenterReal L outL2.1 j) ≤ ((outL2.2.1 : ℝ) /
      (swScale : ℝ)) ^ 2 ∧ outR.2.2 ≤ (outL2.2.2 : ℝ) / (swScale : ℝ) := by
  induction sps generalizing st cum surv cPref hAct rho survUb with
  | nil =>
    dsimp only [solToSwLPulses, List.map_nil, swLEvolutionRealAux, solEvolutionL2Aux]
    exact ⟨by omega, hin, hball, hsurv⟩
  | cons sp rest ih =>
    rw [List.all_cons, Bool.and_eq_true] at hsps; dsimp only [solToSwLPulses, List.map_cons,
      swLEvolutionRealAux, solEvolutionL2Aux]
    rcases hstep : solPulseStepL2 L uvDen trigIvs cPref hAct rho survUb sp with ⟨cNext, hAct', rho',
      survUb'⟩; dsimp only
    have hsnd := solPulseStepL2_sound hL hden hcs htrig hsps.1 hh1 hhL hclen hin hball hsurv
    dsimp only at hsnd; rw [hstep] at hsnd; simp only [solWithIntList_eq, solLitNat_eq,
      solSeqInt_eq]
    exact ih hsps.2 hsnd.1 hsnd.2.1 hsnd.2.2.1 hsnd.2.2.2.1 hsnd.2.2.2.2.1 hsnd.2.2.2.2.2
theorem swLOrbitProj_sub_normSq {L : ℕ} {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM : IsValidSwLOverlap
  M) (u v : Fin (2 * L) → ℝ) : swLNormSq (fun o ↦ swLOrbitProj M u o - swLOrbitProj M v o) =
  swLNormSq (fun j ↦ u j - v j) := by
  have hlin : (fun o ↦ swLOrbitProj M u o - swLOrbitProj M v o) = swLOrbitProj M (fun j ↦ u j - v j)
    := by
    ext o; unfold swLOrbitProj; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hlin]; unfold swLNormSq; exact isValidSwLOverlap_parseval hM (fun j ↦ u j - v j)
/-- Build descending suffix squared-magnitude list `[sufSq_0,..., sufSq_{L-1}]` in `O(L)`. -/
def solSuffixSqWalk (cPref : List ℤ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, accList => accList
  | m + 1, sqAcc, accList =>
      let c := m + 1
      let v1 := (cPref.getD (Nat.sub (Nat.mul 2 c) 1) 0).natAbs
      let v2 := (cPref.getD (Nat.mul 2 c) 0).natAbs
      solLitNat (Nat.add sqAcc (Nat.add (Nat.mul v1 v1) (Nat.mul v2 v2))) fun sqNext ↦
        solSuffixSqWalk cPref m sqNext (sqNext :: accList)
/-- Full `L`-element suffix squared-magnitude list for `cPref`. -/
def solSuffixSqList (L : ℕ) (cPref : List ℤ) : List ℕ :=
  let vTop := (cPref.getD (Nat.sub (Nat.mul 2 L) 1) 0).natAbs
  solLitNat (Nat.mul vTop vTop) fun sqTop ↦
    solSuffixSqWalk cPref (Nat.sub L 1) sqTop [sqTop]
/-- Map `sufSqs: List ℕ` into `tailLbs: List ℤ` at `radTot` and `cumPad`. -/
def solTailLbsFromSufSqs (radTot cumPad : ℤ) : List ℕ → List ℤ
  | [] => []
  | sq :: sqs =>
      let rt := solFloorIsqrt sq
      let ampLb := solMaxZ 0 (Int.sub (Int.ofNat rt) radTot)
      let tLb := solMinZ swScale (Int.add (Int.ediv (Int.mul ampLb ampLb) swScale) cumPad)
      solSeqInt tLb fun tLb' ↦
        let rest := solTailLbsFromSufSqs radTot cumPad sqs
        tLb' :: rest
/-- Extract `(p0Lb, tailLbs, survUb)` in `O(L)` from terminal `(cPref, rho, survUb)`. -/
def solTerminalBoundsL2 (L : ℕ) (cPref : List ℤ) (rho : ℕ) (survUb : ℤ) :
    ℤ × List ℤ × ℤ :=
  solLitNat (solSumSqAbs cPref 0) fun normSqK ↦
    solLitNat (solCeilIsqrt normSqK) fun normKUb ↦
      solSeqInt
        (Int.add (Int.ofNat rho) (ceilDivScaleP (Int.mul 65 (Int.ofNat normKUb))))
        fun radTot ↦
          solLitNat (Nat.add normKUb rho) fun sumRK ↦
            solSeqInt
              (solMinZ swScale (ceilDivScaleP (Int.ofNat (Nat.mul sumRK sumRK))))
              fun oneMinusCumUb ↦
                solSeqInt (solMaxZ 0 (Int.sub swScale oneMinusCumUb)) fun cumLo ↦
                  solSeqInt (solMaxZ 0 (Int.sub cumLo 1)) fun cumPad ↦
                    let c0Abs := Int.ofNat (cPref.getD 0 0).natAbs
                    let p0Amp := solMaxZ 0 (Int.sub c0Abs radTot)
                    solSeqInt (Int.ediv (Int.mul p0Amp p0Amp) swScale) fun p0Lb ↦
                      let sufSqs := solSuffixSqList L cPref
                      let tailLbs := solTailLbsFromSufSqs radTot cumPad sufSqs
                      (p0Lb, tailLbs, survUb)
theorem solSuffixSqWalk_getD_add (cPref : List ℤ) : ∀ (m sqAcc : ℕ) (accList : List ℕ) (k : ℕ),
  (solSuffixSqWalk cPref m sqAcc accList).getD (m + k) 0 = accList.getD k 0
  | 0, _, accList, k => by simp [solSuffixSqWalk]
  | m + 1, sqAcc, accList, k => by
    unfold solSuffixSqWalk
    rw [solLitNat_eq, show m + 1 + k = m + (k + 1) by omega,
      solSuffixSqWalk_getD_add cPref m _ _ (k + 1)]; rfl
theorem solSuffixSqWalk_spec (cPref : List ℤ) : ∀ (m : ℕ) (sqAcc : ℕ) (accList : List ℕ),
  (solSuffixSqWalk cPref m sqAcc accList).length = m + accList.length ∧ ∀ idx < m, (solSuffixSqWalk
  cPref m sqAcc accList).getD idx 0 = sqAcc + ∑ k ∈ Finset.Icc (idx + 1) m, ((cPref.getD (2 * k - 1)
  0).natAbs ^ 2 + (cPref.getD (2 * k) 0).natAbs ^ 2)
  | 0, _, accList => ⟨by simp [solSuffixSqWalk], fun _ h ↦ by omega⟩
  | m + 1, sqAcc, accList => by
    unfold solSuffixSqWalk; simp only [solLitNat_eq, solNatAdd_eq, solNatSub_eq, solNatMul_eq]
    set stTerm := (cPref.getD (2 * (m + 1) - 1) 0).natAbs * (cPref.getD (2 * (m + 1) - 1) 0).natAbs
      + (cPref.getD (2 * (m + 1)) 0).natAbs * (cPref.getD (2 * (m + 1)) 0).natAbs
    rcases solSuffixSqWalk_spec cPref m (sqAcc + stTerm) ((sqAcc + stTerm) :: accList) with ⟨hlen,
      hget⟩; refine ⟨by rw [List.length_cons] at hlen; omega, fun idx hidx ↦ ?_⟩
    by_cases hlt : idx < m
    · rw [hget idx hlt]; have hsplit : ∑ k ∈ Finset.Icc (idx + 1) (m + 1), ((cPref.getD (2 * k - 1)
        0).natAbs ^ 2 + (cPref.getD (2 * k) 0).natAbs ^ 2) = (∑ k ∈ Finset.Icc (idx + 1) m,
        ((cPref.getD (2 * k - 1) 0).natAbs ^ 2 + (cPref.getD (2 * k) 0).natAbs ^ 2)) + stTerm :=
        (by rw [Finset.sum_Icc_succ_top (by omega : idx + 1 ≤ m + 1)]; dsimp [stTerm]; simp [sq])
      omega
    · have heq : idx = m := (by omega); rw [heq]; have h0 := solSuffixSqWalk_getD_add cPref m (sqAcc
        + stTerm) ((sqAcc + stTerm) :: accList) 0; rw [Nat.add_zero] at h0; rw [h0,
        List.getD_cons_zero, Finset.Icc_self, Finset.sum_singleton]; dsimp [stTerm]; simp [sq]
theorem solSuffixSqList_spec {L : ℕ} (hL : 2 ≤ L) (cPref : List ℤ) : (solSuffixSqList L
  cPref).length = L ∧ ∀ idx < L, ((solSuffixSqList L cPref).getD idx 0 : ℝ) / (swScale : ℝ) ^ 2 = ∑
  o : Fin (2 * L), (if 2 * idx + 1 ≤ o.1 then decodeCenterReal L cPref o else 0) ^ 2 := by
  unfold solSuffixSqList; simp only [solLitNat_eq, solNatSub_eq, solNatMul_eq]; set vTop :=
    (cPref.getD (2 * L - 1) 0).natAbs; set sqTop := vTop * vTop
  rcases solSuffixSqWalk_spec cPref (L - 1) sqTop [sqTop] with ⟨hlen, hget⟩
  have hlenL : (solSuffixSqWalk cPref (L - 1) sqTop [sqTop]).length = L :=
    (by rw [List.length_singleton] at hlen; omega); refine ⟨hlenL, fun idx hidx ↦ ?_⟩
  set g : ℕ → ℕ := fun i ↦ (cPref.getD i 0).natAbs ^ 2; have hnat_ico : ∀ d < L,
      let j := L - 1 - d
      (solSuffixSqWalk cPref (L - 1) sqTop [sqTop]).getD j 0 =
        ∑ i ∈ Finset.Ico (2 * j + 1) (2 * L), g i := by
    intro d hd
    induction d with
    | zero =>
        dsimp only; rw [Nat.sub_zero]
        have h0 := solSuffixSqWalk_getD_add cPref (L - 1) sqTop [sqTop] 0; rw [Nat.add_zero] at h0
        have hi : 2 * (L - 1) + 1 = 2 * L - 1 := (by omega); have hico : Finset.Ico (2 * L - 1) (2 *
          L) = {2 * L - 1} := (by ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega)
        rw [h0, List.getD_cons_zero, hi, hico, Finset.sum_singleton]; dsimp [sqTop, vTop, g]; ring
    | succ d' ih =>
        dsimp only; set j := L - 1 - (d' + 1); have hj_lt : j < L - 1 := (by omega)
        have hj_succ : L - 1 - d' = j + 1 := (by omega); have hprev := ih (by omega)
        dsimp only at hprev; rw [hj_succ] at hprev; have hcur := hget j hj_lt
        have hprev_eq : (solSuffixSqWalk cPref (L - 1) sqTop [sqTop]).getD (j + 1) 0 = sqTop + ∑ k ∈
          Finset.Icc (j + 2) (L - 1), ((cPref.getD (2 * k - 1) 0).natAbs ^ 2 + (cPref.getD (2 * k)
          0).natAbs ^ 2) := by
          by_cases hlt1 : j + 1 < L - 1
          · exact hget (j + 1) hlt1
          · have heq1 : j + 1 = L - 1 := (by omega); have heq2 : j + 2 = L - 1 + 1 := (by omega)
            rw [heq1, heq2]; have h0 := solSuffixSqWalk_getD_add cPref (L - 1) sqTop [sqTop] 0
            rw [Nat.add_zero] at h0; rw [h0, List.getD_cons_zero, Finset.Icc_eq_empty_of_lt
              (by omega : L - 1 < L - 1 + 1), Finset.sum_empty, add_zero]
        have hstep_icc : ∑ k ∈ Finset.Icc (j + 1) (L - 1), ((cPref.getD (2 * k - 1) 0).natAbs ^ 2 +
          (cPref.getD (2 * k) 0).natAbs ^ 2) = (g (2 * j + 1) + g (2 * j + 2)) + ∑ k ∈ Finset.Icc (j
          + 2) (L - 1), ((cPref.getD (2 * k - 1) 0).natAbs ^ 2 + (cPref.getD (2 * k) 0).natAbs ^ 2)
          := by
          rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot
            (by omega : j + 1 < L - 1 + 1), Finset.Ico_add_one_right_eq_Icc]; dsimp [g]; rw [show 2
            * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by omega]
        have hstep_ico : ∑ i ∈ Finset.Ico (2 * j + 1) (2 * L), g i = g (2 * j + 1) + (g (2 * j + 2)
          + ∑ i ∈ Finset.Ico (2 * (j + 1) + 1) (2 * L), g i) := by
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 * j + 1 < 2 * L),
            Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 * j + 1 + 1 < 2 * L)]
          rw [show 2 * j + 1 + 1 + 1 = 2 * (j + 1) + 1 by omega,
            show 2 * j + 1 + 1 = 2 * j + 2 by omega]
        omega
  have hd_eq : L - 1 - (L - 1 - idx) = idx := (by omega)
  have hval := hnat_ico (L - 1 - idx) (by omega); dsimp only at hval; rw [hd_eq] at hval
  unfold decodeCenterReal; rw [hval, Nat.cast_sum, sum_div_const, Fin.sum_univ_eq_sum_range (fun i ↦
    (if 2 * idx + 1 ≤ i then (cPref.getD i 0 : ℝ) / (swScale : ℝ) else 0) ^ 2) (2 * L)]
  have hsub : Finset.Ico (2 * idx + 1) (2 * L) ⊆ Finset.range (2 * L) := fun i hi ↦ by
    rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; exact hi.2
  refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans (Finset.sum_subset hsub fun i hi_r hi_not ↦ ?_)
  · have hi' := Finset.mem_Ico.1 hi
    have hz_sq : (g i : ℝ) = (cPref.getD i 0 : ℝ) ^ 2 := by
      dsimp [g]; rw [Nat.cast_pow]; rcases cPref.getD i 0 with n | n
      · simp
      · simp [Int.negSucc_eq]
    rw [ite_eq_left hi'.1, div_pow, hz_sq]
  · rw [Finset.mem_range] at hi_r
    have hnle : ¬(2 * idx + 1 ≤ i) := fun hle ↦ hi_not (Finset.mem_Ico.2 ⟨hle, hi_r⟩); simp [hnle]
theorem solTailLbsFromSufSqs_spec (radTot cumPad : ℤ) : ∀ (sqs : List ℕ), (solTailLbsFromSufSqs
  radTot cumPad sqs).length = sqs.length ∧ ∀ idx < sqs.length, (solTailLbsFromSufSqs radTot cumPad
  sqs).getD idx 0 = min swScale ((max 0 ((Nat.sqrt (sqs.getD idx 0) : ℤ) - radTot)) ^ 2 / swScale +
  cumPad)
  | [] => ⟨rfl, fun _ h ↦ by simp at h⟩
  | sq0 :: sqs => by
    rcases solTailLbsFromSufSqs_spec radTot cumPad sqs with ⟨hlen, hget⟩
    unfold solTailLbsFromSufSqs; simp only [solSeqInt_eq, solFloorIsqrt_eq, solMaxZ_eq, solMinZ_eq,
      Int.ofNat_eq_natCast, solIntSub_eq, solIntAdd_eq, solIntEdiv_eq, solIntMul_eq,
      List.length_cons]; refine ⟨by omega, fun idx hidx ↦ ?_⟩
    cases idx with
    | zero => simp only [List.getD_cons_zero, ← sq]
    | succ i => simp only [List.getD_cons_succ]; exact hget i (by omega)
theorem swLAttemptProbReal_tail_eq {L : ℕ} (hL : 2 ≤ L)
    (M : Fin (2 * L) → Fin (2 * L) → ℝ) (st : Fin (2 * L) → ℝ) (cum : ℝ) :
    ∀ idx < L,
      ∑ h ∈ Finset.Icc (idx + 1) L, swLAttemptProbReal L hL M st cum h =
        (∑ o : Fin (2 * L), (if 2 * idx + 1 ≤ o.1 then swLOrbitProj M st o else 0) ^ 2) +
          cum * ∑ o : Fin (2 * L),
            if 2 * idx + 1 ≤ o.1 then (M o ⟨2 * L - 1, by omega⟩) ^ 2 else 0 := by
  set q1 : ℕ → ℝ := fun i ↦ if hi : i < 2 * L then (swLOrbitProj M st ⟨i, hi⟩) ^ 2 else 0
  set q2 : ℕ → ℝ := fun i ↦ if hi : i < 2 * L then (M ⟨i, hi⟩ ⟨2 * L - 1, by omega⟩) ^ 2 else 0
  have hico : ∀ d < L,
      let idx := L - 1 - d
      ∑ h ∈ Finset.Icc (idx + 1) L, swLAttemptProbReal L hL M st cum h =
        (∑ i ∈ Finset.Ico (2 * idx + 1) (2 * L), q1 i) +
          cum * ∑ i ∈ Finset.Ico (2 * idx + 1) (2 * L), q2 i := by
    intro d hd
    induction d with
    | zero =>
        dsimp only; rw [Nat.sub_zero, show L - 1 + 1 = L
          by omega, Finset.Icc_self, Finset.sum_singleton]
        have hico_top : Finset.Ico (2 * (L - 1) + 1) (2 * L) = {2 * L - 1} :=
          (by ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega); rw [hico_top,
          Finset.sum_singleton, Finset.sum_singleton]; unfold swLAttemptProbReal
        have hn0 : L ≠ 0 := (by omega); have hlt : 2 * L - 1 < 2 * L := (by omega); simp [hn0, q1,
          q2, hlt]
    | succ d' ih =>
        dsimp only; set idx := L - 1 - (d' + 1); have hidx_lt : idx + 1 < L := (by omega)
        have hidx_succ : L - 1 - d' = idx + 1 := (by omega); have hprev := ih (by omega)
        dsimp only at hprev; rw [hidx_succ] at hprev; rw [← Finset.Ico_add_one_right_eq_Icc,
          Finset.sum_eq_sum_Ico_succ_bot (by omega : idx + 1 < L + 1),
          Finset.Ico_add_one_right_eq_Icc, hprev]
        have hp_cur : swLAttemptProbReal L hL M st cum (idx + 1) = (q1 (2 * idx + 1) + q1 (2 * idx +
          2)) + cum * (q2 (2 * idx + 1) + q2 (2 * idx + 2)) := by
          unfold swLAttemptProbReal; have hn0 : idx + 1 ≠ 0 := (by omega)
          have h1 : 2 * idx + 1 < 2 * L := (by omega); have h2 : 2 * idx + 2 < 2 * L := (by omega)
          have hf1 : (⟨2 * (idx + 1) - 1, by omega⟩ : Fin (2 * L)) = ⟨2 * idx + 1, h1⟩ :=
            (by ext; dsimp; omega); have hf2 : (⟨2 * (idx + 1), by omega⟩ : Fin (2 * L)) = ⟨2 * idx
            + 2, h2⟩ := (by ext; dsimp; omega); simp only [hn0, ↓reduceIte, hidx_lt, ↓reduceDIte,
            hf1, hf2, q1, q2, h1, h2]
        have hs1 : ∑ i ∈ Finset.Ico (2 * idx + 1) (2 * L), q1 i = q1 (2 * idx + 1) + (q1 (2 * idx +
          2) + ∑ i ∈ Finset.Ico (2 * (idx + 1) + 1) (2 * L), q1 i) := by
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 * idx + 1 < 2 * L),
            Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 * idx + 1 + 1 < 2 * L),
            show 2 * idx + 1 + 1 + 1 = 2 * (idx + 1) + 1 by omega,
            show 2 * idx + 1 + 1 = 2 * idx + 2 by omega]
        have hs2 : ∑ i ∈ Finset.Ico (2 * idx + 1) (2 * L), q2 i = q2 (2 * idx + 1) + (q2 (2 * idx +
          2) + ∑ i ∈ Finset.Ico (2 * (idx + 1) + 1) (2 * L), q2 i) := by
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 * idx + 1 < 2 * L),
            Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 * idx + 1 + 1 < 2 * L),
            show 2 * idx + 1 + 1 + 1 = 2 * (idx + 1) + 1 by omega,
            show 2 * idx + 1 + 1 = 2 * idx + 2 by omega]
        rw [hp_cur, hs1, hs2]; ring
  intro idx hidx; have hd_eq : L - 1 - (L - 1 - idx) = idx := (by omega); have h := hico (L - 1 -
    idx) (by omega); dsimp only at h; rw [hd_eq] at h; rw [h]
  have hsub : Finset.Ico (2 * idx + 1) (2 * L) ⊆ Finset.range (2 * L) := fun i hi ↦ by
    rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; exact hi.2
  have h1 : ∑ i ∈ Finset.Ico (2 * idx + 1) (2 * L), q1 i = ∑ o : Fin (2 * L), (if 2 * idx + 1 ≤ o.1
    then swLOrbitProj M st o else 0) ^ 2 := by
    have hrhs : (∑ o : Fin (2 * L), (if 2 * idx + 1 ≤ o.1 then swLOrbitProj M st o else 0) ^ 2) = ∑
      o : Fin (2 * L), (if 2 * idx + 1 ≤ o.1 then q1 o.1 else 0) := by
      refine Finset.sum_congr rfl fun o _ ↦ ?_; by_cases hle : 2 * idx + 1 ≤ o.1
      · rw [ite_eq_left hle, ite_eq_left hle]; dsimp only [q1]; rw [dite_eq_left o.2]
      · rw [ite_eq_right hle, ite_eq_right hle]; norm_num
    rw [hrhs, Fin.sum_univ_eq_sum_range (fun i ↦ if 2 * idx + 1 ≤ i then q1 i else 0) (2 * L)]
    refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans (Finset.sum_subset hsub fun i hi_r hi_not ↦
      ?_)
    · simp [(Finset.mem_Ico.1 hi).1]
    · rw [Finset.mem_range] at hi_r
      have hnle : ¬(2 * idx + 1 ≤ i) := fun hle ↦ hi_not (Finset.mem_Ico.2 ⟨hle, hi_r⟩); simp [hnle]
  have h2 : ∑ i ∈ Finset.Ico (2 * idx + 1) (2 * L), q2 i = ∑ o : Fin (2 * L), if 2 * idx + 1 ≤ o.1
    then (M o ⟨2 * L - 1, by omega⟩) ^ 2 else 0 := by
    have hrhs : (∑ o : Fin (2 * L), if 2 * idx + 1 ≤ o.1 then (M o ⟨2 * L - 1, by omega⟩) ^ 2 else
      0) = ∑ o : Fin (2 * L), (if 2 * idx + 1 ≤ o.1 then q2 o.1 else 0) := by
      refine Finset.sum_congr rfl fun o _ ↦ ?_; by_cases hle : 2 * idx + 1 ≤ o.1
      · rw [ite_eq_left hle, ite_eq_left hle]; dsimp only [q2]; rw [dite_eq_left o.2]
      · rw [ite_eq_right hle, ite_eq_right hle]
    rw [hrhs, Fin.sum_univ_eq_sum_range (fun i ↦ if 2 * idx + 1 ≤ i then q2 i else 0) (2 * L)]
    refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans (Finset.sum_subset hsub fun i hi_r hi_not ↦
      ?_)
    · simp [(Finset.mem_Ico.1 hi).1]
    · rw [Finset.mem_range] at hi_r
      have hnle : ¬(2 * idx + 1 ≤ i) := fun hle ↦ hi_not (Finset.mem_Ico.2 ⟨hle, hi_r⟩); simp [hnle]
  rw [h1, h2]
theorem ediv_swScale_le_div (a : ℤ) : ((a / swScale : ℤ) : ℝ) ≤ (a : ℝ) / (swScale : ℝ) :=
  ediv_pos_le_real a swScale (by unfold swScale; norm_num)
theorem solTerminalBoundsL2_sound {L : ℕ} (hL : 2 ≤ L) (hL1024 : L ≤ 1024) {st : Fin (2 * L) → ℝ}
  {cum surv : ℝ} {cPref : List ℤ} {rho : ℕ} {survUb : ℤ} (hclen : cPref.length ≤ 2 * L) (hin :
  swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧ cum ≤ 1 ∧ 0 ≤ surv) (hball : swLNormSq (fun j ↦ st j -
  decodeCenterReal L cPref j) ≤ ((rho : ℝ) / (swScale : ℝ)) ^ 2) (_hsurv : surv ≤ (survUb : ℝ) /
  (swScale : ℝ)) {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM : IsValidSwLOverlap M) :
    let tb := solTerminalBoundsL2 L cPref rho survUb; let p := swLAttemptProbReal L hL M st cum
    tb.2.2 = survUb ∧ 0 ≤ tb.1 ∧ ((tb.1 : ℝ) / (swScale : ℝ)) ≤ p 0 ∧ tb.2.1.length = L ∧ ∀ c ∈
      Finset.Icc 1 L, ((tb.2.1.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈ Finset.Icc c L, p h
      := by
  intro tb p; have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; norm_num); have hS : (0 : ℝ) <
    (swScale : ℝ) := (by unfold swScale; norm_num)
  set cR := decodeCenterReal L cPref; set normKUb : ℕ := ceilIsqrtNat (solSumSqAbs cPref 0)
  set ovPad : ℤ := -((-(65 * (normKUb : ℤ))) / swScale); set radTot : ℤ := (rho : ℤ) + ovPad
  set oneMinusCumUb : ℤ := min swScale (-((-(((normKUb + rho : ℕ) : ℤ) ^ 2)) / swScale))
  set cumLo : ℤ := max 0 (swScale - oneMinusCumUb); set cumPad : ℤ := max 0 (cumLo - 1)
  set c0Abs : ℤ := ((cPref.getD 0 0).natAbs : ℤ); set p0Amp : ℤ := max 0 (c0Abs - radTot)
  set p0Lb : ℤ := (p0Amp * p0Amp) / swScale; set sufSqs := solSuffixSqList L cPref; set tailLbs :=
    solTailLbsFromSufSqs radTot cumPad sufSqs
  have htb_eq : tb = (p0Lb, tailLbs, survUb) := by
    dsimp only [tb]; unfold solTerminalBoundsL2; simp only [solLitNat_eq, solSeqInt_eq,
      solCeilIsqrt_eq, solMinZ_eq, solMaxZ_eq, ceilDivScaleP_eq, ofNat_mul_self_eq_sq]; rfl
  rw [htb_eq]
  -- Norm bound on `cR` and total orbit-projection error `swLOrbitProj M st - cR`
  have hc_norm : swLNormSq cR ≤ ((normKUb : ℝ) / (swScale : ℝ)) ^ 2 := by
    rw [swLCenter_normSq_le_len hclen, div_pow]; exact div_le_div_of_nonneg_right
      (by exact_mod_cast le_ceilIsqrtNat_sq (solSumSqAbs cPref 0)) (sq_nonneg _)
  have hovPad_nn : 0 ≤ ovPad := (by dsimp [ovPad]; unfold swScale; omega); have hradTot_nn : 0 ≤
    radTot := (by dsimp [radTot]; positivity)
  have hov_err : swLNormSq (fun o ↦ swLOrbitProj M cR o - cR o) ≤ ((ovPad : ℝ) / (swScale : ℝ)) ^ 2
    := by
    have h64 := swLOrbitProj_sub_id_normSq_le hL1024 hM cR
    have h64_le : ((64 : ℝ) / (swScale : ℝ)) ^ 2 * swLNormSq cR ≤ (((65 * (normKUb : ℤ) : ℤ) : ℝ) /
      (swScale : ℝ) ^ 2) ^ 2 := by
      have h1 : ((64 : ℝ) / (swScale : ℝ)) ^ 2 * swLNormSq cR ≤ ((64 : ℝ) / (swScale : ℝ)) ^ 2 *
        ((normKUb : ℝ) / (swScale : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hc_norm (sq_nonneg _)
      have h2 : ((64 : ℝ) / (swScale : ℝ)) ^ 2 * ((normKUb : ℝ) / (swScale : ℝ)) ^ 2 ≤ (((65 *
        (normKUb : ℤ) : ℤ) : ℝ) / (swScale : ℝ) ^ 2) ^ 2 := by
        push_cast; have hbase : (64 : ℝ) / (swScale : ℝ) * ((normKUb : ℝ) / (swScale : ℝ)) ≤
            (65 * (normKUb : ℝ)) / (swScale : ℝ) ^ 2 := by
          rw [div_mul_div_comm, ← sq]; exact div_le_div_of_nonneg_right
            (by linarith [Nat.cast_nonneg (α := ℝ) normKUb]) (sq_nonneg _)
        rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg (div_nonneg (by norm_num) hS.le)
          (div_nonneg (Nat.cast_nonneg _) hS.le)) hbase 2
      exact h1.trans h2
    have hceil := real_le_neg_ediv_neg_pos (65 * (normKUb : ℤ)) swScale hS_pos
    have hceil_div : ((65 * (normKUb : ℤ) : ℤ) : ℝ) / (swScale : ℝ) ^ 2 ≤ (ovPad : ℝ) / (swScale :
      ℝ) := (by rw [sq (swScale : ℝ), ← div_div]; exact div_le_div_of_nonneg_right hceil hS.le)
    refine (h64.trans h64_le).trans ?_; exact pow_le_pow_left₀ (by positivity) hceil_div 2
  have hproj_ball : swLNormSq (fun o ↦ swLOrbitProj M st o - cR o) ≤ ((radTot : ℝ) / (swScale : ℝ))
    ^ 2 := by
    have hiso : swLNormSq (fun o ↦ swLOrbitProj M st o - swLOrbitProj M cR o) ≤ ((rho : ℝ) /
      (swScale : ℝ)) ^ 2 := (by rw [swLOrbitProj_sub_normSq hM]; exact hball)
    have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg rho) hS.le) (div_nonneg
      (by exact_mod_cast hovPad_nn) hS.le) hiso hov_err; have hv : (fun o ↦ swLOrbitProj M st o - cR
      o) = (fun o ↦ (swLOrbitProj M st o - swLOrbitProj M cR o) + (swLOrbitProj M cR o - cR o)) :=
      (by ext o; ring); have hr : (rho : ℝ) / (swScale : ℝ) + (ovPad : ℝ) / (swScale : ℝ) = (radTot
      : ℝ) / (swScale : ℝ) := (by dsimp [radTot]; push_cast; ring)
    rwa [← hv, hr] at htri
  -- Lower bound on `cum` and `cumPad`
  have hcum_lb : (cumLo : ℝ) / (swScale : ℝ) ≤ cum := by
    have hst_norm : swLNormSq st ≤ (((normKUb + rho : ℕ) : ℝ) / (swScale : ℝ)) ^ 2 := by
      have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg normKUb) hS.le) (div_nonneg
        (Nat.cast_nonneg rho) hS.le) hc_norm hball; have hv : st = fun j ↦ cR j + (st j - cR j) :=
        (by ext j; ring); have hr : (normKUb : ℝ) / (swScale : ℝ) + (rho : ℝ) / (swScale : ℝ) =
        ((normKUb + rho : ℕ) : ℝ) / (swScale : ℝ) := (by push_cast; ring)
      rwa [← hv, hr] at htri
    set q : ℤ := ((normKUb + rho : ℕ) : ℤ) ^ 2; set ceilZ : ℤ := -((-q) / swScale)
    have hceil_ub : (((normKUb + rho : ℕ) : ℝ) / (swScale : ℝ)) ^ 2 ≤ (ceilZ : ℝ) / (swScale : ℝ)
      := by
      rw [div_pow, sq (swScale : ℝ), ← div_div]; refine div_le_div_of_nonneg_right ?_ hS.le
      have hd := real_le_neg_ediv_neg_pos q swScale hS_pos
      have hq : (((normKUb + rho : ℕ) : ℝ)) ^ 2 = (q : ℝ) := (by dsimp [q]; push_cast; rfl)
      rwa [hq]
    have h1mc : 1 - cum ≤ (oneMinusCumUb : ℝ) / (swScale : ℝ) := by
      have heq1 : 1 - cum = swLNormSq st := (by linarith [hin.1]); rw [heq1, show oneMinusCumUb =
        min swScale ceilZ from rfl, Int.cast_min]
      rcases le_total (swScale : ℝ) (ceilZ : ℝ) with h | h
      · rw [min_eq_left h, div_self hS.ne']; linarith [hin.1, hin.2.1]
      · rw [min_eq_right h]; exact hst_norm.trans hceil_ub
    dsimp [cumLo]; rw [Int.cast_max, Int.cast_zero, Int.cast_sub]; rcases le_total (0 : ℝ) ((swScale
      : ℝ) - (oneMinusCumUb : ℝ)) with h | h
    · rw [max_eq_right h, sub_div, div_self hS.ne']; linarith
    · rw [max_eq_left h, zero_div]; exact hin.2.1
  have hcumPad_lb : (cumPad : ℝ) / (swScale : ℝ) ≤ cum * (M ⟨2 * L - 1, by omega⟩ ⟨2 * L - 1,
    by omega⟩) ^ 2 := by
    rcases hM.2.2.1 ⟨2 * L - 1, by omega⟩ with ⟨_, _, hd_sq⟩; have hprod_nn : 0 ≤ cum * (M ⟨2 * L -
      1, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 := mul_nonneg hin.2.1 (sq_nonneg _); have h1 : cum *
      (1 - (1 : ℝ) / 10 ^ 18) ≤ cum * (M ⟨2 * L - 1, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 :=
      mul_le_mul_of_nonneg_left hd_sq hin.2.1
    have h2 : (cumLo : ℝ) / (swScale : ℝ) - (1 : ℝ) / (swScale : ℝ) ≤ cum * (1 - (1 : ℝ) / 10 ^ 18)
      := by
      have h18 : cum * ((1 : ℝ) / 10 ^ 18) ≤ (1 : ℝ) / (swScale : ℝ) := by
        have hc1 : cum * ((1 : ℝ) / 10 ^ 18) ≤ 1 * ((1 : ℝ) / 10 ^ 18) := mul_le_mul_of_nonneg_right
          hin.2.2.1 (by norm_num); have hs1 : (1 : ℝ) * ((1 : ℝ) / 10 ^ 18) ≤ (1 : ℝ) / (swScale :
          ℝ) := (by unfold swScale; norm_num); exact hc1.trans hs1
      linarith [hcum_lb, h18]
    dsimp [cumPad]; rw [Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one]; rcases le_total (0
      : ℝ) ((cumLo : ℝ) - 1) with h | h
    · rw [max_eq_right h, sub_div]; linarith
    · rw [max_eq_left h, zero_div]; exact hprod_nn
  -- Lower bound on `p 0`
  have hp0Lb_nn : 0 ≤ p0Lb := by dsimp [p0Lb]; have := mul_self_nonneg p0Amp; unfold swScale; omega
  have hp0_bound : (p0Lb : ℝ) / (swScale : ℝ) ≤ p 0 := by
    have hcoord0 : (swLOrbitProj M st ⟨0, by omega⟩ - cR ⟨0, by omega⟩) ^ 2 ≤ ((radTot : ℝ) /
      (swScale : ℝ)) ^ 2 := by
      refine (Finset.single_le_sum (fun o _ ↦ sq_nonneg (swLOrbitProj M st o - cR o))
        (Finset.mem_univ ⟨0, by omega⟩)).trans hproj_ball
    have habs_diff : |swLOrbitProj M st ⟨0, by omega⟩ - cR ⟨0, by omega⟩| ≤
        (radTot : ℝ) / (swScale : ℝ) := by
      have h := sq_le_sq.1 hcoord0
      rwa [abs_of_nonneg (div_nonneg (by exact_mod_cast hradTot_nn) hS.le)] at h
    have hc0_abs : |cR ⟨0, by omega⟩| = (c0Abs : ℝ) / (swScale : ℝ) := by
      dsimp [cR, decodeCenterReal, c0Abs]; rw [abs_div, abs_of_pos hS]; congr 1
      exact_mod_cast Int.abs_eq_natAbs (cPref.getD 0 0)
    have htri0 : |cR ⟨0, by omega⟩| - |swLOrbitProj M st ⟨0, by omega⟩| ≤
        |swLOrbitProj M st ⟨0, by omega⟩ - cR ⟨0, by omega⟩| := by
      have h := abs_sub_abs_le_abs_sub (cR ⟨0, by omega⟩) (swLOrbitProj M st ⟨0, by omega⟩)
      rwa [abs_sub_comm] at h
    have hamp_le : (p0Amp : ℝ) / (swScale : ℝ) ≤ |swLOrbitProj M st ⟨0, by omega⟩| := by
      dsimp [p0Amp]; rw [Int.cast_max, Int.cast_zero, Int.cast_sub]; rcases le_total (0 : ℝ) ((c0Abs
        : ℝ) - (radTot : ℝ)) with h | h
      · rw [max_eq_right h, sub_div, ← hc0_abs]; linarith
      · rw [max_eq_left h, zero_div]; exact abs_nonneg _
    have hamp_nn : 0 ≤ (p0Amp : ℝ) / (swScale : ℝ) := div_nonneg (by dsimp [p0Amp]; positivity)
      hS.le
    have hsq0 : ((p0Amp : ℝ) / (swScale : ℝ)) ^ 2 ≤ (swLOrbitProj M st ⟨0, by omega⟩) ^ 2 :=
      (by have h := pow_le_pow_left₀ hamp_nn hamp_le 2; rwa [sq_abs] at h)
    have hediv0 : (p0Lb : ℝ) / (swScale : ℝ) ≤ ((p0Amp : ℝ) / (swScale : ℝ)) ^ 2 := by
      dsimp [p0Lb]; rw [div_pow, sq (swScale : ℝ), ← div_div]
      refine div_le_div_of_nonneg_right ?_ hS.le; have hd := ediv_swScale_le_div (p0Amp * p0Amp);
        simpa [sq] using hd
    have hp0_def : (swLOrbitProj M st ⟨0, by omega⟩) ^ 2 ≤ p 0 := by
      dsimp [p]; unfold swLAttemptProbReal; simp only [↓reduceIte]; linarith [mul_nonneg hin.2.1
        (sq_nonneg (M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩))]
    exact (hediv0.trans hsq0).trans hp0_def
  -- Tail lower bounds via masked reverse triangle inequality
  rcases solSuffixSqList_spec hL cPref with ⟨hsuf_len, hsuf_eq⟩
  rcases solTailLbsFromSufSqs_spec radTot cumPad sufSqs with ⟨htl_len, htl_eq⟩
  have htl_lenL : tailLbs.length = L := htl_len.trans hsuf_len; refine ⟨rfl, hp0Lb_nn, hp0_bound,
    htl_lenL, fun c hc ↦ ?_⟩; rw [Finset.mem_Icc] at hc; set idx := c - 1; have hidx_lt : idx < L :=
    (by omega); have hc_eq : idx + 1 = c := (by omega); rw [← hc_eq, swLAttemptProbReal_tail_eq hL M
    st cum idx hidx_lt, htl_eq idx (by rw [hsuf_len]; exact hidx_lt)]
  set uMask : Fin (2 * L) → ℝ := fun o ↦ if 2 * idx + 1 ≤ o.1 then swLOrbitProj M st o else 0
  set cMask : Fin (2 * L) → ℝ := fun o ↦ if 2 * idx + 1 ≤ o.1 then cR o else 0
  have hdiff_mask : swLNormSq (fun o ↦ cMask o - uMask o) ≤ ((radTot : ℝ) / (swScale : ℝ)) ^ 2 := by
    refine (Finset.sum_le_sum fun o _ ↦ ?_).trans hproj_ball
    dsimp [cMask, uMask]; by_cases hle : 2 * idx + 1 ≤ o.1
    · rw [ite_eq_left hle, ite_eq_left hle]
      exact (by ring : (cR o - swLOrbitProj M st o) ^ 2 = (swLOrbitProj M st o - cR o) ^ 2).le
    · have h0 : ((0 : ℝ) - 0) ^ 2 = 0 := (by ring); rw [ite_eq_right hle, ite_eq_right hle, h0]
      exact sq_nonneg _
  set ru : ℝ := √(swLNormSq uMask)
  have hru_sq : ru ^ 2 = swLNormSq uMask := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hmask_tri : swLNormSq cMask ≤ (ru + (radTot : ℝ) / (swScale : ℝ)) ^ 2 := by
    have htri := swLNormSq_add_le_sq (Real.sqrt_nonneg _) (div_nonneg (by exact_mod_cast hradTot_nn)
      hS.le) hru_sq.symm.le hdiff_mask; have hv : cMask = fun o ↦ uMask o + (cMask o - uMask o) :=
      (by ext o; ring); rwa [← hv] at htri
  set rt : ℕ := Nat.sqrt (sufSqs.getD idx 0)
  have hrt_sq : ((rt : ℝ) / (swScale : ℝ)) ^ 2 ≤ swLNormSq cMask := by
    have hsuf_i := hsuf_eq idx hidx_lt; change ((sufSqs.getD idx 0 : ℝ) / (swScale : ℝ) ^ 2) =
      swLNormSq cMask at hsuf_i; rw [← hsuf_i, div_pow]; have hsq_le : (rt : ℝ) ^ 2 ≤ (sufSqs.getD
      idx 0 : ℝ) := (by rw [sq]; exact_mod_cast Nat.sqrt_le (sufSqs.getD idx 0))
    exact div_le_div_of_nonneg_right hsq_le (sq_nonneg _)
  have hrt_le : (rt : ℝ) / (swScale : ℝ) ≤ ru + (radTot : ℝ) / (swScale : ℝ) := by
    have h1 : 0 ≤ (rt : ℝ) / (swScale : ℝ) := div_nonneg (Nat.cast_nonneg rt) hS.le
    have h2 : 0 ≤ ru + (radTot : ℝ) / (swScale : ℝ) := add_nonneg (Real.sqrt_nonneg _) (div_nonneg
      (by exact_mod_cast hradTot_nn) hS.le)
    rw [← Real.sqrt_sq h1, ← Real.sqrt_sq h2]; exact Real.sqrt_le_sqrt (hrt_sq.trans hmask_tri)
  set ampLb : ℤ := max 0 ((rt : ℤ) - radTot)
  have hamp_le_ru : (ampLb : ℝ) / (swScale : ℝ) ≤ ru := by
    dsimp [ampLb]; rw [Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_natCast]
    rcases le_total (0 : ℝ) ((rt : ℝ) - (radTot : ℝ)) with h | h
    · rw [max_eq_right h, sub_div]; linarith
    · rw [max_eq_left h, zero_div]; exact Real.sqrt_nonneg _
  have hamp_sq : ((ampLb ^ 2 / swScale : ℤ) : ℝ) / (swScale : ℝ) ≤ swLNormSq uMask := by
    have h1 : ((ampLb ^ 2 / swScale : ℤ) : ℝ) / (swScale : ℝ) ≤ ((ampLb : ℝ) / (swScale : ℝ)) ^ 2
      := by
      rw [div_pow, sq (swScale : ℝ), ← div_div]; refine div_le_div_of_nonneg_right ?_ hS.le
      have hd := ediv_swScale_le_div (ampLb ^ 2); simpa using hd
    have h2 : ((ampLb : ℝ) / (swScale : ℝ)) ^ 2 ≤ ru ^ 2 := pow_le_pow_left₀ (div_nonneg
      (by dsimp [ampLb]; positivity) hS.le) hamp_le_ru 2; exact (h1.trans h2).trans_eq hru_sq
  let iTop : Fin (2 * L) := ⟨2 * L - 1, by omega⟩
  have hcum_tail : (cumPad : ℝ) / (swScale : ℝ) ≤ cum * ∑ o : Fin (2 * L), if 2 * idx + 1 ≤ o.1 then
    (M o iTop) ^ 2 else 0 := by
    have htop_le : 2 * idx + 1 ≤ iTop.1 := (by dsimp [iTop]; omega)
    have hsingle : (M iTop iTop) ^ 2 ≤ ∑ o : Fin (2 * L), if 2 * idx + 1 ≤ o.1 then (M o iTop) ^ 2
      else 0 := by
      have hf_nn : ∀ o ∈ (Finset.univ : Finset (Fin (2 * L))), (0 : ℝ) ≤ if 2 * idx + 1 ≤ o.1 then
        (M o iTop) ^ 2 else 0 := fun o _ ↦ by
        by_cases h : 2 * idx + 1 ≤ o.1
        · rw [ite_eq_left h]; exact sq_nonneg _
        · rw [ite_eq_right h]
      have h := Finset.single_le_sum hf_nn (Finset.mem_univ iTop); simpa [htop_le] using h
    exact hcumPad_lb.trans (mul_le_mul_of_nonneg_left hsingle hin.2.1)
  have hmin_le : ((min swScale (ampLb ^ 2 / swScale + cumPad) : ℤ) : ℝ) ≤ ((ampLb ^ 2 / swScale +
    cumPad : ℤ) : ℝ) := Int.cast_le.mpr (min_le_right _ _); refine (div_le_div_of_nonneg_right
    hmin_le hS.le).trans ?_; rw [Int.cast_add, add_div]; exact add_le_add hamp_sq hcum_tail
/-- `O(L)` pairwise `≤` check on equal-length `List ℤ`. -/
def solAllLeZip : List ℤ → List ℤ → Bool
  | [], ys =>
      match ys with
      | [] => true
      | _ :: _ => false
  | x :: xs, ys =>
      match ys with
      | [] => false
      | y :: ys' => solBleZ x y && solAllLeZip xs ys'
theorem solAllLeZip_spec : ∀ (xs ys : List ℤ), solAllLeZip xs ys = true → xs.length = ys.length ∧ ∀
  i < xs.length, xs.getD i 0 ≤ ys.getD i 0
  | [], [], _ => ⟨rfl, fun _ h ↦ by simp at h⟩ | [], _ :: _, h => (by simp [solAllLeZip] at h)
  | _ :: _, [], h => by simp [solAllLeZip] at h
  | x :: xs, y :: ys, h => by
    simp only [solAllLeZip, Bool.and_eq_true, solBleZ_eq_decide, decide_eq_true_eq] at h
    rcases solAllLeZip_spec xs ys h.2 with ⟨hlen, hle⟩; refine ⟨by simp [hlen], fun i hi ↦ ?_⟩
    cases i with
    | zero => simpa using h.1 | succ j => simpa using hle j (by rw [List.length_cons] at hi; omega)
/-- Multi-pulse `L2Ball` bucket/singleton certificate checker (`2 ≤ L ≤ 1024`, `1 ≤ P ≤
  5120`). -/
def checkPulseBucketCertL2 (L rMin rMax tauNum tauDen uvDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (sps : List SolSparsePulse)
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ) : Bool :=
  solWithPulseList sps fun sps ↦
    Nat.ble 2 L && Nat.ble L 1024 && Nat.ble L rMin && Nat.ble rMin rMax &&
    Nat.ble rMax 1024 && Nat.ble 1 uvDen &&
    Nat.ble 1 sps.length && Nat.ble sps.length 5120 &&
    Nat.beq certTailLbs.length L &&
    sps.all solSparsePulseValid &&
    PulseM1.checkPulseBucketAngles L rMin rMax tauNum tauDen ratios trigIvs &&
    match solEvolutionL2 L uvDen trigIvs sps with
    | (cEnd, rhoEnd, survEnd) =>
        match solTerminalBoundsL2 L cEnd rhoEnd survEnd with
        | (p0Lb, tailLbs, sUb) =>
            Nat.beq tailLbs.length L &&
            solBleZ 0 certP0Lb && solBleZ certP0Lb p0Lb &&
            solBleZ 0 certSurvUb && solBleZ sUb certSurvUb &&
            solBleZ 1 (certTailLbs.getD 0 0) &&
            solBleZ (certTailLbs.getD 0 0) swScale &&
            solBleZ 0 (certTailLbs.getD (Nat.sub L 1) 0) &&
            solAllLeZip certTailLbs tailLbs
theorem checkPulseBucketCertL2_sound {L n r rMin rMax tauNum tauDen uvDen : ℕ} {ratios : List
  IvInt} {trigIvs : List (IvInt × IvInt)} {sps : List SolSparsePulse} {certP0Lb : ℤ} {certTailLbs :
  List ℤ} {certSurvUb : ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkPulseBucketCertL2 L rMin rMax tauNum tauDen uvDen ratios trigIvs sps certP0Lb certTailLbs
  certSurvUb = true) : ∃ (hL2 : 2 ≤ L), L ≤ 1024 ∧ L ≤ r ∧ r ≤ 1024 ∧ 1 ≤ tauNum ∧ 1 ≤ tauDen ∧
  (solToSwLPulses L uvDen sps).all swLPulseValid = true ∧ certTailLbs.length = L ∧ 0 ≤ certP0Lb ∧ 0
  ≤ certSurvUb ∧ 0 < certTailLbs.getD 0 0 ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) → ℝ), IsValidSwLOverlap
  M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs (solToSwLPulses L uvDen sps)
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        0 ≤ out.2.2 ∧ out.2.2 ≤ (certSurvUb : ℝ) / (swScale : ℝ) ∧ (certP0Lb : ℝ) / (swScale : ℝ) ≤
          p 0 ∧ ∀ c ∈ Finset.Icc 1 L, ((certTailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈
          Finset.Icc c L, p h := by
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  unfold checkPulseBucketCertL2 at hchk; rw [solWithPulseList_eq] at hchk; dsimp only at hchk
  rcases hev : solEvolutionL2 L uvDen trigIvs sps with ⟨cEnd, rhoEnd, survEnd⟩; rw [hev] at hchk
  rcases htb : solTerminalBoundsL2 L cEnd rhoEnd survEnd with ⟨p0Lb, tailLbs, sUb⟩; rw [htb] at hchk
  simp only [Bool.and_eq_true, natBle_eq_decide, natBeq_eq_decide, solBleZ_eq_decide,
    decide_eq_true_eq] at hchk; rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL2, hL1024⟩, hLrMin⟩, _⟩, hrMax1024⟩,
    hden⟩, _⟩, _⟩, hclen_cert⟩, hsps⟩, hang⟩, hterm_chk⟩; rcases hterm_chk with ⟨⟨⟨⟨⟨⟨⟨⟨_, hp0_nn⟩,
    hp0_le⟩, hsurv_nn⟩, hsUb_le⟩, htl0_pos⟩, _⟩, _⟩, htl_zip⟩
  have hLr : L ≤ r := hLrMin.trans hmin; have hr1024 : r ≤ 1024 := hmax.trans hrMax1024
  rcases PulseM1.checkPulseBucketAngles_sound hn96 hmin hmax hang with ⟨_, _, _, _, htau1,
    hden1, _, htrig_mem⟩; rcases solAllLeZip_spec certTailLbs tailLbs htl_zip with ⟨_, htl_all⟩
  have hp_val : (solToSwLPulses L uvDen sps).all swLPulseValid = true := solToSwLPulses_valid L hden
    sps; refine ⟨hL2, hL1024, hLr, hr1024, htau1, hden1, hp_val, hclen_cert, hp0_nn, hsurv_nn,
    by omega, ?_⟩; intro M hM K_blk cs out p
  have hcs_unit : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  set st0 : Fin (2 * L) → ℝ := fun j ↦ if j.1 = 0 then 1 else 0
  have hin0 : swLNormSq st0 + 0 = 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 := by
    refine ⟨?_, le_rfl, zero_le_one, le_rfl⟩; unfold swLNormSq; rw [add_zero]
    have hterm : ∀ j : Fin (2 * L), (st0 j) ^ 2 = if j = ⟨0, by omega⟩ then 1 else 0 := by
      intro j; dsimp [st0]; by_cases hj : j.1 = 0
      · have hjeq : j = ⟨0, by omega⟩ := (by ext; exact hj); simp [hjeq]
      · have hjne : j ≠ ⟨0, by omega⟩ := fun h ↦ hj (congrArg Fin.val h); simp [hj, hjne]
    simp [hterm]
  have hball0 : swLNormSq (fun j ↦ st0 j - decodeCenterReal L [swScale, 0] j) ≤ (((0 : ℕ) : ℝ) /
    (swScale : ℝ)) ^ 2 := by
    have hzero : ∀ j : Fin (2 * L), st0 j - decodeCenterReal L [swScale, 0] j = 0 := by
      intro j; dsimp [st0, decodeCenterReal]; rcases j with ⟨_ | _ | _, _⟩
      · simp [div_self hS.ne']
      · simp
      · simp
    unfold swLNormSq; simp [hzero]
  have hsurv0 : (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / (swScale : ℝ) := (by rw [Int.cast_zero, zero_div])
  have hev_snd := solEvolutionL2Aux_sound hL2 hden hcs_unit htrig_mem sps hsps le_rfl (by omega) rfl
    hin0 hball0 hsurv0
  dsimp only at hev_snd; have hev_aux : solEvolutionL2Aux L uvDen trigIvs [swScale, 0] 1 0 0 sps =
      (cEnd, rhoEnd, survEnd) := by
    rw [← hev]; unfold solEvolutionL2; rw [solWithTrigList_eq]
  rw [hev_aux] at hev_snd; rcases hev_snd with ⟨hcEnd_len, hinK, hballK, hsurvK⟩; have htb_snd :=
    solTerminalBoundsL2_sound hL2 hL1024 hcEnd_len hinK hballK hsurvK hM
  dsimp only at htb_snd; rw [htb] at htb_snd; rcases htb_snd with ⟨rfl, _, hp0_real, _, htl_real⟩
  refine ⟨hinK.2.2.2, ?_, ?_, fun c hc ↦ ?_⟩
  · exact hsurvK.trans (div_le_div_of_nonneg_right (by exact_mod_cast hsUb_le) hS.le)
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hp0_le) hS.le).trans hp0_real
  · have hc_lt : c - 1 < certTailLbs.length := (by rw [Finset.mem_Icc] at hc; omega)
    exact (div_le_div_of_nonneg_right (by exact_mod_cast htl_all (c - 1) hc_lt) hS.le).trans
      (htl_real c hc)
/-- Expand a `SolWkbSched` into `List (SwLPulseRat q.L)` via `solUnrollWkbPulses`. -/
def solWkbToSwLPulses (q : SolWkbSched) : List (SwLPulseRat q.L) :=
  solToSwLPulses q.L q.uvDen (solUnrollWkbPulses q)
/-- WKB-compressed bucket/singleton certificate checker unrolling `q: SolWkbSched`
  in-kernel. -/
def checkPulseWkbBucketCertL2 (rMin rMax : ℕ) (q : SolWkbSched)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ) : Bool :=
  checkPulseBucketCertL2 q.L rMin rMax q.tauNum q.tauDen q.uvDen ratios trigIvs
    (solUnrollWkbPulses q) certP0Lb certTailLbs certSurvUb
theorem checkPulseWkbBucketCertL2_sound {n r rMin rMax : ℕ} {q : SolWkbSched} {ratios : List
  IvInt} {trigIvs : List (IvInt × IvInt)} {certP0Lb : ℤ} {certTailLbs : List ℤ} {certSurvUb : ℤ}
  (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk : checkPulseWkbBucketCertL2 rMin rMax
  q ratios trigIvs certP0Lb certTailLbs certSurvUb = true) : ∃ (hL2 : 2 ≤ q.L), q.L ≤ 1024 ∧ q.L ≤ r
  ∧ r ≤ 1024 ∧ 1 ≤ q.tauNum ∧ 1 ≤ q.tauDen ∧ (solWkbToSwLPulses q).all swLPulseValid = true ∧
  certTailLbs.length = q.L ∧ 0 ≤ certP0Lb ∧ 0 ≤ certSurvUb ∧ 0 < certTailLbs.getD 0 0 ∧ ∀ (M : Fin
  (2 * q.L) → Fin (2 * q.L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r q.tauNum q.tauDen
        let cs : Fin q.L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r
          w.1), Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal q.L hL2 cs (solWkbToSwLPulses q)
        let p : ℕ → ℝ := swLAttemptProbReal q.L hL2 M out.1 out.2.1
        0 ≤ out.2.2 ∧ out.2.2 ≤ (certSurvUb : ℝ) / (swScale : ℝ) ∧ (certP0Lb : ℝ) / (swScale : ℝ) ≤
          p 0 ∧ ∀ c ∈ Finset.Icc 1 q.L, ((certTailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h
          ∈ Finset.Icc c q.L, p h := checkPulseBucketCertL2_sound hn96 hmin hmax hchk
/-- Checkpointed prefix invariant after `t` WKB pulses of `q: SolWkbSched`. -/
def SolWkbRunPrefix (q : SolWkbSched) (trigIvs : List (IvInt × IvInt))
    (t : ℕ) (c : List ℤ) (h rho : ℕ) (surv : ℤ) : Prop :=
  (solUnrollWkbSlice q 0 t).length = t ∧
  (solUnrollWkbSlice q 0 t).all solSparsePulseValid = true ∧
  solEvolutionL2Seg q.L q.uvDen trigIvs [swScale, 0] 1 0 0 (solUnrollWkbSlice q 0 t) =
    (c, h, rho, surv)
theorem solWkbRunPrefix_zero (q : SolWkbSched) (trigIvs : List (IvInt × IvInt)) : SolWkbRunPrefix q
  trigIvs 0 [swScale, 0] 1 0 0 := by
  unfold SolWkbRunPrefix; rw [solUnrollWkbSlice_zero]; exact ⟨rfl, rfl, rfl⟩
/-- Boolean checker for a single `len`-pulse WKB slice `[t, t + len)` from checkpoint
  `(cIn, hIn, rhoIn, survIn)` to `(cOut, hOut, rhoOut, survOut)`. -/
def checkPulseWkbSlice (q : SolWkbSched) (t len : ℕ)
    (trigIvs : List (IvInt × IvInt))
    (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ)
    (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) : Bool :=
  solWithTrigList trigIvs fun trigIvs' ↦
    solWithIntList cIn fun cIn' ↦
      solWithPulseList (solUnrollWkbSlice q t len) fun sps ↦
        Nat.beq sps.length len &&
        sps.all solSparsePulseValid &&
        match solEvolutionL2Seg q.L q.uvDen trigIvs' cIn' hIn rhoIn survIn sps with
        | (c1, h1, rh1, sv1) =>
            solListIntBeq c1 cOut &&
            Nat.beq h1 hOut &&
            Nat.beq rh1 rhoOut &&
            solBeqZ sv1 survOut
theorem solWkbRunPrefix_step {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)} {t len : ℕ} {cIn :
  List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ} {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ} (hprev :
  SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn) (hslice : checkPulseWkbSlice q t len trigIvs
  cIn hIn rhoIn survIn cOut hOut rhoOut survOut = true) : SolWkbRunPrefix q trigIvs (t + len) cOut
  hOut rhoOut survOut := by
  rcases hprev with ⟨hlen1, hall1, hseg1⟩; unfold checkPulseWkbSlice at hslice
  rw [solWithTrigList_eq, solWithIntList_eq, solWithPulseList_eq] at hslice; dsimp only at hslice
  rcases hseg2 : solEvolutionL2Seg q.L q.uvDen trigIvs cIn hIn rhoIn survIn (solUnrollWkbSlice q t
    len) with ⟨c1, h1, rh1, sv1⟩; rw [hseg2] at hslice; dsimp only at hslice
  simp only [Bool.and_eq_true, natBeq_eq_decide, solBeqZ_eq_decide, decide_eq_true_eq] at hslice
  rcases hslice with ⟨⟨hlen2, hall2⟩, ⟨⟨⟨hc_eq, hh_eq⟩, hrh_eq⟩, hsv_eq⟩⟩
  have hc1 := solListIntBeq_eq_true c1 cOut hc_eq; have hadd : solUnrollWkbSlice q 0 (t + len) =
      solUnrollWkbSlice q 0 t ++ solUnrollWkbSlice q t len := by
    rw [solUnrollWkbSlice_add q 0 t len, Nat.zero_add]
  unfold SolWkbRunPrefix; rw [hadd, List.length_append, List.all_append, solEvolutionL2Seg_append]
  dsimp only; rw [hlen1, hlen2, hall1, hall2, hseg1]; dsimp only; rw [hseg2, hc1, hh_eq, hrh_eq,
    hsv_eq]; exact ⟨rfl, rfl, rfl⟩
/-- Terminal angle + Parseval certificate check for a checkpointed `SolWkbSched` run
  reaching
  `(cEnd, rhoEnd, survEnd)` after `q.K` pulses (`O(L)` work, zero pulse unrolling). -/
def checkPulseWkbTerminal (rMin rMax : ℕ) (q : SolWkbSched)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (cEnd : List ℤ) (rhoEnd : ℕ) (survEnd : ℤ)
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ) : Bool :=
  solWithIntList cEnd fun cEnd' ↦
    Nat.ble 2 q.L && Nat.ble q.L 1024 && Nat.ble q.L rMin && Nat.ble rMin rMax &&
    Nat.ble rMax 1024 && Nat.ble 1 q.uvDen &&
    Nat.ble 1 q.K && Nat.ble q.K 5120 &&
    Nat.beq certTailLbs.length q.L &&
    PulseM1.checkPulseBucketAngles q.L rMin rMax q.tauNum q.tauDen ratios trigIvs &&
    match solTerminalBoundsL2 q.L cEnd' rhoEnd survEnd with
    | (p0Lb, tailLbs, sUb) =>
        Nat.beq tailLbs.length q.L &&
        solBleZ 0 certP0Lb && solBleZ certP0Lb p0Lb &&
        solBleZ 0 certSurvUb && solBleZ sUb certSurvUb &&
        solBleZ 1 (certTailLbs.getD 0 0) &&
        solBleZ (certTailLbs.getD 0 0) swScale &&
        solBleZ 0 (certTailLbs.getD (Nat.sub q.L 1) 0) &&
        solAllLeZip certTailLbs tailLbs
theorem checkPulseWkbBucketCertL2_of_runPrefix {rMin rMax : ℕ} {q : SolWkbSched} {ratios : List
  IvInt} {trigIvs : List (IvInt × IvInt)} {cEnd : List ℤ} {hEnd rhoEnd : ℕ} {survEnd : ℤ} {certP0Lb
  : ℤ} {certTailLbs : List ℤ} {certSurvUb : ℤ} (hrun : SolWkbRunPrefix q trigIvs q.K cEnd hEnd
  rhoEnd survEnd) (hterm : checkPulseWkbTerminal rMin rMax q ratios trigIvs cEnd rhoEnd survEnd
  certP0Lb certTailLbs certSurvUb = true) : checkPulseWkbBucketCertL2 rMin rMax q ratios trigIvs
  certP0Lb certTailLbs certSurvUb = true := by
  rcases hrun with ⟨hlen, hall, hseg⟩
  have hev : solEvolutionL2 q.L q.uvDen trigIvs (solUnrollWkbSlice q 0 q.K) = (cEnd, rhoEnd,
    survEnd) := by
    unfold solEvolutionL2; rw [solWithTrigList_eq, solEvolutionL2Aux_eq_seg]; dsimp only; rw [hseg]
  unfold checkPulseWkbBucketCertL2 solUnrollWkbPulses checkPulseBucketCertL2
  rw [solWithPulseList_eq]; dsimp only; rw [hev]; dsimp only; rw [hlen, hall, Bool.and_true]
  unfold checkPulseWkbTerminal at hterm; rw [solWithIntList_eq] at hterm; dsimp only at hterm
  exact hterm
/- ## 4. Non-Monotone + Envelope `vPrevs` Bellman Cascade Checker & Soundness -/
/-- Structural `List.rec` Bellman gain accumulator weighting `dv ≥ 0` by `tl` and `dv < 0`
  by
  `swScale - p0Lb` (supports both monotone envelopes and non-monotone dyadic landing
  credit). -/
def solCascadeGainSum (p0Lb : ℤ) : List ℤ → List ℤ → ℤ → ℤ
  | [], _, acc => acc
  | tl :: tls, chain, acc =>
      let v0 := headZP chain
      let v1 := secondZP chain
      let restChain := match chain with | _ :: xs => xs | [] => []
      solSeqInt (Int.sub v0 v1) fun dv ↦
        let w := cond (solBleZ 0 dv) tl (Int.sub swScale p0Lb)
        solSeqInt (Int.add acc (Int.mul w dv)) fun acc' ↦
          solCascadeGainSum p0Lb tls restChain acc'
theorem solCascadeGainSum_eq (p0Lb : ℤ) : ∀ (tls chain : List ℤ) (acc : ℤ), solCascadeGainSum p0Lb
  tls chain acc = acc + ∑ c ∈ Finset.range tls.length, (if 0 ≤ chain.getD c 0 - chain.getD (c + 1) 0
  then tls.getD c 0 else swScale - p0Lb) * (chain.getD c 0 - chain.getD (c + 1) 0)
  | [], _, acc => by simp [solCascadeGainSum]
  | tl :: tls, chain, acc => by
    unfold solCascadeGainSum; simp only [solSeqInt_eq, headZP_eq, secondZP_eq]
    rw [solCascadeGainSum_eq p0Lb tls (match chain with | _ :: xs => xs | [] => [])]
    have hshift : ∀ k : ℕ,
        (match chain with | _ :: xs => xs | [] => []).getD k 0 = chain.getD (k + 1) 0 := by
      intro k; cases chain <;> simp
    have hw : (cond (solBleZ 0 (Int.sub (chain.getD 0 0) (chain.getD 1 0))) tl (Int.sub swScale
      p0Lb)) = if 0 ≤ chain.getD 0 0 - chain.getD 1 0 then tl else swScale - p0Lb := by
      change (cond (solBleZ 0 (chain.getD 0 0 - chain.getD 1 0)) tl (swScale - p0Lb)) = _
      rw [solBleZ_eq_decide]; by_cases h : 0 ≤ chain.getD 0 0 - chain.getD 1 0
      · rw [decide_eq_true h, ite_eq_left h]; rfl
      · rw [decide_eq_false h, ite_eq_right h]; rfl
    rw [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero]
    have hsum_eq : ∑ k ∈ Finset.range tls.length,
          (if 0 ≤ (match chain with | _ :: xs => xs | [] => []).getD k 0 -
              (match chain with | _ :: xs => xs | [] => []).getD (k + 1) 0
            then tls.getD k 0 else swScale - p0Lb) *
            ((match chain with | _ :: xs => xs | [] => []).getD k 0 -
              (match chain with | _ :: xs => xs | [] => []).getD (k + 1) 0) =
        ∑ k ∈ Finset.range tls.length,
          (if 0 ≤ chain.getD (k + 1) 0 - chain.getD (k + 1 + 1) 0
            then (tl :: tls).getD (k + 1) 0 else swScale - p0Lb) *
            (chain.getD (k + 1) 0 - chain.getD (k + 1 + 1) 0) := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_; rw [hshift k, hshift (k + 1), List.getD_cons_succ]
    rw [hsum_eq, hw]; change _ + ((if 0 ≤ _ then tl else swScale - p0Lb) * (chain.getD 0 0 -
      chain.getD 1 0)) + _ = _; ring
/-- `O(L)` walk checking `vTable (r - (w + 1)) ≤ vPrevs[w]` for `w, w + 1,...`. -/
def solVPrevsDomWalk (r : ℕ) (vTable : ℕ → ℤ) : ℕ → List ℤ → Bool
  | _, [] => true
  | w, vp :: vps =>
      solBleZ (vTable (Nat.sub r (Nat.add w 1))) vp &&
      solVPrevsDomWalk r vTable (Nat.add w 1) vps
theorem solVPrevsDomWalk_spec (r : ℕ) (vTable : ℕ → ℤ) : ∀ (w : ℕ) (vps : List ℤ), solVPrevsDomWalk
  r vTable w vps = true → ∀ i < vps.length, vTable (r - (w + i + 1)) ≤ vps.getD i 0
  | _, [], _, _, hi => by simp at hi
  | w, vp :: vps, h, i, hi => by
    simp only [solVPrevsDomWalk, Bool.and_eq_true, solBleZ_eq_decide, decide_eq_true_eq,
      solNatSub_eq, solNatAdd_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
        have hj := solVPrevsDomWalk_spec r vTable (w + 1) vps h.2 j
          (by rw [List.length_cons] at hi; omega); rw [show w + 1 + j + 1 = w + (j + 1) + 1
          by omega] at hj; simpa using hj
/-- Check `vPrevs.length = L`, `vCur ≤ vTable r`, and `vTable (r - (w + 1)) ≤ vPrevs[w]`. -/
def checkPulseVTableDom (L r : ℕ) (vTable : ℕ → ℤ) (vCur : ℤ) (vPrevs : List ℤ) : Bool :=
  Nat.beq vPrevs.length L &&
  solBleZ vCur (vTable r) &&
  solVPrevsDomWalk r vTable 0 vPrevs
theorem checkPulseVTableDom_spec {L r : ℕ} {vTable : ℕ → ℤ} {vCur : ℤ} {vPrevs : List ℤ} (hdom :
  checkPulseVTableDom L r vTable vCur vPrevs = true) : vPrevs.length = L ∧ vCur ≤ vTable r ∧ ∀ w <
  L, vTable (r - (w + 1)) ≤ vPrevs.getD w 0 := by
  unfold checkPulseVTableDom at hdom; simp only [Bool.and_eq_true, natBeq_eq_decide,
    solBleZ_eq_decide, decide_eq_true_eq] at hdom
  rcases hdom with ⟨⟨hlen, hvcur⟩, hwalk⟩; refine ⟨hlen, hvcur, fun w hw ↦ ?_⟩; have h :=
    solVPrevsDomWalk_spec r vTable 0 vPrevs hwalk w (by omega); simpa using h
/-- Pure-GMP non-monotone + envelope Bellman cascade step checker (`2 ≤ L ≤ r ≤ 1024`)
  at `multiUnitScale = 10^16` (`survUb` arg 5, `p0Lb` arg 6, `vCur` scalar arg 8). -/
def checkPulseCascadeStep (L r tauNum tauDen : ℕ)
    (survUb p0Lb : ℤ) (tailLbs : List ℤ) (vCur : ℤ) (vPrevs : List ℤ) : Bool :=
  Nat.ble 2 L && Nat.ble L 1024 && Nat.ble L r && Nat.ble r 1024 &&
  Nat.ble 1 tauNum && Nat.ble 1 tauDen &&
  Nat.beq tailLbs.length L && Nat.beq vPrevs.length L &&
  solBleZ 0 survUb &&
  solBleZ 0 p0Lb && solBleZ p0Lb (Int.sub swScale 1) &&
  solBleZ 1 (tailLbs.getD 0 0) && solBleZ (tailLbs.getD 0 0) swScale &&
  solBleZ 0 (vPrevs.getD (Nat.sub L 1) 0) &&
  solSeqInt (solCascadeGainSum p0Lb tailLbs (vCur :: vPrevs) 0) fun rhsInt ↦
    solSeqInt (Int.add (Int.mul 3 survUb) (Int.mul (Int.mul 2 swScale) (Int.ofNat L)))
      fun bNum ↦
        solSeqInt (Int.sub (Int.mul rhsInt swBden49) (Int.mul multiUnitScale bNum)) fun rem ↦
          solBleZ 0 rem &&
          solBleZ
            (let lhs :=
               Int.mul (Int.mul (Int.mul survUb (Int.ofNat tauNum)) multiUnitScale) swBden49
             Int.mul lhs lhs)
            (Int.mul
              (Int.mul (Int.mul 4 (Int.mul (Int.ofNat tauDen) (Int.ofNat tauDen)))
                (Int.ofNat r))
              (Int.mul rem rem))
/-- Direct table wrapper passing `vTable r` and `[vTable (r - 1),..., vTable (r - L)]`. -/
def checkPulseCascadeStepTable (L r tauNum tauDen : ℕ)
    (survUb p0Lb : ℤ) (tailLbs : List ℤ) (vTable : ℕ → ℤ) : Bool :=
  checkPulseCascadeStep L r tauNum tauDen survUb p0Lb tailLbs (vTable r)
    ((List.range L).map fun w ↦ vTable (Nat.sub r (Nat.add w 1)))
theorem checkPulseCascadeStage_sound {L n r rMin rMax tauNum tauDen uvDen : ℕ} {ratios : List
  IvInt} {trigIvs : List (IvInt × IvInt)} {sps : List SolSparsePulse} {p0Lb : ℤ} {tailLbs : List ℤ}
  {survUb vCur : ℤ} {vTable : ℕ → ℤ} {vPrevs : List ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤
  rMax) (hbkt : checkPulseBucketCertL2 L rMin rMax tauNum tauDen uvDen ratios trigIvs sps p0Lb
  tailLbs survUb = true) (hstep : checkPulseCascadeStep L r tauNum tauDen survUb p0Lb tailLbs vCur
  vPrevs = true) (hdom : checkPulseVTableDom L r vTable vCur vPrevs = true) : ∃ (hL2 : 2 ≤ L), L ≤
  1024 ∧ L ≤ r ∧ (solToSwLPulses L uvDen sps).all swLPulseValid = true ∧ ∀ (M : Fin (2 * L) → Fin (2
  * L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs (solToSwLPulses L uvDen sps)
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (L : ℝ) + ∑ h ∈ Finset.Icc 1 L, p h * V (r - h)) /
          pSucc ≤ V r := by
  rcases checkPulseBucketCertL2_sound hn96 hmin hmax hbkt with ⟨hL2, hL1024, hLr, hr1024, htau1,
    hden1, hp_val, htl_len, _, hsurv0, htl0_pos, hbkt_M⟩
  rcases checkPulseVTableDom_spec hdom with ⟨_, hvcur_le, hvprev_le⟩
  unfold checkPulseCascadeStep at hstep; simp only [solSeqInt_eq, Bool.and_eq_true,
    natBle_eq_decide, natBeq_eq_decide, solBleZ_eq_decide, decide_eq_true_eq] at hstep
  rcases hstep with ⟨_, hrem0, hsq_ineq⟩; refine ⟨hL2, hL1024, hLr, hp_val, ?_⟩
  intro M hM K_blk cs out p pSucc V; rcases hbkt_M M hM with ⟨_, hsurv_le, hp0_lb, htail_lbs⟩
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hvsc_r : (0 : ℝ) <
    (multiUnitScale : ℝ) := (by unfold SchurWeylLCert.multiUnitScale; norm_num); have hbden_r : (0 :
    ℝ) < (swBden49 : ℝ) := (by unfold swBden49; norm_num)
  set N : ℝ := (2 ^ n : ℝ); have hsqrtN_pos : 0 < √N := (by dsimp [N]; positivity)
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow); have h1 : (281474976710656 : ℝ) ^ 2 ≤ N :=
      (by have : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := (by norm_num); linarith)
    have h2 : (281474976710656 : ℝ) ≤ √N :=
      (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]; exact Real.sqrt_le_sqrt h1)
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := (by unfold swBden49; norm_num); linarith
  have hcs_unit : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit (solToSwLPulses L uvDen sps) hp_val with
    ⟨hcons, hcum0, _, _⟩
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range (L + 1), p h = 1 := swLAttemptProbReal_sum_one hL2 hM hcons
  have hpSucc_pos : 0 < pSucc := by
    have hlb1 := htail_lbs 1 (by rw [Finset.mem_Icc]; omega); have hpos : 0 < ((tailLbs.getD 0 0 :
      ℤ) : ℝ) / (swScale : ℝ) := div_pos (by exact_mod_cast htl0_pos) hS; exact hpos.trans_le hlb1
  refine ⟨hpSucc_pos, ?_⟩
  have htail_ub : ∀ c < L, ∑ h ∈ Finset.Icc (c + 1) L, p h ≤ ((swScale - p0Lb : ℤ) : ℝ) / (swScale :
    ℝ) := by
    intro c _hc
    have hsub : Finset.Icc (c + 1) L ⊆ Finset.Icc 1 L := Finset.Icc_subset_Icc_left (by omega)
    have hle_succ : ∑ h ∈ Finset.Icc (c + 1) L, p h ≤ pSucc := Finset.sum_le_sum_of_subset_of_nonneg
      hsub fun h _ _ ↦ hp_nn h
    have hsplit : ∑ h ∈ Finset.range (L + 1), p h = p 0 + pSucc := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L + 1),
        Finset.Ico_add_one_right_eq_Icc]
    have hpSucc_ub : pSucc ≤ 1 - (p0Lb : ℝ) / (swScale : ℝ) := by linarith [hp_sum1, hsplit, hp0_lb]
    have hrw : 1 - (p0Lb : ℝ) / (swScale : ℝ) = ((swScale - p0Lb : ℤ) : ℝ) / (swScale : ℝ) :=
      (by push_cast; rw [sub_div, div_self hS.ne']); linarith
  set chain : List ℤ := vCur :: vPrevs; set Vp : ℕ → ℝ := fun k ↦ ((chain.getD k 0 : ℝ) /
    (multiUnitScale : ℝ)) * √N; set rhsInt : ℤ := solCascadeGainSum p0Lb tailLbs chain 0
  have hrhs_eq : rhsInt = ∑ c ∈ Finset.range L, (if 0 ≤ chain.getD c 0 - chain.getD (c + 1) 0 then
    tailLbs.getD c 0 else swScale - p0Lb) * (chain.getD c 0 - chain.getD (c + 1) 0) :=
    (by dsimp [rhsInt]; rw [solCascadeGainSum_eq, zero_add, htl_len])
  have hgain_vp : ((rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ))) * √N ≤ ∑ h ∈ Finset.Icc 1
    L, p h * (Vp 0 - Vp h) := by
    rw [sum_Icc_abel L p Vp, hrhs_eq]
    have hrew : ((∑ c ∈ Finset.range L, (if 0 ≤ chain.getD c 0 - chain.getD (c + 1) 0 then
      tailLbs.getD c 0 else swScale - p0Lb) * (chain.getD c 0 - chain.getD (c + 1) 0) : ℤ) : ℝ) /
      ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N = ∑ c ∈ Finset.range L, (((if 0 ≤ chain.getD c 0 -
      chain.getD (c + 1) 0 then tailLbs.getD c 0 else swScale - p0Lb : ℤ) : ℝ) / (swScale : ℝ)) *
      (Vp c - Vp (c + 1)) := by
      dsimp [Vp]; push_cast; rw [sum_div_const, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ ↦ ?_; ring
    rw [hrew]; refine Finset.sum_le_sum fun c hc ↦ ?_; rw [Finset.mem_range] at hc; set dv : ℤ :=
      chain.getD c 0 - chain.getD (c + 1) 0; have hdv_r : Vp c - Vp (c + 1) = ((dv : ℝ) /
      (multiUnitScale : ℝ)) * √N := (by dsimp [Vp, dv]; push_cast; ring); by_cases hdv0 : 0 ≤ dv
    · simp only [hdv0, ↓reduceIte]
      have hnn : 0 ≤ Vp c - Vp (c + 1) := by
        rw [hdv_r]; exact mul_nonneg (div_nonneg (by exact_mod_cast hdv0) hvsc_r.le) hsqrtN_pos.le
      have htl_c := htail_lbs (c + 1) (by rw [Finset.mem_Icc]; omega)
      simp only [Nat.add_sub_cancel] at htl_c; exact mul_le_mul_of_nonneg_right htl_c hnn
    · simp only [hdv0, ↓reduceIte]
      have hnp : Vp c - Vp (c + 1) ≤ 0 := by
        rw [hdv_r]; have hd_le : (dv : ℝ) ≤ 0 := (by exact_mod_cast (by omega : dv ≤ 0))
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hd_le hvsc_r.le)
          hsqrtN_pos.le
      exact mul_le_mul_of_nonpos_right (htail_ub c hc) hnp
  have hvp_dom_V : ∑ h ∈ Finset.Icc 1 L, p h * (Vp 0 - Vp h) ≤ ∑ h ∈ Finset.Icc 1 L, p h * (V r - V
    (r - h)) := by
    refine Finset.sum_le_sum fun h hh ↦ ?_; rw [Finset.mem_Icc] at hh
    have hvp0_le : Vp 0 ≤ V r := by
      dsimp [Vp, chain, V]; exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by exact_mod_cast hvcur_le) hvsc_r.le) hsqrtN_pos.le
    have hv_le : V (r - h) ≤ Vp h := by
      obtain ⟨w, rfl⟩ : ∃ w, h = w + 1 := ⟨h - 1, by omega⟩; have hw : w < L := (by omega)
      have hle_z : vTable (r - (w + 1)) ≤ vPrevs.getD w 0 := hvprev_le w hw; dsimp [V, Vp, chain];
        rw [List.getD_cons_succ]; exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (by exact_mod_cast hle_z) hvsc_r.le) hsqrtN_pos.le
    exact mul_le_mul_of_nonneg_left (by linarith) (hp_nn h)
  have hgain_ge := hgain_vp.trans hvp_dom_V
  have hK_ub := kBlk_le_main_add_three_halves hn96 (by omega) hr1024 htau1 hden1; set bNum : ℤ :=
    Int.add (Int.mul 3 survUb) (Int.mul (Int.mul 2 swScale) (Int.ofNat L))
  have hbNum_eq : bNum = 3 * survUb + 2 * swScale * (L : ℤ) := rfl
  have hcost_ub : out.2.2 * (K_blk : ℝ) + (L : ℝ) ≤ (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale :
    ℝ) * (tauDen : ℝ) * √(r : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
    have h1 : out.2.2 * (K_blk : ℝ) ≤ ((survUb : ℝ) / (swScale : ℝ)) * (((tauNum : ℝ) / (2 * (tauDen
      : ℝ) * √(r : ℝ))) * √N + 3 / 2) := mul_le_mul hsurv_le hK_ub (Nat.cast_nonneg K_blk)
      (div_nonneg (by exact_mod_cast hsurv0) hS.le)
    have hbNum_nn : 0 ≤ (bNum : ℝ) := by
      rw [hbNum_eq]; unfold swScale
      exact_mod_cast (by omega : (0 : ℤ) ≤ 3 * survUb + 2 * 1000000000 * (L : ℤ))
    have hoverh : (bNum : ℝ) / (2 * (swScale : ℝ)) ≤ ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)))
      * √N := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtN_ge (div_nonneg hbNum_nn (mul_pos hS hbden_r).le)
      refine (?_ : (bNum : ℝ) / (2 * (swScale : ℝ)) = ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 :
        ℝ))) * ((swBden49 : ℝ) / 2)).trans_le hmul; field_simp [hS.ne', hbden_r.ne']
    have halg : ((survUb : ℝ) / (swScale : ℝ)) * (((tauNum : ℝ) / (2 * (tauDen : ℝ) * √(r : ℝ))) *
      √N + 3 / 2) + (L : ℝ) = (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) *
      √(r : ℝ))) * √N + (bNum : ℝ) / (2 * (swScale : ℝ)) :=
      (by rw [hbNum_eq]; push_cast; field_simp [hS.ne']; ring); linarith
  set rem : ℤ := Int.sub (Int.mul rhsInt swBden49) (Int.mul multiUnitScale bNum)
  have hrem_eq : rem = rhsInt * swBden49 - multiUnitScale * bNum := rfl
  have hcoef_le : ((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ)) +
    (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)) ≤ (rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale
    : ℝ)) := by
    have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r))
    have hsqrt_r_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
    have hden_r : (0 : ℝ) < (tauDen : ℝ) := (by exact_mod_cast hden1); have hrem_r : (0 : ℝ) ≤ (rem
      : ℝ) := (by exact_mod_cast hrem0)
    have hlhs_nn : 0 ≤ (survUb : ℝ) * (tauNum : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ) :=
      (by have : (0 : ℝ) ≤ (survUb : ℝ) := (by exact_mod_cast hsurv0); positivity)
    have hrhs_nn : 0 ≤ 2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ) := (by positivity)
    have hsq_ineq' : (survUb * (tauNum : ℤ) * multiUnitScale * swBden49) ^ 2 ≤ 4 * (tauDen : ℤ) ^ 2
      * (r : ℤ) * rem ^ 2 :=
      (by simpa [sq, solIntMul_eq, Int.ofNat_eq_natCast, mul_assoc] using hsq_ineq)
    have hsq_r : ((survUb : ℝ) * (tauNum : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ)) ^ 2 ≤ (2 *
      (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 := by
      have hcast : (((survUb * (tauNum : ℤ) * multiUnitScale * swBden49) ^ 2 : ℤ) : ℝ) ≤ ((4 *
        (tauDen : ℤ) ^ 2 * (r : ℤ) * rem ^ 2 : ℤ) : ℝ) := (by exact_mod_cast hsq_ineq')
      push_cast at hcast; have hsq_rhs : (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 =
          4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2 := by
        calc (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2
          _ = 4 * (tauDen : ℝ) ^ 2 * (√(r : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by ring
          _ = 4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
      linarith
    have hroot : (survUb : ℝ) * (tauNum : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ) ≤ 2 * (tauDen :
      ℝ) * √(r : ℝ) * (rem : ℝ) :=
      (by rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_r)
    have hrem_def : (rem : ℝ) = (rhsInt : ℝ) * (swBden49 : ℝ) - (multiUnitScale : ℝ) * (bNum : ℝ) :=
      (by rw [hrem_eq]; push_cast; rfl); rw [hrem_def] at hroot; have hpos_prod : 0 < 2 * (swScale :
      ℝ) * (tauDen : ℝ) * √(r : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ) := (by positivity)
    rw [← sub_nonneg]
    have hdiff : (rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) - (((survUb : ℝ) * (tauNum :
      ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49
      : ℝ))) = (2 * (tauDen : ℝ) * √(r : ℝ) * ((rhsInt : ℝ) * (swBden49 : ℝ) - (multiUnitScale : ℝ)
      * (bNum : ℝ)) - (survUb : ℝ) * (tauNum : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ)) / (2 *
      (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ)) :=
      (by field_simp [hS.ne', hden_r.ne', hsqrt_r_pos.ne', hvsc_r.ne', hbden_r.ne']; ring)
    rw [hdiff]; exact div_nonneg (by linarith) hpos_prod.le
  have hnet : out.2.2 * (K_blk : ℝ) + (L : ℝ) ≤ ∑ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) :=
    (hcost_ub.trans (mul_le_mul_of_nonneg_right hcoef_le hsqrtN_pos.le)).trans hgain_ge
  have hexpand : ∑ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) = pSucc * V r - ∑ h ∈ Finset.Icc 1 L,
    p h * V (r - h) := by
    dsimp [pSucc]; rw [Finset.sum_mul]; have hsub : ∀ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) =
        p h * V r - p h * V (r - h) := fun _ _ ↦ mul_sub _ _ _; rw [Finset.sum_congr rfl hsub,
      Finset.sum_sub_distrib]
  rw [div_le_iff₀ hpSucc_pos]; linarith [hnet, hexpand]
theorem checkPulseWkbCascadeStage_sound {n r rMin rMax : ℕ} {q : SolWkbSched} {ratios : List
  IvInt} {trigIvs : List (IvInt × IvInt)} {p0Lb : ℤ} {tailLbs : List ℤ} {survUb vCur : ℤ} {vTable :
  ℕ → ℤ} {vPrevs : List ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hbkt :
  checkPulseWkbBucketCertL2 rMin rMax q ratios trigIvs p0Lb tailLbs survUb = true) (hstep :
  checkPulseCascadeStep q.L r q.tauNum q.tauDen survUb p0Lb tailLbs vCur vPrevs = true) (hdom :
  checkPulseVTableDom q.L r vTable vCur vPrevs = true) : ∃ (hL2 : 2 ≤ q.L), q.L ≤ 1024 ∧ q.L ≤ r ∧
  (solWkbToSwLPulses q).all swLPulseValid = true ∧ ∀ (M : Fin (2 * q.L) → Fin (2 * q.L) → ℝ),
  IsValidSwLOverlap M →
        let K_blk := swLKBlk n r q.tauNum q.tauDen
        let cs : Fin q.L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r
          w.1), Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal q.L hL2 cs (solWkbToSwLPulses q)
        let p : ℕ → ℝ := swLAttemptProbReal q.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 q.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (q.L : ℝ) + ∑ h ∈ Finset.Icc 1 q.L, p h * V (r - h)) /
          pSucc ≤ V r := checkPulseCascadeStage_sound hn96 hmin hmax hbkt hstep hdom
/- ## 5. `PulseM1CertBundle`, Stage Loop, `RelCost` Checker & `ValidFindAllFamily` Bridges -/
/-- Alias for `SwLM1StageSpec` (`2 ≤ L ≤ 1024` multi-pulse conveyor stage specification). -/
abbrev PulseM1StageSpec := SwLM1StageSpec
/-- Non-monotone stage-soundness bundle for `m = 1` multi-pulse conveyors (`2 ≤ L ≤ 1024`,
  `1152 ≤ n`) with cold-entry fallback wherever `usePulse r = false`. -/
structure PulseM1CertBundle where
  /-- Maximum supported target count `kMax ≤ 1024`. -/
  kMax : ℕ
  /-- Fixed-point Bellman scale `vScale > 0` (typically `10^16`). -/
  vScale : ℤ
  /-- Certified Bellman value table `vTable r` (`0 ≤ r ≤ kMax`, no global monotonicity
    required). -/
  vTable : ℕ → ℤ
  /-- Stage routing flag (`true` for multi-pulse `H_dist(L)` stage, `false` for `coldCirc`). -/
  usePulse : ℕ → Bool
  /-- Multi-pulse stage parameters at remaining target count `r`. -/
  stageOfR : ℕ → PulseM1StageSpec
  /-- Bound `kMax ≤ 1024`. -/
  hKMax : kMax ≤ 1024
  /-- Positivity of fixed-point scale `vScale`. -/
  hScalePos : 0 < vScale
  /-- Base Bellman boundary condition `vTable 0 = 0`. -/
  hV0 : vTable 0 = 0
  /-- Nonnegativity of `vTable r` for `0 ≤ r ≤ kMax`. -/
  hNonneg : ∀ r : ℕ, r ≤ kMax → 0 ≤ vTable r
  /-- Per-stage Bellman soundness at every active multi-pulse count `r`. -/
  hStageSound : ∀ {n r : ℕ}, 1152 ≤ n → 1 ≤ r → r ≤ kMax → usePulse r = true →
    let s := stageOfR r
    ∃ (hL2 : 2 ≤ s.L),
      s.L ≤ 1024 ∧ s.L ≤ r ∧
      s.pulses.all swLPulseValid = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
        IsValidSwLOverlap M →
        let K_blk := hdistLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := hdistLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧
        (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
          ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
/-- Fuel-bounded `m = 1` multi-pulse stage recursion (`2 ≤ L ≤ 1024`) on `Q ≥ findAllQubits
  n 1 k`. -/
noncomputable def pulseM1StageLoop {Var : Type} (res : Var) (B : PulseM1CertBundle)
    {n k Q : ℕ} (hQ : findAllQubits n 1 k ≤ Q)
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) :
    ℕ → ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)
  | 0, _, T => swLWriteFinsetLiftCircuit res hQ T
  | fuel + 1, r, T =>
      if r = 0 then
        swLWriteFinsetLiftCircuit res hQ T
      else if B.usePulse r = true then
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
              if 1 ≤ H.card then
                pulseM1StageLoop res B hQ coldCirc fuel (r - H.card) (T ∪ H)
              else
                .skip)
        else
          coldCirc r T
      else
        coldCirc r T
/-- Polymorphic cold-entry `m = 1` multi-pulse stage circuit on `findAllQubits n 1 k`. -/
noncomputable def pulseM1FromSetWithColdCircuit {Var : Type} (res : Var)
    (B : PulseM1CertBundle) {n k : ℕ}
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
        (findAllQubits n 1 k) ((n + 1) * 1))
    (r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  pulseM1StageLoop res B le_rfl coldCirc r r T
theorem pulseM1StageLoop_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var) (B :
    PulseM1CertBundle) {n k Q : ℕ} (hQ : findAllQubits n 1 k ≤ Q) (coldCirc : ℕ → Finset (Fin (2
    ^ n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) (hn : 1152 ≤ n) (_hk1 : 1
    ≤ k) (hkMax : k ≤ B.kMax) (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))}, 1 ≤ r' → r' ≤ k →
    B.usePulse r' = false → ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \
    T').card = r' → ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ))) :
    ∀ (fuel r : ℕ) (T : Finset (Fin (2 ^ n))),
      r ≤ fuel → r ≤ k →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → (S \ T).card = r →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (pulseM1StageLoop res B hQ coldCirc fuel r T).compile
          QProg.qAssign (parallelMarkingOracle 1 S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) :=
  by
  intro fuel
  induction fuel with
  | zero =>
    intro r T hrf _ S hScard hTS hrem Δ hΔ; have hr0 : r = 0 := (by omega); subst hr0
    have hTS_eq : T = S := Finset.Subset.antisymm hTS (Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.card_eq_zero.mp hrem)); subst hTS_eq; obtain ⟨hexp, hcost⟩ :=
      swLWriteFinsetLift_transition res hQ hScard hΔ; refine ⟨hexp, ?_⟩
    dsimp only [pulseM1StageLoop]; rw [hcost, B.hV0]; simp
  | succ fuel ih =>
    intro r T hrf hr_le S hScard hTS hrem Δ hΔ; by_cases hr0 : r = 0
    · subst hr0; have hTS_eq : T = S := Finset.Subset.antisymm hTS
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem))
      subst hTS_eq; unfold pulseM1StageLoop; rw [ite_eq_left rfl]; obtain ⟨hexp, hcost⟩ :=
        swLWriteFinsetLift_transition res hQ hScard hΔ; refine ⟨hexp, ?_⟩; rw [hcost, B.hV0]; simp
    · have hr1 : 1 ≤ r := (by omega); by_cases hsw : B.usePulse r = true
      · set R := S \ T; set s := B.stageOfR r; have hr_kMax : r ≤ B.kMax := hr_le.trans hkMax
        have hr1024 : r ≤ 1024 := hr_kMax.trans B.hKMax
        obtain ⟨hL2, hL1024, hrL, hpulses, hsound⟩ := B.hStageSound hn hr1 hr_kMax hsw; change 2 ≤
          s.L at hL2; change s.L ≤ 1024 at hL1024; change s.L ≤ r at hrL; have hn0 : 0 < n :=
          (by omega)
        have hn_pow : 4096 ≤ 2 ^ n := (by norm_num : 4096 ≤ 2 ^ 12).trans (Nat.pow_le_pow_right
          (by omega) (by omega))
        have hn2L : 2 * s.L ≤ 2 ^ n := (by omega); have hrN : r + s.L ≤ 2 ^ n := (by omega)
        have hQ_sw : swLWireBound n 1 s.L ≤ Q := (swLWireBound_m1_le_findAllQubits_pulse hL2
          (hrL.trans hr_le) (by omega)).trans hQ; have hcond : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧
          swLWireBound n 1 s.L ≤ Q := ⟨hn0, hL2, hn2L, hQ_sw⟩
        have hM_valid : IsValidSwLOverlap (swLOverlapMatFn s.L R) :=
          isValidSwLOverlap_swLOverlapMatFn_pulse hL2 hL1024 hn hrL hr1024 hrem
        obtain ⟨hpSucc_pos, hBell⟩ := hsound (swLOverlapMatFn s.L R) hM_valid; set K_blk :=
          hdistLKBlk n r s.tauNum s.tauDen; set cs : Fin s.L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk :
          ℝ) * swLThetaShiftReal (2 ^ n) r w.1), Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r
          w.1)); set out := hdistLEvolutionReal s.L hL2 cs s.pulses; set pHit : ℕ → ℝ :=
          swLAttemptProbReal s.L hL2 (swLOverlapMatFn s.L R) out.1 out.2.1
        set V : ℕ → ℝ := fun j ↦ ((B.vTable j : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)
        have hV_nn : ∀ j ≤ B.kMax, 0 ≤ V j := fun j hj ↦ by
          dsimp only [V]; have hv_nn : (0 : ℝ) ≤ (B.vTable j : ℝ) :=
            (by exact_mod_cast B.hNonneg j hj); have hsc_pos : (0 : ℝ) < (B.vScale : ℝ) :=
            (by exact_mod_cast B.hScalePos); positivity
        obtain ⟨hwt_nn, hwt_sum, hbot, hwp0, hcost_body, hsub_wt, hsum_P⟩ :=
          swLM1AttemptBody_profile (Var := Var) res hn0 hL2 hn2L hQ_sw hrL hrN hrem K_blk hpulses
        set cBody := swLM1AttemptBodyCircuit (Var := Var) res n s.L Q hn0 hL2 hn2L hQ_sw K_blk
          s.pulses; set keepLoop : ℕ → Bool := fun v ↦ !swLHasVerifHit n 1 s.L Q hn0 hL2 hQ_sw v
        set wt : Fin (2 ^ Q) → ℝ := fun o ↦ ∑ z : Fin (2 ^ (s.L * n + 1)), if swLPackVerifBasis n 1
          s.L Q hn0 hL2 hQ_sw R (fun _ ↦ z) = o then Complex.normSq (swLSurvVec s.L n R out.1 z) +
          out.2.1 * Complex.normSq (swLClickVec s.L n R z) else 0
        have hkeep0 : keepLoop 0 = true := (by simp [keepLoop, swLHasVerifHit_zero])
        have hpSucc_eq : (∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o) = ∑ h ∈ Finset.Icc 1
          s.L, pHit h :=
          (by have h1 := hsum_P (fun _ ↦ (1 : ℝ)); simpa [keepLoop, wt, pHit, mul_one] using h1)
        have hsucc_wt_pos : 0 < ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o :=
          (by rwa [hpSucc_eq]); set cRaw := swLResetWhileCircuit res keepLoop cBody
        have hcRaw_zero : ZeroStepCost cRaw := zeroStepCost_swLResetWhileCircuit res keepLoop
          (zeroStepCost_swLM1AttemptBodyCircuit res n s.L Q hn0 hL2 hn2L hQ_sw K_blk s.pulses)
        obtain ⟨hslice_att, hcost_att⟩ := swLResetWhile_transition res (parallelMarkingOracle 1 R)
          hkeep0 cBody wt (out.2.2 * (K_blk : ℝ) + (s.L : ℝ)) hwt_nn hwt_sum hbot hwp0 (fun {Ξ} hΞ ↦
          hcost_body hΞ) hsucc_wt_pos hΔ; set pSucc : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val =
          false, wt o; set Δ_att := (interp (cRaw.compile QProg.qAssign (parallelMarkingOracle 1
          R))).toStateFun Δ
        set fBranch : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1) := fun v ↦
          let H := swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v
          if 1 ≤ H.card then pulseM1StageLoop res B hQ coldCirc fuel (r - H.card) (T ∪ H)
          else .skip
        unfold pulseM1StageLoop; rw [ite_eq_right hr0, ite_eq_left hsw]; dsimp only
        rw [dite_eq_left hcond]
        change (let prog := (OracleDynamicCircuit.seq (deflateCirc n 1 T cRaw)
              (dispBits res Q 0 fBranch)).compile QProg.qAssign (parallelMarkingOracle 1 S)
            𝔼[(interp prog).toStateFun Δ,
                liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
              expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
                (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (V r))
        dsimp only; rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind,
          interp_deflateCirc n 1 hTS cRaw]; change 𝔼[(interp ((dispBits res Q 0 fBranch).compile
          QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun Δ_att, liftPureProp (fun τ ↦
          decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧ _; refine ⟨?_, ?_⟩
        · rw [expect_dispBits]
          have hterm : ∀ v ∈ Finset.range (2 ^ Q), 𝔼[(interp ((fBranch v).compile QProg.qAssign
            (parallelMarkingOracle 1 S))).toStateFun (sliceState res 0 Q v Δ_att), liftPureProp (fun
            τ ↦ decodeTargetsLocal n k (τ res) = S)] = ((sliceState res 0 Q v Δ_att).trace : ℝ) :=
            by
            intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem; obtain ⟨hsupp_v,
              htr_v⟩ := hslice_att v hv; by_cases hk : keepLoop v = false
            · by_cases hwt0 : wt ⟨v, hv⟩ = 0
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp (by push_cast; rw [htr_v, ite_eq_left hk, hwt0, zero_div,
                    zero_mul])
                rw [expect_eq_zero_of_trace_eq_zero
                  (nonpos_iff_eq_zero.mp (((interp _).trace_toStateFun_le _).trans_eq htr0)),
                  htr0, NNReal.coe_zero]
              · obtain ⟨hH_sub, _⟩ := hsub_wt ⟨v, hv⟩ hwt0
                have hH1 : 1 ≤ (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                have hTU_sub : T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                  Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                have hrem_u : (S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)).card = r -
                  (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  have hsdiff : S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v) = R \
                    swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v :=
                    (by ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]); rw [hsdiff,
                    Finset.card_sdiff_of_subset hH_sub, hrem]
                dsimp only [fBranch]; rw [ite_eq_left hH1]; exact (ih (r - (swLDecodeHarvest n 1 s.L
                  Q hn0 hL2 hQ_sw v).card) (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)
                  (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).1
            · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                NNReal.coe_inj.mp (by push_cast; rw [htr_v, ite_eq_right hk])
              rw [expect_eq_zero_of_trace_eq_zero
                (nonpos_iff_eq_zero.mp (((interp _).trace_toStateFun_le _).trans_eq htr0)),
                htr0, NNReal.coe_zero]
          rw [Finset.sum_congr rfl hterm, ← Fin.sum_univ_eq_sum_range (fun v ↦ ((sliceState res 0 Q
            v Δ_att).trace : ℝ)) (2 ^ Q)]
          have hsum_tr : (∑ o : Fin (2 ^ Q), ((sliceState res 0 Q o.val Δ_att).trace : ℝ)) = ∑ o :
            Fin (2 ^ Q) with keepLoop o.val = false, (wt o / pSucc) * (Δ.trace : ℝ) := by
            rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun o _ ↦ (hslice_att o.val
              o.isLt).2
          rw [hsum_tr, ← Finset.sum_mul, ← Finset.sum_div, div_self hsucc_wt_pos.ne', one_mul]
        · let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)
          rw [expectedCost_qSeq, expectedCost_deflateCirc n 1 hTS hcRaw_zero, interp_deflateCirc n 1
            hTS cRaw]; change expectedCost _ _ Δ + expectedCost model ((dispBits res Q 0
            fBranch).compile QProg.qAssign (parallelMarkingOracle 1 S)) Δ_att ≤ _
          rw [expectedCost_dispBits]
          have hterm_le : ∀ v ∈ Finset.range (2 ^ Q), expectedCost model ((fBranch v).compile
            QProg.qAssign (parallelMarkingOracle 1 S)) (sliceState res 0 Q v Δ_att) ≤ (Δ.trace :
            ℝ≥0∞) * ENNReal.ofReal (if hv : v < 2 ^ Q then if keepLoop v = false then (wt ⟨v, hv⟩ *
            V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) / pSucc else 0 else 0) := by
            intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem; obtain ⟨hsupp_v,
              htr_v⟩ := hslice_att v hv; rw [dite_eq_left hv]; by_cases hk : keepLoop v = false
            · rw [ite_eq_left hk]; by_cases hwt0 : wt ⟨v, hv⟩ = 0
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp (by push_cast; rw [htr_v, ite_eq_left hk, hwt0, zero_div,
                    zero_mul])
                rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0, hwt0, zero_mul, zero_div,
                  ENNReal.ofReal_zero, mul_zero]
              · obtain ⟨hH_sub, _⟩ := hsub_wt ⟨v, hv⟩ hwt0
                have hH1 : 1 ≤ (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                have hTU_sub : T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                  Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                have hrem_u : (S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)).card = r -
                  (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  have hsdiff : S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v) = R \
                    swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v :=
                    (by ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]); rw [hsdiff,
                    Finset.card_sdiff_of_subset hH_sub, hrem]
                dsimp only [fBranch]; rw [ite_eq_left hH1]; have hih := (ih (r - (swLDecodeHarvest n
                  1 s.L Q hn0 hL2 hQ_sw v).card) (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)
                  (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).2; refine hih.trans_eq ?_
                have hdiv_nn : 0 ≤ wt ⟨v, hv⟩ / pSucc := div_nonneg (hwt_nn ⟨v, hv⟩) hsucc_wt_pos.le
                rw [← ENNReal.ofReal_coe_nnreal, htr_v, ite_eq_left hk, ENNReal.ofReal_mul hdiv_nn,
                  mul_comm (ENNReal.ofReal (wt ⟨v, hv⟩ / pSucc)), ENNReal.ofReal_coe_nnreal,
                  mul_assoc, ← ENNReal.ofReal_mul hdiv_nn, div_mul_eq_mul_div]
            · rw [ite_eq_right hk, ENNReal.ofReal_zero, mul_zero]; have htr0 : (sliceState res 0 Q v
                Δ_att).trace = 0 := NNReal.coe_inj.mp (by push_cast; rw [htr_v, ite_eq_right hk])
              rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0]
          have hdisp_le : (∑ v ∈ Finset.range (2 ^ Q), expectedCost model ((fBranch v).compile
            QProg.qAssign (parallelMarkingOracle 1 S)) (sliceState res 0 Q v Δ_att)) ≤ (Δ.trace :
            ℝ≥0∞) * ENNReal.ofReal ((∑ h ∈ Finset.Icc 1 s.L, pHit h * V (r - h)) / pSucc) := by
            refine (Finset.sum_le_sum hterm_le).trans_eq ?_; rw [← Finset.mul_sum]; congr 1
            have hnn : ∀ v ∈ Finset.range (2 ^ Q), 0 ≤ (if hv : v < 2 ^ Q then if keepLoop v = false
              then (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) / pSucc
              else 0 else 0) := by
              intro v _; split_ifs
              · exact div_nonneg (mul_nonneg (hwt_nn _) (hV_nn _ (by omega))) hsucc_wt_pos.le
              · exact le_rfl
              · exact le_rfl
            rw [← ENNReal.ofReal_sum_of_nonneg hnn]; congr 1
            have hfin_eq : (∑ v ∈ Finset.range (2 ^ Q), if hv : v < 2 ^ Q then if keepLoop v = false
              then (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) / pSucc
              else 0 else 0) = ∑ o : Fin (2 ^ Q), if keepLoop o.val = false then (wt o * V (r -
              (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw o.val).card)) / pSucc else 0 := by
              rw [← Fin.sum_univ_eq_sum_range]; refine Finset.sum_congr rfl fun o _ ↦ ?_
              rw [dite_eq_left o.isLt]
            rw [hfin_eq, ← Finset.sum_filter, ← Finset.sum_div]; congr 1; exact hsum_P (fun h ↦ V (r
              - h))
          refine (add_le_add hcost_att hdisp_le).trans ?_; have hcs : ∀ w : Fin s.L, (cs w).1 ^ 2 +
            (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _; have hout_nn : 0 ≤ out.2.2 :=
            (hdistLEvolutionReal_conservation hL2 hcs hpulses).2.2.2; have hatt_nn : 0 ≤ (out.2.2 *
            (K_blk : ℝ) + (s.L : ℝ)) / pSucc := div_nonneg (by positivity) hsucc_wt_pos.le
          have hcont_nn : 0 ≤ (∑ h ∈ Finset.Icc 1 s.L, pHit h * V (r - h)) / pSucc := div_nonneg
            (Finset.sum_nonneg fun h _ ↦ mul_nonneg (swLAttemptProbReal_nonneg hL2 _ _
            (hdistLEvolutionReal_conservation hL2 hcs hpulses).2.1 h) (hV_nn _ (by omega)))
            hsucc_wt_pos.le; rw [← mul_add, ← ENNReal.ofReal_add hatt_nn hcont_nn, ← add_div]
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
          rwa [hpSucc_eq]
      · have hsw_f : B.usePulse r = false := Bool.eq_false_iff.mpr hsw; unfold pulseM1StageLoop;
          rw [ite_eq_right hr0, ite_eq_right hsw]; exact hcold hr1 hr_le hsw_f hScard hTS hrem hΔ
/-- Correctness and expected oracle cost of `pulseM1FromSetWithColdCircuit` (`1152 ≤ n`). -/
theorem pulseM1FromSetWithCold_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var) (B :
    PulseM1CertBundle) {n k r : ℕ} (coldCirc : ℕ → Finset (Fin (2 ^ n)) → OracleDynamicCircuit
    (Unitary (2 ^ findAllQubits n 1 k)) Var (findAllQubits n 1 k) ((n + 1) * 1)) (hn : 1152 ≤ n)
    (hk1 : 1 ≤ k) (hkMax : k ≤ B.kMax) (hr_le : r ≤ k) (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^
    n))}, 1 ≤ r' → r' ≤ k → B.usePulse r' = false → ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k →
    T' ⊆ S' → (S' \ T').card = r' → ∀ {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)},
      SupportedOn (· =
    0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)))
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (pulseM1FromSetWithColdCircuit res B coldCirc r T).compile
      QProg.qAssign (parallelMarkingOracle 1 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) :=
  pulseM1StageLoop_correct_and_cost res B le_rfl coldCirc hn hk1 hkMax hcold r r T le_rfl
    hr_le hScard hTS hrem hΔ
/-- Pure-GMP `m = 1` (`mIdx = 0`) relative-cost cell checker at `10^16` scale. -/
def checkPulseRelCostM1 (kIdx : ℕ) (vTop16 : ℤ) (relNum relDen : ℕ) : Bool :=
  Nat.ble 1 kIdx && Nat.ble kIdx 10 &&
  Nat.ble 1 relNum && Nat.ble 1 relDen &&
  solBleZ 1 vTop16 &&
  solBleZ
    (Int.mul (Int.mul (Int.mul vTop16 (Int.ofNat (swLSqrtMUp12 0))) swUnionScale)
      (Int.ofNat relDen))
    (Int.mul (Int.mul (Int.mul multiUnitScale (Int.ofNat swLPi4Lo12))
      (Int.ofNat (swLHarmPow2 kIdx))) (Int.ofNat relNum))
theorem checkPulseRelCostM1_sound {kIdx : ℕ} {vTop16 : ℤ} {relNum relDen n : ℕ} (hchk :
  checkPulseRelCostM1 kIdx vTop16 relNum relDen = true) : 1 ≤ kIdx ∧ kIdx ≤ 10 ∧ ((vTop16 : ℝ) /
  (multiUnitScale : ℝ)) * √(2 ^ n : ℝ) ≤ ((relNum : ℝ) / (relDen : ℝ)) * ((π / 4) * (∑ r ∈
  Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (1 : ℕ))) := by
  unfold checkPulseRelCostM1 at hchk; simp only [Bool.and_eq_true, natBle_eq_decide,
    solBleZ_eq_decide, decide_eq_true_eq, solIntMul_eq, Int.ofNat_eq_natCast] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hk1, hk10⟩, hrn1⟩, hrd1⟩, hv1⟩, hineq⟩
  have hsc_chk : checkSwLRelCostScaled 0 kIdx vTop16 multiUnitScale relNum relDen = true := by
    unfold checkSwLRelCostScaled; rw [decide_eq_true_eq]; have hmu : (0 : ℤ) < multiUnitScale :=
      (by unfold SchurWeylLCert.multiUnitScale; norm_num)
    exact ⟨by omega, hk10, by omega, hmu, by omega, by omega, by simpa [mul_assoc] using hineq⟩
  have hsnd := checkSwLRelCostScaled_sound (n := n) hsc_chk; refine ⟨hk1, hk10, ?_⟩
  simpa using hsnd
/-- Polymorphic `m = 1` circuit family splicing `PulseM1CertBundle` over an arbitrary
  cold-entry `coldFromSet` fallback (`1152 ≤ n`). -/
noncomputable def pulseOverColdM1Circuit {Var : Type} (res : Var)
    (B : PulseM1CertBundle)
    (coldFromSet : ∀ (n k : ℕ), ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
        (findAllQubits n 1 k) ((n + 1) * 1))
    (n : ℕ) : ∀ (m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | 1, k =>
      if 1152 ≤ n then
        pulseM1FromSetWithColdCircuit res B (coldFromSet n k) k ∅
      else
        findAllCircuit res (fun _ _ _ ↦ 0) n 1 k
  | _, _ => .skip
theorem pulseOverColdM1Circuit_m1 {Var : Type} (res : Var) (B : PulseM1CertBundle) (coldFromSet
  : ∀ (n k : ℕ), ℕ → Finset (Fin (2 ^ n)) → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k))
  Var (findAllQubits n 1 k) ((n + 1) * 1)) (n k : ℕ) : pulseOverColdM1Circuit (Var := Var) res B
  coldFromSet n 1 k = if 1152 ≤ n then pulseM1FromSetWithColdCircuit res B (coldFromSet n k) k ∅
  else findAllCircuit res (fun _ _ _ ↦ 0) n 1 k := rfl
/-- End-to-end `ValidFindAllFamily` bridge for `pulseOverColdM1Circuit`. -/
theorem validFamily_pulseOverColdM1 {Var : Type} [DecidableEq Var] (res : Var) (B :
    PulseM1CertBundle) (coldFromSet : ∀ (n k : ℕ), ℕ → Finset (Fin (2 ^ n)) →
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var (findAllQubits n 1 k) ((n + 1) *
    1)) (hScale : B.vScale = multiUnitScale) (hCold : ∀ {n k r' : ℕ} {T' : Finset (Fin (2 ^ n))},
    1152 ≤ n → 2 ≤ k → k ≤ B.kMax → 1 ≤ r' → r' ≤ k → B.usePulse r' = false → ∀ {S' : Finset
    (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card = r' → ∀ {Δ : CQState (Store Var) (2 ^
    findAllQubits n 1 k)}, SupportedOn (· = 0) Δ →
        let prog := (coldFromSet n k r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)))
    (prof : FindAllCostProfile)
    (hCells : ∀ m k : ℕ, isGridCell m k = true → prof.validCell m k = true →
      m = 1 ∧ 2 ≤ k ∧ k ≤ B.kMax ∧ 1152 ≤ prof.n0 m k ∧
      ∃ kIdx relNum relDen : ℕ,
        k = 2 ^ kIdx ∧
        prof.relCost m k = (relNum : ℚ≥0) / (relDen : ℚ≥0) ∧
        checkPulseRelCostM1 kIdx (B.vTable k) relNum relDen = true) :
    ValidFindAllFamily res prof (pulseOverColdM1Circuit res B coldFromSet) where
  correctness {n m k S} _hn hmk hvalid hkN hS := by
    obtain ⟨rfl, hk2, hkMax, _, _⟩ := hCells m k hmk hvalid; have hScard : S.card = k :=
      (Finset.mem_powersetCard.1 hS).2; by_cases hn1152 : 1152 ≤ n
    · intro Δ; rw [pulseOverColdM1Circuit_m1, ite_eq_left hn1152, expect_top, interp_qSeq,
        QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
      have hcorr := (pulseM1FromSetWithCold_correct_and_cost res B (coldFromSet n k) hn1152
        (by omega) hkMax le_rfl (fun {r'} {T'} hr1' hrk' huf {S'} hS' hTS' hrem' {Δ'} hΔ' ↦ hCold
        hn1152 hk2 hkMax hr1' hrk' huf hS' hTS' hrem' hΔ') hScard (Finset.empty_subset S)
        (by simpa using hScard) hsupp).1
      exact (hcorr.trans (congrArg NNReal.toReal (CQState.trace_qSet Δ))).symm.le
    · rw [pulseOverColdM1Circuit_m1, ite_eq_right hn1152]
      exact findAllProgram_correctness res (fun _ _ _ ↦ 0) le_rfl hScard hkN (fun r hr1 hrk ↦
        p_succ_set_zero_pos hr1 (hrk.trans hkN))
  costBound_uniform {m k} hmk hvalid n hn0 hkN := by
    obtain ⟨rfl, hk2, hkMax, hn0_cond, kIdx, relNum, relDen, hk_pow, hrel_eq, hcell⟩ := hCells m k
      hmk hvalid; have hn1152 : 1152 ≤ n := hn0_cond.trans hn0; have hv_nn : (0 : ℝ) ≤ (B.vTable k :
      ℝ) := (by exact_mod_cast B.hNonneg k hkMax); have hmu_pos : (0 : ℝ) < (multiUnitScale : ℝ) :=
      (by unfold SchurWeylLCert.multiUnitScale; norm_num); set cVal : ℝ := ((B.vTable k : ℝ) /
      (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
    let cNN : ℝ≥0 := ⟨cVal, by dsimp [cVal]; positivity⟩; refine ⟨fun _ ↦ cNN, ?_, ?_⟩
    · intro S hS Δ; have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2
      rw [pulseOverColdM1Circuit_m1, ite_eq_left hn1152, expectedCost_qSeq, expectedCost_qSet,
        CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero, mul_zero, zero_add, interp_qSet,
        QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
      have hmass_eq : (Δ.qSet.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
      have hcb := (pulseM1FromSetWithCold_correct_and_cost res B (coldFromSet n k) hn1152
        (by omega) hkMax le_rfl (fun {r'} {T'} hr1' hrk' huf {S'} hS' hTS' hrem' {Δ'} hΔ' ↦ hCold
        hn1152 hk2 hkMax hr1' hrk' huf hS' hTS' hrem' hΔ') hScard (Finset.empty_subset S)
        (by simpa using hScard) hsupp).2; rw [hmass_eq, hScale] at hcb; have hcNN : ((cNN : ℝ≥0) :
        ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
      dsimp only; rw [hcNN]; exact hcb
    · have hcard_pos : 0 < ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; exact Nat.choose_pos hkN
      have hcard_r : (0 : ℝ) < (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card : ℝ) :=
        Nat.cast_pos.2 hcard_pos; rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _
        hcard_r.ne', hrel_eq]; change cVal ≤ (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) * ((π /
        4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (1 : ℕ)))
      have hrel_cast : (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) = (relNum : ℝ) / (relDen : ℝ)
        := (by push_cast; rfl); rw [hrel_cast, hk_pow]; exact (checkPulseRelCostM1_sound (n := n)
        hcell).2.2
/-- Bundle adapter forcing `usePulse 1 = false` for `lockSingleFromSetCircuit` (`r = 1`). -/
def pulseBundleWithR1Cold (B : PulseM1CertBundle) : PulseM1CertBundle where
  kMax := B.kMax
  vScale := B.vScale
  vTable := B.vTable
  usePulse := fun r ↦ if r = 1 then false else B.usePulse r
  stageOfR := B.stageOfR
  hKMax := B.hKMax
  hScalePos := B.hScalePos
  hV0 := B.hV0
  hNonneg := B.hNonneg
  hStageSound {n r} hn hr1 hrMax huse := by
    have hr_ne1 : r ≠ 1 := by intro h1; subst h1; simp at huse
    simp only [hr_ne1, ↓reduceIte] at huse
    exact B.hStageSound hn hr1 hrMax huse
/-- Standalone `m = 1` multi-pulse circuit routing `r = 1` to `lockSingleFromSetCircuit`. -/
noncomputable def pulseStandaloneM1Circuit {Var : Type} (res : Var)
    (B : PulseM1CertBundle) : ∀ (n m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  pulseOverColdM1Circuit res (pulseBundleWithR1Cold B)
    (fun n k _ T ↦ lockSingleFromSetCircuit res n 1 k T)
/-- End-to-end `ValidFindAllFamily` theorem for standalone 21-stage
  `pulseStandaloneM1Circuit`. -/
theorem validFamily_pulseStandaloneM1 {Var : Type} [DecidableEq Var] (res : Var) (B :
  PulseM1CertBundle) (hScale : B.vScale = multiUnitScale) (hUse : ∀ r, 2 ≤ r → r ≤ B.kMax →
  B.usePulse r = true) (hV1 : (6426990820000000 : ℤ) ≤ B.vTable 1) (prof : FindAllCostProfile)
  (hCells : ∀ m k : ℕ, isGridCell m k = true → prof.validCell m k = true → m = 1 ∧ 2 ≤ k ∧ k ≤
  B.kMax ∧ 1152 ≤ prof.n0 m k ∧ ∃ kIdx relNum relDen : ℕ, k = 2 ^ kIdx ∧ prof.relCost m k = (relNum
  : ℚ≥0) / (relDen : ℚ≥0) ∧ checkPulseRelCostM1 kIdx (B.vTable k) relNum relDen = true) :
  ValidFindAllFamily res prof (pulseStandaloneM1Circuit res B) := by
  refine validFamily_pulseOverColdM1 res (pulseBundleWithR1Cold B) (fun n k _ T ↦
    lockSingleFromSetCircuit res n 1 k T) hScale ?_ prof hCells
  intro n k r' T' hn1152 _hk2 hkMax hr1' hrk' huse_f S' hS' hT'S' hrem' Δ' hΔ'
  have hr'_eq1 : r' = 1 := by
    by_contra hne1; have htr := hUse r' (by omega) (hrk'.trans hkMax)
    simp [pulseBundleWithR1Cold, hne1, htr] at huse_f
  subst hr'_eq1; have hk1024 : k ≤ 1024 := hkMax.trans B.hKMax; have hrem_sub : k - T'.card = 1 :=
    (by have hs := Finset.card_sdiff_of_subset hT'S'; omega)
  obtain ⟨hexp, hcost⟩ := lockSingleFromSet_transition res (by omega : 100 ≤ n) le_rfl
    (by norm_num) hk1024 hS' hT'S' hrem_sub hΔ'; refine ⟨hexp, hcost.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
  simp only [pulseBundleWithR1Cold, Nat.cast_one, div_one]; rw [hScale]
  have hrel : ((relCostLock : ℚ≥0) : ℝ) = (4091549431 : ℝ) / 5000000000 :=
    (by unfold relCostLock; push_cast; norm_num); have hmu_eq : (multiUnitScale : ℝ) =
    10000000000000000 := (by unfold SchurWeylLCert.multiUnitScale; norm_num); have hpi : π <
    3.14159265359 := Real.pi_lt_d20.trans (by norm_num); have hv1_r : (6426990820000000 : ℝ) ≤
    (B.vTable 1 : ℝ) := (by exact_mod_cast hV1)
  have hcoef : ((relCostLock : ℚ≥0) : ℝ) * (π / 4) ≤ (B.vTable 1 : ℝ) / (multiUnitScale : ℝ) :=
    (by rw [hrel, hmu_eq]; linarith); exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
end PulseM1
end QuantumComputation.Specs.GroverFindAll
