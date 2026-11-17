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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Nuc47KpBasis9AlwaysLo

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 8192
set_option Elab.async false
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances

open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW mkKetOpW_congr
    mkKetOpW_mulVec_ket leg_if_pos leg_if_neg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
    (DynWires circWires_inverse)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoinWrap (xagEnv)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec (mkFin3 mkFin187
    mkFin234)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Cartesian254 (b2Spec b6Spec b11Z2OfHX
    cart254V23)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708 (gatesTier1K3708At)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine (beqPair gatesWfCheck
    wBit_eq_of_prefix wPack_eq_of_prefix wBit_const1_gen wBit_coin_gen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine (oddBits_eq_wBit_gen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires)
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1MaskEngine

set_option exponentiation.threshold 256

/-! ## Section 1: GMP-Safe Mask Decoding & Bit-Parity Algebra -/

/-- Decode a `ℕ` bitmask `m` stored as `2 * m + 1` so its low 64-bit limb is always nonzero. -/
abbrev oddMask (p : ℕ) : ℕ := p >>> 1

/-- Select `x` when `b = true` and `y` when `b = false` in balanced lookup trees. -/
abbrev muxPair {α : Type*} (b : Bool) (x y : α) : α := if b then x else y

/-- Pure `Bool` bit-count parity over bits `0 .. n - 1` of `x : ℕ`. -/
def oddBits (x : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => xor (oddBits x n) (x.testBit n)

/-- Pure `Bool` parity of `f j` over indices `j < n` selected by `m.testBit j`. -/
def xorMaskBool (f : ℕ → Bool) (m : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 =>
      let prev := xorMaskBool f m n
      if m.testBit n then xor prev (f n) else prev

theorem oddBits_zero : ∀ n : ℕ, oddBits 0 n = false
  | 0 => rfl
  | n + 1 => by simp [oddBits, oddBits_zero n]

theorem oddBits_congr_low (x y : ℕ) :
    ∀ (n : ℕ), (∀ i < n, x.testBit i = y.testBit i) → oddBits x n = oddBits y n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [oddBits, oddBits_congr_low x y n (fun i hi ↦ h i (Nat.lt_succ_of_lt hi)),
        h n (Nat.lt_succ_self n)]

theorem oddBits_xor : ∀ (a b n : ℕ), oddBits (a ^^^ b) n = xor (oddBits a n) (oddBits b n)
  | _, _, 0 => rfl
  | a, b, n + 1 => by
      simp only [oddBits, Nat.testBit_xor, oddBits_xor a b n]
      cases oddBits a n <;> cases oddBits b n <;> cases a.testBit n <;> cases b.testBit n <;> rfl

theorem nat_and_xor_distrib (e a b : ℕ) : e &&& (a ^^^ b) = (e &&& a) ^^^ (e &&& b) :=
  Nat.eq_of_testBit_eq fun i ↦ by
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases e.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl

theorem oddBits_and_xor (e a b n : ℕ) :
    oddBits (e &&& (a ^^^ b)) n = xor (oddBits (e &&& a) n) (oddBits (e &&& b) n) := by
  rw [nat_and_xor_distrib, oddBits_xor]

theorem oddBits_eq_of_above_false :
    ∀ (x m n : ℕ), m ≤ n → (∀ i, m ≤ i → i < n → x.testBit i = false) → oddBits x n = oddBits x m
  | _, m, 0, hm, _ => by rw [Nat.eq_zero_of_le_zero hm]
  | x, m, n + 1, hm, hf => by
      by_cases hmn : m = n + 1
      · rw [hmn]
      · simp only [oddBits, hf n (by omega) (Nat.lt_succ_self n), Bool.xor_false]
        exact oddBits_eq_of_above_false x m n (by omega) fun i h1 h2 ↦
            hf i h1 (Nat.lt_succ_of_lt h2)

theorem testBit_and_lt_two_pow {e mask m i : ℕ} (h : mask < 2 ^ m) (hi : m ≤ i) :
    (e &&& mask).testBit i = false := by
  rw [Nat.testBit_and,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi)),
    Bool.and_false]

theorem oddBits_and_eq_of_lt_two_pow {e mask m n : ℕ} (h : mask < 2 ^ m) (hmn : m ≤ n) :
    oddBits (e &&& mask) n = oddBits (e &&& mask) m :=
  oddBits_eq_of_above_false (e &&& mask) m n hmn fun _ hi _ ↦ testBit_and_lt_two_pow h hi

theorem testBit_one_shiftLeft (b i : ℕ) : (1 <<< b).testBit i = decide (b = i) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem oddBits_single_bit_le (e b : ℕ) :
    ∀ (m : ℕ), m ≤ b → oddBits (e &&& (1 <<< b)) m = false
  | 0, _ => rfl
  | m + 1, hm => by
      simp only [oddBits, oddBits_single_bit_le e b m (Nat.le_of_succ_le hm), Bool.false_xor,
        Nat.testBit_and, testBit_one_shiftLeft, decide_eq_false (by omega : ¬ b = m),
            Bool.and_false]

theorem oddBits_single_bit :
    ∀ (e b n : ℕ), b < n → oddBits (e &&& (1 <<< b)) n = e.testBit b
  | _, _, 0, hb => absurd hb (Nat.not_lt_zero _)
  | e, b, n + 1, hb => by
      by_cases hbn : b = n
      · subst hbn
        simp only [oddBits, oddBits_single_bit_le e b b le_rfl, Bool.false_xor,
          Nat.testBit_and, testBit_one_shiftLeft, decide_true, Bool.and_true]
      · simp only [oddBits, oddBits_single_bit e b n (by omega), Nat.testBit_and,
          testBit_one_shiftLeft, decide_eq_false hbn, Bool.and_false, Bool.xor_false]

/-! ## Section 2: Universal Subspace Coordinate XAG & Router Certifier -/

/-- Pack `f 0, ..., f (k - 1)` into the low `k` bits of a `ℕ`. -/
def packBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => packBits f k ||| (if f k then 1 <<< k else 0)

theorem packBits_lt_two_pow (f : ℕ → Bool) : ∀ k : ℕ, packBits f k < 2 ^ k
  | 0 => by
      dsimp only [packBits]
      decide
  | k + 1 => by
      have hk : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self k)
      have ih := Nat.lt_trans (packBits_lt_two_pow f k) hk
      dsimp only [packBits]
      split_ifs
      · rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.or_lt_two_pow ih hk
      · simpa using ih

theorem testBit_packBits (f : ℕ → Bool) :
    ∀ (k i : ℕ), (packBits f k).testBit i = (if i < k then f i else false)
  | 0, _ => by simp [packBits]
  | k + 1, i => by
      dsimp only [packBits]
      rw [Nat.testBit_or, testBit_packBits f k i]
      by_cases hik : i < k
      · cases f k <;> simp [hik, Nat.lt_succ_of_lt hik]
      · by_cases hieq : i = k
        · subst hieq
          cases hfi : f i
          · simp
          · simp
        · rw [ite_eq_right hik, ite_eq_right (show ¬ i < k + 1 by omega), Bool.false_or]
          cases f k
          · rw [ite_eq_right Bool.false_ne_true, Nat.zero_testBit]
          · rw [ite_eq_left rfl, testBit_one_shiftLeft, decide_eq_false (Ne.symm hieq)]

/-- Packed `(K + E)`-bit coordinate state of `env` over linear `basis` and gate indices `exp`. -/
def envSt (basis exp : List ℕ) (env : ℕ) : ℕ :=
  packBits (fun i ↦
    if i < basis.length then oddBits (env &&& basis.getD i 0) 181
    else env.testBit (42 + exp.getD (i - basis.length) 0)) (basis.length + exp.length)

/-- Fold XOR of `f k` over `k < n` selected by `comb.testBit k`. -/
def reconMaskAux (f : ℕ → ℕ) (comb : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => reconMaskAux f comb n ^^^ (if comb.testBit n then f n else 0)

/-- Reconstruct an environment mask from constant bit `c0` and `(K + E)`-bit `comb`. -/
def reconMask (basis exp : List ℕ) (c0 : Bool) (comb : ℕ) : ℕ :=
  (if c0 then 1 else 0) ^^^
    reconMaskAux (fun i ↦
      if i < basis.length then basis.getD i 0
      else 1 <<< (42 + exp.getD (i - basis.length) 0)) comb (basis.length + exp.length)

theorem reconMaskAux_oddBits {basis exp : List ℕ} {env : ℕ}
    (hexp : ∀ i < exp.length, exp.getD i 0 < 139) (comb : ℕ) :
    ∀ (m : ℕ), m ≤ basis.length + exp.length →
      oddBits (envSt basis exp env &&& comb) m =
        oddBits (env &&& reconMaskAux (fun i ↦
          if i < basis.length then basis.getD i 0
          else 1 <<< (42 + exp.getD (i - basis.length) 0)) comb m) 181
  | 0, _ => by
      change false = oddBits (env &&& 0) 181
      rw [Nat.and_zero, oddBits_zero]
  | m + 1, hm => by
      dsimp only [reconMaskAux]
      rw [show oddBits (envSt basis exp env &&& comb) (m + 1) =
            xor (oddBits (envSt basis exp env &&& comb) m)
              ((envSt basis exp env &&& comb).testBit m) from rfl,
          oddBits_and_xor, reconMaskAux_oddBits hexp comb m (Nat.le_of_succ_le hm)]
      have hBit : (envSt basis exp env &&& comb).testBit m =
          oddBits (env &&& (if comb.testBit m then
            if m < basis.length then basis.getD m 0
            else 1 <<< (42 + exp.getD (m - basis.length) 0) else 0)) 181 := by
        dsimp only [envSt]
        rw [Nat.testBit_and, testBit_packBits,
            ite_eq_left (show m < basis.length + exp.length by omega)]
        cases comb.testBit m
        · rw [Bool.and_false, ite_eq_right Bool.false_ne_true, Nat.and_zero, oddBits_zero]
        · rw [Bool.and_true, ite_eq_left rfl]
          by_cases hb : m < basis.length
          · rw [ite_eq_left hb, ite_eq_left hb]
          · rw [ite_eq_right hb, ite_eq_right hb]
            have hg := hexp (m - basis.length) (by omega)
            exact (oddBits_single_bit env (42 + exp.getD (m - basis.length) 0) 181
              (by omega)).symm
      rw [hBit]

theorem reconMask_oddBits {basis exp : List ℕ} {env : ℕ}
    (h0 : env.testBit 0 = true) (hexp : ∀ i < exp.length, exp.getD i 0 < 139)
    (c0 : Bool) (comb : ℕ) :
    xor c0 (oddBits (envSt basis exp env &&& comb) (basis.length + exp.length)) =
      oddBits (env &&& reconMask basis exp c0 comb) 181 := by
  dsimp only [reconMask]
  rw [oddBits_and_xor, reconMaskAux_oddBits hexp comb (basis.length + exp.length) le_rfl]
  cases c0
  · rw [ite_eq_right Bool.false_ne_true, Nat.and_zero, oddBits_zero]
  · rw [ite_eq_left rfl, show (1 : ℕ) = 1 <<< 0 from rfl,
        oddBits_single_bit env 0 181 (by omega), h0]

/-- Build `(ones, cols)` truth-table bitvectors for `k` independent Boolean coordinates. -/
def initCols : ℕ → ℕ × List ℕ
  | 0 => (1, [])
  | k + 1 =>
      let p := initCols k
      let ones := p.1
      let sh := 1 <<< k
      (ones ||| (ones <<< sh), p.2.map (fun c ↦ c ||| (c <<< sh)) ++ [ones <<< sh])

theorem initCols_length : ∀ k : ℕ, (initCols k).2.length = k
  | 0 => rfl
  | k + 1 => by simp [initCols, initCols_length k]

theorem initCols_ones_bit : ∀ (k z : ℕ), ((initCols k).1).testBit z = decide (z < 2 ^ k)
  | 0, 0 => rfl
  | 0, k + 1 => by
      dsimp only [initCols]
      rw [decide_eq_false (by omega : ¬ (k + 1 < 2 ^ 0))]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
          (Nat.pow_le_pow_right (by omega) (by omega)))
  | k + 1, z => by
      dsimp only [initCols]
      have hsh : (1 <<< k) = 2 ^ k := by rw [Nat.shiftLeft_eq, one_mul]
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
      rw [hsh, Nat.testBit_or, Nat.testBit_shiftLeft, initCols_ones_bit k z,
          initCols_ones_bit k (z - 2 ^ k)]
      by_cases h1 : z < 2 ^ k <;> by_cases h2 : z < 2 ^ (k + 1) <;> simp [h1, h2] <;> try omega

theorem getD_append_singleton : ∀ (l : List ℕ) (x i : ℕ),
    (l ++ [x]).getD i 0 = if i < l.length then l.getD i 0 else if i = l.length then x else 0
  | [], _, 0 => rfl
  | [], _, _ + 1 => rfl
  | _ :: _, _, 0 => by simp
  | _ :: l, x, i + 1 => by
      simp only [List.cons_append, List.length_cons, List.getD_cons_succ,
          getD_append_singleton l x i]
      rcases (show i < l.length ∨ i = l.length ∨ l.length < i by omega) with h | rfl | h
      · simp [h, Nat.succ_lt_succ h]
      · simp
      · simp [show ¬ i < l.length by omega, Nat.ne_of_gt h, show ¬ i + 1 < l.length + 1 by omega]

theorem getD_map_zero (f : ℕ → ℕ) (hf : f 0 = 0) :
    ∀ (l : List ℕ) (i : ℕ), (l.map f).getD i 0 = f (l.getD i 0)
  | [], _ => by simp [hf]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map_zero f hf l i

theorem initCols_col_bit : ∀ (k i z : ℕ), i < k →
    ((initCols k).2.getD i 0).testBit z = (decide (z < 2 ^ k) && z.testBit i)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, z, hi => by
      dsimp only [initCols]
      have hsh : (1 <<< k) = 2 ^ k := by rw [Nat.shiftLeft_eq, one_mul]
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
      rw [hsh, getD_append_singleton, List.length_map, initCols_length]
      by_cases hik : i < k
      · rw [ite_eq_left hik, getD_map_zero _ (by simp), Nat.testBit_or, Nat.testBit_shiftLeft,
            initCols_col_bit k i z hik, initCols_col_bit k i (z - 2 ^ k) hik]
        by_cases hz1 : z < 2 ^ k
        · simp [hz1, show ¬ z ≥ 2 ^ k by omega, show z < 2 ^ (k + 1) by omega]
        · by_cases hz2 : z < 2 ^ (k + 1)
          · have hg : z ≥ 2 ^ k := by omega
            have hm1 := Nat.testBit_mod_two_pow z k i
            have hm2 := Nat.testBit_mod_two_pow (z - 2 ^ k) k i
            rw [decide_eq_true hik, Bool.true_and] at hm1 hm2
            have hbit : (z - 2 ^ k).testBit i = z.testBit i := by
              rw [← hm1, ← hm2, Nat.mod_eq_sub_mod hg]
            simp [hz1, hz2, hg, show z - 2 ^ k < 2 ^ k by omega, hbit]
          · simp [hz1, hz2, show z ≥ 2 ^ k by omega, show ¬ z - 2 ^ k < 2 ^ k by omega]
      · have heq : i = k := by omega
        subst heq
        rw [ite_eq_right hik, ite_eq_left rfl, Nat.testBit_shiftLeft, initCols_ones_bit i (z - 2 ^
            i)]
        by_cases hz1 : z < 2 ^ i
        · simp [show ¬ z ≥ 2 ^ i by omega, Nat.testBit_lt_two_pow hz1]
        · by_cases hz2 : z < 2 ^ (i + 1)
          · have hg : z ≥ 2 ^ i := by omega
            have hsub : z - 2 ^ i < 2 ^ i := by omega
            have hbt : z.testBit i = true := by
              rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_sub_div (Nat.two_pow_pos i) hg,
                  Nat.div_eq_of_lt hsub]
              rfl
            simp [hz2, hg, hsub, hbt]
          · simp [hz2, show z ≥ 2 ^ i by omega, show ¬ z - 2 ^ i < 2 ^ i by omega]

/-- Fold bitwise XOR of `cols` entries below `n` selected by bitmask `m`. -/
def xorMaskedColsAux (cols : List ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      let prev := xorMaskedColsAux cols m n
      if m.testBit n then prev ^^^ cols.getD n 0 else prev

/-- Evaluate an affine coordinate `(c0, mask)` as a `2 ^ K` truth-table bitvector. -/
def evalCoordVec (ones : ℕ) (cols : List ℕ) (n : ℕ) (cd : Bool × ℕ) : ℕ :=
  let v := xorMaskedColsAux cols cd.2 n
  if cd.1 then ones ^^^ v else v

/-- Vectorized truth-table simulator for `AND`-gate coordinate pairs `gcs`. -/
def simVecIdx : ℕ → ℕ → List ℕ → List ((Bool × ℕ) × (Bool × ℕ)) → List ℕ
  | _, _, cols, [] => cols
  | idx, ones, cols, gc :: rest =>
      let vL := evalCoordVec ones cols idx gc.1
      let vR := evalCoordVec ones cols idx gc.2
      simVecIdx (idx + 1) ones (cols ++ [vL &&& vR]) rest

theorem testBit_xorMaskedColsAux (cols : List ℕ) (f : ℕ → Bool) (m z M : ℕ) :
    ∀ (n : ℕ), n ≤ M → (∀ i < n, (cols.getD i 0).testBit z = f i) →
      (xorMaskedColsAux cols m n).testBit z = oddBits (packBits f M &&& m) n
  | 0, _, _ => by simp [xorMaskedColsAux, oddBits]
  | n + 1, hn, hf => by
      dsimp only [xorMaskedColsAux]
      rw [oddBits, Nat.testBit_and, testBit_packBits, ite_eq_left (show n < M from hn)]
      have ih := testBit_xorMaskedColsAux cols f m z M n (Nat.le_of_succ_le hn)
        fun i hi ↦ hf i (Nat.lt_succ_of_lt hi)
      cases hm : m.testBit n <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true, Bool.xor_false,
            Nat.testBit_xor, ih, hf n (Nat.lt_succ_self n)]

theorem testBit_evalCoordVec (ones : ℕ) (cols : List ℕ) (f : ℕ → Bool) (z M n : ℕ)
    (cd : Bool × ℕ) (hOnes : ones.testBit z = true) (hn : n ≤ M)
    (hf : ∀ i < n, (cols.getD i 0).testBit z = f i) :
    (evalCoordVec ones cols n cd).testBit z = xor cd.1 (oddBits (packBits f M &&& cd.2) n) := by
  dsimp only [evalCoordVec]
  rw [← testBit_xorMaskedColsAux cols f cd.2 z M n hn hf]
  cases cd.1 <;> simp [Nat.testBit_xor, hOnes]

theorem list_drop_eq_getD_cons : ∀ (l : List ((Bool × ℕ) × (Bool × ℕ))) (e : ℕ),
    e < l.length → l.drop e = l.getD e ((false, 0), (false, 0)) :: l.drop (e + 1)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: xs, e + 1, h => list_drop_eq_getD_cons xs e (Nat.lt_of_succ_lt_succ h)

/-- Verify that `gcs` reconstructs the input masks of every gate in `exp` over `(basis, exp)`. -/
def checkCert (gates : ℕ → ℕ × ℕ) (basis exp : List ℕ)
    (gcs : List ((Bool × ℕ) × (Bool × ℕ))) : Bool :=
  let K := basis.length
  let E := exp.length
  (gcs.length == E) &&
  (List.range E).all fun e ↦
    let g := exp.getD e 0
    let gc := gcs.getD e ((false, 0), (false, 0))
    let p := gates g
    decide (g < 139) &&
    decide (gc.1.2 < 2 ^ (K + e)) &&
    decide (gc.2.2 < 2 ^ (K + e)) &&
    decide (p.1 < 2 ^ (42 + g)) &&
    decide (p.2 < 2 ^ (42 + g)) &&
    decide (reconMask basis exp gc.1.1 gc.1.2 = p.1) &&
    decide (reconMask basis exp gc.2.1 gc.2.2 = p.2)

theorem checkCert_exp_lt_w5 {gates : ℕ → ℕ × ℕ} {basis exp : List ℕ}
    {gcs : List ((Bool × ℕ) × (Bool × ℕ))}
    (hCert : checkCert gates basis exp gcs = true) :
    ∀ i < exp.length, exp.getD i 0 < 139 := fun i hi ↦ by
  have hiB := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hCert).2) i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hiB
  exact hiB.1.1.1.1.1.1

/-- Pointwise evaluation of coordinate `(c0, mask)` on packed state `st`. -/
def evalCoord (K E : ℕ) (st : ℕ) (c : Bool × ℕ) : Bool :=
  xor c.1 (oddBits (st &&& c.2) (K + E))

theorem simVecIdx_inv {gates : ℕ → ℕ × ℕ} {basis exp : List ℕ}
    {gcs : List ((Bool × ℕ) × (Bool × ℕ))} {env ones z0 : ℕ}
    (hCert : checkCert gates basis exp gcs = true)
    (h0 : env.testBit 0 = true)
    (hOnes : ones.testBit z0 = true)
    (hGates : ∀ e < exp.length,
      let g := exp.getD e 0
      env.testBit (42 + g) =
        (oddBits (env &&& (gates g).1) (42 + g) && oddBits (env &&& (gates g).2) (42 + g))) :
    ∀ (d e : ℕ), e + d = exp.length → ∀ (cols : List ℕ),
      cols.length = basis.length + e →
      (∀ i < basis.length + e,
        (cols.getD i 0).testBit z0 =
          (if i < basis.length then oddBits (env &&& basis.getD i 0) 181
           else env.testBit (42 + exp.getD (i - basis.length) 0))) →
      ∀ i < basis.length + exp.length,
        ((simVecIdx (basis.length + e) ones cols (gcs.drop e)).getD i 0).testBit z0 =
          (if i < basis.length then oddBits (env &&& basis.getD i 0) 181
           else env.testBit (42 + exp.getD (i - basis.length) 0))
  | 0, e, hed, cols, _, hcols => by
      have hLenEq := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hCert).1
      have heEq : e = exp.length := by omega
      subst heEq
      rw [List.drop_eq_nil_of_le (by omega : gcs.length ≤ exp.length)]
      exact hcols
  | d + 1, e, hed, cols, hlen, hcols => by
      obtain ⟨hLenB, hAllB⟩ := Bool.and_eq_true_iff.mp hCert
      have hLenEq := beq_iff_eq.mp hLenB
      have hAll := List.all_eq_true.mp hAllB
      have he : e < exp.length := by omega
      have hexp := checkCert_exp_lt_w5 hCert
      have hg := hexp e he
      have heB := hAll e (List.mem_range.mpr he)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at heB
      rcases heB with ⟨⟨⟨⟨⟨⟨_, hmL⟩, hmR⟩, hp1⟩, hp2⟩, hr1⟩, hr2⟩
      rw [list_drop_eq_getD_cons gcs e (by omega)]
      dsimp only [simVecIdx]
      let gc := gcs.getD e ((false, 0), (false, 0))
      have hv : ∀ (cd : Bool × ℕ) (gm : ℕ), cd.2 < 2 ^ (basis.length + e) →
          gm < 2 ^ (42 + exp.getD e 0) → reconMask basis exp cd.1 cd.2 = gm →
          (evalCoordVec ones cols (basis.length + e) cd).testBit z0 =
            oddBits (env &&& gm) (42 + exp.getD e 0) := fun cd gm hm hp hr ↦ by
        rw [testBit_evalCoordVec ones cols
            (fun i ↦ if i < basis.length then oddBits (env &&& basis.getD i 0) 181
                     else env.testBit (42 + exp.getD (i - basis.length) 0))
            z0 (basis.length + exp.length) (basis.length + e) cd hOnes (by omega) hcols]
        change xor cd.1 (oddBits (envSt basis exp env &&& cd.2) (basis.length + e)) = _
        rw [← oddBits_and_eq_of_lt_two_pow (n := basis.length + exp.length) hm (by omega),
            reconMask_oddBits h0 hexp, hr, oddBits_and_eq_of_lt_two_pow hp (by omega)]
      rw [show (basis.length + e) + 1 = basis.length + (e + 1) by omega]
      refine simVecIdx_inv hCert h0 hOnes hGates d (e + 1) (by omega)
        (cols ++ [evalCoordVec ones cols (basis.length + e) gc.1 &&&
                  evalCoordVec ones cols (basis.length + e) gc.2])
                      (by rw [List.length_append, List.length_singleton, hlen, Nat.add_assoc]) fun i
                      hi ↦ ?_
      rw [getD_append_singleton, hlen]
      by_cases hiLt : i < basis.length + e
      · rw [ite_eq_left hiLt]
        exact hcols i hiLt
      · obtain rfl : i = basis.length + e := by omega
        rw [ite_eq_right hiLt, ite_eq_left rfl, Nat.testBit_and, hv gc.1 _ hmL hp1 hr1, hv gc.2 _
            hmR hp2 hr2,
            ← hGates e he, ite_eq_right (by omega : ¬ (basis.length + e < basis.length)),
                Nat.add_sub_cancel_left]

theorem simVecIdx_evalCoord_eq {gates : ℕ → ℕ × ℕ} {basis exp : List ℕ}
    {gcs : List ((Bool × ℕ) × (Bool × ℕ))} {env : ℕ}
    (hCert : checkCert gates basis exp gcs = true)
    (h0 : env.testBit 0 = true)
    (hGates : ∀ e < exp.length,
      let g := exp.getD e 0
      env.testBit (42 + g) =
        (oddBits (env &&& (gates g).1) (42 + g) && oddBits (env &&& (gates g).2) (42 + g))) :
    let z0 := packBits (fun i ↦ oddBits (env &&& basis.getD i 0) 181) basis.length
    let p := initCols basis.length
    let cols := simVecIdx basis.length p.1 p.2 gcs
    p.1.testBit z0 = true ∧ ∀ cd : Bool × ℕ,
      (evalCoordVec p.1 cols (basis.length + exp.length) cd).testBit z0 =
        evalCoord basis.length exp.length (envSt basis exp env) cd := by
  let z0 := packBits (fun i ↦ oddBits (env &&& basis.getD i 0) 181) basis.length
  have hz0 : z0 < 2 ^ basis.length := packBits_lt_two_pow _ basis.length
  have hOnes : (initCols basis.length).1.testBit z0 = true := by
    rw [initCols_ones_bit, decide_eq_true hz0]
  have hCols := simVecIdx_inv hCert h0 hOnes hGates exp.length 0 (by omega)
    (initCols basis.length).2 (by rw [initCols_length, Nat.add_zero]) fun i hi ↦ by
      rw [Nat.add_zero] at hi
      rw [initCols_col_bit basis.length i z0 hi, decide_eq_true hz0, Bool.true_and,
        testBit_packBits, ite_eq_left hi, ite_eq_left hi]
  simp only [Nat.add_zero, List.drop_zero] at hCols
  exact ⟨hOnes, fun cd ↦ testBit_evalCoordVec (initCols basis.length).1 _
    (fun i ↦ if i < basis.length then oddBits (env &&& basis.getD i 0) 181
             else env.testBit (42 + exp.getD (i - basis.length) 0))
    z0 (basis.length + exp.length) (basis.length + exp.length) cd hOnes le_rfl hCols⟩

/-- Vectorized truth-table check that coordinates `c0` and `c1` are never simultaneously `1`. -/
def checkDisjVec (K E : ℕ) (gcs : List ((Bool × ℕ) × (Bool × ℕ))) (c0 c1 : Bool × ℕ) : Bool :=
  let p := initCols K
  let cols := simVecIdx K p.1 p.2 gcs
  let v0 := evalCoordVec p.1 cols (K + E) c0
  let v1 := evalCoordVec p.1 cols (K + E) c1
  ((v0 &&& v1) &&& p.1) == 0

/-- Fold bitwise XOR of `evalCoordVec` over branch coordinates `lCs` selected by `mh`. -/
def evalMaskedCoordsVec (ones : ℕ) (cols : List ℕ) (n : ℕ)
    (lCs : List (Bool × ℕ)) (mh : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      let prev := evalMaskedCoordsVec ones cols n lCs mh j
      if mh.testBit j then prev ^^^ evalCoordVec ones cols n (lCs.getD j (false, 0)) else prev

theorem testBit_evalMaskedCoordsVec (ones : ℕ) (cols : List ℕ) (n : ℕ)
    (lCs : List (Bool × ℕ)) (mh z : ℕ) (f : ℕ → Bool) :
    ∀ (k : ℕ), (∀ j < k, (evalCoordVec ones cols n (lCs.getD j (false, 0))).testBit z = f j) →
      (evalMaskedCoordsVec ones cols n lCs mh k).testBit z = xorMaskBool f mh k
  | 0, _ => by simp [evalMaskedCoordsVec, xorMaskBool]
  | j + 1, hf => by
      dsimp only [evalMaskedCoordsVec, xorMaskBool]
      have ih := testBit_evalMaskedCoordsVec ones cols n lCs mh z f j fun i hi ↦
          hf i (Nat.lt_succ_of_lt hi)
      cases hm : mh.testBit j <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_xor, ih, hf j (Nat.lt_succ_self j)]

/-- Vectorized truth-table check of `l`-disjointness and gates for an `R`-branch router. -/
def checkRouterVec (K E R : ℕ) (maskHs : List ℕ) (gcs : List ((Bool × ℕ) × (Bool × ℕ)))
    (uC : Bool × ℕ) (lCs yCs : List (Bool × ℕ))
    (rgCs : List ((Bool × ℕ) × (Bool × ℕ))) : Bool :=
  let p := initCols K
  let ones := p.1
  let cols := simVecIdx K ones p.2 gcs
  let n := K + E
  let vU := evalCoordVec ones cols n uC
  ((List.range R).all fun b1 ↦
    (List.range R).all fun b2 ↦
      if b1 < b2 then
        let l1 := evalCoordVec ones cols n (lCs.getD b1 (false, 0))
        let l2 := evalCoordVec ones cols n (lCs.getD b2 (false, 0))
        ((l1 &&& l2) &&& ones) == 0
      else true) &&
  ((List.range R).all fun b ↦
    let rc := rgCs.getD b ((false, 0), (false, 0))
    let gL := evalCoordVec ones cols n rc.1
    let gR := evalCoordVec ones cols n rc.2
    let vH := evalMaskedCoordsVec ones cols n lCs (maskHs.getD b 0) R
    let vY := evalCoordVec ones cols n (yCs.getD b (false, 0))
    (((gL &&& gR) ^^^ ((vH &&& vU) ^^^ vY)) &&& ones) == 0)

/-- Verify coordinate mask reconstructions for an `R`-branch router epoch. -/
def checkRouterRecon (f : ℕ → ℕ × ℕ) (R : ℕ) (gates : List ℕ) (mU : ℕ) (mLs mYs : List ℕ)
    (basis exp : List ℕ) (uC : Bool × ℕ) (lCs yCs : List (Bool × ℕ))
    (rgCs : List ((Bool × ℕ) × (Bool × ℕ))) : Bool :=
  decide (gates.length = R) &&
  decide (mLs.length = R) &&
  decide (mYs.length = R) &&
  decide (lCs.length = R) &&
  decide (yCs.length = R) &&
  decide (rgCs.length = R) &&
  decide (reconMask basis exp uC.1 uC.2 = mU) &&
  ((List.range R).all fun b ↦
    let g := gates.getD b 0
    let p := f g
    let rc := rgCs.getD b ((false, 0), (false, 0))
    let lc := lCs.getD b (false, 0)
    let yc := yCs.getD b (false, 0)
    decide (g < 139) &&
    decide (p.1 < 2 ^ (42 + g)) &&
    decide (p.2 < 2 ^ (42 + g)) &&
    decide (reconMask basis exp lc.1 lc.2 = mLs.getD b 0) &&
    decide (reconMask basis exp yc.1 yc.2 = mYs.getD b 0) &&
    decide (reconMask basis exp rc.1.1 rc.1.2 = p.1) &&
    decide (reconMask basis exp rc.2.1 rc.2.2 = p.2))

/-- Verify coordinate reconstruction and truth-table equality for a custom 2-mask `AND` gate. -/
def checkCustomGateCert (f : ℕ → ℕ × ℕ) (g mA mB : ℕ) (basis exp : List ℕ)
    (gcs : List ((Bool × ℕ) × (Bool × ℕ))) (aC bC : Bool × ℕ)
    (rgC : (Bool × ℕ) × (Bool × ℕ)) : Bool :=
  let K := basis.length
  let E := exp.length
  let p := initCols K
  let ones := p.1
  let cols := simVecIdx K ones p.2 gcs
  let n := K + E
  let vA := evalCoordVec ones cols n aC
  let vB := evalCoordVec ones cols n bC
  let gL := evalCoordVec ones cols n rgC.1
  let gR := evalCoordVec ones cols n rgC.2
  let gp := f g
  checkCert f basis exp gcs &&
  decide (g < 139) &&
  decide (gp.1 < 2 ^ (42 + g)) &&
  decide (gp.2 < 2 ^ (42 + g)) &&
  decide (reconMask basis exp aC.1 aC.2 = mA) &&
  decide (reconMask basis exp bC.1 bC.2 = mB) &&
  decide (reconMask basis exp rgC.1.1 rgC.1.2 = gp.1) &&
  decide (reconMask basis exp rgC.2.1 rgC.2.2 = gp.2) &&
  ((((gL &&& gR) ^^^ (vA &&& vB)) &&& ones) == 0)

theorem bool_eq_of_xor_eq_false {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

/-! ## Section 3: Configuration Types, Semantic Predicates & Certificate Soundness -/

/-- Configuration of one Stage-1 `WRouter` epoch (`R` branches). -/
structure RouterEpochCfg where
  /-- Gate indices in `0 .. 138` computed by this router epoch. -/
  gates : List ℕ
  /-- Shared `u`-wire input parity mask (`< 2 ^ 181`). -/
  mU : ℕ
  /-- Per-branch `L`-slot parity masks (`length = R`). -/
  mLs : List ℕ
  /-- Per-gate linear correction parity masks (`length = R`). -/
  mYs : List ℕ
  /-- Per-gate `H`-slot subset bitmasks (`length = R`). -/
  maskHs : List ℕ

/-- Semantic specification of a custom 2-mask `AND` gate `(g, mA, mB)` over `envFn`. -/
def CustomGateSem (envFn : Fin (2 ^ 41) → ℕ) (g mA mB : ℕ) : Prop :=
  ∀ c : Fin (2 ^ 41),
    (oddBits (envFn c &&& mA) 181 && oddBits (envFn c &&& mB) 181) =
      (envFn c).testBit (42 + g)

/-- Semantic specification of an `R`-branch `WRouter` epoch `rc` over `envFn`. -/
def RouterEpochSem (envFn : Fin (2 ^ 41) → ℕ) (R : ℕ) (rc : RouterEpochCfg) : Prop :=
  ∀ c : Fin (2 ^ 41),
    (∀ (b₁ b₂ : ℕ), b₁ < R → b₂ < R → b₁ ≠ b₂ →
      oddBits (envFn c &&& rc.mLs.getD b₁ 0) 181 = true →
      oddBits (envFn c &&& rc.mLs.getD b₂ 0) 181 = false) ∧
    (∀ (b : ℕ), b < R →
      xor (xorMaskBool (fun j ↦ oddBits (envFn c &&& rc.mLs.getD j 0) 181)
            (rc.maskHs.getD b 0) R && oddBits (envFn c &&& rc.mU) 181)
          (oddBits (envFn c &&& rc.mYs.getD b 0) 181) =
        (envFn c).testBit (42 + rc.gates.getD b 0))

theorem simVecIdx_recon_env_w5 {fgatesAt : ℕ → ℕ × ℕ} {envFn : Fin (2 ^ 41) → ℕ}
    (hBit0 : ∀ c : Fin (2 ^ 41), (envFn c).testBit 0 = true)
    (hGate : ∀ (c : Fin (2 ^ 41)) (g : ℕ), g < 139 → (envFn c).testBit (42 + g) =
      (oddBits (envFn c &&& (fgatesAt g).1) (42 + g) &&
        oddBits (envFn c &&& (fgatesAt g).2) (42 + g)))
    {basis exp : List ℕ} {gcs : List ((Bool × ℕ) × (Bool × ℕ))}
    (hCert : checkCert fgatesAt basis exp gcs = true) (c : Fin (2 ^ 41)) :
    ∃ z0 : ℕ, (initCols basis.length).1.testBit z0 = true ∧
      ∀ cd : Bool × ℕ,
        (evalCoordVec (initCols basis.length).1
          (simVecIdx basis.length (initCols basis.length).1 (initCols basis.length).2 gcs)
          (basis.length + exp.length) cd).testBit z0 =
          oddBits (envFn c &&& reconMask basis exp cd.1 cd.2) 181 := by
  have hexp := checkCert_exp_lt_w5 hCert
  obtain ⟨hOnes, hEv⟩ := simVecIdx_evalCoord_eq hCert (hBit0 c) fun e he ↦ hGate c _ (hexp e he)
  exact ⟨_, hOnes, fun cd ↦ (hEv cd).trans (reconMask_oddBits (hBit0 c) hexp cd.1 cd.2)⟩

theorem router_spec_of_cert_env {fgatesAt : ℕ → ℕ × ℕ} {envFn : Fin (2 ^ 41) → ℕ}
    (hBit0 : ∀ c : Fin (2 ^ 41), (envFn c).testBit 0 = true)
    (hGate : ∀ (c : Fin (2 ^ 41)) (g : ℕ), g < 139 →
      (envFn c).testBit (42 + g) =
        (oddBits (envFn c &&& (fgatesAt g).1) (42 + g) &&
         oddBits (envFn c &&& (fgatesAt g).2) (42 + g)))
    {R : ℕ} {gates : List ℕ} {mU : ℕ} {mLs mYs maskHs : List ℕ}
    {basis exp : List ℕ} {gcs : List ((Bool × ℕ) × (Bool × ℕ))}
    {uC : Bool × ℕ} {lCs yCs : List (Bool × ℕ)} {rgCs : List ((Bool × ℕ) × (Bool × ℕ))}
    (hCert : checkCert fgatesAt basis exp gcs = true)
    (hRecon : checkRouterRecon fgatesAt R gates mU mLs mYs basis exp uC lCs yCs rgCs = true)
    (hTree : checkRouterVec basis.length exp.length R maskHs gcs uC lCs yCs rgCs = true)
    (c : Fin (2 ^ 41)) :
    let env := envFn c
    (∀ b1 b2, b1 < b2 → b2 < R →
      (oddBits (env &&& mLs.getD b1 0) 181 && oddBits (env &&& mLs.getD b2 0) 181) = false) ∧
    (∀ b < R, env.testBit (42 + gates.getD b 0) =
      xor (xorMaskBool (fun j ↦ oddBits (env &&& mLs.getD j 0) 181) (maskHs.getD b 0) R &&
            oddBits (env &&& mU) 181) (oddBits (env &&& mYs.getD b 0) 181)) := by
  let env := envFn c
  obtain ⟨z0, hz0, hEvalAt⟩ := simVecIdx_recon_env_w5 hBit0 hGate hCert c
  obtain ⟨hDisjB, hEqB⟩ := Bool.and_eq_true_iff.mp hTree
  have hDisjAll := List.all_eq_true.mp hDisjB
  have hEqAll := List.all_eq_true.mp hEqB
  unfold checkRouterRecon at hRecon
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hRecon
  rcases hRecon with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hrU⟩, hRecB⟩
  have hRecAll := List.all_eq_true.mp hRecB
  refine ⟨fun b1 b2 hb12 hb2 ↦ ?_, fun b hb ↦ ?_⟩
  · have hb1 : b1 < R := Nat.lt_trans hb12 hb2
    have hd2 :=
      List.all_eq_true.mp (hDisjAll b1 (List.mem_range.mpr hb1)) b2 (List.mem_range.mpr hb2)
    rw [ite_eq_left hb12, beq_iff_eq] at hd2
    have hBit := congrArg (fun x ↦ x.testBit z0) hd2
    have hr1 := hRecAll b1 (List.mem_range.mpr hb1)
    have hr2 := hRecAll b2 (List.mem_range.mpr hb2)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr1 hr2
    rwa [Nat.testBit_and, Nat.zero_testBit, hz0, Bool.and_true, Nat.testBit_and,
      hEvalAt, hEvalAt, hr1.1.1.1.2, hr2.1.1.1.2] at hBit
  · have heB := beq_iff_eq.mp (hEqAll b (List.mem_range.mpr hb))
    have hrB := hRecAll b (List.mem_range.mpr hb)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrB
    rcases hrB with ⟨⟨⟨⟨⟨⟨hg139, hp1⟩, hp2⟩, _⟩, hrY⟩, hrG1⟩, hrG2⟩
    have hvH : (evalMaskedCoordsVec (initCols basis.length).1
        (simVecIdx basis.length (initCols basis.length).1 (initCols basis.length).2 gcs)
        (basis.length + exp.length) lCs (maskHs.getD b 0) R).testBit z0 =
        xorMaskBool (fun j ↦ oddBits (env &&& mLs.getD j 0) 181) (maskHs.getD b 0) R :=
      testBit_evalMaskedCoordsVec _ _ _ lCs (maskHs.getD b 0) z0 _ R fun j hj ↦ by
        have hrJ := hRecAll j (List.mem_range.mpr hj)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrJ
        rw [hEvalAt, hrJ.1.1.1.2]
    have hBit := congrArg (fun x ↦ x.testBit z0) heB
    rw [Nat.testBit_and, Nat.zero_testBit, hz0, Bool.and_true, Nat.testBit_xor,
        Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, hEvalAt, hEvalAt, hvH,
        hEvalAt, hEvalAt, hrG1, hrG2, hrU, hrY,
        oddBits_and_eq_of_lt_two_pow hp1 (by omega),
        oddBits_and_eq_of_lt_two_pow hp2 (by omega)] at hBit
    exact (hGate c (gates.getD b 0) hg139).trans (bool_eq_of_xor_eq_false hBit)

theorem router_epoch_sem_of_cert {fgatesAt : ℕ → ℕ × ℕ} {envFn : Fin (2 ^ 41) → ℕ}
    (hBit0 : ∀ c : Fin (2 ^ 41), (envFn c).testBit 0 = true)
    (hGate : ∀ (c : Fin (2 ^ 41)) (g : ℕ), g < 139 →
      (envFn c).testBit (42 + g) =
        (oddBits (envFn c &&& (fgatesAt g).1) (42 + g) && oddBits (envFn c &&& (fgatesAt g).2)
            (42 + g)))
    {R : ℕ} {rc : RouterEpochCfg} {basis exp : List ℕ} {gcs : List ((Bool × ℕ) × (Bool × ℕ))}
    {uC : Bool × ℕ} {lCs yCs : List (Bool × ℕ)} {rgCs : List ((Bool × ℕ) × (Bool × ℕ))}
    (hCert : checkCert fgatesAt basis exp gcs = true)
    (hRecon : checkRouterRecon fgatesAt R rc.gates rc.mU rc.mLs rc.mYs basis exp uC lCs yCs rgCs =
        true)
    (hTree : checkRouterVec basis.length exp.length R rc.maskHs gcs uC lCs yCs rgCs = true) :
    RouterEpochSem envFn R rc := fun c ↦ by
  obtain ⟨hDisj, hEval⟩ := router_spec_of_cert_env hBit0 hGate hCert hRecon hTree c
  refine ⟨fun b₁ b₂ hb₁ hb₂ hne hb1T ↦ ?_, fun b hb ↦ (hEval b hb).symm⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · simpa only [hb1T, Bool.true_and] using hDisj b₁ b₂ hlt hb₂
  · simpa only [hb1T, Bool.and_true] using hDisj b₂ b₁ hgt hb₁

theorem custom_gate_sem_of_cert {fgatesAt : ℕ → ℕ × ℕ} {envFn : Fin (2 ^ 41) → ℕ}
    (hBit0 : ∀ c : Fin (2 ^ 41), (envFn c).testBit 0 = true)
    (hGate : ∀ (c : Fin (2 ^ 41)) (g : ℕ), g < 139 →
      (envFn c).testBit (42 + g) =
        (oddBits (envFn c &&& (fgatesAt g).1) (42 + g) &&
         oddBits (envFn c &&& (fgatesAt g).2) (42 + g)))
    {g mA mB : ℕ} {basis exp : List ℕ} {gcs : List ((Bool × ℕ) × (Bool × ℕ))}
    {aC bC : Bool × ℕ} {rgC : (Bool × ℕ) × (Bool × ℕ)}
    (hChk : checkCustomGateCert fgatesAt g mA mB basis exp gcs aC bC rgC = true) :
    CustomGateSem envFn g mA mB := by
  unfold checkCustomGateCert at hChk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hChk
  rcases hChk with ⟨⟨⟨⟨⟨⟨⟨⟨hCert, hg139⟩, hp1⟩, hp2⟩, hrA⟩, hrB⟩, hrG1⟩, hrG2⟩, hVec⟩
  intro c
  obtain ⟨z0, hOnes, hEval⟩ := simVecIdx_recon_env_w5 hBit0 hGate hCert c
  have hBit := congrArg (fun x ↦ x.testBit z0) hVec
  rw [Nat.testBit_and, Nat.zero_testBit, hOnes, Bool.and_true, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_and, hEval, hEval, hEval, hEval, hrG1, hrG2, hrA, hrB,
      oddBits_and_eq_of_lt_two_pow hp1 (by omega),
      oddBits_and_eq_of_lt_two_pow hp2 (by omega)] at hBit
  exact (bool_eq_of_xor_eq_false hBit).symm.trans (hGate c g hg139).symm

/-! ## Section 4: Inductive `PrefixOp` Schedule Engine & Single-Step Fold Theorem -/

/-- Circuit-level operation in a Stage-1 prefix schedule (contains no proof witnesses). -/
inductive PrefixOp where
  | gchunk (gs : List ℕ)
  | customGate (g mA mB : ℕ)
  | routerEpoch (R sb : ℕ) (rc : RouterEpochCfg)

/-- Subspace simulation witness paired with a `PrefixOp` (used only inside proof certificates). -/
inductive PrefixOpCert where
  | none
  | custom (basis exp : List ℕ) (gcs : List ((Bool × ℕ) × (Bool × ℕ)))
      (aC bC : Bool × ℕ) (rgC : (Bool × ℕ) × (Bool × ℕ))
  | router (basis exp : List ℕ) (gcs : List ((Bool × ℕ) × (Bool × ℕ)))
      (uC : Bool × ℕ) (lCs yCs : List (Bool × ℕ))
      (rgCs : List ((Bool × ℕ) × (Bool × ℕ)))

/-- Precondition check for computing single prefix gate `g` from active gate mask `m`. -/
def checkGGatePre (fgatesAt : ℕ → ℕ × ℕ) (m g : ℕ) : Bool :=
  if g < 139 then
    let p := fgatesAt g
    let allowed := ((1 <<< 42) - 1) ||| (m <<< 42)
    (!m.testBit g) &&
    decide (p.1 < (1 <<< (42 + g))) && decide (p.2 < (1 <<< (42 + g))) &&
    ((p.1 &&& allowed) == p.1) && ((p.2 &&& allowed) == p.2)
  else false

/-- Precondition check for computing custom 2-mask gate `(g, a, b)` from active gate mask `m`. -/
def checkCustomGGatePre (m g a b : ℕ) : Bool :=
  let allowed := ((1 <<< 42) - 1) ||| (m <<< 42)
  decide (g < 139) && (!m.testBit g) &&
  decide (a < (1 <<< 181)) && decide (b < (1 <<< 181)) &&
  ((a &&& allowed) == a) && ((b &&& allowed) == b)

/-- Precondition check for a sequential list of unrouted prefix gates `gs`. -/
def checkGChunkPre (fgatesAt : ℕ → ℕ × ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | m, g :: gs => checkGGatePre fgatesAt m g && checkGChunkPre fgatesAt (m ||| (1 <<< g)) gs

/-- Fold active gate bitmask `m` across a list of gate indices `gs`. -/
def foldGatesMask : ℕ → List ℕ → ℕ
  | m, [] => m
  | m, g :: gs => foldGatesMask (m ||| (1 <<< g)) gs

/-- Fold active router-slot bitmask `sMask` across `k` consecutive slots starting at `sb`. -/
def foldSlotsMask (sb : ℕ) : ℕ → ℕ → ℕ
  | sMask, 0 => sMask
  | sMask, k + 1 => (foldSlotsMask sb sMask k) ||| (1 <<< (sb + k))

/-- Check pairwise distinctness of a `List ℕ`. -/
def checkListPairwiseNe : List ℕ → Bool
  | [] => true
  | x :: xs => (xs.all (fun y ↦ x != y)) && checkListPairwiseNe xs

theorem pairwise_ne_of_check :
    ∀ (xs : List ℕ), checkListPairwiseNe xs = true →
      ∀ (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length), i ≠ j → xs[i] ≠ xs[j]
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, hChk, i, j, hi, hj, hne => by
      obtain ⟨hAll, hRest⟩ := Bool.and_eq_true_iff.mp hChk
      match i, j with
      | 0, 0 => exact absurd rfl hne
      | 0, j' + 1 =>
          exact bne_iff_ne.mp (List.all_eq_true.mp hAll _ (List.getElem_mem (Nat.lt_of_succ_lt_succ
              hj)))
      | i' + 1, 0 =>
          exact (bne_iff_ne.mp (List.all_eq_true.mp hAll _ (List.getElem_mem (Nat.lt_of_succ_lt_succ
              hi)))).symm
      | i' + 1, j' + 1 =>
          exact pairwise_ne_of_check xs hRest i' j' (Nat.lt_of_succ_lt_succ hi)
            (Nat.lt_of_succ_lt_succ hj) fun e ↦ hne (congrArg Nat.succ e)

theorem foldGatesMask_testBit (m : ℕ) :
    ∀ (gs : List ℕ) (q : ℕ),
      (foldGatesMask m gs).testBit q = (m.testBit q || decide (q ∈ gs))
  | [], _ => by simp [foldGatesMask]
  | g :: gs, q => by
      rw [foldGatesMask, foldGatesMask_testBit (m ||| (1 <<< g)) gs q, Nat.testBit_or,
          testBit_one_shiftLeft]
      by_cases h1 : g = q <;> by_cases h2 : q ∈ gs <;> simp [h1, h2, eq_comm]

theorem foldSlotsMask_testBit (sb sMask : ℕ) :
    ∀ (k q : ℕ),
      (foldSlotsMask sb sMask k).testBit q = (sMask.testBit q || decide (sb ≤ q ∧ q < sb + k))
  | 0, q => by simp [foldSlotsMask]
  | k + 1, q => by
      rw [foldSlotsMask, Nat.testBit_or, foldSlotsMask_testBit sb sMask k q, testBit_one_shiftLeft,
          Bool.or_assoc]
      congr 1
      by_cases h1 : sb ≤ q ∧ q < sb + k <;> by_cases h2 : sb + k = q <;> simp [h1, h2] <;> try omega

/-- Verify that slots `sb + k ..` match static slot tables `(slotL, slotU)`. -/
def checkSlotTableMatch (slotL slotU : List ℕ) (sb mU : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | k, ml :: mls =>
      (slotL.getD (sb + k) 0 == ml) &&
      (slotU.getD (sb + k) 0 == mU) &&
      checkSlotTableMatch slotL slotU sb mU (k + 1) mls

theorem slot_table_match_get (slotL slotU : List ℕ) (sb mU : ℕ) :
    ∀ (k : ℕ) (mls : List ℕ), checkSlotTableMatch slotL slotU sb mU k mls = true →
      ∀ (b : ℕ) (hb : b < mls.length),
        slotL.getD (sb + (k + b)) 0 = mls[b] ∧ slotU.getD (sb + (k + b)) 0 = mU
  | _, [], _, _, hb => absurd hb (Nat.not_lt_zero _)
  | k, ml :: mls, hChk, 0, _ => by
      obtain ⟨⟨hL, hU⟩, _⟩ := by simpa only [checkSlotTableMatch, Bool.and_eq_true] using hChk
      simpa only [Nat.add_zero, List.getElem_cons_zero] using ⟨beq_iff_eq.mp hL, beq_iff_eq.mp hU⟩
  | k, _ :: mls, hChk, b' + 1, hb => by
      obtain ⟨_, hRest⟩ := Bool.and_eq_true_iff.mp hChk
      rw [show sb + (k + (b' + 1)) = sb + (k + 1 + b') by omega]
      exact slot_table_match_get slotL slotU sb mU (k + 1) mls hRest b' (Nat.lt_of_succ_lt_succ hb)

/-- Precondition check for an `R`-branch router epoch at slot offset `sb`. -/
def checkRouterEpochPre (slotL slotU : List ℕ) (m sMask R sb : ℕ) (rc : RouterEpochCfg) : Bool :=
  let allowed := ((1 <<< 42) - 1) ||| (m <<< 42)
  decide (0 < R) && decide (sb + R ≤ 45) &&
  (rc.gates.length == R) && (rc.mLs.length == R) && (rc.mYs.length == R) &&
  checkListPairwiseNe rc.gates &&
  (rc.gates.all (fun g ↦ decide (g < 139) && !m.testBit g)) &&
  ((List.range R).all (fun b ↦ !sMask.testBit (sb + b))) &&
  decide (rc.mU < (1 <<< 181)) && ((rc.mU &&& allowed) == rc.mU) &&
  (rc.mLs.all (fun ml ↦ decide (ml < (1 <<< 181)) && ((ml &&& allowed) == ml))) &&
  (rc.mYs.all (fun my ↦ decide (my < (1 <<< 181)) && ((my &&& allowed) == my))) &&
  checkSlotTableMatch slotL slotU sb rc.mU 0 rc.mLs

/-- Fold `(m, sMask)` across a full schedule `ops : List PrefixOp`. -/
def foldPrefixOps : ℕ → ℕ → List PrefixOp → ℕ × ℕ
  | m, sMask, [] => (m, sMask)
  | m, sMask, .gchunk gs :: rest => foldPrefixOps (foldGatesMask m gs) sMask rest
  | m, sMask, .customGate g _ _ :: rest => foldPrefixOps (m ||| (1 <<< g)) sMask rest
  | m, sMask, .routerEpoch R sb rc :: rest =>
      foldPrefixOps (foldGatesMask m rc.gates) (foldSlotsMask sb sMask R) rest

/-- Total `T`-gate count contributed by `ops : List PrefixOp`. -/
def prefixOpsT : List PrefixOp → ℕ
  | [] => 0
  | .gchunk gs :: rest => 4 * gs.length + prefixOpsT rest
  | .customGate _ _ _ :: rest => 4 + prefixOpsT rest
  | .routerEpoch R _ _ :: rest => (2 * R + 2) + prefixOpsT rest

/-- Single decidable `Bool` check for all mask/slot preconditions along `ops`. -/
def checkPrefixPre (fgatesAt : ℕ → ℕ × ℕ) (slotL slotU : List ℕ) :
    ℕ → ℕ → List PrefixOp → Bool
  | _, _, [] => true
  | m, sMask, .gchunk gs :: rest =>
      checkGChunkPre fgatesAt m gs &&
      checkPrefixPre fgatesAt slotL slotU (foldGatesMask m gs) sMask rest
  | m, sMask, .customGate g mA mB :: rest =>
      checkCustomGGatePre m g mA mB &&
      checkPrefixPre fgatesAt slotL slotU (m ||| (1 <<< g)) sMask rest
  | m, sMask, .routerEpoch R sb rc :: rest =>
      decide (sb + R ≤ 45) &&
      checkRouterEpochPre slotL slotU m sMask R sb rc &&
      checkPrefixPre fgatesAt slotL slotU
        (foldGatesMask m rc.gates) (foldSlotsMask sb sMask R) rest

/-- Single decidable `Bool` check for all custom-gate and router subspace certificates in `ops`. -/
def checkPrefixCerts (fgatesAt : ℕ → ℕ × ℕ) : List PrefixOp → List PrefixOpCert → Bool
  | [], [] => true
  | .gchunk _ :: rest, .none :: restC => checkPrefixCerts fgatesAt rest restC
  | .customGate g mA mB :: rest, .custom basis exp gcs aC bC rgC :: restC =>
      checkCustomGateCert fgatesAt g mA mB basis exp gcs aC bC rgC &&
      checkPrefixCerts fgatesAt rest restC
  | .routerEpoch R _ rc :: rest, .router basis exp gcs uC lCs yCs rgCs :: restC =>
      checkCert fgatesAt basis exp gcs &&
      checkRouterRecon fgatesAt R rc.gates rc.mU rc.mLs rc.mYs basis exp uC lCs yCs rgCs &&
      checkRouterVec basis.length exp.length R rc.maskHs gcs uC lCs yCs rgCs &&
      checkPrefixCerts fgatesAt rest restC
  | _, _ => false

/-- Inductive semantic obligation across all custom gates and router epochs in `ops`. -/
def PrefixOpsSem (envFn : Fin (2 ^ 41) → ℕ) : List PrefixOp → Prop
  | [] => True
  | .gchunk _ :: rest => PrefixOpsSem envFn rest
  | .customGate g mA mB :: rest => CustomGateSem envFn g mA mB ∧ PrefixOpsSem envFn rest
  | .routerEpoch R _ rc :: rest => RouterEpochSem envFn R rc ∧ PrefixOpsSem envFn rest

theorem prefix_ops_sem_of_certs {fgatesAt : ℕ → ℕ × ℕ} {envFn : Fin (2 ^ 41) → ℕ}
    (hBit0 : ∀ c : Fin (2 ^ 41), (envFn c).testBit 0 = true)
    (hGate : ∀ (c : Fin (2 ^ 41)) (g : ℕ), g < 139 →
      (envFn c).testBit (42 + g) =
        (oddBits (envFn c &&& (fgatesAt g).1) (42 + g) &&
         oddBits (envFn c &&& (fgatesAt g).2) (42 + g))) :
    ∀ (ops : List PrefixOp) (certs : List PrefixOpCert),
      checkPrefixCerts fgatesAt ops certs = true → PrefixOpsSem envFn ops
  | [], _, _ => trivial
  | op :: _, [], h => by cases op <;> exact Bool.noConfusion h
  | .gchunk _ :: rest, c :: restC, h => by
      cases c <;> try exact Bool.noConfusion h
      exact prefix_ops_sem_of_certs hBit0 hGate rest restC h
  | .customGate _ _ _ :: rest, c :: restC, h => by
      cases c <;> try exact Bool.noConfusion h
      obtain ⟨hC, hRest⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨custom_gate_sem_of_cert hBit0 hGate hC,
          prefix_ops_sem_of_certs hBit0 hGate rest restC hRest⟩
  | .routerEpoch _ _ _ :: rest, c :: restC, h => by
      cases c <;> try exact Bool.noConfusion h
      obtain ⟨⟨⟨hCert, hRecon⟩, hTree⟩, hRest⟩ := by
        simpa only [checkPrefixCerts, Bool.and_eq_true] using h
      exact ⟨router_epoch_sem_of_cert hBit0 hGate hCert hRecon hTree,
        prefix_ops_sem_of_certs hBit0 hGate rest restC hRest⟩

/-- Fold a schedule `ops : List PrefixOp` around `mid : DynamicCircuit Var n`. -/
def wrapPrefixOps {Var : Type} {n : ℕ}
    (wrapChunkFn : List ℕ → DynamicCircuit Var n → DynamicCircuit Var n)
    (wrapCustomFn : ℕ → ℕ → ℕ → DynamicCircuit Var n → DynamicCircuit Var n)
    (wrapEpochFn : (R sb : ℕ) → sb + R ≤ 45 → RouterEpochCfg →
      DynamicCircuit Var n → DynamicCircuit Var n) :
    List PrefixOp → DynamicCircuit Var n → DynamicCircuit Var n
  | [], mid => mid
  | .gchunk gs :: rest, mid =>
      wrapChunkFn gs (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn rest mid)
  | .customGate g mA mB :: rest, mid =>
      wrapCustomFn g mA mB (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn rest mid)
  | .routerEpoch R sb rc :: rest, mid =>
      if hsb : sb + R ≤ 45 then
        wrapEpochFn R sb hsb rc (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn rest mid)
      else
        wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn rest mid

theorem dw_wrap_prefix_ops {Var : Type} {n : ℕ} {DW : DynamicCircuit Var n → Prop}
    (wrapChunkFn : List ℕ → DynamicCircuit Var n → DynamicCircuit Var n)
    (wrapCustomFn : ℕ → ℕ → ℕ → DynamicCircuit Var n → DynamicCircuit Var n)
    (wrapEpochFn : (R sb : ℕ) → sb + R ≤ 45 → RouterEpochCfg →
      DynamicCircuit Var n → DynamicCircuit Var n)
    (hdwChunk : ∀ gs mid, DW mid → DW (wrapChunkFn gs mid))
    (hdwCustom : ∀ g mA mB mid, DW mid → DW (wrapCustomFn g mA mB mid))
    (hdwEpoch : ∀ R sb (hsb : sb + R ≤ 45) rc mid, DW mid → DW (wrapEpochFn R sb hsb rc mid)) :
    ∀ (ops : List PrefixOp) (mid : DynamicCircuit Var n),
      DW mid → DW (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn ops mid)
  | [], _, hd => hd
  | .gchunk gs :: rest, mid, hd =>
      hdwChunk gs _ (dw_wrap_prefix_ops wrapChunkFn wrapCustomFn wrapEpochFn hdwChunk hdwCustom
          hdwEpoch rest mid hd)
  | .customGate g mA mB :: rest, mid, hd =>
      hdwCustom g mA mB _ (dw_wrap_prefix_ops wrapChunkFn wrapCustomFn wrapEpochFn hdwChunk
          hdwCustom hdwEpoch rest mid hd)
  | .routerEpoch R sb rc :: rest, mid, hd => by
      dsimp only [wrapPrefixOps]
      have ih :=
          dw_wrap_prefix_ops wrapChunkFn wrapCustomFn wrapEpochFn hdwChunk hdwCustom hdwEpoch rest
          mid hd
      split_ifs with hsb
      · exact hdwEpoch R sb hsb rc _ ih
      · exact ih

theorem step_wrap_prefix_ops {Var : Type} {n : ℕ}
    {fgatesAt : ℕ → ℕ × ℕ} {slotL slotU : List ℕ} {envFn : Fin (2 ^ 41) → ℕ}
    {Step : ℕ → ℕ → DynamicCircuit Var n → Prop}
    (wrapChunkFn : List ℕ → DynamicCircuit Var n → DynamicCircuit Var n)
    (wrapCustomFn : ℕ → ℕ → ℕ → DynamicCircuit Var n → DynamicCircuit Var n)
    (wrapEpochFn : (R sb : ℕ) → sb + R ≤ 45 → RouterEpochCfg →
      DynamicCircuit Var n → DynamicCircuit Var n)
    (hChunk : ∀ m sMask gs mid,
      checkGChunkPre fgatesAt m gs = true →
      Step (foldGatesMask m gs) sMask mid →
      Step m sMask (wrapChunkFn gs mid) ∧
      (wrapChunkFn gs mid).count .T = 4 * gs.length + mid.count .T ∧
      (wrapChunkFn gs mid).count .TOFF = mid.count .TOFF)
    (hCustom : ∀ m sMask g mA mB mid,
      checkCustomGGatePre m g mA mB = true →
      CustomGateSem envFn g mA mB →
      Step (m ||| (1 <<< g)) sMask mid →
      Step m sMask (wrapCustomFn g mA mB mid) ∧
      (wrapCustomFn g mA mB mid).count .T = 4 + mid.count .T ∧
      (wrapCustomFn g mA mB mid).count .TOFF = mid.count .TOFF)
    (hEpoch : ∀ m sMask R sb (hsb : sb + R ≤ 45) rc mid,
      checkRouterEpochPre slotL slotU m sMask R sb rc = true →
      RouterEpochSem envFn R rc →
      Step (foldGatesMask m rc.gates) (foldSlotsMask sb sMask R) mid →
      Step m sMask (wrapEpochFn R sb hsb rc mid) ∧
      (wrapEpochFn R sb hsb rc mid).count .T = (2 * R + 2) + mid.count .T ∧
      (wrapEpochFn R sb hsb rc mid).count .TOFF = mid.count .TOFF) :
    ∀ (ops : List PrefixOp) (m sMask : ℕ) (mid : DynamicCircuit Var n),
      checkPrefixPre fgatesAt slotL slotU m sMask ops = true →
      PrefixOpsSem envFn ops →
      Step (foldPrefixOps m sMask ops).1 (foldPrefixOps m sMask ops).2 mid →
      Step m sMask (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn ops mid) ∧
      (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn ops mid).count .T =
        prefixOpsT ops + mid.count .T ∧
      (wrapPrefixOps wrapChunkFn wrapCustomFn wrapEpochFn ops mid).count .TOFF =
        mid.count .TOFF
  | [], m, sMask, mid, _, _, hMid => ⟨hMid, by simp [wrapPrefixOps, prefixOpsT], rfl⟩
  | .gchunk gs :: rest, m, sMask, mid, hPre, hSem, hMid => by
      obtain ⟨hCk, hPreRest⟩ := Bool.and_eq_true_iff.mp hPre
      obtain ⟨ihS, ihT, ihF⟩ := step_wrap_prefix_ops wrapChunkFn wrapCustomFn wrapEpochFn
        hChunk hCustom hEpoch rest (foldGatesMask m gs) sMask mid hPreRest hSem hMid
      obtain ⟨sC, tC, fC⟩ := hChunk m sMask gs _ hCk ihS
      dsimp only [wrapPrefixOps, prefixOpsT]
      exact ⟨sC, by rw [tC, ihT, Nat.add_assoc], fC.trans ihF⟩
  | .customGate g mA mB :: rest, m, sMask, mid, hPre, hSem, hMid => by
      obtain ⟨hCk, hPreRest⟩ := Bool.and_eq_true_iff.mp hPre
      obtain ⟨ihS, ihT, ihF⟩ := step_wrap_prefix_ops wrapChunkFn wrapCustomFn wrapEpochFn
        hChunk hCustom hEpoch rest (m ||| (1 <<< g)) sMask mid hPreRest hSem.2 hMid
      obtain ⟨sC, tC, fC⟩ := hCustom m sMask g mA mB _ hCk hSem.1 ihS
      dsimp only [wrapPrefixOps, prefixOpsT]
      exact ⟨sC, by rw [tC, ihT, Nat.add_assoc], fC.trans ihF⟩
  | .routerEpoch R sb rc :: rest, m, sMask, mid, hPre, hSem, hMid => by
      obtain ⟨⟨hsbB, hCk⟩, hPreRest⟩ := by simpa only [checkPrefixPre, Bool.and_eq_true] using hPre
      have hsb : sb + R ≤ 45 := of_decide_eq_true hsbB
      obtain ⟨ihS, ihT, ihF⟩ := step_wrap_prefix_ops wrapChunkFn wrapCustomFn wrapEpochFn
        hChunk hCustom hEpoch rest (foldGatesMask m rc.gates)
            (foldSlotsMask sb sMask R) mid hPreRest hSem.2 hMid
      obtain ⟨sE, tE, fE⟩ := hEpoch m sMask R sb hsb rc _ hCk hSem.1 ihS
      dsimp only [wrapPrefixOps, prefixOpsT]
      rw [dite_eq_left hsb]
      exact ⟨sE, by omega, fE.trans ihF⟩

end QuantumComputation.Specs.PhotochemistrySolution.Stage1MaskEngine

open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1MaskEngine (oddMask)
noncomputable section
section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1WRouter1416
open PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.ScreenFermatCore
open PhotochemistrySolution.Tier1K3708 PhotochemistrySolution.Stage1CoinDecode
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (decodeUltraNuc192 phiU1
    h224 muxPair allTree coinW outW wBit wPack bitAt bitAt_eq_testBit b2BEq)
def careTier1Walk_12 (r : ℕ) : Bool :=
  Bool.or (Bool.not (bitAt r 0)) (Bool.and (Nat.ble ((r / 2) % 8) 4) (Nat.ble ((r / 16) % 32) 30))

abbrev nGatesTier1W11Opt1416 : ℕ := 209
abbrev nGatesTier1Sym96 : ℕ := nGatesTier1W11Opt1416

def gatesTier1Sym96TailLo (k : ℕ) : ℕ × ℕ :=
    (muxPair (Nat.blt k 72) (muxPair (Nat.blt k 49) (muxPair (Nat.blt k 37) (muxPair (Nat.blt k 31)
    (muxPair (Nat.blt k 28) (muxPair (Nat.blt k 27) (0x400001, 0x2800001) (0x1000000, 0x2000000))
    (muxPair (Nat.blt k 29) ((oddMask 0x400000000000000001), 0x200001) (muxPair (Nat.blt k 30)
    ((oddMask 0x200000000000000001), (oddMask 0x800000000000000001))
    ((oddMask 0x1000000000000000001), 0xa00000000000c50000)))) (muxPair (Nat.blt k 34)
    (muxPair (Nat.blt k 32) (0x2a60000, (oddMask 0x1000000000000000001)) (muxPair (Nat.blt k 33)
    ((oddMask 0x1000000000000000001), 0x2300000000001940001)
    (0x80001, (oddMask 0x1000000000000000001)))) (muxPair (Nat.blt k 35)
    ((oddMask 0x1000000000000000001), 0x6000000000000100001) (muxPair (Nat.blt k 36)
    (0xa800000000000080000, 0x12800000000000040000)
    (0x1a8000000000000e0001, 0x35000000000000050000))))) (muxPair (Nat.blt k 43)
    (muxPair (Nat.blt k 40) (muxPair (Nat.blt k 38) (0x38800000000000080000, 0x70800000000000040000)
    (muxPair (Nat.blt k 39) (0xa6800000000000100000, (oddMask 0x166000000000000000001))
    (0x1f0000000000000c0001, (oddMask 0x241000000000000000001)))) (muxPair (Nat.blt k 41)
    ((oddMask 0x580000000000000000001), (oddMask 0x658000000000000000001)) (muxPair (Nat.blt k 42)
    ((oddMask 0x4a4000000000000000001), (oddMask 0xa00000000000000000001))
    (0x403800000000000000001, 0x920200000000000800001)))) (muxPair (Nat.blt k 46)
    (muxPair (Nat.blt k 44) (0x800000, 0x400000) (muxPair (Nat.blt k 45)
    (0x2000000000000000800000, 0x200000) ((oddMask 0x4000000000000000000001), 0x10001)))
    (muxPair (Nat.blt k 47) ((oddMask 0x10000000000000000000001), 0x200000) (muxPair (Nat.blt k 48)
    (0x401000000000000020000, (oddMask 0x28000000000000000000001))
    ((oddMask 0x44000000000000000000001), 0x10000)))))) (muxPair (Nat.blt k 60)
    (muxPair (Nat.blt k 54) (muxPair (Nat.blt k 51) (muxPair (Nat.blt k 50)
    ((oddMask 0x10008000000000000000001), 0x3000000000000030000)
    ((oddMask 0x100050000000000000000001), (oddMask 0x54240000000000000000001)))
    (muxPair (Nat.blt k 52) (0x80000000000000000100001, (oddMask 0x54240000000000000000001))
    (muxPair (Nat.blt k 53) ((oddMask 0x120000000000000000000001), 0x100120000000000000200000)
    (0x100020000000000000000001, 0x2a000000000000000100000)))) (muxPair (Nat.blt k 57)
    (muxPair (Nat.blt k 55) (0x20020000000000000080000, 0xc1a020000000000000180000)
    (muxPair (Nat.blt k 56) (0x800000000000001, 0x8100a018002800010000)
    (0x800000000000001, 0x200011b0060200018000f0000))) (muxPair (Nat.blt k 58)
    (0x800000000000000, 0x60003a50091c8002524020001) (muxPair (Nat.blt k 59)
    (0x800000000000001, 0xa0002170051f0001524040000) (0x105800020000000,
  0x1b1800130000000))))) (muxPair (Nat.blt k 66) (muxPair (Nat.blt k 63) (muxPair (Nat.blt k 61)
      (0x5800020000000, 0x3d800010000000) (muxPair (Nat.blt k 62)
      (0x118000028000001, (oddMask 0x80000000000000000000000001))
      (0x20000000000105800020000000, 0xa00000000001b1800130000000))) (muxPair (Nat.blt k 64)
      (0xd01cd800120000001, 0x200000000001cd800120000000) (muxPair (Nat.blt k 65)
      ((oddMask 0x400000000000000000000000001), 0x300000000000000000000000001)
      (0x200000000d0000000000000001, (oddMask 0xe000000001a0000000000000001)))))
      (muxPair (Nat.blt k 69) (muxPair (Nat.blt k 67)
      (0x6200000000d00c8000100000001, (oddMask 0x1200000000000000000000000001))
      (muxPair (Nat.blt k 68) (0xa801f820000000000, (oddMask 0x3600000000000000000000000001))
      ((oddMask 0x1900000000000000000000000001), (oddMask 0x5840000000000000000000000001))))
      (muxPair (Nat.blt k 70) ((oddMask 0x9840000000000000000000000001),
      0x60000000000781ab820110000000) (muxPair (Nat.blt k 71)
      (0xd20000000000000000000000001, 0x50200000000a8127820030000000)
      (0x20000000078046020028000000, 0xd20000000000000000000000001))))))) (muxPair (Nat.blt k 95)
      (muxPair (Nat.blt k 83) (muxPair (Nat.blt k 77) (muxPair (Nat.blt k 74)
      (muxPair (Nat.blt k 73) (0x400, 0x800) (256, 512)) (muxPair (Nat.blt k 75)
      (0x881, (oddMask 0x100000000000000000000000000001)) (muxPair (Nat.blt k 76)
      (0x40000000000000000000000000800, 0x140000000000000000000000000400)
      (0x116000000000000100041, 0x40000000000000000000000000041)))) (muxPair (Nat.blt k 80)
      (muxPair (Nat.blt k 78) ((oddMask 0x800000000000000000000000000001),
      0x600000000000000000000000000001) (muxPair (Nat.blt k 79)
      (0x40000000116000000000000100000, 0xe00000000116000000000000100001)
      (0xc40000000116000000000000100841, (oddMask 0x2400000000000000000000000000001))))
      (muxPair (Nat.blt k 81) ((oddMask 0x161000000000000000001),
      (oddMask 0x6c00000000000000000000000000001)) (muxPair (Nat.blt k 82)
      ((oddMask 0x3200000000000000000000000000001), (oddMask 0xb080000000000000000000000000001))
      ((oddMask 0x13080000000000000000000000000001), 0xc0000000001a6800000000000100601)))))
      (muxPair (Nat.blt k 89) (muxPair (Nat.blt k 86) (muxPair (Nat.blt k 84)
      (0x1a40000000000000000000000000001, 0xa0400000000b0800000000000000900) (muxPair (Nat.blt k 85)
      (0x400000001a68000000000001007c0, 0x1a40000000000000000000000000001)
      (0x540400000001a6800000000000100640, 0x760110200001160a811a020020100e41)))
      (muxPair (Nat.blt k 87) (0x1800c000000000000005800020000200,
      0xee000000000116000000000000100c41) (muxPair (Nat.blt k 88)
      (0x220510200000b08a811a020020000801,
  0x17603b0000001160d017c000010100e41) (0x1800c000000000000005800020000200,
      (oddMask 0x600000000000000000000000000000001))))) (muxPair (Nat.blt k 92)
      (muxPair (Nat.blt k 90) (0x30018000000000001b1800130000400,
      0x1ef04d020000116000100000000100040) (muxPair (Nat.blt k 91)
      (0x105800020000800, 0x9ee00c000000116000005800020100440) (0x2041020000000000000000000000001,
      0x19ee00d020000116000005800020100c41))) (muxPair (Nat.blt k 93)
      (0x10020010000000000001b1800130000401, 0x30018000000000000b4000110000c01)
      (muxPair (Nat.blt k 94) ((oddMask 0xe00000000000000000000000000000001),
      (oddMask 0x8e00000000000000000000000000000001))
      (0x80001a680281d800800100040, 0x2440000000116000000000000100041)))))) (muxPair (Nat.blt k 106)
      (muxPair (Nat.blt k 100) (muxPair (Nat.blt k 97) (muxPair (Nat.blt k 96)
      (0x120003010011cd800524140801, 0x100024400000001a6800000000000100800)
      (0x1e00038d0011cd8005240a0201, 0x300024400000000b0800000000000000200)) (muxPair (Nat.blt k 98)
      (0x80001a680281d800800100041, 0x3000244000200003180b9d5802d24010001) (muxPair (Nat.blt k 99)
      (0x120003010011cd800524140800, (oddMask 0x100000000000000000000000000000000001))
      ((oddMask 0x200000000000000000000000000000000001), 0x1b000000001e00038d0011cd8005240a0201))))
      (muxPair (Nat.blt k 103) (muxPair (Nat.blt k 101)
      (0x200000000a818002800000100, 0x4000000001e00038d0011cd8005240a0101) (muxPair (Nat.blt k 102)
      (0x80003a5000800000000020080, 0x44000000001e00038d0011cd8005240a0081)
      (0x220000120000b08059f0001524000501, 0xc4002304001e00033d8011cd8005240a0d00)))
      (muxPair (Nat.blt k 104) (0x104001e0003a50091c8002524020800,
      0x1c4000104001e00038d0011cd8005240a0801) (muxPair (Nat.blt k 105)
      (0x100000000000200000000a818002800000101, (oddMask 0x3400000000000000000000000000000000001))
      (0x20000000000080003a5000800000000020081,
      (oddMask 0xc000000000000000000000000000000000001)))))) (muxPair (Nat.blt k 112)
      (muxPair (Nat.blt k 109) (muxPair (Nat.blt k 107) (0x220000120000b08059f0001524000500,
      (oddMask 0x16000000000000000000000000000000000001)) (muxPair (Nat.blt k 108)
      ((oddMask 0x20000000000000000000000000000000000001), 0x1a00000104001e0003a50091c8002524020800)
      (0x1800000000001, 0x1d23a00000000000800000))) (muxPair (Nat.blt k 110)
      ((oddMask 0x80000000000000001), 0x200000000000000001) (muxPair (Nat.blt k 111)
      ((oddMask 0x80000000000000000000000000000000000001), 0x16000000000002000000)
      ((oddMask 0x200000000000000000000000000000000000001), 0x8000000000001000000))))
      (muxPair (Nat.blt k 115) (muxPair (Nat.blt k 113)
      ((oddMask 0x400000000000000000000000000000000000001),
  0x10800000000000800000) (muxPair (Nat.blt k 114)
      ((oddMask 0xc00000000000000000000000000000000000001), 0x170bd81c1d0000000)
      ((oddMask 0x1000000000000000000000000000000000000001), 0x12800000000000400001)))
      (muxPair (Nat.blt k 116) ((oddMask 0x3000000000000000000000000000000000000001),
      0x11000000000000200001) (muxPair (Nat.blt k 117)
      ((oddMask 0x2000000000000000000000000000000000000001), 0x11000000000000200001)
      ((oddMask 0x1c00000000000000000000000000000000000001), 0x12800000000000400001))))))))
def gatesTier1Sym96TailHi (k : ℕ) : ℕ × ℕ :=
    (muxPair (Nat.blt k 163) (muxPair (Nat.blt k 140) (muxPair (Nat.blt k 129)
    (muxPair (Nat.blt k 123) (muxPair (Nat.blt k 120) (muxPair (Nat.blt k 119)
    ((oddMask 0x10000000000000000000000000000000000000001), 0x11000000000000200001)
    ((oddMask 0x20000000000000000000000000000000000000001), 0xa91ae024170000000))
    (muxPair (Nat.blt k 121) ((oddMask 0x40000000000000000000000000000000000000001),
    0x221058080a0000000) (muxPair (Nat.blt k 122) ((oddMask 0x2000000000000000000000000000001),
    (oddMask 0x8000000000000000000000000000000000000001))
    ((oddMask 0x80000000000000000000000000000000000000001), 0x7801f820000000001))))
    (muxPair (Nat.blt k 126) (muxPair (Nat.blt k 124)
    ((oddMask 0x80000000000000000000000000000000000000001), 0xa801f820000000000)
    (muxPair (Nat.blt k 125) ((oddMask 0x878000000000000000000001), 64)
    ((oddMask 0x800000000000000000000000000000000000000001), 0x2c0001826020000000000000180000)))
    (muxPair (Nat.blt k 127) ((oddMask 0x600000000000000000000000000000000000000001),
    0x8000000200000000000000000000000080) (muxPair (Nat.blt k 128)
    ((oddMask 0x680000000000000000000000000000000000000001), 0x1000000000000000000000000040000000)
    (0x2804000000000000001802020000000000000180002,
    0x2804000000000000001802020000000000000180000))))) (muxPair (Nat.blt k 134)
    (muxPair (Nat.blt k 131) (muxPair (Nat.blt k 130)
    (0x1105000000000000000806000000000000000100004, 0x5105000000000000000806000000000000000100000)
    (0x147000000000000000418000000000000000000008,
    (oddMask 0x1828e000000000000000830000000000000000000001))) (muxPair (Nat.blt k 132)
    (0xb02000000000000000000000000000000000000010,
    (oddMask 0x39604000000000000000000000000000000000000001)) (muxPair (Nat.blt k 133)
    (0x41000000000000000024000000000000000000020,
    (oddMask 0x78082000000000000000048000000000000000000001))
    (0xa0200000000000000141c020000000000000081000,
    0x7ca0200000000000000141c020000000000000080000)))) (muxPair (Nat.blt k 137)
    (muxPair (Nat.blt k 135) (0x205000000000000000418000000000000000002000,
    (oddMask 0x1f840a000000000000000830000000000000000000001)) (muxPair (Nat.blt k 136)
    (0x1d43000000000000001438020000000000000084000, 0x1fdd43000000000000001438020000000000000080000)
    (0x30600000000000000043c000000000000000008000,
    (oddMask 0x7f860c000000000000000878000000000000000000001)))) (muxPair (Nat.blt k 138)
    (0x1205000000000000000000000000009800100000000,
    (oddMask 0xffa40a000000000000000000000000000000000000001)) (muxPair (Nat.blt k 139)
    (0x30700000000000000000000000001f800200000000,
    (oddMask 0x1ff860e000000000000000000000000000000000000001))
  ((oddMask 0x10e000000000000000000000000000000000000001),
      (oddMask 0x3ff8000000000000000000000000000000000000000001))))))) (muxPair (Nat.blt k 151)
      (muxPair (Nat.blt k 145) (muxPair (Nat.blt k 142) (muxPair (Nat.blt k 141)
      (0x500000000000000000000000001, (oddMask 0x400010fc80000000000000000000000000000000000001))
      ((oddMask 0x8800000000000000000000000000000000000001),
      (oddMask 0x8000000000000000000000000000000000000000000001))) (muxPair (Nat.blt k 143)
      (0xa00000000000000000000000000001,
      (oddMask 0x18000000000000000000000000000000000000000000001)) (muxPair (Nat.blt k 144)
      ((oddMask 0x3280000000000000000000000000000000000001),
      (oddMask 0x20000000000000000000000000000000000000000000001))
      (0x30000000000000000000000000000000000001,
      (oddMask 0x40000000000000000000000000000000000000000000001))))) (muxPair (Nat.blt k 148)
      (muxPair (Nat.blt k 146) (0x8700000000000000000000000000000001,
      (oddMask 0x60000000000000000000000000000000000000000000001)) (muxPair (Nat.blt k 147)
      (0xc9ffc040000000000000000047d23a40000000000800001,
      0xc9ffc000000000000000000046000040000000000000001)
      (0x101ffc000080000000000000046000040000000000000001,
      0x100000040080000000000000001d23a00000000000800000))) (muxPair (Nat.blt k 149)
      (0x301ffc300080000000000000046000000000000000000001,
      (oddMask 0x403ff808010000000000000008c000000000000000000001)) (muxPair (Nat.blt k 150)
      (0xc8000000000000000000000001d23a00000000000800001,
      0x1c8000300080000000000000001d23a90000000000800001)
      (0x7801f820000000001, (oddMask 0x390000080000000000000000000000000000000000000001))))))
      (muxPair (Nat.blt k 157) (muxPair (Nat.blt k 154) (muxPair (Nat.blt k 152)
      (0x3c4000000001e00038d0011cd8005240a0000,
      (oddMask 0x80000000000000000000000000000000000000000000001)) (muxPair (Nat.blt k 153)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x2000000000003c4000244001c0003bc80a8180028000b0000)
      (0x254000034000000000000001e00038d0411cd8005240a0000,
      (oddMask 0x4a00000680000000000000000000000080000000000000001)))) (muxPair (Nat.blt k 155)
      (0x40000000000000000000000000000000000000000000001,
      0xa500000340003c4000000001e00022b8411cd8005241a0040) (muxPair (Nat.blt k 156)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x1c0400000000000000000000080001a680281d800800100240)
      ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0x454000034000000000000000e00011b04b9d5802d240f0001)))) (muxPair (Nat.blt k 160)
      (muxPair (Nat.blt k 158) (0x40000000000000000000000000000000000000000000001,
      0x26000000000003c4000244001e00038d0011cd8005240a0840) (muxPair (Nat.blt k 159)
  ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0xde5000003400000000000000120003010411cd800524140801)
      ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0x4854000034000000000000000a0000810491c8002524010001))) (muxPair (Nat.blt k 161)
      (0x40000000000000000000000000000000000000000000001,
      0x370000000000000000002440000000116000000000000100240) (muxPair (Nat.blt k 162)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x2b0540000340000000000000000000000040000000000000200)
      ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0x24400000000000000000000000200008100b9d5802d24010000))))))) (muxPair (Nat.blt k 186)
      (muxPair (Nat.blt k 174) (muxPair (Nat.blt k 168) (muxPair (Nat.blt k 165)
      (muxPair (Nat.blt k 164) (0x40000000000000000000000000000000000000000000001,
      0xd9a500000340003c4000244001e00038d0411cd8005240a0a40)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x204000000000000000000000200000000a818002800000101)) (muxPair (Nat.blt k 166)
      ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0x254000034000000000000001c0003a50439d0000d24020000) (muxPair (Nat.blt k 167)
      (0x40000000000000000000000000000000000000000000001,
      0x80005000003400000000230400000000b0840000000000000d80)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x180000400000000000000000000080003a5000800000000020080)))) (muxPair (Nat.blt k 171)
      (muxPair (Nat.blt k 169) ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0x2800204000000000000000000000400000000c038003000000001) (muxPair (Nat.blt k 170)
      (0x40000000000000000000000000000000000000000000001,
      0xc0020400000000000000220000000000b0800000000000000581)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x580020400000000000000220000120000b08059f0001524000500))) (muxPair (Nat.blt k 172)
      ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0x680025400003400000000000000120000000459f0001524000001) (muxPair (Nat.blt k 173)
      ((oddMask 0x80000000000000000000000000000000000000000000001),
      0x174000000000000000000000000000000000000000000000000100)
      ((oddMask 0x4000000000000000000000000000000000000000000000001),
      0x27800000000000000000000104001e0003a50091c8002524020800))))) (muxPair (Nat.blt k 180)
      (muxPair (Nat.blt k 177) (muxPair (Nat.blt k 175)
      ((oddMask 0xa00000680000000000000000000000080000000000000001),
      0xa2000000000000000000000000000c0003a500c838003000020000) (muxPair (Nat.blt k 176)
      (0x40000000000000000000000000000000000000000000001,
  0xfb80025000003400000000230400000000b0840000000000000d00)
      ((oddMask 0x4000002040000000000000000000000001),
      (oddMask 0x100000000000000000000000000000000000000000000001)))) (muxPair (Nat.blt k 178)
      ((oddMask 0x8000000000000000000000000000000000000000000000000000001),
      0x400000000000000000000007603b0000001160d017c000010100e40) (muxPair (Nat.blt k 179)
      (0xc8000000000000000000000000000000000000000000001,
      0xc8000000000000000004820000000000000000000000001) (0x20262010200000b0800000000000000800,
      0x80000000000000000000000000000000000000000000001)))) (muxPair (Nat.blt k 183)
      (muxPair (Nat.blt k 181) ((oddMask 0x8000000000000000000000000000000000000000000000000000001),
      0x40000000800000000000000220510200000b08a811a020020000801) (muxPair (Nat.blt k 182)
      (0xc8000000000000000000000000000000000000000000001,
      0x4c0000000c800000000000000003d9000000000d017c000010000000)
      (0x80000000000000000000000000000000000000000000001,
      0xc800000008000000000000207b201020000116000000000000100e40))) (muxPair (Nat.blt k 184)
      ((oddMask 0x8000000000000000000000000000000000000000000000000000001),
      (h224 0x1 (oddMask 0xe0000000100000000000004008486200000000000000000000000001)))
      (muxPair (Nat.blt k 185) (0xc8000000000000000000000000000000000000000000001,
      0x94000000080000000000000000002120000000000000000000000001)
      (0x80000000000000000000000000000000000000000000001,
      (oddMask 0x100000000000000012080000000000000000000000000001))))))) (muxPair (Nat.blt k 197)
      (muxPair (Nat.blt k 191) (muxPair (Nat.blt k 188) (muxPair (Nat.blt k 187)
      ((oddMask 0x8000000000000000000000000000000000000000000000000000001),
      (h224 0x2 (oddMask 0x12000000010000000000000401208b000000000000000000000000001)))
      ((oddMask 0x190000000000000000000000000000000000000000000001),
      (h224 0x6 0x480000000480000000000000000131000000000a811a020020000001)))
      (muxPair (Nat.blt k 189) (0x80000000000000000000000000000000000000000000001,
      (h224 0x5 (oddMask 0x110000000000000000000004008482040000000000000000000000001)))
      (muxPair (Nat.blt k 190) (0x4800000000000001800c000000000000005800020000200,
      (oddMask 0x8000000000000000000000000000000000000000000000000000001))
      (0xc8000000000000000000000000000000000000000000001,
      (h224 0x80 (oddMask 0x100000000000000000002040000000000000000000000001))))))
      (muxPair (Nat.blt k 194) (muxPair (Nat.blt k 192)
      ((oddMask 0x100000000000000000000000000000000000000000000001),
      (h224 0x80 (oddMask 0x90000000000000004080000000000000000000000000001)))
      (muxPair (Nat.blt k 193) ((oddMask 0x8000000000000000000000000000000000000000000000000000001),
      (h224 0x100
  0x40000000800000000000000030018000000000001b1800130000401))
      (0xc8000000000000000000000000000000000000000000001,
      (h224 0x380 0x800000000000000000018000000000001b1800130000001)))) (muxPair (Nat.blt k 195)
      ((oddMask 0x100000000000000000000000000000000000000000000001),
      (h224 0xb00 0x80000000000000019040000000000000000000000000600)) (muxPair (Nat.blt k 196)
      ((oddMask 0x8000000000000000000000000000000000000000000000000000001),
      (h224 0x900 0xc8000000000000002041020000000000105800020000800))
      (0xc8000000000000000000000000000000000000000000001,
      (h224 0x180 0xc800000000000000000c8200000000001b4000110000001)))))) (muxPair (Nat.blt k 203)
      (muxPair (Nat.blt k 200) (muxPair (Nat.blt k 198)
      (0x80000000000000000000000000000000000000000000001,
      (h224 0x4100 0x40000000c800000000000001a040000000000000000000000000200))
      (muxPair (Nat.blt k 199) (0x4000000000000000000000000000000000000000000000000000001,
      (h224 0xcc00 0x80000000000000002041020000000000000000000000001))
      ((oddMask 0x190000000000000000000000000000000000000000000001),
      (h224 0x700 0xd020000000000100000000000001)))) (muxPair (Nat.blt k 201)
      (0x80000000000000000000000000000000000000000000001,
      (h224 0x3a80 0xc8000000000000003000000000000000000000000000c00)) (muxPair (Nat.blt k 202)
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x4 0xc00000000000000000000000003b0000000000d017c000010040000))
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x26 0x9c000000048000000000000000002120000000000000000000080001)))))
      (muxPair (Nat.blt k 206) (muxPair (Nat.blt k 204)
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x4980 0xc000f10120000005800020000000)) (muxPair (Nat.blt k 205)
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0xd00 0x40000000c80000000000000000018005482070001b1800130010000))
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x26f00 0x40000000c800000000000000000c0005f2203000005800020010001))))
      (muxPair (Nat.blt k 207) (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x1c900 0x8000000000000000204000057a207000000000000010001)) (muxPair (Nat.blt k 208)
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x47 0xc400000108000000000000200424102000000007801f820001000001))
      (0x301ffc000080000000000000046000040000000000000001,
      (h224 0x1a 0x1c00000300000000009040000001d23aa801f820002800001)))))))))
def gatesTier1Sym96At (k : ℕ) : ℕ × ℕ :=
    muxPair (Nat.blt k 26) (gatesTier1K3708At k) (muxPair (Nat.blt k 118)
    (gatesTier1Sym96TailLo k) (gatesTier1Sym96TailHi k))
def gatesTier1Sym96 (k : Fin nGatesTier1Sym96) : ℕ × ℕ := gatesTier1Sym96At k.val

theorem gatesTier1Sym96_wf :
    gatesWfCheck nGatesTier1Sym96 gatesTier1Sym96At = true := by decide +kernel

theorem gatesTier1Sym96_prefix26 : allTree 10 0 26 (fun k ↦ beqPair (gatesTier1Sym96At k)
    (gatesTier1K3708At k)) = true := by decide +kernel
def outs40ListTier1Sym96 : List ℕ :=
    [ 0x3c9ffc000080000000000000046000040000000000000001,
    (oddMask 0x100000000000000000000000000000000000000000000001),
    (h224 0x80004 0xc00000000000000000000000003b0000000000d017c000010000000),
    (h224 0x100026 0x9c000000048000000000000000002120000000000000000000000001),
    (h224 0x204980 0xc000000000000005800020000000),
    (h224 0x400d00 0x40000000c80000000000000000018000000000001b1800130000001),
    (h224 0x826f00 0x40000000c800000000000000000c000000000000005800020000000),
    (h224 0x101c900 0x80000000000000002040000000000000000000000000001),
    (h224 0x4c 0xc000000000000000000000076000000000116000000000000100e40),
    (h224 0x45 0xe40000000000000000000000220400000000b0800000000000000800),
    (h224 0xc300 0x4800000000000001a040000000000000000000000000200),
    (h224 0xd700 0x40000000c800000000000001a040000000000000000000000000200),
    (h224 0x4f980 0x4000000080000000000000019040000000000000000000000000e00),
    (h224 0x1ca80 0x80000000000000002041020000000000000000000000001),
    0x500000340000000000000000000000040000000000000001,
    (oddMask 0x80000000000000000000000000000000000000000000001),
    0x124450000034000000000000000200008104b9d5802d24010001,
    0x180c00000000000000000000000800000000281d800800000000,
    0x130e5000003400000000000000120002170411cd800524040000,
    0x82a50000034000000000000001e00038d0411cd8005240a0000,
    0x104400250000034000000000000000200000004a818002800000000,
    0x12680025000003400000000000000080003a5040800000000020000,
    0x3480020000000000000000000000120000000059f0001524000000,
    0x186800000000000000000000000001e0003a50091c8002524020000,
    0x2256040000000003c4000244001e00033d8011cd8005240a0000,
    0x81e500000340003c4000000001e00022b8411cd8005241a0040,
    0x23cc540000340003c4000000001e00029b0411cd8005241a0800,
    0x2c3a500000340000000000000000000000040000000000000200,
    (oddMask 0xa40004000000000000000000000000000000000000000000000001),
    0x22a0002000000000000000000000000000000000000000000000080,
    0x23080020000000000000000220000000000b0800000000000000501,
    0x8b0000540000340000000001040000000000040000000000000801,
    (oddMask 0x180000000000000000000000000000000000000000000001),
    (oddMask 0x190000000000000000000000000000000000000000000001),
    (oddMask 0xd93ff868010000000000000008c000000000000000000001),
    (oddMask 0x100000000000000000000000000000000000000000000001),
    (h224 0x6 0xd0000000000000000000000000002120000000000000000000000001),
    (h224 0x12 0x100000000c8000000000000000004820000000000000000000000001), (h224 0x2000047
  0xc400000108000000000000200424102000000007801f820000000001),
      (h224 0x400001a 0x1c00000300000000009040000001d23aa801f820000800001) ]
def outs40Tier1Sym96 (j : Fin 40) : ℕ := outs40ListTier1Sym96.getD j.val 0
abbrev nGatesTier1Sym96Rev144 : ℕ := 143

def gatesTier1Sym96RevTail4 (k : ℕ) : ℕ × ℕ :=
    (muxPair (Nat.blt k 141) (muxPair (Nat.blt k 140) (0x85300000000000000000000000000000000000001,
    0x5e70008700a00500000000000000000000000001) (0x2000087d40008700a00000000000000000000000000001,
    0x7d40000000a00000000000000000000000000001)) (muxPair (Nat.blt k 142)
    (0x7e40000000000500000000000000000000000001,
    (oddMask 0x8000007280000000000000000000000000000000000001))
    (0x8000080000000000000000000000000000000000000001,
    (oddMask 0xbff8107480000000000000000000000000000000000001))))
def gatesTier1Sym96Rev144At (k : ℕ) : ℕ × ℕ :=
    muxPair (Nat.blt k 139) (gatesTier1Sym96At k) (gatesTier1Sym96RevTail4 k)
def gatesTier1Sym96Rev144 (k : Fin nGatesTier1Sym96Rev144) : ℕ × ℕ :=
    gatesTier1Sym96Rev144At k.val
theorem gatesTier1Sym96Rev144_wf :
    gatesWfCheck nGatesTier1Sym96Rev144 gatesTier1Sym96Rev144At = true := by decide +kernel

theorem gatesTier1Sym96Rev144_prefix140 : allTree 10 0 139 (fun k ↦
    beqPair (gatesTier1Sym96Rev144At k) (gatesTier1Sym96At k)) = true := by decide +kernel
def envTier1Sym96 (c : Fin (2 ^ 41)) : ℕ :=
    xagEnv c.val nGatesTier1Sym96 gatesTier1Sym96 nGatesTier1Sym96 le_rfl
theorem wBit_t1a_eq_k3708_lt26 (c : Fin (2 ^ 41)) {msk : ℕ} (hMsk : Nat.blt msk (1 <<< (42 + 26)) =
    true) : wBit (envTier1Sym96 c) msk = wBit (envTier1K3708 c) msk :=
  wBit_eq_of_prefix (K := 26) (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl)
    (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl) gatesTier1Sym96_prefix26 hMsk

theorem wPack_t1a_eq_k3708_lt26 (c : Fin (2 ^ 41)) {ms : List ℕ}
    (hAll : (ms.all fun m ↦ Nat.blt m (1 <<< (42 + 26))) = true) : wPack (envTier1Sym96 c) ms =
    wPack (envTier1K3708 c) ms :=
  wPack_eq_of_prefix c.val (K := 26) (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl)
    (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl) gatesTier1Sym96_prefix26 hAll

def specT1a_03 (r : ℕ) : ℕ := specTier1_03 r + cond (Bool.and (bitAt r 8) (bitAt r 9)) 4096 0
def fastSpecT1a_03 (r : ℕ) : ℕ :=
    fastSpecTier1_03 r + cond (Bool.and (bitAt r 8) (bitAt r 9)) 4096 0
theorem fastSpecT1a_03_eq (r : ℕ) : fastSpecT1a_03 r = specT1a_03 r := by
  unfold fastSpecT1a_03 specT1a_03; rw [fastSpecTier1_03_eq]
def t1aIn03 : List ℕ :=
    [coinW 15, coinW 16, coinW 17, coinW 18, coinW 19, Nat.xor 1 (coinW 20), Nat.xor 1 (coinW 21),
    coinW 22, coinW 23, coinW 24]
def t1aOut03 : List ℕ :=
    [ 0x81000000000000010000, 0x3a5000000000000020000, 0x217000000000000040000,
    0x28000000000000080000, 0x1a6800000000000100000, (oddMask 0x161000000000000000001),
    0x11000000000000200001, 0x12800000000000400001, 0x10800000000000800000, 0x8000000000001000000,
    0x16000000000002000000, 0x1d23a00000000000800001, (oddMask 0x400000000000000001) ]
theorem t1aCert03 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 26 10 t1aIn03
      [
        (128, 0x501), (512, 0x400), (0x1000, 64), (0x800, 0x2000), (0x4000, 0x518b),
        (0x54d, 0x4000), (0x4000, 0x11b29), (17, 0x4000), (0x4000, 0x30021),
        (0x54010, 0x94008), (0xd401d, 0x1a800a), (0x1c4010, 0x384008),
        (0x534020, 0x598000), (0xf8019, 0x904000), (0x1600000, 0x1960000),
        (0x1290000, 0x2800000), (0x201c001, 0x4901101)
      ]
      [0x408002, 0x1d28004, 0x10b8008, 0x140010, 0xd34020, 0x584000, 0x88040, 0x94080, 0x84100,
          0x40200, 0xb0400, 0xe91d101, 0x1000]
      t1aOut03 careAllTier1 fastSpecT1a_03 = true := by decide +kernel
theorem wPack_t1aOut03 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut03 =
    specT1a_03 (wPack (envTier1Sym96 c) t1aIn03) :=
  (wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert03 c rfl).trans (fastSpecT1a_03_eq _)
def t1aIn04 : List ℕ :=
    [outW t1aOut03 0, outW t1aOut03 1, outW t1aOut03 2, outW t1aOut03 3, outW tier1Out02 0,
    outW tier1Out02 1, outW tier1Out02 2, outW tier1Out02 3, outW tier1Out02 4]
def t1aOut04 : List ℕ :=
    [ 0x200008100b9d5802d24010001, 0x800000000281d800800000000, 0x120002170011cd800524040000,
    0x1e00038d0011cd8005240a0000, 0x200000000a818002800000000, 0x80003a5000800000000020000,
    0x120000000059f0001524000000, 0x1e0003a50091c8002524020000 ]
theorem t1aCert04 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 55 9 t1aIn04
      [(513, 322), (513, 0x4de), (512, 0xd24), (513, 0x14a9)]
      [0x562, 0x1040, 0x2629, 0x3e35, 0x740, 0x1204, 0x26a1, 0x3d25]
      t1aOut04 careTier1_04 specTier1_04 = true := by decide +kernel
theorem wPack_t1aOut04 (c : Fin (2 ^ 41))
    (hCare : careTier1_04 (wPack (envTier1Sym96 c) t1aIn04) = true) :
    wPack (envTier1Sym96 c) t1aOut04 = specTier1_04 (wPack (envTier1Sym96 c) t1aIn04) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert04 c hCare
def maskT1a_05 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  cond d.1 2047 513

def specT1a_05 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  specTier1_05 r +
    cond (Nat.beq (((r / 4) % 64) / 2) 23) 512 0 +
    cond (Bool.and d.1 (Bool.or (Nat.beq (d.2.val / 8) 3) (Nat.beq (d.2.val / 8) 4))) 1024 0

def t1aIn05 : List ℕ :=
    [outW tier1Out02 5, outW tier1Out02 6, b8T1W 0, b8T1W 1, b8T1W 2, b8T1W 3, b8T1W 4, b8T1W 5]
def t1aOut05 : List ℕ :=
    [ 0x500000000000000000000000001, 0x2120000000000000000000000001,
    (oddMask 0x9040000000000000000000000001), 0x3b0000000000d017c000010000000,
    0x110200000000a811a020020000000, 0xc000000000000005800020000000, 0x18000000000001b1800130000000,
    0x1020000000000105800020000000, (oddMask 0x2040000000000000000000000001),
    (oddMask 0x200000000000000000000000001), (oddMask 0x1000000000000000000000000001) ]
theorem t1aCert05 :
    checkBlockMaskFastT1 nGatesTier1Sym96 gatesTier1Sym96At 59 8 t1aIn05
      [
        (256, 128), (64, 32), (273, 0x400), (768, 0xa80), (15, 521), (0x2000, 0x3001),
        (518, 0x7007), (0x630f, 0x9000), (4, 0x1b000), (0xc800, 0x2c200),
        (0x4c200, 0x600c3), (0xd201, 0x50324), (762, 0xd201)
      ]
      [0x5001, 0x21201, 0x48200, 0x3b01ce, 0x110304, 0xc0040, 0x18080, 0x10300, 0x10200, 0x1000,
          0x8000]
      t1aOut05 careTier1_05 maskT1a_05 specT1a_05 = true := by decide +kernel
theorem wPack_t1aOut05 (c : Fin (2 ^ 41))
    (hCare : careTier1_05 (wPack (envTier1Sym96 c) t1aIn05) = true) :
    (wPack (envTier1Sym96 c) t1aOut05) &&& maskT1a_05 (wPack (envTier1Sym96 c) t1aIn05) =
    (specT1a_05 (wPack (envTier1Sym96 c) t1aIn05)) &&& maskT1a_05 (wPack (envTier1Sym96 c)
    t1aIn05) := wPack_of_checkBlockMaskFastT1 gatesTier1Sym96_wf t1aCert05 c hCare
def maskT1a_06 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  maskTier1_06 r + 131072 + cond d.1 262144 0

def specT1a_06 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  specTier1_06 r +
    cond (Nat.ble 48 ((r / 4) % 64)) 131072 0 +
    cond (Bool.and d.1 (Bool.or (Nat.beq (d.2.val / 8) 3) (Nat.beq (d.2.val / 8) 4))) 262144 0

def t1aIn06 : List ℕ :=
    [outW t1aOut03 4, outW t1aOut03 5, coinW 5, coinW 6, coinW 7, coinW 8, coinW 9, coinW 10]
def t1aOut06 : List ℕ :=
    [ 0xa00000000000000000000000000001, 0x4240000000000000000000000000001,
    (oddMask 0x12080000000000000000000000000001), 0x76000000000116000000000000100e40,
    0x220400000000b0800000000000000800, 0x18000000000000000000000000000200,
    0x3000000000000000000000000000400, 0x2040000000000000000000000000800,
    (oddMask 0x4080000000000000000000000000001), 0x24400000000b0800000000000000001,
    0x1a6800000000000100040, 0x116000000000000100801, 512, 256, 128,
    0x220000000000b0800000000000000501, 0x1040000000000000000000000000800,
    (oddMask 0x80000000000000000000000000001), (oddMask 0x2000000000000000000000000000001) ]
theorem t1aCert06 :
    checkBlockMaskFastT1 nGatesTier1Sym96 gatesTier1Sym96At 72 8 t1aIn06
      [
        (128, 256), (32, 64), (273, 0x400), (768, 0xa80), (15, 521), (0x2000, 0x3001),
        (518, 0x7007), (0x630f, 0x9000), (4, 0x1b000), (0xc800, 0x2c200),
        (0x4c200, 0x600c3), (0xd201, 0x50324), (762, 0xd201)
      ]
      [0x5001, 0x21201, 0x48200, 0x3b01ce, 0x110304, 0xc0040, 0x18080, 0x10300, 0x10200, 0x12205,
          10, 263, 64, 32, 16, 0x1100a5, 0x8300, 512, 0x8000]
      t1aOut06 careTier1_06 maskT1a_06 specT1a_06 = true := by decide +kernel
theorem wPack_t1aOut06 (c : Fin (2 ^ 41))
    (hCare : careTier1_06 (wPack (envTier1Sym96 c) t1aIn06) = true) :
    (wPack (envTier1Sym96 c) t1aOut06) &&& maskT1a_06 (wPack (envTier1Sym96 c) t1aIn06) =
    (specT1a_06 (wPack (envTier1Sym96 c) t1aIn06)) &&& maskT1a_06 (wPack (envTier1Sym96 c)
    t1aIn06) := wPack_of_checkBlockMaskFastT1 gatesTier1Sym96_wf t1aCert06 c hCare
def t1aIn07 : List ℕ :=
    [outW t1aOut05 3, outW t1aOut05 4, outW t1aOut05 5, outW t1aOut06 3, outW t1aOut06 4,
    outW t1aOut06 5]
def t1aOut07 : List ℕ :=
    [ 0x1ee00c000000116000005800020100c40, (oddMask 0xe00000000000000000000000000000001) ]
theorem t1aCert07 :
    checkBlockMaskFastT1 nGatesTier1Sym96 gatesTier1Sym96At 85 6 t1aIn07
      [(48, 21), (72, 209), (37, 275), (72, 768)]
      [472, 0x700]
      t1aOut07 careAllTier1 maskTier1_07 specTier1_07 = true := by decide +kernel
theorem wPack_t1aOut07 (c : Fin (2 ^ 41)) :
    (wPack (envTier1Sym96 c) t1aOut07) &&& maskTier1_07 (wPack (envTier1Sym96 c) t1aIn07) =
    (specTier1_07 (wPack (envTier1Sym96 c) t1aIn07)) &&& maskTier1_07 (wPack (envTier1Sym96 c)
    t1aIn07) :=
  wPack_of_checkBlockMaskFastT1 gatesTier1Sym96_wf t1aCert07 c rfl

def careT1a_08 (r : ℕ) : Bool :=
  let a := r % 8
  let b := (r / 8) % 8
  Bool.and (Bool.and (Nat.blt a 6) (Nat.blt b 6))
    (b2BEq (bitAt r 8)
      (xor (Bool.or (Nat.beq a 3) (Nat.beq a 4))
           (Bool.or (Nat.beq b 3) (Nat.beq b 4))))

def specT1a_08 (r : ℕ) : ℕ := specTier1_08 (r % 256)

def t1aIn08 : List ℕ :=
    [outW t1aOut05 6, outW t1aOut05 7, outW t1aOut05 8, outW t1aOut06 6, outW t1aOut06 7,
    outW t1aOut06 8, outW t1aOut07 0, outW t1aOut07 1, Nat.xor (outW t1aOut05 10)
    (outW t1aOut06 18)]
def t1aOut08 : List ℕ :=
    [ 0x2000001020000000000000000000000001, (oddMask 0x10e00000000000000000000000000000001) ]
theorem t1aCert08 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 89 9 t1aIn08
      [(18, 180), (108, 0x4e0), (73, 0xc89), (0xa13, 127), (256, 0x2100)]
      [0x1009, 0x4100]
      t1aOut08 careT1a_08 specT1a_08 = true := by decide +kernel
theorem wPack_t1aOut08 (c : Fin (2 ^ 41)) (hCare : careT1a_08 (wPack (envTier1Sym96 c) t1aIn08) =
    true) : wPack (envTier1Sym96 c) t1aOut08 = specT1a_08 (wPack (envTier1Sym96 c) t1aIn08) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert08 c hCare
def t1aIn09 : List ℕ :=
    [outW t1aOut04 0, outW t1aOut04 1, outW t1aOut04 2, outW t1aOut04 3, outW t1aOut06 9,
    outW t1aOut06 10, outW t1aOut06 11, outW t1aOut06 12]
def t1aOut09 : List ℕ :=
    [ 0x4000000001e00038d0011cd8005240a0001, (oddMask 0x400000000000000000000000000000000001) ]
theorem t1aCert09 :
    checkBlockMaskFastT1 nGatesTier1Sym96 gatesTier1Sym96At 94 8 t1aIn09
      [(68, 96), (136, 672), (273, 0x721), (69, 0x623), (137, 0x1000), (0x2000, 0x3711)]
      [0x811, 0x4000]
      t1aOut09 careAllTier1 maskTier1_09 specTier1_09 = true := by decide +kernel
theorem wPack_t1aOut09 (c : Fin (2 ^ 41)) :
    (wPack (envTier1Sym96 c) t1aOut09) &&& maskTier1_09 (wPack (envTier1Sym96 c) t1aIn09) =
    (specTier1_09 (wPack (envTier1Sym96 c) t1aIn09)) &&& maskTier1_09 (wPack (envTier1Sym96 c)
    t1aIn09) :=
  wPack_of_checkBlockMaskFastT1 gatesTier1Sym96_wf t1aCert09 c rfl

def t1aIn10 : List ℕ :=
    [outW t1aOut04 4, outW t1aOut04 5, outW t1aOut04 6, outW t1aOut04 7, outW t1aOut06 13,
    outW t1aOut06 14, outW t1aOut06 15, outW t1aOut06 16, outW t1aOut09 0, outW t1aOut09 1]
def t1aOut10 : List ℕ :=
    [ 0x3c4000000001e00038d0011cd8005240a0001, (oddMask 0x60000000000000000000000000000000000001) ]
theorem t1aCert10 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 100 10 t1aIn10
      [
        (34, 544), (68, 0xa40), (136, 0x1b80), (272, 0x3b00), (0x2023, 0x3400),
        (0x4045, 0xc000), (137, 0x16000), (0x20000, 0x34110)
      ]
      [0x7a00, 0x60000]
      t1aOut10 careTier1_10 specTier1_10 = true := by decide +kernel
theorem wPack_t1aOut10 (c : Fin (2 ^ 41))
    (hCare : careTier1_10 (wPack (envTier1Sym96 c) t1aIn10) = true) :
    wPack (envTier1Sym96 c) t1aOut10 = specTier1_10 (wPack (envTier1Sym96 c) t1aIn10) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert10 c hCare
def specT1a_11 (r : ℕ) : ℕ :=
  let inTile := Bool.and (Bool.not (bitAt r 2)) (Bool.not (bitAt r 1))
  let knOk := Bool.and (bitAt r 0) (Bool.not (bitAt r 3))
  cond inTile 1 0 + cond knOk 2 0

def t1aIn11 : List ℕ := [outW tier1Out02 10, outW t1aOut03 11, outW tier1Out00 0, outW t1aOut03 12]
def t1aOut11 : List ℕ :=
    [ (oddMask 0x80000000000000000000000000000000000001),
    (oddMask 0x100000000000000000000000000000000000001) ]
theorem t1aCert11 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 108 4 t1aIn11
      [(9, 5), (2, 17)]
      [32, 64]
      t1aOut11 careAllTier1 specT1a_11 = true := by decide +kernel
theorem wPack_t1aOut11 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut11 =
    specT1a_11 (wPack (envTier1Sym96 c) t1aIn11) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert11 c rfl
def specSym_12 (r : ℕ) : ℕ :=
  cond (bitAt r 0)
    (let q5 := (r / 2) % 8
     let q31 := (r / 16) % 32
     cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4)) 1
       (cond (Nat.beq q31 25 && Nat.beq q5 4) 2
         (cond (Nat.ble 16 q31 && Nat.blt q31 24) 4
           (cond (Nat.beq q31 26 && Nat.beq q5 4) 8
             (cond (Nat.ble 28 q31) 16
               (cond (Nat.beq q31 27 && Nat.beq q5 4) 32
                 (cond (Nat.beq q31 27 && Nat.beq q5 3) 64 0))))))) 0

def t1aIn12 : List ℕ :=
    [outW t1aOut11 0, outW tier1Out02 7, outW tier1Out02 8, outW tier1Out02 9, outW t1aOut03 6,
    outW t1aOut03 7, outW t1aOut03 8, outW t1aOut03 9, outW t1aOut03 10]
def t1aOut12 : List ℕ :=
    [ (oddMask 0x7280000000000000000000000000000000000001),
    (oddMask 0x4000000000000000000000000000000000000001),
    (oddMask 0x600000000000000000000000000000000000001),
    (oddMask 0xa000000000000000000000000000000000000001),
    (oddMask 0x800000000000000000000000000000000000001),
    (oddMask 0x8000000000000000000000000000000000000001),
    (oddMask 0x80000000000000000000000000000000000000001) ]
theorem t1aCert12 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 110 9 t1aIn12
      [
        (2, 512), (0x400, 256), (0x800, 128), (0x1800, 16), (0x2000, 64), (0x6000, 32),
        (0x4000, 32), (0x3800, 64), (0x20000, 32), (0x40000, 8), (0x80000, 4)
      ]
      [0xe402, 0x8000, 0xc00, 0x14000, 0x1000, 0x10000, 0x100000]
      t1aOut12 careTier1Walk_12 specSym_12 = true := by decide +kernel
theorem wPack_t1aOut12 (c : Fin (2 ^ 41))
    (hCare : careTier1Walk_12 (wPack (envTier1Sym96 c) t1aIn12) = true) :
    wPack (envTier1Sym96 c) t1aOut12 = specSym_12 (wPack (envTier1Sym96 c) t1aIn12) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert12 c hCare
def fastSpec03x (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
    (cond (bitAt r 9) 0 3) 3) 3) 3) 3) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) (cond (bitAt r 9) 2 1) 1) 1) 1) 1)) (cond (bitAt r 4) 0 (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0)))
    (cond (bitAt r 3) (cond (bitAt r 4) 0 (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0)) (cond (bitAt r 4) 0 (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0))))
    (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 0 3) 3) 3) 3) 3) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 1) 1) 1) 1) 1))
    (cond (bitAt r 4) 0 (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
    (cond (bitAt r 9) 2 0) 0) 0) 0) 0))) (cond (bitAt r 3) (cond (bitAt r 4) 0 (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0))
    (cond (bitAt r 4) 0 (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
    (cond (bitAt r 9) 2 0) 0) 0) 0) 0))))) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
    (cond (bitAt r 9) 2 3) 3) 3) 3) 3) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) (cond (bitAt r 9) 0 1) 1) 1) 1) 1)) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0) 0))
    (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0) 0) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0) 0)))
    (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 3) 3) 3) 3) 3) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 0 1) 1) 1) 1) 1))
    (cond (bitAt r 4) (cond
  (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
      (cond (bitAt r 9) 2 0) 0) 0) 0) 0) 0)) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 2 0) 0) 0) 0) 0) 0)
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
      (cond (bitAt r 9) 2 0) 0) 0) 0) 0) 0))))
def fastSpec05Full (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x533 123) (cond (bitAt r 7) 880 59))
    (cond (bitAt r 6) (cond (bitAt r 7) 0x507 91) (cond (bitAt r 7) 155 27))) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 0x51f 107) (cond (bitAt r 7) 171 43)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x517 75) (cond (bitAt r 7) 139 11)))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 0x507 115) (cond (bitAt r 7) 179 51)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x50f 83) (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x517 99) (cond (bitAt r 7) 163 35)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x51f 67) (cond (bitAt r 7) 131 3))))) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x4f9 113) (cond (bitAt r 7) 657 49))
    (cond (bitAt r 6) (cond (bitAt r 7) 0x4d9 81) (cond (bitAt r 7) 145 17))) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 0x4e9 97) (cond (bitAt r 7) 161 33)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x4c9 65) (cond (bitAt r 7) 129 1)))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 0x4f1 69) (cond (bitAt r 7) 185 45)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x4d1 89) (cond (bitAt r 7) 153 25))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x4e1 105) (cond (bitAt r 7) 169 41)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x4c1 73) (cond (bitAt r 7) 137 9)))))) (cond (bitAt r 2) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 329 123)
    (cond (bitAt r 7) 0x6d4 59)) (cond (bitAt r 6) (cond (bitAt r 7) 365 91)
    (cond (bitAt r 7) 155 27))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 365 107)
    (cond (bitAt r 7) 171 43)) (cond (bitAt r 6) (cond (bitAt r 7) 365 75)
    (cond (bitAt r 7) 139 11)))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 365 115) (cond (bitAt r 7) 179 51)) (cond (bitAt r 6)
    (cond (bitAt r 7) 365 83) (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 365 99) (cond (bitAt r 7) 163 35)) (cond (bitAt r 6) (cond (bitAt r 7) 365 67)
    (cond (bitAt r 7) 131 3))))) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 321 123) (cond (bitAt r 7) 0x6d4 59)) (cond (bitAt r 6)
    (cond
  (bitAt r 7) 357 91) (cond (bitAt r 7) 155 27))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 357 107) (cond (bitAt r 7) 171 43)) (cond (bitAt r 6)
      (cond (bitAt r 7) 357 75) (cond (bitAt r 7) 139 11)))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 357 115) (cond (bitAt r 7) 179 51)) (cond (bitAt r 6)
      (cond (bitAt r 7) 357 83) (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 357 99) (cond (bitAt r 7) 163 35)) (cond (bitAt r 6)
      (cond (bitAt r 7) 357 67) (cond (bitAt r 7) 131 3))))))) (cond (bitAt r 1) (cond (bitAt r 2)
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 123) (cond (bitAt r 7) 0x6fc 59)) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 91) (cond (bitAt r 7) 155 27))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 107) (cond (bitAt r 7) 171 43)) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 75) (cond (bitAt r 7) 139 11)))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 375 115) (cond (bitAt r 7) 179 51)) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 83) (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 99) (cond (bitAt r 7) 163 35)) (cond (bitAt r 6)
      (cond (bitAt r 7) 375 67) (cond (bitAt r 7) 131 3))))) (cond (bitAt r 3) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 337 123) (cond (bitAt r 7) 0x6fc 59))
      (cond (bitAt r 6) (cond (bitAt r 7) 349 91) (cond (bitAt r 7) 155 27))) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 349 107) (cond (bitAt r 7) 171 43)) (cond (bitAt r 6)
      (cond (bitAt r 7) 349 75) (cond (bitAt r 7) 139 11)))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 349 115) (cond (bitAt r 7) 179 51)) (cond (bitAt r 6)
      (cond (bitAt r 7) 349 83) (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 349 99) (cond (bitAt r 7) 163 35)) (cond (bitAt r 6)
      (cond (bitAt r 7) 349 67) (cond (bitAt r 7) 131 3)))))) (cond (bitAt r 2) (cond (bitAt r 3)
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x539 123)
      (cond (bitAt r 7) 864 59)) (cond (bitAt r 6) (cond (bitAt r 7) 0x519 91)
      (cond (bitAt r 7) 155 27))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x529 107)
      (cond (bitAt r 7) 171 43)) (cond (bitAt r 6) (cond (bitAt r 7) 0x509 75)
      (cond (bitAt r 7) 139 11)))) (cond
  (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x531 115)
      (cond (bitAt r 7) 179 51)) (cond (bitAt r 6) (cond (bitAt r 7) 0x511 83)
      (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x521 99)
      (cond (bitAt r 7) 163 35)) (cond (bitAt r 6) (cond (bitAt r 7) 0x501 67)
      (cond (bitAt r 7) 131 3))))) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x4f9 123) (cond (bitAt r 7) 697 59)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x4d9 91) (cond (bitAt r 7) 155 27))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x4e9 107) (cond (bitAt r 7) 171 43)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x4c9 75) (cond (bitAt r 7) 139 11)))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x4f1 115) (cond (bitAt r 7) 179 51)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x4d1 83) (cond (bitAt r 7) 147 19))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x4e1 99) (cond (bitAt r 7) 163 35)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x4c1 67) (cond (bitAt r 7) 131 3)))))))
theorem t1bCert05Full :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 59 8 t1aIn05
      [(256, 128), (64, 32), (273, 0x400), (768, 0xa80), (15, 521), (0x2000, 0x3001), (518, 0x7007),
          (0x630f, 0x9000), (4, 0x1b000), (0xc800, 0x2c200), (0x4c200, 0x600c3), (0xd201, 0x50324),
          (762, 0xd201)] [0x5001, 0x21201, 0x48200, 0x3b01ce, 0x110304, 0xc0040, 0x18080, 0x10300,
          0x10200, 0x1000, 0x8000]
      t1aOut05 careAllTier1 fastSpec05Full = true := by decide +kernel
theorem wPack_t1bOut05Full (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut05 =
    fastSpec05Full (wPack (envTier1Sym96 c) t1aIn05) :=
        wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1bCert05Full c rfl
def fastSpec05x (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) 0 (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6)
    (cond (bitAt r 7) 0 1) 1)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
    (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1))
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6)
    (cond (bitAt r 7) 0 1) 1))))) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0)))) 0)) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))) 0) (cond (bitAt r 2) 0 (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
    (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1))) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6)
    (cond (bitAt r 7) 0 1) 1)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
    (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1))))))
def t1bOut05x : List ℕ := [ (oddMask 0x400000000000000000000000001) ]
theorem t1bCert05x :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 59 8 t1aIn05
      [(256, 128), (64, 32), (273, 0x400), (768, 0xa80), (15, 521), (0x2000, 0x3001), (518, 0x7007),
          (0x630f, 0x9000), (4, 0x1b000), (0xc800, 0x2c200), (0x4c200, 0x600c3), (0xd201, 0x50324),
          (762, 0xd201)] [0x2000]
      t1bOut05x careAllTier1 fastSpec05x = true := by decide +kernel
theorem wPack_t1bOut05x (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1bOut05x =
    fastSpec05x (wPack (envTier1Sym96 c) t1aIn05) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1bCert05x c rfl
def fastSpec06Full (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x77333 0x787b)
    (cond (bitAt r 7) 0x17370 0xf83b)) (cond (bitAt r 6) (cond (bitAt r 7) 0x7e307 0x685b)
    (cond (bitAt r 7) 0x1609b 0xe81b))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x7d31f 0x586b) (cond (bitAt r 7) 0x150ab 0xd82b)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x7c317 0x484b) (cond (bitAt r 7) 0x1408b 0xc80b)))) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x7b307 0x3873)
    (cond (bitAt r 7) 0x130b3 0xb833)) (cond (bitAt r 6) (cond (bitAt r 7) 0x7a30f 0x2853)
    (cond (bitAt r 7) 0x12093 0xa813))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x79317 0x1863) (cond (bitAt r 7) 0x110a3 0x9823)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x7831f 0x843) (cond (bitAt r 7) 0x10083 0x8803))))) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x774f9 0x7e71)
    (cond (bitAt r 7) 0x17691 0xfe31)) (cond (bitAt r 6) (cond (bitAt r 7) 0x764d9 0x6e51)
    (cond (bitAt r 7) 0x16691 0xee11))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x754e9 0x5e61) (cond (bitAt r 7) 0x156a1 0xde21)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x744c9 0x4e41) (cond (bitAt r 7) 0x14681 0xce01)))) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x734f1 0xbe45)
    (cond (bitAt r 7) 0x136b9 0x3e2d)) (cond (bitAt r 6) (cond (bitAt r 7) 0x724d1 0x2e59)
    (cond (bitAt r 7) 0x12699 0xae19))) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x714e1 0x1e69) (cond (bitAt r 7) 0x116a9 0x9e29)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x704c1 0xe49) (cond (bitAt r 7) 0x10689 0x8e09)))))) (cond (bitAt r 2)
    (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x2fb49 0x727b) (cond (bitAt r 7) 0x47ad4 0xf23b)) (cond (bitAt r 6)
    (cond (bitAt r 7) 0x2eb6d 0x625b) (cond (bitAt r 7) 0x16a9b 0xe21b))) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 0x25b6d 0x526b) (cond (bitAt r 7) 0x15aab 0xd22b))
    (cond (bitAt r 6) (cond (bitAt r 7) 0x24b6d 0x424b) (cond (bitAt r 7) 0x14a8b 0xc20b))))
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x2bb6d 0x3273)
    (cond (bitAt r 7) 0x13ab3 0xb233)) (cond (bitAt r 6) (cond (bitAt r 7) 0x2ab6d 0x2253)
    (cond (bitAt r 7) 0x12a93 0xa213)))
  (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x21b6d 0x1263)
      (cond (bitAt r 7) 0x11aa3 0x9223)) (cond (bitAt r 6) (cond (bitAt r 7) 0x20b6d 579)
      (cond (bitAt r 7) 0x10a83 0x8203))))) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x2fd41 0x767b) (cond (bitAt r 7) 0x47ed4 0xf63b))
      (cond (bitAt r 6) (cond (bitAt r 7) 0x2ed65 0x665b) (cond (bitAt r 7) 0x16e9b 0xe61b)))
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x25d65 0x566b)
      (cond (bitAt r 7) 0x15eab 0xd62b)) (cond (bitAt r 6) (cond (bitAt r 7) 0x24d65 0x464b)
      (cond (bitAt r 7) 0x14e8b 0xc60b)))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x2bd65 0x3673) (cond (bitAt r 7) 0x13eb3 0xb633)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x2ad65 0x2653) (cond (bitAt r 7) 0x12e93 0xa613))) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x21d65 0x1663) (cond (bitAt r 7) 0x11ea3 0x9623))
      (cond (bitAt r 6) (cond (bitAt r 7) 0x20d65 0x643) (cond (bitAt r 7) 0x10e83 0x8603)))))))
      (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x27d77 0x747b) (cond (bitAt r 7) 0x47cfc 0xf43b))
      (cond (bitAt r 6) (cond (bitAt r 7) 0x26d77 0x645b) (cond (bitAt r 7) 0x16c9b 0xe41b)))
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x2dd77 0x546b)
      (cond (bitAt r 7) 0x15cab 0xd42b)) (cond (bitAt r 6) (cond (bitAt r 7) 0x2cd77 0x444b)
      (cond (bitAt r 7) 0x14c8b 0xc40b)))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x23d77 0x3473) (cond (bitAt r 7) 0x13cb3 0xb433)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x22d77 0x2453) (cond (bitAt r 7) 0x12c93 0xa413))) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x29d77 0x1463) (cond (bitAt r 7) 0x11ca3 0x9423))
      (cond (bitAt r 6) (cond (bitAt r 7) 0x28d77 0x443) (cond (bitAt r 7) 0x10c83 0x8403)))))
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x27b51 0x707b) (cond (bitAt r 7) 0x478fc 0xf03b)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x26b5d 0x605b) (cond (bitAt r 7) 0x1689b 0xe01b))) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x2db5d 0x506b) (cond (bitAt r 7) 0x158ab 0xd02b))
      (cond (bitAt r 6) (cond (bitAt r 7) 0x2cb5d 0x404b) (cond (bitAt r 7) 0x1488b 0xc00b))))
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x23b5d 0x3073)
  (cond (bitAt r 7) 0x138b3 0xb033)) (cond (bitAt r 6) (cond (bitAt r 7) 0x22b5d 0x2053)
      (cond (bitAt r 7) 0x12893 0xa013))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x29b5d 0x1063) (cond (bitAt r 7) 0x118a3 0x9023)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x28b5d 67) (cond (bitAt r 7) 0x10883 0x8003)))))) (cond (bitAt r 2)
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x77539 0x7e7b) (cond (bitAt r 7) 0x1f560 0xfe3b)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x76519 0x6e5b) (cond (bitAt r 7) 0x1669b 0xee1b))) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 0x75529 0x5e6b) (cond (bitAt r 7) 0x156ab 0xde2b))
      (cond (bitAt r 6) (cond (bitAt r 7) 0x74509 0x4e4b) (cond (bitAt r 7) 0x1468b 0xce0b))))
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x73531 0x3e73)
      (cond (bitAt r 7) 0x136b3 0xbe33)) (cond (bitAt r 6) (cond (bitAt r 7) 0x72511 0x2e53)
      (cond (bitAt r 7) 0x12693 0xae13))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x71521 0x1e63) (cond (bitAt r 7) 0x116a3 0x9e23)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x70501 0xe43) (cond (bitAt r 7) 0x10683 0x8e03))))) (cond (bitAt r 3)
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x772f9 0x787b)
      (cond (bitAt r 7) 0x170b9 0xf83b)) (cond (bitAt r 6) (cond (bitAt r 7) 0x762d9 0x685b)
      (cond (bitAt r 7) 0x1609b 0xe81b))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x752e9 0x586b) (cond (bitAt r 7) 0x150ab 0xd82b)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x742c9 0x484b) (cond (bitAt r 7) 0x1408b 0xc80b)))) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0x732f1 0x3873)
      (cond (bitAt r 7) 0x130b3 0xb833)) (cond (bitAt r 6) (cond (bitAt r 7) 0x722d1 0x2853)
      (cond (bitAt r 7) 0x12093 0xa813))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x712e1 0x1863) (cond (bitAt r 7) 0x110a3 0x9823)) (cond (bitAt r 6)
      (cond (bitAt r 7) 0x702c1 0x843) (cond (bitAt r 7) 0x10083 0x8803)))))))
theorem t1bCert06Full :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 72 8 t1aIn06
      [(128, 256), (32, 64), (273, 0x400), (768, 0xa80), (15, 521), (0x2000, 0x3001), (518, 0x7007),
          (0x630f, 0x9000), (4, 0x1b000), (0xc800, 0x2c200), (0x4c200, 0x600c3), (0xd201, 0x50324),
          (762, 0xd201)] [0x5001, 0x21201, 0x48200, 0x3b01ce, 0x110304, 0xc0040, 0x18080, 0x10300,
          0x10200, 0x12205, 10, 263, 64, 32, 16, 0x1100a5, 0x8300, 512, 0x8000]
      t1aOut06 careAllTier1 fastSpec06Full = true := by decide +kernel
theorem wPack_t1bOut06Full (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut06 =
    fastSpec06Full (wPack (envTier1Sym96 c) t1aIn06) :=
        wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1bCert06Full c rfl
def fastSpec06x (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) (cond (bitAt r 7) 0 1))
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) (cond (bitAt r 7) 0 1))
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))))) (cond (bitAt r 2) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1)
    (cond (bitAt r 7) 0 1)) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1)
    (cond (bitAt r 7) 0 1)) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
    (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))))) (cond (bitAt r 1)
    (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 0 1) (cond (bitAt r 7) 0 1)) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond
  (bitAt r 6) (cond (bitAt r 7) 1 0) 0))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 0 1) 1) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))))
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1)
      (cond (bitAt r 7) 0 1)) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))))) (cond (bitAt r 2)
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1)
      (cond (bitAt r 7) 0 1)) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))) (cond (bitAt r 3)
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1)
      (cond (bitAt r 7) 0 1)) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)))
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 0 1) 1)
      (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 1 0) 0) (cond (bitAt r 6) (cond (bitAt r 7) 1 0) 0))))))
def t1bOut06x : List ℕ := [ (oddMask 0x580000000000000000000000000001) ]
theorem t1bCert06x :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 72 8 t1aIn06
      [(128, 256), (32, 64), (273, 0x400), (768, 0xa80), (15, 521), (0x2000, 0x3001), (518, 0x7007),
          (0x630f, 0x9000), (4, 0x1b000), (0xc800, 0x2c200), (0x4c200, 0x600c3), (0xd201, 0x50324),
          (762, 0xd201)] [0x1600]
      t1bOut06x careAllTier1 fastSpec06x = true := by decide +kernel
theorem wPack_t1bOut06x (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1bOut06x =
    fastSpec06x (wPack (envTier1Sym96 c) t1aIn06) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1bCert06x c rfl
def fastSpec08x (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
    (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
    (cond (bitAt r 7) 3 1))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
    (cond (bitAt r 7) 3 1)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
    (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)))
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)
    (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
    (cond (bitAt r 7) 2 0))))) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 3 1) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)))
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
    (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 3 1)
    (cond (bitAt r 7) 2 0)))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0))
    (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0))) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1))))))
    (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) 3 1) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0))) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7)
    (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 3 1) (cond (bitAt r 7) 2 0))))
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 3 1) 1) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)) (cond (bitAt r 6)
    (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0))) (cond (bitAt r 5) (cond
  (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 0 2) 0) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0))))) (cond (bitAt r 3)
      (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6)
      (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 3 1))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 3 1)) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)))) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0))
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0) (cond (bitAt r 7)
      (cond (bitAt r 8) 0 2) 0))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 3 1) 1) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)) (cond (bitAt r 6)
      (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0))))))) (cond (bitAt r 1) (cond (bitAt r 2)
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 2 0)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0))) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1))
      (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0)))) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 3 1))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 3 1)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0))))) (cond (bitAt r 3) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)
      (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 2 0))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 2 0)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 3 1) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6) (cond
  (bitAt r 7) (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)))
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 3 1)
      (cond (bitAt r 7) 2 0)))))) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 2 0))) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 2 0)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)
      (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 3 1) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)))
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 3 1)
      (cond (bitAt r 7) 2 0))))) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 2 0)) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1) (cond (bitAt r 7) (cond (bitAt r 8) 3 1) 1)))
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)
      (cond (bitAt r 7) (cond (bitAt r 8) 0 2) 0)) (cond (bitAt r 6) (cond (bitAt r 7) 2 0)
      (cond (bitAt r 7) 2 0)))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0))
      (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 3 1))) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 2 0) (cond (bitAt r 7) 3 1)) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0) (cond (bitAt r 7) (cond (bitAt r 8) 2 0) 0)))))))
def t1bOut08x : List ℕ :=
    [ (oddMask 0x2000000000000000000000000000000001),
    (oddMask 0x10000000000000000000000000000000001) ]
theorem t1bCert08x :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 89 9 t1aIn08
      [(18, 180), (108, 0x4e0), (73, 0xc89), (0xa13, 127), (256, 0x2100)] [0x800, 0x4000]
      t1bOut08x careAllTier1 fastSpec08x = true := by decide +kernel
theorem wPack_t1bOut08x (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1bOut08x =
    fastSpec08x (wPack (envTier1Sym96 c) t1aIn08) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1bCert08x c rfl
def specT1b_12b (r : ℕ) : ℕ := cond (bitAt r 0) (cond (Bool.not (bitAt r 1)) 1 2) 0
def t1aIn12b : List ℕ := [outW t1aOut12 5, outW t1aOut06 18]
def t1aOut12b : List ℕ :=
    [ (oddMask 0x108000000000000000000000000000000000000001),
    (oddMask 0x100000000000000000000000000000000000000001) ]
theorem t1aCert12b :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 121 2 t1aIn12b
      [(4, 2)] [10, 8]
      t1aOut12b careAllTier1 specT1b_12b = true := by decide +kernel
theorem wPack_t1aOut12b (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut12b =
    specT1b_12b (wPack (envTier1Sym96 c) t1aIn12b) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert12b c rfl
def t1aEff12 : List ℕ :=
    [outW t1aOut12 0, outW t1aOut12 1, outW t1aOut12 2, outW t1aOut12 3, Nat.xor (outW t1aOut12 4)
    (outW t1aOut12b 0), outW t1aOut12b 1, outW t1aOut12 6]
def fastSpec13 (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 737 0x561) 0x4e1)
    (cond (bitAt r 7) (cond (bitAt r 8) 737 0x561) 0x4e1)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 737 0x561) 0x4e1) 0x4e1)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 737 0x561) 0x461) (cond (bitAt r 7)
    (cond (bitAt r 8) 737 0x561) 0x461)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 737 0x561) 0x461) 0x461))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 673 0x521) 0x4a1) (cond (bitAt r 7)
    (cond (bitAt r 8) 673 0x521) 0x4a1)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 673 0x521) 0x4a1) 0x4a1)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 673 0x521) 0x421) (cond (bitAt r 7)
    (cond (bitAt r 8) 673 0x521) 0x421)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 673 0x521) 0x421) 0x421)))) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 705 0x541) 0x4c1)
    (cond (bitAt r 7) (cond (bitAt r 8) 705 0x541) 0x4c1)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 705 0x541) 0x4c1) 0x4c1)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 705 0x541) 0x441) (cond (bitAt r 7)
    (cond (bitAt r 8) 705 0x541) 0x441)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 705 0x541) 0x441) 0x441))) (cond (bitAt r 4) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 641 0x501) 0x481) (cond (bitAt r 7)
    (cond (bitAt r 8) 641 0x501) 0x481)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 641 0x501) 0x481) 0x481)) (cond (bitAt r 5) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 641 0x501) 0x401) (cond (bitAt r 7)
    (cond (bitAt r 8) 641 0x501) 0x401)) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 641 0x501) 0x401) 0x401))))) (cond (bitAt r 2) (cond (bitAt r 3)
    (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
    (cond (bitAt r 8) 737 0x561) 0x4e1) (cond (bitAt r 7) 0x4e2 0x4e1)) (cond (bitAt r 6)
    (cond (bitAt r 7) (cond (bitAt r 8) 737 0x561) 0x4e1) 0x4e1)) (cond (bitAt r 5)
    (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 737 0x561) 0x461)
    (cond (bitAt r 7) 0x462 0x461)) (cond (bitAt r 6) (cond
  (bitAt r 7) (cond (bitAt r 8) 737 0x561) 0x461) 0x461))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 673 0x521) 0x4a1)
      (cond (bitAt r 7) 0x4a2 0x4a1)) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 673 0x521) 0x4a1) 0x4a1)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 673 0x521) 0x421) (cond (bitAt r 7) 0x422 0x421))
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 673 0x521) 0x421) 0x421))))
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 705 0x541) 0x4c1) (cond (bitAt r 7) 0x4c2 0x4c1)) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 705 0x541) 0x4c1) 0x4c1)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 705 0x541) 0x441)
      (cond (bitAt r 7) 0x442 0x441)) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 705 0x541) 0x441) 0x441))) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 641 0x501) 0x481)
      (cond (bitAt r 7) 0x482 0x481)) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 641 0x501) 0x481) 0x481)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 641 0x501) 0x401) (cond (bitAt r 7) 0x402 0x401))
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 641 0x501) 0x401) 0x401))))))
      (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0x568 0x5f0) 993) (cond (bitAt r 7)
      (cond (bitAt r 8) 736 0x560) 993)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
      (cond (bitAt r 9) 736 740) (cond (bitAt r 9) 736 740)) 993) 993)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 738 0x562) 865) (cond (bitAt r 7)
      (cond (bitAt r 8) 736 0x560) 865)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
      (cond (bitAt r 9) 608 612) (cond (bitAt r 9) 608 612)) 865) 865))) (cond (bitAt r 4)
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 0x530 0x5a8) 929)
      (cond (bitAt r 7) (cond (bitAt r 8) 672 0x520) 929)) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) (cond (bitAt r 9) 672 676) (cond (bitAt r 9) 672 676)) 929) 929))
      (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 674 0x522) 801)
      (cond (bitAt r 7) (cond (bitAt r 8) 672 0x520) 801)) (cond (bitAt r 6) (cond (bitAt
  r 7) (cond (bitAt r 8) (cond (bitAt r 9) 544 548) (cond (bitAt r 9) 544 548)) 801) 801))))
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 0x548 0x5d0) 961) (cond (bitAt r 7) (cond (bitAt r 8) 704 0x540) 961))
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 704 708)
      (cond (bitAt r 9) 704 708)) 961) 961)) (cond (bitAt r 5) (cond (bitAt r 6) (cond (bitAt r 7)
      (cond (bitAt r 8) 706 0x542) 833) (cond (bitAt r 7) (cond (bitAt r 8) 704 0x540) 833))
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) (cond (bitAt r 9) 576 580)
      (cond (bitAt r 9) 576 580)) 833) 833))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) (cond (bitAt r 8) 0x510 0x588) 897) (cond (bitAt r 7)
      (cond (bitAt r 8) 640 0x500) 897)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
      (cond (bitAt r 9) 640 644) (cond (bitAt r 9) 640 644)) 897) 897)) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8) 642 0x502) 769) (cond (bitAt r 7)
      (cond (bitAt r 8) 640 0x500) 769)) (cond (bitAt r 6) (cond (bitAt r 7) (cond (bitAt r 8)
      (cond (bitAt r 9) 512 516) (cond (bitAt r 9) 512 516)) 769) 769))))) (cond (bitAt r 2)
      (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 484 993) (cond (bitAt r 7) 994 993)) (cond (bitAt r 6)
      (cond (bitAt r 7) 228 993) 993)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 356 865) (cond (bitAt r 7) 866 865)) (cond (bitAt r 6)
      (cond (bitAt r 7) 100 865) 865))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 420 929) (cond (bitAt r 7) 930 929)) (cond (bitAt r 6)
      (cond (bitAt r 7) 164 929) 929)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 292 801) (cond (bitAt r 7) 802 801)) (cond (bitAt r 6)
      (cond (bitAt r 7) 36 801) 801)))) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5)
      (cond (bitAt r 6) (cond (bitAt r 7) 452 961) (cond (bitAt r 7) 962 961)) (cond (bitAt r 6)
      (cond (bitAt r 7) 196 961) 961)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 324 833) (cond (bitAt r 7) 834 833)) (cond (bitAt r 6)
      (cond (bitAt r 7) 68 833) 833))) (cond (bitAt r 4) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 388 897) (cond (bitAt r 7) 898 897)) (cond (bitAt r 6)
      (cond (bitAt r 7) 132 897) 897)) (cond (bitAt r 5) (cond (bitAt r 6)
      (cond (bitAt r 7) 260 769) (cond (bitAt r
  7) 770 769)) (cond (bitAt r 6) (cond (bitAt r 7) 4 769) 769))))))
def t1aOut13 : List ℕ :=
    [ 0x46000000000000000000001, 0xc1e000000000000000100000, (oddMask 0x830000000000000000000001),
    0x1020020000000000000080000, 0x1c1a020000000000000180000, 0x40000, 0x80000,
    (oddMask 0x1e20240000000000000000001), 0x548207000000000000010001, 0x5f2203000000000000010001,
    0x57a207000000000000010000 ]
def fastSpec13_of_in03 (r : ℕ) : ℕ := fastSpec13 (Nat.xor (r % 256) 96 + 256 * fastSpec03x r)
theorem t1aCert13 : checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 26 10 t1aIn03
    [(128, 0x501), (512, 0x400), (0x1000, 64), (0x800, 0x2000), (0x4000, 0x518b), (0x54d, 0x4000),
        (0x4000, 0x11b29), (17, 0x4000), (0x4000, 0x30021), (0x54010, 0x94008), (0xd401d, 0x1a800a),
        (0x1c4010, 0x384008),
     (0x534020, 0x598000), (0xf8019, 0x904000), (0x1600000, 0x1960000), (0x1290000, 0x2800000),
         (0x201c001, 0x4901101), (256, 129), (0x10000100, 65), (0x10000000, 3), (0x40000000, 65),
         (0x2008004, 0xa0000000),
     (0x110000000, 2), (0x40020000, 0x18006), (0x400140000, 0x150900000),
         (0x400000021, 0x150900000), (0x480000000, 0x800900041), (0x800100001, 0x150000020),
         (0x100100010, 0x60d0100030)]
    [0x230000001, 0x60f0000020, 0x20c0000000, 0x8100100010, 0xe0d0100030, 8, 16, 0x7880900000,
        0x2a41038003, 0x2f91018003, 0x2bd1038002] t1aOut13 careAllTier1 fastSpec13_of_in03 =
        true := by decide +kernel
theorem wPack_t1aOut13 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut13 =
    fastSpec13_of_in03 (wPack (envTier1Sym96 c) t1aIn03) :=
        wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert13 c rfl
def wKnP13 : ℕ :=
    Nat.xor (Nat.xor (outW t1aOut13 1) (outW t1aOut13 2)) (Nat.xor (outW t1aOut13 3)
    (outW t1aOut13 4))
def wKnUbXorKnP13 : ℕ := Nat.xor (Nat.xor (outW t1aOut13 1) (outW t1aOut13 2)) (outW t1aOut13 3)
def specT1b_14 (r : ℕ) : ℕ :=
  let g0 := Bool.and (bitAt r 0) (bitAt r 1)
  let g1 := Bool.and (bitAt r 0) (bitAt r 2)
  let g2 := Bool.and (bitAt r 3) (bitAt r 4)
  let g3 := Bool.and g2 (bitAt r 5)
  let g4 := Bool.and (xor g0 g1) (bitAt r 6)
  let g5 := Bool.and (xor (bitAt r 0) (xor g0 g1)) (bitAt r 7)
  cond g0 1 0 + cond g1 2 0 + cond g2 4 0 + cond g3 8 0 + cond g4 16 0 + cond g5 32 0

def t1aIn14 : List ℕ :=
    [outW t1aOut12 6, outW tier1Out02 5, outW tier1Out02 6, wKnP13, coinW 5,
    Nat.xor wKnUbXorKnP13 (outW t1bOut06x 0), Nat.xor (coinW 6) (Nat.xor (outW t1bOut05x 0)
    (outW t1bOut08x 1)), Nat.xor (coinW 29) (outW t1bOut08x 0)]
def t1aOut14 : List ℕ :=
    [ (oddMask 0x200000000000000000000000000000000000000001),
    (oddMask 0x400000000000000000000000000000000000000001),
    (oddMask 0x800000000000000000000000000000000000000001),
    (oddMask 0x1000000000000000000000000000000000000000001),
    (oddMask 0x2000000000000000000000000000000000000000001),
    (oddMask 0x4000000000000000000000000000000000000000001) ]
theorem t1aCert14 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 122 8 t1aIn14
      [(2, 4), (2, 8), (16, 32), (0x800, 64), (0x600, 128), (0x602, 256)]
          [512, 0x400, 0x800, 0x1000, 0x2000, 0x4000]
      t1aOut14 careAllTier1 specT1b_14 = true := by decide +kernel
theorem wPack_t1aOut14 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut14 =
    specT1b_14 (wPack (envTier1Sym96 c) t1aIn14) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert14 c rfl
def cmpRhsBitT1aLo (i : ℕ) : ℕ :=
  let v1 := xorMaskedConstT1 (outW t1aOut12 1) 1452 i 0
  let v2 := xorMaskedConstT1 (outW t1aOut12 3) 1750 i v1
  let v3 := xorMaskedConstT1 (outW t1aOut12 5) 401 i v2
  let v4 := xorMaskedConstT1 (outW t1aOut12 6) 148 i v3
  let v5 := xorMaskedConstT1 (outW t1aOut14 0) 1422 i v4
  let v6 := xorMaskedConstT1 (outW t1aOut14 1) 1896 i v5
  xorMaskedConstT1 (outW t1aOut14 2) 128 i v6

def cmpRhsBitT1aW (i : ℕ) : ℕ :=
  let v7 := xorMaskedConstT1 (outW t1aOut14 3) 169 i (cmpRhsBitT1aLo i)
  let v8 := xorMaskedConstT1 (outW t1aOut14 4) 642 i v7
  let v9 := xorMaskedConstT1 (outW t1aOut14 5) 1 i v8
  let v10 := xorMaskedConstT1 (outW t1aOut13 1) 306 i v9
  let vy1 := xorMaskedConstT1 (outW t1aOut13 2) 487 i v10
  let vy2 := xorMaskedConstT1 (outW t1aOut13 3) 400 i vy1
  xorMaskedConstT1 (outW t1aOut13 4) 305 i vy2

def specT1b_16 (r : ℕ) : ℕ := cond (Nat.blt (r % 32) ((r / 32) % 32)) 1 0

def t1aIn16 : List ℕ :=
    [v23T1W.getD 12 0, v23T1W.getD 13 0, v23T1W.getD 14 0, v23T1W.getD 15 0, v23T1W.getD 16 0,
    cmpRhsBitT1aW 0, cmpRhsBitT1aW 1, cmpRhsBitT1aW 2, cmpRhsBitT1aW 3, cmpRhsBitT1aW 4]
def t1aOut16 : List ℕ := [ (oddMask 0xf8000000000000000000000000000000000000000001) ]
theorem t1aCert16 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 128 10 t1aIn16
      [(66, 64), (132, 0x880), (264, 0x1900), (528, 0x3a00), (0x420, 0x7c00)] [0xf800]
      t1aOut16 careAllTier1 specT1b_16 = true := by decide +kernel
theorem wPack_t1aOut16 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut16 =
    specT1b_16 (wPack (envTier1Sym96 c) t1aIn16) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert16 c rfl
def t1aIn17 : List ℕ :=
    [v23T1W.getD 17 0, v23T1W.getD 18 0, v23T1W.getD 19 0, v23T1W.getD 20 0, v23T1W.getD 21 0,
    cmpRhsBitT1aW 5, cmpRhsBitT1aW 6, cmpRhsBitT1aW 7, cmpRhsBitT1aW 8, cmpRhsBitT1aW 9,
    outW t1aOut16 0]
def t1aOut17 : List ℕ := [ (oddMask 0x1ff8000000000000000000000000000000000000000001) ]
theorem t1aCert17 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 133 11 t1aIn17
      [(66, 0x840), (132, 0x1880), (264, 0x3900), (528, 0x7a00), (0x420, 0xfc00)] [0x1f800]
      t1aOut17 (planesCmpKT1 5) = true := by decide +kernel
theorem wPack_t1aOut17 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut17 =
    specTier1_17 (wPack (envTier1Sym96 c) t1aIn17) :=
  wPack_of_checkBlockPlanesT1 (care :=
      careAllTier1) gatesTier1Sym96_wf t1aCert17 (planesCmpKT1_spec (k := 5)) c rfl
def specT1b_18 (r : ℕ) : ℕ :=
    cond (Bool.or (Nat.blt (r % 2) ((r / 2) % 2)) (Bool.and (Nat.beq (r % 2) ((r / 2) % 2))
    (bitAt r 2))) 1 0
def t1aIn18 : List ℕ := [v23T1W.getD 22 0, cmpRhsBitT1aW 10, outW t1aOut17 0]
def t1aOut18 : List ℕ := [ (oddMask 0x3ff8000000000000000000000000000000000000000001) ]
theorem t1aCert18 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 138 3 t1aIn18
      [(6, 12)] [24]
      t1aOut18 careAllTier1 specT1b_18 = true := by decide +kernel
theorem wPack_t1aOut18 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut18 =
    specT1b_18 (wPack (envTier1Sym96 c) t1aIn18) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert18 c rfl
def t1aIn20 : List ℕ :=
    [outW t1aEff12 0, outW t1aEff12 1, outW t1aEff12 2, outW t1aEff12 3, outW t1aEff12 4,
    outW t1aEff12 5, outW t1aOut18 0, outW t1aOut05 0, outW t1aOut06 0, outW t1aOut10 1,
    outW t1aOut08 1]
def t1aOut20 : List ℕ :=
    [ (oddMask 0x80000000000000000000000000000000000000000000001),
    (oddMask 0x100000000000000000000000000000000000000000000001),
    (oddMask 0x10000000000000000000000000000000000000000000001) ]
theorem t1aCert20 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 139 11 t1aIn20
      [(84, 128), (256, 0x102a), (96, 0x2000), (512, 0x6000), (6, 0x8000), (0x401, 0x10000),
          (0x801, 0x18000)] [0x20000, 0x40000, 0x4000]
      t1aOut20 planesPot20T1 = true := by decide +kernel
theorem wPack_t1aOut20 (c : Fin (2 ^ 41))
    (hCare : careTier1_20 (wPack (envTier1Sym96 c) t1aIn20) = true) :
    wPack (envTier1Sym96 c) t1aOut20 = specTier1_20 (wPack (envTier1Sym96 c) t1aIn20) :=
    wPack_of_checkBlockPlanesT1 gatesTier1Sym96_wf t1aCert20 planesPot20T1_spec c hCare
def envTier1Sym96Rev144 (c : Fin (2 ^ 41)) : ℕ :=
    xagEnv c.val nGatesTier1Sym96Rev144 gatesTier1Sym96Rev144 nGatesTier1Sym96Rev144 le_rfl
theorem wBit_rev144_eq_fwd_of_lt140 (c : Fin (2 ^ 41)) {msk : ℕ}
    (hMsk : Nat.blt msk (1 <<< (42 + 139)) = true) : wBit (envTier1Sym96Rev144 c) msk =
    wBit (envTier1Sym96 c) msk :=
  wBit_eq_of_prefix (K := 139) (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl)
      (Nat.ble_eq.mp rfl) gatesTier1Sym96Rev144_prefix140 hMsk
theorem wPack_rev144_eq_fwd_of_lt140 (c : Fin (2 ^ 41)) {ms : List ℕ}
    (hAll : (ms.all fun m ↦ Nat.blt m (1 <<< (42 + 139))) = true) :
    wPack (envTier1Sym96Rev144 c) ms = wPack (envTier1Sym96 c) ms :=
  wPack_eq_of_prefix c.val (K := 139) (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl) (Nat.ble_eq.mp rfl)
      (Nat.ble_eq.mp rfl) gatesTier1Sym96Rev144_prefix140 hAll
def t1aRevIn20 : List ℕ := t1aIn20
def t1aRevOut20 : List ℕ :=
    [ (oddMask 0x4000000000000000000000000000000000000000000001),
    (oddMask 0x8000000000000000000000000000000000000000000001),
    (oddMask 0x10000000000000000000000000000000000000000000001),
    (oddMask 0x20000000000000000000000000000000000000000000001) ]
def specT1aRev20 (r : ℕ) : ℕ :=
  let g0 :=
      Bool.and (xor (xor (xor true (bitAt r 2)) (bitAt r 3)) (bitAt r 5))
      (xor (xor (xor (xor (xor (xor (xor (xor (xor true (bitAt r 0)) (bitAt r 1)) (bitAt r 2))
      (bitAt r 4)) (bitAt r 5)) (bitAt r 7)) (bitAt r 8)) (bitAt r 9)) (bitAt r 10))
  let g1 := Bool.and (xor (xor (xor (xor (bitAt r 0) (bitAt r 4)) (bitAt r 8)) (bitAt r 10)) g0)
      (xor (xor (xor (bitAt r 0) (bitAt r 4)) (bitAt r 5)) (bitAt r 8))
  let g2 :=
      Bool.and (xor (xor (xor (xor (bitAt r 0) (bitAt r 2)) (bitAt r 4)) (bitAt r 5)) (bitAt r 7))
      (xor (bitAt r 0) g1)
  let g3 :=
      Bool.and (xor (xor true (bitAt r 5)) g2)
      (xor (xor (xor (xor (bitAt r 0) (bitAt r 2)) (bitAt r 5)) (bitAt r 6)) g1)
  cond g0 1 0 + cond g1 2 0 + cond g2 4 0 + cond g3 8 0

theorem t1aRevCert20 :
    checkBlockFullFastT1 nGatesTier1Sym96Rev144 gatesTier1Sym96Rev144At 139 11 t1aRevIn20
      [(89, 0xf6f), (0x1a22, 610), (362, 0x2002), (0x4041, 0x20ca)] [0x1000, 0x2000, 0x4000, 0x8000]
      t1aRevOut20 careAllTier1 specT1aRev20 = true := by decide +kernel
theorem wPack_rev144_t1aRevIn20 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96Rev144 c) t1aRevIn20 =
    wPack (envTier1Sym96 c) t1aIn20 := wPack_rev144_eq_fwd_of_lt140 c (by decide +kernel)
theorem wPack_t1aRevOut20 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96Rev144 c) t1aRevOut20 =
    specT1aRev20 (wPack (envTier1Sym96 c) t1aIn20) := by
  rw [← wPack_rev144_t1aRevIn20 c];
  exact wPack_of_checkBlockFullFastT1 gatesTier1Sym96Rev144_wf t1aRevCert20 c rfl
def fastSpec07Full (r : ℕ) : ℕ :=
    cond (bitAt r 0) (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) 3 0) 0) 0) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) 1 3)
    (cond (bitAt r 5) 1 0)) (cond (bitAt r 4) (cond (bitAt r 5) 1 0) (cond (bitAt r 5) 1 0))))
    (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4) (cond (bitAt r 5) 1 0)
    (cond (bitAt r 5) 3 0)) (cond (bitAt r 4) (cond (bitAt r 5) 1 0) 0)) (cond (bitAt r 3)
    (cond (bitAt r 4) 1 (cond (bitAt r 5) 1 3)) (cond (bitAt r 4) 1 (cond (bitAt r 5) 1 0)))))
    (cond (bitAt r 1) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) 1 0) 0) (cond (bitAt r 4) (cond (bitAt r 5) 2 0) 0)) (cond (bitAt r 3)
    (cond (bitAt r 4) 1 (cond (bitAt r 5) 1 0)) (cond (bitAt r 4) (cond (bitAt r 5) 1 2)
    (cond (bitAt r 5) 1 0)))) (cond (bitAt r 2) (cond (bitAt r 3) (cond (bitAt r 4)
    (cond (bitAt r 5) 1 0) (cond (bitAt r 5) 1 0)) (cond (bitAt r 4) (cond (bitAt r 5) 1 0)
    (cond (bitAt r 5) 2 0))) (cond (bitAt r 3) 1 (cond (bitAt r 4) 1 (cond (bitAt r 5) 1 2)))))
theorem t1bCert07Full :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 85 6 t1aIn07
      [(48, 21), (72, 209), (37, 275), (72, 768)] [472, 0x700]
      t1aOut07 careAllTier1 fastSpec07Full = true := by decide +kernel
theorem wPack_t1bOut07Full (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut07 =
    fastSpec07Full (wPack (envTier1Sym96 c) t1aIn07) :=
        wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1bCert07Full c rfl
def isPotT1aW : ℕ := Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2)
def t1aXor3 (a b c : ℕ) : ℕ := Nat.xor a (Nat.xor b c)
def t1aXor4 (a b c d : ℕ) : ℕ := Nat.xor a (Nat.xor b (Nat.xor c d))
def t1aXor5 (a b c d e : ℕ) : ℕ := Nat.xor a (Nat.xor b (Nat.xor c (Nat.xor d e)))

def careT1a_21Lo (r : ℕ) : Bool :=
  let isX := bitAt r 0
  let inBox := Bool.and (Bool.not isX) (Bool.not (bitAt r 1))
  let isPot := bitAt r 2
  let h1 := (r / 64) % 4
  let knF := bitAt r 9
  Bool.and (Nat.blt h1 3)
    (Bool.and (Bool.or (Bool.not isX) (Nat.beq h1 0))
      (Bool.and (Bool.or (Bool.not isPot) inBox)
        (Bool.and (Bool.or (Bool.not (bitAt r 3))
            (Bool.and (Bool.and inBox (Bool.not isPot)) (Bool.and (Nat.beq h1 0) knF)))
          (Bool.or (Bool.not (bitAt r 4))
            (Bool.and (Bool.and inBox (Bool.not isPot))
              (Bool.and (Bool.or (Nat.beq h1 1) (Nat.beq h1 2)) knF))))))

def careT1a_21 (r : ℕ) : Bool :=
  let isX := bitAt r 0
  let isY := bitAt r 1
  let inBox := Bool.and (Bool.not isX) (Bool.not isY)
  let knF := bitAt r 9
  let knP := bitAt r 10
  Bool.and (careT1a_21Lo r)
    (Bool.and (Bool.or (Bool.not isY) knF)
      (Bool.and (Bool.or (Bool.not (bitAt r 8)) (Bool.and isX (Bool.not isY)))
        (Bool.and (Bool.not (Bool.and knF knP))
          (Bool.or inBox (Bool.or (Bool.not (bitAt r 5)) knP)))))

def specT1a_21Kel (r : ℕ) : Bool :=
  let inBox := Bool.and (Bool.not (bitAt r 0)) (Bool.not (bitAt r 1))
  let ovIdle := Bool.and (bitAt r 3) (bitAt r 5)
  Bool.and inBox (Bool.and (Bool.not (bitAt r 2)) (Bool.not ovIdle))

def specT1a_21 (r : ℕ) : ℕ :=
  let lt17 := bitAt r 5
  let doKel := specT1a_21Kel r
  let ovAx0 := Bool.and (bitAt r 4) lt17
  let axEl := cond doKel (cond ovAx0 0 ((r / 64) % 4)) 0
  let doKn := Bool.and (bitAt r 8) (Bool.or (bitAt r 9) (Bool.and (bitAt r 10) lt17))
  cond doKel 1 0 + cond doKn 2 0 + 4 * axEl

def t1aIn21 : List ℕ :=
    [outW tier1Out02 10, outW t1aOut03 11, Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1))
    (outW t1aOut20 2), Nat.xor (outW t1aOut12 6) (Nat.xor (outW t1aOut14 0) (outW t1aOut14 1)),
    Nat.xor (outW t1aOut14 0) (outW t1aOut14 1), outW t1aOut18 0, outW tier1Out02 5,
    outW tier1Out02 6, outW t1aOut11 1, outW t1aOut13 0, Nat.xor (Nat.xor (outW t1aOut13 1)
    (outW t1aOut13 2)) (Nat.xor (outW t1aOut13 3) (outW t1aOut13 4))]
def t1aOut21 : List ℕ :=
    [ 0x5c8000340000000000000000000000040000000000000001,
    0x301ffc000080000000000000046000040000000000000001,
    0x100000000000000000000000000000007801f820000000001,
    0x1c00000300000000000000000001d23aa801f820000800001 ]
theorem t1aCert21 :
    checkBlockFullFastT1 nGatesTier1Sym96 gatesTier1Sym96At 146 11 t1aIn21
      [(0x47f, 0x44a), (0x1642, 0x1235), (0x3660, 0x2671), (12, 0x13af), (128, 0x1038)]
          [0x501b, 0x3642, 0x10080, 0x1c124]
      t1aOut21 careT1a_21 specT1a_21 = true := by decide +kernel
theorem wPack_t1aOut21 (c : Fin (2 ^ 41)) (hCare : careT1a_21 (wPack (envTier1Sym96 c) t1aIn21) =
    true) : wPack (envTier1Sym96 c) t1aOut21 = specT1a_21 (wPack (envTier1Sym96 c) t1aIn21) :=
    wPack_of_checkBlockFullFastT1 gatesTier1Sym96_wf t1aCert21 c hCare
def t1aIn22 : List ℕ :=
    [Nat.xor (Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2))
    (outW t1aOut21 0), outW t1aOut20 0, outW t1aOut10 0, outW t1aOut04 0, outW t1aOut04 1,
    outW t1aOut04 2, outW t1aOut04 3, outW t1aOut06 9, outW t1aOut06 10, outW t1aOut06 11,
    outW t1aOut06 12]
def t1aOut22 : List ℕ :=
    [ (oddMask 0x4000000000000000000000000000000000000000000000001),
    0x124450000034000000000000000200008104b9d5802d24010001,
    0x180c00000000000000000000000800000000281d800800000000,
    0x130e5000003400000000000000120002170411cd800524040000,
    0x82a50000034000000000000001e00038d0411cd8005240a0000,
    0x2256040000000003c4000244001e00033d8011cd8005240a0000,
    0x81e500000340003c4000000001e00022b8411cd8005241a0040,
    0x23cc540000340003c4000000001e00029b0411cd8005241a0800,
    0x2c3a500000340000000000000000000000040000000000000200 ]
theorem t1aCert22 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 151 11 t1aIn22
      [(9, 4), (0x1000, 0x1119), (0x1087, 0x1003), (5, 0x520a), (0x1000, 0xea24), (3, 0x20d7),
          (5, 0x13709), (0x1000, 0x6f443), (3, 0x24037), (5, 0x1b8b01), (0x1000, 0x158807),
          (3, 0x122011), (5, 0x6cdf0a)] [0x1000, 0x922013, 0xc06020, 0x987043, 0x415083, 0x112b10c,
          0x40f20a, 0x11e640f, 0x161d803]
      t1aOut22 (planesSwMux2T1 4) = true := by decide +kernel
theorem wPack_t1aOut22 (c : Fin (2 ^ 41))
    (hCare : careTier1_22 (wPack (envTier1Sym96 c) t1aIn22) = true) :
    wPack (envTier1Sym96 c) t1aOut22 = specTier1_22 (wPack (envTier1Sym96 c) t1aIn22) :=
  wPack_of_checkBlockPlanesT1 gatesTier1Sym96_wf t1aCert22 (fun hr h1 hVt hC ↦
      planesSwMux2T1_spec (by decide) hr h1 hVt hC) c hCare
def t1aIn23 : List ℕ :=
    [Nat.xor (Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2))
    (outW t1aOut21 0), outW t1aOut20 0, outW t1aOut22 0, outW t1aOut04 4, outW t1aOut04 5,
    outW t1aOut04 6, outW t1aOut04 7, outW t1aOut06 13, outW t1aOut06 14, outW t1aOut06 15,
    outW t1aOut06 16]
def t1aOut23 : List ℕ :=
    [ 0x104400250000034000000000000000200000004a818002800000000,
    0x12680025000003400000000000000080003a5040800000000020000,
    0x3480020000000000000000000000120000000059f0001524000000,
    0x186800000000000000000000000001e0003a50091c8002524020000,
    (oddMask 0xa40004000000000000000000000000000000000000000000000001),
    0x22a0002000000000000000000000000000000000000000000000080,
    0x23080020000000000000000220000000000b0800000000000000501,
    0x8b0000540000340000000001040000000000040000000000000801 ]
theorem t1aCert23 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 164 11 t1aIn23
      [(8, 285), (3, 159), (5, 0x2e02), (8, 0x6224), (3, 0xa0ed), (5, 0x360c), (8, 0x1644d),
          (3, 0x1a04e), (4, 0x5d100), (8, 0x9e880), (3, 0x2880c0), (5, 0x3eec0a)]
          [0x41101b, 0x49a02b, 0xd2048, 0x61a080, 0x148008, 0x8a8208, 0x8c2408, 0x22c806]
      t1aOut23 (planesDirectMux2T1 4) = true := by decide +kernel
theorem wPack_t1aOut23 (c : Fin (2 ^ 41))
    (hCare : careTier1_23 (wPack (envTier1Sym96 c) t1aIn23) = true) :
    wPack (envTier1Sym96 c) t1aOut23 = specTier1_23 (wPack (envTier1Sym96 c) t1aIn23) :=
  wPack_of_checkBlockPlanesT1 gatesTier1Sym96_wf t1aCert23 (fun hr h1 hVt hC ↦
      planesDirectMux2T1_spec (by decide) hr h1 hVt hC) c hCare
def t1aIn24 : List ℕ :=
    [Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2), outW t1aOut20 1,
    outW t1aOut08 0, outW t1aOut05 3, outW t1aOut05 4, outW t1aOut06 3, outW t1aOut06 4,
    outW t1aOut05 1, outW t1aOut05 2, outW t1aOut06 1, outW t1aOut06 2]
def t1aOut24 : List ℕ :=
    [ (oddMask 0x8000000000000000000000000000000000000000000000000000001),
    (h224 0x4 0xc00000000000000000000000003b0000000000d017c000010000000),
    (h224 0x26 0x9c000000048000000000000000002120000000000000000000000001),
    (h224 0x4c 0xc000000000000000000000076000000000116000000000000100e40),
    (h224 0x45 0xe40000000000000000000000220400000000b0800000000000000800),
    (h224 0x6 0xd0000000000000000000000000002120000000000000000000000001),
    (h224 0x12 0x100000000c8000000000000000004820000000000000000000000001),
    (h224 0x47 (oddMask 0x188000000100000000000004008482040000000000000000000000001)),
    (h224 0x1a (oddMask 0x12080000000000000000000000000001)) ]
theorem t1aCert24 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 176 11 t1aIn24
      [(9, 4), (0x1000, 0x1050), (3, 515), (0x488, 5), (0x1000, 0x10a5), (3, 0x13313), (5, 0x32c4c),
          (0x1000, 0x5c50d), (3, 0x25104), (5, 0x804), (0x1000, 0xa4a0d), (2, 0x192126),
          (5, 0x162408)] [0x1000, 0x103010, 0x9a7106, 0x1303040, 0x1179080, 0x1b4100, 0x484203,
          0x11f140c, 0x680800]
      t1aOut24 (planesSwMux4T1 2) = true := by decide +kernel
theorem wPack_t1aOut24 (c : Fin (2 ^ 41))
    (hCare : careTier1_24 (wPack (envTier1Sym96 c) t1aIn24) = true) :
    wPack (envTier1Sym96 c) t1aOut24 = specTier1_24 (wPack (envTier1Sym96 c) t1aIn24) :=
  wPack_of_checkBlockPlanesT1 gatesTier1Sym96_wf t1aCert24 (fun hr h1 hVt hC ↦
      planesSwMux4T1_spec (by decide) hr h1 hVt hC) c hCare
def t1aIn25 : List ℕ :=
    [Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2), outW t1aOut20 1,
    outW t1aOut24 0, outW t1aOut05 5, outW t1aOut05 6, outW t1aOut05 7, outW t1aOut05 8,
    outW t1aOut06 5, outW t1aOut06 6, outW t1aOut06 7, outW t1aOut06 8]
def t1aOut25 : List ℕ :=
    [ (h224 0x4980 0xc000000000000005800020000000),
    (h224 0xd00 0x40000000c80000000000000000018000000000001b1800130000001),
    (h224 0x26f00 0x40000000c800000000000000000c000000000000005800020000000),
    (h224 0x1c900 0x80000000000000002040000000000000000000000000001),
    (h224 0xc300 0x4800000000000001a040000000000000000000000000200),
    (h224 0xd700 0x40000000c800000000000001a040000000000000000000000000200),
    (h224 0x4f980 0x4000000080000000000000019040000000000000000000000000e00),
    (h224 0x1ca80 0x80000000000000002041020000000000000000000000001) ]
theorem t1aCert25 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 189 11 t1aIn25
      [(278, 8), (3, 0x1084), (4, 0x1806), (8, 0x222d), (3, 0x7025), (4, 0x16b04), (8, 0x12442),
          (3, 0x30b3), (5, 0x8290a), (9, 0x198885), (2, 0xe051), (5, 0x75e02)]
          [0x93010, 0x1a02b, 0x4de01a, 0x392805, 0x186906, 0x1ae90a, 0x9f370c, 0x395885]
      t1aOut25 (planesDirectMux2T1 4) = true := by decide +kernel
theorem wPack_t1aOut25 (c : Fin (2 ^ 41))
    (hCare : careTier1_23 (wPack (envTier1Sym96 c) t1aIn25) = true) :
    wPack (envTier1Sym96 c) t1aOut25 = specTier1_23 (wPack (envTier1Sym96 c) t1aIn25) :=
  wPack_of_checkBlockPlanesT1 gatesTier1Sym96_wf t1aCert25 (fun hr h1 hVt hC ↦
      planesDirectMux2T1_spec (by decide) hr h1 hVt hC) c hCare
def t1aKin26 : List ℕ :=
    [outW t1aOut13 5, outW t1aOut13 6, outW t1aOut13 7, outW t1aOut13 8, outW t1aOut13 9,
    outW t1aOut13 10, coinW 23, coinW 24]
def t1aIn26 : List ℕ :=
    [outW t1aOut21 1, Nat.xor (outW t1aOut13 5) (outW t1aOut24 1), Nat.xor (outW t1aOut13 6)
    (outW t1aOut24 2), Nat.xor (outW t1aOut13 7) (outW t1aOut25 0), Nat.xor (outW t1aOut13 8)
    (outW t1aOut25 1), Nat.xor (outW t1aOut13 9) (outW t1aOut25 2), Nat.xor (outW t1aOut13 10)
    (outW t1aOut25 3), Nat.xor (coinW 23) (Nat.xor (outW t1aOut24 7) (outW t1aOut21 2)),
    Nat.xor (coinW 24) (Nat.xor (outW t1aOut24 8) (outW t1aOut21 3))]
def t1aOut26 : List ℕ :=
    [ (h224 0x80000 0x0), (h224 0x100000 0x0), (h224 0x200000 0x0), (h224 0x400000 0x0),
    (h224 0x800000 0x0), (h224 0x1000000 0x0), (h224 0x2000000 0x0), (h224 0x4000000 0x0) ]
theorem t1aCert26 :
    checkBlockPlanesT1 nGatesTier1Sym96 gatesTier1Sym96At 201 9 t1aIn26
      [(2, 4), (2, 8), (2, 16), (2, 32), (2, 64), (2, 128), (2, 256), (2, 512)]
          [0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000]
      t1aOut26 (planesGateTopSliceT1 8) = true := by decide +kernel
theorem wPack_t1aOut26 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut26 =
    specTier1_26 (wPack (envTier1Sym96 c) t1aIn26) :=
  wPack_of_checkBlockPlanesT1 (care :=
      careAllTier1) gatesTier1Sym96_wf t1aCert26 (fun hr h1 hVt _ ↦
      planesGateTopSliceT1_spec hr h1 hVt) c rfl
def n1T1aW (i : ℕ) : ℕ :=
    Nat.xor (cond (Nat.blt i 2) (outW t1aOut24 (1 + i)) (outW t1aOut25 (i - 2))) (outW t1aOut26 i)
def n2T1aW (i : ℕ) : ℕ := cond (Nat.blt i 2) (outW t1aOut24 (3 + i)) (outW t1aOut25 (2 + i))
def e1T1aW (i : ℕ) : ℕ := cond (Nat.blt i 4) (outW t1aOut22 (1 + i)) (outW t1aOut23 (i - 4))
def e2T1aW (i : ℕ) : ℕ := cond (Nat.blt i 4) (outW t1aOut22 (5 + i)) (outW t1aOut23 i)
def aux2T1aW (i : ℕ) : ℕ :=
    Nat.xor (Nat.xor (outW t1aOut24 (7 + i)) (outW t1aOut21 (2 + i))) (outW t1aOut26 (6 + i))
def symOuts40Tier1Sym96 : List ℕ :=
    [Nat.xor isPotT1aW (outW t1aOut21 1), outW t1aOut20 1, n1T1aW 0, n1T1aW 1, n1T1aW 2, n1T1aW 3,
    n1T1aW 4, n1T1aW 5, n2T1aW 0, n2T1aW 1, n2T1aW 2, n2T1aW 3, n2T1aW 4, n2T1aW 5,
    Nat.xor isPotT1aW (outW t1aOut21 0), outW t1aOut20 0, e1T1aW 0, e1T1aW 1, e1T1aW 2, e1T1aW 3,
    e1T1aW 4, e1T1aW 5, e1T1aW 6, e1T1aW 7, e2T1aW 0, e2T1aW 1, e2T1aW 2, e2T1aW 3, e2T1aW 4,
    e2T1aW 5, e2T1aW 6, e2T1aW 7, Nat.xor (outW t1aOut20 0) (outW t1aOut20 1), isPotT1aW,
    Nat.xor (outW t1aOut21 0) (outW t1aOut21 1), outW t1aOut20 1, outW t1aOut24 5, outW t1aOut24 6,
    aux2T1aW 0, aux2T1aW 1]
theorem outs40ListTier1Sym96_eq_sym : outs40ListTier1Sym96 = symOuts40Tier1Sym96 :=
  listBeqNatT1_imp (by decide +kernel)

-- STAGE_B_START
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (wBit_zero wPack_lt_pow
    testBit_wPack allTree_zero nat_xor_eq blt_eq_false_iff b2_bEq_iff b2_testBit_mod_pow)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoinWrap (oddBits)
theorem careTier1Walk_12_mod512 (r : ℕ) : careTier1Walk_12 (r % 512) = careTier1Walk_12 r := by
  dsimp only [careTier1Walk_12]
  have hb0 : bitAt (r % 512) 0 = bitAt r 0 := by
    rw [bitAt_eq_testBit, show (512 : ℕ) = 2 ^ 9 from rfl, b2_testBit_mod_pow r 9 0 (by decide),
        ← bitAt_eq_testBit]
  rw [hb0, show (r % 512 / 2) % 8 = (r / 2) % 8 by omega, show (r % 512 / 16) % 32 =
      (r / 16) % 32 by omega]

def mEvXorConst (b : Bool) (val acc : ℕ) : ℕ := cond b (Nat.xor acc val) acc

theorem mEv_testBit_xorConst (b : Bool) (val acc i : ℕ) :
    (mEvXorConst b val acc).testBit i = xor (acc.testBit i) (Bool.and (val.testBit i) b) := by
  cases b <;> simp [mEvXorConst, cond, Nat.testBit_xor]

theorem mEv_wBit_xorMaskedConst (e sig val i acc : ℕ) :
    wBit e (xorMaskedConstT1 sig val i acc) = xor (wBit e acc) (Bool.and (val.testBit i)
        (wBit e sig)) := by
  unfold xorMaskedConstT1
  rw [bitAt_eq_testBit]
  cases val.testBit i <;>
    simp only [cond, Bool.false_and, Bool.xor_false, Bool.true_and, t1Ev_wBit_xor]

theorem mEv_mkFin3_val {k : ℕ} (hk : k < 3) : (mkFin3 k).val = k := Nat.mod_eq_of_lt hk
theorem mEv_mkFin187_val {k : ℕ} (hk : k < 187) : (mkFin187 k).val = k := Nat.mod_eq_of_lt hk
theorem mEv_mkFin234_val {k : ℕ} (hk : k < 234) : (mkFin234 k).val = k := Nat.mod_eq_of_lt hk
theorem mEv_packOut40_idle :
    packOut40ZeroNErem false false 0 0 false false 0 0 false false false false 0 0 = 0 := by
      decide +kernel
theorem mEv_outMask_idle : zeroNEremOutMask .idle = 0 := rfl
theorem mEv_outMask_kin_lt {i : Fin 234} {ax : Fin 3} (h : i.val < 47) :
    zeroNEremOutMask (.kin i ax) =
      packOut40ZeroNErem true false i.val 0 false false 0 0 false false true false 0 ax.val := by
  simp only [zeroNEremOutMask, h, ↓reduceIte]
theorem mEv_outMask_kin_ge {i : Fin 234} {ax : Fin 3} (h : ¬ (i.val < 47)) :
    zeroNEremOutMask (.kin i ax) =
      packOut40ZeroNErem false false 0 0 true false (i.val -
          47) 0 false false true false 0 ax.val := by
  simp only [zeroNEremOutMask, h, ↓reduceIte]
def mEvPackOfFlags (doEe doNn doEn doKel doKn : Bool)
    (u1 z2 d1v d2v sp1v sp2v axEl n1K axK : ℕ) : ℕ :=
  let isPot := xor (xor doEe doNn) doEn
  let swE := Bool.and doEe (Nat.blt z2 u1)
  let swN := Bool.and doNn (Nat.blt d2v d1v)
  let hasE1 := xor isPot doKel
  packOut40ZeroNErem (xor isPot doKn) doNn
    (Nat.xor (cond swN d2v (cond isPot d1v 0)) n1K) (cond doNn (cond swN d1v d2v) 0)
    hasE1 doEe (cond swE z2 (cond hasE1 u1 0)) (cond doEe (cond swE u1 z2) 0)
    (xor doEe doNn) isPot (xor doKel doKn) doNn
    (cond swN sp2v (cond isPot sp1v 0))
    (Nat.xor (Nat.xor (cond doNn (cond swN sp1v sp2v) 0) axEl) axK)

theorem mEv_pack_idle (u1 z2 d1v d2v sp1v sp2v : ℕ) :
    mEvPackOfFlags false false false false false u1 z2 d1v d2v sp1v sp2v 0 0 0 =
      zeroNEremOutMask .idle := by
  simp [mEvPackOfFlags, xor, cond, mEv_packOut40_idle, mEv_outMask_idle]

theorem mEv_pack_kinNuc (u1 z2 d1v d2v sp1v sp2v : ℕ) {n1K axK : ℕ}
    (hn1 : n1K < 47) (hax : axK < 3) :
    mEvPackOfFlags false false false false true u1 z2 d1v d2v sp1v sp2v 0 n1K axK =
      zeroNEremOutMask (.kin (mkFin234 n1K) (mkFin3 axK)) := by
  have hv : (mkFin234 n1K).val = n1K := mEv_mkFin234_val (by omega)
  rw [mEv_outMask_kin_lt (by omega), hv, mEv_mkFin3_val hax]
  simp [mEvPackOfFlags, xor, cond]

theorem mEv_pack_kinEl {u1 : ℕ} (hu1 : u1 < 187) (z2 d1v d2v sp1v sp2v : ℕ) {axEl : ℕ}
    (hax : axEl < 3) :
    mEvPackOfFlags false false false true false u1 z2 d1v d2v sp1v sp2v axEl 0 0 =
      zeroNEremOutMask (.kin (mkFin234 (47 + u1)) (mkFin3 axEl)) := by
  have hv : (mkFin234 (47 + u1)).val = 47 + u1 := mEv_mkFin234_val (by omega)
  rw [mEv_outMask_kin_ge (by omega), hv, mEv_mkFin3_val hax, show 47 + u1 - 47 = u1 by omega]
  simp [mEvPackOfFlags, xor, cond]

theorem mEv_pack_ee {u1 z2 : ℕ} (hu1 : u1 < 187) (hz2 : z2 < 187)
    (n1 : Fin 47) (d2v sp2v : ℕ) :
    let cE := Nat.blt z2 u1
    mEvPackOfFlags true false false false false u1 z2 n1.val d2v (nucSpecies n1).val sp2v 0 0 0 =
      zeroNEremOutMask (.ee n1 (mkFin187 (cond cE z2 u1)) (mkFin187 (cond cE u1 z2))) := by
  intro cE
  unfold zeroNEremOutMask
  dsimp only
  rw [mEv_mkFin187_val (by cases cE <;> dsimp only [cond] <;> omega),
      mEv_mkFin187_val (by cases cE <;> dsimp only [cond] <;> omega)]
  simp [mEvPackOfFlags, cE, xor, cond]

theorem mEv_pack_nn {u1 : ℕ} (hu1 : u1 < 187) (z2 : ℕ) (n1 n2 : Fin 47) :
    let cN := Nat.blt n2.val n1.val
    mEvPackOfFlags false true false false false u1 z2 n1.val n2.val (nucSpecies n1).val (nucSpecies
        n2).val 0 0 0 =
      zeroNEremOutMask (.nn (cond cN n2 n1) (cond cN n1 n2) (mkFin187 u1)) := by
  intro cN
  unfold zeroNEremOutMask
  dsimp only
  rw [mEv_mkFin187_val hu1]
  cases hc : Nat.blt n2.val n1.val <;> simp [mEvPackOfFlags, cN, hc, xor, cond]

theorem mEv_pack_en {u1 : ℕ} (hu1 : u1 < 187) (z2 : ℕ) (n1 : Fin 47) (d2v sp2v : ℕ) :
    mEvPackOfFlags false false true false false u1 z2 n1.val d2v (nucSpecies n1).val sp2v 0 0 0 =
      zeroNEremOutMask (.en n1 (mkFin187 u1)) := by
  unfold zeroNEremOutMask
  dsimp only
  rw [mEv_mkFin187_val hu1]
  simp [mEvPackOfFlags, xor, cond]
def mEvIsKin (s : ZeroNEremSector) (na ax : ℕ) : Bool :=
  match s with
  | .kin i a => Bool.and (Nat.beq i.val na) (Nat.beq a.val ax)
  | _ => false

theorem wBit_t1a_const1 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c) 1 = true :=
  wBit_const1_gen (N := nGatesTier1Sym96) (Nat.ble_eq.mp rfl) c

theorem mEv_wBit_coinW (c : Fin (2 ^ 41)) {i : ℕ} (hi : i < 41) : wBit (envTier1Sym96 c)
    (coinW i) = c.val.testBit i :=
  wBit_coin_gen (N := nGatesTier1Sym96) (Nat.ble_eq.mp rfl) c hi

theorem mEv_coin_hi10_bit (c : Fin (2 ^ 41)) {i : ℕ} (hi : i < 10) : wBit (envTier1Sym96 c)
    (coinW (15 + i)) = (t1EvHi10 c).testBit i :=
  (mEv_wBit_coinW c (by omega)).trans
    ((t1Ev_wBit_coinW c (by omega)).symm.trans (t1Ev_coin_hi10_bit c hi))

theorem mEv_out02_slices (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c)
    (t1EvOutSlice tier1Out02 0 5) = (t1EvPx c).1 ∧ wPack (envTier1Sym96 c)
    (t1EvOutSlice tier1Out02 5 2) = (t1EvPx c).2.1 ∧ wPack (envTier1Sym96 c)
    (t1EvOutSlice tier1Out02 7 3) = (t1EvPx c).2.2.1 ∧ wBit (envTier1Sym96 c)
    (outW tier1Out02 10) = (t1EvPx c).2.2.2 := by
  rw [wPack_t1a_eq_k3708_lt26 c (by decide +kernel),
      wPack_t1a_eq_k3708_lt26 c (by decide +kernel),
      wPack_t1a_eq_k3708_lt26 c (by decide +kernel),
      wBit_t1a_eq_k3708_lt26 c (by decide +kernel)]
  exact t1Ev_out02_slices c

theorem mEv_wPack_v23T1W (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) v23T1W = t1EvV23 c :=
  (wPack_t1a_eq_k3708_lt26 c (by decide +kernel)).trans (t1Ev_wPack_v23T1W c)

def t1aEvHi10Xor (c : Fin (2 ^ 41)) : ℕ := Nat.xor (t1EvHi10 c) 96
def t1aEvPy (c : Fin (2 ^ 41)) : ℕ × ℕ × ℕ × Bool := b6Spec (t1aEvHi10Xor c)
def t1aEvU1 (c : Fin (2 ^ 41)) : ℕ := phiU1 (t1aEvPy c).1 (t1EvPx c).1
def t1aEvD2 (c : Fin (2 ^ 41)) : Bool × Fin 47 :=
    decodeUltraNuc192 (64 * (t1aEvPy c).2.1 + t1EvLo10 c % 64)
def t1aEvZ2 (c : Fin (2 ^ 41)) : ℕ := b11Z2OfHX (t1aEvPy c).2.1 (t1EvLo10 c % 64)
def t1aEvInBox (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (Bool.not (t1EvPx c).2.2.2) (Bool.not (t1aEvPy c).2.2.2)
def t1aEvInTile (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (Bool.not (Nat.beq (t1EvHi8 c) 255)) (Bool.not (t1aEvPy c).2.2.2)
def t1aEvV17 (c : Fin (2 ^ 41)) : ℕ := (t1EvLo10 c % 64) + 64 * t1EvW11 c
def t1aEvTax (c : Fin (2 ^ 41)) : Bool := Nat.beq ((t1EvB8 c % 64) / 2) 23

theorem t1aEv_hi10Xor_lt (c : Fin (2 ^ 41)) : t1aEvHi10Xor c < 1024 := by
  dsimp only [t1aEvHi10Xor]; rw [nat_xor_eq]
  exact Nat.xor_lt_two_pow (n := 10) (t1Ev_coin_bounds c).2.2.1 (by decide)

theorem t1aEv_v17_props (c : Fin (2 ^ 41)) : t1EvV23 c / 64 = t1aEvV17 c ∧ t1aEvV17 c < 131072 ∧
    (Nat.beq (t1EvHi8 c) 255 = true → t1aEvV17 c = t1EvU15 c) := by
  have hb8 : t1EvB8 c % 64 < 64 := Nat.mod_lt _ (by decide)
  have hv23 : t1EvV23 c < 8388608 := (t1Ev_coin_bounds c).2.2.2.2.2.2.2.2.1
  have hd : t1EvV23 c / 64 = t1aEvV17 c := by dsimp only [t1EvV23, cart254V23, t1aEvV17]; omega
  refine ⟨hd, by omega, fun h255 ↦ ?_⟩
  have hk := t1Ev_v23_kinNuc c h255; omega
def t1aHi10XorW (i : ℕ) : ℕ :=
    cond (Bool.or (Nat.beq i 5) (Nat.beq i 6)) (Nat.xor 1 (coinW (15 + i))) (coinW (15 + i))
theorem t1aEv_wPack_in03 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aIn03 =
    t1aEvHi10Xor c := by
  have hBit : ∀ i < 10, wBit (envTier1Sym96 c) (t1aHi10XorW (0 + i)) =
      (t1aEvHi10Xor c).testBit (0 + i) := fun i hi ↦ by
    rw [Nat.zero_add]
    have hc := mEv_coin_hi10_bit c hi
    have h1 := wBit_t1a_const1 c
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i =
        9 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · dsimp only [t1aHi10XorW, t1aEvHi10Xor, Nat.beq, Bool.or, cond]
      try rw [t1Ev_wBit_xor, h1]
      rw [hc, nat_xor_eq, Nat.testBit_xor]
      cases (t1EvHi10 c).testBit _ <;> decide
  rw [show t1aIn03 = t1EvWireSlice t1aHi10XorW 0 10 from listBeqNatT1_imp (by decide +kernel),
      t1Ev_wPack_wireSlice _ t1aHi10XorW (t1aEvHi10Xor c) 0 10 hBit, pow_zero, Nat.div_one,
      show (2 : ℕ) ^ 10 = 1024 from rfl, Nat.mod_eq_of_lt (t1aEv_hi10Xor_lt c)]

theorem t1a_sp5 {a b c d e f : Bool}
    (h : Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e f)))) = true) :
    (a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true) ∧ f = true := by
  simpa only [Bool.and_eq_true, and_assoc] using h

theorem t1a_cert_b6 :
    allTree 11 0 1024 (fun h ↦
      let a10 := Nat.xor h 96
      let p := b6Spec a10
      let s := specT1a_03 a10
      Bool.and (Nat.blt p.1 11) (Bool.and (Nat.blt p.2.1 3) (Bool.and (Nat.blt p.2.2.1 32)
        (Bool.and (b2BEq p.2.2.2 (Nat.beq a10 1023))
            (Bool.and (Bool.or p.2.2.2 (Nat.ble p.2.2.1 30))
          (Bool.and (Nat.beq (s % 16) p.1) (Bool.and (Nat.beq ((s / 16) % 4) p.2.1)
            (Bool.and (Nat.beq ((s / 64) % 32) p.2.2.1)
              (Bool.and (b2BEq (s.testBit 11) p.2.2.2) (b2BEq (s.testBit 12)
                  (Bool.not (Nat.blt h 768)))))))))))) = true := by
  decide +kernel

theorem t1aEv_b6_props (c : Fin (2 ^ 41)) : (t1aEvPy c).1 < 11 ∧ (t1aEvPy c).2.1 < 3 ∧
    (t1aEvPy c).2.2.1 < 32 ∧
    (t1aEvPy c).2.2.2 = Nat.beq (t1aEvHi10Xor c) 1023 ∧ ((t1aEvPy c).2.2.2 = false →
        (t1aEvPy c).2.2.1 ≤ 30) := by
  rcases (t1a_sp5 (allTree_zero t1a_cert_b6 (t1Ev_coin_bounds c).2.2.1)).1 with ⟨h1, h2, h3, h4, h5⟩
  dsimp only [t1aEvPy, t1aEvHi10Xor]
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, (b2_bEq_iff _ _).mp h4, fun hf ↦
      Nat.ble_eq.mp (by simpa only [hf, Bool.false_or] using h5)⟩

theorem t1aEv_wPack_out03 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut03 =
    specT1a_03 (t1aEvHi10Xor c) := by rw [wPack_t1aOut03 c, t1aEv_wPack_in03 c]
theorem mEv_out03_slices (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut03 0 4) = (t1aEvPy c).1 ∧
        wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut03 4 2) = (t1aEvPy c).2.1 ∧
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut03 6 5) = (t1aEvPy c).2.2.1 ∧
        wBit (envTier1Sym96 c) (outW t1aOut03 11) = (t1aEvPy c).2.2.2 ∧
    wBit (envTier1Sym96 c) (outW t1aOut03 12) = Bool.not (Nat.blt (t1EvHi10 c) 768) := by
  rcases
      (by simpa only [Bool.and_eq_true] using (t1a_sp5 (allTree_zero t1a_cert_b6 (t1Ev_coin_bounds
            c).2.2.1)).2 : _ ∧ _ ∧ _ ∧ _ ∧ _) with ⟨s1, s2, s3, s4, s5⟩
  simp only [t1Ev_wPack_outSlice, t1Ev_wBit_outW, t1aEv_wPack_out03 c, pow_zero, Nat.div_one]
  exact ⟨Nat.beq_eq.mp s1, Nat.beq_eq.mp s2, Nat.beq_eq.mp s3, (b2_bEq_iff _ _).mp s4,
      (b2_bEq_iff _ _).mp s5⟩

theorem t1aEv_u1_z2_bounds (c : Fin (2 ^ 41)) : t1aEvU1 c < 187 ∧ t1aEvZ2 c < 256 ∧ ((t1aEvD2 c).1 =
    true → t1aEvZ2 c < 187) := by
  rcases Bool.and_eq_true_iff.mp t1Ev_cert_phi_z2 with ⟨hPhi, hZ2⟩
  rcases Bool.and_eq_true_iff.mp (allTree_zero (allTree_zero hZ2 (t1aEv_b6_props c).2.1)
      (Nat.mod_lt _ (by decide))) with ⟨hz256, hz187⟩
  refine ⟨Nat.blt_eq.mp (allTree_zero (allTree_zero hPhi (t1aEv_b6_props c).1)
      (t1Ev_b2_props c).1), Nat.blt_eq.mp hz256, fun hd2 ↦ ?_⟩
  dsimp only [t1aEvD2] at hd2
  rw [hd2, Bool.not_true, Bool.false_or] at hz187
  exact Nat.blt_eq.mp hz187

theorem t1a_dmod {a : ℕ} (b B : ℕ) (ha : a < B) (hB : 0 < B := by omega) :
    (a + B * b) % B = a ∧ (a + B * b) / B = b := by
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt ha, Nat.zero_add, and_self]

theorem mEv_wPack_out04 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut04 = t1aEvU1 c := by
  have hmd := t1a_dmod (t1EvPx c).1 16 (Nat.lt_trans (t1aEv_b6_props c).1 (by decide))
  have hIn : wPack (envTier1Sym96 c) t1aIn04 = (t1aEvPy c).1 + 16 * (t1EvPx c).1 := by
    rw [show t1aIn04 = t1EvOutSlice t1aOut03 0 4 ++
        t1EvOutSlice tier1Out02 0 5 from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_len_outSlice, (mEv_out03_slices c).1, (mEv_out02_slices c).1,
            show (2 : ℕ) ^ 4 = 16 from rfl]
  rw [wPack_t1aOut04 c
      (by simpa only [hIn, careTier1_04, hmd.1,
            hmd.2] using Bool.and_eq_true_iff.mpr ⟨Nat.blt_eq.mpr (t1aEv_b6_props c).1,
            Nat.blt_eq.mpr (t1Ev_b2_props c).1⟩),
      hIn, specTier1_04, hmd.1, hmd.2]
  rfl

theorem t1a_cert_nuc05 :
    allTree 9 0 256 (fun r ↦
      let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
      let m5 := maskT1a_05 r
      let s5 := specT1a_05 r
      Bool.and (m5.testBit 0) (Bool.and (b2BEq (s5.testBit 0) d.1) (Bool.and (m5.testBit 9)
        (Bool.and (b2BEq (s5.testBit 9) (Nat.beq (((r / 4) % 64) / 2) 23))
          (Bool.or (Bool.not d.1) (Bool.and (m5.testBit 10)
            (Bool.and (b2BEq (s5.testBit 10) (Bool.or (Nat.beq (d.2.val / 8) 3)
                (Nat.beq (d.2.val / 8) 4)))
              (Bool.and (allTree 2 0 2 (fun i ↦ Bool.and (m5.testBit (1 + i))
                  (b2BEq (s5.testBit (1 + i)) ((nucSpNatT1 d.2.val).testBit i))))
                (allTree 4 0 6 (fun i ↦ Bool.and (m5.testBit (3 + i)) (b2BEq (s5.testBit (3 + i))
                    (d.2.val.testBit i)))))))))))) = true := by
  decide +kernel

theorem t1a_cert_nuc06 :
    allTree 9 0 256 (fun r ↦
      let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
      let m6 := maskT1a_06 r
      let s6 := specT1a_06 r
      let z2 := b11Z2OfHX (r % 4) ((r / 4) % 64)
      Bool.and (m6.testBit 0) (Bool.and (b2BEq (s6.testBit 0) d.1) (Bool.and (m6.testBit 17)
        (Bool.and (b2BEq (s6.testBit 17) (Nat.ble 48 ((r / 4) % 64)))
          (Bool.and (allTree 4 0 8 (fun i ↦ Bool.and (m6.testBit (9 + i))
              (b2BEq (s6.testBit (9 + i)) (z2.testBit i))))
            (Bool.or (Bool.not d.1) (Bool.and (m6.testBit 18)
              (Bool.and (b2BEq (s6.testBit 18) (Bool.or (Nat.beq (d.2.val / 8) 3)
                  (Nat.beq (d.2.val / 8) 4)))
                (Bool.and (allTree 2 0 2 (fun i ↦ Bool.and (m6.testBit (1 + i))
                    (b2BEq (s6.testBit (1 + i)) ((nucSpNatT1 d.2.val).testBit i))))
                  (allTree 4 0 6 (fun i ↦ Bool.and (m6.testBit (3 + i)) (b2BEq (s6.testBit (3 + i))
                      (d.2.val.testBit i))))))))))))) = true := by
  decide +kernel
def mEvNa1Hw (c : Fin (2 ^ 41)) : ℕ := wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut05 3 6)
def mEvSp1Hw (c : Fin (2 ^ 41)) : ℕ := wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut05 1 2)
def mEvNa2Hw (c : Fin (2 ^ 41)) : ℕ := wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut06 3 6)
def mEvSp2Hw (c : Fin (2 ^ 41)) : ℕ := wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut06 1 2)
theorem mEv_hw_bounds (c : Fin (2 ^ 41)) : mEvNa1Hw c < 64 ∧ mEvSp1Hw c < 4 ∧ mEvNa2Hw c < 64 ∧
    mEvSp2Hw c < 4 := ⟨wPack_lt_pow _ _, wPack_lt_pow _ _, wPack_lt_pow _ _, wPack_lt_pow _ _⟩
theorem t1a_mb {e m s j : ℕ} {outs : List ℕ} {b : Bool} (hM : wPack e outs &&& m = s &&& m)
    (hm : m.testBit j = true) (hs : b2BEq (s.testBit j) b = true) : wBit e (outW outs j) = b :=
    (t1Ev_wBit_of_masked hM hm).trans ((b2_bEq_iff _ _).mp hs)
theorem t1a_pk (outs : List ℕ) (o k P : ℕ) {e x : ℕ}
    (hx : x < P) (hb : ∀ i < k, wBit e (outW outs (o + i)) = x.testBit i)
    (hbq : listBeqNatT1 (t1EvOutSlice outs o k)
      (t1EvWireSlice (fun i ↦ outW outs (o + i)) 0 k) = true := by decide +kernel)
    (hP : 2 ^ k = P := by rfl) : wPack e (t1EvOutSlice outs o k) = x := by
  rw [listBeqNatT1_imp hbq, t1Ev_wPack_wireSlice e _ x 0 k
        (fun i hi ↦ by simpa only [Nat.zero_add] using hb i hi),
      pow_zero, Nat.div_one, hP, Nat.mod_eq_of_lt hx]

theorem t1a_pk_tree_w5 (outs : List ℕ) (o k P : ℕ) {fuel e m s x : ℕ}
    (hx : x < P) (hM : wPack e outs &&& m = s &&& m)
    (hT : allTree fuel 0 k (fun i ↦
      Bool.and (m.testBit (o + i)) (b2BEq (s.testBit (o + i)) (x.testBit i))) = true)
    (hbq : listBeqNatT1 (t1EvOutSlice outs o k)
      (t1EvWireSlice (fun i ↦ outW outs (o + i)) 0 k) = true := by decide +kernel)
    (hP : 2 ^ k = P := by rfl) : wPack e (t1EvOutSlice outs o k) = x :=
  t1a_pk outs o k P hx (fun i hi ↦ by
    obtain ⟨mi, si⟩ := Bool.and_eq_true_iff.mp (allTree_zero hT hi)
    exact t1a_mb hM mi si) hbq hP

theorem t1a_sp4 (na : ℕ) : nucSpNatT1 na < 4 := by
  unfold nucSpNatT1
  cases Nat.blt na 23 <;> cases Nat.blt na 43 <;> cases Nat.blt na 46 <;> decide

theorem t1a_r4 {h : ℕ} (x : ℕ) (hh : h < 3) :
    let r := h + 4 * (x % 64)
    h + 2 ^ 2 * ((x / 2 ^ 0) % 2 ^ 6) = r ∧ r % 4 = h ∧ (r / 4) % 64 = x % 64 ∧ r < 256 := by
  set u := x % 64
  have hu : u < 64 := Nat.mod_lt x (by decide)
  have pq := t1a_dmod u 4 (Nat.lt_trans hh (by decide))
  exact ⟨by rw [pow_zero, Nat.div_one]; rfl, pq.1, by rw [pq.2, Nat.mod_eq_of_lt hu], by omega⟩

theorem t1a_lo10_mod64 (v : ℕ) : (v / 2 ^ 5) % 2 ^ 6 = ((v / 32) % 1048576 % 1024) % 64 := by
  change (v / 32) % 64 = _
  rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 1024),
      Nat.mod_mod_of_dvd _ (by decide +kernel : 64 ∣ 1048576)]

theorem t1b_wPack_in05 (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) t1aIn05 = (t1EvPx c).2.1 + 4 * (t1EvB8 c % 64) := by
  have a5 := t1a_r4 (t1EvB8 c) (t1Ev_b2_props c).2.1
  rw [show t1aIn05 = t1EvOutSlice tier1Out02 5 2 ++ t1EvWireSlice b8T1W 0 6
        from listBeqNatT1_imp (by decide +kernel),
      t1Ev_wPack_append, t1Ev_len_outSlice, (mEv_out02_slices c).2.1,
      wPack_t1a_eq_k3708_lt26 c (by decide +kernel),
      t1Ev_wPack_wireSlice _ b8T1W (t1EvB8 c) 0 6
        (fun i hi ↦ by simpa only [Nat.zero_add] using t1Ev_wBit_b8T1W c (by omega))]
  exact a5.1

theorem t1b_wPack_in06 (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) t1aIn06 = (t1aEvPy c).2.1 + 4 * (t1EvLo10 c % 64) := by
  rw [show t1aIn06 = t1EvOutSlice t1aOut03 4 2 ++ t1EvWireSlice coinW 5 6
        from listBeqNatT1_imp (by decide +kernel),
      t1Ev_wPack_append, t1Ev_len_outSlice, (mEv_out03_slices c).2.1,
      t1Ev_wPack_wireSlice _ coinW c.val 5 6 (fun i hi ↦ mEv_wBit_coinW c (by omega)),
      t1a_lo10_mod64 c.val, show (2 : ℕ) ^ 2 = 4 from rfl]
  rfl

theorem t1a_imp_and4_w5 {b x1 x2 x3 x4 : Bool}
    (h : Bool.or (Bool.not b) (Bool.and x1 (Bool.and x2 (Bool.and x3 x4))) = true)
    (hb : b = true) : x1 = true ∧ x2 = true ∧ x3 = true ∧ x4 = true := by
  rw [hb, Bool.not_true, Bool.false_or] at h
  exact t1Ev_and4 h

theorem t1aEv_out05_06_all (c : Fin (2 ^ 41)) : (wBit (envTier1Sym96 c)
    (outW t1aOut05 0) = (t1EvD1 c).1 ∧ wBit (envTier1Sym96 c) (outW t1aOut06 0) = (t1aEvD2 c).1 ∧
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut06 9 8) = t1aEvZ2 c ∧ ((t1EvD1 c).1 = true →
    mEvNa1Hw c = (t1EvD1 c).2.val ∧ mEvSp1Hw c = nucSpNatT1 (t1EvD1 c).2.val) ∧ ((t1aEvD2 c).1 =
    true → mEvNa2Hw c = (t1aEvD2 c).2.val ∧ mEvSp2Hw c = nucSpNatT1 (t1aEvD2 c).2.val)) ∧
    wBit (envTier1Sym96 c) (outW t1aOut05 9) = t1aEvTax c ∧ wBit (envTier1Sym96 c)
    (outW t1aOut06 17) = Nat.ble 48 (t1EvLo10 c % 64) ∧ ((t1EvD1 c).1 = true →
    wBit (envTier1Sym96 c) (outW t1aOut05 10) = Bool.or (Nat.beq ((t1EvD1 c).2.val / 8) 3)
    (Nat.beq ((t1EvD1 c).2.val / 8) 4)) ∧ ((t1aEvD2 c).1 = true → wBit (envTier1Sym96 c)
    (outW t1aOut06 18) = Bool.or (Nat.beq ((t1aEvD2 c).2.val / 8) 3)
    (Nat.beq ((t1aEvD2 c).2.val / 8) 4)) := by
  set e := envTier1Sym96 c
  have a5 := t1a_r4 (t1EvB8 c) (t1Ev_b2_props c).2.1;
  have a6 := t1a_r4 (t1EvLo10 c) (t1aEv_b6_props c).2.1
  have hIn5 : wPack e t1aIn05 = (t1EvPx c).2.1 + 4 * (t1EvB8 c % 64) := t1b_wPack_in05 c
  have hIn6 : wPack e t1aIn06 = (t1aEvPy c).2.1 + 4 * (t1EvLo10 c % 64) := t1b_wPack_in06 c
  have hM5 :=
      wPack_t1aOut05 c
      (by rw [hIn5, careTier1_05, a5.2.1]; exact Nat.blt_eq.mpr (t1Ev_b2_props c).2.1)
  have hM6 :=
      wPack_t1aOut06 c
      (by rw [hIn6, careTier1_06, a6.2.1]; exact Nat.blt_eq.mpr (t1aEv_b6_props c).2.1)
  rw [hIn5] at hM5; rw [hIn6] at hM6
  have c5 := allTree_zero t1a_cert_nuc05 a5.2.2.2; have c6 := allTree_zero t1a_cert_nuc06 a6.2.2.2
  dsimp only at c5 c6; rw [a5.2.1, a5.2.2.1] at c5; rw [a6.2.1, a6.2.2.1] at c6
  obtain ⟨m50, s50, m59, c5⟩ := t1Ev_and4 c5
  obtain ⟨s59, v5⟩ := Bool.and_eq_true_iff.mp c5
  obtain ⟨⟨m60, s60, maskSp617, s617, z6⟩, v6⟩ := t1a_sp5 c6
  have h5 := t1a_imp_and4_w5 v5
  have h6 := t1a_imp_and4_w5 v6
  have d1Lt := Nat.lt_trans (t1EvD1 c).2.isLt (by decide : 47 < 64)
  have d2Lt := Nat.lt_trans (t1aEvD2 c).2.isLt (by decide : 47 < 64)
  exact ⟨⟨t1a_mb hM5 m50 s50, t1a_mb hM6 m60 s60,
    t1a_pk_tree_w5 t1aOut06 9 8 256 (t1aEv_u1_z2_bounds c).2.1 hM6 z6,
    fun hv ↦ ⟨t1a_pk_tree_w5 t1aOut05 3 6 64 d1Lt hM5 (h5 hv).2.2.2,
      t1a_pk_tree_w5 t1aOut05 1 2 4 (t1a_sp4 (t1EvD1 c).2.val) hM5 (h5 hv).2.2.1⟩,
    fun hv ↦ ⟨t1a_pk_tree_w5 t1aOut06 3 6 64 d2Lt hM6 (h6 hv).2.2.2,
      t1a_pk_tree_w5 t1aOut06 1 2 4 (t1a_sp4 (t1aEvD2 c).2.val) hM6 (h6 hv).2.2.1⟩⟩,
    t1a_mb hM5 m59 s59, t1a_mb hM6 maskSp617 s617,
    fun hv ↦ t1a_mb hM5 (h5 hv).1 (h5 hv).2.1, fun hv ↦ t1a_mb hM6 (h6 hv).1 (h6 hv).2.1⟩

theorem mEv_out05_06_bits (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (outW t1aOut05 0) = (t1EvD1 c).1 ∧ wBit (envTier1Sym96 c) (outW t1aOut06 0) = (t1aEvD2 c).1 ∧
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut06 9 8) = t1aEvZ2 c ∧ ((t1EvD1 c).1 = true →
    mEvNa1Hw c = (t1EvD1 c).2.val ∧ mEvSp1Hw c = nucSpNatT1 (t1EvD1 c).2.val) ∧ ((t1aEvD2 c).1 =
    true → mEvNa2Hw c = (t1aEvD2 c).2.val ∧ mEvSp2Hw c = nucSpNatT1 (t1aEvD2 c).2.val) :=
    (t1aEv_out05_06_all c).1
theorem mEv_or_shl_eq_add {a b k : ℕ} (ha : a < 2 ^ k) :
    a ||| (b <<< k) = a + 2 ^ k * b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hik : i ≥ k
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hik)),
        Bool.false_or, decide_eq_true hik, Bool.true_and]
    conv_rhs => rw [(Nat.sub_add_cancel hik).symm, ← Nat.testBit_div_two_pow,
      Nat.add_mul_div_left a b (Nat.two_pow_pos k), Nat.div_eq_of_lt ha, Nat.zero_add]
  · rw [decide_eq_false hik, Bool.false_and, Bool.or_false, ← b2_testBit_mod_pow (a + 2 ^ k *
        b) k i (Nat.lt_of_not_le hik), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
theorem mEv_step_or_shl {acc cur b k : ℕ} (hEq : acc = cur) (hLt : cur < 2 ^ k) :
    acc ||| (b <<< k) = cur + 2 ^ k * b := by rw [hEq]; exact mEv_or_shl_eq_add hLt
theorem mEv_ite10_eq_cond (b : Bool) : (if b then 1 else 0) = cond b 1 0 := by cases b <;> rfl
theorem mEv_and_mask_of_lt {x m k : ℕ} (hm : m = 2 ^ k - 1) (hx : x < 2 ^ k) :
    x &&& m = x := by rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
theorem pkBitmk (m k : ℕ) {x : ℕ} (hx : x < 2 ^ k) (hm : m = 2 ^ k - 1 := by rfl) :
    x &&& m = x := mEv_and_mask_of_lt hm hx
theorem pkBitst (k Q R : ℕ) {P acc cur b : ℕ}
    (hEq : acc = cur) (hCur : cur < P) (hb : b < Q)
    (hP : 2 ^ k = P := by rfl) (hPQ : P * Q = R := by rfl) :
    acc ||| (b <<< k) = cur + P * b ∧ cur + P * b < R := by
  refine ⟨by rw [← hP]; exact mEv_step_or_shl hEq (by rwa [hP]), ?_⟩
  rw [← hPQ]
  calc cur + P * b < P + P * b := Nat.add_lt_add_right hCur _
    _ = P * (b + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ P * Q := Nat.mul_le_mul_left P hb
theorem mEv_packOut40_eq_add (hasN1 hasN2 : Bool) {n1 n2 : ℕ} (hn1 : n1 < 64) (hn2 : n2 < 64)
    (hasE1 hasE2 : Bool) {e1 e2 : ℕ} (he1 : e1 < 256) (he2 : e2 < 256)
    (isScreen isPot isKin isNN : Bool) {sp1 aux2 : ℕ} (hsp1 : sp1 < 4) (haux2 : aux2 < 4) :
    packOut40ZeroNErem hasN1 hasN2 n1 n2 hasE1 hasE2 e1 e2 isScreen isPot isKin isNN sp1 aux2 =
    cond hasN1 1 0 + 2 * cond hasN2 1 0 + 4 * n1 + 256 * n2 + 16384 * cond hasE1 1 0 + 32768 *
    cond hasE2 1 0 + 65536 * e1 + 16777216 * e2 + 4294967296 * cond isScreen 1 0 + 8589934592 *
    cond isPot 1 0 + 17179869184 * cond isKin 1 0 + 34359738368 * cond isNN 1 0 + 68719476736 *
    sp1 + 274877906944 * aux2 := by
  unfold packOut40ZeroNErem; simp only [mEv_ite10_eq_cond]
  rw [pkBitmk 63 6 hn1, pkBitmk 63 6 hn2, pkBitmk 255 8 he1, pkBitmk 255 8 he2, pkBitmk 3 2 hsp1,
      pkBitmk 3 2 haux2]; have p1 :=
                            pkBitst 1 2 4 rfl (t1Ev_cond_lt2 hasN1)
                            (t1Ev_cond_lt2 hasN2); have p2 :=
                                                     pkBitst 2 64 256 p1.1 p1.2 hn1;
                                                     have p3 :=
                                                     pkBitst 8 64 16384 p2.1 p2.2 hn2;
                                                     have p4 :=
                                                     pkBitst 14 2 32768 p3.1 p3.2 (t1Ev_cond_lt2
                                                     hasE1);
                                                     have p5 :=
                                                     pkBitst 15 2 65536 p4.1 p4.2 (t1Ev_cond_lt2
                                                     hasE2);
                                                     have p6 :=
                                                     pkBitst 16 256 16777216 p5.1 p5.2 he1;
                                                     have p7 :=
                                                     pkBitst 24 256 4294967296 p6.1 p6.2 he2;
                                                     have p8 :=
                                                     pkBitst 32 2 8589934592 p7.1 p7.2
                                                     (t1Ev_cond_lt2 isScreen);
                                                     have p9 :=
                                                     pkBitst 33 2 17179869184 p8.1 p8.2
                                                     (t1Ev_cond_lt2 isPot);
                                                     have p10 :=
                                                     pkBitst 34 2 34359738368 p9.1 p9.2
                                                     (t1Ev_cond_lt2 isKin);
                                                     have p11 :=
                                                     pkBitst 35 2 68719476736 p10.1 p10.2
                                                     (t1Ev_cond_lt2 isNN);
                                                     have p12 :=
                                                     pkBitst 36 4 274877906944 p11.1 p11.2 hsp1;
                                                     exact (pkBitst 38 4 1099511627776 p12.1 p12.2
                                                     haux2).1
theorem mEv_field_bit_at {v P Q sh k x j i : ℕ} (hj : j = sh + i) (hP : P = 2 ^ sh)
    (hQ : Q = 2 ^ k) (hi : i < k) (hEq : (v / P) % Q = x) : v.testBit j = x.testBit i := by
  rw [hj, ← hEq, hP, hQ, b2_testBit_mod_pow _ k i hi, Nat.testBit_div_two_pow, Nat.add_comm i sh]
theorem mEv_div_pow_bit {x P k j : ℕ} (hP : P = 2 ^ k) :
    (x / P).testBit j = x.testBit (j + k) := by rw [hP, Nat.testBit_div_two_pow]
theorem mEv_mod_pow_bit {x Q k i : ℕ} (hQ : Q = 2 ^ k) (hi : i < k) :
    (x % Q).testBit i = x.testBit i := by rw [hQ, b2_testBit_mod_pow x k i hi]
theorem mEv_three_bits {x : ℕ} {a b c : Bool} (h : x = cond a 1 0 + cond b 2 0 + cond c 4 0) :
    x.testBit 0 = a ∧ x.testBit 1 = b ∧ x.testBit 2 = c := by
  rw [h]; cases a <;> cases b <;> cases c <;> exact ⟨rfl, rfl, rfl⟩
theorem mEv_nat_xor_lt_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.xor a b < 2 ^ k := by rw [nat_xor_eq]; exact Nat.xor_lt_two_pow ha hb
/-- Low `14` symbolic output masks `symOuts40Tier1Sym96[0..13]`. -/
def mEvSymLo14 : List ℕ :=
  Nat.xor isPotT1aW (outW t1aOut21 1) :: outW t1aOut20 1 ::
    (t1EvWireSlice n1T1aW 0 6 ++ t1EvWireSlice n2T1aW 0 6)
/-- Middle `18` symbolic output masks `symOuts40Tier1Sym96[14..31]`. -/
def mEvSymMid18 : List ℕ :=
  Nat.xor isPotT1aW (outW t1aOut21 0) :: outW t1aOut20 0 ::
    (t1EvWireSlice e1T1aW 0 8 ++ t1EvWireSlice e2T1aW 0 8)
/-- High `8` symbolic output masks `symOuts40Tier1Sym96[32..39]`. -/
def mEvSymHi8 : List ℕ :=
    Nat.xor (outW t1aOut20 0) (outW t1aOut20 1) :: isPotT1aW :: Nat.xor (outW t1aOut21 0)
    (outW t1aOut21 1) :: outW t1aOut20 1 :: (t1EvOutSlice t1aOut24 5 2 ++
    t1EvWireSlice aux2T1aW 0 2)
theorem mEv_len_symLo14 : mEvSymLo14.length = 14 := rfl
theorem mEv_len_symMid18 : mEvSymMid18.length = 18 := rfl
theorem pkBitfb (P Q sh k : ℕ) {v x j i : ℕ}
    (hj : j = sh + i) (hi : i < k) (hEq : (v / P) % Q = x)
    (hP : P = 2 ^ sh := by rfl) (hQ : Q = 2 ^ k := by rfl) : v.testBit j = x.testBit i :=
  mEv_field_bit_at hj hP hQ hi hEq
theorem pkBitdb (P k : ℕ) {x j : ℕ} (hP : P = 2 ^ k := by rfl) :
    (x / P).testBit j = x.testBit (j + k) := mEv_div_pow_bit hP
theorem pkBitmb (Q k : ℕ) {x i : ℕ} (hi : i < k) (hQ : Q = 2 ^ k := by rfl) :
    (x % Q).testBit i = x.testBit i := mEv_mod_pow_bit hQ hi
theorem pkBitws {e x : ℕ} (f : ℕ → ℕ) (k : ℕ) (hb : ∀ i < k, wBit e (f i) = x.testBit i) :
    wPack e (t1EvWireSlice f 0 k) = x % 2 ^ k := by
  rw [t1Ev_wPack_wireSlice e f x 0 k (fun i hi ↦ by rw [Nat.zero_add]; exact hb i hi),
      pow_zero, Nat.div_one]
theorem pkBitsl {i a b n : ℕ} (h : a + b = n) (hge : a ≤ i) (hi : i < n) :
    i - a < b := by subst h; omega
theorem pkBita2 {i : ℕ} (hge : 2 ≤ i) : 2 + i = 4 + (i - 2) := by omega
theorem pkBitd1 {x y Q : ℕ} (hx : x < Q) : (x + Q * y) / 1 % Q = x := by
  rw [Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
theorem pkBitdt {lo x P Q : ℕ} (hlo : lo < P) (hx : x < Q) (hP : 0 < P := by omega) :
    (lo + P * x) / P % Q = x := by
  rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hlo, Nat.zero_add, Nat.mod_eq_of_lt hx]
theorem pkBit21 (a b : Bool) {x : ℕ} (hx : x < 4) :
    let v := cond a 1 0 + 2 * cond b 1 0 + 4 * x
    (v / 1) % 2 = cond a 1 0 ∧ (v / 2) % 2 = cond b 1 0 ∧ (v / 4) % 4 = x := by
  cases a <;> cases b <;> dsimp only [cond] <;> refine ⟨by omega, by omega, by omega⟩

theorem pkBit22 (s : Bool) {u1 u2 : ℕ} (hu1 : u1 < 16) (hu2 : u2 < 16) :
    let v := cond s 1 0 + 2 * u1 + 32 * u2
    (v / 2) % 16 = u1 ∧ (v / 32) % 16 = u2 := by
  cases s <;> dsimp only [cond] <;> exact ⟨by omega, by omega⟩

theorem pkBit24 (s : Bool) {u1 u2 p1 p2 : ℕ}
    (hu1 : u1 < 4) (hu2 : u2 < 4) (hp1 : p1 < 4) (hp2 : p2 < 4) :
    let v := cond s 1 0 + 2 * u1 + 8 * u2 + 32 * p1 + 128 * p2
    (v / 2) % 4 = u1 ∧ (v / 8) % 4 = u2 ∧ (v / 32) % 4 = p1 ∧ (v / 128) % 4 = p2 := by
  cases s <;> dsimp only [cond] <;> exact ⟨by omega, by omega, by omega, by omega⟩

theorem pkBitll (a b c d : ℕ) :
    a + 2 * (b + 2 * (c + 64 * d)) = a + 2 * b + 4 * c + 256 * d := by omega
theorem pkBitlm (a b c d : ℕ) :
    a + 2 * (b + 2 * (c + 256 * d)) = a + 2 * b + 4 * c + 1024 * d := by omega
theorem pkBitlh (a b c d s x : ℕ) :
    a + 2 * (b + 2 * (c + 2 * (d + 2 * (s + 4 * x)))) =
      a + 2 * b + 4 * c + 8 * d + 16 * s + 64 * x := by omega
theorem pkBitl4 (a b c d f g h i j k l m n p : ℕ) :
    (a + 2 * b + 4 * c + 256 * d) +
      16384 * ((f + 2 * g + 4 * h + 1024 * i) +
        262144 * (j + 2 * k + 4 * l + 8 * m + 16 * n + 64 * p)) =
      a + 2 * b + 4 * c + 256 * d + 16384 * f + 32768 * g + 65536 * h +
        16777216 * i + 4294967296 * j + 8589934592 * k + 17179869184 * l +
        34359738368 * m + 68719476736 * n + 274877906944 * p := by
  omega

theorem pkBitsb (s S P_lo sh_lo P_hi sh_hi : ℕ) {n e vLo vHi x i idxH : ℕ}
    {oLo oHi : List ℕ}
    (hi : i < n) (hwL : wPack e oLo = vLo) (hwH : wPack e oHi = vHi)
    (hdL : (vLo / P_lo) % S = x % S) (hdH : (vHi / P_hi) % 16 = x / S)
    (hIdx : s ≤ i → idxH = sh_hi + (i - s))
    (hs : s + 4 = n := by rfl) (hS : 2 ^ s = S := by rfl)
    (hPl : P_lo = 2 ^ sh_lo := by rfl) (hPh : P_hi = 2 ^ sh_hi := by rfl) :
    wBit e (cond (Nat.blt i s) (outW oLo (sh_lo + i)) (outW oHi idxH)) = x.testBit i := by
  cases hlt : Nat.blt i s
  · have hge := (blt_eq_false_iff i s).mp hlt
    dsimp only [cond]
    rw [t1Ev_wBit_outW, hwH, pkBitfb P_hi 16 sh_hi 4 (hIdx hge) (pkBitsl hs hge hi) hdH hPh rfl,
        pkBitdb S s hS.symm, Nat.sub_add_cancel hge]
  · have his := Nat.blt_eq.mp hlt
    dsimp only [cond]
    rw [t1Ev_wBit_outW, hwL, pkBitfb P_lo S sh_lo s rfl his hdL hPl hS.symm,
        pkBitmb S s his hS.symm]

theorem mEv_wPack_symOuts40_of_blocks
    (e : ℕ) (doEe doNn doEn doKel doKn swE swN : Bool)
    {e1 e2 n1P n2 sp1 sp2 axEl n1K axK : ℕ}
    (he1 : e1 < 256) (he2 : e2 < 256)
    (hn1P : n1P < 64) (hn2 : n2 < 64)
    (hsp1 : sp1 < 4) (hsp2 : sp2 < 4)
    (haxEl : axEl < 4) (hn1K : n1K < 64) (haxK : axK < 4)
    (h20 : wPack e t1aOut20 = cond doEe 1 0 + cond doNn 2 0 + cond doEn 4 0)
    (h21 : wPack e t1aOut21 = cond doKel 1 0 + cond doKn 2 0 + 4 * axEl)
    (h22 : wPack e t1aOut22 = cond swE 1 0 + 2 * (e1 % 16) + 32 * (e2 % 16))
    (h23 : wPack e t1aOut23 = (e1 / 16) + 16 * (e2 / 16))
    (h24 : wPack e t1aOut24 =
      cond swN 1 0 + 2 * (n1P % 4) + 8 * (n2 % 4) + 32 * sp1 + 128 * sp2)
    (h25 : wPack e t1aOut25 = (n1P / 4) + 16 * (n2 / 4))
    (h26 : wPack e t1aOut26 = n1K + 64 * axK) :
    let isPot := xor (xor doEe doNn) doEn
    wPack e symOuts40Tier1Sym96 =
      packOut40ZeroNErem (xor isPot doKn) doNn (Nat.xor n1P n1K) n2
        (xor isPot doKel) doEe e1 e2 (xor doEe doNn) isPot (xor doKel doKn) doNn
        sp1 (Nat.xor (Nat.xor sp2 axEl) axK) := by
  intro isPot
  have b20 := mEv_three_bits h20
  rw [show cond doKn 2 0 = 2 * cond doKn 1 0 by cases doKn <;> rfl] at h21
  have d21 := pkBit21 doKel doKn haxEl
  have d22 := pkBit22 swE (Nat.mod_lt e1 (by decide)) (Nat.mod_lt e2 (by decide))
  have d24 := pkBit24 swN (Nat.mod_lt n1P (by decide)) (Nat.mod_lt n2 (by decide)) hsp1 hsp2
  have dN1 : n1P / 4 < 16 := Nat.div_lt_of_lt_mul hn1P
  have dE1 : e1 / 16 < 16 := Nat.div_lt_of_lt_mul he1
  have h20_0 : wBit e (outW t1aOut20 0) = doEe := (t1Ev_wBit_outW _ _ _).trans b20.1
  have h20_1 : wBit e (outW t1aOut20 1) = doNn := (t1Ev_wBit_outW _ _ _).trans b20.2.1
  have h21_0 : wBit e (outW t1aOut21 0) = doKel := by
    rw [t1Ev_wBit_outW, h21, pkBitfb 1 2 0 1 rfl Nat.zero_lt_one d21.1, t1Ev_testBit0_single]
  have h21_1 : wBit e (outW t1aOut21 1) = doKn := by
    rw [t1Ev_wBit_outW, h21, pkBitfb 2 2 1 1 rfl Nat.zero_lt_one d21.2.1, t1Ev_testBit0_single]
  have hP : wBit e isPotT1aW = isPot := by
    dsimp only [isPotT1aW, isPot]
    rw [t1Ev_wBit_xor, t1Ev_wBit_xor, h20_0, h20_1, t1Ev_wBit_outW, b20.2.2]
  have bN1 : ∀ i < 6, wBit e (n1T1aW i) = (Nat.xor n1P n1K).testBit i := fun i hi ↦ by
    dsimp only [n1T1aW]
    rw [t1Ev_wBit_xor, nat_xor_eq, Nat.testBit_xor,
        pkBitsb 2 4 2 1 1 0 hi h24 h25 d24.1 (pkBitd1 dN1) (fun _ ↦ (Nat.zero_add _).symm),
        t1Ev_wBit_outW, h26, pkBitfb 1 64 0 6 (Nat.zero_add i).symm hi (pkBitd1 hn1K)]
  have bN2 : ∀ i < 6, wBit e (n2T1aW i) = n2.testBit i := fun i hi ↦
    pkBitsb 2 4 8 3 16 4 hi h24 h25 d24.2.1 (pkBitdt dN1 (Nat.div_lt_of_lt_mul hn2)) pkBita2
  have bE1 : ∀ i < 8, wBit e (e1T1aW i) = e1.testBit i := fun i hi ↦
    pkBitsb 4 16 2 1 1 0 hi h22 h23 d22.1 (pkBitd1 dE1) (fun _ ↦ (Nat.zero_add _).symm)
  have bE2 : ∀ i < 8, wBit e (e2T1aW i) = e2.testBit i := fun i hi ↦
    pkBitsb 4 16 32 5 16 4 hi h22 h23 d22.2 (pkBitdt dE1 (Nat.div_lt_of_lt_mul he2))
        (fun g ↦ (Nat.add_sub_of_le g).symm)
  have bAx : ∀ i < 2, wBit e (aux2T1aW i) = (Nat.xor (Nat.xor sp2 axEl) axK).testBit i := fun i hi ↦
      by
    dsimp only [aux2T1aW]
    rw [t1Ev_wBit_xor, t1Ev_wBit_xor, nat_xor_eq, nat_xor_eq, Nat.testBit_xor, Nat.testBit_xor,
        t1Ev_wBit_outW, h24, pkBitfb 128 4 7 2 rfl hi d24.2.2.2,
        t1Ev_wBit_outW, h21, pkBitfb 4 4 2 2 rfl hi d21.2.2,
        t1Ev_wBit_outW, h26, pkBitfb 64 4 6 2 rfl hi (pkBitdt hn1K haxK)]
  have hN1X : Nat.xor n1P n1K < 64 := mEv_nat_xor_lt_pow (k := 6) hn1P hn1K
  have hAxX : Nat.xor (Nat.xor sp2 axEl) axK < 4 :=
      mEv_nat_xor_lt_pow (k := 2) (mEv_nat_xor_lt_pow (k := 2) hsp2 haxEl) haxK
  have hLo : wPack e mEvSymLo14 = cond (xor isPot doKn) 1 0 + 2 * cond doNn 1 0 + 4 *
      Nat.xor n1P n1K + 256 * n2 := by
    dsimp only [mEvSymLo14, wPack]
    rw [t1Ev_wPack_append, t1Ev_len_wireSlice, pkBitws n1T1aW 6 bN1, pkBitws n2T1aW 6 bN2,
        t1Ev_wBit_xor, hP, h21_1, h20_1, show (2 : ℕ) ^ 6 = 64 from rfl, Nat.mod_eq_of_lt hN1X,
            Nat.mod_eq_of_lt hn2]
    exact pkBitll _ _ _ _
  have hMid : wPack e mEvSymMid18 = cond (xor isPot doKel) 1 0 + 2 * cond doEe 1 0 + 4 * e1 +
      1024 * e2 := by
    dsimp only [mEvSymMid18, wPack]
    rw [t1Ev_wPack_append, t1Ev_len_wireSlice, pkBitws e1T1aW 8 bE1, pkBitws e2T1aW 8 bE2,
        t1Ev_wBit_xor, hP, h21_0, h20_0, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mod_eq_of_lt he1,
            Nat.mod_eq_of_lt he2]
    exact pkBitlm _ _ _ _
  have hHi : wPack e mEvSymHi8 =
      cond (xor doEe doNn) 1 0 + 2 * cond isPot 1 0 + 4 * cond (xor doKel doKn) 1 0 +
        8 * cond doNn 1 0 + 16 * sp1 + 64 * Nat.xor (Nat.xor sp2 axEl) axK := by
    have hSp1 : wPack e (t1EvOutSlice t1aOut24 5 2) = sp1 := by
      rw [t1Ev_wPack_outSlice, h24]
      exact d24.2.2.1
    dsimp only [mEvSymHi8, wPack]
    rw [t1Ev_wPack_append, t1Ev_len_outSlice, hSp1, pkBitws aux2T1aW 2 bAx, hP,
        t1Ev_wBit_xor, t1Ev_wBit_xor, h21_0, h21_1, h20_0, h20_1,
        show (2 : ℕ) ^ 2 = 4 from rfl, Nat.mod_eq_of_lt hAxX]
    exact pkBitlh _ _ _ _ _ _
  rw [mEv_packOut40_eq_add _ _ hN1X hn2 _ _ he1 he2 _ _ _ _ hsp1 hAxX,
      show symOuts40Tier1Sym96 = mEvSymLo14 ++ (mEvSymMid18 ++
          mEvSymHi8) from listBeqNatT1_imp (by decide +kernel),
      t1Ev_wPack_append, t1Ev_wPack_append, mEv_len_symLo14, mEv_len_symMid18,
      hLo, hMid, hHi, show (2 : ℕ) ^ 14 = 16384 from rfl, show (2 : ℕ) ^ 18 = 262144 from rfl]
  exact pkBitl4 _ _ _ _ _ _ _ _ _ _ _ _ _ _
/-- Structural list lookup avoiding unfolding inner wire masks. -/
def mEvNth : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => mEvNth xs k
theorem mEv_nth_eq_outW : ∀ (ms : List ℕ) (q : ℕ), outW ms q = mEvNth ms q
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => mEv_nth_eq_outW xs k
theorem mEv_bitAt_wPack (e : ℕ) (ms : List ℕ) (q : ℕ) : bitAt (wPack e ms) q =
    wBit e (mEvNth ms q) := by rw [bitAt_eq_testBit, ← t1Ev_wBit_outW, mEv_nth_eq_outW]
theorem mEv_in_field_eq {e : ℕ} (P Q sh k : ℕ) (ms sub : List ℕ) (hP : P = 2 ^ sh) (hQ : Q = 2 ^ k)
    (hSub : listBeqNatT1 (t1EvOutSlice ms sh k) sub = true) : (wPack e ms / P) % Q =
    wPack e sub := by rw [hP, hQ, ← t1Ev_wPack_outSlice, listBeqNatT1_imp hSub]
theorem mEv_cond_div_mod (sw en : Bool) (a b M : ℕ) : (cond sw b (cond en a 0)) % M =
    cond sw (b % M) (cond en (a % M) 0) ∧ (cond sw b (cond en a 0)) / M = cond sw (b / M)
    (cond en (a / M) 0) ∧ (cond en (cond sw a b) 0) % M = cond en (cond sw (a % M) (b % M)) 0 ∧
    (cond en (cond sw a b) 0) / M = cond en (cond sw (a / M) (b / M)) 0 := by
  cases sw <;> cases en <;> simp [cond, Nat.zero_mod, Nat.zero_div]
theorem mEv_not_blt_of_ne {a b : ℕ} (hNe : a ≠ b) : Bool.not (Nat.blt a b) = Nat.blt b a := by
  cases h : Nat.blt a b
  · have hge := (blt_eq_false_iff a b).mp h
    exact (Nat.blt_eq.mpr (by omega)).symm
  · have hlt := Nat.blt_eq.mp h
    exact ((blt_eq_false_iff b a).mpr (by omega)).symm
theorem mEv_mux_eq_of_imp {sw en : Bool} {x1 y1 x2 y2 : ℕ} (hSw : sw = true → x2 = y2)
    (hEn : en = true → x1 = y1) : cond sw x2 (cond en x1 0) = cond sw y2 (cond en y1 0) := by
  cases h1 : sw
  · cases h2 : en
    · rfl
    · dsimp only [cond]; exact hEn h2
  · dsimp only [cond]; exact hSw h1
theorem mEv_mux2_eq_of_imp {doN sw : Bool} {x1 y1 x2 y2 : ℕ}
    (hN : doN = true → x1 = y1 ∧ x2 = y2) : cond doN (cond sw x1 x2) 0 =
    cond doN (cond sw y1 y2) 0 := by
  cases h : doN
  · rfl
  · rcases hN h with ⟨e1, e2⟩; rw [e1, e2]
theorem mEv_bitAt_0 (e m0 : ℕ) (ms : List ℕ) : bitAt (wPack e (m0 :: ms)) 0 = wBit e m0 :=
    mEv_bitAt_wPack e (m0 :: ms) 0
theorem t1a_mdp {a b B : ℕ} (ha : a < B) (hb : b < B) (hB : 0 < B := by omega) :
    (a + B * b) % B = a ∧ ((a + B * b) / B) % B = b := by
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt ha, Nat.zero_add, Nat.mod_eq_of_lt hb, and_self]
theorem t1a_cmpLo_eval_w5 (outs : List ℕ) {e a b : ℕ}
    (hM : wPack e outs &&& cond (Nat.beq a b) 2 3 =
      cond (Nat.beq a b) 2 (cond (Nat.blt a b) 1 0) &&& cond (Nat.beq a b) 2 3) :
    wBit e (outW outs 1) = Nat.beq a b ∧ (a ≠ b → wBit e (outW outs 0) = Nat.blt a b) := by
  refine ⟨?_, fun hNe ↦ ?_⟩
  · rw [t1Ev_wBit_of_masked hM (by cases Nat.beq a b <;> rfl)]
    cases Nat.beq a b <;> cases Nat.blt a b <;> rfl
  · have hF : Nat.beq a b = false := Bool.eq_false_iff.mpr fun hh ↦ hNe (Nat.eq_of_beq_eq_true hh)
    rw [hF] at hM
    rw [t1Ev_wBit_of_masked hM rfl]
    cases Nat.blt a b <;> rfl

theorem t1a_f07_eval {e a b : ℕ} (ha : a < 8) (hb : b < 8)
    (hM : (wPack e t1aOut07) &&& maskTier1_07 (a + 8 * b) =
      (specTier1_07 (a + 8 * b)) &&& maskTier1_07 (a + 8 * b)) :
    wBit e (outW t1aOut07 1) = Nat.beq a b ∧
      (a ≠ b → wBit e (outW t1aOut07 0) = Nat.blt a b) := by
  obtain ⟨hm1, hm2⟩ := t1a_mdp ha hb
  rw [maskTier1_07, specTier1_07, hm1, hm2] at hM
  exact t1a_cmpLo_eval_w5 t1aOut07 hM
theorem t1a_s36 (v : ℕ) : (v / 2 ^ 3) % 2 ^ 3 = ((v / 2 ^ 3) % 2 ^ 6) % 8 ∧ (v / 2 ^ 6) % 2 ^ 3 =
    ((v / 2 ^ 3) % 2 ^ 6) / 8 :=
  ⟨(Nat.mod_mod_of_dvd (v / 8) (by decide : 8 ∣ 64)).symm,
   show (v / 64) % 8 = ((v / 8) % 64) /
       8 by rw [show (64 : ℕ) = 8 * 8 from rfl, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul]⟩
theorem t1a_cpl (qa qb B M u0 u1 : ℕ) (hM : B * B = M) : qa + B * (qb + B * (u0 + 2 * u1)) = qa +
    B * qb + M * u0 + (2 * M) * u1 := by
  rw [Nat.mul_add B qb, ← Nat.mul_assoc B B, hM, Nat.mul_add M u0, ← Nat.mul_assoc M 2 u1,
      Nat.mul_comm M 2, ← Nat.add_assoc, ← Nat.add_assoc]
theorem t1a_chp {a b B M : ℕ} (b0 b1 : Bool) (hB : 0 < B) (hM : B * B = M) (ha : a < M)
    (hb : b < M) : a % B < B ∧ b % B < B ∧ (a / B) + B * ((b / B) + B * (cond b0 1 0 + 2 *
    cond b1 1 0)) = (a / B) + B * (b / B) + M * cond b0 1 0 + (2 * M) * cond b1 1 0 ∧
    ((a / B) + B * (b / B) + M * cond b0 1 0 + (2 * M) * cond b1 1 0) % B = a / B ∧
    (((a / B) + B * (b / B) + M * cond b0 1 0 + (2 * M) * cond b1 1 0) / B) % B = b / B ∧
    ((a / B) + B * (b / B) + M * cond b0 1 0 + (2 * M) * cond b1 1 0) / M = cond b0 1 0 + 2 *
    cond b1 1 0 ∧ ((a / B) + B * (b / B) + M * cond b0 1 0 + (2 * M) * cond b1 1 0) / (2 * M) =
    cond b1 1 0 := by
  have hqa : a / B < B := Nat.div_lt_of_lt_mul (by rwa [hM])
  have hqb : b / B < B := Nat.div_lt_of_lt_mul (by rwa [hM])
  have h1 := t1a_cpl (a / B) (b / B) B M (cond b0 1 0) (cond b1 1 0) hM
  have hD : ((a / B) + B * (b / B) + M * cond b0 1 0 + (2 * M) * cond b1 1 0) / M = cond b0 1 0 +
      2 * cond b1 1 0 := by
    rw [← h1, ← hM, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hqa,
        Nat.zero_add, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hqb, Nat.zero_add]
  refine ⟨Nat.mod_lt a hB, Nat.mod_lt b hB, h1, ?_, ?_, hD, ?_⟩
  · rw [← h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqa]
  · rw [← h1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hqa, Nat.zero_add,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqb]
  · (conv_lhs => arg 2; rw [Nat.mul_comm 2 M])
    rw [← Nat.div_div_eq_div_mul, hD]; cases b0 <;> cases b1 <;> rfl

theorem mEv_out08_bits (c : Fin (2 ^ 41)) (hd1 : (t1EvD1 c).1 = true)
    (hd2 : (t1aEvD2 c).1 = true) : wBit (envTier1Sym96 c)
    (outW t1aOut08 1) = Nat.beq (t1EvD1 c).2.val (t1aEvD2 c).2.val ∧ ((t1EvD1 c).2.val ≠
    (t1aEvD2 c).2.val → wBit (envTier1Sym96 c)
    (outW t1aOut08 0) = Nat.blt (t1EvD1 c).2.val (t1aEvD2 c).2.val) := by
  set e := envTier1Sym96 c
  have hAll := t1aEv_out05_06_all c;
  have hNa1 : mEvNa1Hw c = (t1EvD1 c).2.val := (hAll.1.2.2.2.1 hd1).1;
  have hNa2 : mEvNa2Hw c = (t1aEvD2 c).2.val := (hAll.1.2.2.2.2 hd2).1
  have hLt1 : mEvNa1Hw c < 48 := by rw [hNa1]; exact Nat.lt_trans (t1EvD1 c).2.isLt (by decide)
  have hLt2 : mEvNa2Hw c < 48 := by rw [hNa2]; exact Nat.lt_trans (t1aEvD2 c).2.isLt (by decide)
  have hS1 : wPack e (t1EvOutSlice t1aOut05 3 3) = mEvNa1Hw c % 8 ∧
      wPack e (t1EvOutSlice t1aOut05 6 3) = mEvNa1Hw c / 8 := by
    rw [mEvNa1Hw, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice]; exact t1a_s36 _
  have hS2 : wPack e (t1EvOutSlice t1aOut06 3 3) = mEvNa2Hw c % 8 ∧
      wPack e (t1EvOutSlice t1aOut06 6 3) = mEvNa2Hw c / 8 := by
    rw [mEvNa2Hw, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice]; exact t1a_s36 _
  have hIn7 : wPack e t1aIn07 = (mEvNa1Hw c % 8) + 8 * (mEvNa2Hw c % 8) := by
    rw [show t1aIn07 = t1EvOutSlice t1aOut05 3 3 ++ t1EvOutSlice t1aOut06 3 3
          from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_len_outSlice, hS1.1, hS2.1, show (2 : ℕ) ^ 3 = 8 from rfl]
  have hM7 := wPack_t1aOut07 c; rw [hIn7] at hM7
  set b0 := wBit e (outW t1aOut07 0); set b1 := wBit e (outW t1aOut07 1)
  set b8 := xor (wBit e (outW t1aOut05 10)) (wBit e (outW t1aOut06 18))
  have hP := t1a_chp (B := 8) (M := 64) b0 b1 (by decide) rfl
    (Nat.lt_trans hLt1 (by decide)) (Nat.lt_trans hLt2 (by decide))
  have h07 := t1a_f07_eval hP.1 hP.2.1 hM7
  set lo8 := (mEvNa1Hw c / 8) + 8 * (mEvNa2Hw c / 8) + 64 * cond b0 1 0 + 128 * cond b1 1 0
  have hLo8Lt : lo8 < 256 := by
    have cb0 := t1Ev_cond_lt2 b0; have cb1 := t1Ev_cond_lt2 b1
    dsimp only [lo8]; omega
  have hIn8 : wPack e t1aIn08 = lo8 + 256 * cond b8 1 0 := by
    rw [show t1aIn08 =
          (t1EvOutSlice t1aOut05 6 3 ++
            (t1EvOutSlice t1aOut06 6 3 ++ ([outW t1aOut07 0] ++ [outW t1aOut07 1]))) ++
          [Nat.xor (outW t1aOut05 10) (outW t1aOut06 18)]
          from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_wPack_append]
    simp only [List.length_append, t1Ev_len_outSlice, List.length_cons, List.length_nil,
        Nat.zero_add]
    rw [hS1.2, hS2.2, t1Ev_wPack_singleton, t1Ev_wPack_singleton, t1Ev_wPack_singleton,
        t1Ev_wBit_xor, show (2 : ℕ) ^ 3 = 8 from rfl, show (2 : ℕ) ^ 1 = 2 from rfl,
        show (2 : ℕ) ^ (3 + (3 + (1 + 1))) = 256 from rfl]
    exact congrArg (· + 256 * cond b8 1 0) hP.2.2.1
  have hMod256 : (lo8 + 256 * cond b8 1 0) % 256 = lo8 := (t1a_dmod _ 256 hLo8Lt).1
  have hMod8 : (lo8 + 256 * cond b8 1 0) % 8 = mEvNa1Hw c / 8 :=
    (show (lo8 + 256 * cond b8 1 0) % 8 = lo8 % 8 by omega).trans hP.2.2.2.1
  have hDiv8 : ((lo8 + 256 * cond b8 1 0) / 8) % 8 = mEvNa2Hw c / 8 :=
    (show ((lo8 + 256 * cond b8 1 0) / 8) % 8 = (lo8 / 8) % 8 by omega).trans hP.2.2.2.2.1
  have hBit8 : bitAt (lo8 + 256 * cond b8 1 0) 8 = b8 := by
    rw [t1Ev_bitAt_div _ 8, show (2 : ℕ) ^ 8 = 256 from rfl,
        (t1a_dmod _ 256 hLo8Lt).2, t1Ev_testBit0_single]
  have hB8Eq : b8 = xor (Bool.or (Nat.beq (mEvNa1Hw c / 8) 3) (Nat.beq (mEvNa1Hw c / 8) 4))
      (Bool.or (Nat.beq (mEvNa2Hw c / 8) 3) (Nat.beq (mEvNa2Hw c / 8) 4)) := by
    dsimp only [b8]; rw [hAll.2.2.2.1 hd1, hAll.2.2.2.2 hd2, ← hNa1, ← hNa2]
  have hCare8 : careT1a_08 (wPack e t1aIn08) = true := by
    rw [hIn8]; unfold careT1a_08; dsimp only
    rw [hMod8, hDiv8, hBit8, hB8Eq, (b2_bEq_iff _ _).mpr rfl, Bool.and_true];
    exact Bool.and_eq_true_iff.mpr ⟨Nat.blt_eq.mpr (Nat.div_lt_of_lt_mul hLt1),
        Nat.blt_eq.mpr (Nat.div_lt_of_lt_mul hLt2)⟩
  have hOut8 := wPack_t1aOut08 c hCare8
  rw [hIn8, specT1a_08, hMod256, specTier1_08, hP.2.2.2.1, hP.2.2.2.2.1,
      t1Ev_bitAt_div _ 6, show (2 : ℕ) ^ 6 = 64 from rfl, hP.2.2.2.2.2.1, t1Ev_testBit0_pair,
      t1Ev_bitAt_div _ 7, show (2 : ℕ) ^ 7 = 128 from rfl, hP.2.2.2.2.2.2,
      t1Ev_testBit0_single] at hOut8
  have hCmp := t1Ev_cmp2_hi (a := mEvNa1Hw c) (b := mEvNa2Hw c) (B := 8) (by decide) h07.2
  have hBits := t1Ev_two_bits hOut8
  rw [← hNa1, ← hNa2]
  refine ⟨by
      rw [t1Ev_wBit_outW, hBits.2, show b1 = _ from h07.1]
      exact hCmp.1,
    fun hNe ↦ by
      rw [t1Ev_wBit_outW, hBits.1]
      exact hCmp.2 hNe⟩

theorem t1a_u1_z2_slices_w5 (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut04 0 4) = t1aEvU1 c % 16 ∧
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut04 4 4) = t1aEvU1 c / 16 ∧
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut06 9 4) = t1aEvZ2 c % 16 ∧
    wPack (envTier1Sym96 c) (t1EvOutSlice t1aOut06 13 4) = t1aEvZ2 c / 16 := by
  set e := envTier1Sym96 c
  have hu := Nat.lt_trans (t1aEv_u1_z2_bounds c).1 (by decide : 187 < 256)
  have hZ : t1aEvZ2 c =
      wPack e (t1EvOutSlice t1aOut06 9 4) + 16 * wPack e (t1EvOutSlice t1aOut06 13 4) := by
    rw [← (mEv_out05_06_bits c).2.2.1, show t1EvOutSlice t1aOut06 9 8 =
          t1EvOutSlice t1aOut06 9 4 ++ t1EvOutSlice t1aOut06 13 4
          from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_len_outSlice, show (2 : ℕ) ^ 4 = 16 from rfl]
  have hZL : wPack e (t1EvOutSlice t1aOut06 9 4) < 16 := wPack_lt_pow _ _
  have hZH : wPack e (t1EvOutSlice t1aOut06 13 4) < 16 := wPack_lt_pow _ _
  refine ⟨by rw [t1Ev_wPack_outSlice, mEv_wPack_out04 c, pow_zero, Nat.div_one,
        show (2 : ℕ) ^ 4 = 16 from rfl], ?_,
    (t1a_mdp hZL hZH).1.symm.trans (congrArg (· % 16) hZ.symm),
    by rw [hZ, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hZL, Nat.zero_add]⟩
  rw [t1Ev_wPack_outSlice, mEv_wPack_out04 c, show (2 : ℕ) ^ 4 = 16 from rfl]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hu)

theorem mEv_out10_bits (c : Fin (2 ^ 41)) (hd2 : (t1aEvD2 c).1 = true) : wBit (envTier1Sym96 c)
    (outW t1aOut10 1) = Nat.beq (t1aEvU1 c) (t1aEvZ2 c) ∧ (t1aEvU1 c ≠ t1aEvZ2 c →
    wBit (envTier1Sym96 c) (outW t1aOut10 0) = Nat.blt (t1aEvU1 c) (t1aEvZ2 c)) := by
  set e := envTier1Sym96 c
  have hu192 : t1aEvU1 c < 192 := Nat.lt_trans (t1aEv_u1_z2_bounds c).1 (by decide)
  have hz192 : t1aEvZ2 c < 192 := Nat.lt_trans ((t1aEv_u1_z2_bounds c).2.2 hd2) (by decide)
  obtain ⟨hULo, hUHi, hZL_eq, hZH_eq⟩ := t1a_u1_z2_slices_w5 c
  have hIn9 : wPack e t1aIn09 = (t1aEvU1 c % 16) + 16 * (t1aEvZ2 c % 16) := by
    rw [show t1aIn09 = t1EvOutSlice t1aOut04 0 4 ++ t1EvOutSlice t1aOut06 9 4
          from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_len_outSlice, hULo, hZL_eq, show (2 : ℕ) ^ 4 = 16 from rfl]
  have hM9 := wPack_t1aOut09 c; rw [hIn9] at hM9
  set b0 := wBit e (outW t1aOut09 0); set b1 := wBit e (outW t1aOut09 1)
  have hP := t1a_chp (B := 16) (M := 256) b0 b1 (by decide) rfl
    (Nat.lt_trans hu192 (by decide)) (Nat.lt_trans hz192 (by decide))
  obtain ⟨hm1, hm2⟩ := t1a_mdp hP.1 hP.2.1
  rw [maskTier1_09, specTier1_09, hm1, hm2] at hM9
  obtain ⟨hEqLo, hLtLo⟩ : b1 = _ ∧ (_ → b0 = _) := t1a_cmpLo_eval_w5 t1aOut09 hM9
  have hIn10 : wPack e t1aIn10 = (t1aEvU1 c / 16) + 16 * (t1aEvZ2 c / 16) + 256 * cond b0 1 0 +
      512 * cond b1 1 0 := by
    rw [show t1aIn10 = t1EvOutSlice t1aOut04 4 4 ++
          (t1EvOutSlice t1aOut06 13 4 ++ ([outW t1aOut09 0] ++ [outW t1aOut09 1]))
          from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_wPack_append,
        t1Ev_len_outSlice, t1Ev_len_outSlice, List.length_cons, List.length_nil,
        hUHi, hZH_eq, t1Ev_wPack_singleton, t1Ev_wPack_singleton,
        show (2 : ℕ) ^ 4 = 16 from rfl, show (2 : ℕ) ^ 1 = 2 from rfl]
    exact hP.2.2.1
  have hCare10 : careTier1_10 (wPack e t1aIn10) = true := by
    rw [hIn10, careTier1_10, hP.2.2.2.1, hP.2.2.2.2.1];
    exact Bool.and_eq_true_iff.mpr ⟨Nat.blt_eq.mpr (Nat.div_lt_of_lt_mul hu192),
        Nat.blt_eq.mpr (Nat.div_lt_of_lt_mul hz192)⟩
  have hOut10 := wPack_t1aOut10 c hCare10
  rw [hIn10, specTier1_10, hP.2.2.2.1, hP.2.2.2.2.1,
      t1Ev_bitAt_div _ 8, show (2 : ℕ) ^ 8 = 256 from rfl, hP.2.2.2.2.2.1, t1Ev_testBit0_pair,
      t1Ev_bitAt_div _ 9, show (2 : ℕ) ^ 9 = 512 from rfl, hP.2.2.2.2.2.2,
      t1Ev_testBit0_single] at hOut10
  have hCmp := t1Ev_cmp2_hi (a := t1aEvU1 c) (b := t1aEvZ2 c) (B := 16) (by decide) hLtLo
  have hBits := t1Ev_two_bits hOut10
  refine ⟨by rw [t1Ev_wBit_outW, hBits.2, hEqLo]; exact hCmp.1,
    fun hNe ↦ by rw [t1Ev_wBit_outW, hBits.1]; exact hCmp.2 hNe⟩

theorem t1b_cert_g66_06x :
    allTree 4 0 3 (fun h2 ↦
      allTree 8 0 64 (fun lo2 ↦
        let r := h2 + 4 * lo2
        Bool.and
          (b2BEq ((fastSpec06Full r).testBit 18) (g66VOpt h2 lo2))
          (b2BEq ((fastSpec06x r).testBit 0) (lo2L2Mask64.testBit lo2)))) = true := by
  decide +kernel

theorem mEv_out06_bit18_g66 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c) (outW t1aOut06 18) =
    g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64) := by
  have h := allTree_zero (allTree_zero t1b_cert_g66_06x (t1aEv_b6_props c).2.1)
    (Nat.mod_lt (t1EvLo10 c) (by decide))
  rw [t1Ev_wBit_outW, wPack_t1bOut06Full c, t1b_wPack_in06 c];
  exact (b2_bEq_iff _ _).mp (Bool.and_eq_true_iff.mp h).1
theorem mEv_out06x_bit0 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c) (outW t1bOut06x 0) =
    lo2L2Mask64.testBit (t1EvLo10 c % 64) := by
  have h := allTree_zero (allTree_zero t1b_cert_g66_06x (t1aEv_b6_props c).2.1)
    (Nat.mod_lt (t1EvLo10 c) (by decide))
  rw [t1Ev_wBit_outW, wPack_t1bOut06x c, t1b_wPack_in06 c];
  exact (b2_bEq_iff _ _).mp (Bool.and_eq_true_iff.mp h).2
def t1bSpec08xOf (r5 r6 : ℕ) : ℕ :=
  let s5 := fastSpec05Full r5
  let s6 := fastSpec06Full r6
  let s7 := fastSpec07Full (((s5 / 8) % 8) + 8 * ((s6 / 8) % 8))
  fastSpec08x (((s5 / 64) % 8) + 8 * ((s6 / 64) % 8) + 64 * s7 +
    256 * cond (xor (s5.testBit 10) (s6.testBit 18)) 1 0)

theorem t1b_wPack_out08x (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) t1bOut08x = t1bSpec08xOf ((t1EvPx c).2.1 + 4 * (t1EvB8 c % 64))
        ((t1aEvPy c).2.1 + 4 * (t1EvLo10 c % 64)) := by
  set e := envTier1Sym96 c
  set r5 := (t1EvPx c).2.1 + 4 * (t1EvB8 c % 64)
  set r6 := (t1aEvPy c).2.1 + 4 * (t1EvLo10 c % 64)
  have hs5 : wPack e t1aOut05 = fastSpec05Full r5 := by rw [wPack_t1bOut05Full c, t1b_wPack_in05 c]
  have hs6 : wPack e t1aOut06 = fastSpec06Full r6 := by rw [wPack_t1bOut06Full c, t1b_wPack_in06 c]
  have hs7 : wPack e t1aOut07 = fastSpec07Full (((fastSpec05Full r5 / 8) % 8) + 8 *
      ((fastSpec06Full r6 / 8) % 8)) := by
    rw [wPack_t1bOut07Full c, show t1aIn07 = t1EvOutSlice t1aOut05 3 3 ++
        t1EvOutSlice t1aOut06 3 3 from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_len_outSlice, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice, hs5, hs6,
            show (2 : ℕ) ^ 3 = 8 from rfl]
  rw [wPack_t1bOut08x c, show wPack e t1aIn08 =
        ((fastSpec05Full r5 / 64) % 8) + 8 * ((fastSpec06Full r6 / 64) % 8) +
          64 * fastSpec07Full (((fastSpec05Full r5 / 8) % 8) + 8 * ((fastSpec06Full r6 / 8) % 8)) +
          256 * cond (xor ((fastSpec05Full r5).testBit 10) ((fastSpec06Full r6).testBit 18)) 1 0 by
      rw [show t1aIn08 = t1EvOutSlice t1aOut05 6 3 ++ (t1EvOutSlice t1aOut06 6 3 ++
          (t1aOut07 ++ [Nat.xor (outW t1aOut05 10) (outW t1aOut06 18)]))
            from listBeqNatT1_imp (by decide +kernel),
          t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_len_outSlice,
              t1Ev_len_outSlice,
          show t1aOut07.length = 2 from rfl, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice, hs5, hs6,
              hs7,
          t1Ev_wPack_singleton, t1Ev_wBit_xor, t1Ev_wBit_outW, t1Ev_wBit_outW, hs5, hs6,
          show (2 : ℕ) ^ 6 = 64 from rfl, show (2 : ℕ) ^ 3 = 8 from rfl, show (2 : ℕ) ^ 2 =
              4 from rfl]
      omega]
  rfl
theorem mEv_out11_bits (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (outW t1aOut11 0) = t1aEvInTile c ∧ wBit (envTier1Sym96 c)
    (outW t1aOut11 1) = t1EvKnOk c := by
  set e := envTier1Sym96 c
  have bi (j : ℕ) : bitAt (wPack e t1aIn11) j = wBit e (outW t1aIn11 j) := by
    rw [bitAt_eq_testBit, ← t1Ev_wBit_outW]
  have hOut := wPack_t1aOut11 c
  rw [specT1a_11, bi 0, bi 1, bi 2, bi 3,
      show wBit e (outW t1aIn11 0) = _ from (mEv_out02_slices c).2.2.2,
      show wBit e (outW t1aIn11 1) = _ from (mEv_out03_slices c).2.2.2.1,
      show wBit e (outW t1aIn11 2) =
          _ from (wBit_t1a_eq_k3708_lt26 c (by decide +kernel)).trans (t1Ev_wBit_out00 c),
      show wBit e (outW t1aIn11 3) = _ from (mEv_out03_slices c).2.2.2.2, Bool.not_not] at hOut
  change wPack e t1aOut11 = cond (t1aEvInTile c) 1 0 + cond (t1EvKnOk c) 2 0 at hOut
  refine ⟨?_, ?_⟩ <;> rw [t1Ev_wBit_outW, hOut] <;> cases t1aEvInTile c <;> cases t1EvKnOk c <;> rfl

theorem mEv_isX_imp_hi8_255 (c : Fin (2 ^ 41)) (hX : (t1EvPx c).2.2.2 = true) :
    Nat.beq (t1EvHi8 c) 255 = true := by
  rw [(t1Ev_b2_props c).2.2.2.1, t1EvA8] at hX
  cases h255 : Nat.beq (t1EvHi8 c) 255
  · rwa [h255, Bool.cond_false, h255] at hX
  · rfl

theorem mEv_inTile_imp (c : Fin (2 ^ 41)) (hT : t1aEvInTile c = true) : Nat.beq (t1EvHi8 c) 255 =
    false ∧ (t1EvPx c).2.2.2 = false ∧ (t1aEvPy c).2.2.2 = false ∧ t1aEvInBox c = true ∧
    t1EvKnOk c = false := by
  rcases Bool.and_eq_true_iff.mp hT with ⟨hN255, hNY⟩
  have h255 : Nat.beq (t1EvHi8 c) 255 = false := by cases h : Nat.beq (t1EvHi8 c) 255 <;> simp_all
  have hY : (t1aEvPy c).2.2.2 = false := by cases h : (t1aEvPy c).2.2.2 <;> simp_all
  have hX : (t1EvPx c).2.2.2 = false := Bool.eq_false_iff.mpr fun h ↦
    Bool.noConfusion (h255.symm.trans (mEv_isX_imp_hi8_255 c h))
  exact ⟨h255, hX, hY, by simp [t1aEvInBox, hX, hY], by simp [t1EvKnOk, hX]⟩

theorem mEv_knOk_imp (c : Fin (2 ^ 41)) (hK : t1EvKnOk c = true) : (t1EvPx c).2.2.2 = true ∧
    t1EvHi10 c < 768 ∧ Nat.beq (t1EvHi8 c) 255 = true ∧ t1aEvInBox c = false ∧ t1aEvInTile c =
    false := by
  rcases Bool.and_eq_true_iff.mp hK with ⟨hX, h768⟩
  have h255 := mEv_isX_imp_hi8_255 c hX
  exact ⟨hX, Nat.blt_eq.mp h768, h255, by simp [t1aEvInBox, hX], by simp [t1aEvInTile, h255]⟩
theorem eff12_pack7 (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    cond b0 1 0 + 2 * (cond b1 1 0 + 2 * (cond b2 1 0 + 2 * (cond b3 1 0 + 2 * (cond b4 1 0 + 2 *
        (cond b5 1 0 + 2 * (cond b6 1 0 + 2 * 0)))))) =
      cond b0 1 0 + cond b1 2 0 + cond b2 4 0 + cond b3 8 0 + cond b4 16 0 + cond b5 32 0 +
          cond b6 64 0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> rfl

def t1bEffIn12 : List ℕ :=
    [outW t1aOut11 0, outW tier1Out02 7, outW tier1Out02 8, outW tier1Out02 9, outW t1aOut03 6,
    outW t1aOut03 7, outW t1aOut03 8, outW t1aOut03 9, outW t1aOut03 10, outW t1aOut06 18]
def specSymEff12 (r : ℕ) : ℕ :=
  let s12 := specSym_12 (r % 512)
  let s12b := specT1b_12b (cond (s12.testBit 5) 1 0 + 2 * ((r / 512) % 2))
  cond (s12.testBit 0) 1 0 + cond (s12.testBit 1) 2 0 +
    cond (s12.testBit 2) 4 0 + cond (s12.testBit 3) 8 0 +
    cond (xor (s12.testBit 4) (s12b.testBit 0)) 16 0 +
    cond (s12b.testBit 1) 32 0 +
    cond (s12.testBit 6) 64 0

theorem specSymEff12_of_bit0_false {r : ℕ} (h0 : bitAt r 0 = false) : specSymEff12 r = 0 := by
  have hs12 : specSym_12 (r % 512) = 0 := by
    dsimp only [specSym_12]
    rw [show bitAt (r % 512) 0 =
        false
        by rw [bitAt_eq_testBit, show (512 : ℕ) = 2 ^ 9 from rfl,
             b2_testBit_mod_pow r 9 0 (by decide), ← bitAt_eq_testBit, h0]]
    rfl
  have hs12b : specT1b_12b (0 + 2 * ((r / 512) % 2)) = 0 := by
    dsimp only [specT1b_12b]
    rw [show bitAt (0 + 2 * ((r / 512) % 2)) 0 =
        false by rw [show 0 + 2 * ((r / 512) % 2) = cond false 1 0 + 2 * ((r / 512) % 2) from rfl,
                   t1Ev_bitAt_zero]]
    rfl
  simp only [specSymEff12, hs12, Nat.zero_testBit, cond, hs12b, bne_self_eq_false]
theorem wPack_t1aEff12 (c : Fin (2 ^ 41))
    (hCare : careTier1Walk_12 (wPack (envTier1Sym96 c) t1bEffIn12) = true) :
    wPack (envTier1Sym96 c) t1aEff12 = specSymEff12 (wPack (envTier1Sym96 c) t1bEffIn12) := by
  set e := envTier1Sym96 c
  set a := wPack e t1aIn12
  set g := cond (wBit e (outW t1aOut06 18)) 1 0
  have ha : a < 512 := wPack_lt_pow e t1aIn12; have hg : g < 2 := t1Ev_cond_lt2 _
  have hSplit : wPack e t1bEffIn12 = a + 512 * g := by
    rw [show t1bEffIn12 = t1aIn12 ++ [outW t1aOut06 18] from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append,
      show t1aIn12.length = 9 from rfl, show 2 ^ 9 = 512 from rfl, t1Ev_wPack_singleton]
  have hMod : (a + 512 * g) % 512 = a := by omega
  have hDiv : ((a + 512 * g) / 512) % 2 = g := by omega
  have hCareA : careTier1Walk_12 a = true := by
    rw [← hMod, careTier1Walk_12_mod512, ← hSplit]
    exact hCare
  have h12 : wPack e t1aOut12 = specSym_12 a := wPack_t1aOut12 c hCareA
  have h12b : wPack e t1aOut12b = specT1b_12b (cond ((specSym_12 a).testBit 5) 1 0 + 2 * g) := by
    rw [wPack_t1aOut12b c]; dsimp only [t1aIn12b, wPack]
    rw [t1Ev_wBit_outW, h12]; exact congrArg specT1b_12b (by dsimp only [g, e]; omega)
  dsimp only [t1aEff12, wPack];
  rw [t1Ev_wBit_xor, t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW,
      t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW, h12, h12b, hSplit, eff12_pack7]
  dsimp only [specSymEff12]
  rw [hMod, hDiv]

def mEvRawR12 (c : Fin (2 ^ 41)) : ℕ :=
    cond (t1aEvInTile c) 1 0 + 2 * (t1EvPx c).2.2.1 + 16 * (t1aEvPy c).2.2.1
def mEvRawB12 (c : Fin (2 ^ 41)) : ℕ := specSym_12 (mEvRawR12 c)

def mEvR12 (c : Fin (2 ^ 41)) : ℕ :=
    mEvRawR12 c + 512 * cond (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64)) 1 0
def mEvB12 (c : Fin (2 ^ 41)) : ℕ := specSymEff12 (mEvR12 c)

theorem mr_e2_r12 (t g : Bool) {q5 q31 : ℕ} (hq5 : q5 < 8) (hq31 : q31 < 32) :
    let a := cond t 1 0 + 2 * q5 + 16 * q31
    let r := a + 512 * cond g 1 0
    a < 512 ∧ r < 1024 ∧ cond t 1 0 + 2 * (q5 + 8 * q31) = a ∧ cond t 1 0 + 2 *
        (q5 + 8 * (q31 + 32 * cond g 1 0)) = r ∧
    a = cond t 1 0 + 2 * (q5 + 8 * q31) ∧ r = cond t 1 0 + 2 * (q5 + 8 * q31 + 256 * cond g 1 0) ∧
    (a / 2) % 8 = q5 ∧ (a / 16) % 32 = q31 ∧ (r / 2) % 8 = q5 ∧ (r / 16) % 32 = q31 := by
  cases t <;> cases g <;> dsimp only [cond] <;> exact ⟨by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem mEv_r12_lt (c : Fin (2 ^ 41)) : mEvR12 c < 1024 :=
    (mr_e2_r12 (t1aEvInTile c) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))
    (t1Ev_b2_props c).2.2.1 (t1aEv_b6_props c).2.2.1).2.1
theorem mEv_wPack_rawOut12 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut12 =
    mEvRawB12 c := by
  have hA :=
      mr_e2_r12 (t1aEvInTile c) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))
      (t1Ev_b2_props c).2.2.1 (t1aEv_b6_props c).2.2.1
  have hIn : wPack (envTier1Sym96 c) t1aIn12 = mEvRawR12 c := by
    simpa only [show t1aIn12 = [outW t1aOut11 0] ++ (t1EvOutSlice tier1Out02 7 3 ++
        t1EvOutSlice t1aOut03 6 5) from listBeqNatT1_imp (by decide +kernel),
      t1Ev_wPack_append, List.length_cons, List.length_nil, t1Ev_len_outSlice, t1Ev_wPack_singleton,
          (mEv_out11_bits c).1, (mEv_out02_slices c).2.2.1, (mEv_out03_slices c).2.2.1,
      mEvRawR12, show (2 : ℕ) ^ 1 = 2 from rfl, show (2 : ℕ) ^ 3 = 8 from rfl] using hA.2.2.1
  have hCare : careTier1Walk_12 (wPack (envTier1Sym96 c) t1aIn12) = true := by
    rw [hIn, careTier1Walk_12, show bitAt (mEvRawR12 c) 0 =
        t1aEvInTile c by rw [mEvRawR12, hA.2.2.2.2.1, t1Ev_bitAt_zero]]
    dsimp only [mEvRawR12]
    rw [hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1]
    cases hT : t1aEvInTile c
    · rfl
    · rcases mEv_inTile_imp c hT with ⟨_, hXF, hYF, _, _⟩
      exact Bool.and_eq_true_iff.mpr ⟨Nat.ble_eq.mpr ((t1Ev_b2_props c).2.2.2.2 hXF),
          Nat.ble_eq.mpr ((t1aEv_b6_props c).2.2.2.2 hYF)⟩
  rw [wPack_t1aOut12 c hCare, hIn]
  rfl

theorem mEv_wPack_out12 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aEff12 =
    specSymEff12 (mEvR12 c) := by
  have hA :=
      mr_e2_r12 (t1aEvInTile c) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))
      (t1Ev_b2_props c).2.2.1 (t1aEv_b6_props c).2.2.1
  have hIn : wPack (envTier1Sym96 c) t1bEffIn12 = mEvR12 c := by
    simpa only [show t1bEffIn12 = [outW t1aOut11 0] ++ (t1EvOutSlice tier1Out02 7 3 ++
        (t1EvOutSlice t1aOut03 6 5 ++
        [outW t1aOut06 18])) from listBeqNatT1_imp (by decide +kernel),
      t1Ev_wPack_append, List.length_cons, List.length_nil, t1Ev_len_outSlice, t1Ev_wPack_singleton,
          (mEv_out11_bits c).1, (mEv_out02_slices c).2.2.1, (mEv_out03_slices c).2.2.1,
      mEv_out06_bit18_g66 c, mEvR12, mEvRawR12, show (2 : ℕ) ^ 1 = 2 from rfl,
      show (2 : ℕ) ^ 3 = 8 from rfl, show (2 : ℕ) ^ 5 = 32 from rfl] using hA.2.2.2.1
  have hCare : careTier1Walk_12 (wPack (envTier1Sym96 c) t1bEffIn12) = true := by
    rw [hIn, careTier1Walk_12, show bitAt (mEvR12 c) 0 =
        t1aEvInTile c by rw [mEvR12, mEvRawR12, hA.2.2.2.2.2.1, t1Ev_bitAt_zero]]
    dsimp only [mEvR12, mEvRawR12]
    rw [hA.2.2.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.2.2]
    cases hT : t1aEvInTile c
    · rfl
    · rcases mEv_inTile_imp c hT with ⟨_, hXF, hYF, _, _⟩
      exact Bool.and_eq_true_iff.mpr ⟨Nat.ble_eq.mpr ((t1Ev_b2_props c).2.2.2.2 hXF),
          Nat.ble_eq.mpr ((t1aEv_b6_props c).2.2.2.2 hYF)⟩
  rw [wPack_t1aEff12 c hCare, hIn]

theorem t1b_cert_raw12_eff12 :
    allTree 11 0 1024 (fun r ↦
      let raw := specSym_12 (r % 512)
      let eff := specSymEff12 r
      Bool.and (b2BEq (raw.testBit 1) (eff.testBit 1))
        (Bool.and (b2BEq (raw.testBit 3) (eff.testBit 3))
          (Bool.and (b2BEq (raw.testBit 6) (eff.testBit 6))
            (Bool.or (Bool.not (eff.testBit 5)) (raw.testBit 5))))) = true := by decide +kernel

theorem mEv_rawB12_bits (c : Fin (2 ^ 41)) : (mEvRawB12 c).testBit 1 = (mEvB12 c).testBit 1 ∧
    (mEvRawB12 c).testBit 3 = (mEvB12 c).testBit 3 ∧ (mEvRawB12 c).testBit 6 =
    (mEvB12 c).testBit 6 ∧ ((mEvB12 c).testBit 5 = true → (mEvRawB12 c).testBit 5 = true) := by
  have hA :=
      mr_e2_r12 (t1aEvInTile c) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))
      (t1Ev_b2_props c).2.2.1 (t1aEv_b6_props c).2.2.1
  have hMod : mEvR12 c % 512 = mEvRawR12 c := by
    have h1 := hA.1; dsimp only [mEvR12, mEvRawR12] at h1 ⊢;
    have h2 := t1Ev_cond_lt2 (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64)); omega
  have hc := allTree_zero t1b_cert_raw12_eff12 (mEv_r12_lt c); dsimp only at hc; rw [hMod] at hc
  rcases t1Ev_and4 hc with ⟨h1, h3, h6, h5⟩
  refine ⟨(b2_bEq_iff _ _).mp h1, (b2_bEq_iff _ _).mp h3, (b2_bEq_iff _ _).mp h6, fun hs5 ↦ ?_⟩
  change Bool.or (Bool.not ((mEvB12 c).testBit 5)) ((mEvRawB12 c).testBit 5) = true at h5
  rw [hs5, Bool.not_true, Bool.false_or] at h5; exact h5

def mr_ea_f12Cnt : ℕ → Bool
  | 0 => true
  | n + 1 =>
    let s := n + 1
    Nat.ble (cond (s.testBit 0) 1 0 + cond (s.testBit 1) 1 0 + cond (s.testBit 2) 1 0 +
      cond (s.testBit 3) 1 0 + cond (s.testBit 4) 1 0 + cond (s.testBit 5) 1 0 +
      cond (s.testBit 6) 1 0) 1
theorem mEv_cert_f12_excl :
    allTree 11 0 1024 (fun r ↦
      let s := specSymEff12 r
      let cnt :=
          cond (s.testBit 0) 1 0 + cond (s.testBit 1) 1 0 + cond (s.testBit 2) 1 0 +
          cond (s.testBit 3) 1 0 + cond (s.testBit 4) 1 0 + cond (s.testBit 5) 1 0 +
          cond (s.testBit 6) 1 0
      Nat.ble cnt 1) = true := by
  rw [show (fun r ↦
        let s := specSymEff12 r
        let cnt :=
            cond (s.testBit 0) 1 0 + cond (s.testBit 1) 1 0 + cond (s.testBit 2) 1 0 +
            cond (s.testBit 3) 1 0 + cond (s.testBit 4) 1 0 + cond (s.testBit 5) 1 0 +
            cond (s.testBit 6) 1 0
        Nat.ble cnt 1) = (fun r ↦ mr_ea_f12Cnt (specSymEff12 r)) from
      funext fun r ↦ by dsimp only [mr_ea_f12Cnt]; cases specSymEff12 r <;> rfl]
  decide +kernel

def mEvS13Full (h : ℕ) : ℕ := fastSpec13 ((h % 256) + 256 * fastSpec03x (Nat.xor h 96))
def mEvS13 (c : Fin (2 ^ 41)) : ℕ := mEvS13Full (t1EvHi10 c)

theorem mEv_cert_s13_in03 : allTree 11 0 1024 (fun h ↦ Nat.beq (fastSpec13_of_in03 (Nat.xor h 96))
    (mEvS13Full h)) = true := by decide +kernel
theorem mEv_wPack_out13 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut13 = mEvS13 c := by
  rw [wPack_t1aOut13 c, t1aEv_wPack_in03 c];
  exact Nat.eq_of_beq_eq_true (allTree_zero mEv_cert_s13_in03 (t1Ev_coin_bounds c).2.2.1)
theorem mEv_out13_bit (c : Fin (2 ^ 41)) (q : ℕ) (_hq : q < 11) : wBit (envTier1Sym96 c)
    (outW t1aOut13 q) = (mEvS13 c).testBit q := by rw [t1Ev_wBit_outW, mEv_wPack_out13 c]
def mEvKnP (c : Fin (2 ^ 41)) : Bool :=
    xor (xor ((mEvS13 c).testBit 1) ((mEvS13 c).testBit 2)) (xor ((mEvS13 c).testBit 3)
    ((mEvS13 c).testBit 4))
def mEvKnUbXor (c : Fin (2 ^ 41)) : Bool :=
    xor (xor ((mEvS13 c).testBit 1) ((mEvS13 c).testBit 2)) ((mEvS13 c).testBit 3)
def mEvPair14 (c : Fin (2 ^ 41)) : Bool :=
  let r5 := (t1EvPx c).2.1 + 4 * (t1EvB8 c % 64)
  let r6 := (t1aEvPy c).2.1 + 4 * (t1EvLo10 c % 64)
  xor ((t1EvLo10 c % 64).testBit 1)
    (xor ((fastSpec05x r5).testBit 0) ((t1bSpec08xOf r5 r6).testBit 1))

def mEvSolo14 (c : Fin (2 ^ 41)) : Bool :=
  let r5 := (t1EvPx c).2.1 + 4 * (t1EvB8 c % 64)
  let r6 := (t1aEvPy c).2.1 + 4 * (t1EvLo10 c % 64)
  xor ((t1EvLo8 c).testBit 4) ((t1bSpec08xOf r5 r6).testBit 0)

theorem mEv_coin5_lo2 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (coinW 5) = (t1EvLo10 c % 64).testBit 0 := by
  rw [mEv_wBit_coinW c (by omega)]
  dsimp only [t1EvLo10, t1EvY20]
  rw [← t1a_lo10_mod64 c.val, b2_testBit_mod_pow _ 6 0 (by decide), Nat.testBit_div_two_pow]

theorem mEv_coin6_lo2 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (coinW 6) = (t1EvLo10 c % 64).testBit 1 := by
  rw [mEv_wBit_coinW c (by omega)]
  dsimp only [t1EvLo10, t1EvY20]
  rw [← t1a_lo10_mod64 c.val, b2_testBit_mod_pow _ 6 1 (by decide), Nat.testBit_div_two_pow]

theorem mEv_coin29_lo8 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (coinW 29) = (t1EvLo8 c).testBit 4 := by
  rw [mEv_wBit_coinW c (by omega)]
  dsimp only [t1EvLo8, t1EvX16]
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, b2_testBit_mod_pow _ 8 4 (by decide),
      show (33554432 : ℕ) = 2 ^ 25 from rfl, Nat.testBit_div_two_pow]

def mEvR14 (c : Fin (2 ^ 41)) : ℕ :=
    cond ((mEvB12 c).testBit 6) 1 0 + 2 * (t1EvPx c).2.1 + 8 * cond (mEvKnP c) 1 0 + 16 *
    cond ((t1EvLo10 c % 64).testBit 0) 1 0 + 32 * cond (xor (mEvKnUbXor c)
    (lo2L2Mask64.testBit (t1EvLo10 c % 64))) 1 0 + 64 * cond (mEvPair14 c) 1 0 + 128 *
    cond (mEvSolo14 c) 1 0
def mEvS14 (c : Fin (2 ^ 41)) : ℕ := specT1b_14 (mEvR14 c)

theorem mEv_out14_exact (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut14 = mEvS14 c := by
  set e := envTier1Sym96 c
  have hh1 : (t1EvPx c).2.1 < 3 := (t1Ev_b2_props c).2.1
  have hb0 : wBit e (outW t1aOut12 6) = (mEvB12 c).testBit 6 := by
    rw [t1Ev_wBit_outW, mEv_wPack_rawOut12 c, (mEv_rawB12_bits c).2.2.1]
  have hb3 : wBit e wKnP13 = mEvKnP c := by
    rw [wKnP13, mEvKnP, t1Ev_wBit_xor, t1Ev_wBit_xor, t1Ev_wBit_xor, mEv_out13_bit c 1 (by omega),
        mEv_out13_bit c 2 (by omega), mEv_out13_bit c 3 (by omega), mEv_out13_bit c 4 (by omega)]
  have hb5 : wBit e (Nat.xor wKnUbXorKnP13 (outW t1bOut06x 0)) = xor (mEvKnUbXor c)
      (lo2L2Mask64.testBit (t1EvLo10 c % 64)) := by
    rw [wKnUbXorKnP13, mEvKnUbXor, t1Ev_wBit_xor, t1Ev_wBit_xor, t1Ev_wBit_xor,
        mEv_out13_bit c 1 (by omega), mEv_out13_bit c 2 (by omega), mEv_out13_bit c 3 (by omega),
        mEv_out06x_bit0 c]
  have hb6 : wBit e (Nat.xor (coinW 6) (Nat.xor (outW t1bOut05x 0) (outW t1bOut08x 1))) =
      mEvPair14 c := by
    dsimp only [mEvPair14];
    rw [t1Ev_wBit_xor, t1Ev_wBit_xor, mEv_coin6_lo2 c, t1Ev_wBit_outW, wPack_t1bOut05x c,
        t1b_wPack_in05 c, t1Ev_wBit_outW, t1b_wPack_out08x c]
  have hb7 : wBit e (Nat.xor (coinW 29) (outW t1bOut08x 0)) = mEvSolo14 c := by
    dsimp only [mEvSolo14];
    rw [t1Ev_wBit_xor, mEv_coin29_lo8 c, t1Ev_wBit_outW, t1b_wPack_out08x c]
  have hIn : wPack e t1aIn14 = mEvR14 c := by
    rw [show t1aIn14 = [outW t1aOut12 6] ++ (t1EvOutSlice tier1Out02 5 2 ++
          [wKnP13, coinW 5, Nat.xor wKnUbXorKnP13 (outW t1bOut06x 0), Nat.xor (coinW 6)
              (Nat.xor (outW t1bOut05x 0) (outW t1bOut08x 1)), Nat.xor (coinW 29)
              (outW t1bOut08x 0)])
          from listBeqNatT1_imp (by decide +kernel), t1Ev_wPack_append, t1Ev_wPack_append,
              List.length_cons, List.length_nil, t1Ev_len_outSlice, t1Ev_wPack_singleton,
              (mEv_out02_slices c).2.1]
    dsimp only [wPack, mEvR14]
    rw [hb0, hb3, mEv_coin5_lo2 c, hb5, hb6, hb7]
    cases (mEvB12 c).testBit 6 <;> cases mEvKnP c <;> cases (t1EvLo10 c % 64).testBit 0 <;>
      cases xor (mEvKnUbXor c) (lo2L2Mask64.testBit (t1EvLo10 c % 64)) <;> cases mEvPair14 c <;>
          cases mEvSolo14 c <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
  rw [wPack_t1aOut14 c, hIn]
  rfl

def mEvT1H0 (c : Fin (2 ^ 41)) : Bool :=
    xor ((mEvB12 c).testBit 6) (xor ((mEvS14 c).testBit 0) ((mEvS14 c).testBit 1))
theorem t1b_cert_spec14_props :
    allTree 9 0 256 (fun r ↦
      Bool.or (Bool.not (Nat.blt ((r / 2) % 4) 3))
        (let s := specT1b_14 r
         let t1 := bitAt r 0
         let h1 := (r / 2) % 4
         let knP := bitAt r 3
         let h0 := xor t1 (xor (s.testBit 0) (s.testBit 1))
         Bool.and (b2BEq h0 (Bool.and t1 (Nat.beq h1 0)))
           (Bool.and (b2BEq (s.testBit 0) (Bool.and t1 (Nat.beq h1 1)))
             (Bool.and (b2BEq (s.testBit 1) (Bool.and t1 (Nat.beq h1 2)))
               (Bool.and (Bool.not (Bool.and h0 (xor (s.testBit 0) (s.testBit 1))))
                 (Bool.or t1 (Bool.or knP (Nat.beq s 0)))))))) = true := by decide +kernel

theorem mEv_out14_props (c : Fin (2 ^ 41)) (q : ℕ) (_hq : q < 6) : wBit (envTier1Sym96 c)
    (outW t1aOut14 q) = (mEvS14 c).testBit q := by rw [t1Ev_wBit_outW, mEv_out14_exact c]
theorem mEv_s14_struct (c : Fin (2 ^ 41)) : mEvT1H0 c = Bool.and ((mEvB12 c).testBit 6)
    (Nat.beq (t1EvPx c).2.1 0) ∧ (mEvS14 c).testBit 0 = Bool.and ((mEvB12 c).testBit 6)
    (Nat.beq (t1EvPx c).2.1 1) ∧ (mEvS14 c).testBit 1 = Bool.and ((mEvB12 c).testBit 6)
    (Nat.beq (t1EvPx c).2.1 2) ∧ Bool.not (Bool.and (mEvT1H0 c) (xor ((mEvS14 c).testBit 0)
    ((mEvS14 c).testBit 1))) = true ∧ ((mEvB12 c).testBit 6 = false → mEvKnP c = false →
    mEvS14 c = 0) := by
  have hh1 : (t1EvPx c).2.1 < 3 := (t1Ev_b2_props c).2.1
  obtain ⟨_, _, _, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ :=
    ⟨t1Ev_cond_lt2 ((mEvB12 c).testBit 6), t1Ev_cond_lt2 (mEvKnP c),
     t1Ev_cond_lt2 ((t1EvLo10 c % 64).testBit 0),
     t1Ev_cond_lt2 (xor (mEvKnUbXor c) (lo2L2Mask64.testBit (t1EvLo10 c % 64))),
     t1Ev_cond_lt2 (mEvPair14 c), t1Ev_cond_lt2 (mEvSolo14 c)⟩
  have hb0 : bitAt (mEvR14 c) 0 = (mEvB12 c).testBit 6 := by
    rw [show mEvR14 c = cond ((mEvB12 c).testBit 6) 1 0 + 2 * (mEvR14 c / 2) by
          dsimp only [mEvR14]; omega, t1Ev_bitAt_zero]
  have hb3 : bitAt (mEvR14 c) 3 = mEvKnP c := by
    rw [bitAt_eq_testBit, show (3 : ℕ) = 0 + 3 from rfl, ← Nat.testBit_div_two_pow,
        show (2 : ℕ) ^ 3 = 8 from rfl,
        show mEvR14 c / 8 = cond (mEvKnP c) 1 0 + 2 * (mEvR14 c / 16) by
          dsimp only [mEvR14]; omega, ← bitAt_eq_testBit, t1Ev_bitAt_zero]
  have hc := allTree_zero t1b_cert_spec14_props
    (show mEvR14 c < 256 by dsimp only [mEvR14]; omega)
  rw [show (mEvR14 c / 2) % 4 = (t1EvPx c).2.1 by dsimp only [mEvR14]; omega,
      Nat.blt_eq.mpr hh1, Bool.not_true, Bool.false_or] at hc
  rcases (by simpa only [hb0, hb3, Bool.and_eq_true] using hc : _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨c1, c2, c3, c4, c5⟩
  exact ⟨(b2_bEq_iff _ _).mp c1, (b2_bEq_iff _ _).mp c2, (b2_bEq_iff _ _).mp c3, c4,
    fun ht hk ↦ Nat.beq_eq.mp (by simpa only [mEvS14, ht, hk, Bool.false_or] using c5)⟩
theorem t1a_blt_lin_c0 {B qL rL qR rR c0 : ℕ} (hrL : rL < B) (hrR : rR < B)
    (hc0 : c0 ≤ 1) : Bool.or (Nat.blt qL qR) (Bool.and (Nat.beq qL qR) (Nat.blt rL (rR + c0))) =
    Nat.blt (B * qL + rL) (B * qR + rR + c0) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  rcases lt_trichotomy qL qR with h | rfl | h
  · have h1 := Nat.mul_le_mul_left B (show qL + 1 ≤ qR from h)
    rw [Nat.mul_add, Nat.mul_one] at h1; omega
  · omega
  · have h1 := Nat.mul_le_mul_left B (show qR + 1 ≤ qL from h)
    rw [Nat.mul_add, Nat.mul_one] at h1; omega

theorem t1a_cstg (lhs rhs b k B K M : ℕ) (cin : Bool)
    (hB : 2 ^ b = B := by rfl) (hK : 2 ^ k = K := by rfl) (hM : K * K = M := by rfl) :
    let a := (lhs / B) % K
    let d := (rhs / B) % K
    let r := a + K * d + M * cond cin 1 0
    a + K * (d + K * cond cin 1 0) = r ∧ r % K = a ∧ (r / K) % K = d ∧ r / M = cond cin 1 0 ∧
    lhs % B < B ∧ rhs % B < B ∧ B * a + lhs % B = lhs % (B * K) ∧ B * d + rhs % B = rhs % (B * K)
        := by
  have pB : 0 < B := hB ▸ Nat.two_pow_pos b; have pK : 0 < K := hK ▸ Nat.two_pow_pos k
  have ha : (lhs / B) % K < K := Nat.mod_lt _ pK
  have hd : (rhs / B) % K < K := Nat.mod_lt _ pK
  have h1 : (lhs / B) % K + K * ((rhs / B) % K + K * cond cin 1 0) = (lhs / B) % K + K *
      ((rhs / B) % K) + M * cond cin 1 0 := by
    rw [Nat.mul_add K, ← Nat.mul_assoc K K, hM, ← Nat.add_assoc]
  refine ⟨h1, by rw [← h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha],
    by rw [← h1, Nat.add_mul_div_left _ _ pK, Nat.div_eq_of_lt ha, Nat.zero_add,
         Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd],
    by rw [← h1, ← hM, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ pK, Nat.div_eq_of_lt ha,
         Nat.zero_add, Nat.add_mul_div_left _ _ pK, Nat.div_eq_of_lt hd, Nat.zero_add],
    Nat.mod_lt lhs pB, Nat.mod_lt rhs pB, by rw [Nat.add_comm, ← Nat.mod_mul],
        by rw [Nat.add_comm, ← Nat.mod_mul]⟩

theorem t1a_v23_slice (c : Fin (2 ^ 41)) (sh k P6 B : ℕ)
    (hP6 : 2 ^ (6 + sh) = P6 := by rfl) (hB : 64 * B = P6 := by rfl) :
    wPack (envTier1Sym96 c) (t1EvOutSlice v23T1W (6 + sh) k) =
      ((t1aEvV17 c) / B) % 2 ^ k := by
  rw [t1Ev_wPack_outSlice, mEv_wPack_v23T1W c, hP6, ← hB, ← Nat.div_div_eq_div_mul,
      (t1aEv_v17_props c).1]

def mEvCmpRhsList : List ℕ := t1EvWireSlice cmpRhsBitT1aW 0 11

theorem t1b_w11_slice (c : Fin (2 ^ 41)) (sh k P6 B64 B : ℕ)
    (hP6 : 2 ^ (6 + (6 + sh)) = P6 := by rfl)
    (hB64 : 64 * B64 = P6 := by rfl)
    (hB : 64 * B = B64 := by rfl) :
    wPack (envTier1Sym96 c) (t1EvOutSlice v23T1W (12 + sh) k) =
      ((t1EvW11 c) / B) % 2 ^ k := by
  have hd : t1aEvV17 c / 64 = t1EvW11 c := by
    have := Nat.mod_lt (t1EvLo10 c) (by decide : 0 < 64)
    dsimp only [t1aEvV17]
    omega
  rw [show 12 + sh = 6 + (6 + sh) by omega, t1a_v23_slice c (6 + sh) k P6 B64 hP6 hB64, ← hB,
      ← Nat.div_div_eq_div_mul, hd]

theorem mEv_out18_bit (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (outW t1aOut18 0) = Nat.blt (t1EvW11 c) (wPack (envTier1Sym96 c) mEvCmpRhsList) := by
  set e := envTier1Sym96 c
  set lhs := t1EvW11 c
  set rhs := wPack e mEvCmpRhsList
  have hLhsLt : lhs < 2048 := (t1Ev_coin_bounds c).2.2.2.2.2.2.2.1
  have hRhsLt : rhs < 2048 := (wPack_lt_pow e mEvCmpRhsList).trans_eq
    (by rw [show mEvCmpRhsList.length = 11 from t1Ev_len_wireSlice _ 0 11]; rfl)
  have h16 : wBit e (outW t1aOut16 0) = Nat.blt (lhs % 32) (rhs % 32 + 0) := by
    have hIn : wPack e t1aIn16 = ((lhs / 1) % 32) + 32 * ((rhs / 1) % 32) := by
      rw [show t1aIn16 = t1EvOutSlice v23T1W (12 + 0) 5 ++
          t1EvOutSlice mEvCmpRhsList 0 5 from listBeqNatT1_imp (by decide +kernel),
          t1Ev_wPack_append, t1Ev_len_outSlice, t1b_w11_slice c 0 5 4096 64 1, t1Ev_wPack_outSlice,
              pow_zero, show (2 : ℕ) ^ 5 = 32 from rfl]
    rw [t1Ev_wBit_outW, wPack_t1aOut16 c, hIn, specT1b_16,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
        Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (Nat.mod_lt _ (by decide)),
            Nat.zero_add,
        Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), t1Ev_testBit0_single, Nat.div_one, Nat.div_one,
            Nat.add_zero]
  have h17 : wBit e (outW t1aOut17 0) = Nat.blt (lhs % 1024) (rhs % 1024 + 0) := by
    set cin := wBit e (outW t1aOut16 0)
    have hS := t1a_cstg lhs rhs 5 5 32 32 1024 cin
    have hIn : wPack e t1aIn17 = ((lhs / 32) % 32) + 32 * ((rhs / 32) % 32) + 1024 *
        cond cin 1 0 := by
      rw [show t1aIn17 = t1EvOutSlice v23T1W (12 + 5) 5 ++ (t1EvOutSlice mEvCmpRhsList 5 5 ++
          [outW t1aOut16 0]) from listBeqNatT1_imp (by decide +kernel),
          t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_len_outSlice, t1Ev_len_outSlice,
          t1b_w11_slice c 5 5 131072 2048 32, t1Ev_wPack_outSlice, t1Ev_wPack_singleton,
              show (2 : ℕ) ^ 5 = 32 from rfl]
      exact hS.1
    rw [t1Ev_wBit_outW, wPack_t1aOut17 c, hIn, specTier1_17, hS.2.1, hS.2.2.1,
        t1Ev_bitAt_div _ 10, show (2 : ℕ) ^ 10 = 1024 from rfl, hS.2.2.2.1,
        t1Ev_testBit0_single, t1Ev_testBit0_single, show cin = Nat.blt (lhs % 32)
            (rhs % 32 + 0) from h16,
        t1a_blt_lin_c0 (B := 32) hS.2.2.2.2.1 hS.2.2.2.2.2.1 (Nat.zero_le 1), hS.2.2.2.2.2.2.1,
            hS.2.2.2.2.2.2.2]
  set cin := wBit e (outW t1aOut17 0)
  have hS := t1a_cstg lhs rhs 10 1 1024 2 4 cin
  have hIn18 : wPack e t1aIn18 = ((lhs / 1024) % 2) + 2 * ((rhs / 1024) % 2) + 4 *
      cond cin 1 0 := by
    rw [show t1aIn18 = t1EvOutSlice v23T1W (12 + 10) 1 ++ (t1EvOutSlice mEvCmpRhsList 10 1 ++
        [outW t1aOut17 0]) from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_len_outSlice, t1Ev_len_outSlice,
        t1b_w11_slice c 10 1 4194304 65536 1024, t1Ev_wPack_outSlice, t1Ev_wPack_singleton,
        show (2 : ℕ) ^ 10 = 1024 from rfl, show (2 : ℕ) ^ 1 = 2 from rfl]
    exact hS.1
  have hSpec18 (ql qr : ℕ) (b : Bool) (hql : ql < 2) (hqr : qr < 2) :
      (specT1b_18 (ql + 2 * qr + 4 * cond b 1 0)).testBit 0 = Bool.or (Nat.blt ql qr)
          (Bool.and (Nat.beq ql qr) b) := by
    rcases (show ql = 0 ∨ ql = 1 by omega) with rfl | rfl <;>
      rcases (show qr = 0 ∨ qr = 1 by omega) with rfl | rfl <;> cases b <;> rfl
  rw [t1Ev_wBit_outW, wPack_t1aOut18 c, hIn18,
      hSpec18 _ _ cin (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
      show cin = Nat.blt (lhs % 1024) (rhs % 1024 + 0) from h17,
      t1a_blt_lin_c0 (B := 1024) hS.2.2.2.2.1 hS.2.2.2.2.2.1 (Nat.zero_le 1),
      hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2, show 1024 * 2 = 2048 from rfl,
      Nat.mod_eq_of_lt hLhsLt, Nat.mod_eq_of_lt hRhsLt, Nat.add_zero]

def mEvRhsSigs : List ℕ :=
    [outW t1aOut12 1, outW t1aOut12 3, outW t1aOut12 5, outW t1aOut12 6, outW t1aOut14 0,
    outW t1aOut14 1, outW t1aOut14 2, outW t1aOut14 3, outW t1aOut14 4, outW t1aOut14 5,
    outW t1aOut13 1, outW t1aOut13 2, outW t1aOut13 3, outW t1aOut13 4]
def mEvCmpRhsValLo (m : ℕ) : ℕ :=
  let v1 := mEvXorConst (m.testBit 0) 1452 0
  let v2 := mEvXorConst (m.testBit 1) 1750 v1
  let v3 := mEvXorConst (m.testBit 2) 401 v2
  let v4 := mEvXorConst (m.testBit 3) 148 v3
  let v5 := mEvXorConst (m.testBit 4) 1422 v4
  let v6 := mEvXorConst (m.testBit 5) 1896 v5
  mEvXorConst (m.testBit 6) 128 v6

def mEvCmpRhsVal (m : ℕ) : ℕ :=
  let v7 := mEvXorConst (m.testBit 7) 169 (mEvCmpRhsValLo m)
  let v8 := mEvXorConst (m.testBit 8) 642 v7
  let v9 := mEvXorConst (m.testBit 9) 1 v8
  let v10 := mEvXorConst (m.testBit 10) 306 v9
  let vy1 := mEvXorConst (m.testBit 11) 487 v10
  let vy2 := mEvXorConst (m.testBit 12) 400 vy1
  mEvXorConst (m.testBit 13) 305 vy2

theorem pkBitxc {b : Bool} {v a : ℕ} (hv : Nat.blt v 2048 = true)
    (ha : a < 2048) : mEvXorConst b v a < 2048 := by
  cases b
  · exact ha
  · dsimp only [mEvXorConst, cond]
    rw [nat_xor_eq]
    exact Nat.xor_lt_two_pow (n := 11) ha (Nat.blt_eq.mp hv)

theorem pkBitlt (m : ℕ) : mEvCmpRhsVal m < 2048 := by
  unfold mEvCmpRhsVal mEvCmpRhsValLo
  exact pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl
    (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl (pkBitxc rfl
        (Nat.blt_eq.mp rfl))))))))))))))

theorem mEv_wBit_cmpRhsBitT1W (e i : ℕ) : wBit e (cmpRhsBitT1aW i) =
    (mEvCmpRhsVal (wPack e mEvRhsSigs)).testBit i := by
  unfold cmpRhsBitT1aW cmpRhsBitT1aLo mEvCmpRhsVal mEvCmpRhsValLo
  dsimp only
  repeat rw [mEv_wBit_xorMaskedConst]
  repeat rw [mEv_testBit_xorConst]
  rw [wBit_zero, Nat.zero_testBit]
  repeat rw [← t1Ev_wBit_outW]
  rfl

theorem mEv_wPack_cmpRhsList (e : ℕ) : wPack e mEvCmpRhsList = mEvCmpRhsVal (wPack e mEvRhsSigs)
    := by
  rw [mEvCmpRhsList, t1Ev_wPack_wireSlice e cmpRhsBitT1aW _ 0 11 (fun i _ ↦
      mEv_wBit_cmpRhsBitT1W e (0 + i)),
      pow_zero, Nat.div_one, show 2 ^ 11 = 2048 from rfl, Nat.mod_eq_of_lt (pkBitlt _)]

def mEvRhsMask (c : Fin (2 ^ 41)) : ℕ :=
    cond ((mEvRawB12 c).testBit 1) 1 0 + 2 * cond ((mEvRawB12 c).testBit 3) 1 0 + 4 *
    cond ((mEvRawB12 c).testBit 5) 1 0 + 8 * cond ((mEvRawB12 c).testBit 6) 1 0 + 16 *
    cond ((mEvS14 c).testBit 0) 1 0 + 32 * cond ((mEvS14 c).testBit 1) 1 0 + 64 *
    cond ((mEvS14 c).testBit 2) 1 0 + 128 * cond ((mEvS14 c).testBit 3) 1 0 + 256 *
    cond ((mEvS14 c).testBit 4) 1 0 + 512 * cond ((mEvS14 c).testBit 5) 1 0 + 1024 *
    cond ((mEvS13 c).testBit 1) 1 0 + 2048 * cond ((mEvS13 c).testBit 2) 1 0 + 4096 *
    cond ((mEvS13 c).testBit 3) 1 0 + 8192 * cond ((mEvS13 c).testBit 4) 1 0
def mEvLt11 (c : Fin (2 ^ 41)) : Bool := Nat.blt (t1EvW11 c) (mEvCmpRhsVal (mEvRhsMask c))
theorem mEv_wBit_out18 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (outW t1aOut18 0) = mEvLt11 c := by
  have hMask : wPack (envTier1Sym96 c) mEvRhsSigs = mEvRhsMask c := by
    dsimp only [mEvRhsSigs, wPack]
    rw [mEv_out14_props c 0 (by omega), mEv_out14_props c 1 (by omega),
        mEv_out14_props c 2 (by omega), mEv_out14_props c 3 (by omega),
        mEv_out14_props c 4 (by omega), mEv_out14_props c 5 (by omega),
        mEv_out13_bit c 1 (by omega), mEv_out13_bit c 2 (by omega),
        mEv_out13_bit c 3 (by omega), mEv_out13_bit c 4 (by omega),
        t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW,
        mEv_wPack_rawOut12 c]
    dsimp only [mEvRhsMask, cond]; omega
  rw [mEv_out18_bit c, mEv_wPack_cmpRhsList, hMask]; rfl

def mEvDoEe (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1) (Bool.not (Nat.beq (t1aEvU1 c)
    (t1aEvZ2 c)))) (Bool.or ((mEvB12 c).testBit 0) (Bool.and ((mEvB12 c).testBit 1) (mEvLt11 c)))
def mEvDoNn (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1)
    (Bool.not (Nat.beq (t1EvD1 c).2.val (t1aEvD2 c).2.val))) (Bool.or ((mEvB12 c).testBit 2)
    (Bool.and ((mEvB12 c).testBit 3) (mEvLt11 c)))
def mEvDoEn (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (t1EvD1 c).1 (Bool.or ((mEvB12 c).testBit 4) (Bool.and ((mEvB12 c).testBit 5)
    (mEvLt11 c)))
def mEvIsPot (c : Fin (2 ^ 41)) : Bool := xor (xor (mEvDoEe c) (mEvDoNn c)) (mEvDoEn c)
def mEvDoKel (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (t1aEvInBox c) (Bool.and (Bool.not (mEvIsPot c)) (Bool.not (Bool.and (mEvT1H0 c)
    (mEvLt11 c))))
def mEvAxEl (c : Fin (2 ^ 41)) : ℕ :=
    cond (mEvDoKel c) (cond (Bool.and (xor ((mEvS14 c).testBit 0) ((mEvS14 c).testBit 1))
    (mEvLt11 c)) 0 (t1EvPx c).2.1) 0
def mEvDoKn (c : Fin (2 ^ 41)) : Bool :=
    Bool.and (t1EvKnOk c) (Bool.or ((mEvS13 c).testBit 0) (Bool.and (mEvKnP c) (mEvLt11 c)))
def mEvN1K (c : Fin (2 ^ 41)) : ℕ := cond (mEvDoKn c) (mEvS13 c / 32) 0
def mEvAxK (c : Fin (2 ^ 41)) : ℕ := cond (mEvDoKn c) (t1EvHi10 c / 256) 0
theorem mEv_b12_of_not_inTile (c : Fin (2 ^ 41)) (hF : t1aEvInTile c = false) : mEvRawB12 c = 0 ∧
    mEvB12 c = 0 := by
  have hb0Raw : bitAt (mEvRawR12 c) 0 = false := by
    have hEq : mEvRawR12 c = cond false 1 0 + 2 * ((t1EvPx c).2.2.1 + 8 * (t1aEvPy c).2.2.1) := by
      dsimp only [mEvRawR12]; rw [hF]; omega
    rw [hEq, t1Ev_bitAt_zero]
  have hRaw : mEvRawB12 c = 0 := by dsimp only [mEvRawB12, specSym_12]; rw [hb0Raw]; rfl
  refine ⟨hRaw, specSymEff12_of_bit0_false ?_⟩
  have hEq : mEvR12 c = cond false 1 0 + 2 * ((t1EvPx c).2.2.1 + 8 * (t1aEvPy c).2.2.1 + 256 *
      cond (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64)) 1 0)
      := by dsimp only [mEvR12, mEvRawR12]; rw [hF]; omega
  rw [hEq, t1Ev_bitAt_zero]

theorem mEv_cert_kinS13 :
    allTree 11 0 1024 (fun h ↦
      let code := mEvS13Full h
      let cnt :=
          cond (code.testBit 0) 1 0 + cond (code.testBit 1) 1 0 + cond (code.testBit 2) 1 0 +
          cond (code.testBit 3) 1 0 + cond (code.testBit 4) 1 0
      let knP := xor (xor (code.testBit 1) (code.testBit 2)) (xor (code.testBit 3) (code.testBit 4))
      Bool.and (Nat.blt code 2048)
        (Bool.and (Nat.blt (code / 32) 64)
          (Bool.and (Nat.ble cnt 1)
            (Bool.not (Bool.and (code.testBit 0) knP))))) = true := by decide +kernel

private theorem cond_gate_or_le (g b0 b1 l : Bool) :
    cond (Bool.and g (Bool.or b0 (Bool.and b1 l))) 1 0 ≤ cond b0 1 0 + cond b1 1 0 := by
  cases g <;> cases b0 <;> cases b1 <;> cases l <;> decide

private theorem two_hot_false {a b : Bool} : a = true → cond a 1 0 + cond b 1 0 ≤ 1 → b =
    false := by
  cases a <;> cases b <;> decide

theorem mEv_excl_sum (c : Fin (2 ^ 41)) :
    cond (mEvDoEe c) 1 0 + cond (mEvDoNn c) 1 0 + cond (mEvDoEn c) 1 0 +
        cond ((mEvB12 c).testBit 6) 1 0 ≤ 1 := by
  have hEx := Nat.ble_eq.mp (allTree_zero mEv_cert_f12_excl (mEv_r12_lt c))
  change cond ((mEvB12 c).testBit 0) 1 0 + cond ((mEvB12 c).testBit 1) 1 0 +
    cond ((mEvB12 c).testBit 2) 1 0 + cond ((mEvB12 c).testBit 3) 1 0 +
    cond ((mEvB12 c).testBit 4) 1 0 + cond ((mEvB12 c).testBit 5) 1 0 +
    cond ((mEvB12 c).testBit 6) 1 0 ≤ 1 at hEx
  have hEe :=
      cond_gate_or_le (Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1) (Bool.not (Nat.beq (t1aEvU1 c)
      (t1aEvZ2 c)))) ((mEvB12 c).testBit 0) ((mEvB12 c).testBit 1) (mEvLt11 c)
  have hNn :=
      cond_gate_or_le (Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1)
      (Bool.not (Nat.beq (t1EvD1 c).2.val (t1aEvD2 c).2.val))) ((mEvB12 c).testBit 2)
      ((mEvB12 c).testBit 3) (mEvLt11 c)
  have hEn :=
      cond_gate_or_le (t1EvD1 c).1 ((mEvB12 c).testBit 4) ((mEvB12 c).testBit 5) (mEvLt11 c)
  dsimp only [mEvDoEe, mEvDoNn, mEvDoEn]
  omega

theorem mEv_pot_props (c : Fin (2 ^ 41)) :
    (mEvIsPot c = true → t1aEvInBox c = true ∧ (t1EvD1 c).1 = true) ∧
    (mEvDoEe c = true → (t1EvD1 c).1 = true ∧ (t1aEvD2 c).1 = true ∧ t1aEvU1 c ≠ t1aEvZ2 c ∧
        mEvIsPot c = true ∧ mEvDoKel c = false) ∧
    (mEvDoNn c = true → (t1EvD1 c).1 = true ∧ (t1aEvD2 c).1 = true ∧ (t1EvD1 c).2.val ≠
        (t1aEvD2 c).2.val ∧ mEvIsPot c = true) := by
  have hSum := mEv_excl_sum c
  refine ⟨fun hP ↦ ?_, fun hE ↦ ?_, fun hN ↦ ?_⟩
  · refine ⟨?_, ?_⟩
    · cases hT : t1aEvInTile c
      · have hs0 := (mEv_b12_of_not_inTile c hT).2
        simp [mEvIsPot, mEvDoEe, mEvDoNn, mEvDoEn, hs0, xor] at hP
      · exact (mEv_inTile_imp c hT).2.2.2.1
    · cases hd : (t1EvD1 c).1
      · simp [mEvIsPot, mEvDoEe, mEvDoNn, mEvDoEn, hd, xor] at hP
      · rfl
  · have hn : mEvDoNn c = false := two_hot_false hE (by omega)
    have hen : mEvDoEn c = false := two_hot_false hE (by omega)
    have hP : mEvIsPot c = true := by dsimp only [mEvIsPot]; rw [hE, hn, hen]; rfl
    rcases Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hE).1 with ⟨hd12, hNeB⟩
    rcases Bool.and_eq_true_iff.mp hd12 with ⟨hd1, hd2⟩
    refine ⟨hd1, hd2, fun hEq ↦ Bool.noConfusion (Nat.beq_eq.mpr hEq ▸ hNeB), hP, ?_⟩
    dsimp only [mEvDoKel]
    rw [hP, Bool.not_true, Bool.false_and, Bool.and_false]
  · have he : mEvDoEe c = false := two_hot_false hN (by omega)
    have hen : mEvDoEn c = false := two_hot_false hN (by omega)
    have hP : mEvIsPot c = true := by dsimp only [mEvIsPot]; rw [he, hN, hen]; rfl
    rcases Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hN).1 with ⟨hd12, hNeB⟩
    rcases Bool.and_eq_true_iff.mp hd12 with ⟨hd1, hd2⟩
    exact ⟨hd1, hd2, fun hEq ↦ Bool.noConfusion (Nat.beq_eq.mpr hEq ▸ hNeB), hP⟩

theorem mEv_care_and_out20 (c : Fin (2 ^ 41)) : careTier1_20 (wPack (envTier1Sym96 c) t1aIn20) =
    true ∧ wPack (envTier1Sym96 c) t1aOut20 = cond (mEvDoEe c) 1 0 + cond (mEvDoNn c) 2 0 +
    cond (mEvDoEn c) 4 0 := by
  have hbi (i : ℕ) (hi : i < 6) :
      bitAt (wPack (envTier1Sym96 c) t1aIn20) i = (mEvB12 c).testBit i := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [mEv_bitAt_wPack]
      dsimp only [t1aIn20, mEvNth]
      rw [t1Ev_wBit_outW, mEv_wPack_out12 c]
      rfl
  have hb6 : bitAt (wPack (envTier1Sym96 c) t1aIn20) 6 = mEvLt11 c := by
    rw [mEv_bitAt_wPack]; dsimp only [t1aIn20, mEvNth]; exact mEv_wBit_out18 c
  have hb7 : bitAt (wPack (envTier1Sym96 c) t1aIn20) 7 = (t1EvD1 c).1 := by
    rw [mEv_bitAt_wPack]; dsimp only [t1aIn20, mEvNth]; exact (mEv_out05_06_bits c).1
  have hb8 : bitAt (wPack (envTier1Sym96 c) t1aIn20) 8 = (t1aEvD2 c).1 := by
    rw [mEv_bitAt_wPack]; dsimp only [t1aIn20, mEvNth]; exact (mEv_out05_06_bits c).2.1
  have hCare : careTier1_20 (wPack (envTier1Sym96 c) t1aIn20) = true := by
    unfold careTier1_20; dsimp only
    rw [hbi 0 (by decide), hbi 1 (by decide), hbi 2 (by decide), hbi 3 (by decide),
        hbi 4 (by decide),
        hbi 5 (by decide)]; have hEx :=
                              Nat.ble_eq.mp (allTree_zero mEv_cert_f12_excl (mEv_r12_lt c));
                              change cond ((mEvB12 c).testBit 0) 1 0 +
                              cond ((mEvB12 c).testBit 1) 1 0 + cond ((mEvB12 c).testBit 2) 1 0 +
                              cond ((mEvB12 c).testBit 3) 1 0 + cond ((mEvB12 c).testBit 4) 1 0 +
                              cond ((mEvB12 c).testBit 5) 1 0 + cond ((mEvB12 c).testBit 6) 1 0 ≤
                              1 at hEx
    exact Nat.ble_eq.mpr (by omega)
  refine ⟨hCare, ?_⟩; rw [wPack_t1aOut20 c hCare]
  unfold specTier1_20; dsimp only
  rw [hbi 0 (by decide), hbi 1 (by decide), hbi 2 (by decide), hbi 3 (by decide), hbi 4 (by decide),
      hbi 5 (by decide), hb6, hb7, hb8]
  have hEeEq : Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1)
      (Bool.not (bitAt (wPack (envTier1Sym96 c) t1aIn20) 9)) =
      Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1) (Bool.not (Nat.beq (t1aEvU1 c) (t1aEvZ2 c)))
      := by
    cases hd2 : (t1aEvD2 c).1
    · rw [Bool.and_false, Bool.false_and, Bool.false_and]
    · rw [mEv_bitAt_wPack]; dsimp only [t1aIn20, mEvNth]
      rw [(mEv_out10_bits c hd2).1]
  have hNnEq : Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1)
      (Bool.not (bitAt (wPack (envTier1Sym96 c) t1aIn20) 10)) =
      Bool.and (Bool.and (t1EvD1 c).1 (t1aEvD2 c).1)
      (Bool.not (Nat.beq (t1EvD1 c).2.val (t1aEvD2 c).2.val)) := by
    cases hd1 : (t1EvD1 c).1
    · rw [Bool.false_and, Bool.false_and, Bool.false_and]
    · cases hd2 : (t1aEvD2 c).1
      · rw [Bool.and_false, Bool.false_and, Bool.false_and]
      · rw [mEv_bitAt_wPack]; dsimp only [t1aIn20, mEvNth]
        rw [(mEv_out08_bits c hd1 hd2).1]
  rw [hEeEq, hNnEq]; rfl

theorem mEv_care_in20 (c : Fin (2 ^ 41)) : careTier1_20 (wPack (envTier1Sym96 c) t1aIn20) =
    true := (mEv_care_and_out20 c).1
theorem mEv_wPack_out20 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut20 =
    cond (mEvDoEe c) 1 0 + cond (mEvDoNn c) 2 0 + cond (mEvDoEn c) 4 0 :=
    (mEv_care_and_out20 c).2
theorem mEv_out20_bits_w5 (c : Fin (2 ^ 41)) :
    wBit (envTier1Sym96 c) (outW t1aOut20 0) = mEvDoEe c ∧
    wBit (envTier1Sym96 c) (outW t1aOut20 1) = mEvDoNn c ∧
    wBit (envTier1Sym96 c)
      (Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2)) =
      mEvIsPot c := by
  obtain ⟨b0, b1, b2⟩ := mEv_three_bits (mEv_wPack_out20 c)
  refine ⟨(t1Ev_wBit_outW _ _ _).trans b0, (t1Ev_wBit_outW _ _ _).trans b1, ?_⟩
  rw [t1Ev_wBit_xor, t1Ev_wBit_xor, t1Ev_wBit_outW, t1Ev_wBit_outW, t1Ev_wBit_outW, b0, b1, b2]
  rfl
theorem t1aEv_cert_b2_isX_h1 :
    allTree 9 0 256 (fun a8 ↦
      let p := b2Spec a8
      Bool.or (Bool.not p.2.2.2) (Nat.beq p.2.1 0)) = true := by decide +kernel

def t1aUsesLt (s12 : ℕ) : Bool :=
    Bool.or (s12.testBit 1) (Bool.or (s12.testBit 3) (Bool.or (s12.testBit 5) (s12.testBit 6)))
theorem t1aEv_cert_b12_uses_lt :
    allTree 11 0 1024 (fun r ↦
      let s := specSymEff12 r
      let q31 := (r / 16) % 32
      Bool.and
        (Bool.or (Bool.not (t1aUsesLt s))
          (Bool.or (Nat.beq q31 25) (Bool.or (Nat.beq q31 26) (Nat.beq q31 27))))
        (Bool.or (Bool.not (s.testBit 6)) (Nat.beq q31 27))) = true := by decide +kernel

theorem t1aEv_cert_hi10_invs :
    allTree 11 0 1024 (fun h ↦
      let py := b6Spec (Nat.xor h 96)
      let cd := mEvS13Full h
      let q31 := py.2.2.1
      Bool.and
        (Bool.or py.2.2.2
          (Bool.or (Bool.not (Bool.or (Nat.beq q31 25) (Bool.or (Nat.beq q31 26) (Nat.beq q31 27))))
            (Bool.and (Bool.not (cd.testBit 1))
              (Bool.and (Bool.not (cd.testBit 2))
                (Bool.and (Bool.not (cd.testBit 3)) (Bool.not (cd.testBit 4)))))))
        (Bool.and
          (Bool.or py.2.2.2 (Bool.or (Bool.not (Nat.beq q31 27)) (cd.testBit 0)))
          (Bool.and
            (Bool.or (Bool.not py.2.2.2) (cd.testBit 0))
            (Bool.or (Bool.not (Nat.blt h 768)) (Bool.not py.2.2.2))))) = true := by decide +kernel

theorem t1a_knP_false_imp_bits {cd : ℕ} (_hLt : cd < 256 ∨ True)
    (hCnt : cond (cd.testBit 0) 1 0 + cond (cd.testBit 1) 1 0 + cond (cd.testBit 2) 1 0 +
    cond (cd.testBit 3) 1 0 + cond (cd.testBit 4) 1 0 ≤ 1)
    (hP : xor (xor (cd.testBit 1) (cd.testBit 2)) (xor (cd.testBit 3) (cd.testBit 4)) = false) :
    cd.testBit 1 = false ∧ cd.testBit 2 = false ∧ cd.testBit 3 = false ∧ cd.testBit 4 = false := by
  cases b0 : cd.testBit 0 <;> cases b1 : cd.testBit 1 <;> cases b2 : cd.testBit 2 <;>
    cases b3 : cd.testBit 3 <;> cases b4 : cd.testBit 4 <;>
    rw [b0, b1, b2, b3, b4] at hCnt <;> rw [b1, b2, b3, b4] at hP <;>
    first | exact ⟨rfl, rfl, rfl, rfl⟩ | exact absurd hP (by decide) | exact absurd hCnt (by decide)

theorem mEv_care_and_out21 (c : Fin (2 ^ 41)) : careT1a_21 (wPack (envTier1Sym96 c) t1aIn21) =
    true ∧ wPack (envTier1Sym96 c) t1aOut21 = cond (mEvDoKel c) 1 0 + cond (mEvDoKn c) 2 0 +
    4 * mEvAxEl c := by
  set r := wPack (envTier1Sym96 c) t1aIn21
  have h14S := mEv_s14_struct c
  have hb0 : bitAt r 0 = (t1EvPx c).2.2.2 :=
    (mEv_bitAt_wPack _ t1aIn21 0).trans (mEv_out02_slices c).2.2.2
  have hb1 : bitAt r 1 = (t1aEvPy c).2.2.2 :=
    (mEv_bitAt_wPack _ t1aIn21 1).trans (mEv_out03_slices c).2.2.2.1
  have hb2 : bitAt r 2 = mEvIsPot c :=
    (mEv_bitAt_wPack _ t1aIn21 2).trans (mEv_out20_bits_w5 c).2.2
  have hb3 : bitAt r 3 = mEvT1H0 c := by
    rw [mEv_bitAt_wPack]
    dsimp only [t1aIn21, mEvNth, mEvT1H0]
    rw [t1Ev_wBit_xor, t1Ev_wBit_xor, t1Ev_wBit_outW, mEv_wPack_rawOut12 c,
        (mEv_rawB12_bits c).2.2.1, mEv_out14_props c 0 (by omega),
        mEv_out14_props c 1 (by omega)]
  have hb4 : bitAt r 4 = xor ((mEvS14 c).testBit 0) ((mEvS14 c).testBit 1) := by
    rw [mEv_bitAt_wPack]
    dsimp only [t1aIn21, mEvNth]
    rw [t1Ev_wBit_xor, mEv_out14_props c 0 (by omega), mEv_out14_props c 1 (by omega)]
  have hb5 : bitAt r 5 = mEvLt11 c :=
    (mEv_bitAt_wPack _ t1aIn21 5).trans (mEv_wBit_out18 c)
  have hh1 : (r / 64) % 4 = (t1EvPx c).2.1 := by
    rw [mEv_in_field_eq 64 4 6 2 t1aIn21 (t1EvOutSlice tier1Out02 5 2)
          rfl rfl (by decide +kernel), (mEv_out02_slices c).2.1]
  have hb8 : bitAt r 8 = t1EvKnOk c :=
    (mEv_bitAt_wPack _ t1aIn21 8).trans (mEv_out11_bits c).2
  have hb9 : bitAt r 9 = (mEvS13 c).testBit 0 :=
    (mEv_bitAt_wPack _ t1aIn21 9).trans (mEv_out13_bit c 0 (by omega))
  have hb10 : bitAt r 10 = mEvKnP c := by
    rw [mEv_bitAt_wPack]; dsimp only [t1aIn21, mEvNth]
    rw [t1Ev_wBit_xor, t1Ev_wBit_xor, t1Ev_wBit_xor,
        mEv_out13_bit c 1 (by omega), mEv_out13_bit c 2 (by omega),
        mEv_out13_bit c 3 (by omega), mEv_out13_bit c 4 (by omega)]; rfl
  have hInv := allTree_zero t1aEv_cert_hi10_invs (t1Ev_coin_bounds c).2.2.1
  rcases t1Ev_and4 hInv with ⟨_, hQ27KnF, hIsYKnF, h768NotY⟩
  have hT1Imp : (mEvB12 c).testBit 6 = true → t1aEvInBox c = true ∧ mEvIsPot c = false ∧
      (mEvS13 c).testBit 0 = true := by
    intro hT1
    have hTile : t1aEvInTile c = true := by
      cases ht : t1aEvInTile c
      · rw [(mEv_b12_of_not_inTile c ht).2, Nat.zero_testBit] at hT1; cases hT1
      · rfl
    rcases mEv_inTile_imp c hTile with ⟨_, _, hYF, hBox, _⟩
    have hSum := mEv_excl_sum c
    have hPF : mEvIsPot c = false := by
      have he : mEvDoEe c = false := two_hot_false hT1 (by omega)
      have hn : mEvDoNn c = false := two_hot_false hT1 (by omega)
      have hen : mEvDoEn c = false := two_hot_false hT1 (by omega)
      dsimp only [mEvIsPot]; rw [he, hn, hen]; rfl
    have hA :=
        mr_e2_r12 (t1aEvInTile c) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))
        (t1Ev_b2_props c).2.2.1 (t1aEv_b6_props c).2.2.1; have hB12U :=
                                                            (Bool.and_eq_true_iff.mp (allTree_zero
                                                            t1aEv_cert_b12_uses_lt hA.2.1)).2;
                                                            change Bool.or
                                                            (Bool.not ((mEvB12 c).testBit 6))
                                                            (Nat.beq ((mEvR12 c / 16) % 32) 27) =
                                                            true at hB12U; dsimp only [mEvR12,
                                                            mEvRawR12] at hB12U; rw [hT1,
                                                            Bool.not_true, Bool.false_or,
                                                            hA.2.2.2.2.2.2.2.2.2] at hB12U; change
                                                            Bool.or (t1aEvPy c).2.2.2
                                                            (Bool.or
                                                            (Bool.not (Nat.beq (t1aEvPy c).2.2.1
                                                            27)) ((mEvS13 c).testBit 0)) =
                                                            true at hQ27KnF; rw [hYF, Bool.false_or,
                                                            hB12U, Bool.not_true,
                                                            Bool.false_or] at hQ27KnF; exact ⟨hBox,
                                                            hPF, hQ27KnF⟩
  have hCare : careT1a_21 r = true := by
    unfold careT1a_21 careT1a_21Lo; dsimp only
    rw [hb0, hb1, hb2, hb3, hb4, hb5, hh1, hb8, hb9, hb10];
    change Bool.and (Bool.and (Nat.blt (t1EvPx c).2.1 3)
        (Bool.and (Bool.or (Bool.not (t1EvPx c).2.2.2) (Nat.beq (t1EvPx c).2.1 0))
        (Bool.and (Bool.or (Bool.not (mEvIsPot c)) (t1aEvInBox c))
        (Bool.and (Bool.or (Bool.not (mEvT1H0 c)) (Bool.and (Bool.and (t1aEvInBox c)
        (Bool.not (mEvIsPot c))) (Bool.and (Nat.beq (t1EvPx c).2.1 0) ((mEvS13 c).testBit 0))))
        (Bool.or (Bool.not (xor ((mEvS14 c).testBit 0) ((mEvS14 c).testBit 1)))
        (Bool.and (Bool.and (t1aEvInBox c) (Bool.not (mEvIsPot c)))
        (Bool.and (Bool.or (Nat.beq (t1EvPx c).2.1 1) (Nat.beq (t1EvPx c).2.1 2))
        ((mEvS13 c).testBit 0)))))))) (Bool.and (Bool.or (Bool.not (t1aEvPy c).2.2.2)
        ((mEvS13 c).testBit 0)) (Bool.and (Bool.or (Bool.not (t1EvKnOk c))
        (Bool.and (t1EvPx c).2.2.2 (Bool.not (t1aEvPy c).2.2.2)))
        (Bool.and (Bool.not (Bool.and ((mEvS13 c).testBit 0) (mEvKnP c))) (Bool.or (t1aEvInBox c)
        (Bool.or (Bool.not (mEvLt11 c)) (mEvKnP c)))))) =
        true; have c1 : Nat.blt (t1EvPx c).2.1 3 = true :=
                Nat.blt_eq.mpr (t1Ev_b2_props c).2.1; have c2 : Bool.or (Bool.not (t1EvPx c).2.2.2)
                                                        (Nat.beq (t1EvPx c).2.1 0) = true :=
                                                        allTree_zero t1aEv_cert_b2_isX_h1
                                                        (t1Ev_coin_bounds c).2.2.2.2.2.1
    obtain ⟨_, _, hCnt, c8⟩ :=
      t1Ev_and4 (allTree_zero mEv_cert_kinS13 (t1Ev_coin_bounds c).2.2.1)
    change Bool.or (Bool.not (t1aEvPy c).2.2.2) ((mEvS13 c).testBit 0) = true at hIsYKnF
    change Bool.not (Bool.and ((mEvS13 c).testBit 0) (mEvKnP c)) = true at c8
    rw [c1, c2, hIsYKnF, c8]
    simp only [Bool.true_and]
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · cases hp : mEvIsPot c
      · rfl
      · rw [((mEv_pot_props c).1 hp).1, Bool.or_true]
    · cases hs0 : mEvT1H0 c
      · rfl
      · obtain ⟨hT1, hh10⟩ := Bool.and_eq_true_iff.mp (h14S.1.symm.trans hs0)
        obtain ⟨hB, hPF, hKF⟩ := hT1Imp hT1
        rw [hB, hPF, hh10, hKF]
        rfl
    · cases hs12 : xor ((mEvS14 c).testBit 0) ((mEvS14 c).testBit 1)
      · rfl
      · rw [h14S.2.1, h14S.2.2.1] at hs12
        have hSplit : Bool.and ((mEvB12 c).testBit 6)
            (Bool.or (Nat.beq (t1EvPx c).2.1 1) (Nat.beq (t1EvPx c).2.1 2)) = true := by
          revert hs12
          cases (mEvB12 c).testBit 6 <;> cases Nat.beq (t1EvPx c).2.1 1 <;>
            cases Nat.beq (t1EvPx c).2.1 2 <;> decide
        obtain ⟨hT1, hh12⟩ := Bool.and_eq_true_iff.mp hSplit
        obtain ⟨hB, hPF, hKF⟩ := hT1Imp hT1
        rw [hB, hPF, hh12, hKF]
        rfl
    · cases hk : t1EvKnOk c
      · rfl
      · obtain ⟨hX, h768⟩ := Bool.and_eq_true_iff.mp hk
        change Bool.or (Bool.not (Nat.blt (t1EvHi10 c) 768))
          (Bool.not (t1aEvPy c).2.2.2) = true at h768NotY
        rw [h768, Bool.not_true, Bool.false_or] at h768NotY
        rw [hX, h768NotY]
        rfl
    · cases hB : t1aEvInBox c
      · cases hKP : mEvKnP c
        · have hTF : t1aEvInTile c = false := Bool.eq_false_iff.mpr fun ht ↦
            Bool.noConfusion (hB.symm.trans (mEv_inTile_imp c ht).2.2.2.1)
          obtain ⟨hsRaw, hs12⟩ := mEv_b12_of_not_inTile c hTF
          have hs14 : mEvS14 c = 0 := h14S.2.2.2.2 (by rw [hs12, Nat.zero_testBit]) hKP
          obtain ⟨hb1f, hb2f, hb3f, hb4f⟩ :=
            t1a_knP_false_imp_bits (Or.inr trivial) (Nat.ble_eq.mp hCnt) hKP
          have hRM0 : mEvRhsMask c = 0 := by
            dsimp only [mEvRhsMask, mEvS13]
            rw [hsRaw, hs14, hb1f, hb2f, hb3f, hb4f]
            repeat rw [Nat.zero_testBit]
            rfl
          rw [show mEvLt11 c = false from by
            dsimp only [mEvLt11]
            rw [hRM0]
            exact (blt_eq_false_iff (t1EvW11 c) 0).mpr (Nat.zero_le _)]
          rfl
        · rw [Bool.or_true, Bool.or_true]
      · rfl
  refine ⟨hCare, ?_⟩; rw [wPack_t1aOut21 c hCare]
  unfold specT1a_21 specT1a_21Kel; dsimp only
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hh1, hb8, hb9, hb10]; rfl

theorem mEv_care_in21 (c : Fin (2 ^ 41)) : careT1a_21 (wPack (envTier1Sym96 c) t1aIn21) =
    true := (mEv_care_and_out21 c).1
theorem mEv_wPack_out21 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut21 =
    cond (mEvDoKel c) 1 0 + cond (mEvDoKn c) 2 0 + 4 * mEvAxEl c := (mEv_care_and_out21 c).2
theorem mEv_outW0_of_mod2_w5 {e : ℕ} {ms : List ℕ} {b : Bool} {r : ℕ}
    (h : wPack e ms = cond b 1 0 + 2 * r) : wBit e (outW ms 0) = b := by
  have hc := t1Ev_cond_lt2 b
  rw [t1Ev_wBit_outW, h,
      mEv_field_bit_at (P := 1) (Q := 2) (sh := 0) (k := 1) (i := 0)
        (x := cond b 1 0) rfl rfl rfl (by omega) (by omega),
      t1Ev_testBit0_single]
theorem mEv_out21_bits_w5 (c : Fin (2 ^ 41)) :
    wBit (envTier1Sym96 c) (outW t1aOut21 0) = mEvDoKel c ∧
    wBit (envTier1Sym96 c) (outW t1aOut21 1) = mEvDoKn c := by
  have cKel := t1Ev_cond_lt2 (mEvDoKel c)
  have cKn := t1Ev_cond_lt2 (mEvDoKn c)
  have h21 : wPack (envTier1Sym96 c) t1aOut21 =
      cond (mEvDoKel c) 1 0 + 2 * cond (mEvDoKn c) 1 0 + 4 * mEvAxEl c := by
    rw [mEv_wPack_out21 c,
        show cond (mEvDoKn c) 2 0 = 2 * cond (mEvDoKn c) 1 0 by cases mEvDoKn c <;> rfl]
  refine ⟨mEv_outW0_of_mod2_w5 (r := cond (mEvDoKn c) 1 0 + 2 * mEvAxEl c) (by omega), ?_⟩
  rw [t1Ev_wBit_outW, h21,
      mEv_field_bit_at (P := 2) (Q := 2) (sh := 1) (k := 1) (i := 0)
        (x := cond (mEvDoKn c) 1 0) rfl rfl rfl (by omega) (by omega),
      t1Ev_testBit0_single]
theorem mEv_in_bits012_w5 (e : ℕ) (ms : List ℕ) {v0 v1 v2 : Bool}
    (h0 : wBit e (mEvNth ms 0) = v0) (h1 : wBit e (mEvNth ms 1) = v1)
    (h2 : wBit e (mEvNth ms 2) = v2) :
    bitAt (wPack e ms) 0 = v0 ∧ bitAt (wPack e ms) 1 = v1 ∧ bitAt (wPack e ms) 2 = v2 :=
  ⟨(mEv_bitAt_wPack e ms 0).trans h0, (mEv_bitAt_wPack e ms 1).trans h1,
   (mEv_bitAt_wPack e ms 2).trans h2⟩
theorem mEv_care23_sw_w5 {r : ℕ} {b0 en cmp : Bool}
    (hb0 : bitAt r 0 = b0) (hb1 : bitAt r 1 = en) (hb2 : bitAt r 2 = Bool.and en cmp)
    (hImp : Bool.or (Bool.not en) b0 = true) : careTier1_23 r = true := by
  unfold careTier1_23
  rw [hb0, hb1, hb2, hImp, Bool.true_and]
  cases en <;> simp
theorem mEv_wPack_out22_23 (c : Fin (2 ^ 41)) :
    let swE := Bool.and (mEvDoEe c) (Nat.blt (t1aEvZ2 c) (t1aEvU1 c))
    let hasE1 := xor (mEvIsPot c) (mEvDoKel c)
    let e1 := cond swE (t1aEvZ2 c) (cond hasE1 (t1aEvU1 c) 0)
    let e2 := cond (mEvDoEe c) (cond swE (t1aEvU1 c) (t1aEvZ2 c)) 0
    wPack (envTier1Sym96 c) t1aOut22 = cond swE 1 0 + 2 * (e1 % 16) + 32 * (e2 % 16) ∧
    wPack (envTier1Sym96 c) t1aOut23 = (e1 / 16) + 16 * (e2 / 16) := by
  intro swE hasE1 e1 e2
  obtain ⟨b20_0, _, hPotBit⟩ := mEv_out20_bits_w5 c
  have hHasE1Bit : wBit (envTier1Sym96 c)
      (Nat.xor (Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2))
        (outW t1aOut21 0)) = hasE1 := by
    rw [t1Ev_wBit_xor, hPotBit, (mEv_out21_bits_w5 c).1]
  have hEeImpHas : Bool.or (Bool.not (mEvDoEe c)) hasE1 = true := by
    cases hE : mEvDoEe c
    · rfl
    · rcases (mEv_pot_props c).2.1 hE with ⟨_, _, _, hP, hKelF⟩
      dsimp only [hasE1]; rw [hP, hKelF]; rfl
  have hSwEq : Bool.and (mEvDoEe c) (Bool.not (wBit (envTier1Sym96 c) (outW t1aOut10 0))) =
      swE := by
    dsimp only [swE]
    cases hE : mEvDoEe c
    · rw [Bool.false_and, Bool.false_and]
    · rcases (mEv_pot_props c).2.1 hE with ⟨_, hd2, hNe, _, _⟩
      rw [Bool.true_and, Bool.true_and, (mEv_out10_bits c hd2).2 hNe, mEv_not_blt_of_ne hNe]
  obtain ⟨hu0, hu1, hz0, hz1⟩ := t1a_u1_z2_slices_w5 c
  obtain ⟨h22b0, h22b1, h22b2⟩ :=
    mEv_in_bits012_w5 (envTier1Sym96 c) t1aIn22 hHasE1Bit b20_0
      (rfl : _ = wBit _ (outW t1aOut10 0))
  have h22u : (wPack (envTier1Sym96 c) t1aIn22 / 8) % 16 = t1aEvU1 c % 16 :=
    (mEv_in_field_eq 8 16 3 4 t1aIn22 (t1EvOutSlice t1aOut04 0 4)
      rfl rfl (by decide +kernel)).trans hu0
  have h22z : (wPack (envTier1Sym96 c) t1aIn22 / 128) % 16 = t1aEvZ2 c % 16 :=
    (mEv_in_field_eq 128 16 7 4 t1aIn22 (t1EvOutSlice t1aOut06 9 4)
      rfl rfl (by decide +kernel)).trans hz0
  have hdm := mEv_cond_div_mod swE hasE1 (t1aEvU1 c) (t1aEvZ2 c) 16
  have hdm2 := mEv_cond_div_mod swE (mEvDoEe c) (t1aEvU1 c) (t1aEvZ2 c) 16
  have hCare22 : careTier1_22 (wPack (envTier1Sym96 c) t1aIn22) = true := by
    unfold careTier1_22
    rw [h22b0, h22b1]
    exact hEeImpHas
  have hOut22 : wPack (envTier1Sym96 c) t1aOut22 =
      cond swE 1 0 + 2 * (e1 % 16) + 32 * (e2 % 16) := by
    rw [wPack_t1aOut22 c hCare22]
    unfold specTier1_22
    dsimp only [e1, e2]
    rw [h22b0, h22b1, h22b2, hSwEq, h22u, h22z, hdm.1, hdm2.2.2.1]
  have hSwBit : wBit (envTier1Sym96 c) (outW t1aOut22 0) = swE :=
    mEv_outW0_of_mod2_w5 (r := e1 % 16 + 16 * (e2 % 16)) (by omega)
  obtain ⟨h23b0, h23b1, h23b2⟩ :=
    mEv_in_bits012_w5 (envTier1Sym96 c) t1aIn23 hHasE1Bit b20_0 hSwBit
  have h23u : (wPack (envTier1Sym96 c) t1aIn23 / 8) % 16 = t1aEvU1 c / 16 :=
    (mEv_in_field_eq 8 16 3 4 t1aIn23 (t1EvOutSlice t1aOut04 4 4)
      rfl rfl (by decide +kernel)).trans hu1
  have h23z : (wPack (envTier1Sym96 c) t1aIn23 / 128) % 16 = t1aEvZ2 c / 16 :=
    (mEv_in_field_eq 128 16 7 4 t1aIn23 (t1EvOutSlice t1aOut06 13 4)
      rfl rfl (by decide +kernel)).trans hz1
  have hOut23 : wPack (envTier1Sym96 c) t1aOut23 = (e1 / 16) + 16 * (e2 / 16) := by
    rw [wPack_t1aOut23 c (mEv_care23_sw_w5 h23b0 h23b1 h23b2 hEeImpHas)]
    unfold specTier1_23
    dsimp only [e1, e2]
    rw [h23b0, h23b1, h23b2, h23u, h23z, hdm.2.1, hdm2.2.2.2]
  exact ⟨hOut22, hOut23⟩
theorem mEv_wPack_out24_25 (c : Fin (2 ^ 41)) :
    let swN := Bool.and (mEvDoNn c) (Nat.blt (t1aEvD2 c).2.val (t1EvD1 c).2.val)
    let n1P := cond swN (t1aEvD2 c).2.val (cond (mEvIsPot c) (t1EvD1 c).2.val 0)
    let n2 := cond (mEvDoNn c) (cond swN (t1EvD1 c).2.val (t1aEvD2 c).2.val) 0
    let sp1 :=
        cond swN (nucSpecies (t1aEvD2 c).2).val (cond (mEvIsPot c) (nucSpecies (t1EvD1 c).2).val 0)
    let sp2 :=
        cond (mEvDoNn c) (cond swN (nucSpecies (t1EvD1 c).2).val (nucSpecies (t1aEvD2 c).2).val) 0
    wPack (envTier1Sym96 c) t1aOut24 =
      cond swN 1 0 + 2 * (n1P % 4) + 8 * (n2 % 4) + 32 * sp1 + 128 * sp2 ∧
    wPack (envTier1Sym96 c) t1aOut25 = (n1P / 4) + 16 * (n2 / 4) := by
  intro swN n1P n2 sp1 sp2
  obtain ⟨_, b20_1, hPotBit⟩ := mEv_out20_bits_w5 c
  have hNnImpPot : Bool.or (Bool.not (mEvDoNn c)) (mEvIsPot c) = true := by
    cases hN : mEvDoNn c
    · rfl
    · rw [(mEv_pot_props c).2.2 hN |>.2.2.2, Bool.or_true]
  have hSwEq : Bool.and (mEvDoNn c) (Bool.not (wBit (envTier1Sym96 c) (outW t1aOut08 0))) =
      swN := by
    dsimp only [swN]
    cases hN : mEvDoNn c
    · rw [Bool.false_and, Bool.false_and]
    · rcases (mEv_pot_props c).2.2 hN with ⟨hd1, hd2, hNe, _⟩
      rw [Bool.true_and, Bool.true_and, (mEv_out08_bits c hd1 hd2).2 hNe, mEv_not_blt_of_ne hNe]
  have hSwImp : swN = true → mEvDoNn c = true := by
    dsimp only [swN]; intro h; exact (Bool.and_eq_true_iff.mp h).1
  have hD1Hw : mEvIsPot c = true → mEvNa1Hw c = (t1EvD1 c).2.val ∧ mEvSp1Hw c =
      (nucSpecies (t1EvD1 c).2).val := by
    intro hP
    have hd1 := (mEv_pot_props c).1 hP |>.2
    rcases (mEv_out05_06_bits c).2.2.2.1 hd1 with ⟨hn, hs⟩
    exact ⟨hn, hs.trans (nucSpNatT1_eq_nucSpecies _)⟩
  have hD2Hw : mEvDoNn c = true → (mEvNa1Hw c = (t1EvD1 c).2.val ∧ mEvNa2Hw c =
      (t1aEvD2 c).2.val) ∧ (mEvSp1Hw c = (nucSpecies (t1EvD1 c).2).val ∧ mEvSp2Hw c =
      (nucSpecies (t1aEvD2 c).2).val) := by
    intro hN
    rcases (mEv_pot_props c).2.2 hN with ⟨hd1, hd2, _, _⟩
    rcases (mEv_out05_06_bits c).2.2.2.1 hd1 with ⟨hn1, hs1⟩
    rcases (mEv_out05_06_bits c).2.2.2.2 hd2 with ⟨hn2, hs2⟩
    exact ⟨⟨hn1, hn2⟩, ⟨hs1.trans (nucSpNatT1_eq_nucSpecies _),
        hs2.trans (nucSpNatT1_eq_nucSpecies _)⟩⟩
  obtain ⟨hHw1, _, hHw2, _⟩ := mEv_hw_bounds c
  obtain ⟨h24b0, h24b1, h24b2⟩ :=
    mEv_in_bits012_w5 (envTier1Sym96 c) t1aIn24 hPotBit b20_1
      (rfl : _ = wBit _ (outW t1aOut08 0))
  have h24a : (wPack (envTier1Sym96 c) t1aIn24 / 8) % 4 = mEvNa1Hw c % 4 := by
    rw [mEv_in_field_eq 8 4 3 2 t1aIn24 (t1EvOutSlice t1aOut05 3 2)
          rfl rfl (by decide +kernel), mEvNa1Hw, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice]
    omega
  have h24b : (wPack (envTier1Sym96 c) t1aIn24 / 32) % 4 = mEvNa2Hw c % 4 := by
    rw [mEv_in_field_eq 32 4 5 2 t1aIn24 (t1EvOutSlice t1aOut06 3 2)
          rfl rfl (by decide +kernel), mEvNa2Hw, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice]
    omega
  have h24s1 : (wPack (envTier1Sym96 c) t1aIn24 / 128) % 4 = mEvSp1Hw c :=
    mEv_in_field_eq 128 4 7 2 t1aIn24 (t1EvOutSlice t1aOut05 1 2) rfl rfl (by decide +kernel)
  have h24s2 : (wPack (envTier1Sym96 c) t1aIn24 / 512) % 4 = mEvSp2Hw c :=
    mEv_in_field_eq 512 4 9 2 t1aIn24 (t1EvOutSlice t1aOut06 1 2) rfl rfl (by decide +kernel)
  have hdm := mEv_cond_div_mod swN (mEvIsPot c) (t1EvD1 c).2.val (t1aEvD2 c).2.val 4
  have hdm2 := mEv_cond_div_mod swN (mEvDoNn c) (t1EvD1 c).2.val (t1aEvD2 c).2.val 4
  have hCare24 : careTier1_24 (wPack (envTier1Sym96 c) t1aIn24) = true := by
    unfold careTier1_24
    rw [h24b0, h24b1]
    exact hNnImpPot
  have hOut24 : wPack (envTier1Sym96 c) t1aOut24 =
      cond swN 1 0 + 2 * (n1P % 4) + 8 * (n2 % 4) + 32 * sp1 + 128 * sp2 := by
    rw [wPack_t1aOut24 c hCare24]
    unfold specTier1_24
    dsimp only [n1P, n2, sp1, sp2]
    rw [h24b0, h24b1, h24b2, hSwEq, h24a, h24b, h24s1, h24s2,
        mEv_mux_eq_of_imp (fun hs ↦ congrArg (· % 4) (hD2Hw (hSwImp hs)).1.2)
          (fun hp ↦ congrArg (· % 4) (hD1Hw hp).1),
        mEv_mux2_eq_of_imp (fun hn ↦ ⟨congrArg (· % 4) (hD2Hw hn).1.1,
          congrArg (· % 4) (hD2Hw hn).1.2⟩),
        mEv_mux_eq_of_imp (fun hs ↦ (hD2Hw (hSwImp hs)).2.2) (fun hp ↦ (hD1Hw hp).2),
        mEv_mux2_eq_of_imp (fun hn ↦ (hD2Hw hn).2), hdm.1, hdm2.2.2.1]
  have hSwBit : wBit (envTier1Sym96 c) (outW t1aOut24 0) = swN :=
    mEv_outW0_of_mod2_w5 (r := n1P % 4 + 4 * (n2 % 4) + 16 * sp1 + 64 * sp2) (by omega)
  obtain ⟨h25b0, h25b1, h25b2⟩ :=
    mEv_in_bits012_w5 (envTier1Sym96 c) t1aIn25 hPotBit b20_1 hSwBit
  have h25a : (wPack (envTier1Sym96 c) t1aIn25 / 8) % 16 = mEvNa1Hw c / 4 := by
    rw [mEv_in_field_eq 8 16 3 4 t1aIn25 (t1EvOutSlice t1aOut05 5 4)
          rfl rfl (by decide +kernel), mEvNa1Hw, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice]
    omega
  have h25b : (wPack (envTier1Sym96 c) t1aIn25 / 128) % 16 = mEvNa2Hw c / 4 := by
    rw [mEv_in_field_eq 128 16 7 4 t1aIn25 (t1EvOutSlice t1aOut06 5 4)
          rfl rfl (by decide +kernel), mEvNa2Hw, t1Ev_wPack_outSlice, t1Ev_wPack_outSlice]
    omega
  have hOut25 : wPack (envTier1Sym96 c) t1aOut25 = (n1P / 4) + 16 * (n2 / 4) := by
    rw [wPack_t1aOut25 c (mEv_care23_sw_w5 h25b0 h25b1 h25b2 hNnImpPot)]
    unfold specTier1_23
    dsimp only [n1P, n2]
    rw [h25b0, h25b1, h25b2, h25a, h25b,
        mEv_mux_eq_of_imp (fun hs ↦ congrArg (· / 4) (hD2Hw (hSwImp hs)).1.2)
          (fun hp ↦ congrArg (· / 4) (hD1Hw hp).1),
        mEv_mux2_eq_of_imp (fun hn ↦ ⟨congrArg (· / 4) (hD2Hw hn).1.1,
          congrArg (· / 4) (hD2Hw hn).1.2⟩), hdm.2.1, hdm2.2.2.2]
  exact ⟨hOut24, hOut25⟩

theorem mEv_doKn_bit21 (c : Fin (2 ^ 41)) :
    wBit (envTier1Sym96 c) (outW t1aOut21 1) = mEvDoKn c :=
  (mEv_out21_bits_w5 c).2

theorem mEv_not_inTile_pot_zero (c : Fin (2 ^ 41)) (hF : t1aEvInTile c = false) : mEvRawB12 c =
    0 ∧ mEvB12 c = 0 ∧ mEvT1H0 c = false ∧ (mEvS14 c).testBit 0 = false ∧ (mEvS14 c).testBit 1 =
    false ∧ mEvDoEe c = false ∧ mEvDoNn c = false ∧ mEvDoEn c = false ∧ mEvIsPot c = false := by
  rcases mEv_b12_of_not_inTile c hF with ⟨hRaw, hB12⟩
  have h14S := mEv_s14_struct c
  have hb6 : (mEvB12 c).testBit 6 = false := by rw [hB12, Nat.zero_testBit]
  have ht0 : mEvT1H0 c = false := by rw [h14S.1, hb6, Bool.false_and]
  have hs0 : (mEvS14 c).testBit 0 = false := by rw [h14S.2.1, hb6, Bool.false_and]
  have hs1 : (mEvS14 c).testBit 1 = false := by rw [h14S.2.2.1, hb6, Bool.false_and]
  have hEe : mEvDoEe c = false := by
    simp only [mEvDoEe, hB12, Nat.zero_testBit, Bool.false_and, Bool.or_false, Bool.and_false]
  have hNn : mEvDoNn c = false := by
    simp only [mEvDoNn, hB12, Nat.zero_testBit, Bool.false_and, Bool.or_false, Bool.and_false]
  have hEn : mEvDoEn c = false := by
    simp only [mEvDoEn, hB12, Nat.zero_testBit, Bool.false_and, Bool.or_false, Bool.and_false]
  refine ⟨hRaw, hB12, ht0, hs0, hs1, hEe, hNn, hEn, ?_⟩
  dsimp only [mEvIsPot]; rw [hEe, hNn, hEn]; rfl

theorem mEv_base26_zero_of_doKn (c : Fin (2 ^ 41)) (hDoKn : mEvDoKn c = true) :
    wPack (envTier1Sym96 c) t1aOut24 = 0 ∧ wPack (envTier1Sym96 c) t1aOut25 = 0 ∧
    wBit (envTier1Sym96 c) (outW t1aOut21 2) = false ∧ wBit (envTier1Sym96 c)
    (outW t1aOut21 3) = false := by
  have hKnOk : t1EvKnOk c = true := (Bool.and_eq_true_iff.mp hDoKn).1;
  have hX : (t1EvPx c).2.2.2 = true := (Bool.and_eq_true_iff.mp hKnOk).1;
  have h255 := mEv_isX_imp_hi8_255 c hX
  have hBox : t1aEvInBox c = false := by dsimp only [t1aEvInBox]; rw [hX]; rfl
  have hTile : t1aEvInTile c = false := by dsimp only [t1aEvInTile]; rw [h255]; rfl
  rcases mEv_not_inTile_pot_zero c hTile with ⟨_, _, _, _, _, _, hNn, _, hPot⟩
  have hKel : mEvDoKel c = false := by dsimp only [mEvDoKel]; rw [hBox, Bool.false_and]
  have hAxEl : mEvAxEl c = 0 := by dsimp only [mEvAxEl]; rw [hKel, Bool.cond_false]
  rcases mEv_wPack_out24_25 c with ⟨h24, h25⟩
  rw [hNn, hPot] at h24 h25; simp only [Bool.false_and, Bool.cond_false] at h24 h25
  have h21 : wPack (envTier1Sym96 c) t1aOut21 = 2 := by
    rw [mEv_wPack_out21 c, hKel, hDoKn, hAxEl]; rfl
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [t1Ev_wBit_outW, h21]; decide
  · rw [t1Ev_wBit_outW, h21]; decide

theorem mEv_wPack_out26 (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut26 = mEvN1K c + 64 *
    mEvAxK c := by
  set e := envTier1Sym96 c
  have hb0 : bitAt (wPack e t1aIn26) 0 = mEvDoKn c := by
    rw [t1aIn26, mEv_bitAt_0]; exact mEv_doKn_bit21 c
  rw [wPack_t1aOut26 c]; unfold specTier1_26; rw [hb0]
  cases hDoKn : mEvDoKn c
  · dsimp only [mEvN1K, mEvAxK]; rw [hDoKn, Bool.cond_false, Bool.cond_false, Bool.cond_false]
  · rcases mEv_base26_zero_of_doKn c hDoKn with ⟨h24, h25, h21_2, h21_3⟩
    have h24b (i : ℕ) : wBit e (outW t1aOut24 i) = false := by
      rw [t1Ev_wBit_outW, h24, Nat.zero_testBit]
    have h25b (i : ℕ) : wBit e (outW t1aOut25 i) = false := by
      rw [t1Ev_wBit_outW, h25, Nat.zero_testBit]
    have hR26Lt : wPack e t1aIn26 < 2 * 256 := wPack_lt_pow e t1aIn26;
    have hDiv2 : wPack e t1aIn26 / 2 = (wPack e t1aIn26 / 2) % 256 :=
        (Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hR26Lt)).symm
    have hSliceEq : wPack e (t1EvOutSlice t1aIn26 1 8) = wPack e t1aKin26 := by
      rw [show t1EvOutSlice t1aIn26 1 8 = t1aIn26.tail from
            listBeqNatT1_imp (by decide +kernel)]
      dsimp only [t1aIn26, List.tail, t1aKin26, wPack, e] at *
      repeat rw [t1Ev_wBit_xor]
      rw [h24b 1, h24b 2, h25b 0, h25b 1, h25b 2, h25b 3, h24b 7, h24b 8, h21_2, h21_3];
      simp only [Bool.xor_false]
    have hcK := allTree_zero mEv_cert_kinS13 (t1Ev_coin_bounds c).2.2.1
    rcases t1Ev_and4 hcK with ⟨_, hCd64, _, _⟩
    have hCd64' : mEvS13 c / 32 < 64 := Nat.blt_eq.mp hCd64
    have hAxEq : (c.val / 2 ^ 23) % 2 ^ 2 = t1EvHi10 c / 256 := by
      have hc := c.isLt; dsimp only [t1EvHi10, t1EvY20]; omega
    rw [Bool.cond_true, hDiv2,
        mEv_in_field_eq 2 256 1 8 t1aIn26 (t1EvOutSlice t1aIn26 1 8) rfl rfl (by decide +kernel),
        hSliceEq,
        show t1aKin26 = t1EvOutSlice t1aOut13 5 6 ++ t1EvWireSlice coinW 23 2
          from listBeqNatT1_imp (by decide +kernel),
        t1Ev_wPack_append, t1Ev_len_outSlice, t1Ev_wPack_outSlice, mEv_wPack_out13 c,
        show (2 : ℕ) ^ 5 = 32 from rfl, show (2 : ℕ) ^ 6 = 64 from rfl,
        Nat.mod_eq_of_lt hCd64',
        t1Ev_wPack_wireSlice _ coinW c.val 23 2 (fun i hi ↦ mEv_wBit_coinW c (by omega)),
        hAxEq]
    dsimp only [mEvN1K, mEvAxK]; rw [hDoKn, Bool.cond_true, Bool.cond_true]

theorem cond_lt_of_lt {b : Bool} {x y m : ℕ} (hx : x < m) (hy : y < m) :
    cond b x y < m := by cases b <;> dsimp only [cond] <;> omega
theorem mEv_wPack_symOuts40_master (c : Fin (2 ^ 41)) :
    let swE := Bool.and (mEvDoEe c) (Nat.blt (t1aEvZ2 c) (t1aEvU1 c))
    let swN := Bool.and (mEvDoNn c) (Nat.blt (t1aEvD2 c).2.val (t1EvD1 c).2.val)
    let hasE1 := xor (mEvIsPot c) (mEvDoKel c)
    let e1 := cond swE (t1aEvZ2 c) (cond hasE1 (t1aEvU1 c) 0)
    let e2 := cond (mEvDoEe c) (cond swE (t1aEvU1 c) (t1aEvZ2 c)) 0
    let n1P := cond swN (t1aEvD2 c).2.val (cond (mEvIsPot c) (t1EvD1 c).2.val 0)
    let n2 := cond (mEvDoNn c) (cond swN (t1EvD1 c).2.val (t1aEvD2 c).2.val) 0
    let sp1 :=
        cond swN (nucSpecies (t1aEvD2 c).2).val (cond (mEvIsPot c) (nucSpecies (t1EvD1 c).2).val 0)
    let sp2 :=
        cond (mEvDoNn c) (cond swN (nucSpecies (t1EvD1 c).2).val (nucSpecies (t1aEvD2 c).2).val) 0
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96 =
      packOut40ZeroNErem (xor (mEvIsPot c) (mEvDoKn c)) (mEvDoNn c)
        (Nat.xor n1P (mEvN1K c)) n2 hasE1 (mEvDoEe c) e1 e2
        (xor (mEvDoEe c) (mEvDoNn c)) (mEvIsPot c)
        (xor (mEvDoKel c) (mEvDoKn c)) (mEvDoNn c)
        sp1 (Nat.xor (Nat.xor sp2 (mEvAxEl c)) (mEvAxK c)) := by
  intro swE swN hasE1 e1 e2 n1P n2 sp1 sp2
  have hu : t1aEvU1 c < 256 := Nat.lt_trans (t1aEv_u1_z2_bounds c).1 (by decide)
  have hz := (t1aEv_u1_z2_bounds c).2.1
  have hd1 : (t1EvD1 c).2.val < 64 := Nat.lt_trans (t1EvD1 c).2.isLt (by decide)
  have hd2 : (t1aEvD2 c).2.val < 64 := Nat.lt_trans (t1aEvD2 c).2.isLt (by decide)
  have hs1 := (nucSpecies (t1EvD1 c).2).isLt
  have hs2 := (nucSpecies (t1aEvD2 c).2).isLt
  have haxEl : mEvAxEl c < 4 := by
    have hh1 := (t1Ev_b2_props c).2.1
    exact cond_lt_of_lt (cond_lt_of_lt (by omega) (by omega)) (by decide)
  have hn1K : mEvN1K c < 64 := by
    have hcK := allTree_zero mEv_cert_kinS13 (t1Ev_coin_bounds c).2.2.1
    have := Nat.blt_eq.mp (t1Ev_and4 hcK).2.1
    exact cond_lt_of_lt (by dsimp only [mEvS13]; omega) (by decide)
  have haxK : mEvAxK c < 4 := by
    dsimp only [mEvAxK]
    cases hDo : mEvDoKn c
    · exact Nat.zero_lt_succ 3
    · have h768 := (mEv_knOk_imp c (Bool.and_eq_true_iff.mp hDo).1).2.1
      dsimp only [cond]
      omega
  exact mEv_wPack_symOuts40_of_blocks (envTier1Sym96 c) (mEvDoEe c) (mEvDoNn c)
    (mEvDoEn c) (mEvDoKel c) (mEvDoKn c) swE swN
    (cond_lt_of_lt hz (cond_lt_of_lt hu (by decide)))
    (cond_lt_of_lt (cond_lt_of_lt hu hz) (by decide))
    (cond_lt_of_lt hd2 (cond_lt_of_lt hd1 (by decide)))
    (cond_lt_of_lt (cond_lt_of_lt hd1 hd2) (by decide))
    (cond_lt_of_lt hs2 (cond_lt_of_lt hs1 (by decide)))
    (cond_lt_of_lt (cond_lt_of_lt hs1 hs2) (by decide))
    haxEl hn1K haxK (mEv_wPack_out20 c) (mEv_wPack_out21 c)
    (mEv_wPack_out22_23 c).1 (mEv_wPack_out22_23 c).2
    (mEv_wPack_out24_25 c).1 (mEv_wPack_out24_25 c).2 (mEv_wPack_out26 c)

theorem mEv_master_eq_packOfFlags (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96 = mEvPackOfFlags (mEvDoEe c) (mEvDoNn c)
    (mEvDoEn c) (mEvDoKel c) (mEvDoKn c) (t1aEvU1 c) (t1aEvZ2 c)
    (t1EvD1 c).2.val (t1aEvD2 c).2.val (nucSpecies (t1EvD1 c).2).val (nucSpecies (t1aEvD2 c).2).val
    (mEvAxEl c) (mEvN1K c) (mEvAxK c) := by rw [mEv_wPack_symOuts40_master c]; rfl
theorem mEv_outMask_of_isKin {s : ZeroNEremSector} {na ax : ℕ} (hK : mEvIsKin s na ax = true)
    (hna : na < 47) : zeroNEremOutMask s =
    packOut40ZeroNErem true false na 0 false false 0 0 false false true false 0 ax := by
  rcases s with _ | _ | _ | _ | ⟨i, a⟩ <;> try exact Bool.noConfusion hK
  rcases Bool.and_eq_true_iff.mp hK with ⟨hi, ha⟩
  rw [mEv_outMask_kin_lt (lt_of_eq_of_lt (Nat.beq_eq.mp hi) hna),
      Nat.beq_eq.mp hi, Nat.beq_eq.mp ha]

theorem mEv_spec14_kn_indep (b3 b4 b5 b6 b7 : Bool) : specT1b_14 (8 * cond b3 1 0 + 16 *
    cond b4 1 0 + 32 * cond b5 1 0 + 64 * cond b6 1 0 + 128 * cond b7 1 0) = specT1b_14 (8 *
    cond b3 1 0 + 16 * cond b4 1 0 + 32 * cond b5 1 0) := by
  cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem mEv_cert_kinThr9_zero :
    allTree 7 0 64 (fun lo2 ↦ Nat.beq (kinNucThr9 0 lo2) 0) = true := by decide +kernel

theorem mEv_cert_kinNucT1b :
    allTree 11 0 768 (fun h ↦
      allTree 7 0 64 (fun lo2 ↦
        let p := tier1T1bKinNucBlk h
        let thr9 := kinNucThr9 p.2 lo2
        let cd := mEvS13Full h
        let knP := xor (xor (cd.testBit 1) (cd.testBit 2)) (xor (cd.testBit 3) (cd.testBit 4))
        let knUb := xor (xor (cd.testBit 1) (cd.testBit 2)) (cd.testBit 3)
        let s14 :=
            specT1b_14 (8 + 16 * cond (lo2.testBit 0) 1 0 + 32 *
            cond (xor knUb (lo2L2Mask64.testBit lo2)) 1 0)
        let m :=
            16 * cond (s14.testBit 0) 1 0 + 32 * cond (s14.testBit 1) 1 0 + 64 *
            cond (s14.testBit 2) 1 0 +
          128 * cond (s14.testBit 3) 1 0 + 256 * cond (s14.testBit 4) 1 0 + 512 *
              cond (s14.testBit 5) 1 0 +
          1024 * cond (cd.testBit 1) 1 0 + 2048 * cond (cd.testBit 2) 1 0 + 4096 *
              cond (cd.testBit 3) 1 0 +
          8192 * cond (cd.testBit 4) 1 0
        let na := cd / 32
        let ax := h / 256
        cond (cd.testBit 0)
          (Bool.and (Bool.not knP) (Bool.and (Nat.beq thr9 512) (Bool.and (Nat.blt na 47)
              (mEvIsKin p.1 na ax))))
          (cond knP
            (Bool.and (Nat.beq (mEvCmpRhsVal m) thr9) (Bool.and (Nat.blt na 47)
                (mEvIsKin p.1 na ax)))
            (Nat.beq thr9 0)))) = true := by decide +kernel

theorem mEv_eval_isX (c : Fin (2 ^ 41)) (hX : (t1EvPx c).2.2.2 = true) :
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96 =
      zeroNEremOutMask
        (let p := tier1T1bKinNucBlk (t1EvHi10 c)
         cond (Nat.blt (t1EvW11 c) (kinNucThr9 p.2 (t1EvLo10 c % 64))) p.1 .idle) := by
  have h255 := mEv_isX_imp_hi8_255 c hX
  rcases mEv_not_inTile_pot_zero c (by simp [t1aEvInTile, h255]) with ⟨hRaw12, hB12, _, _, _, hEe,
      hNn, hEn, _⟩
  have hKel : mEvDoKel c = false := by simp [mEvDoKel, t1aEvInBox, hX]
  have hAxEl : mEvAxEl c = 0 := by simp [mEvAxEl, hKel]
  have hlo2Lt : t1EvLo10 c % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [mEv_master_eq_packOfFlags c, hEe, hNn, hEn, hKel, hAxEl]
  have hIdleOf (hDoKn : mEvDoKn c = false) :
      mEvPackOfFlags false false false false (mEvDoKn c) (t1aEvU1 c) (t1aEvZ2 c)
        (t1EvD1 c).2.val (t1aEvD2 c).2.val (nucSpecies (t1EvD1 c).2).val
        (nucSpecies (t1aEvD2 c).2).val 0 (mEvN1K c) (mEvAxK c) = zeroNEremOutMask .idle := by
    rw [hDoKn, show mEvN1K c = 0 by simp [mEvN1K, hDoKn], show mEvAxK c =
        0 by simp [mEvAxK, hDoKn], mEv_pack_idle]
  cases h768 : Nat.blt (t1EvHi10 c) 768
  · rw [hIdleOf (by simp [mEvDoKn, t1EvKnOk, hX, h768])]
    dsimp only [tier1T1bKinNucBlk]
    rw [Nat.ble_eq.mpr ((blt_eq_false_iff _ _).mp h768), Bool.cond_true,
        Nat.beq_eq.mp (allTree_zero mEv_cert_kinThr9_zero hlo2Lt),
            (blt_eq_false_iff _ _).mpr (Nat.zero_le _), Bool.cond_false]
  · have hLt768 : t1EvHi10 c < 768 := Nat.blt_eq.mp h768
    have hKnOk : t1EvKnOk c = true := by simp [t1EvKnOk, hX, h768]
    have haxLt3 : t1EvHi10 c / 256 < 3 := by omega
    have hV17 := (t1aEv_v17_props c).2.2 h255
    have hw11Lt512 : t1EvW11 c < 512 := by
      have := (t1Ev_coin_bounds c).2.2.2.2.2.2.2.2.2
      dsimp only [t1aEvV17] at hV17
      omega
    have hh1Zero : (t1EvPx c).2.1 = 0 := by
      have hh1B : Bool.or (Bool.not (t1EvPx c).2.2.2) (Nat.beq (t1EvPx c).2.1 0) = true :=
        allTree_zero t1aEv_cert_b2_isX_h1 (t1Ev_coin_bounds c).2.2.2.2.2.1
      rwa [hX, Bool.not_true, Bool.false_or, Nat.beq_eq] at hh1B
    have hCert := allTree_zero (allTree_zero mEv_cert_kinNucT1b hLt768) hlo2Lt
    dsimp only at hCert ⊢
    set p := tier1T1bKinNucBlk (t1EvHi10 c)
    set thr9 := kinNucThr9 p.2 (t1EvLo10 c % 64)
    set cd := mEvS13Full (t1EvHi10 c)
    have hKinOf (hDoKn : mEvDoKn c = true) (hnaLt : Nat.blt (cd / 32) 47 = true)
        (hIsK : mEvIsKin p.1 (cd / 32) (t1EvHi10 c / 256) = true) :
        mEvPackOfFlags false false false false (mEvDoKn c) (t1aEvU1 c) (t1aEvZ2 c)
          (t1EvD1 c).2.val (t1aEvD2 c).2.val (nucSpecies (t1EvD1 c).2).val
          (nucSpecies (t1aEvD2 c).2).val 0 (mEvN1K c) (mEvAxK c) = zeroNEremOutMask p.1 := by
      have hna := Nat.blt_eq.mp hnaLt
      rw [hDoKn, show mEvN1K c = cd / 32 by simp [mEvN1K, mEvS13, cd, hDoKn],
          show mEvAxK c = t1EvHi10 c / 256 by simp [mEvAxK, hDoKn],
          mEv_pack_kinNuc _ _ _ _ _ _ hna haxLt3, mEv_outMask_of_isKin hIsK hna,
          mEv_outMask_kin_lt (lt_of_eq_of_lt (mEv_mkFin234_val (by omega)) hna),
          mEv_mkFin234_val (by omega), mEv_mkFin3_val haxLt3]
    cases hCd0 : cd.testBit 0
    · rw [hCd0, Bool.cond_false] at hCert
      cases hKnP : xor (xor (cd.testBit 1) (cd.testBit 2)) (xor (cd.testBit 3) (cd.testBit 4))
      · rw [hKnP, Bool.cond_false] at hCert
        rw [hIdleOf (by simp [mEvDoKn, mEvKnP, show mEvS13 c = cd from rfl, hCd0, hKnP]),
            Nat.beq_eq.mp hCert, (blt_eq_false_iff _ _).mpr (Nat.zero_le _), Bool.cond_false]
      · rw [hKnP, Bool.cond_true] at hCert
        rcases (by simpa only [Bool.and_eq_true] using hCert : _ ∧ _ ∧ _) with
          ⟨hRhsEq, hnaLt, hIsK⟩
        have hS14Eq : mEvS14 c = specT1b_14 (8 + 16 * cond ((t1EvLo10 c % 64).testBit 0) 1 0 +
            32 * cond (xor (xor (xor (cd.testBit 1) (cd.testBit 2)) (cd.testBit 3))
              (lo2L2Mask64.testBit (t1EvLo10 c % 64))) 1 0) := by
          dsimp only [mEvS14, mEvR14, mEvKnP, mEvKnUbXor]
          rw [hB12, Nat.zero_testBit, Bool.cond_false, hh1Zero, Nat.mul_zero, Nat.add_zero,
              Nat.zero_add, show mEvS13 c = cd from rfl, mEv_spec14_kn_indep, hKnP,
              Bool.cond_true]
        have hRhsM : mEvCmpRhsVal (mEvRhsMask c) = thr9 :=
          (congrArg mEvCmpRhsVal (by
            dsimp only [mEvRhsMask]
            rw [hRaw12, show mEvS13 c = cd from rfl, hS14Eq]
            simp only [Nat.zero_testBit, Bool.cond_false]
            omega)).trans (Nat.beq_eq.mp hRhsEq)
        have hDoKn : mEvDoKn c = Nat.blt (t1EvW11 c) thr9 := by
          dsimp only [mEvDoKn, mEvKnP, mEvLt11]
          rw [hKnOk, Bool.true_and, show mEvS13 c = cd from rfl, hCd0, hKnP,
              Bool.false_or, Bool.true_and, hRhsM]
        cases hCmp : Nat.blt (t1EvW11 c) thr9
        · rw [hIdleOf (hDoKn.trans hCmp), Bool.cond_false]
        · rw [Bool.cond_true]
          exact hKinOf (hDoKn.trans hCmp) hnaLt hIsK
    · rw [hCd0, Bool.cond_true] at hCert
      rcases t1Ev_and4 hCert with ⟨_, hThr512, hnaLt, hIsK⟩
      rw [Nat.beq_eq.mp hThr512, Nat.blt_eq.mpr hw11Lt512, Bool.cond_true]
      exact hKinOf (by simp [mEvDoKn, hKnOk, show mEvS13 c = cd from rfl, hCd0]) hnaLt hIsK

theorem mEv_eval_isY (c : Fin (2 ^ 41)) (hX : (t1EvPx c).2.2.2 = false)
    (hY : (t1aEvPy c).2.2.2 = true) : wPack (envTier1Sym96 c) symOuts40Tier1Sym96 =
    zeroNEremOutMask .idle := by
  rcases mEv_not_inTile_pot_zero c (by simp [t1aEvInTile, hY]) with ⟨_, _, _, _, _, hEe, hNn, hEn,
      _⟩
  have hKel : mEvDoKel c = false := by simp [mEvDoKel, t1aEvInBox, hY]
  have hDoKn : mEvDoKn c = false := by simp [mEvDoKn, t1EvKnOk, hX]
  rw [mEv_master_eq_packOfFlags c, hEe, hNn, hEn, hKel, hDoKn,
      show mEvAxEl c = 0 by simp [mEvAxEl, hKel], show mEvN1K c = 0 by simp [mEvN1K, hDoKn],
      show mEvAxK c = 0 by simp [mEvAxK, hDoKn], mEv_pack_idle]

theorem mEv_eval_hi8_255 (c : Fin (2 ^ 41)) (hX : (t1EvPx c).2.2.2 = false)
    (hY : (t1aEvPy c).2.2.2 = false)
    (h255 : Nat.beq (t1EvHi8 c) 255 = true) :
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96 =
        zeroNEremOutMask (.kin (mkFin234 (47 + t1aEvU1 c)) (mkFin3 (t1EvPx c).2.1)) := by
  rcases mEv_not_inTile_pot_zero c (by simp [t1aEvInTile, h255]) with ⟨_, _, ht0, hs0, hs1, hEe,
      hNn, hEn, hPot⟩
  have hKel : mEvDoKel c = true := by simp [mEvDoKel, t1aEvInBox, hX, hY, hPot, ht0]
  have hDoKn : mEvDoKn c = false := by simp [mEvDoKn, t1EvKnOk, hX]
  rw [mEv_master_eq_packOfFlags c, hEe, hNn, hEn, hKel, hDoKn,
      show mEvAxEl c = (t1EvPx c).2.1 by simp [mEvAxEl, xor, hKel, hs0, hs1],
      show mEvN1K c = 0 by simp [mEvN1K, hDoKn], show mEvAxK c = 0 by simp [mEvAxK, hDoKn]]
  exact mEv_pack_kinEl (t1aEv_u1_z2_bounds c).1 _ _ _ _ _ (t1Ev_b2_props c).2.1
def mEvSoloOf (h1 lo1 h2 lo2 : ℕ) : Bool :=
    xor (lo1.testBit 4) ((t1bSpec08xOf (h1 + 4 * lo1) (h2 + 4 * lo2)).testBit 0)
def mEvPairOf (h1 lo1 h2 lo2 : ℕ) : Bool :=
    xor (lo2.testBit 1) (xor ((fastSpec05x (h1 + 4 * lo1)).testBit 0)
    ((t1bSpec08xOf (h1 + 4 * lo1) (h2 + 4 * lo2)).testBit 1))
def mEvIntLt11 (s12 s14 w11 : ℕ) : Bool :=
    Nat.blt w11 (mEvCmpRhsVal (cond (s12.testBit 1) 1 0 + 2 * cond (s12.testBit 3) 1 0 + 4 *
    cond (s12.testBit 5) 1 0 + 8 * cond (s12.testBit 6) 1 0 + 16 * cond (s14.testBit 0) 1 0 + 32 *
    cond (s14.testBit 1) 1 0 + 64 * cond (s14.testBit 2) 1 0 + 128 * cond (s14.testBit 3) 1 0 +
    256 * cond (s14.testBit 4) 1 0 + 512 * cond (s14.testBit 5) 1 0))
def mEvIntFlags (s12 : ℕ) (s14b0 s14b1 : Bool) (h1 u1 z2 : ℕ) (d1 d2 : Bool × Fin 47)
    (lt11 : Bool) : ℕ :=
  let doEe :=
      Bool.and (Bool.and (Bool.and d1.1 d2.1) (Bool.not (Nat.beq u1 z2))) (Bool.or (s12.testBit 0)
      (Bool.and (s12.testBit 1) lt11))
  let doNn :=
      Bool.and (Bool.and (Bool.and d1.1 d2.1) (Bool.not (Nat.beq d1.2.val d2.2.val)))
      (Bool.or (s12.testBit 2) (Bool.and (s12.testBit 3) lt11))
  let doEn := Bool.and d1.1 (Bool.or (s12.testBit 4) (Bool.and (s12.testBit 5) lt11))
  let isPot := xor (xor doEe doNn) doEn
  let t1h0 := xor (s12.testBit 6) (xor s14b0 s14b1)
  let doKel := Bool.and (Bool.not isPot) (Bool.not (Bool.and t1h0 lt11))
  let axEl := cond doKel (cond (Bool.and (xor s14b0 s14b1) lt11) 0 h1) 0
  mEvPackOfFlags doEe doNn doEn doKel false u1 z2
    d1.2.val d2.2.val (nucSpecies d1.2).val (nucSpecies d2.2).val axEl 0 0

def mEvIntHwPack (s12 h1 h2 u1 z2 : ℕ) (d1 d2 : Bool × Fin 47) (lo1 lo2 w11 : ℕ) : ℕ :=
  let pair := mEvPairOf h1 lo1 h2 lo2
  let solo := mEvSoloOf h1 lo1 h2 lo2
  let s14 :=
      specT1b_14 (cond (s12.testBit 6) 1 0 + 2 * h1 + 64 * cond pair 1 0 + 128 * cond solo 1 0)
  mEvIntFlags s12 (s14.testBit 0) (s14.testBit 1) h1 u1 z2 d1 d2 (mEvIntLt11 s12 s14 w11)

theorem t1b_cert_b12_uses_lt_raw :
    allTree 11 0 1024 (fun r ↦
      let s := specSymEff12 r
      Bool.or (Bool.not (t1aUsesLt s)) (Nat.beq (specSym_12 (r % 512)) s)) = true := by
  decide +kernel

theorem mEv_spec14_b6_false {h1 : ℕ} (hh1 : h1 < 4) (pair solo : Bool) : specT1b_14 (2 * h1 + 64 *
    cond pair 1 0 + 128 * cond solo 1 0) = 0 := by
  rcases (show h1 = 0 ∨ h1 = 1 ∨ h1 = 2 ∨ h1 = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases pair <;> cases solo <;> decide

theorem mEv_spec14_kn_false_indep {h1 : ℕ} (hh1 : h1 < 4) (b0 b4 b5 pair solo : Bool) :
    specT1b_14 (cond b0 1 0 + 2 * h1 + 0 + 16 * cond b4 1 0 + 32 * cond b5 1 0 + 64 *
    cond pair 1 0 + 128 * cond solo 1 0) = specT1b_14 (cond b0 1 0 + 2 * h1 + 64 * cond pair 1 0 +
    128 * cond solo 1 0) := by
  rcases (show h1 = 0 ∨ h1 = 1 ∨ h1 = 2 ∨ h1 = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases b0 <;> cases b4 <;> cases b5 <;> cases pair <;> cases solo <;> decide

theorem t1a_usesLt_false_bits {s12 : ℕ} (h : t1aUsesLt s12 = false) : s12.testBit 1 = false ∧
    s12.testBit 3 = false ∧ s12.testBit 5 = false ∧ s12.testBit 6 = false := by
  unfold t1aUsesLt at h
  cases b1 : s12.testBit 1 <;> cases b3 : s12.testBit 3 <;>
    cases b5 : s12.testBit 5 <;> cases b6 : s12.testBit 6 <;>
    rw [b1, b3, b5, b6] at h <;>
    first | exact ⟨rfl, rfl, rfl, rfl⟩ | exact absurd h (by decide)

theorem mEv_intFlags_no_lt {s12 h1 u1 z2 : ℕ} (d1 d2 : Bool × Fin 47) (b1 b2 : Bool)
    (hb1 : s12.testBit 1 = false) (hb3 : s12.testBit 3 = false) (hb5 : s12.testBit 5 = false)
    (hb6 : s12.testBit 6 = false) : mEvIntFlags s12 false false h1 u1 z2 d1 d2 b1 =
    mEvIntFlags s12 false false h1 u1 z2 d1 d2 b2 := by
  unfold mEvIntFlags; simp only [hb1, hb3, hb5, hb6, xor, bne_self_eq_false, Bool.false_and]
theorem t1a_not_eq_true {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b <;> first | rfl | exact Bool.noConfusion h
theorem mEv_inTile_pack_eq (c : Fin (2 ^ 41)) (hT : t1aEvInTile c = true) :
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96 = mEvIntHwPack (mEvB12 c)
    (t1EvPx c).2.1 (t1aEvPy c).2.1 (t1aEvU1 c) (t1aEvZ2 c) (t1EvD1 c) (t1aEvD2 c) (t1EvB8 c % 64)
    (t1EvLo10 c % 64) (t1EvW11 c) := by
  rcases mEv_inTile_imp c hT with ⟨h255F, _, hYF, hBox, hKnOk⟩
  have hDoKn : mEvDoKn c = false := by dsimp only [mEvDoKn]; rw [hKnOk, Bool.false_and]
  have hN1K : mEvN1K c = 0 := by dsimp only [mEvN1K]; rw [hDoKn]; rfl
  have hAxK : mEvAxK c = 0 := by dsimp only [mEvAxK]; rw [hDoKn]; rfl
  have hKel : mEvDoKel c = Bool.and (Bool.not (mEvIsPot c)) (Bool.not (Bool.and (mEvT1H0 c)
      (mEvLt11 c))) := by unfold mEvDoKel; rw [hBox, Bool.true_and]
  rw [mEv_master_eq_packOfFlags c, hDoKn, hN1K, hAxK]
  have hLHS : mEvPackOfFlags (mEvDoEe c) (mEvDoNn c) (mEvDoEn c) (mEvDoKel c) false (t1aEvU1 c)
      (t1aEvZ2 c)
      (t1EvD1 c).2.val (t1aEvD2 c).2.val (nucSpecies (t1EvD1 c).2).val (nucSpecies
      (t1aEvD2 c).2).val (mEvAxEl c) 0 0 = mEvIntFlags (mEvB12 c) ((mEvS14 c).testBit 0)
      ((mEvS14 c).testBit 1) (t1EvPx c).2.1 (t1aEvU1 c) (t1aEvZ2 c) (t1EvD1 c) (t1aEvD2 c)
      (mEvLt11 c) := by unfold mEvT1H0 at hKel; unfold mEvAxEl mEvIntFlags; rw [hKel]; rfl
  rw [hLHS]; unfold mEvIntHwPack; dsimp only
  have hh1 : (t1EvPx c).2.1 < 4 := Nat.lt_trans (t1Ev_b2_props c).2.1 (by omega)
  cases hUse : t1aUsesLt (mEvB12 c)
  · rcases t1a_usesLt_false_bits hUse with ⟨hb1, hb3, hb5, hb6⟩
    have h14S := mEv_s14_struct c
    have hs0 : (mEvS14 c).testBit 0 = false := by rw [h14S.2.1, hb6, Bool.false_and]
    have hs1 : (mEvS14 c).testBit 1 = false := by rw [h14S.2.2.1, hb6, Bool.false_and]
    rw [hs0, hs1, hb6, Bool.cond_false, Nat.zero_add, mEv_spec14_b6_false hh1, Nat.zero_testBit,
        Nat.zero_testBit]; exact mEv_intFlags_no_lt (t1EvD1 c) (t1aEvD2 c) _ _ hb1 hb3 hb5 hb6
  · have hA := mr_e2_r12 (t1aEvInTile c) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))
      (t1Ev_b2_props c).2.2.1 (t1aEv_b6_props c).2.2.1
    have hRawEqB :=
        allTree_zero t1b_cert_b12_uses_lt_raw hA.2.1; change Bool.or (Bool.not (t1aUsesLt
        (mEvB12 c))) (Nat.beq (specSym_12 (mEvR12 c % 512)) (mEvB12 c)) =
        true at hRawEqB; rw [hUse, Bool.not_true, Bool.false_or] at hRawEqB
    have hR12Mod : mEvR12 c % 512 = mEvRawR12 c := by
      have h1 := hA.1; dsimp only [mEvR12, mEvRawR12] at h1 ⊢;
      have h2 := t1Ev_cond_lt2 (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64)); omega
    have hRaw12Eq : mEvRawB12 c = mEvB12 c := by
      dsimp only [mEvRawB12]; rw [← hR12Mod]; exact Nat.beq_eq.mp hRawEqB
    have hB12U :=
        (Bool.and_eq_true_iff.mp (allTree_zero t1aEv_cert_b12_uses_lt hA.2.1)).1; change Bool.or
        (Bool.not (t1aUsesLt (mEvB12 c))) (Bool.or (Nat.beq ((mEvR12 c / 16) % 32) 25)
        (Bool.or (Nat.beq ((mEvR12 c / 16) % 32) 26) (Nat.beq ((mEvR12 c / 16) % 32) 27))) =
        true at hB12U; dsimp only [mEvR12, mEvRawR12] at hB12U; rw [hUse, Bool.not_true,
        Bool.false_or,
        hA.2.2.2.2.2.2.2.2.2] at hB12U; have hInv1 :=
                                          (Bool.and_eq_true_iff.mp (allTree_zero
                                          t1aEv_cert_hi10_invs (t1Ev_coin_bounds c).2.2.1)).1;
                                          change Bool.or (t1aEvPy c).2.2.2
                                          (Bool.or (Bool.not (Bool.or (Nat.beq (t1aEvPy c).2.2.1 25)
                                          (Bool.or (Nat.beq (t1aEvPy c).2.2.1 26)
                                          (Nat.beq (t1aEvPy c).2.2.1 27))))
                                          (Bool.and (Bool.not ((mEvS13 c).testBit 1))
                                          (Bool.and (Bool.not ((mEvS13 c).testBit 2))
                                          (Bool.and (Bool.not ((mEvS13 c).testBit 3))
                                          (Bool.not ((mEvS13 c).testBit 4)))))) =
                                          true at hInv1; rw [hYF, Bool.false_or, hB12U,
                                          Bool.not_true, Bool.false_or] at hInv1
    rcases t1Ev_and4 hInv1 with ⟨ns1, ns2, ns3, ns4⟩
    have ks1 : (mEvS13 c).testBit 1 = false := t1a_not_eq_true ns1;
    have ks2 : (mEvS13 c).testBit 2 = false := t1a_not_eq_true ns2;
    have ks3 : (mEvS13 c).testBit 3 = false := t1a_not_eq_true ns3;
    have ks4 : (mEvS13 c).testBit 4 = false := t1a_not_eq_true ns4
    have hKnPF : mEvKnP c = false := by dsimp only [mEvKnP]; rw [ks1, ks2, ks3, ks4]; rfl
    have hB8Eq : t1EvB8 c = t1EvLo8 c := by dsimp only [t1EvB8]; rw [h255F, Bool.cond_false]
    have hSoloEq : mEvSolo14 c = mEvSoloOf (t1EvPx c).2.1 (t1EvB8 c % 64)
        (t1aEvPy c).2.1 (t1EvLo10 c % 64) := by
      dsimp only [mEvSolo14, mEvSoloOf]
      rw [← hB8Eq, show (64 : ℕ) = 2 ^ 6 from rfl, b2_testBit_mod_pow _ 6 4 (by decide)]
    have hPairEq : mEvPair14 c =
        mEvPairOf (t1EvPx c).2.1 (t1EvB8 c % 64) (t1aEvPy c).2.1 (t1EvLo10 c % 64) := rfl
    have hS14Eq : mEvS14 c = specT1b_14 (cond ((mEvB12 c).testBit 6) 1 0 + 2 * (t1EvPx c).2.1 +
        64 * cond (mEvPairOf (t1EvPx c).2.1 (t1EvB8 c % 64)
        (t1aEvPy c).2.1 (t1EvLo10 c % 64)) 1 0 + 128 *
        cond (mEvSoloOf (t1EvPx c).2.1 (t1EvB8 c % 64) (t1aEvPy c).2.1 (t1EvLo10 c % 64)) 1 0)
        := by
      dsimp only [mEvS14, mEvR14]; rw [hKnPF, Bool.cond_false, Nat.mul_zero, hSoloEq, hPairEq];
      exact mEv_spec14_kn_false_indep hh1 _ _ _ _ _
    have hLt : mEvLt11 c = mEvIntLt11 (mEvB12 c) (mEvS14 c) (t1EvW11 c) := by
      unfold mEvLt11 mEvIntLt11 mEvRhsMask; rw [hRaw12Eq, ks1, ks2, ks3, ks4]
      dsimp only [cond]; repeat rw [Nat.mul_zero]; repeat rw [Nat.add_zero]
    rw [hLt, ← hS14Eq]

theorem mEv_cmpRhs_consts :
    mEvCmpRhsVal 0 = 0 ∧
    mEvCmpRhsVal 1 = 1452 ∧
    mEvCmpRhsVal 2 = 1750 ∧
    mEvCmpRhsVal 4 = 401 := by decide +kernel
theorem mEv_intHwPack_of_b6_false {s12 h1 h2 u1 z2 : ℕ} (hb6 : s12.testBit 6 = false)
    (hh1 : h1 < 4) (d1 d2 : Bool × Fin 47)
    (lo1 lo2 w11 : ℕ) : mEvIntHwPack s12 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
    mEvIntFlags s12 false false h1 u1 z2 d1 d2 (mEvIntLt11 s12 0 w11) := by
  unfold mEvIntHwPack; dsimp only
  rw [hb6, Bool.cond_false, Nat.zero_add, mEv_spec14_b6_false hh1, Nat.zero_testBit,
      Nat.zero_testBit]

theorem mEv_intLt11_s14_0 (s12 w11 : ℕ) (hb6 : s12.testBit 6 = false) : mEvIntLt11 s12 0 w11 =
    Nat.blt w11 (mEvCmpRhsVal (cond (s12.testBit 1) 1 0 + 2 * cond (s12.testBit 3) 1 0 + 4 *
    cond (s12.testBit 5) 1 0))
    := by
  unfold mEvIntLt11; simp only [hb6, Nat.zero_testBit, Bool.cond_false, Nat.mul_zero, Nat.add_zero]
theorem mEv_intFlags_w5 {s h1 u1 z2 : ℕ} {b0 b2 b4 : Bool}
    (hb : s.testBit 0 = b0 ∧ s.testBit 1 = false ∧ s.testBit 2 = b2 ∧
      s.testBit 3 = false ∧ s.testBit 4 = b4 ∧ s.testBit 5 = false ∧ s.testBit 6 = false)
    (d1 d2 : Bool × Fin 47) (b : Bool) :
    mEvIntFlags s false false h1 u1 z2 d1 d2 b =
      let doEe := (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2)) && b0
      let doNn := (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val)) && b2
      let doEn := d1.1 && b4
      let isPot := xor (xor doEe doNn) doEn
      mEvPackOfFlags doEe doNn doEn (Bool.not isPot) false u1 z2
        d1.2.val d2.2.val (nucSpecies d1.2).val (nucSpecies d2.2).val
        (cond (Bool.not isPot) h1 0) 0 0 := by
  unfold mEvIntFlags
  dsimp only
  rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2]
  simp only [Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true, Bool.cond_false,
    show xor false false = false from rfl]
theorem mEv_intFlags_0 {h1 u1 : ℕ} (hh1 : h1 < 3) (hu1 : u1 < 187) (z2 : ℕ)
    (d1 d2 : Bool × Fin 47) (b : Bool) :
    mEvIntFlags 0 false false h1 u1 z2 d1 d2 b =
      zeroNEremOutMask (.kin (mkFin234 (47 + u1)) (mkFin3 h1)) := by
  rw [mEv_intFlags_w5 (b0 := false) (b2 := false) (b4 := false) (by decide),
      Bool.and_false, Bool.and_false, Bool.and_false]
  exact mEv_pack_kinEl hu1 _ _ _ _ _ hh1
theorem mEv_intHwPack_0 {h1 h2 u1 : ℕ} (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187) (z2 : ℕ)
    (d1 d2 : Bool × Fin 47) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 0 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask (.kin (mkFin234 (47 + u1)) (mkFin3 h1)) := by
  rw [mEv_intHwPack_of_b6_false (by decide) (by omega)]
  exact mEv_intFlags_0 hh1 hu1 z2 d1 d2 _
theorem mEv_intFlags_1 {h1 u1 z2 : ℕ} (hh1 : h1 < 3) (hu1 : u1 < 187)
    (d1 d2 : Bool × Fin 47) (hz2 : d2.1 = true → z2 < 187) (b : Bool) :
    mEvIntFlags 1 false false h1 u1 z2 d1 d2 b =
      zeroNEremOutMask
        (cond (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
          (let cE := Nat.blt z2 u1
           .ee d1.2 (mkFin187 (cond cE z2 u1)) (mkFin187 (cond cE u1 z2)))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) := by
  rw [mEv_intFlags_w5 (b0 := true) (b2 := false) (b4 := false) (by decide),
      Bool.and_true, Bool.and_false, Bool.and_false]
  cases hg : (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
  · exact mEv_pack_kinEl hu1 _ _ _ _ _ hh1
  · exact mEv_pack_ee hu1 (hz2 (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).2)
      d1.2 d2.2.val (nucSpecies d2.2).val
theorem mEv_intHwPack_1 {h1 h2 u1 z2 : ℕ} (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187)
    (d1 d2 : Bool × Fin 47) (hz2 : d2.1 = true → z2 < 187) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 1 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask
        (cond (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
          (let cE := Nat.blt z2 u1
           .ee d1.2 (mkFin187 (cond cE z2 u1)) (mkFin187 (cond cE u1 z2)))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) := by
  rw [mEv_intHwPack_of_b6_false (by decide) (by omega)]
  exact mEv_intFlags_1 hh1 hu1 d1 d2 hz2 _
theorem mEv_intFlags_pair {s sHalf : ℕ} (lt11 : Bool)
    (h0 : Bool.or (s.testBit 0) (Bool.and (s.testBit 1) lt11) =
          Bool.or ((cond lt11 sHalf 0).testBit 0) (Bool.and ((cond lt11 sHalf 0).testBit 1) lt11))
    (h2 : Bool.or (s.testBit 2) (Bool.and (s.testBit 3) lt11) =
          Bool.or ((cond lt11 sHalf 0).testBit 2) (Bool.and ((cond lt11 sHalf 0).testBit 3) lt11))
    (h4 : Bool.or (s.testBit 4) (Bool.and (s.testBit 5) lt11) =
          Bool.or ((cond lt11 sHalf 0).testBit 4) (Bool.and ((cond lt11 sHalf 0).testBit 5) lt11))
    (h6 : s.testBit 6 = (cond lt11 sHalf 0).testBit 6)
    (h1 u1 z2 : ℕ) (d1 d2 : Bool × Fin 47) :
    mEvIntFlags s false false h1 u1 z2 d1 d2 lt11 =
      mEvIntFlags (cond lt11 sHalf 0) false false h1 u1 z2 d1 d2 lt11 := by
  dsimp only [mEvIntFlags]
  rw [h0, h2, h4, h6]
theorem mEv_intHwPack_thresh {s sHalf idx thr h1 h2 u1 z2 : ℕ} {act : ZeroNEremSector}
    (d1 d2 : Bool × Fin 47)
    (hb6 : s.testBit 6 = false)
    (hIdx : cond (s.testBit 1) 1 0 + 2 * cond (s.testBit 3) 1 0 + 4 * cond (s.testBit 5) 1 0 = idx)
    (hRhs : mEvCmpRhsVal idx = thr)
    (hPair : ∀ b : Bool, mEvIntFlags s false false h1 u1 z2 d1 d2 b =
      mEvIntFlags (cond b sHalf 0) false false h1 u1 z2 d1 d2 b)
    (hh1 : h1 < 3) (hu1 : u1 < 187)
    (hAct : mEvIntFlags sHalf false false h1 u1 z2 d1 d2 true = zeroNEremOutMask act)
    (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack s h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask (cond (Nat.blt w11 thr) act (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) := by
  rw [mEv_intHwPack_of_b6_false hb6 (by omega), mEv_intLt11_s14_0 s w11 hb6, hIdx, hRhs, hPair]
  cases Nat.blt w11 thr
  · exact mEv_intFlags_0 hh1 hu1 z2 d1 d2 false
  · exact hAct
theorem mEv_intHwPack_2 {h1 h2 u1 z2 : ℕ}
    (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187)
    (d1 d2 : Bool × Fin 47) (hz2 : d2.1 = true → z2 < 187) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 2 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask
        (cond (Nat.blt w11 1452)
          (cond (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
            (let cE := Nat.blt z2 u1
             .ee d1.2 (mkFin187 (cond cE z2 u1)) (mkFin187 (cond cE u1 z2)))
            (.kin (mkFin234 (47 + u1)) (mkFin3 h1)))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) :=
  mEv_intHwPack_thresh (sHalf := 1) (idx := 1) d1 d2 (by decide) (by decide) mEv_cmpRhs_consts.2.1
    (fun b ↦ mEv_intFlags_pair b (by cases b <;> decide) (by cases b <;> decide)
        (by cases b <;> decide)
      (by cases b <;> decide) h1 u1 z2 d1 d2) hh1 hu1 (mEv_intFlags_1 hh1 hu1 d1 d2 hz2 true) lo1
          lo2 w11
theorem mEv_intFlags_4 {h1 u1 : ℕ} (hh1 : h1 < 3) (hu1 : u1 < 187)
    (z2 : ℕ) (d1 d2 : Bool × Fin 47) (b : Bool) :
    mEvIntFlags 4 false false h1 u1 z2 d1 d2 b =
      zeroNEremOutMask
        (cond (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val))
          (let cN := Nat.blt d2.2.val d1.2.val
           .nn (cond cN d2.2 d1.2) (cond cN d1.2 d2.2) (mkFin187 u1))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) := by
  rw [mEv_intFlags_w5 (b0 := false) (b2 := true) (b4 := false) (by decide),
      Bool.and_false, Bool.and_true, Bool.and_false]
  cases d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val)
  · exact mEv_pack_kinEl hu1 _ _ _ _ _ hh1
  · exact mEv_pack_nn hu1 z2 d1.2 d2.2
theorem mEv_intHwPack_4 {h1 h2 u1 : ℕ} (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187)
    (z2 : ℕ) (d1 d2 : Bool × Fin 47) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 4 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask
        (cond (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val))
          (let cN := Nat.blt d2.2.val d1.2.val
           .nn (cond cN d2.2 d1.2) (cond cN d1.2 d2.2) (mkFin187 u1))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) := by
  rw [mEv_intHwPack_of_b6_false (by decide) (by omega)]
  exact mEv_intFlags_4 hh1 hu1 z2 d1 d2 _
theorem mEv_intHwPack_8 {h1 h2 u1 : ℕ}
    (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187)
    (z2 : ℕ) (d1 d2 : Bool × Fin 47) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 8 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask
        (cond (Nat.blt w11 1750)
          (cond (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val))
            (let cN := Nat.blt d2.2.val d1.2.val
             .nn (cond cN d2.2 d1.2) (cond cN d1.2 d2.2) (mkFin187 u1))
            (.kin (mkFin234 (47 + u1)) (mkFin3 h1)))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) :=
  mEv_intHwPack_thresh (sHalf := 4) (idx := 2) d1 d2 (by decide)
      (by decide) mEv_cmpRhs_consts.2.2.1
    (fun b ↦ mEv_intFlags_pair b (by cases b <;> decide) (by cases b <;> decide)
        (by cases b <;> decide)
      (by cases b <;> decide) h1 u1 z2 d1 d2) hh1 hu1 (mEv_intFlags_4 hh1 hu1 z2 d1 d2 true) lo1
          lo2 w11
theorem mEv_intFlags_16 {h1 u1 : ℕ} (hh1 : h1 < 3) (hu1 : u1 < 187) (z2 : ℕ)
    (d1 d2 : Bool × Fin 47) (b : Bool) :
    mEvIntFlags 16 false false h1 u1 z2 d1 d2 b =
      zeroNEremOutMask (cond d1.1 (.en d1.2 (mkFin187 u1)) (.kin (mkFin234 (47 + u1)) (mkFin3 h1)))
          := by
  rw [mEv_intFlags_w5 (b0 := false) (b2 := false) (b4 := true) (by decide),
      Bool.and_false, Bool.and_false, Bool.and_true]
  cases d1.1
  · exact mEv_pack_kinEl hu1 _ _ _ _ _ hh1
  · exact mEv_pack_en hu1 z2 d1.2 d2.2.val (nucSpecies d2.2).val
theorem mEv_intHwPack_16 {h1 h2 u1 : ℕ} (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187) (z2 : ℕ)
    (d1 d2 : Bool × Fin 47) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 16 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask (cond d1.1 (.en d1.2 (mkFin187 u1)) (.kin (mkFin234 (47 + u1)) (mkFin3 h1)))
          := by
  rw [mEv_intHwPack_of_b6_false (by decide) (by omega)]
  exact mEv_intFlags_16 hh1 hu1 z2 d1 d2 _
theorem mEv_intHwPack_32 {h1 h2 u1 : ℕ} (hh1 : h1 < 3) (_hh2 : h2 < 3) (hu1 : u1 < 187)
    (z2 : ℕ) (d1 d2 : Bool × Fin 47) (lo1 lo2 w11 : ℕ) :
    mEvIntHwPack 32 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask
        (cond (Nat.blt w11 401)
          (cond d1.1 (.en d1.2 (mkFin187 u1)) (.kin (mkFin234 (47 + u1)) (mkFin3 h1)))
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) :=
  mEv_intHwPack_thresh (sHalf := 16) (idx := 4) d1 d2 (by decide)
      (by decide) mEv_cmpRhs_consts.2.2.2
    (fun b ↦ mEv_intFlags_pair b (by cases b <;> decide) (by cases b <;> decide)
        (by cases b <;> decide)
      (by cases b <;> decide) h1 u1 z2 d1 d2) hh1 hu1 (mEv_intFlags_16 hh1 hu1 z2 d1 d2 true) lo1
          lo2 w11
theorem t1b_cert_solo_pair :
    allTree 4 0 3 (fun h1 ↦ allTree 8 0 64 (fun lo1 ↦ allTree 4 0 3 (fun h2 ↦
        allTree 8 0 64 (fun lo2 ↦
      cond (Nat.beq h1 0) (b2BEq (mEvSoloOf h1 lo1 h2 lo2) (t1SoloBit (64 * h1 + lo1)
          (64 * h2 + lo2)))
        (b2BEq (mEvPairOf h1 lo1 h2 lo2) (t1PairBit (64 * h1 + lo1) (64 * h2 + lo2))))))) =
    true := by decide +kernel
theorem mEv_spec14_t1_t1b (pair solo : Bool) :
    specT1b_14 (1 + 2 * 0 + 64 * cond pair 1 0 + 128 * cond false 1 0) = 0 ∧
    specT1b_14 (1 + 2 * 0 + 64 * cond pair 1 0 + 128 * cond true 1 0) = 32 ∧
    specT1b_14 (1 + 2 * 1 + 64 * cond false 1 0 + 128 * cond solo 1 0) = 1 ∧
    specT1b_14 (1 + 2 * 1 + 64 * cond true 1 0 + 128 * cond solo 1 0) = 17 ∧
    specT1b_14 (1 + 2 * 2 + 64 * cond false 1 0 + 128 * cond solo 1 0) = 2 ∧
    specT1b_14 (1 + 2 * 2 + 64 * cond true 1 0 + 128 * cond solo 1 0) = 18 := by
  cases pair <;> cases solo <;> decide
theorem mEv_intLt11_64 (w11 : ℕ) :
    mEvIntLt11 64 0 w11 = Nat.blt w11 148 ∧ mEvIntLt11 64 32 w11 = Nat.blt w11 149 ∧
    mEvIntLt11 64 1 w11 = Nat.blt w11 1306 ∧ mEvIntLt11 64 17 w11 = Nat.blt w11 1944 ∧
    mEvIntLt11 64 2 w11 = Nat.blt w11 2044 ∧ mEvIntLt11 64 18 w11 = Nat.blt w11 1406 :=
  ⟨congrArg (Nat.blt w11) (by decide +kernel), congrArg (Nat.blt w11) (by decide +kernel),
   congrArg (Nat.blt w11) (by decide +kernel), congrArg (Nat.blt w11) (by decide +kernel),
   congrArg (Nat.blt w11) (by decide +kernel), congrArg (Nat.blt w11) (by decide +kernel)⟩
theorem mEv_intFlags_64 (s14b0 s14b1 : Bool) (h1 u1 z2 : ℕ) (d1 d2 : Bool × Fin 47) (lt11 : Bool) :
    mEvIntFlags 64 s14b0 s14b1 h1 u1 z2 d1 d2 lt11 =
      let doKel := Bool.not (Bool.and (xor true (xor s14b0 s14b1)) lt11)
      mEvPackOfFlags false false false doKel false u1 z2 d1.2.val d2.2.val (nucSpecies d1.2).val
          (nucSpecies d2.2).val
        (cond doKel (cond (Bool.and (xor s14b0 s14b1) lt11) 0 h1) 0) 0 0 := by
  have hb : (64 : ℕ).testBit 0 = false ∧ (64 : ℕ).testBit 1 = false ∧ (64 : ℕ).testBit 2 = false ∧
      (64 : ℕ).testBit 3 = false ∧ (64 : ℕ).testBit 4 = false ∧ (64 : ℕ).testBit 5 = false ∧
      (64 : ℕ).testBit 6 = true := by decide
  unfold mEvIntFlags
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2,
    Bool.false_and, Bool.and_false, Bool.false_or]
  rfl
theorem mEv_intFlags_64_pair {s14 h1 u1 z2 : ℕ} (hh1 : h1 < 3) (hu1 : u1 < 187)
    (hx : xor (s14.testBit 0) (s14.testBit 1) = true) (d1 d2 : Bool × Fin 47) (lt11 : Bool) :
    mEvIntFlags 64 (s14.testBit 0) (s14.testBit 1) h1 u1 z2 d1 d2 lt11 =
      zeroNEremOutMask (cond lt11 (.kin (mkFin234 (47 + u1)) (mkFin3 0))
        (.kin (mkFin234 (47 + u1)) (mkFin3 h1))) := by
  rw [mEv_intFlags_64]
  dsimp only
  rw [hx, show xor true true = false from rfl, Bool.false_and, Bool.not_false, Bool.true_and,
      Bool.cond_true]
  cases lt11
  · exact mEv_pack_kinEl hu1 _ _ _ _ _ hh1
  · exact mEv_pack_kinEl hu1 _ _ _ _ _ (Nat.zero_lt_succ 2)
theorem mEv_intHwPack_64 {h1 h2 u1 lo1 lo2 : ℕ}
    (hh1 : h1 < 3) (hh2 : h2 < 3) (hu1 : u1 < 187) (hlo1 : lo1 < 64) (hlo2 : lo2 < 64)
    (z2 : ℕ) (d1 d2 : Bool × Fin 47) (w11 : ℕ) :
    let z1Idx := 64 * h1 + lo1
    let z2Idx := 64 * h2 + lo2
    mEvIntHwPack 64 h1 h2 u1 z2 d1 d2 lo1 lo2 w11 = zeroNEremOutMask (cond (Nat.beq h1 0)
      (cond (Nat.blt w11 (cond (t1SoloBit z1Idx z2Idx) 149 148)) .idle (.kin (mkFin234 (47 + u1))
          (mkFin3 h1)))
      (cond (Nat.beq h1 1 && Nat.blt w11 (cond (t1PairBit z1Idx z2Idx) 1944 1306))
        (.kin (mkFin234 (47 + u1)) (mkFin3 0))
        (cond (Nat.beq h1 2 && Nat.blt w11 (cond (t1PairBit z1Idx z2Idx) 1406 2044))
          (.kin (mkFin234 (47 + u1)) (mkFin3 0)) (.kin (mkFin234 (47 + u1)) (mkFin3 h1))))) := by
  intro z1Idx z2Idx
  have hCert :=
      allTree_zero (allTree_zero (allTree_zero (allTree_zero t1b_cert_solo_pair hh1) hlo1) hh2) hlo2
  have hlt64 := mEv_intLt11_64 w11
  unfold mEvIntHwPack
  dsimp only
  rw [show (64 : ℕ).testBit 6 = true by decide, Bool.cond_true]
  rcases (show h1 = 0 ∨ h1 = 1 ∨ h1 = 2 by omega) with rfl | rfl | rfl
  · rw [show Nat.beq 0 0 = true from rfl, Bool.cond_true] at hCert ⊢
    rw [(b2_bEq_iff _ _).mp hCert]
    have hc := mEv_spec14_t1_t1b (mEvPairOf 0 lo1 h2 lo2) false
    have hSolo (s14 : ℕ) (hb0 : s14.testBit 0 = false) (hb1 : s14.testBit 1 = false)
        (lt11 : Bool) : mEvIntFlags 64 (s14.testBit 0) (s14.testBit 1) 0 u1 z2 d1 d2 lt11 =
        zeroNEremOutMask (cond lt11 .idle (.kin (mkFin234 (47 + u1)) (mkFin3 0))) := by
      rw [hb0, hb1, mEv_intFlags_64]
      cases lt11
      · exact mEv_pack_kinEl hu1 _ _ _ _ _ hh1
      · exact mEv_pack_idle _ _ _ _ _ _
    cases t1SoloBit z1Idx z2Idx
    · rw [hc.1, Bool.cond_false, hlt64.1]
      exact hSolo 0 (by decide) (by decide) _
    · rw [hc.2.1, Bool.cond_true, hlt64.2.1]
      exact hSolo 32 (by decide) (by decide) _
  · rw [show Nat.beq 1 0 = false from rfl, Bool.cond_false] at hCert ⊢
    rw [(b2_bEq_iff _ _).mp hCert, show Nat.beq 1 1 = true from rfl, Bool.true_and,
        show Nat.beq 1 2 = false from rfl, Bool.false_and, Bool.cond_false]
    have hc := mEv_spec14_t1_t1b false (mEvSoloOf 1 lo1 h2 lo2)
    cases t1PairBit z1Idx z2Idx
    · rw [hc.2.2.1, Bool.cond_false, hlt64.2.2.1]
      exact mEv_intFlags_64_pair hh1 hu1 (by decide) d1 d2 _
    · rw [hc.2.2.2.1, Bool.cond_true, hlt64.2.2.2.1]
      exact mEv_intFlags_64_pair hh1 hu1 (by decide) d1 d2 _
  · rw [show Nat.beq 2 0 = false from rfl, Bool.cond_false] at hCert ⊢
    rw [(b2_bEq_iff _ _).mp hCert, show Nat.beq 2 1 = false from rfl, Bool.false_and,
        Bool.cond_false,
        show Nat.beq 2 2 = true from rfl, Bool.true_and]
    have hc := mEv_spec14_t1_t1b false (mEvSoloOf 2 lo1 h2 lo2)
    cases t1PairBit z1Idx z2Idx
    · rw [hc.2.2.2.2.1, Bool.cond_false, hlt64.2.2.2.2.1]
      exact mEv_intFlags_64_pair hh1 hu1 (by decide) d1 d2 _
    · rw [hc.2.2.2.2.2, Bool.cond_true, hlt64.2.2.2.2.2]
      exact mEv_intFlags_64_pair hh1 hu1 (by decide) d1 d2 _
def mEvExpectedB12 (q5 q31 : ℕ) (g66 : Bool) : ℕ :=
  cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4)) 1
    (cond (Nat.beq q31 25 && Nat.beq q5 4) 2
      (cond (Nat.ble 16 q31 && Nat.blt q31 24) 4
        (cond (Nat.beq q31 26 && Nat.beq q5 4) 8
          (cond (Nat.ble 28 q31 || (Nat.beq q31 27 && Nat.beq q5 4 && Bool.not g66)) 16
            (cond (Nat.beq q31 27 && Nat.beq q5 4 && g66) 32
              (cond (Nat.beq q31 27 && Nat.beq q5 3) 64 0))))))

theorem mEv_cert_spec12 :
    allTree 4 0 8 (fun q5 ↦
      allTree 6 0 32 (fun q31 ↦
        allTree 2 0 2 (fun g ↦
          Bool.or (Bool.not (Bool.and (Nat.ble q5 4) (Nat.ble q31 30)))
            (Nat.beq (specSymEff12 (1 + 2 * q5 + 16 * q31 + 512 * g))
              (mEvExpectedB12 q5 q31 (Nat.beq g 1)))))) = true := by decide +kernel

theorem mEv_spec12_eq {q5 q31 : ℕ} (hq5 : q5 ≤ 4) (hq31 : q31 ≤ 30)
    (g66 : Bool) : specSymEff12 (1 + 2 * q5 + 16 * q31 + 512 * cond g66 1 0) =
    mEvExpectedB12 q5 q31 g66 := by
  have hgLt : cond g66 1 0 < 2 := t1Ev_cond_lt2 g66
  have h := allTree_zero
    (allTree_zero (allTree_zero mEv_cert_spec12 (show q5 < 8 by omega))
      (show q31 < 32 by omega)) hgLt
  rw [Nat.ble_eq.mpr hq5, Nat.ble_eq.mpr hq31, Bool.and_true, Bool.not_true, Bool.false_or] at h
  have hBeq : Nat.beq (cond g66 1 0) 1 = g66 := by cases g66 <;> rfl
  rw [hBeq] at h; exact Nat.beq_eq.mp h
theorem mEv_intHwPack_expected_eq_intCell
    {u1 h1 h2 q5 q31 lo1 lo2 w11 : ℕ}
    (hu1 : u1 < 187) (hh1 : h1 < 3) (hh2 : h2 < 3)
    (hlo1 : lo1 < 64) (hlo2 : lo2 < 64)
    (hz2 : (decodeUltraNuc192 (64 * h2 + lo2)).1 = true → b11Z2OfHX h2 lo2 < 187) :
    let d1 := decodeUltraNuc192 (64 * h1 + lo1)
    let d2 := decodeUltraNuc192 (64 * h2 + lo2)
    let z2 := b11Z2OfHX h2 lo2
    mEvIntHwPack (mEvExpectedB12 q5 q31 (g66VOpt h2 lo2)) h1 h2 u1 z2 d1 d2 lo1 lo2 w11 =
      zeroNEremOutMask (tier1W11IntCell u1 h1 h2 q5 q31 lo1 lo2 w11) := by
  intro d1 d2 z2; unfold mEvExpectedB12 tier1W11IntCell; dsimp only
  cases hg1 : (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4))
  · rw [Bool.false_or, Bool.cond_false]
    cases hg2 : (Nat.beq q31 25 && Nat.beq q5 4)
    · rw [Bool.false_and, Bool.cond_false, Bool.cond_false]
      cases hg3 : (Nat.ble 16 q31 && Nat.blt q31 24)
      · rw [Bool.false_or, Bool.cond_false]
        cases hg4 : (Nat.beq q31 26 && Nat.beq q5 4)
        · rw [Bool.false_and, Bool.cond_false, Bool.cond_false]
          cases hg5a : Nat.ble 28 q31
          · simp only [Bool.false_or]
            cases hg6 : (Nat.beq q31 27 && Nat.beq q5 4)
            · simp only [Bool.false_and, Bool.cond_false]
              cases hg7 : (Nat.beq q31 27 && Nat.beq q5 3)
              · rw [Bool.cond_false, Bool.cond_false];
                exact mEv_intHwPack_0 hh1 hh2 hu1 z2 d1 d2 lo1 lo2 w11
              · rw [Bool.cond_true, Bool.cond_true];
                exact mEv_intHwPack_64 hh1 hh2 hu1 hlo1 hlo2 z2 d1 d2 w11
            · rcases Bool.and_eq_true_iff.mp hg6 with ⟨hq31, hq5⟩
              simp only [Bool.true_and]
              cases hg66 : g66VOpt h2 lo2
              · simp only [Bool.not_false, Bool.true_or, Bool.cond_true];
                exact mEv_intHwPack_16 hh1 hh2 hu1 z2 d1 d2 lo1 lo2 w11
              · simp only [Bool.not_true, Bool.false_or, Bool.cond_false, Bool.cond_true];
                rw [mEv_intHwPack_32 hh1 hh2 hu1 z2 d1 d2 lo1 lo2 w11, Nat.beq_eq.mp hq31,
                    Nat.beq_eq.mp hq5]
                cases Nat.blt w11 401 <;> rfl
          · simp only [Bool.true_or, Bool.cond_true];
            exact mEv_intHwPack_16 hh1 hh2 hu1 z2 d1 d2 lo1 lo2 w11
        · rcases Bool.and_eq_true_iff.mp hg4 with ⟨hq31, hq5⟩
          rw [Bool.true_and, Bool.cond_true, mEv_intHwPack_8 hh1 hh2 hu1 z2 d1 d2 lo1 lo2 w11,
              Nat.beq_eq.mp hq31, Nat.beq_eq.mp hq5]
          cases Nat.blt w11 1750 <;> rfl
      · rw [Bool.true_or, Bool.cond_true, Bool.cond_true];
        exact mEv_intHwPack_4 hh1 hh2 hu1 z2 d1 d2 lo1 lo2 w11
    · rcases Bool.and_eq_true_iff.mp hg2 with ⟨hq31, hq5⟩
      rw [Bool.true_and, Bool.cond_true, mEv_intHwPack_2 hh1 hh2 hu1 d1 d2 hz2 lo1 lo2 w11,
          Nat.beq_eq.mp hq31, Nat.beq_eq.mp hq5]
      cases Nat.blt w11 1452 <;> rfl
  · rw [Bool.true_or, Bool.cond_true, Bool.cond_true];
    exact mEv_intHwPack_1 hh1 hh2 hu1 d1 d2 hz2 lo1 lo2 w11
theorem mEv_decode_eq (c : Fin (2 ^ 41)) :
    decodeTier1W11Opt1424Coin c =
      cond (t1EvPx c).2.2.2
        (let p := tier1T1bKinNucBlk (t1EvHi10 c)
         cond (Nat.blt (t1EvW11 c) (kinNucThr9 p.2 (t1EvLo10 c % 64))) p.1 .idle)
        (cond (t1aEvPy c).2.2.2 .idle
          (cond (Nat.beq (t1EvHi8 c) 255)
            (.kin (mkFin234 (47 + t1aEvU1 c)) (mkFin3 (t1EvPx c).2.1))
            (tier1W11IntCell (t1aEvU1 c) (t1EvPx c).2.1 (t1aEvPy c).2.1
              (t1EvPx c).2.2.1 (t1aEvPy c).2.2.1
              (t1EvB8 c % 64) (t1EvLo10 c % 64) (t1EvW11 c)))) := by
  have hBeq : ((t1EvHi8 c == 255) : Bool) = Nat.beq (t1EvHi8 c) 255 := by
    cases h1 : (t1EvHi8 c == 255) <;> cases h2 : Nat.beq (t1EvHi8 c) 255 <;> simp_all [Nat.beq_eq]
  have ha8 : cond (t1EvHi8 c == 255) (255 - t1EvLo8 c) (t1EvHi8 c) = t1EvA8 c := by rw [hBeq]; rfl
  have hb8 : cond (t1EvHi8 c == 255) 0 (t1EvLo8 c) = t1EvB8 c := by rw [hBeq]; rfl
  unfold decodeTier1W11Opt1424Coin
  change (let b8 := cond (t1EvHi8 c == 255) 0 (t1EvLo8 c)
    let w11 := t1EvC5 c + 32 * (t1EvLo10 c / 64) + 512 * (b8 / 64)
    let px := Cartesian254.b2Spec (cond (t1EvHi8 c == 255) (255 - t1EvLo8 c) (t1EvHi8 c))
    let py := Cartesian254.b6Spec (Nat.xor (t1EvHi10 c) 96)
    cond px.2.2.2
      (cond (Nat.blt w11 (kinNucThr9 (tier1T1bKinNucBlk (t1EvHi10 c)).2 (t1EvLo10 c % 64)))
        (tier1T1bKinNucBlk (t1EvHi10 c)).1 .idle)
      (cond py.2.2.2 .idle
        (cond (t1EvHi8 c == 255)
          (.kin (mkFin234 (47 + FermatInverse.phiU1 py.1 px.1)) (mkFin3 px.2.1))
          (tier1W11IntCell (PhotochemistrySolution.FermatInverse.phiU1 py.1 px.1)
            px.2.1 py.2.1 px.2.2.1 py.2.2.1 (b8 % 64) (t1EvLo10 c % 64) w11)))) = _
  rw [ha8, hb8, hBeq]; rfl
theorem mEv_wPack_symOuts40_eq (c : Fin (2 ^ 41)) :
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96 =
    zeroNEremOutMask (decodeTier1W11Opt1424Coin c) := by
  rw [mEv_decode_eq c]
  cases hX : (t1EvPx c).2.2.2
  · rw [Bool.cond_false]
    cases hY : (t1aEvPy c).2.2.2
    · rw [Bool.cond_false]
      cases h255 : Nat.beq (t1EvHi8 c) 255
      · rw [Bool.cond_false]
        have hTile : t1aEvInTile c = true := by dsimp only [t1aEvInTile]; rw [h255, hY]; rfl
        have hB12 : mEvB12 c = specSymEff12 (1 + 2 * (t1EvPx c).2.2.1 + 16 * (t1aEvPy c).2.2.1 +
            512 * cond (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64)) 1 0)
            := by dsimp only [mEvB12, mEvR12, mEvRawR12]; rw [hTile, Bool.cond_true]
        rw [mEv_inTile_pack_eq c hTile, hB12, mEv_spec12_eq ((t1Ev_b2_props c).2.2.2.2 hX)
            ((t1aEv_b6_props c).2.2.2.2 hY) (g66VOpt (t1aEvPy c).2.1 (t1EvLo10 c % 64))]
        exact mEv_intHwPack_expected_eq_intCell
          (t1aEv_u1_z2_bounds c).1
          (t1Ev_b2_props c).2.1
          (t1aEv_b6_props c).2.1
          (Nat.mod_lt _ (by omega))
          (Nat.mod_lt _ (by omega))
          (t1aEv_u1_z2_bounds c).2.2
      · rw [Bool.cond_true]; exact mEv_eval_hi8_255 c hX hY h255
    · rw [Bool.cond_true]; exact mEv_eval_isY c hX hY
  · rw [Bool.cond_true]; exact mEv_eval_isX c hX
theorem xag_tier1W11Opt1424_eval : ∀ (c : Fin (2 ^ 41))
    (j : Fin 40),
    oddBits (xagEnv c.val nGatesTier1Sym96 gatesTier1Sym96 nGatesTier1Sym96 le_rfl &&&
    outs40Tier1Sym96 j) (42 + nGatesTier1Sym96) =
    (zeroNEremOutMask (decodeTier1W11Opt1424Coin c)).testBit j.val := by
  intro c j
  rw [oddBits_eq_wBit_gen (N := nGatesTier1Sym96)
      (by dsimp only [nGatesTier1Sym96, nGatesTier1W11Opt1416]; omega) c,
      show xagEnv c.val nGatesTier1Sym96 gatesTier1Sym96 nGatesTier1Sym96 le_rfl =
        envTier1Sym96 c from rfl,
      show outs40Tier1Sym96 j = outW outs40ListTier1Sym96 j.val from rfl,
      outs40ListTier1Sym96_eq_sym, t1Ev_wBit_outW, mEv_wPack_symOuts40_eq c]

-- ============================================================================
-- STAGE C: Reverse XAG + Bilinear Phase-Uncompute (`1,424 T/step`)
-- ============================================================================
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
    (dLayout rOuter41Layout val_rOuter41Layout rOut40Layout val_rOut40Layout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact (rScrCompact1493
    val_rScrCompact1493)
open PhotochemistrySolution.Stage1AsymRevEngine
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore (ActiveOuterCoinStackOf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc (mr_revT1_wBit_xor
    mr_revT1_wBit_outW mr_wPack_cons_zero_t1 mr_wPack_cons_succ_t1 mr_listXor_singleton_t1
    mr_listXor_two_t1 mr_xor_cancel_left_t1 mr_xor_mid_swap_t1 mr_evalBilinear_two_b0_t1
    mr_evalBilinear_two_t1 mr_evalBilinear_three_t1 mr_evalBilinear_five_t1 mr_mid32OutIdx_lt8_t1
    mr_mid32OutIdx_8_16_t1 mr_mid32OutIdx_16_22_t1 mr_mid32OutIdx_22_28_t1 mr_mid32OutIdx_ge28_t1
    mr_revT1_cert_f20_props mr_revT1_cert_f22_sw mr_revT1_cert_f24_sw mr_f22MidBitOkT1
    mr_f23MidBitOkT1 mr_f24MidBitOkT1 mr_f25MidBitOkT1 mr_revT1_cert_mid_f22 mr_revT1_cert_mid_f23
    mr_revT1_cert_mid_f24 mr_revT1_cert_mid_f25)

abbrev revCoreGatesSym96 : Fin 143 → ℕ × ℕ := gatesTier1Sym96Rev144
def coreMask0Sym96 : ℕ := Nat.xor 1 (outW t1aOut10 0)
def coreMask1Sym96 : ℕ := Nat.xor 1 (outW t1aOut08 0)

def mr_naKnT1aW (i : ℕ) : ℕ := outW t1aOut13 (5 + i)

def midPreXSym96 (_ : Fin 32) : Bool := false

def midTermsSym96At (v : ℕ) : List (List ℕ × List ℕ) :=
    cond (Nat.blt v 8) [([185], bitsOfMaskT1 (outW t1aOut06 (9 + v)) 185),
    ([190], bitsOfMaskT1 (Nat.xor (outW t1aOut04 v) (outW t1aOut06 (9 + v))) 185)]
    (cond (Nat.blt v 16) [([188], bitsOfMaskT1 (outW t1aOut04 (v - 8)) 185),
    ([185], bitsOfMaskT1 (outW t1aOut06 (9 + (v - 8))) 185)] (cond (Nat.blt v 22)
    [([186], bitsOfMaskT1 (outW t1aOut06 (3 + (v - 16))) 185),
    ([191], bitsOfMaskT1 (Nat.xor (outW t1aOut05 (3 + (v - 16)))
    (outW t1aOut06 (3 + (v - 16)))) 185)] (cond (Nat.blt v 28)
    [([187], bitsOfMaskT1 (outW t1aOut05 (3 + (v - 22))) 185),
    ([186], bitsOfMaskT1 (outW t1aOut06 (3 + (v - 22))) 185),
    ([189, 187], bitsOfMaskT1 (mr_naKnT1aW (v - 22)) 185)] (cond (Nat.blt v 30)
    [([187], bitsOfMaskT1 (outW t1aOut05 (1 + (v - 28))) 185),
    ([191], bitsOfMaskT1 (Nat.xor (outW t1aOut05 (1 + (v - 28)))
    (outW t1aOut06 (1 + (v - 28)))) 185)] (cond (Nat.beq v 30)
    [([186], bitsOfMaskT1 (outW t1aOut06 1) 185), ([191], bitsOfMaskT1 (Nat.xor (outW t1aOut05 1)
    (outW t1aOut06 1)) 185), ([189, 187], bitsOfMaskT1 (coinW 23) 185),
    ([188, 187], bitsOfMaskT1 (outW tier1Out02 5) 185), (bitsOfMaskT1 (outW t1aOut14 0) 185,
    bitsOfMaskT1 (outW t1aOut18 0) 185)] [([186], bitsOfMaskT1 (outW t1aOut06 2) 185),
    ([191], bitsOfMaskT1 (Nat.xor (outW t1aOut05 2) (outW t1aOut06 2)) 185),
    ([189, 187], bitsOfMaskT1 (coinW 24) 185), ([188, 187], bitsOfMaskT1 (outW tier1Out02 6) 185),
    (bitsOfMaskT1 (outW t1aOut14 1) 185, bitsOfMaskT1 (outW t1aOut18 0) 185)])))))
def midTermsSym96 (j : Fin 32) : List (List ℕ × List ℕ) := midTermsSym96At j.val

def tailPreXSym96 (_ : Fin 5) : Bool := false

def tailTermsSym96At (v : ℕ) : List (List ℕ × List ℕ) :=
    cond (Nat.beq v 0) [(bitsOfMaskT1 (t1aXor4 1 (outW t1aIn20 7) (outW t1aIn20 8)
    (outW t1aIn20 9)) 185, bitsOfMaskT1 (outW t1aIn20 0) 185), (bitsOfMaskT1 (outW t1aIn20 1) 185,
    bitsOfMaskT1 (t1aXor4 (outW t1aIn20 6) (outW t1aRevOut20 1) (outW t1aRevOut20 2)
    (outW t1aRevOut20 3)) 185), (bitsOfMaskT1 (outW t1aIn20 0) 185,
    bitsOfMaskT1 (Nat.xor (outW t1aRevOut20 1) (outW t1aRevOut20 2)) 185),
    (bitsOfMaskT1 (t1aXor3 (outW t1aIn20 10) (outW t1aIn20 5) (outW t1aRevOut20 0)) 185,
    bitsOfMaskT1 (outW t1aRevOut20 2) 185)] (cond (Nat.beq v 1)
    [(bitsOfMaskT1 (outW t1aIn20 2) 185, bitsOfMaskT1 (Nat.xor (outW t1aRevOut20 1)
    (outW t1aRevOut20 2)) 185), (bitsOfMaskT1 (outW t1aIn20 3) 185,
    bitsOfMaskT1 (t1aXor4 (outW t1aIn20 6) (outW t1aRevOut20 1) (outW t1aRevOut20 2)
    (outW t1aRevOut20 3)) 185)] (cond (Nat.beq v 2)
    [([186, 185], [0]), (bitsOfMaskT1 (t1aXor5 (outW t1aIn20 0) (outW t1aIn20 2) (outW t1aIn20 4)
    (outW t1aRevOut20 1) (outW t1aRevOut20 2)) 185, [0]),
    (bitsOfMaskT1 (Nat.xor 1 (outW t1aIn20 7)) 185, bitsOfMaskT1 (t1aXor4 (outW t1aIn20 2)
    (outW t1aIn20 4) (outW t1aIn20 6) (outW t1aRevOut20 3)) 185),
    (bitsOfMaskT1 (t1aXor3 (outW t1aIn20 0) (outW t1aIn20 2) (outW t1aIn20 4)) 185,
    bitsOfMaskT1 (Nat.xor (outW t1aIn20 6) (outW t1aRevOut20 3)) 185),
    (bitsOfMaskT1 (outW t1aIn20 5) 185, bitsOfMaskT1 (t1aXor4 (outW t1aIn20 6) (outW t1aRevOut20 1)
    (outW t1aRevOut20 2) (outW t1aRevOut20 3)) 185)] (cond (Nat.beq v 3)
    [(bitsOfMaskT1 (Nat.xor 1 (outW tier1Out02 10)) 185,
    bitsOfMaskT1 (Nat.xor 1 (outW t1aOut03 11)) 185), (bitsOfMaskT1 (Nat.xor (outW t1aOut12 6)
    (Nat.xor (outW t1aOut14 0) (outW t1aOut14 1))) 185, bitsOfMaskT1 (outW t1aOut18 0) 185)]
    [([187], [0]), (bitsOfMaskT1 (outW t1aOut11 1) 185, bitsOfMaskT1 (Nat.xor (outW t1aOut13 0)
    (outW t1aOut18 0)) 185)])))
def tailTermsSym96 (s : Fin 5) : List (List ℕ × List ℕ) := tailTermsSym96At s.val

theorem t1a_evalBilinear_four_b0 (f : ℕ → Bool) (a1 b1 a2 b2 a3 b3 a4 b4 : List ℕ) :
    evalBilinearBool f [(a1, b1), (a2, b2), (a3, b3), (a4, b4)] = xor (listXorBool f a1 &&
    listXorBool f b1) (xor (listXorBool f a2 && listXorBool f b2)
    (xor (listXorBool f a3 && listXorBool f b3) (listXorBool f a4 && listXorBool f b4)))
    := by dsimp only [evalBilinearBool]; rw [Bool.xor_false]
theorem t1a_evalBilinear_five_b0 (f : ℕ → Bool) (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : List ℕ) :
    evalBilinearBool f [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5)] = xor (listXorBool f a1 &&
    listXorBool f b1) (xor (listXorBool f a2 && listXorBool f b2)
    (xor (listXorBool f a3 && listXorBool f b3) (xor (listXorBool f a4 && listXorBool f b4)
    (listXorBool f a5 && listXorBool f b5))))
    := by dsimp only [evalBilinearBool]; rw [Bool.xor_false]
theorem mr_cert_checkBilinearTerms_midT1a : allTree 6 0 32 (fun v ↦ checkBilinearTerms (49 + 143)
    (midTermsSym96At v)) = true := by decide +kernel
theorem checkBilinearTerms_midTermsSym96 (j : Fin 32) : checkBilinearTerms (49 + 143)
    (midTermsSym96 j) = true := allTree_zero mr_cert_checkBilinearTerms_midT1a j.isLt
theorem mr_cert_checkBilinearTerms_tailT1a : allTree 4 0 5 (fun v ↦ checkBilinearTerms (42 + 143 +
    v) (tailTermsSym96At v)) = true := by decide +kernel
theorem checkBilinearTerms_tailTermsSym96 (s : Fin 5) : checkBilinearTerms (42 + 143 + s.val)
    (tailTermsSym96 s) = true := allTree_zero mr_cert_checkBilinearTerms_tailT1a s.isLt
theorem mr_revT1a_wBit_not1 (c : Fin (2 ^ 41)) (a : ℕ) : wBit (envTier1Sym96 c)
    (Nat.xor 1 a) = Bool.not (wBit (envTier1Sym96 c) a) := by
  rw [mr_revT1_wBit_xor]
  have h1 : wBit (envTier1Sym96 c) 1 = true := wBit_const1_gen (by decide +kernel) c
  rw [h1]; cases wBit (envTier1Sym96 c) a <;> rfl

theorem wBit_rev144_const1 (c : Fin (2 ^ 41)) : wBit (envTier1Sym96Rev144 c) 1 = true :=
  wBit_const1_gen (by decide +kernel) c

theorem t1a_true_xor (b : Bool) : xor true b = Bool.not b := by cases b <;> rfl

theorem mr_listXor_mid_fwd_t1a (c : Fin (2 ^ 41)) (m40 msk : ℕ)
    (hLt : Nat.blt msk (1 <<< (42 + 139)) = true) :
    listXorBool (midPredBit 143 gatesTier1Sym96Rev144 coreMask0Sym96 coreMask1Sym96 c m40)
    (bitsOfMaskT1 msk 185) = wBit (envTier1Sym96 c) msk := by
  have h1 :
      listXorBool (midPredBit 143 gatesTier1Sym96Rev144 coreMask0Sym96 coreMask1Sym96 c
      m40) (bitsOfMaskT1 msk 185) = wBit (envTier1Sym96Rev144 c) msk := by
    rw [listXorBool_midPredBit_bitsOfMaskT1 143 gatesTier1Sym96Rev144 _ _ c m40 msk,
        oddBits_eq_wBit_gen (N := 143) (by omega) c msk]; rfl
  exact h1.trans (wBit_rev144_eq_fwd_of_lt140 c hLt)

theorem mr_listXor_tail_rev_t1a (c : Fin (2 ^ 41))
    (m40 msk : ℕ) : listXorBool (tailPredBit 143 gatesTier1Sym96Rev144 c m40)
    (bitsOfMaskT1 msk 185) = wBit (envTier1Sym96Rev144 c) msk := by
  rw [listXorBool_tailPredBit_bitsOfMaskT1 143 gatesTier1Sym96Rev144 c m40 msk,
      oddBits_eq_wBit_gen (N := 143) (by omega) c msk]; rfl

theorem mr_listXor_tail_fwd_t1a (c : Fin (2 ^ 41)) (m40 msk : ℕ)
    (hLt : Nat.blt msk (1 <<< (42 + 139)) = true) :
    listXorBool (tailPredBit 143 gatesTier1Sym96Rev144 c m40) (bitsOfMaskT1 msk 185) =
    wBit (envTier1Sym96 c) msk :=
    (mr_listXor_tail_rev_t1a c m40 msk).trans (wBit_rev144_eq_fwd_of_lt140 c hLt)
theorem mr_midPredBit_tmp0_t1a (c : Fin (2 ^ 41))
    (m40 : ℕ) :
    midPredBit 143 gatesTier1Sym96Rev144 coreMask0Sym96 coreMask1Sym96 c m40 190 =
    (preCnotBit40 m40 15 && Bool.not (wBit (envTier1Sym96 c) (outW t1aOut10 0))) := by
  change (preCnotBit40 m40 15 && oddBits (xagEnv c.val 143 _ 143 le_rfl &&& coreMask0Sym96)
      (42 + 143)) = _
  rw [oddBits_eq_wBit_gen (N := 143) (by omega) c coreMask0Sym96]
  exact congrArg (preCnotBit40 m40 15 && ·)
    ((wBit_rev144_eq_fwd_of_lt140 c (by decide +kernel)).trans (mr_revT1a_wBit_not1 c _))

theorem mr_midPredBit_tmp1_t1a (c : Fin (2 ^ 41))
    (m40 : ℕ) :
    midPredBit 143 gatesTier1Sym96Rev144 coreMask0Sym96 coreMask1Sym96 c m40 191 =
    (preCnotBit40 m40 1 && Bool.not (wBit (envTier1Sym96 c) (outW t1aOut08 0))) := by
  change (preCnotBit40 m40 1 && oddBits (xagEnv c.val 143 _ 143 le_rfl &&& coreMask1Sym96)
      (42 + 143)) = _
  rw [oddBits_eq_wBit_gen (N := 143) (by omega) c coreMask1Sym96]
  exact congrArg (preCnotBit40 m40 1 && ·)
    ((wBit_rev144_eq_fwd_of_lt140 c (by decide +kernel)).trans (mr_revT1a_wBit_not1 c _))

def outs40HwMaskTier1Sym96 (c : Fin (2 ^ 41)) : ℕ :=
    wPack (envTier1Sym96 c) symOuts40Tier1Sym96

theorem mr_outs40HwMaskSym_testBit_eq_of_xag (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (hXag : ∀ (c : Fin (2 ^ 41))
    (j : Fin 40), oddBits (xagEnv c.val 209 gatesTier1Sym96 209 le_rfl &&& outs40Tier1Sym96 j)
    (42 + 209) = (zeroNEremOutMask (decode c)).testBit j.val) (c : Fin (2 ^ 41))
    (k : Fin 40) : (outs40HwMaskTier1Sym96 c).testBit k.val =
    (zeroNEremOutMask (decode c)).testBit k.val := by
  dsimp only [outs40HwMaskTier1Sym96]; rw [← outs40ListTier1Sym96_eq_sym, testBit_wPack]
  change wBit (envTier1Sym96 c) (outs40Tier1Sym96 k) = _; unfold envTier1Sym96
  exact (oddBits_eq_wBit_gen (N := nGatesTier1Sym96)
      (by decide +kernel) c _).symm.trans (hXag c k)

theorem mr_eval_out20_sym (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut20 =
    specTier1_20 (wPack (envTier1Sym96 c) t1aIn20) := wPack_t1aOut20 c (mEv_care_in20 c)
theorem mr_eval_out21_sym (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut21 =
    specT1a_21 (wPack (envTier1Sym96 c) t1aIn21) := wPack_t1aOut21 c (mEv_care_in21 c)
theorem mr_revSym_cert_f21_not_pot_kel : allTree 12 0 2048 (fun r ↦ Bool.or (Bool.not (bitAt r 2))
    (Bool.not ((specT1a_21 r).testBit 0))) = true := by decide +kernel
theorem mr_care_in22_sym (c : Fin (2 ^ 41)) : careTier1_22 (wPack (envTier1Sym96 c) t1aIn22) =
    true := by
  have h20 :=
      allTree_zero mr_revT1_cert_f20_props (wPack_lt_pow (envTier1Sym96 c) t1aIn20);
      rw [mEv_care_in20 c, Bool.not_true, Bool.false_or,
      ← mr_eval_out20_sym c] at h20; dsimp only at h20; have hDoEe :=
                                                          (Bool.and_eq_true_iff.mp
                                                          (Bool.and_eq_true_iff.mp h20).2).1;
                                                          have h21 :=
                                                          allTree_zero
                                                          mr_revSym_cert_f21_not_pot_kel
                                                          (wPack_lt_pow (envTier1Sym96 c)
                                                          t1aIn21); rw [← mr_eval_out21_sym c]
                                                          at h21; simp only [← mr_revT1_wBit_outW]
                                                          at hDoEe h21; dsimp only [t1aIn21] at h21;
                                                          dsimp only [careTier1_22,
                                                          t1aIn22]; simp only [bitAt_eq_testBit,
                                                          mr_wPack_cons_succ_t1,
                                                          mr_wPack_cons_zero_t1,
                                                          mr_revT1_wBit_xor] at hDoEe h21 ⊢
  revert hDoEe h21
  generalize wBit (envTier1Sym96 c) (outW t1aOut20 0) = d0
  generalize wBit (envTier1Sym96 c) (outW t1aOut20 1) = d1
  generalize wBit (envTier1Sym96 c) (outW t1aOut20 2) = d2
  generalize wBit (envTier1Sym96 c) (outW t1aOut21 0) = kel
  cases d0 <;> cases d1 <;> cases d2 <;> cases kel <;>
    intro h1 h2 <;> first | rfl | exact Bool.noConfusion h1 | exact Bool.noConfusion h2

theorem mr_eval_out22_sym (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut22 =
    specTier1_22 (wPack (envTier1Sym96 c) t1aIn22) := wPack_t1aOut22 c (mr_care_in22_sym c)
theorem mr_care_in23_sym (c : Fin (2 ^ 41)) : careTier1_23 (wPack (envTier1Sym96 c) t1aIn23) =
    true := by
  have h22 := mr_care_in22_sym c;
  have hSw :=
      allTree_zero mr_revT1_cert_f22_sw (wPack_lt_pow (envTier1Sym96 c) t1aIn22);
      rw [← mr_eval_out22_sym c] at hSw; simp only [← mr_revT1_wBit_outW] at hSw; dsimp only
      [careTier1_22, t1aIn22] at h22; dsimp only [t1aIn22] at hSw; dsimp only [careTier1_23,
      t1aIn23]; simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1,
      mr_revT1_wBit_xor] at h22 hSw ⊢; exact Bool.and_eq_true_iff.mpr ⟨h22, hSw⟩
theorem mr_eval_out23_sym (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut23 =
    specTier1_23 (wPack (envTier1Sym96 c) t1aIn23) := wPack_t1aOut23 c (mr_care_in23_sym c)
theorem mr_care_in24_sym (c : Fin (2 ^ 41)) : careTier1_24 (wPack (envTier1Sym96 c) t1aIn24) =
    true := by
  have h20 :=
      allTree_zero mr_revT1_cert_f20_props (wPack_lt_pow (envTier1Sym96 c) t1aIn20);
      rw [mEv_care_in20 c, Bool.not_true, Bool.false_or,
      ← mr_eval_out20_sym c] at h20; dsimp only at h20; have hNn :=
                                                          (Bool.and_eq_true_iff.mp
                                                          (Bool.and_eq_true_iff.mp
                                                          (Bool.and_eq_true_iff.mp h20).2).2).1;
                                                          simp only [← mr_revT1_wBit_outW] at hNn;
                                                          dsimp only [careTier1_24,
                                                          t1aIn24]; simp only [bitAt_eq_testBit,
                                                          mr_wPack_cons_succ_t1,
                                                          mr_wPack_cons_zero_t1,
                                                          mr_revT1_wBit_xor]; exact hNn
theorem mr_eval_out24_sym (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut24 =
    specTier1_24 (wPack (envTier1Sym96 c) t1aIn24) := wPack_t1aOut24 c (mr_care_in24_sym c)
theorem mr_care_in25_sym (c : Fin (2 ^ 41)) : careTier1_23 (wPack (envTier1Sym96 c) t1aIn25) =
    true := by
  have h24 := mr_care_in24_sym c;
  have hSw :=
      allTree_zero mr_revT1_cert_f24_sw (wPack_lt_pow (envTier1Sym96 c) t1aIn24);
      rw [← mr_eval_out24_sym c] at hSw; simp only [← mr_revT1_wBit_outW] at hSw; dsimp only
      [careTier1_24, t1aIn24] at h24; dsimp only [t1aIn24] at hSw; dsimp only [careTier1_23,
      t1aIn25]; simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1,
      mr_revT1_wBit_xor] at h24 hSw ⊢; exact Bool.and_eq_true_iff.mpr ⟨h24, hSw⟩
theorem mr_eval_out25_sym (c : Fin (2 ^ 41)) : wPack (envTier1Sym96 c) t1aOut25 =
    specTier1_23 (wPack (envTier1Sym96 c) t1aIn25) := wPack_t1aOut25 c (mr_care_in25_sym c)
theorem mr_hwMask_testBit_sym (c : Fin (2 ^ 41)) (k : ℕ) : (outs40HwMaskTier1Sym96 c).testBit k =
    wBit (envTier1Sym96 c) (outW symOuts40Tier1Sym96 k) :=
    testBit_wPack (envTier1Sym96 c) symOuts40Tier1Sym96 k
theorem mr_preCnot_hw_sym_15 (c : Fin (2 ^ 41)) : preCnotBit40 (outs40HwMaskTier1Sym96 c) 15 =
    wBit (envTier1Sym96 c) (outW t1aOut20 0) := by
  change (outs40HwMaskTier1Sym96 c).testBit 15 = _; rw [mr_hwMask_testBit_sym]; rfl
theorem mr_preCnot_hw_sym_1 (c : Fin (2 ^ 41)) : preCnotBit40 (outs40HwMaskTier1Sym96 c) 1 =
    wBit (envTier1Sym96 c) (outW t1aOut20 1) := by
  change (outs40HwMaskTier1Sym96 c).testBit 1 = _; rw [mr_hwMask_testBit_sym]; rfl
theorem mr_preCnot_hw_sym_33 (c : Fin (2 ^ 41)) : preCnotBit40 (outs40HwMaskTier1Sym96 c) 33 =
    wBit (envTier1Sym96 c) isPotT1aW := by
  change (outs40HwMaskTier1Sym96 c).testBit 33 = _; rw [mr_hwMask_testBit_sym]; rfl
theorem mr_preCnot_hw_sym_14 (c : Fin (2 ^ 41)) : preCnotBit40 (outs40HwMaskTier1Sym96 c) 14 =
    xor (wBit (envTier1Sym96 c) isPotT1aW) (wBit (envTier1Sym96 c) (outW t1aOut21 0)) := by
  change (outs40HwMaskTier1Sym96 c).testBit 14 = _
  rw [mr_hwMask_testBit_sym, show outW symOuts40Tier1Sym96 14 =
      Nat.xor isPotT1aW (outW t1aOut21 0) from rfl, mr_revT1_wBit_xor]
theorem mr_preCnot_hw_sym_0 (c : Fin (2 ^ 41)) : preCnotBit40 (outs40HwMaskTier1Sym96 c) 0 =
    xor (wBit (envTier1Sym96 c) isPotT1aW) (wBit (envTier1Sym96 c) (outW t1aOut21 1)) := by
  change (outs40HwMaskTier1Sym96 c).testBit 0 = _
  rw [mr_hwMask_testBit_sym, show outW symOuts40Tier1Sym96 0 =
      Nat.xor isPotT1aW (outW t1aOut21 1) from rfl, mr_revT1_wBit_xor]

abbrev mr_tPredHwSym (c : Fin (2 ^ 41)) : ℕ → Bool :=
    tailPredBit 143 revCoreGatesSym96 c (outs40HwMaskTier1Sym96 c)
abbrev mr_mPredHwSym (c : Fin (2 ^ 41)) : ℕ → Bool :=
    midPredBit 143 revCoreGatesSym96 coreMask0Sym96 coreMask1Sym96 c
    (outs40HwMaskTier1Sym96 c)
def mr_hiIdx_sym : ℕ → ℕ | 0 => 15 | 1 => 1 | 2 => 33 | 3 => 14 | _ => 0
theorem mr_ifNeg_sym {p : Prop} [Decidable p] {t e : Bool} (h : ¬p) :
    (if p then t else e) = e := by simp only [h, ↓reduceIte]
theorem mr_mpHi_sym (g : Fin 143 → ℕ × ℕ) (m0 m1 : ℕ) (c : Fin (2 ^ 41)) (m40 i : ℕ)
    (hi : i < 5) : midPredBit 143 g m0 m1 c m40 (185 + i) = preCnotBit40 m40 (mr_hiIdx_sym i) ∧
    tailPredBit 143 g c m40 (185 + i) = preCnotBit40 m40 (mr_hiIdx_sym i) := by
  have hb : Nat.ble ((185 + i) + 1) (42 + 143) = false :=
    Bool.eq_false_iff.mpr fun h ↦ by have := Nat.le_of_ble_eq_true h; omega
  have ne {a b : ℕ} (h : a ≠ b) : (a == b) = false := beq_eq_false_iff_ne.mpr h
  have h13 : (185 + i == 47 + 143) = false := ne (by omega)
  have h14 : (185 + i == 48 + 143) = false := ne (by omega)
  dsimp only [midPredBit, tailPredBit] at hb h13 h14 ⊢;
  simp only [hb, h13, h14, Bool.false_eq_true, ↓reduceIte]
  rcases i with _ | _ | _ | _ | _ | i <;> try omega
  all_goals
    repeat rw [mr_ifNeg_sym (by rw [ne (by omega)]; exact Bool.noConfusion)]
    dsimp only [mr_hiIdx_sym]; simp only [beq_self_eq_true, ↓reduceIte]; exact ⟨trivial, trivial⟩

theorem mr_tPredHwSym_0 (c : Fin (2 ^ 41)) : mr_tPredHwSym c 0 = true :=
    tailPredBit_zero 143 revCoreGatesSym96 c (outs40HwMaskTier1Sym96 c)
theorem mr_tPredHwSym_186 (c : Fin (2 ^ 41)) : mr_tPredHwSym c 185 = wBit (envTier1Sym96 c)
    (outW t1aOut20 0) :=
    ((mr_mpHi_sym revCoreGatesSym96 0 0 c _ 0 (by omega)).2).trans (mr_preCnot_hw_sym_15 c)
theorem mr_tPredHwSym_187 (c : Fin (2 ^ 41)) : mr_tPredHwSym c 186 = wBit (envTier1Sym96 c)
    (outW t1aOut20 1) :=
    ((mr_mpHi_sym revCoreGatesSym96 0 0 c _ 1 (by omega)).2).trans (mr_preCnot_hw_sym_1 c)
theorem mr_tPredHwSym_188 (c : Fin (2 ^ 41)) : mr_tPredHwSym c 187 =
    wBit (envTier1Sym96 c) isPotT1aW :=
    ((mr_mpHi_sym revCoreGatesSym96 0 0 c _ 2 (by omega)).2).trans (mr_preCnot_hw_sym_33 c)
theorem mr_mPredHwSym_186 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 185 = wBit (envTier1Sym96 c)
    (outW t1aOut20 0) :=
    ((mr_mpHi_sym revCoreGatesSym96 _ _ c _ 0 (by omega)).1).trans (mr_preCnot_hw_sym_15 c)
theorem mr_mPredHwSym_187 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 186 = wBit (envTier1Sym96 c)
    (outW t1aOut20 1) :=
    ((mr_mpHi_sym revCoreGatesSym96 _ _ c _ 1 (by omega)).1).trans (mr_preCnot_hw_sym_1 c)
theorem mr_mPredHwSym_188 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 187 =
    wBit (envTier1Sym96 c) isPotT1aW :=
    ((mr_mpHi_sym revCoreGatesSym96 _ _ c _ 2 (by omega)).1).trans (mr_preCnot_hw_sym_33 c)
theorem mr_mPredHwSym_189 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 188 =
    xor (wBit (envTier1Sym96 c) isPotT1aW) (wBit (envTier1Sym96 c) (outW t1aOut21 0)) :=
  ((mr_mpHi_sym revCoreGatesSym96 _ _ c _ 3 (by omega)).1).trans (mr_preCnot_hw_sym_14 c)
theorem mr_mPredHwSym_190 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 189 =
    xor (wBit (envTier1Sym96 c) isPotT1aW) (wBit (envTier1Sym96 c) (outW t1aOut21 1)) :=
  ((mr_mpHi_sym revCoreGatesSym96 _ _ c _ 4 (by omega)).1).trans (mr_preCnot_hw_sym_0 c)
theorem mr_mPredHwSym_191 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 190 = (wBit (envTier1Sym96 c)
    (outW t1aOut20 0) && Bool.not (wBit (envTier1Sym96 c) (outW t1aOut10 0)))
    := by dsimp only [mr_mPredHwSym]; rw [mr_midPredBit_tmp0_t1a, mr_preCnot_hw_sym_15]
theorem mr_mPredHwSym_192 (c : Fin (2 ^ 41)) : mr_mPredHwSym c 191 = (wBit (envTier1Sym96 c)
    (outW t1aOut20 1) && Bool.not (wBit (envTier1Sym96 c) (outW t1aOut08 0)))
    := by dsimp only [mr_mPredHwSym]; rw [mr_midPredBit_tmp1_t1a, mr_preCnot_hw_sym_1]
theorem mr_listXor_mPredHwSym_190_188 (c : Fin (2 ^ 41)) : listXorBool (mr_mPredHwSym c)
    [189, 187] = wBit (envTier1Sym96 c) (outW t1aOut21 1) := by
  rw [mr_listXor_two_t1, mr_mPredHwSym_190 c, mr_mPredHwSym_188 c, mr_xor_cancel_left_t1]
theorem mr_listXor_mPredHwSym_189_188 (c : Fin (2 ^ 41)) : listXorBool (mr_mPredHwSym c)
    [188, 187] = wBit (envTier1Sym96 c) (outW t1aOut21 0) := by
  rw [mr_listXor_two_t1, mr_mPredHwSym_189 c, mr_mPredHwSym_188 c, mr_xor_cancel_left_t1]
theorem mr_wBit_rev144_in20 (c : Fin (2 ^ 41)) (i : ℕ) : wBit (envTier1Sym96Rev144 c)
    (outW t1aIn20 i) = bitAt (wPack (envTier1Sym96 c) t1aIn20) i := by
  have hEq : wPack (envTier1Sym96Rev144 c) t1aIn20 = wPack (envTier1Sym96 c) t1aIn20 :=
      wPack_rev144_t1aRevIn20 c; rw [mr_revT1_wBit_outW, hEq, ← bitAt_eq_testBit]
theorem mr_wBit_rev144_revOut20 (c : Fin (2 ^ 41)) (k : ℕ) : wBit (envTier1Sym96Rev144 c)
    (outW t1aRevOut20 k) = (specT1aRev20 (wPack (envTier1Sym96 c) t1aIn20)).testBit k := by
  rw [mr_revT1_wBit_outW, wPack_t1aRevOut20 c]
theorem mr_revSym_cert_tail012 :
    allTree 12 0 2048 (fun r ↦
      Bool.or (Bool.not (careTier1_20 r))
        (let s20 := specTier1_20 r
         let sr := specT1aRev20 r
         let b16sr := xor (bitAt r 6) (xor (sr.testBit 1) (xor (sr.testBit 2) (sr.testBit 3)))
         let sr12 := xor (sr.testBit 1) (sr.testBit 2)
         let c0 :=
             BEq.beq (xor (Bool.and (Bool.not (xor (bitAt r 7) (xor (bitAt r 8) (bitAt r 9))))
             (bitAt r 0)) (xor (Bool.and (bitAt r 1) b16sr) (xor (Bool.and (bitAt r 0) sr12)
             (Bool.and (xor (bitAt r 10) (xor (bitAt r 5) (sr.testBit 0))) (sr.testBit 2)))))
             (s20.testBit 0)
         let c1 :=
             BEq.beq (xor (Bool.and (bitAt r 2) sr12) (Bool.and (bitAt r 3) b16sr)) (s20.testBit 1)
         let c2 :=
             BEq.beq (xor (xor (s20.testBit 1) (s20.testBit 0))
             (xor (xor (bitAt r 0) (xor (bitAt r 2) (xor (bitAt r 4) sr12)))
             (xor (Bool.and (Bool.not (bitAt r 7)) (xor (bitAt r 2) (xor (bitAt r 4)
             (xor (bitAt r 6) (sr.testBit 3)))))
             (xor (Bool.and (xor (bitAt r 0) (xor (bitAt r 2) (bitAt r 4))) (xor (bitAt r 6)
             (sr.testBit 3))) (Bool.and (bitAt r 5) b16sr)))))
             (xor (xor (s20.testBit 0) (s20.testBit 1)) (s20.testBit 2))
         Bool.and c0 (Bool.and c1 c2))) = true := by
  decide +kernel

theorem mr_revSym_cert_tail34 :
    allTree 12 0 2048 (fun r ↦
      Bool.or (Bool.not (careT1a_21 r))
        (let s21 := specT1a_21 r
         let c3 :=
             BEq.beq (xor (Bool.and (Bool.not (bitAt r 0)) (Bool.not (bitAt r 1)))
             (Bool.and (bitAt r 3) (bitAt r 5))) (xor (bitAt r 2) (s21.testBit 0))
         let c4 :=
             BEq.beq (xor (bitAt r 2) (Bool.and (bitAt r 8) (xor (bitAt r 9) (bitAt r 5))))
             (xor (bitAt r 2) (s21.testBit 1))
         Bool.and c3 c4)) = true := by
  decide +kernel

theorem mr_evalBilinearBool_tailTermsSym_hw (c : Fin (2 ^ 41))
    (s : Fin 5) : xor (tailPreXSym96 s) (evalBilinearBool (mr_tPredHwSym c)
    (tailTermsSym96 s)) = preCnotBit40 (outs40HwMaskTier1Sym96 c) (tail5OutIdx s) := by
  have h012 :=
      allTree_zero mr_revSym_cert_tail012 (wPack_lt_pow (envTier1Sym96 c) t1aIn20);
      rw [mEv_care_in20 c, Bool.not_true, Bool.false_or,
      ← mr_eval_out20_sym c] at h012; dsimp only at h012
  rcases Bool.and_eq_true_iff.mp h012 with ⟨hc0, h12⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hc1, hc2⟩
  have h34 :=
      allTree_zero mr_revSym_cert_tail34 (wPack_lt_pow (envTier1Sym96 c) t1aIn21);
      rw [mEv_care_in21 c, Bool.not_true, Bool.false_or, ← mr_eval_out21_sym c] at h34
  dsimp only at h34; rcases Bool.and_eq_true_iff.mp h34 with ⟨hc3, hc4⟩
  simp only [← mr_revT1_wBit_outW] at hc0 hc1 hc2 hc3 hc4;
  dsimp only [t1aIn21, isPotT1aW] at hc3 hc4;
  simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1] at hc3 hc4
  dsimp only [tailPreXSym96]; rw [Bool.false_xor]
  rcases s with ⟨v, hv⟩; rcases v with _ | _ | _ | _ | _ | v
  · rw [show tail5OutIdx ⟨0, hv⟩ = 15 from rfl, mr_preCnot_hw_sym_15 c]
    dsimp only [tailTermsSym96, tailTermsSym96At, cond, t1aXor3, t1aXor4];
    rw [t1a_evalBilinear_four_b0];
    simp only [mr_listXor_tail_rev_t1a, mr_revT1_wBit_xor, wBit_rev144_const1, t1a_true_xor,
        mr_wBit_rev144_in20, mr_wBit_rev144_revOut20]; exact beq_iff_eq.mp hc0
  · rw [show tail5OutIdx ⟨1, hv⟩ = 1 from rfl, mr_preCnot_hw_sym_1 c]
    dsimp only [tailTermsSym96, tailTermsSym96At, cond, t1aXor4];
    rw [mr_evalBilinear_two_b0_t1];
    simp only [mr_listXor_tail_rev_t1a, mr_revT1_wBit_xor, mr_wBit_rev144_in20,
        mr_wBit_rev144_revOut20]; exact beq_iff_eq.mp hc1
  · rw [show tail5OutIdx ⟨2, hv⟩ = 33 from rfl, mr_preCnot_hw_sym_33 c]
    dsimp only [tailTermsSym96, tailTermsSym96At, cond, t1aXor3, t1aXor4, t1aXor5];
    rw [t1a_evalBilinear_five_b0, mr_listXor_two_t1, mr_listXor_singleton_t1, mr_tPredHwSym_187 c,
        mr_tPredHwSym_186 c, mr_tPredHwSym_0 c, Bool.and_true,
        Bool.and_true]; simp only [mr_listXor_tail_rev_t1a, mr_revT1_wBit_xor, wBit_rev144_const1,
        t1a_true_xor, mr_wBit_rev144_in20, mr_wBit_rev144_revOut20]
    dsimp only [isPotT1aW]; rw [mr_revT1_wBit_xor, mr_revT1_wBit_xor]
    exact beq_iff_eq.mp hc2
  · rw [show tail5OutIdx ⟨3, hv⟩ = 14 from rfl, mr_preCnot_hw_sym_14 c]
    dsimp only [tailTermsSym96, tailTermsSym96At, cond]
    rw [mr_evalBilinear_two_b0_t1,
        mr_listXor_tail_fwd_t1a c _ _ (by decide +kernel),
        mr_listXor_tail_fwd_t1a c _ _ (by decide +kernel),
        mr_listXor_tail_fwd_t1a c _ _ (by decide +kernel),
        mr_listXor_tail_fwd_t1a c _ _ (by decide +kernel),
        mr_revT1a_wBit_not1, mr_revT1a_wBit_not1]
    dsimp only [isPotT1aW]; simp only [mr_revT1_wBit_xor] at hc3 ⊢
    exact beq_iff_eq.mp hc3
  · rw [show tail5OutIdx ⟨4, hv⟩ = 0 from rfl, mr_preCnot_hw_sym_0 c]
    dsimp only [tailTermsSym96, tailTermsSym96At, cond]
    rw [mr_evalBilinear_two_b0_t1,
        mr_listXor_singleton_t1, mr_listXor_singleton_t1,
        mr_tPredHwSym_188 c, mr_tPredHwSym_0 c, Bool.and_true,
        mr_listXor_tail_fwd_t1a c _ _ (by decide +kernel),
        mr_listXor_tail_fwd_t1a c _ _ (by decide +kernel),
        mr_revT1_wBit_xor]
    dsimp only [isPotT1aW]; simp only [mr_revT1_wBit_xor] at hc4 ⊢; exact beq_iff_eq.mp hc4
  · omega

theorem evalBilinearBool_tailTermsSym96_of_xag
    (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (hXag : ∀ (c : Fin (2 ^ 41)) (j : Fin 40),
      oddBits (xagEnv c.val 209 gatesTier1Sym96 209 le_rfl &&& outs40Tier1Sym96 j)
          (42 + 209) =
        (zeroNEremOutMask (decode c)).testBit j.val)
    (c : Fin (2 ^ 41)) (s : Fin 5) :
    let m40 := zeroNEremOutMask (decode c)
    xor (tailPreXSym96 s)
      (evalBilinearBool (tailPredBit 143 revCoreGatesSym96 c m40) (tailTermsSym96 s)) =
      preCnotBit40 m40 (tail5OutIdx s) := by
  have hm : ∀ k : Fin 40, (zeroNEremOutMask (decode c)).testBit k.val =
      (outs40HwMaskTier1Sym96 c).testBit k.val := fun k ↦
      (mr_outs40HwMaskSym_testBit_eq_of_xag decode hXag c k).symm
  dsimp only;
  rw [tailPredBit_congr_m40T1 143 revCoreGatesSym96 c hm,
      preCnotBit40_congrT1 hm (tail5OutIdx_lt40 s)]; exact mr_evalBilinearBool_tailTermsSym_hw c s
theorem mr_preCnot_hw_sym_e2 (c : Fin (2 ^ 41)) (i : ℕ)
    (hi : i < 8) : preCnotBit40 (outs40HwMaskTier1Sym96 c) (24 + i) = wBit (envTier1Sym96 c)
    (e2T1aW i) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first
      | omega
      | (change (outs40HwMaskTier1Sym96 c).testBit _ = _; rw [mr_hwMask_testBit_sym]; rfl)
theorem mr_preCnot_hw_sym_e12 (c : Fin (2 ^ 41)) (i : ℕ)
    (hi : i < 8) : preCnotBit40 (outs40HwMaskTier1Sym96 c)
    (16 + i) = xor (wBit (envTier1Sym96 c) (e1T1aW i)) (wBit (envTier1Sym96 c) (e2T1aW i))
    := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first
      | omega
      | (change xor ((outs40HwMaskTier1Sym96 c).testBit _)
            ((outs40HwMaskTier1Sym96 c).testBit _) = _; rw [mr_hwMask_testBit_sym,
            mr_hwMask_testBit_sym]; rfl)
theorem mr_preCnot_hw_sym_n2 (c : Fin (2 ^ 41)) (i : ℕ)
    (hi : i < 6) : preCnotBit40 (outs40HwMaskTier1Sym96 c) (8 + i) = wBit (envTier1Sym96 c)
    (n2T1aW i) := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;>
    first
      | omega
      | (change (outs40HwMaskTier1Sym96 c).testBit _ = _; rw [mr_hwMask_testBit_sym]; rfl)
theorem mr_preCnot_hw_sym_n12 (c : Fin (2 ^ 41)) (i : ℕ)
    (hi : i < 6) : preCnotBit40 (outs40HwMaskTier1Sym96 c)
    (2 + i) = xor (wBit (envTier1Sym96 c) (n1T1aW i)) (wBit (envTier1Sym96 c) (n2T1aW i))
    := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;>
    first
      | omega
      | (change xor ((outs40HwMaskTier1Sym96 c).testBit _)
            ((outs40HwMaskTier1Sym96 c).testBit _) = _; rw [mr_hwMask_testBit_sym,
            mr_hwMask_testBit_sym]; rfl)
theorem mr_preCnot_hw_sym_sp1 (c : Fin (2 ^ 41)) (k : ℕ)
    (hk : k < 2) : preCnotBit40 (outs40HwMaskTier1Sym96 c) (36 + k) = wBit (envTier1Sym96 c)
    (outW t1aOut24 (5 + k)) := by
  rcases k with _ | _ | k <;>
    first
      | omega
      | (change (outs40HwMaskTier1Sym96 c).testBit _ = _; rw [mr_hwMask_testBit_sym]; rfl)
theorem mr_preCnot_hw_sym_aux2 (c : Fin (2 ^ 41)) (k : ℕ)
    (hk : k < 2) : preCnotBit40 (outs40HwMaskTier1Sym96 c) (38 + k) = wBit (envTier1Sym96 c)
    (aux2T1aW k) := by
  rcases k with _ | _ | k <;>
    first
      | omega
      | (change (outs40HwMaskTier1Sym96 c).testBit _ = _; rw [mr_hwMask_testBit_sym]; rfl)

theorem mr_tb_cond_sym (b : Bool) (x y i : ℕ) :
    (cond b x y).testBit i = cond b (x.testBit i) (y.testBit i) := by
  cases b <;> rfl
theorem mr_tb0_sw_sym (b : Bool) (z : ℕ) : (cond b 1 0 + 2 ^ 1 * z).testBit 0 = b := by
  rw [← b2_testBit_mod_pow _ 1 0 (by omega), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by cases b <;> decide)]
  cases b <;> rfl
theorem mr_pack144_sym (a b c : ℕ) : a + 2 * b + 32 * c = a + 2 ^ 1 * (b + 2 ^ 4 * c) := by omega
theorem mr_pack12222_sym (a b c d e : ℕ) :
    a + 2 * b + 8 * c + 32 * d + 128 * e =
      a + 2 ^ 1 * (b + 2 ^ 2 * (c + 2 ^ 2 * (d + 2 ^ 2 * e))) := by omega
theorem mr_f26_bit_sym (r q : ℕ) : (specTier1_26 r).testBit q = Bool.and (bitAt r 0)
    (bitAt r (1 + q)) := by
  dsimp only [specTier1_26]
  rw [mr_tb_cond_sym, Nat.zero_testBit, show r / 2 = r / 2 ^ 1 from rfl,
      Nat.testBit_div_two_pow, Nat.add_comm q 1, ← bitAt_eq_testBit]
  cases bitAt r 0 <;> rfl
theorem mr_eval_sw22_sym (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (outW t1aOut22 0) = mr_mPredHwSym c 190 := by
  rw [mr_revT1_wBit_outW, mr_eval_out22_sym c, mr_mPredHwSym_191 c]
  dsimp only [specTier1_22, t1aIn22]; rw [mr_pack144_sym, mr_tb0_sw_sym]
  simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1, mr_revT1_wBit_outW]

theorem mr_eval_sw24_sym (c : Fin (2 ^ 41)) : wBit (envTier1Sym96 c)
    (outW t1aOut24 0) = mr_mPredHwSym c 191 := by
  rw [mr_revT1_wBit_outW, mr_eval_out24_sym c, mr_mPredHwSym_192 c]
  dsimp only [specTier1_24, t1aIn24]; rw [mr_pack12222_sym, mr_tb0_sw_sym]
  simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1, mr_revT1_wBit_outW]

theorem mr_eval_f26_naKn_sym (c : Fin (2 ^ 41)) (i : ℕ)
    (hi : i < 6) : Bool.and (wBit (envTier1Sym96 c) (outW t1aOut21 1)) (wBit (envTier1Sym96 c)
    (mr_naKnT1aW i)) = wBit (envTier1Sym96 c) (outW t1aOut26 i) := by
  rw [mr_revT1_wBit_outW (ms := t1aOut26), wPack_t1aOut26 c, mr_f26_bit_sym, bitAt_eq_testBit,
      bitAt_eq_testBit]
  have hb0 : (wPack (envTier1Sym96 c) t1aIn26).testBit 0 = wBit (envTier1Sym96 c)
      (outW t1aOut21 1) := by dsimp only [t1aIn26]; rw [mr_wPack_cons_zero_t1]
  rw [hb0]
  cases hDo : mEvDoKn c
  · rw [mEv_doKn_bit21 c, hDo, Bool.false_and, Bool.false_and]
  · rcases mEv_base26_zero_of_doKn c hDo with ⟨h24, h25, _, _⟩
    have h24b (q : ℕ) : wBit (envTier1Sym96 c) (outW t1aOut24 q) = false := by
      rw [mr_revT1_wBit_outW, h24, Nat.zero_testBit]
    have h25b (q : ℕ) : wBit (envTier1Sym96 c) (outW t1aOut25 q) = false := by
      rw [mr_revT1_wBit_outW, h25, Nat.zero_testBit]
    rcases i with _ | _ | _ | _ | _ | _ | i <;>
      first
        | omega
        | (dsimp only [t1aIn26, mr_naKnT1aW]; simp only [mr_wPack_cons_succ_t1,
              mr_wPack_cons_zero_t1, mr_revT1_wBit_xor, h24b, h25b, Bool.xor_false])

theorem mr_eval_f26_sp2_sym (c : Fin (2 ^ 41)) (k : ℕ)
    (hk : k < 2) : Bool.and (wBit (envTier1Sym96 c) (outW t1aOut21 1)) (wBit (envTier1Sym96 c)
    (coinW (23 + k))) = wBit (envTier1Sym96 c) (outW t1aOut26 (6 + k)) := by
  rw [mr_revT1_wBit_outW (ms := t1aOut26), wPack_t1aOut26 c, mr_f26_bit_sym, bitAt_eq_testBit,
      bitAt_eq_testBit]
  have hb0 : (wPack (envTier1Sym96 c) t1aIn26).testBit 0 = wBit (envTier1Sym96 c)
      (outW t1aOut21 1) := by dsimp only [t1aIn26]; rw [mr_wPack_cons_zero_t1]
  rw [hb0]
  cases hDo : mEvDoKn c
  · rw [mEv_doKn_bit21 c, hDo, Bool.false_and, Bool.false_and]
  · rcases mEv_base26_zero_of_doKn c hDo with ⟨h24, _, h21_2, h21_3⟩
    have h24b (q : ℕ) : wBit (envTier1Sym96 c) (outW t1aOut24 q) = false := by
      rw [mr_revT1_wBit_outW, h24, Nat.zero_testBit]
    rcases k with _ | _ | k <;>
      first
        | omega
        | (dsimp only [t1aIn26]; simp only [mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1,
              mr_revT1_wBit_xor, h24b, h21_2, h21_3, Bool.xor_false])

private def okMidMaskB (m : ℕ) : Bool := Nat.blt m (1 <<< (42 + 139))

private abbrev mid_fwd_hw (c : Fin (2 ^ 41)) {m40 m : ℕ} (h : okMidMaskB m = true) :=
  mr_listXor_mid_fwd_t1a c m40 m h

private theorem okMidE_masks {d : ℕ} (hd : d < 8) :
    okMidMaskB (outW t1aOut04 d) = true ∧
    okMidMaskB (outW t1aOut06 (9 + d)) = true ∧
    okMidMaskB (Nat.xor (outW t1aOut04 d) (outW t1aOut06 (9 + d))) = true :=
  (by decide +kernel : ∀ k : Fin 8, okMidMaskB (outW t1aOut04 k.val) = true ∧
    okMidMaskB (outW t1aOut06 (9 + k.val)) = true ∧
    okMidMaskB (Nat.xor (outW t1aOut04 k.val) (outW t1aOut06 (9 + k.val))) = true) ⟨d, hd⟩
private theorem okMidN_masks {d : ℕ} (hd : d < 6) :
    okMidMaskB (outW t1aOut05 (3 + d)) = true ∧
    okMidMaskB (outW t1aOut06 (3 + d)) = true ∧
    okMidMaskB (Nat.xor (outW t1aOut05 (3 + d)) (outW t1aOut06 (3 + d))) = true ∧
    okMidMaskB (mr_naKnT1aW d) = true :=
  (by decide +kernel : ∀ k : Fin 6, okMidMaskB (outW t1aOut05 (3 + k.val)) = true ∧
    okMidMaskB (outW t1aOut06 (3 + k.val)) = true ∧
    okMidMaskB (Nat.xor (outW t1aOut05 (3 + k.val)) (outW t1aOut06 (3 + k.val))) = true ∧
    okMidMaskB (mr_naKnT1aW k.val) = true) ⟨d, hd⟩
private theorem okMidAux_masks {d : ℕ} (hd : d < 2) :
    okMidMaskB (outW t1aOut05 (1 + d)) = true ∧
    okMidMaskB (outW t1aOut06 (1 + d)) = true ∧
    okMidMaskB (Nat.xor (outW t1aOut05 (1 + d)) (outW t1aOut06 (1 + d))) = true ∧
    okMidMaskB (coinW (23 + d)) = true ∧
    okMidMaskB (outW tier1Out02 (5 + d)) = true ∧
    okMidMaskB (outW t1aOut14 d) = true ∧
    okMidMaskB (outW t1aOut18 0) = true :=
  (by decide +kernel : ∀ k : Fin 2, okMidMaskB (outW t1aOut05 (1 + k.val)) = true ∧
    okMidMaskB (outW t1aOut06 (1 + k.val)) = true ∧
    okMidMaskB (Nat.xor (outW t1aOut05 (1 + k.val)) (outW t1aOut06 (1 + k.val))) = true ∧
    okMidMaskB (coinW (23 + k.val)) = true ∧ okMidMaskB (outW tier1Out02 (5 + k.val)) = true ∧
    okMidMaskB (outW t1aOut14 k.val) = true ∧ okMidMaskB (outW t1aOut18 0) = true) ⟨d, hd⟩
theorem mr_eval_mid_e_all_sym (c : Fin (2 ^ 41)) (d : ℕ) (hd : d < 8) :
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At d) =
      wBit (envTier1Sym96 c) (e2T1aW d) ∧
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (8 + d)) =
      xor (wBit (envTier1Sym96 c) (e1T1aW d)) (wBit (envTier1Sym96 c) (e2T1aW d)) := by
  obtain ⟨ok04, ok06, ok46⟩ := okMidE_masks (d := d) hd
  unfold midTermsSym96At
  rw [Nat.blt_eq.mpr hd, (blt_eq_false_iff (8 + d) 8).mpr (by omega),
      Nat.blt_eq.mpr (show 8 + d < 16 by omega)]
  dsimp only [cond]
  rw [Nat.add_sub_cancel_left]
  simp only [mr_evalBilinear_two_t1, mr_listXor_singleton_t1]
  rw [mr_mPredHwSym_189 c, mr_mPredHwSym_186 c, mid_fwd_hw c ok04, mid_fwd_hw c ok06,
      mid_fwd_hw c ok46, mr_revT1_wBit_xor]
  by_cases h4 : d < 4
  · have h22 := allTree_zero mr_revT1_cert_mid_f22 (wPack_lt_pow (envTier1Sym96 c) t1aIn22)
    rw [mr_care_in22_sym c, Bool.not_true, Bool.false_or] at h22
    obtain ⟨hb0, hb1, hb2, hb3⟩ := t1Ev_and4 (Bool.and_eq_true_iff.mp h22).2
    have hbi : mr_f22MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn22) d = true :=
      if h0 : d = 0 then h0 ▸ hb0 else if h1 : d = 1 then h1 ▸ hb1
      else if h2 : d = 2 then h2 ▸ hb2 else (by omega : d = 3) ▸ hb3
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl
    all_goals
      dsimp only [mr_f22MidBitOkT1] at hbi
      rw [← mr_eval_out22_sym c] at hbi
      simp only [← mr_revT1_wBit_outW] at hbi
      dsimp only [t1aIn22] at hbi
      simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1] at hbi
      rw [mr_eval_sw22_sym c,
          show Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2) =
            isPotT1aW from rfl, mr_revT1_wBit_xor] at hbi
      obtain ⟨he2, he12⟩ := Bool.and_eq_true_iff.mp hbi
      dsimp only [e1T1aW, e2T1aW, cond, Nat.blt]
      exact ⟨beq_iff_eq.mp he2, beq_iff_eq.mp he12⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = 4 + k := ⟨d - 4, by omega⟩
    have h23 := allTree_zero mr_revT1_cert_mid_f23 (wPack_lt_pow (envTier1Sym96 c) t1aIn23)
    rw [mr_care_in23_sym c, Bool.not_true, Bool.false_or] at h23
    obtain ⟨hb0, hb1, hb2, hb3⟩ := t1Ev_and4 h23
    have hbd : mr_f23MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn23) k = true :=
      if h0 : k = 0 then h0 ▸ hb0 else if h1 : k = 1 then h1 ▸ hb1
      else if h2 : k = 2 then h2 ▸ hb2 else (by omega : k = 3) ▸ hb3
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    all_goals
      dsimp only [mr_f23MidBitOkT1] at hbd
      rw [← mr_eval_out23_sym c] at hbd
      simp only [← mr_revT1_wBit_outW] at hbd
      dsimp only [t1aIn23] at hbd
      simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1] at hbd
      rw [mr_eval_sw22_sym c,
          show Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2) =
            isPotT1aW from rfl, mr_revT1_wBit_xor] at hbd
      obtain ⟨he2, he12⟩ := Bool.and_eq_true_iff.mp hbd
      dsimp only [e1T1aW, e2T1aW, cond, Nat.blt]
      exact ⟨beq_iff_eq.mp he2, beq_iff_eq.mp he12⟩
theorem mr_f24_ok_w5 (c : Fin (2 ^ 41)) :
    mr_f24MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn24) 0 = true ∧
    mr_f24MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn24) 1 = true := by
  have h := allTree_zero mr_revT1_cert_mid_f24 (wPack_lt_pow (envTier1Sym96 c) t1aIn24)
  rw [mr_care_in24_sym c, Bool.not_true, Bool.false_or] at h
  exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2
theorem mr_eval_mid_n_all_sym (c : Fin (2 ^ 41)) (d : ℕ) (hd : d < 6) :
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (16 + d)) =
      wBit (envTier1Sym96 c) (n2T1aW d) ∧
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (22 + d)) =
      xor (wBit (envTier1Sym96 c) (n1T1aW d)) (wBit (envTier1Sym96 c) (n2T1aW d)) := by
  obtain ⟨ok05, ok06, ok56, okNa⟩ := okMidN_masks (d := d) hd
  have h26 := mr_eval_f26_naKn_sym c d hd
  unfold midTermsSym96At
  rw [(blt_eq_false_iff (16 + d) 8).mpr (by omega),
      (blt_eq_false_iff (16 + d) 16).mpr (by omega),
      Nat.blt_eq.mpr (show 16 + d < 22 by omega),
      (blt_eq_false_iff (22 + d) 8).mpr (by omega),
      (blt_eq_false_iff (22 + d) 16).mpr (by omega),
      (blt_eq_false_iff (22 + d) 22).mpr (by omega),
      Nat.blt_eq.mpr (show 22 + d < 28 by omega)]
  dsimp only [cond]
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  simp only [mr_evalBilinear_two_t1, mr_evalBilinear_three_t1, mr_listXor_singleton_t1]
  rw [mr_mPredHwSym_188 c, mr_mPredHwSym_187 c, mr_listXor_mPredHwSym_190_188 c,
      mid_fwd_hw c ok05, mid_fwd_hw c ok06, mid_fwd_hw c ok56, mid_fwd_hw c okNa,
      mr_revT1_wBit_xor, h26]
  by_cases h2 : d < 2
  · obtain ⟨hb0, hb1⟩ := mr_f24_ok_w5 c
    have hbi : mr_f24MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn24) d = true :=
      if h0 : d = 0 then h0 ▸ hb0 else (by omega : d = 1) ▸ hb1
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    all_goals
      dsimp only [mr_f24MidBitOkT1] at hbi
      rw [← mr_eval_out24_sym c] at hbi
      simp only [← mr_revT1_wBit_outW] at hbi
      dsimp only [t1aIn24] at hbi
      simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1] at hbi
      rw [mr_eval_sw24_sym c,
          show Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2) =
            isPotT1aW from rfl] at hbi
      obtain ⟨hn2, hn12, _, _⟩ := t1Ev_and4 hbi
      dsimp only [n1T1aW, n2T1aW, cond, Nat.blt]
      rw [beq_iff_eq.mp hn2, beq_iff_eq.mp hn12, mr_revT1_wBit_xor, mr_xor_mid_swap_t1]
      exact ⟨rfl, rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 + k := ⟨d - 2, by omega⟩
    have h25 := allTree_zero mr_revT1_cert_mid_f25 (wPack_lt_pow (envTier1Sym96 c) t1aIn25)
    rw [mr_care_in25_sym c, Bool.not_true, Bool.false_or] at h25
    obtain ⟨hb0, hb1, hb2, hb3⟩ := t1Ev_and4 h25
    have hbd : mr_f25MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn25) k = true :=
      if h0 : k = 0 then h0 ▸ hb0 else if h1 : k = 1 then h1 ▸ hb1
      else if h2 : k = 2 then h2 ▸ hb2 else (by omega : k = 3) ▸ hb3
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    all_goals
      dsimp only [mr_f25MidBitOkT1] at hbd
      rw [← mr_eval_out25_sym c] at hbd
      simp only [← mr_revT1_wBit_outW] at hbd
      dsimp only [t1aIn25] at hbd
      simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1] at hbd
      rw [mr_eval_sw24_sym c,
          show Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2) =
            isPotT1aW from rfl] at hbd
      obtain ⟨hn2, hn12⟩ := Bool.and_eq_true_iff.mp hbd
      dsimp only [n1T1aW, n2T1aW, cond, Nat.blt]
      rw [beq_iff_eq.mp hn2, beq_iff_eq.mp hn12, mr_revT1_wBit_xor, mr_xor_mid_swap_t1]
      exact ⟨rfl, rfl⟩
theorem mr_f24_sp_w5 (c : Fin (2 ^ 41)) (k : ℕ) (hk : k < 2) :
    xor (Bool.and (wBit (envTier1Sym96 c) isPotT1aW)
          (wBit (envTier1Sym96 c) (outW t1aOut05 (1 + k))))
        (Bool.and (mr_mPredHwSym c 191)
          (xor (wBit (envTier1Sym96 c) (outW t1aOut05 (1 + k)))
            (wBit (envTier1Sym96 c) (outW t1aOut06 (1 + k))))) =
      wBit (envTier1Sym96 c) (outW t1aOut24 (5 + k)) ∧
    xor (Bool.and (wBit (envTier1Sym96 c) (outW t1aOut20 1))
          (wBit (envTier1Sym96 c) (outW t1aOut06 (1 + k))))
        (Bool.and (mr_mPredHwSym c 191)
          (xor (wBit (envTier1Sym96 c) (outW t1aOut05 (1 + k)))
            (wBit (envTier1Sym96 c) (outW t1aOut06 (1 + k))))) =
      wBit (envTier1Sym96 c) (outW t1aOut24 (7 + k)) := by
  obtain ⟨hb0, hb1⟩ := mr_f24_ok_w5 c
  have hbk : mr_f24MidBitOkT1 (wPack (envTier1Sym96 c) t1aIn24) k = true :=
    if h0 : k = 0 then h0 ▸ hb0 else (by omega : k = 1) ▸ hb1
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  all_goals
    dsimp only [mr_f24MidBitOkT1] at hbk
    rw [← mr_eval_out24_sym c] at hbk
    simp only [← mr_revT1_wBit_outW] at hbk
    dsimp only [t1aIn24] at hbk
    simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1] at hbk
    rw [mr_eval_sw24_sym c,
        show Nat.xor (Nat.xor (outW t1aOut20 0) (outW t1aOut20 1)) (outW t1aOut20 2) =
          isPotT1aW from rfl] at hbk
    obtain ⟨_, _, hsp1, hsp2⟩ := t1Ev_and4 hbk
    exact ⟨beq_iff_eq.mp hsp1, beq_iff_eq.mp hsp2⟩
theorem mr_eval_mid_n_lo_sym (c : Fin (2 ^ 41)) (i : ℕ) (hi : i < 2) :
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (16 + i)) =
      wBit (envTier1Sym96 c) (n2T1aW i) ∧
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (22 + i)) =
      xor (wBit (envTier1Sym96 c) (n1T1aW i)) (wBit (envTier1Sym96 c) (n2T1aW i)) ∧
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (28 + i)) =
      wBit (envTier1Sym96 c) (outW t1aOut24 (5 + i)) := by
  obtain ⟨hn2, hn12⟩ := mr_eval_mid_n_all_sym c i (by omega)
  obtain ⟨hsp1, _⟩ := mr_f24_sp_w5 c i hi
  obtain ⟨okA05, _, okA56, _, _, _, _⟩ := okMidAux_masks (d := i) hi
  refine ⟨hn2, hn12, ?_⟩
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  all_goals
    dsimp only [midTermsSym96At, cond, Nat.blt, Nat.ble]
    rw [mr_evalBilinear_two_t1, mr_listXor_singleton_t1, mr_listXor_singleton_t1,
        mr_mPredHwSym_188 c, mid_fwd_hw c okA05, mid_fwd_hw c okA56, mr_revT1_wBit_xor]
    exact hsp1
theorem mr_revSym_cert_mid_f21 :
    allTree 12 0 2048 (fun r ↦ Bool.or (Bool.not (careT1a_21 r))
      (let s := specT1a_21 r
       Bool.and (BEq.beq (xor (Bool.and (s.testBit 0) (bitAt r 6)) (Bool.and (Bool.and (bitAt r 4)
           (bitAt r 6)) (bitAt r 5))) (s.testBit 2))
         (BEq.beq (xor (Bool.and (s.testBit 0) (bitAt r 7)) (Bool.and (Bool.and (bitAt r 4)
             (bitAt r 7)) (bitAt r 5))) (s.testBit 3)))) = true := by
  decide +kernel
theorem mr_sym_out14_12_eq (c : Fin (2 ^ 41)) :
    wBit (envTier1Sym96 c) (outW t1aOut14 0) =
      Bool.and (xor (wBit (envTier1Sym96 c) (outW t1aOut14 0)) (wBit (envTier1Sym96 c)
          (outW t1aOut14 1)))
        (wBit (envTier1Sym96 c) (outW tier1Out02 5)) ∧
    wBit (envTier1Sym96 c) (outW t1aOut14 1) =
      Bool.and (xor (wBit (envTier1Sym96 c) (outW t1aOut14 0)) (wBit (envTier1Sym96 c)
          (outW t1aOut14 1)))
        (wBit (envTier1Sym96 c) (outW tier1Out02 6)) := by
  have h14S := mEv_s14_struct c
  have hh1 : wPack (envTier1Sym96 c) [outW tier1Out02 5, outW tier1Out02 6] =
      (t1EvPx c).2.1 := by
    simpa [t1EvOutSlice] using (mEv_out02_slices c).2.1
  have hb5 : wBit (envTier1Sym96 c) (outW tier1Out02 5) = ((t1EvPx c).2.1).testBit 0 := by
    rw [← mr_wPack_cons_zero_t1 _ (outW tier1Out02 5) [outW tier1Out02 6], hh1]
  have hb6 : wBit (envTier1Sym96 c) (outW tier1Out02 6) = ((t1EvPx c).2.1).testBit 1 := by
    rw [← mr_wPack_cons_zero_t1 _ (outW tier1Out02 6)
        [], ← mr_wPack_cons_succ_t1 _ (outW tier1Out02 5) [outW tier1Out02 6] 0, hh1]
  rw [mEv_out14_props c 0 (by omega), mEv_out14_props c 1 (by omega), h14S.2.1, h14S.2.2.1, hb5,
      hb6]
  have hlt := (t1Ev_b2_props c).2.1
  rcases (show (t1EvPx c).2.1 = 0 ∨ (t1EvPx c).2.1 = 1 ∨ (t1EvPx c).2.1 =
      2 by omega) with h | h | h <;>
    rw [h] <;> cases (mEvB12 c).testBit 6 <;> decide
theorem mr_eval_mid_aux2_sym (c : Fin (2 ^ 41)) (k : ℕ) (hk : k < 2) :
    evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (30 + k)) =
      wBit (envTier1Sym96 c) (aux2T1aW k) := by
  have h21 := allTree_zero mr_revSym_cert_mid_f21 (wPack_lt_pow (envTier1Sym96 c) t1aIn21)
  rw [mEv_care_in21 c, Bool.not_true, Bool.false_or, ← mr_eval_out21_sym c] at h21
  dsimp only at h21
  simp only [← mr_revT1_wBit_outW] at h21
  dsimp only [t1aIn21] at h21
  simp only [bitAt_eq_testBit, mr_wPack_cons_succ_t1, mr_wPack_cons_zero_t1,
    mr_revT1_wBit_xor] at h21
  obtain ⟨h21_0, h21_1⟩ := Bool.and_eq_true_iff.mp h21
  obtain ⟨hs10, hs20⟩ := mr_sym_out14_12_eq c
  obtain ⟨_, ok06, ok56, okC, okT, ok14, ok18⟩ := okMidAux_masks (d := k) hk
  have h26 := mr_eval_f26_sp2_sym c k hk
  obtain ⟨_, hsp2⟩ := mr_f24_sp_w5 c k hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd] at hsp2
    dsimp only [midTermsSym96At, cond, Nat.blt, Nat.ble, Nat.beq, aux2T1aW]
    rw [mr_evalBilinear_five_t1, mr_listXor_singleton_t1, mr_listXor_singleton_t1,
        mr_mPredHwSym_187 c, mr_listXor_mPredHwSym_190_188 c, mr_listXor_mPredHwSym_189_188 c,
        mid_fwd_hw c ok06, mid_fwd_hw c ok56, mid_fwd_hw c okC,
        mid_fwd_hw c okT, mid_fwd_hw c ok14, mid_fwd_hw c ok18, mr_revT1_wBit_xor]
  · rw [hs10, h26, hsp2, beq_iff_eq.mp h21_0, mr_revT1_wBit_xor, mr_revT1_wBit_xor]
  · rw [hs20, h26, hsp2, beq_iff_eq.mp h21_1, mr_revT1_wBit_xor, mr_revT1_wBit_xor]
theorem mr_evalBilinearBool_midTermsSym_hw (c : Fin (2 ^ 41)) (j : Fin 32) :
    xor (midPreXSym96 j) (evalBilinearBool (mr_mPredHwSym c) (midTermsSym96 j)) =
      preCnotBit40 (outs40HwMaskTier1Sym96 c) (mid32OutIdx j) := by
  dsimp only [midPreXSym96, midTermsSym96]
  rw [Bool.false_xor]
  have hk := j.isLt
  have hs {a : ℕ} {b : Bool} (h : a ≤ j.val)
      (he : evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At (a + (j.val - a))) = b) :
      evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At j.val) = b :=
    (congrArg (fun x ↦ evalBilinearBool (mr_mPredHwSym c) (midTermsSym96At x))
      (Nat.add_sub_of_le h).symm).trans he
  rcases (by omega : j.val < 8 ∨ (8 ≤ j.val ∧ j.val < 16) ∨ (16 ≤ j.val ∧ j.val < 22) ∨
      (22 ≤ j.val ∧ j.val < 28) ∨ (28 ≤ j.val ∧ j.val < 30) ∨ 30 ≤ j.val) with
    h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h0
  · rw [mr_mid32OutIdx_lt8_t1 j h, mr_preCnot_hw_sym_e2 c j.val h]
    exact (mr_eval_mid_e_all_sym c j.val h).1
  · rw [mr_mid32OutIdx_8_16_t1 j h0 h1, mr_preCnot_hw_sym_e12 c (j.val - 8) (by omega)]
    exact hs h0 (mr_eval_mid_e_all_sym c (j.val - 8) (by omega)).2
  · rw [mr_mid32OutIdx_16_22_t1 j h0 h1, mr_preCnot_hw_sym_n2 c (j.val - 16) (by omega)]
    exact hs h0 (mr_eval_mid_n_all_sym c (j.val - 16) (by omega)).1
  · rw [mr_mid32OutIdx_22_28_t1 j h0 h1, mr_preCnot_hw_sym_n12 c (j.val - 22) (by omega)]
    exact hs h0 (mr_eval_mid_n_all_sym c (j.val - 22) (by omega)).2
  · rw [mr_mid32OutIdx_ge28_t1 j h0, show 8 + j.val = 36 + (j.val - 28) by omega,
        mr_preCnot_hw_sym_sp1 c (j.val - 28) (by omega)]
    exact hs h0 (mr_eval_mid_n_lo_sym c (j.val - 28) (by omega)).2.2
  · rw [mr_mid32OutIdx_ge28_t1 j (by omega), show 8 + j.val = 38 + (j.val - 30) by omega,
        mr_preCnot_hw_sym_aux2 c (j.val - 30) (by omega)]
    exact hs h0 (mr_eval_mid_aux2_sym c (j.val - 30) (by omega))
theorem evalBilinearBool_midTermsSym96_of_xag
    (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (hXag : ∀ (c : Fin (2 ^ 41)) (j : Fin 40),
      oddBits (xagEnv c.val 209 gatesTier1Sym96 209 le_rfl &&& outs40Tier1Sym96 j)
          (42 + 209) =
        (zeroNEremOutMask (decode c)).testBit j.val)
    (c : Fin (2 ^ 41)) (j : Fin 32) :
    let m40 := zeroNEremOutMask (decode c)
    xor (midPreXSym96 j)
      (evalBilinearBool (midPredBit 143 revCoreGatesSym96 coreMask0Sym96 coreMask1Sym96 c
          m40) (midTermsSym96 j)) =
      preCnotBit40 m40 (mid32OutIdx j) := by
  have hm : ∀ k : Fin 40, (zeroNEremOutMask (decode c)).testBit k.val =
      (outs40HwMaskTier1Sym96 c).testBit k.val :=
    fun k ↦ (mr_outs40HwMaskSym_testBit_eq_of_xag decode hXag c k).symm
  dsimp only
  rw [midPredBit_congr_m40T1 143 revCoreGatesSym96 coreMask0Sym96 coreMask1Sym96 c hm,
      preCnotBit40_congrT1 hm (mid32OutIdx_lt40 j)]
  exact mr_evalBilinearBool_midTermsSym_hw c j
theorem activeStack_rOuter41_sym (gLo wWork : ℕ) {mCoin : ℕ} (hm : 39 ≤ mCoin) (k : Fin 41) :
    ActiveOuterCoinStackOf gLo wWork mCoin (rOuter41Layout k) := by
  have := k.isLt
  have := val_rOuter41Layout k
  unfold ActiveOuterCoinStackOf
  omega
theorem activeStack_rOut40_sym (gLo : ℕ) {wWork : ℕ} (hw40 : 40 ≤ wWork) (mCoin : ℕ) (j : Fin 40) :
    ActiveOuterCoinStackOf gLo wWork mCoin (rOut40Layout j) := by
  have := j.isLt
  have := val_rOut40Layout j
  unfold ActiveOuterCoinStackOf
  omega
theorem activeStack_rScr_lt_sym (gLo : ℕ) {M wWork : ℕ} (hM12 : M + 12 ≤ wWork) (mCoin : ℕ)
    (k : Fin 1493) (hk : k.val < M + 5) :
    ActiveOuterCoinStackOf gLo wWork mCoin (rScrCompact1493 k) := by
  unfold ActiveOuterCoinStackOf
  rw [val_rScrCompact1493 k]
  split_ifs <;> omega
theorem evalBilinearBool_midTermsSym96_coin (c : Fin (2 ^ 41)) (j : Fin 32) :
    let m40 := zeroNEremOutMask (decodeTier1W11Opt1424Coin c)
    xor (midPreXSym96 j)
      (evalBilinearBool (midPredBit 143 revCoreGatesSym96 coreMask0Sym96 coreMask1Sym96 c
          m40) (midTermsSym96 j)) =
      preCnotBit40 m40 (mid32OutIdx j) :=
  evalBilinearBool_midTermsSym96_of_xag decodeTier1W11Opt1424Coin xag_tier1W11Opt1424_eval
      c j
theorem evalBilinearBool_tailTermsSym96_coin (c : Fin (2 ^ 41)) (s : Fin 5) :
    let m40 := zeroNEremOutMask (decodeTier1W11Opt1424Coin c)
    xor (tailPreXSym96 s) (evalBilinearBool (tailPredBit 143 revCoreGatesSym96 c m40)
        (tailTermsSym96 s)) =
      preCnotBit40 m40 (tail5OutIdx s) :=
  evalBilinearBool_tailTermsSym96_of_xag decodeTier1W11Opt1424Coin xag_tier1W11Opt1424_eval
      c s
end QuantumComputation.Specs.PhotochemistrySolution.Stage1WRouter1416
end


namespace QuantumComputation.Specs.PhotochemistrySolution.MidOW42ExactOpt

open Operator QProg DynamicCircuit Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast (dynWires_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu (subspaceStep_of_eq_post
    subspaceStep_seq_mbu)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
    (subspaceStep_circuit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd (finBitsVal
    finBitsVal_succ)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254 (cnot1 cnot1_counts
    cnot1_dynWires cnot1_step two_mul_mod_add)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore (zmod2_maj_id)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (zmod2_val_cast x1 cz2
    cz2_counts cz2_dynWires cz2_step w4_0 w4_1 w4_2 w4_3 cpMaj4 cpMaj4_numAnd stepCB_cpMaj4_not
    stepCB_cpMaj4_anc wrapCpMaj4 cpXorAnd4 cpXorAnd4_numAnd cpXorAnd4_valid8 stepCB_cpXorAnd4_not
    stepCB_cpXorAnd4_anc maj_div_pow_succ mask8_eq_w4_3 wrapStepMask)
open PrimitiveGate (T TOFF)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60
    (ctrl_finBitsVal_fin1_local)
open scoped Circuit.Notation
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP


/-! ### 1. Zero-Ancilla `4 T` Signed Toffoli (`cSignedToff`) & `4`-Wire Controlled 1-Bit Adder -/

/--
`3`-qubit `4 T` (`0` `.TOFF`, `0` ancilla) signed Toffoli:
maps `|β⟩ ↦ (-1)^(β c₁ * β c₂ * β t) |β[t ⊕= β c₁ * β c₂]⟩`.
-/
def cSignedToff {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) : Circuit n :=
  Circuit.S t ;;ᶜ Circuit.Z t ;;ᶜ CircExt.andCompute_loc c₁ c₂ t h₁₂ h₁t h₂t

theorem signedToff_Combine1 {n : ℕ} (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) :
    DynCircExt.gad_bitPhaseI 1 • (DynCircExt.gad_bitSign 1 • (DynCircExt.gad_sqrtHalf •
    (DynCircExt.gad_phase4T c₁ c₂ 0 • (DynCircExt.gad_sqrtHalf • (ψ₀ +
    DynCircExt.gad_bitPhaseI 1 • ψ₁)) +
    DynCircExt.gad_bitSign 1 • (DynCircExt.gad_phase4T c₁ c₂ 1 •
    (DynCircExt.gad_sqrtHalf • (ψ₀ +
    DynCircExt.gad_bitSign 1 • DynCircExt.gad_bitPhaseI 1 • ψ₁)))))) =
    DynCircExt.gad_bitSign (c₁ * c₂) • (if c₁ * c₂ = 0 then ψ₁ else ψ₀) := by
  rw [DynCircExt.gad_phase4T_eq c₁ c₂ 0, DynCircExt.gad_phase4T_eq c₁ c₂ 1]
  rcases DynCircExt.bit_cases (c₁ * c₂) with h | h <;>
    simp only [h, DynCircExt.gad_bitPhaseI, DynCircExt.gad_bitSign,
      one_ne_zero, ↓reduceIte, smul_add, smul_smul] <;>
    match_scalars <;>
    first
      | ring1
      | (ring_nf; simp only [DynCircExt.gad_sqrtHalf_sq, Complex.I_sq]; try ring1)

theorem ket_cSignedToff {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (cSignedToff c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (DynCircExt.ket β) =
    DynCircExt.gad_bitSign (β c₁ * β c₂ * β t) • DynCircExt.ket (Function.update β t (β t +
    β c₁ * β c₂)) := by
  simp only [cSignedToff, DynCircExt.eval_seq_mulVec, DynCircExt.gad_ket_S,
      DynCircExt.gad_ket_Z, Matrix.mulVec_smul]
  rcases DynCircExt.bit_cases (β t) with ht | ht
  · rw [DynCircExt.andCompute_mulVec_ket_of_zero c₁ c₂ t h₁₂ h₁t h₂t β ht];
    simp only [ht, mul_zero, zero_add, DynCircExt.gad_bitPhaseI, DynCircExt.gad_bitSign,
        ↓reduceIte, one_smul]
  · rw [CircExt.andCompute_loc, DynCircExt.eval_seq_mulVec, DynCircExt.gad_ket_H, ht];
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, DynCircExt.gad_jonesPhaseStep_mulVec_ket,
        Function.update_self, Function.update_of_ne h₁t,
        Function.update_of_ne h₂t]; simp only [DynCircExt.eval_seq_mulVec,
        DynCircExt.gad_ket_H, Function.update_self, Function.update_idem, Matrix.mulVec_smul,
        Matrix.mulVec_add,
        DynCircExt.gad_ket_S]; have h0 : DynCircExt.gad_bitPhaseI 0 = 1 :=
                                     rfl; have hs0 : DynCircExt.gad_bitSign 0 = 1 :=
                                            rfl; rw [h0, hs0, one_smul, one_smul,
                                            signedToff_Combine1]
    rcases DynCircExt.bit_cases (β c₁ * β c₂) with h | h
    · rw [mul_one, h]; simp only [↓reduceIte, add_zero]
    · rw [mul_one, h]; simp only [one_ne_zero, ↓reduceIte, DynCircExt.gad_one_add_one_zmod2]
def dSignedToff {Var : Type} {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) : DynamicCircuit Var n := .circuit (cSignedToff c₁ c₂ t h₁₂ h₁t h₂t)
theorem dSignedToff_counts {Var : Type} {n : ℕ} (c₁ c₂ t : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (dSignedToff (Var := Var) c₁ c₂ t h₁₂ h₁t h₂t).count .T = 4 ∧
    (dSignedToff (Var := Var) c₁ c₂ t h₁₂ h₁t h₂t).count .TOFF = 0 :=
  ⟨by simp [dSignedToff, cSignedToff, Circuit.S, Circuit.Z],
      by simp [dSignedToff, cSignedToff, Circuit.S, Circuit.Z]⟩
theorem dSignedToff_dynWires {Var : Type} {n : ℕ} (P : Wire n → Prop)
    (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (h₁ : P c₁) (h₂ : P c₂) (ht : P t) :
    DynWires P (dSignedToff (Var := Var) c₁ c₂ t h₁₂ h₁t h₂t) := by
  have ht1 {g : PrimitiveGate 1} : CircWires P (.gate g (QRegister.singleton t)) := fun _ ↦ ht
  have hp2 {x y : Wire n} (hx : P x) (hy : P y) (hne : x ≠ y) : CircWires P (Circuit.CNOT x y hne)
      := fun i ↦ by
    fin_cases i
    · exact hx
    · exact hy
  exact ⟨ht1, ht1, ht1, ht1, hp2 h₂ ht _, circWires_inverse ht1, hp2 h₁ ht _, ht1, hp2 h₂ ht _,
    circWires_inverse ht1, hp2 h₁ ht _, ht1, ht1⟩
theorem dSignedToff_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    (rWork : QRegister W n) (c₁ c₂ t : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork
        (fun δ ↦ Function.update (st δ) t (st δ t + st δ c₁ * st δ c₂))
        (fun δ ↦ ph δ + st δ c₁ * st δ c₂ * st δ t))
      (dSignedToff (Var := Var) c₁ c₂ t h₁₂ h₁t h₂t) := by
  refine subspaceStep_of_eq_post
    (subspaceStep_circuit (Var := Var) (cSignedToff c₁ c₂ t h₁₂ h₁t h₂t)
        (mkKetOpW rWork st ph)) ?_
  apply DynCircExt.matrix_ext_ket
  intro δ
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, ket_cSignedToff c₁ c₂ t h₁₂ h₁t h₂t (st δ), smul_smul,
        ← XMeasUnld.bitSign_add]
  · exact Matrix.mulVec_zero _
/-! ### 2. `0`-Ancilla Base Case (`4` Wires) & `(4 + 3 * k)`-Wire Controlled Adder + Kick -/

theorem ctrl0_lt0 (k : ℕ) : 0 < 4 + 3 * k := by omega
theorem ctrl0_lt1 (k : ℕ) : 1 < 4 + 3 * k := by omega
theorem ctrl0_lt2 (k : ℕ) : 2 < 4 + 3 * k := by omega
theorem ctrl0_ltB0 (k : ℕ) : 3 + k < 4 + 3 * k := by omega
theorem ctrl0_ltZ (k : ℕ) (i : Fin (k + 1)) : 2 + i.val < 4 + 3 * k := by have := i.isLt; omega
theorem ctrl0_ltB (k : ℕ) (i : Fin (k + 1)) : 3 + k + i.val < 4 + 3 * k := by have := i.isLt; omega
theorem ctrl0_ltC (k : ℕ) : 6 + 2 * k < 4 + 3 * (k + 1) := by omega

private theorem ctrl0_ne_mk {W n : ℕ} (r : QRegister W n) {i j : ℕ}
    (hi : i < W) (hj : j < W) (h : i ≠ j) : r ⟨i, hi⟩ ≠ r ⟨j, hj⟩ :=
  fun e ↦ h (congrArg Fin.val (r.wires.injective e))

theorem ctrl0_ne01 {n : ℕ} (k : ℕ) (r : QRegister (4 + 3 * k) n) : r ⟨0, ctrl0_lt0 k⟩ ≠
    r ⟨1, ctrl0_lt1 k⟩ := ctrl0_ne_mk r _ _ (by omega)
theorem ctrl0_ne02_0 {n : ℕ} (r : QRegister (4 + 3 * 0) n) : r ⟨0, ctrl0_lt0 0⟩ ≠ r ⟨2, ctrl0_lt2 0⟩
    := ctrl0_ne_mk r _ _ (by omega)
theorem ctrl0_ne03_0 {n : ℕ} (r : QRegister (4 + 3 * 0) n) : r ⟨0, ctrl0_lt0 0⟩ ≠
    r ⟨3 + 0, ctrl0_ltB0 0⟩ := ctrl0_ne_mk r _ _ (by omega)
theorem ctrl0_ne12_0 {n : ℕ} (r : QRegister (4 + 3 * 0) n) : r ⟨1, ctrl0_lt1 0⟩ ≠ r ⟨2, ctrl0_lt2 0⟩
    := ctrl0_ne_mk r _ _ (by omega)
theorem ctrl0_ne13_0 {n : ℕ} (r : QRegister (4 + 3 * 0) n) : r ⟨1, ctrl0_lt1 0⟩ ≠
    r ⟨3 + 0, ctrl0_ltB0 0⟩ := ctrl0_ne_mk r _ _ (by omega)
theorem ctrl0_ne32_0 {n : ℕ} (r : QRegister (4 + 3 * 0) n) : r ⟨3 + 0, ctrl0_ltB0 0⟩ ≠
    r ⟨2, ctrl0_lt2 0⟩ := ctrl0_ne_mk r _ _ (by omega)
theorem ctrl0_neC2 {n : ℕ} (k : ℕ) (r : QRegister (4 + 3 * (k + 1)) n) :
    r ⟨6 + 2 * k, ctrl0_ltC k⟩ ≠ r ⟨2, ctrl0_lt2 (k + 1)⟩ := ctrl0_ne_mk r _ _ (by omega)

/--
`4` -wire (`0`-ancilla) controlled 1-bit in-place adder + carry-out phase kick (`4 T`, `0` `.TOFF`
).
-/
def pCtrlAddCarryKick1_0anc {Var : Type} {n : ℕ} (v : Var) (r : QRegister (4 + 3 * 0) n) :
    DynamicCircuit Var n :=
    .seq (cz2 (r ⟨0, ctrl0_lt0 0⟩) (r ⟨1, ctrl0_lt1 0⟩) (ctrl0_ne01 0 r))
    (.seq (cnot1 v (r ⟨1, ctrl0_lt1 0⟩) (r ⟨3 + 0, ctrl0_ltB0 0⟩) (ctrl0_ne13_0 r))
    (.seq (cnot1 v (r ⟨1, ctrl0_lt1 0⟩) (r ⟨2, ctrl0_lt2 0⟩) (ctrl0_ne12_0 r))
    (.seq (dSignedToff (r ⟨0, ctrl0_lt0 0⟩) (r ⟨3 + 0, ctrl0_ltB0 0⟩) (r ⟨2, ctrl0_lt2 0⟩)
    (ctrl0_ne03_0 r) (ctrl0_ne02_0 r) (ctrl0_ne32_0 r)) (.seq (cnot1 v (r ⟨1, ctrl0_lt1 0⟩)
    (r ⟨2, ctrl0_lt2 0⟩) (ctrl0_ne12_0 r)) (cnot1 v (r ⟨1, ctrl0_lt1 0⟩) (r ⟨3 + 0, ctrl0_ltB0 0⟩)
    (ctrl0_ne13_0 r))))))
theorem pCtrlAddCarryKick1_0anc_counts {Var : Type} {n : ℕ} (v : Var)
    (r : QRegister (4 + 3 * 0) n) : (pCtrlAddCarryKick1_0anc v r).count .T = 4 ∧
    (pCtrlAddCarryKick1_0anc v r).count .TOFF = 0 := by
  obtain ⟨zT, zF⟩ := cz2_counts (Var := Var) (r ⟨0, ctrl0_lt0 0⟩) (r ⟨1, ctrl0_lt1 0⟩)
    (ctrl0_ne01 0 r)
  obtain ⟨c1T, c1F⟩ := cnot1_counts (Var := Var) v (r ⟨1, ctrl0_lt1 0⟩) (r ⟨3 + 0, ctrl0_ltB0 0⟩)
    (ctrl0_ne13_0 r)
  obtain ⟨c2T, c2F⟩ := cnot1_counts (Var := Var) v (r ⟨1, ctrl0_lt1 0⟩) (r ⟨2, ctrl0_lt2 0⟩)
    (ctrl0_ne12_0 r)
  obtain ⟨sT, sF⟩ := dSignedToff_counts (Var := Var) (r ⟨0, ctrl0_lt0 0⟩)
    (r ⟨3 + 0, ctrl0_ltB0 0⟩) (r ⟨2, ctrl0_lt2 0⟩) (ctrl0_ne03_0 r) (ctrl0_ne02_0 r)
        (ctrl0_ne32_0 r)
  dsimp only [pCtrlAddCarryKick1_0anc, DynamicCircuit.count];
  rw [zT, zF, c1T, c1F, c2T, c2F, sT, sF]; exact ⟨rfl, rfl⟩
theorem pCtrlAddCarryKick1_0anc_dynWires {Var : Type} {n : ℕ} (P : Wire n → Prop) (v : Var)
    (r : QRegister (4 + 3 * 0) n) (hP : ∀ i : Fin (4 + 3 * 0), P (r i)) :
    DynWires P (pCtrlAddCarryKick1_0anc v r) :=
    ⟨cz2_dynWires P _ _ (ctrl0_ne01 0 r) (hP _) (hP _), cnot1_dynWires P v _ _ (ctrl0_ne13_0 r)
    (hP _) (hP _), cnot1_dynWires P v _ _ (ctrl0_ne12_0 r) (hP _)
    (hP _), dSignedToff_dynWires P _ _ _ (ctrl0_ne03_0 r) (ctrl0_ne02_0 r) (ctrl0_ne32_0 r) (hP _)
    (hP _) (hP _), cnot1_dynWires P v _ _ (ctrl0_ne12_0 r) (hP _)
    (hP _), cnot1_dynWires P v _ _ (ctrl0_ne13_0 r) (hP _) (hP _)⟩
theorem pCtrlAddCarryKick1_0anc_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (4 + 3 * 0) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) : ∃ st' :
    BitAssignment n → BitAssignment n, SubspaceStep (mkKetOpW rWork st ph)
    (mkKetOpW rWork st' (fun δ ↦ ph δ + st δ (r ⟨0, ctrl0_lt0 0⟩) *
    (((finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ 0 i⟩)) +
    finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨3 + 0 + i.val, ctrl0_ltB 0 i⟩)) +
    (st δ (r ⟨1, ctrl0_lt1 0⟩)).val) / 2 ^ 1 : ℕ) : ZMod 2))) (pCtrlAddCarryKick1_0anc v r) ∧
    (∀ (δ : BitAssignment n) (w : Wire n), (∀ i : Fin 1, w ≠ r ⟨2 + i.val, ctrl0_ltZ 0 i⟩) →
    st' δ w = st δ w) ∧ (∀ (δ : BitAssignment n), (∀ m : Fin W, δ (rWork m) = 0) →
    st δ (r ⟨0, ctrl0_lt0 0⟩) = 0 → ∀ i : Fin 1, st' δ (r ⟨2 + i.val, ctrl0_ltZ 0 i⟩) =
    st δ (r ⟨2 + i.val, ctrl0_ltZ 0 i⟩)) ∧ (∀ (δ : BitAssignment n), (∀ m : Fin W, δ (rWork m) =
    0) → st δ (r ⟨0, ctrl0_lt0 0⟩) = 1 → finBitsVal (fun i : Fin 1 ↦
    st' δ (r ⟨2 + i.val, ctrl0_ltZ 0 i⟩)) =
    (finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ 0 i⟩)) + finBitsVal (fun i : Fin 1 ↦
    st δ (r ⟨3 + 0 + i.val, ctrl0_ltB 0 i⟩)) + (st δ (r ⟨1, ctrl0_lt1 0⟩)).val) % 2 ^ 1) := by
  let wCtrl := r ⟨0, ctrl0_lt0 0⟩
  let wCin := r ⟨1, ctrl0_lt1 0⟩
  let wZ0 := r ⟨2, ctrl0_lt2 0⟩
  let wB0 := r ⟨3 + 0, ctrl0_ltB0 0⟩
  let stOut : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st δ) wZ0 (st δ wZ0 + st δ wCtrl * (st δ wB0 + st δ wCin))
  let phPost : BitAssignment n → ZMod 2 := fun δ ↦
      ph δ + st δ wCtrl * (((finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ 0 i⟩)) +
      finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨3 + 0 + i.val, ctrl0_ltB 0 i⟩)) + (st δ wCin).val) /
      2 ^ 1 : ℕ) : ZMod 2)
  let ph1 : BitAssignment n → ZMod 2 := fun δ ↦ ph δ + st δ wCtrl * st δ wCin
  let st1 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st δ) wB0 (st δ wB0 + st δ wCin)
  let st2 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st1 δ) wZ0 (st1 δ wZ0 + st1 δ wCin)
  let st3 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st2 δ) wZ0 (st2 δ wZ0 + st2 δ wCtrl * st2 δ wB0)
  let ph2 : BitAssignment n → ZMod 2 := fun δ ↦ ph1 δ + st2 δ wCtrl * st2 δ wB0 * st2 δ wZ0
  let st4 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st3 δ) wZ0 (st3 δ wZ0 + st3 δ wCin)
  let st5 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st4 δ) wB0 (st4 δ wB0 + st4 δ wCin)
  have hChain : SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork st5 ph2)
      (pCtrlAddCarryKick1_0anc v r) :=
      subspaceStep_seq_mbu (cz2_step rWork wCtrl wCin (ctrl0_ne01 0 r) st ph)
      (subspaceStep_seq_mbu (cnot1_step v rWork wCin wB0 (ctrl0_ne13_0 r) st ph1)
      (subspaceStep_seq_mbu (cnot1_step v rWork wCin wZ0 (ctrl0_ne12_0 r) st1 ph1)
      (subspaceStep_seq_mbu (dSignedToff_step rWork wCtrl wB0 wZ0 (ctrl0_ne03_0 r) (ctrl0_ne02_0 r)
      (ctrl0_ne32_0 r) st2 ph1)
      (subspaceStep_seq_mbu (cnot1_step v rWork wCin wZ0 (ctrl0_ne12_0 r) st3 ph2)
      (cnot1_step v rWork wCin wB0 (ctrl0_ne13_0 r) st4 ph2)))))
  have h2Ctrl (δ : BitAssignment n) : st2 δ wCtrl = st δ wCtrl :=
    (Function.update_of_ne (ctrl0_ne02_0 r) _ _).trans (Function.update_of_ne (ctrl0_ne03_0 r) _ _)
  have h2B0 (δ : BitAssignment n) : st2 δ wB0 = st δ wB0 + st δ wCin :=
    (Function.update_of_ne (ctrl0_ne32_0 r) _ _).trans (Function.update_self _ _ _)
  have h2Z0 (δ : BitAssignment n) : st2 δ wZ0 = st δ wZ0 + st δ wCin :=
    (Function.update_self _ _ _).trans (congrArg₂ (· + ·)
        (Function.update_of_ne (ctrl0_ne32_0 r).symm _ _)
        (Function.update_of_ne (ctrl0_ne13_0 r) _ _))
  have hStep : SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork stOut phPost)
      (pCtrlAddCarryKick1_0anc v r) := by
    refine subspaceStep_of_eq_post hChain (mkKetOpW_congr rWork (fun δ _ ↦ ?_) (fun δ _ ↦ ?_))
    · funext w
      have h2Cin : st2 δ wCin = st δ wCin := by
        dsimp only [st2, st1];
        rw [Function.update_of_ne (ctrl0_ne12_0 r), Function.update_of_ne (ctrl0_ne13_0 r)]
      have h3Cin : st3 δ wCin = st δ wCin := by
        dsimp only [st3]; rw [Function.update_of_ne (ctrl0_ne12_0 r), h2Cin]
      have h4Cin : st4 δ wCin = st δ wCin := by
        dsimp only [st4]; rw [Function.update_of_ne (ctrl0_ne12_0 r), h3Cin]
      by_cases hwz : w = wZ0
      · subst hwz; dsimp only [st5, st4, stOut];
        rw [Function.update_of_ne (ctrl0_ne32_0 r).symm, Function.update_self, Function.update_self,
            h3Cin]; dsimp only [st3]; rw [Function.update_self, h2Z0, h2Ctrl, h2B0]
        rw [show st δ wZ0 + st δ wCin + st δ wCtrl * (st δ wB0 + st δ wCin) + st δ wCin = st δ wZ0 +
            st δ wCtrl * (st δ wB0 + st δ wCin) + st δ wCin + st δ wCin by ring,
            CharTwo.add_cancel_right]
      · by_cases hwb : w = wB0
        · subst hwb; dsimp only [st5, stOut];
          rw [Function.update_self, Function.update_of_ne (ctrl0_ne32_0 r), h4Cin];
          dsimp only [st4, st3];
          rw [Function.update_of_ne (ctrl0_ne32_0 r), Function.update_of_ne (ctrl0_ne32_0 r), h2B0,
              CharTwo.add_cancel_right]
        · dsimp only [st5, st4, st3, st2, st1, stOut];
          rw [Function.update_of_ne hwb, Function.update_of_ne hwz, Function.update_of_ne hwz,
              Function.update_of_ne hwz, Function.update_of_ne hwb, Function.update_of_ne hwz]
    · dsimp only [ph2, ph1, phPost]
      rw [h2Ctrl, h2B0, h2Z0, ctrl_finBitsVal_fin1_local, ctrl_finBitsVal_fin1_local,
          show r ⟨2 + (0 : Fin 1).val, ctrl0_ltZ 0 0⟩ = wZ0 from rfl,
          show r ⟨3 + 0 + (0 : Fin 1).val, ctrl0_ltB 0 0⟩ = wB0 from rfl,
          ← zmod2_maj_id (st δ wZ0) (st δ wB0) (st δ wCin),
          maj_div_pow_succ (ZMod.val_lt _) _ 0, pow_zero, Nat.div_one, zmod2_val_cast]
      ring
  refine ⟨stOut, hStep, fun δ w hw ↦ ?_, fun δ _ hIdle i ↦ ?_, fun δ _ hAct ↦ ?_⟩
  · dsimp only [stOut]; exact Function.update_of_ne (hw 0) _ _
  · fin_cases i
    change stOut δ wZ0 = st δ wZ0; dsimp only [stOut];
    rw [Function.update_self, hIdle, zero_mul, add_zero]
  · rw [ctrl_finBitsVal_fin1_local, ctrl_finBitsVal_fin1_local, ctrl_finBitsVal_fin1_local,
        show r ⟨2 + (0 : Fin 1).val, ctrl0_ltZ 0 0⟩ = wZ0 from rfl,
        show r ⟨3 + 0 + (0 : Fin 1).val, ctrl0_ltB 0 0⟩ = wB0 from rfl]
    dsimp only [stOut]
    rw [Function.update_self, hAct, one_mul, pow_one,
        show st δ wZ0 + (st δ wB0 + st δ wCin) = st δ wZ0 + st δ wB0 + st δ wCin by ring]
    have hm := zmod2_maj_id (st δ wZ0) (st δ wB0) (st δ wCin);
    have hlt :=
        ZMod.val_lt (st δ wZ0 + st δ wB0 + st δ wCin); dsimp only [wZ0, wB0,
        wCin] at hm hlt ⊢; omega
/-! ### 3. Recursive `(4 + 3 * k)`-Wire `pCtrlAddCarryKickFast0Anc` (`8 * k + 4` `T`) -/

def idxCtrl0Maj (k : ℕ) (u : Fin 4) : ℕ :=
    if u.val = 0 then 2 else if u.val = 1 then 4 + k else if u.val = 2 then 1 else 6 + 2 * k
theorem idxCtrl0Maj_lt (k : ℕ) (u : Fin 4) : idxCtrl0Maj k u < 4 + 3 * (k + 1) := by
  dsimp only [idxCtrl0Maj]; split_ifs <;> omega
def fCtrl0Maj (k : ℕ) : Fin 4 → Fin (4 + 3 * (k + 1)) := fun u ↦
    ⟨idxCtrl0Maj k u, idxCtrl0Maj_lt k u⟩
theorem fCtrl0Maj_inj (k : ℕ) : Function.Injective (fCtrl0Maj k) := fun a b e ↦ by
  have hv : idxCtrl0Maj k a = idxCtrl0Maj k b := congrArg Fin.val e
  have _ := a.isLt; have _ := b.isLt
  dsimp only [idxCtrl0Maj] at hv; split_ifs at hv <;> exact Fin.ext (by omega)

def idxCtrl0Xor (k : ℕ) (u : Fin 4) : ℕ :=
    if u.val = 0 then 0 else if u.val = 1 then 4 + k else if u.val = 2 then 1 else 6 + 2 * k
theorem idxCtrl0Xor_lt (k : ℕ) (u : Fin 4) : idxCtrl0Xor k u < 4 + 3 * (k + 1) := by
  dsimp only [idxCtrl0Xor]; split_ifs <;> omega
def fCtrl0Xor (k : ℕ) : Fin 4 → Fin (4 + 3 * (k + 1)) := fun u ↦
    ⟨idxCtrl0Xor k u, idxCtrl0Xor_lt k u⟩
theorem fCtrl0Xor_inj (k : ℕ) : Function.Injective (fCtrl0Xor k) := fun a b e ↦ by
  have hv : idxCtrl0Xor k a = idxCtrl0Xor k b := congrArg Fin.val e
  have _ := a.isLt; have _ := b.isLt
  dsimp only [idxCtrl0Xor] at hv; split_ifs at hv <;> exact Fin.ext (by omega)

def idxCtrl0Sub (k : ℕ) (u : Fin (4 + 3 * k)) : ℕ :=
    if u.val = 0 then 0 else if u.val = 1 then 6 + 2 * k else if u.val < 3 + k then 1 +
    u.val else if u.val < 4 + 2 * k then 2 + u.val else 3 + u.val
theorem idxCtrl0Sub_lt (k : ℕ) (u : Fin (4 + 3 * k)) : idxCtrl0Sub k u < 4 + 3 * (k + 1) := by
  have _ := u.isLt; dsimp only [idxCtrl0Sub]; split_ifs <;> omega
def fCtrl0Sub (k : ℕ) : Fin (4 + 3 * k) → Fin (4 + 3 * (k + 1)) := fun u ↦
    ⟨idxCtrl0Sub k u, idxCtrl0Sub_lt k u⟩
theorem fCtrl0Sub_inj (k : ℕ) : Function.Injective (fCtrl0Sub k) := fun a b e ↦ by
  have hv : idxCtrl0Sub k a = idxCtrl0Sub k b := congrArg Fin.val e
  have _ := a.isLt; have _ := b.isLt
  dsimp only [idxCtrl0Sub] at hv; split_ifs at hv <;> exact Fin.ext (by omega)

/--
Controlled `(k + 1)`-bit in-place adder + carry-out kick on `4 + 3 * k` wires (`k` clean ancillas,
`8 * k + 4` `T` gates, `0` `.TOFF` ). At `k = 15` (`16` bits), uses `49` wires (`15` ancillas,
`124 T` ).
-/
def pCtrlAddCarryKickFast0Anc : (k : ℕ) → {Var : Type} → {n : ℕ} → Var →
    QRegister (4 + 3 * k) n → DynamicCircuit Var n
  | 0, _, _, v, r =>
      pCtrlAddCarryKick1_0anc v r
  | k + 1, _, _, v, r =>
      .seq
        (wrapDynOnReg v (r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩) cpMaj4
          (pCtrlAddCarryKickFast0Anc k v (r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩)))
        (wrapDynOnReg v (r.compose ⟨fCtrl0Xor k, fCtrl0Xor_inj k⟩) cpXorAnd4
          (cnot1 v (r ⟨6 + 2 * k, ctrl0_ltC k⟩) (r ⟨2, ctrl0_lt2 (k + 1)⟩)
            (ctrl0_neC2 k r)))

theorem pCtrlAddCarryKickFast0Anc_counts : ∀ (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (r : QRegister (4 + 3 * k) n),
    (pCtrlAddCarryKickFast0Anc k v r).count .T = 8 * k + 4 ∧
    (pCtrlAddCarryKickFast0Anc k v r).count .TOFF = 0
  | 0, _, _, v, r => pCtrlAddCarryKick1_0anc_counts v r
  | k + 1, Var, _, v, r => by
      obtain ⟨ihT, ihF⟩ :=
          pCtrlAddCarryKickFast0Anc_counts k v (r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩)
      obtain ⟨w1T, w1F⟩ := counts_wrapDynOnReg v (r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩) cpMaj4
        (pCtrlAddCarryKickFast0Anc k v (r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩))
      obtain ⟨cT, cF⟩ :=
          cnot1_counts (Var := Var) v (r ⟨6 + 2 * k, ctrl0_ltC k⟩) (r ⟨2, ctrl0_lt2 (k + 1)⟩)
          (ctrl0_neC2 k r)
      obtain ⟨w2T, w2F⟩ :=
          counts_wrapDynOnReg v (r.compose ⟨fCtrl0Xor k, fCtrl0Xor_inj k⟩) cpXorAnd4
        (cnot1 v (r ⟨6 + 2 * k, ctrl0_ltC k⟩) (r ⟨2, ctrl0_lt2 (k + 1)⟩) (ctrl0_neC2 k r))
      dsimp only [pCtrlAddCarryKickFast0Anc, DynamicCircuit.count]
      rw [w1T, w1F, cpMaj4_numAnd, ihT, ihF, w2T, w2F, cpXorAnd4_numAnd, cT, cF]
      exact ⟨by omega, rfl⟩
theorem pCtrlAddCarryKickFast0Anc_dynWires : ∀ (k : ℕ) {Var : Type} {n : ℕ} (P : Wire n → Prop)
    (v : Var) (r : QRegister (4 + 3 * k) n),
    (∀ i : Fin (4 + 3 * k), P (r i)) → DynWires P (pCtrlAddCarryKickFast0Anc k v r)
  | 0, _, _, P, v, r, hP => pCtrlAddCarryKick1_0anc_dynWires P v r hP
  | k + 1, _, _, P, v, r, hP =>
      ⟨dynWires_wrapDynOnReg v (r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩)
          (fun u ↦ hP (fCtrl0Maj k u)) cpMaj4
        (pCtrlAddCarryKickFast0Anc_dynWires k P v (r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩)
            (fun u ↦ hP (fCtrl0Sub k u))),
       dynWires_wrapDynOnReg v (r.compose ⟨fCtrl0Xor k, fCtrl0Xor_inj k⟩)
           (fun u ↦ hP (fCtrl0Xor k u)) cpXorAnd4
        (cnot1_dynWires P v (r _) (r _) (ctrl0_neC2 k r) (hP _) (hP _))⟩
abbrev ctrl0SubStFwd {n : ℕ} (k : ℕ) (r : QRegister (4 + 3 * (k + 1)) n)
    (st : BitAssignment n → BitAssignment n) : BitAssignment n → BitAssignment n := fun δ ↦
    stepCB (r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩) cpMaj4.fwdBits (st δ)
theorem ctrl0SubStFwd_at_sub {n : ℕ} (k : ℕ) (r : QRegister (4 + 3 * (k + 1)) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
    (u : Fin (4 + 3 * k)) (hu : u.val ≠ 1) :
    ctrl0SubStFwd k r st δ ((r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩) u) =
      st δ (r (fCtrl0Sub k u)) :=
  stepCB_cpMaj4_not (r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩) (st δ) fun e ↦ by
    have hv := congrArg Fin.val (r.wires.injective e)
    have _ := u.isLt
    dsimp [fCtrl0Sub, idxCtrl0Sub, fCtrl0Maj, idxCtrl0Maj, w4_3] at hv
    split_ifs at hv <;> omega
theorem ctrl0_sub_decomp (k : ℕ) {W n : ℕ} (rWork : QRegister W n)
    (r : QRegister (4 + 3 * (k + 1)) n) (st : BitAssignment n → BitAssignment n)
    (hCln : ∀ (u : Fin (4 + 3 * (k + 1))) (δ : BitAssignment n), 4 + 2 * (k + 1) ≤ u.val →
      (∀ m : Fin W, δ (rWork m) = 0) → st δ (r u) = 0)
    (δ : BitAssignment n) (hz : ∀ m : Fin W, δ (rWork m) = 0) :
    finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ (k + 1) i⟩)) +
    finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨3 + (k + 1) + i.val, ctrl0_ltB (k + 1) i⟩)) +
    (st δ (r ⟨1, ctrl0_lt1 (k + 1)⟩)).val =
    (st δ (r ⟨2, ctrl0_lt2 (k + 1)⟩) + st δ (r ⟨4 + k, by omega⟩) +
      st δ (r ⟨1, ctrl0_lt1 (k + 1)⟩)).val +
    2 * (finBitsVal (fun i : Fin (k + 1) ↦
           ctrl0SubStFwd k r st δ ((r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩)
               ⟨2 + i.val, ctrl0_ltZ k i⟩)) +
         finBitsVal (fun i : Fin (k + 1) ↦
           ctrl0SubStFwd k r st δ ((r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩)
               ⟨3 + k + i.val, ctrl0_ltB k i⟩)) +
         (ctrl0SubStFwd k r st δ ((r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩) ⟨1, ctrl0_lt1 k⟩)).val)
             := by
  let rMaj := r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩
  let rSub := r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩
  let wCin := r ⟨1, ctrl0_lt1 (k + 1)⟩
  let wZ0 := r ⟨2, ctrl0_lt2 (k + 1)⟩
  let wB0 := r ⟨4 + k, by omega⟩
  let wCn := r ⟨6 + 2 * k, ctrl0_ltC k⟩
  have hSubZIn :
      finBitsVal (fun i : Fin (k + 1) ↦ ctrl0SubStFwd k r st δ (rSub ⟨2 + i.val, ctrl0_ltZ k i⟩)) =
      finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨2 + i.succ.val, ctrl0_ltZ (k + 1) i.succ⟩)) :=
    congrArg finBitsVal (funext fun i ↦ (ctrl0SubStFwd_at_sub k r st δ _ (by dsimp; omega)).trans
      (congrArg (st δ ∘ r.wires) (Fin.ext (by
        have := i.isLt
        dsimp [fCtrl0Sub, idxCtrl0Sub, Fin.val_succ]
        split_ifs <;> omega))))
  have hSubBIn :
      finBitsVal (fun i : Fin (k + 1) ↦ ctrl0SubStFwd k r st δ (rSub ⟨3 + k + i.val,
          ctrl0_ltB k i⟩)) =
      finBitsVal (fun i : Fin (k + 1) ↦
        st δ (r ⟨3 + (k + 1) + i.succ.val, ctrl0_ltB (k + 1) i.succ⟩)) :=
    congrArg finBitsVal (funext fun i ↦ (ctrl0SubStFwd_at_sub k r st δ _ (by dsimp; omega)).trans
      (congrArg (st δ ∘ r.wires) (Fin.ext (by
        have := i.isLt
        dsimp [fCtrl0Sub, idxCtrl0Sub, Fin.val_succ]
        split_ifs <;> omega))))
  have hSubCin : ctrl0SubStFwd k r st δ (rSub ⟨1, ctrl0_lt1 k⟩) = (st δ wZ0 + st δ wCin) *
      (st δ wB0 + st δ wCin) + st δ wCin := by
    rw [show rSub ⟨1, ctrl0_lt1 k⟩ = rMaj w4_3 from rfl]
    dsimp only [ctrl0SubStFwd]
    rw [stepCB_cpMaj4_anc,
        show rMaj w4_3 = wCn from rfl,
        hCln ⟨6 + 2 * k, ctrl0_ltC k⟩ δ (by dsimp only; omega) hz, zero_add]
    rfl
  have hzSplit : finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ (k + 1) i⟩)) =
      (st δ wZ0).val + 2 * finBitsVal (fun i : Fin (k + 1) ↦
      st δ (r ⟨2 + i.succ.val, ctrl0_ltZ (k + 1) i.succ⟩)) := by
    rw [finBitsVal_succ, show r ⟨2 + (0 : Fin (k + 2)).val, ctrl0_ltZ (k + 1) 0⟩ =
        wZ0 from congrArg r.wires (Fin.ext (by dsimp))]
  have hbSplit : finBitsVal (fun i : Fin (k + 2) ↦
      st δ (r ⟨3 + (k + 1) + i.val, ctrl0_ltB (k + 1) i⟩)) = (st δ wB0).val + 2 *
      finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨3 + (k + 1) + i.succ.val,
      ctrl0_ltB (k + 1) i.succ⟩)) := by
    rw [finBitsVal_succ, show r ⟨3 + (k + 1) + (0 : Fin (k + 2)).val, ctrl0_ltB (k + 1) 0⟩ =
        wB0 from congrArg r.wires (Fin.ext (show 3 + (k + 1) + 0 = 4 + k by omega))]
  rw [hzSplit, hbSplit, hSubZIn, hSubBIn, hSubCin];
  have hm :=
      zmod2_maj_id (st δ wZ0) (st δ wB0) (st δ wCin); dsimp only [wZ0, wB0, wCin] at hm ⊢; omega
theorem ctrl0_wrap2_step (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n)
    (r : QRegister (4 + 3 * (k + 1)) n)
    (st stUn : BitAssignment n → BitAssignment n) (phPost : BitAssignment n → ZMod 2)
    (hClnC : ∀ δ : BitAssignment n, (∀ m : Fin W, δ (rWork m) = 0) →
      st δ (r ⟨6 + 2 * k, ctrl0_ltC k⟩) = 0)
    (hUnC : ∀ δ : BitAssignment n,
      stUn δ (r ⟨6 + 2 * k, ctrl0_ltC k⟩) = st δ (r ⟨6 + 2 * k, ctrl0_ltC k⟩))
    (hUnFixed : ∀ (δ : BitAssignment n) {idx : ℕ} (hi : idx < 4 + 3 * (k + 1)),
      (∀ i : Fin (k + 1), idx ≠ 3 + i.val) → stUn δ (r ⟨idx, hi⟩) = st δ (r ⟨idx, hi⟩)) :
    SubspaceStep (mkKetOpW rWork stUn phPost)
      (mkKetOpW rWork (fun δ ↦ Function.update (stUn δ) (r ⟨2, ctrl0_lt2 (k + 1)⟩)
        (stUn δ (r ⟨2, ctrl0_lt2 (k + 1)⟩) +
          st δ (r ⟨0, ctrl0_lt0 (k + 1)⟩) *
            (st δ (r ⟨4 + k, by omega⟩) + st δ (r ⟨1, ctrl0_lt1 (k + 1)⟩)))) phPost)
      (wrapDynOnReg v (r.compose ⟨fCtrl0Xor k, fCtrl0Xor_inj k⟩) cpXorAnd4
        (cnot1 v (r ⟨6 + 2 * k, ctrl0_ltC k⟩) (r ⟨2, ctrl0_lt2 (k + 1)⟩) (ctrl0_neC2 k r))) := by
  let rXor := r.compose ⟨fCtrl0Xor k, fCtrl0Xor_inj k⟩
  let wCtrl := r ⟨0, ctrl0_lt0 (k + 1)⟩
  let wCin := r ⟨1, ctrl0_lt1 (k + 1)⟩
  let wZ0 := r ⟨2, ctrl0_lt2 (k + 1)⟩
  let wB0 := r ⟨4 + k, by omega⟩
  let wCn := r ⟨6 + 2 * k, ctrl0_ltC k⟩
  let stOut : BitAssignment n → BitAssignment n :=
    fun δ ↦ Function.update (stUn δ) wZ0 (stUn δ wZ0 + st δ wCtrl * (st δ wB0 + st δ wCin))
  have hCn0 (δ : BitAssignment n) (hz : ∀ m : Fin W, δ (rWork m) = 0) : stUn δ wCn = 0 :=
    (hUnC δ).trans (hClnC δ hz)
  refine wrapStepMask v rWork rXor 8 cpXorAnd4 cpXorAnd4_valid8
    (cnot1 v wCn wZ0 (ctrl0_neC2 k r)) stUn stOut phPost phPost
    (fun u δ hu hz ↦ (congrArg (stUn δ ∘ rXor.wires) (mask8_eq_w4_3 hu)).trans (hCn0 δ hz))
    (fun u δ hu hz ↦ (congrArg (stOut δ ∘ rXor.wires) (mask8_eq_w4_3 hu)).trans
      ((Function.update_of_ne (ctrl0_neC2 k r) _ _).trans (hCn0 δ hz))) ?_
  refine subspaceStep_of_eq_post (cnot1_step v rWork wCn wZ0 (ctrl0_neC2 k r)
    (fun δ ↦ stepCB rXor cpXorAnd4.fwdBits (stUn δ)) phPost) ?_
  refine mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ ?_) (fun _ _ ↦ rfl)
  have hUnB0 : stUn δ wB0 = st δ wB0 := hUnFixed δ _ fun i ↦ by
    have := i.isLt
    omega
  have hXorZ0 : stepCB rXor cpXorAnd4.fwdBits (stUn δ) wZ0 = stUn δ wZ0 :=
    stepCB_cpXorAnd4_not rXor (stUn δ) (ctrl0_neC2 k r).symm
  have hXorCn : stepCB rXor cpXorAnd4.fwdBits (stUn δ) wCn =
      st δ wCtrl * (st δ wB0 + st δ wCin) := by
    rw [show wCn = rXor w4_3 from rfl, stepCB_cpXorAnd4_anc,
        show rXor w4_3 = wCn from rfl, hCn0 δ hz, zero_add,
        show rXor w4_0 = wCtrl from rfl, hUnFixed δ _ (fun _ ↦ by omega),
        show rXor w4_1 = wB0 from rfl, hUnB0,
        show rXor w4_2 = wCin from rfl, hUnFixed δ _ (fun _ ↦ by omega)]
  by_cases hwz : w = wZ0
  · subst hwz;
    rw [Function.update_self, hXorZ0, hXorCn, stepCB_cpXorAnd4_not rXor (stOut δ)
        (ctrl0_neC2 k r).symm]
    dsimp only [stOut]; rw [Function.update_self]
  · rw [Function.update_of_ne hwz]
    by_cases hwc : w = wCn
    · subst hwc
      rw [show wCn = rXor w4_3 from rfl, stepCB_cpXorAnd4_anc, stepCB_cpXorAnd4_anc]
      dsimp only [stOut]
      have nz : ∀ u : Wire 4, rXor u ≠ wZ0 := fun u e ↦ by
        have hv := congrArg Fin.val (r.wires.injective e); have _ := u.isLt
        dsimp [rXor, fCtrl0Xor, idxCtrl0Xor, wZ0] at hv; split_ifs at hv <;> omega
      rw [Function.update_of_ne (nz w4_3), Function.update_of_ne (nz w4_0),
          Function.update_of_ne (nz w4_1), Function.update_of_ne (nz w4_2)]
    · rw [stepCB_cpXorAnd4_not rXor (stUn δ) hwc, stepCB_cpXorAnd4_not rXor (stOut δ) hwc]
      dsimp only [stOut]; rw [Function.update_of_ne hwz]

theorem pCtrlAddCarryKickFast0Anc_step : ∀ (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (4 + 3 * k) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (u : Fin (4 + 3 * k)) (δ : BitAssignment n), 4 + 2 * k ≤ u.val →
      (∀ m : Fin W, δ (rWork m) = 0) → st δ (r u) = 0) →
    ∃ st' : BitAssignment n → BitAssignment n,
      SubspaceStep (mkKetOpW rWork st ph)
        (mkKetOpW rWork st' (fun δ ↦ ph δ + st δ (r ⟨0, ctrl0_lt0 k⟩) *
          (((finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ k i⟩)) +
             finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨3 + k + i.val, ctrl0_ltB k i⟩)) +
             (st δ (r ⟨1, ctrl0_lt1 k⟩)).val) / 2 ^ (k + 1) : ℕ) : ZMod 2)))
        (pCtrlAddCarryKickFast0Anc k v r) ∧
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ i : Fin (k + 1), w ≠ r ⟨2 + i.val, ctrl0_ltZ k i⟩) → st' δ w = st δ w) ∧
      (∀ (δ : BitAssignment n), (∀ m : Fin W, δ (rWork m) = 0) →
        st δ (r ⟨0, ctrl0_lt0 k⟩) = 0 →
        ∀ i : Fin (k + 1), st' δ (r ⟨2 + i.val, ctrl0_ltZ k i⟩) =
            st δ (r ⟨2 + i.val, ctrl0_ltZ k i⟩)) ∧
      (∀ (δ : BitAssignment n), (∀ m : Fin W, δ (rWork m) = 0) →
        st δ (r ⟨0, ctrl0_lt0 k⟩) = 1 →
        finBitsVal (fun i : Fin (k + 1) ↦ st' δ (r ⟨2 + i.val, ctrl0_ltZ k i⟩)) =
          (finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ k i⟩)) +
           finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨3 + k + i.val, ctrl0_ltB k i⟩)) +
           (st δ (r ⟨1, ctrl0_lt1 k⟩)).val) % 2 ^ (k + 1))
  | 0, _, _, _, _, _, _, v, rWork, r, st, ph, _ =>
      pCtrlAddCarryKick1_0anc_step v rWork r st ph
  | k + 1, _, _, _, wLen, n, _, v, rWork, r, st, ph, hCln => by
      let rMaj := r.compose ⟨fCtrl0Maj k, fCtrl0Maj_inj k⟩
      let rSub := r.compose ⟨fCtrl0Sub k, fCtrl0Sub_inj k⟩
      let wCtrl := r ⟨0, ctrl0_lt0 (k + 1)⟩
      let wCin := r ⟨1, ctrl0_lt1 (k + 1)⟩
      let wZ0 := r ⟨2, ctrl0_lt2 (k + 1)⟩
      let wB0 := r ⟨4 + k, by omega⟩
      let stFwd : BitAssignment n → BitAssignment n := ctrl0SubStFwd k r st
      have hSubCln : ∀ (u : Fin (4 + 3 * k)) (δ : BitAssignment n), 4 + 2 * k ≤ u.val →
          (∀ m : Fin wLen, δ (rWork m) = 0) → stFwd δ (rSub u) = 0 := fun u δ hu hz ↦
        (ctrl0SubStFwd_at_sub k r st δ u (by omega)).trans
          ((congrArg (st δ ∘ r.wires) (Fin.ext (by
            have := u.isLt
            dsimp [fCtrl0Sub, idxCtrl0Sub]
            split_ifs <;> omega))).trans
            (hCln ⟨3 + u.val, Nat.lt_of_lt_of_eq (Nat.add_lt_add_left u.isLt 3) (by omega)⟩
              δ (show 4 + 2 * (k + 1) ≤ 3 + u.val by omega) hz))
      obtain ⟨stMid, hMidStep, hMidNot, hMidIdle, hMidAct⟩ :=
        pCtrlAddCarryKickFast0Anc_step k v rWork rSub stFwd ph hSubCln
      let stUn : BitAssignment n → BitAssignment n :=
        fun δ w ↦ if w = rMaj w4_3 then st δ w else stMid δ w
      have hMajNotSub : ∀ u : Wire 4, ∀ i : Fin (k + 1),
          rMaj u ≠ rSub ⟨2 + i.val, ctrl0_ltZ k i⟩ := fun u i e ↦ by
        have hv := congrArg Fin.val (r.wires.injective e)
        have _ := u.isLt
        have _ := i.isLt
        dsimp [rMaj, fCtrl0Maj, idxCtrl0Maj, rSub, fCtrl0Sub, idxCtrl0Sub] at hv
        split_ifs at hv <;> omega
      let phPost : BitAssignment n → ZMod 2 := fun δ ↦
        ph δ + st δ wCtrl *
          (((finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨2 + i.val, ctrl0_ltZ (k + 1) i⟩)) +
             finBitsVal (fun i : Fin (k + 2) ↦
               st δ (r ⟨3 + (k + 1) + i.val, ctrl0_ltB (k + 1) i⟩)) +
             (st δ wCin).val) / 2 ^ (k + 2) : ℕ) : ZMod 2)
      have hSubCtrl : ∀ δ, stFwd δ (rSub ⟨0, ctrl0_lt0 k⟩) = st δ wCtrl :=
        fun δ ↦ ctrl0SubStFwd_at_sub k r st δ ⟨0, ctrl0_lt0 k⟩ Nat.zero_ne_one
      have hClnC (δ : BitAssignment n) :=
        hCln ⟨6 + 2 * k, ctrl0_ltC k⟩ δ (show 4 + 2 * (k + 1) ≤ 6 + 2 * k by omega)
      have hWrap1 : SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork stUn phPost)
          (wrapDynOnReg v rMaj cpMaj4 (pCtrlAddCarryKickFast0Anc k v rSub)) :=
        wrapCpMaj4 v rWork rMaj (pCtrlAddCarryKickFast0Anc k v rSub) st stMid ph _ phPost
          hClnC (fun u δ ↦ hMidNot δ (rMaj u) (hMajNotSub u))
          (fun δ hz ↦ by
            dsimp only [phPost]
            rw [hSubCtrl δ, ctrl0_sub_decomp k rWork r st hCln δ hz,
                maj_div_pow_succ (ZMod.val_lt _) _ (k + 1)])
          hMidStep
      have hUnFixed : ∀ (δ : BitAssignment n) {idx : ℕ} (hi : idx < 4 + 3 * (k + 1)),
          (∀ i : Fin (k + 1), idx ≠ 3 + i.val) → stUn δ (r ⟨idx, hi⟩) = st δ (r ⟨idx, hi⟩) :=
          fun δ {idx} hi hni ↦ by
        by_cases hcn : r ⟨idx, hi⟩ = rMaj w4_3
        · exact leg_if_pos hcn
        · rw [show stUn δ (r ⟨idx, hi⟩) = stMid δ (r ⟨idx, hi⟩) from leg_if_neg hcn,
              hMidNot δ _ (fun i e ↦ by
                have hv := congrArg Fin.val (r.wires.injective e)
                have _ := i.isLt
                dsimp [rSub, fCtrl0Sub, idxCtrl0Sub] at hv
                split_ifs at hv <;> exact hni i (by omega))]
          exact stepCB_cpMaj4_not rMaj (st δ) hcn
      let stOut : BitAssignment n → BitAssignment n :=
        fun δ ↦ Function.update (stUn δ) wZ0 (stUn δ wZ0 + st δ wCtrl * (st δ wB0 + st δ wCin))
      have hWrap2 := ctrl0_wrap2_step k v rWork r st stUn phPost hClnC
        (fun _ ↦ leg_if_pos (rfl : r ⟨6 + 2 * k, ctrl0_ltC k⟩ = rMaj w4_3)) hUnFixed
      have hSuccEq : ∀ j : Fin (k + 1),
          r ⟨2 + j.succ.val, ctrl0_ltZ (k + 1) j.succ⟩ = rSub ⟨2 + j.val, ctrl0_ltZ k j⟩ :=
        fun j ↦ congrArg r.wires (Fin.ext (by
          have := j.isLt
          dsimp [rSub, fCtrl0Sub, idxCtrl0Sub, Fin.val_succ]
          split_ifs <;> omega))
      have hSuccOut : ∀ (δ : BitAssignment n) (j : Fin (k + 1)),
          stOut δ (r ⟨2 + j.succ.val, ctrl0_ltZ (k + 1) j.succ⟩) =
            stMid δ (rSub ⟨2 + j.val, ctrl0_ltZ k j⟩) := fun δ j ↦ by
        dsimp only [stOut, stUn]
        rw [Function.update_of_ne (ctrl0_ne_mk r _ (ctrl0_lt2 (k + 1)) (by
              rw [Fin.val_succ]
              omega)),
            leg_if_neg (fun e ↦ hMajNotSub w4_3 j (e.symm.trans (hSuccEq j))), hSuccEq j]
      refine ⟨stOut, subspaceStep_seq_mbu hWrap1 hWrap2, fun δ w hw ↦ ?_,
        fun δ hz hIdle i ↦ ?_, fun δ hz hAct ↦ ?_⟩
      · dsimp only [stOut, stUn]
        rw [Function.update_of_ne (show w ≠ wZ0 from hw ⟨0, Nat.zero_lt_succ (k + 1)⟩)]
        by_cases hcn : w = rMaj w4_3
        · exact leg_if_pos hcn
        · rw [leg_if_neg hcn]
          exact (hMidNot δ w fun i e ↦ hw i.succ (e.trans (hSuccEq i).symm)).trans
            (stepCB_cpMaj4_not rMaj (st δ) hcn)
      · by_cases hi0 : i.val = 0
        · dsimp only [stOut]
          rw [show r ⟨2 + i.val, ctrl0_ltZ (k + 1) i⟩ = wZ0 from
                congrArg r.wires (Fin.ext (Nat.add_eq_left.mpr hi0)),
              Function.update_self, hIdle, zero_mul, add_zero]
          exact hUnFixed δ _ (fun _ ↦ by omega)
        · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_of_val_ne hi0)
          rw [hSuccOut δ j, hMidIdle δ hz ((hSubCtrl δ).trans hIdle) j, hSuccEq j]
          exact ctrl0SubStFwd_at_sub k r st δ _ (by dsimp; omega)
      · rw [finBitsVal_succ, congrArg finBitsVal (funext (hSuccOut δ)),
            hMidAct δ hz ((hSubCtrl δ).trans hAct)]
        have h0Eq : stOut δ (r ⟨2 + (0 : Fin (k + 2)).val, ctrl0_ltZ (k + 1) 0⟩) =
            st δ wZ0 + st δ wB0 + st δ wCin := by
          rw [show r ⟨2 + (0 : Fin (k + 2)).val, ctrl0_ltZ (k + 1) 0⟩ = wZ0 from rfl]
          dsimp only [stOut]
          rw [Function.update_self, hAct, one_mul, hUnFixed δ _ (fun _ ↦ by omega)]
          ring
        rw [h0Eq, two_mul_mod_add (ZMod.val_lt _), ← ctrl0_sub_decomp k rWork r st hCln δ hz,
            show (2 * 2 ^ (k + 1) : ℕ) = 2 ^ (k + 2) by ring]

/-! ### 4. `MidOWNoMux42Exact` (`71 + 42 = 113` Wires, `296 T`, `0` `.TOFF`) -/

end QuantumComputation.Specs.PhotochemistrySolution.MidOW42ExactOpt


namespace QuantumComputation.Specs.PhotochemistrySolution.Bf33K9WRouter258

open scoped Matrix Circuit.Notation BigOperators
open Operator QProg Matrix Circuit Qubit HermitianMat
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate (T TOFF)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
/-! ### 1. Definitional Spine Split of `uniTree3_9_k9` + `0-T` Prep & Uncompute `PrimTree`s -/

/-!
### 3. `6-T` W-Router Subcircuit `pBfRouter6` , `34-T` `pStep2bWRouter34` , & `Butterfly33K9Pkg 258`
-/

theorem supportedOn_mkKetOpW_bf {W n : ℕ} (rWork : QRegister W n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    {P : BitAssignment n → Prop}
    (hP : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → P (st δ)) :
    SupportedOn P (mkKetOpW rWork st ph) := fun A B hAB ↦ by
  apply matrix_ext_ket
  intro δ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hAB (st δ) (hP δ hz)]
  · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem zmod2_bool_mul (a b : Bool) :
    ((if a then (1 : ZMod 2) else 0) * (if b then 1 else 0)) = if (a && b) then 1 else 0 := by
      cases a <;> cases b <;> decide
theorem zmod2_self_cancel (b : Bool) : ((if b then (1 : ZMod 2) else 0) + (if b then 1 else 0)) =
    0 := by cases b <;> decide
theorem z2_bf6_oneHot (l f1 f2 : ZMod 2) (hnb : ¬(f1 = 1 ∧ f2 = 1)) :
    let v :=
        ((0 + if l = 1 then 2 ^ 0 else 0) + if f1 = 1 then 2 ^ 1 else 0) + if f2 =
        1 then 2 ^ 2 else 0
    v < 6 ∧ (0 : ZMod 2) + (if v = 3 then 1 else 0) = f1 * l ∧ (0 : ZMod 2) +
        (if v = 5 then 1 else 0) = f2 * l := by
  revert l f1 f2 hnb
  decide
abbrev bfIdx3 {n : ℕ} (rBasis9 : QRegister 9 n) (rCopy30 : QRegister 30 n) : Fin 3 → Wire n
  | ⟨0, _⟩ => rCopy30 ⟨2, by decide⟩
  | ⟨1, _⟩ => rBasis9 ⟨0, by decide⟩
  | ⟨2, _⟩ => rBasis9 ⟨8, by decide⟩

theorem stepCB_update_disj {w1 N : ℕ} (r1 : QRegister w1 N)
    (f : BitAssignment w1 → BitAssignment w1) (β : BitAssignment N) (w : Wire N) (val : ZMod 2)
    (hw : ∀ u : Fin w1, r1 u ≠ w) : stepCB r1 f (Function.update β w val) =
    Function.update (stepCB r1 f β) w val := by
  funext z
  have hfEq : (fun k ↦ Function.update β w val (r1 k)) = (fun k ↦ β (r1 k)) :=
    funext fun k ↦ Function.update_of_ne (hw k) val β
  by_cases hz : z = w
  · subst hz; rw [Function.update_self]; unfold stepCB
    rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ hw u hu), Function.update_self]
  · rw [Function.update_of_ne hz]; unfold stepCB
    by_cases hm : ∃ u : Fin w1, r1 u = z
    · obtain ⟨u, rfl⟩ := hm; rw [writeReg_apply_reg, writeReg_apply_reg, hfEq]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hm, writeReg_apply_of_not_mem _ _ _ _ hm,
          Function.update_of_ne hz]
end QuantumComputation.Specs.PhotochemistrySolution.Bf33K9WRouter258
end

namespace QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW322
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (totDimCompactGen)
attribute [local reducible] totDimCompactGen
theorem hDLayout_eq_7298_w322 : dLayout = 7298 := rfl
/-!
## Part 1: `circWires_cOut40Scrub3_w322` , `rPermElec322` , & `pLoadEAlwaysLoW322` (`322 ≤ wWork`,
`0` extra T)
-/
end QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW322

end
