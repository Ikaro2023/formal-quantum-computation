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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectArithBase

/-!
# Fast `RawOp` Compiler & Primitive `Bool` CPS Evaluator (`SelectRawOps`)

Provides `RawOp`, `compileRawOps`, `evalRawRevFast`, `allPow2`, and `check_compileRawOps_of_fast`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open BlockEncodingCore

open Operator Matrix Circuit QProg CleanDyn HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! #### Fast `O(s)` List Evaluators for `TempProg` (Avoiding Nested `Fin.snoc` Closures) -/

/-- Structural conversion of `x : Fin k → Bool` into a `k`-element `List Bool`. -/
def bitsToList : {k : ℕ} → (Fin k → Bool) → List Bool
  | 0, _ => []
  | _ + 1, x => x 0 :: bitsToList (fun i ↦ x i.succ)

private theorem bitsToList_snoc :
    ∀ {k : ℕ} (x : Fin k → Bool) (b : Bool),
      bitsToList (Fin.snoc x b) = bitsToList x ++ [b]
  | 0, _, _ => rfl
  | k + 1, x, b => by
      simp only [bitsToList, List.cons_append]
      refine congrArg₂ List.cons ?_ ?_
      · exact Fin.snoc_castSucc (α := fun _ ↦ Bool) b x 0
      · have hfun : (fun i : Fin (k + 1) ↦ Fin.snoc (α := fun _ ↦ Bool) x b i.succ) =
            Fin.snoc (α := fun _ ↦ Bool) (fun j : Fin k ↦ x j.succ) b := by
          funext i
          induction i using Fin.lastCases with
          | last =>
              have hl : (Fin.last k).succ = Fin.last (k + 1) := Fin.ext rfl
              rw [hl, Fin.snoc_last, Fin.snoc_last]
          | cast j =>
              have hj : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
              rw [hj, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact (congrArg bitsToList hfun).trans (bitsToList_snoc (fun j ↦ x j.succ) b)

private theorem bitsToList_getD :
    ∀ {k : ℕ} (x : Fin k → Bool) (i : Fin k), (bitsToList x).getD i.val false = x i
  | 0, _, i => Fin.elim0 i
  | _ + 1, x, i => by
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact bitsToList_getD (fun u ↦ x u.succ) j

/-- Symbolic list-based evaluator for `TempProg` (no `Fin.snoc` closure nesting). -/
def TempProg.evalListSym : {k_in k_out s : ℕ} → TempProg k_in k_out s → List Bool → List Bool
  | _, _, _, .nil, xs => xs
  | _, _, _, .linear terms neg rest, xs =>
      rest.evalListSym (xs ++ [terms.foldl (fun acc i ↦ xor acc (xs.getD i.val false)) neg])
  | _, _, _, .andGate i₁ i₂ _ rest, xs =>
      rest.evalListSym (xs ++ [xs.getD i₁.val false && xs.getD i₂.val false])

theorem TempProg.evalListSym_bitsToList {k_in k_out s : ℕ} (p : TempProg k_in k_out s)
    (x : Fin k_in → Bool) :
    p.evalListSym (bitsToList x) = bitsToList (p.evalBits x) := by
  induction p with
  | nil => rfl
  | linear terms neg _ ih =>
      dsimp only [TempProg.evalListSym, TempProg.evalBits]
      have hfold : terms.foldl (fun acc i ↦ xor acc ((bitsToList x).getD i.val false)) neg =
          terms.foldl (fun acc i ↦ xor acc (x i)) neg := by
        congr 1; funext acc i; rw [bitsToList_getD]
      rw [hfold, ← bitsToList_snoc, ih]
  | andGate _ _ _ _ ih =>
      dsimp only [TempProg.evalListSym, TempProg.evalBits]
      rw [bitsToList_getD, bitsToList_getD, ← bitsToList_snoc, ih]

theorem TempProg.evalBits_eq_evalListSym {k_in k_out s : ℕ} (p : TempProg k_in k_out s)
    (x : Fin k_in → Bool) (j : Fin k_out) :
    p.evalBits x j = (p.evalListSym (bitsToList x)).getD j.val false := by
  rw [TempProg.evalListSym_bitsToList, bitsToList_getD]

/-- Strict little-endian `k`-bit list of `n : ℕ` with literal `Bool` elements for fast `decide`. -/
def bitsListOfNat : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n =>
      match decide (n % 2 = 1) with
      | true => true :: bitsListOfNat k (n / 2)
      | false => false :: bitsListOfNat k (n / 2)

private theorem bitsToList_bitsOfFin :
    ∀ (k : ℕ) (c : Fin (2 ^ k)), bitsToList (bitsOfFin k c) = bitsListOfNat k c.val
  | 0, _ => rfl
  | k + 1, c => by
      dsimp only [bitsToList, bitsListOfNat]
      have h0 : bitsOfFin (k + 1) c 0 = decide (c.val % 2 = 1) := by
        rw [bitsOfFin_eq_div_mod]; simp
      have hrest : (fun j : Fin k ↦ bitsOfFin (k + 1) c j.succ) =
          bitsOfFin k ⟨c.val / 2, by
            have := c.isLt
            have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
            omega⟩ := by
        funext j
        rw [bitsOfFin_eq_div_mod, bitsOfFin_eq_div_mod]
        have hdiv : c.val / 2 ^ (j.val + 1) = c.val / 2 / 2 ^ j.val := by
          have hp : 2 ^ (j.val + 1) = 2 * 2 ^ j.val := by ring
          rw [hp, ← Nat.div_div_eq_div_mul]
        simp only [Fin.val_succ, hdiv]
      rw [h0, hrest, bitsToList_bitsOfFin k]
      cases decide (c.val % 2 = 1) <;> rfl

/-- Untyped temporary-wire operation compiled into `TempProg` by `compileRawOps`. -/
inductive RawOp where
  | linear (terms : List ℕ) (neg : Bool)
  | andGate (i₁ i₂ : ℕ)

/-- Output wire count after compiling `ops : List RawOp` from `k` initial wires. -/
abbrev rawOutLen (k : ℕ) : List RawOp → ℕ
  | [] => k
  | _ :: rest => rawOutLen (k + 1) rest

/-- Compile a `List RawOp` into a typed `TempProg k (rawOutLen k ops) ops.length`. -/
def compileRawOps (k : ℕ) : (ops : List RawOp) → TempProg k (rawOutLen k ops) ops.length
  | [] => .nil
  | .linear terms neg :: rest =>
      let termsFin : List (Fin k) := terms.filterMap fun idx ↦
        if h : idx < k then some ⟨idx, h⟩ else none
      .linear termsFin neg (compileRawOps (k + 1) rest)
  | .andGate i₁ i₂ :: rest =>
      let tail := compileRawOps (k + 1) rest
      if h : i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then
        .andGate ⟨i₁, h.1⟩ ⟨i₂, h.2.1⟩ (by intro heq; exact h.2.2 (congrArg Fin.val heq)) tail
      else
        .linear [] false tail

private theorem bitsToList_length :
    ∀ {k : ℕ} (x : Fin k → Bool), (bitsToList x).length = k
  | 0, _ => rfl
  | _ + 1, x => by simp [bitsToList, bitsToList_length]

theorem list_getD_ge_length :
    ∀ (xs : List Bool) (idx : ℕ), xs.length ≤ idx → xs.getD idx false = false
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: tl, idx + 1, h => list_getD_ge_length tl idx (by simp at h; omega)

theorem foldl_filterMap_fin_eq :
    ∀ (terms : List ℕ) (xs : List Bool) (init : Bool),
      (terms.filterMap fun idx ↦
        if h : idx < xs.length then some (⟨idx, h⟩ : Fin xs.length) else none).foldl
          (fun acc i ↦ xor acc (xs.getD i.val false)) init =
      terms.foldl (fun acc idx ↦ xor acc (xs.getD idx false)) init
  | [], _, _ => rfl
  | idx :: tl, xs, init => by
      simp only [List.filterMap_cons, List.foldl_cons]
      by_cases h : idx < xs.length
      · rw [dite_eq_left h]
        simp only [List.foldl_cons]
        exact foldl_filterMap_fin_eq tl xs _
      · rw [dite_eq_right h, list_getD_ge_length xs idx (by omega)]
        have hxor : xor init false = init := by cases init <;> rfl
        rw [hxor]
        exact foldl_filterMap_fin_eq tl xs init

/-- Direct `AND`-count on `List RawOp` without unfolding `TempProg` indexed recursion. -/
def numAndsRawOps (k : ℕ) : List RawOp → ℕ
  | [] => 0
  | .linear _ _ :: rest => numAndsRawOps (k + 1) rest
  | .andGate i₁ i₂ :: rest =>
      (if i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then 1 else 0) + numAndsRawOps (k + 1) rest

theorem numAnds_compileRawOps :
    ∀ (ops : List RawOp) (k : ℕ), (compileRawOps k ops).numAnds = numAndsRawOps k ops
  | [], _ => rfl
  | .linear _ _ :: rest, k => numAnds_compileRawOps rest (k + 1)
  | .andGate i₁ i₂ :: rest, k => by
      dsimp only [compileRawOps, numAndsRawOps]
      by_cases h : i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂
      · rw [dite_eq_left h, ite_eq_left h]
        dsimp only [TempProg.numAnds]
        rw [numAnds_compileRawOps rest (k + 1)]
      · rw [dite_eq_right h, ite_eq_right h]
        dsimp only [TempProg.numAnds]
        rw [zero_add, numAnds_compileRawOps rest (k + 1)]

/-- Direct symbolic evaluator on `List RawOp` (no `TempProg` indexed family or `Fin` recursion). -/
def evalRawOpsSym : List RawOp → List Bool → List Bool
  | [], xs => xs
  | .linear terms neg :: rest, xs =>
      evalRawOpsSym rest (xs ++ [terms.foldl (fun acc idx ↦ xor acc (xs.getD idx false)) neg])
  | .andGate i₁ i₂ :: rest, xs =>
      let b :=
        if i₁ < xs.length ∧ i₂ < xs.length ∧ i₁ ≠ i₂ then
          xs.getD i₁ false && xs.getD i₂ false
        else false
      evalRawOpsSym rest (xs ++ [b])

theorem evalListSym_compileRawOps :
    ∀ (ops : List RawOp) (k : ℕ) (xs : List Bool),
      k = xs.length →
      (compileRawOps k ops).evalListSym xs = evalRawOpsSym ops xs
  | [], _, _, _ => rfl
  | .linear terms neg :: rest, k, xs, hk => by
      subst hk
      dsimp only [compileRawOps, TempProg.evalListSym, evalRawOpsSym]
      rw [foldl_filterMap_fin_eq]
      exact evalListSym_compileRawOps rest (xs.length + 1) _ (by simp)
  | .andGate i₁ i₂ :: rest, k, xs, hk => by
      subst hk
      dsimp only [compileRawOps, evalRawOpsSym]
      by_cases h : i₁ < xs.length ∧ i₂ < xs.length ∧ i₁ ≠ i₂
      · rw [dite_eq_left h, ite_eq_left h]
        dsimp only [TempProg.evalListSym]
        exact evalListSym_compileRawOps rest (xs.length + 1) _ (by simp)
      · rw [dite_eq_right h, ite_eq_right h]
        dsimp only [TempProg.evalListSym, List.foldl]
        exact evalListSym_compileRawOps rest (xs.length + 1) _ (by simp)

theorem evalBits_compileRawOps_sym (k : ℕ) (ops : List RawOp) (x : Fin k → Bool)
    (j : Fin (rawOutLen k ops)) :
    (compileRawOps k ops).evalBits x j = (evalRawOpsSym ops (bitsToList x)).getD j.val false := by
  rw [TempProg.evalBits_eq_evalListSym,
    evalListSym_compileRawOps ops k (bitsToList x) (bitsToList_length x).symm]

/-- Strict reversed `k`-bit list of `n` (`[b_{k-1}, ..., b_0]` as literal `Bool` constructors). -/
def bitsRevAux : ℕ → ℕ → List Bool → List Bool
  | 0, _, acc => acc
  | k + 1, n, acc =>
      match decide (n % 2 = 1) with
      | true => bitsRevAux k (n / 2) (true :: acc)
      | false => bitsRevAux k (n / 2) (false :: acc)

private theorem bitsRevAux_eq_reverse_append :
    ∀ (k n : ℕ) (acc : List Bool),
      bitsRevAux k n acc = (bitsListOfNat k n).reverse ++ acc
  | 0, _, _ => rfl
  | k + 1, n, acc => by
      dsimp only [bitsRevAux, bitsListOfNat]
      cases decide (n % 2 = 1) <;>
        simp [bitsRevAux_eq_reverse_append k (n / 2), List.append_assoc]

private theorem list_getD_append_left :
    ∀ (xs ys : List Bool) (i : ℕ), i < xs.length → (xs ++ ys).getD i false = xs.getD i false
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => rfl
  | _ :: tl, ys, i + 1, h => list_getD_append_left tl ys i (by simp at h; omega)

private theorem list_getD_append_len :
    ∀ (xs : List Bool) (b : Bool), (xs ++ [b]).getD xs.length false = b
  | [], _ => rfl
  | _ :: tl, b => list_getD_append_len tl b

private theorem list_getD_reverse_sub :
    ∀ (xs : List Bool) (idx : ℕ), idx < xs.length →
      xs.reverse.getD (xs.length - 1 - idx) false = xs.getD idx false
  | [], _, h => by simp at h
  | a :: tl, 0, _ => by
      have hlen : (a :: tl).length - 1 - 0 = tl.reverse.length := by simp
      rw [List.reverse_cons, hlen]
      exact list_getD_append_len tl.reverse a
  | a :: tl, idx + 1, h => by
      have hlt : idx < tl.length := by simp at h; omega
      have hsub : (a :: tl).length - 1 - (idx + 1) = tl.length - 1 - idx := by simp; omega
      rw [List.reverse_cons, hsub,
        list_getD_append_left tl.reverse [a] (tl.length - 1 - idx) (by simp; omega)]
      exact list_getD_reverse_sub tl idx hlt

/-- Lookup wire `idx` inside a reversed wire list `rev` of length `k`. -/
def revLookup (k : ℕ) (rev : List Bool) (idx : ℕ) : Bool :=
  if idx < k then rev.getD (k - 1 - idx) false else false

private theorem revLookup_reverse (xs : List Bool) (idx : ℕ) :
    revLookup xs.length xs.reverse idx = xs.getD idx false := by
  dsimp only [revLookup]
  by_cases h : idx < xs.length
  · rw [ite_eq_left h, list_getD_reverse_sub xs idx h]
  · rw [ite_eq_right h, list_getD_ge_length xs idx (by omega)]

/-- Fast `O(1)`-prepend reversed-list evaluator for `List RawOp` (zero `++` or `List.length`). -/
def evalRawRev (k : ℕ) : List RawOp → List Bool → List Bool
  | [], rev => rev
  | .linear terms neg :: rest, rev =>
      match terms.foldl (fun acc idx ↦ xor acc (revLookup k rev idx)) neg with
      | true => evalRawRev (k + 1) rest (true :: rev)
      | false => evalRawRev (k + 1) rest (false :: rev)
  | .andGate i₁ i₂ :: rest, rev =>
      let b :=
        if i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then
          rev.getD (k - 1 - i₁) false && rev.getD (k - 1 - i₂) false
        else false
      match b with
      | true => evalRawRev (k + 1) rest (true :: rev)
      | false => evalRawRev (k + 1) rest (false :: rev)

/-- Continuation-passing `evalRawRev` so call-by-name `whnf` (`decide`) evaluates the circuit
exactly once per input and passes a literal `List Bool` to `cont`. -/
def evalRawRevCPS (k : ℕ) : List RawOp → List Bool → (List Bool → Bool) → Bool
  | [], rev, cont => cont rev
  | .linear terms neg :: rest, rev, cont =>
      match terms.foldl (fun acc idx ↦ xor acc (revLookup k rev idx)) neg with
      | true => evalRawRevCPS (k + 1) rest (true :: rev) cont
      | false => evalRawRevCPS (k + 1) rest (false :: rev) cont
  | .andGate i₁ i₂ :: rest, rev, cont =>
      let b :=
        if i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then
          rev.getD (k - 1 - i₁) false && rev.getD (k - 1 - i₂) false
        else false
      match b with
      | true => evalRawRevCPS (k + 1) rest (true :: rev) cont
      | false => evalRawRevCPS (k + 1) rest (false :: rev) cont

private theorem evalRawRevCPS_eq :
    ∀ (ops : List RawOp) (k : ℕ) (rev : List Bool) (cont : List Bool → Bool),
      evalRawRevCPS k ops rev cont = cont (evalRawRev k ops rev)
  | [], _, _, _ => rfl
  | .linear terms neg :: rest, k, rev, cont => by
      dsimp only [evalRawRevCPS, evalRawRev]
      cases terms.foldl (fun acc idx ↦ xor acc (revLookup k rev idx)) neg <;>
        exact evalRawRevCPS_eq rest (k + 1) _ cont
  | .andGate i₁ i₂ :: rest, k, rev, cont => by
      dsimp only [evalRawRevCPS, evalRawRev]
      cases (if i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then
        rev.getD (k - 1 - i₁) false && rev.getD (k - 1 - i₂) false else false) <;>
        exact evalRawRevCPS_eq rest (k + 1) _ cont

private theorem evalRawRev_reverse :
    ∀ (ops : List RawOp) (k : ℕ) (xs : List Bool),
      k = xs.length →
      evalRawRev k ops xs.reverse = (evalRawOpsSym ops xs).reverse
  | [], _, _, _ => rfl
  | .linear terms neg :: rest, k, xs, hk => by
      subst hk
      dsimp only [evalRawRev, evalRawOpsSym]
      have hfold : terms.foldl (fun acc idx ↦ xor acc (revLookup xs.length xs.reverse idx)) neg =
          terms.foldl (fun acc idx ↦ xor acc (xs.getD idx false)) neg := by
        congr 1; funext acc idx; rw [revLookup_reverse]
      rw [hfold]
      cases terms.foldl (fun acc idx ↦ xor acc (xs.getD idx false)) neg
      · simpa using evalRawRev_reverse rest (xs.length + 1) (xs ++ [false]) (by simp)
      · simpa using evalRawRev_reverse rest (xs.length + 1) (xs ++ [true]) (by simp)
  | .andGate i₁ i₂ :: rest, k, xs, hk => by
      subst hk
      dsimp only [evalRawRev, evalRawOpsSym]
      have hb : (if i₁ < xs.length ∧ i₂ < xs.length ∧ i₁ ≠ i₂ then
            xs.reverse.getD (xs.length - 1 - i₁) false &&
              xs.reverse.getD (xs.length - 1 - i₂) false
          else false) =
          (if i₁ < xs.length ∧ i₂ < xs.length ∧ i₁ ≠ i₂ then
            xs.getD i₁ false && xs.getD i₂ false
          else false) := by
        by_cases h : i₁ < xs.length ∧ i₂ < xs.length ∧ i₁ ≠ i₂
        · rw [ite_eq_left h, ite_eq_left h,
            list_getD_reverse_sub xs i₁ h.1, list_getD_reverse_sub xs i₂ h.2.1]
        · rw [ite_eq_right h, ite_eq_right h]
      rw [hb]
      cases (if i₁ < xs.length ∧ i₂ < xs.length ∧ i₁ ≠ i₂ then
        xs.getD i₁ false && xs.getD i₂ false else false)
      · simpa using evalRawRev_reverse rest (xs.length + 1) (xs ++ [false]) (by simp)
      · simpa using evalRawRev_reverse rest (xs.length + 1) (xs ++ [true]) (by simp)

private theorem evalRawOpsSym_length :
    ∀ (ops : List RawOp) (k : ℕ) (xs : List Bool),
      xs.length = k → (evalRawOpsSym ops xs).length = rawOutLen k ops
  | [], _, xs, hk => hk
  | .linear _ _ :: rest, k, xs, hk =>
      evalRawOpsSym_length rest (k + 1) _ (by simp [hk])
  | .andGate _ _ :: rest, k, xs, hk =>
      evalRawOpsSym_length rest (k + 1) _ (by simp [hk])

private theorem evalBits_compileRawOps_rev (k : ℕ) (ops : List RawOp) (c : Fin (2 ^ k))
    (j : Fin (rawOutLen k ops)) :
    (compileRawOps k ops).evalBits (bitsOfFin k c) j =
      (evalRawRev k ops (bitsRevAux k c.val [])).getD (rawOutLen k ops - 1 - j.val) false := by
  have hlen_in : (bitsListOfNat k c.val).length = k := by
    rw [← bitsToList_bitsOfFin, bitsToList_length]
  have hlen_out : (evalRawOpsSym ops (bitsListOfNat k c.val)).length = rawOutLen k ops :=
    evalRawOpsSym_length ops k _ hlen_in
  have hrev : (evalRawOpsSym ops (bitsListOfNat k c.val)).reverse =
      evalRawRev k ops (bitsRevAux k c.val []) := by
    rw [bitsRevAux_eq_reverse_append, List.append_nil, evalRawRev_reverse ops k _ hlen_in.symm]
  rw [evalBits_compileRawOps_sym, bitsToList_bitsOfFin,
    ← list_getD_reverse_sub _ j.val (by rw [hlen_out]; exact j.isLt), hlen_out, hrev]

/-- Primitive `Bool` list indexing with `false` fallback (zero `GetElem?` typeclass overhead). -/
def bget : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: tl, i + 1 => bget tl i

theorem bget_eq_getD : ∀ (xs : List Bool) (i : ℕ), bget xs i = xs.getD i false
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: tl, i + 1 => bget_eq_getD tl i

/-- Primitive reversed `k`-bit list of `n` using `Nat.beq` (zero `Prop`/`Decidable` terms). -/
def bitsRevFast : ℕ → ℕ → List Bool → List Bool
  | 0, _, acc => acc
  | k + 1, n, acc =>
      match Nat.beq (n % 2) 1 with
      | true => bitsRevFast k (n / 2) (true :: acc)
      | false => bitsRevFast k (n / 2) (false :: acc)

private theorem bitsRevFast_eq :
    ∀ (k n : ℕ) (acc : List Bool), bitsRevFast k n acc = bitsRevAux k n acc
  | 0, _, _ => rfl
  | k + 1, n, acc => by
      dsimp only [bitsRevFast, bitsRevAux]
      by_cases h : n % 2 = 1
      · rw [Nat.beq_eq.mpr h, decide_eq_true h]
        exact bitsRevFast_eq k (n / 2) (true :: acc)
      · rw [Bool.eq_false_iff.mpr (mt Nat.beq_eq.mp h), decide_eq_false h]
        exact bitsRevFast_eq k (n / 2) (false :: acc)

/-- Binary-tree bounded check over `acc * 2 ^ k + y` (`y < 2 ^ k`), recursion depth `k`. -/
def allPow2 : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, acc, f => f acc
  | k + 1, acc, f =>
      cond (allPow2 k (2 * acc) f) (allPow2 k (2 * acc + 1) f) false

theorem allPow2_true :
    ∀ (k acc : ℕ) (f : ℕ → Bool),
      allPow2 k acc f = true → ∀ y < 2 ^ k, f (acc * 2 ^ k + y) = true
  | 0, acc, f, hall, y, hy => by
      have hy0 : y = 0 := Nat.lt_one_iff.mp hy
      subst hy0; simpa [allPow2] using hall
  | k + 1, acc, f, hall, y, hy => by
      dsimp only [allPow2] at hall
      cases h0 : allPow2 k (2 * acc) f
      · rw [h0] at hall; cases hall
      · rw [h0] at hall
        have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        by_cases hlt : y < 2 ^ k
        · have heq : acc * 2 ^ (k + 1) + y = (2 * acc) * 2 ^ k + y := by rw [hp]; ring
          rw [heq]; exact allPow2_true k (2 * acc) f h0 y hlt
        · have hsub : 2 ^ k + (y - 2 ^ k) = y := Nat.add_sub_of_le (Nat.not_lt.mp hlt)
          have heq : acc * 2 ^ (k + 1) + y = (2 * acc + 1) * 2 ^ k + (y - 2 ^ k) := by
            generalize y - 2 ^ k = d at hsub ⊢
            rw [hp, ← hsub]; ring
          rw [heq]; exact allPow2_true k (2 * acc + 1) f hall (y - 2 ^ k) (by omega)

theorem allPow2_zero_true {k : ℕ} {f : ℕ → Bool} (hall : allPow2 k 0 f = true)
    (x : ℕ) (hx : x < 2 ^ k) : f x = true := by
  simpa using allPow2_true k 0 f hall x hx

/-- Primitive `Bool` equality (avoids `BEq` typeclass projection in kernel reduction). -/
def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Primitive `Bool`-only CPS evaluator (`cond`, `bget`, `Nat.blt`, `Nat.beq`). -/
def evalRawRevFast (k : ℕ) : List RawOp → List Bool → (List Bool → Bool) → Bool
  | [], rev, cont => cont rev
  | .linear terms neg :: rest, rev, cont =>
      match terms.foldl (fun acc idx ↦
          xor acc (cond (Nat.blt idx k) (bget rev (k - 1 - idx)) false)) neg with
      | true => evalRawRevFast (k + 1) rest (true :: rev) cont
      | false => evalRawRevFast (k + 1) rest (false :: rev) cont
  | .andGate i₁ i₂ :: rest, rev, cont =>
      let b :=
        cond (Nat.blt i₁ k && Nat.blt i₂ k && !(Nat.beq i₁ i₂))
          (bget rev (k - 1 - i₁) && bget rev (k - 1 - i₂))
          false
      match b with
      | true => evalRawRevFast (k + 1) rest (true :: rev) cont
      | false => evalRawRevFast (k + 1) rest (false :: rev) cont

private theorem evalRawRevFast_eq :
    ∀ (ops : List RawOp) (k : ℕ) (rev : List Bool) (cont : List Bool → Bool),
      evalRawRevFast k ops rev cont = evalRawRevCPS k ops rev cont
  | [], _, _, _ => rfl
  | .linear terms neg :: rest, k, rev, cont => by
      dsimp only [evalRawRevFast, evalRawRevCPS]
      have hfold : terms.foldl (fun acc idx ↦
            xor acc (cond (Nat.blt idx k) (bget rev (k - 1 - idx)) false)) neg =
          terms.foldl (fun acc idx ↦ xor acc (revLookup k rev idx)) neg := by
        congr 1; funext acc idx
        dsimp only [revLookup]
        rw [bget_eq_getD]
        by_cases h : idx < k
        · rw [ite_eq_left h, show Nat.blt idx k = true from Nat.blt_eq.mpr h]; rfl
        · rw [ite_eq_right h,
            show Nat.blt idx k = false from Bool.eq_false_iff.mpr (mt Nat.blt_eq.mp h)]
          rfl
      rw [hfold]
      cases terms.foldl (fun acc idx ↦ xor acc (revLookup k rev idx)) neg <;>
        exact evalRawRevFast_eq rest (k + 1) _ cont
  | .andGate i₁ i₂ :: rest, k, rev, cont => by
      dsimp only [evalRawRevFast, evalRawRevCPS]
      have hb : cond (Nat.blt i₁ k && Nat.blt i₂ k && !(Nat.beq i₁ i₂))
            (bget rev (k - 1 - i₁) && bget rev (k - 1 - i₂)) false =
          (if i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then
            rev.getD (k - 1 - i₁) false && rev.getD (k - 1 - i₂) false
          else false) := by
        rw [bget_eq_getD, bget_eq_getD]
        by_cases h : i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂
        · have hne_b : Nat.beq i₁ i₂ = false :=
            Bool.eq_false_iff.mpr (mt Nat.beq_eq.mp h.2.2)
          have hb_true : (Nat.blt i₁ k && Nat.blt i₂ k && !(Nat.beq i₁ i₂)) = true := by
            rw [Nat.blt_eq.mpr h.1, Nat.blt_eq.mpr h.2.1, hne_b]; rfl
          rw [ite_eq_left h, hb_true]; rfl
        · have hb_false : (Nat.blt i₁ k && Nat.blt i₂ k && !(Nat.beq i₁ i₂)) = false :=
            Bool.eq_false_iff.mpr fun htr ↦ by
              simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at htr
              exact h ⟨htr.1.1, htr.1.2, fun heq ↦
                Bool.noConfusion ((Nat.beq_eq.mpr heq).symm.trans htr.2)⟩
          rw [ite_eq_right h, hb_false]; rfl
      rw [hb]
      cases (if i₁ < k ∧ i₂ < k ∧ i₁ ≠ i₂ then
        rev.getD (k - 1 - i₁) false && rev.getD (k - 1 - i₂) false else false) <;>
        exact evalRawRevFast_eq rest (k + 1) _ cont

theorem check_compileRawOps_of_fast (k : ℕ) (ops : List RawOp) (c : Fin (2 ^ k))
    (checkFn : (Fin (rawOutLen k ops) → Bool) → Bool)
    (hfast : evalRawRevFast k ops (bitsRevFast k c.val [])
      (fun rev ↦ checkFn (fun j ↦ bget rev (rawOutLen k ops - 1 - j.val))) = true) :
    checkFn ((compileRawOps k ops).evalBits (bitsOfFin k c)) = true := by
  have hfun : (compileRawOps k ops).evalBits (bitsOfFin k c) =
      fun j ↦ bget (evalRawRev k ops (bitsRevAux k c.val []))
        (rawOutLen k ops - 1 - j.val) := by
    funext j
    rw [bget_eq_getD, evalBits_compileRawOps_rev]
  rw [hfun]
  rw [bitsRevFast_eq] at hfast
  exact (evalRawRevCPS_eq ops k (bitsRevAux k c.val []) _).symm.trans
    ((evalRawRevFast_eq ops k (bitsRevAux k c.val []) _).symm.trans hfast)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
