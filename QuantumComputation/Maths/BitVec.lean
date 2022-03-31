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

public import Mathlib.Data.Nat.Notation
public meta import Qq.MetaM
public meta import Std.Do.Triple.SpecLemmas
import Qq.Macro
import Qq.Match
import Qq.Typ

/-!
# Bit-packed `BitVec` tables

Fixed-width chunk extraction (`BitVec.getChunk`, `BitVec.getChunk₂`) and the `pack_bitvec%`
elaborator, which packs nested `#[…]` or `[…]` literals of natural numbers into a single
`BitVec (d₁ * ⋯ * dₖ * w)` backed by one raw `Nat` literal in the `.olean` file.

Both construction (`Nat.lt_two_pow_of_shiftRight_eq_zero` with `rfl`) and extraction
(`BitVec.extractLsb'`) shift on `Nat` rather than reducing `% 2 ^ totalWidth`, avoiding
`exponentiation.threshold` on multi-kilobyte bitvectors while keeping `O(1)`-step kernel
reduction via `rfl`.
-/

@[expose] public section

/-- If shifting `x` right by `n` bits gives `0`, then `x < 2 ^ n`. Unlike `decide` on `x < 2 ^ n`,
kernel reduction of `x >>> n = 0` uses GMP bit-shifts without evaluating `2 ^ n`, avoiding
`exponentiation.threshold` for large `n`. -/
theorem Nat.lt_two_pow_of_shiftRight_eq_zero {x n : ℕ} (h : x >>> n = 0) : x < 2 ^ n := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos n)).mp h

namespace BitVec

/-- Extract the `i`-th `w`-bit chunk (least-significant chunk first) of a packed
`BitVec (n * w)`. -/
abbrev getChunk {n w : ℕ} (x : BitVec (n * w)) (i : Fin n) : BitVec w :=
  x.extractLsb' (i.val * w) w

/-- Extract entry `(i, j)` of a row-major packed `m × n` table of `w`-bit chunks. -/
abbrev getChunk₂ {m n w : ℕ} (x : BitVec (m * n * w)) (i : Fin m) (j : Fin n) : BitVec w :=
  x.extractLsb' ((i.val * n + j.val) * w) w

open Qq in
/-- Collect the syntactic multiplicative factors of a width expression `d₁ * ⋯ * dₖ * w` before
`whnf` collapses the product. -/
meta partial def mulFactors (e : Q(ℕ)) : Lean.MetaM (Array ℕ) := do
  match e with
  | ~q($lhs * $rhs) => return (← mulFactors lhs) ++ (← mulFactors rhs)
  | _ =>
    let some n ← (Lean.Meta.evalNat e).run
      | Lean.throwError "expected concrete Nat factor in BitVec width, got {e}"
    return #[n]

/-- Parse nested `#[…]` or `[…]` literal syntax of shape `dims` with entries `< 2 ^ w`. -/
meta def parsePackedTable (dims : List ℕ) (w : ℕ) (stx : Lean.TSyntax `term) :
    Lean.MacroM (Array ℕ) := do
  let bound := 1 <<< w
  let rec go : List ℕ → Lean.TSyntax `term → Array ℕ → Lean.MacroM (Array ℕ)
    | d :: rest, s, acc => do
      let elems ← match s with
        | `(#[ $xs,* ]) | `([ $xs,* ]) => pure xs.getElems
        | _ => Lean.Macro.throwErrorAt s "expected `#[…]` or `[…]` literal"
      if elems.size != d then
        Lean.Macro.throwErrorAt s s!"expected {d} entries from type, got {elems.size}"
      let mut acc := acc
      for x in elems do
        acc ← go rest x acc
      return acc
    | [], s, acc => do
      let `($n:num) := s | Lean.Macro.throwErrorAt s "expected natural-number literal"
      let v := n.getNat
      if v >= bound then
        Lean.Macro.throwErrorAt s s!"entry {v} exceeds {w}-bit bound 2^{w} = {bound}"
      return acc.push v
  go dims stx (Array.mkEmpty (dims.foldl (· * ·) 1))

/-- Pack `vals` of `w`-bit integers (least-significant entry first) into one `ℕ` in
`O(N log N)` limb operations. -/
meta def packWords (vals : Array ℕ) (w : ℕ) : ℕ :=
  let rec go (lo len : ℕ) : ℕ :=
    if len == 0 then 0
    else if len == 1 then vals[lo]!
    else
      let half := len / 2
      go lo half ||| (go (lo + half) (len - half) <<< (half * w))
  termination_by len
  decreasing_by all_goals grind
  go 0 vals.size

/-- Pack a nested `#[…]` or `[…]` table of natural-number literals into a
`BitVec (d₁ * ⋯ * dₖ * w)` as a single kernel `Nat` literal, inferring the table shape
`(d₁, …, dₖ)` and entry bit-width `w` from the expected type. -/
syntax (name := packBitVecStx) "pack_bitvec% " term : term

open Qq in
/-- Elaborator for `pack_bitvec%`. -/
@[term_elab packBitVecStx]
meta def elabPackBitVec : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let `(pack_bitvec% $body:term) := stx | Lean.Elab.throwUnsupportedSyntax
  let some expectedType := expectedType?
    | Lean.throwError "pack_bitvec% requires an expected type `BitVec (d₁ * ⋯ * dₖ * w)`"
  let expectedType ← Lean.instantiateMVars expectedType
  let some expectedTypeQ ← checkTypeQ expectedType q(Type)
    | Lean.throwError "pack_bitvec% expected `BitVec (d₁ * ⋯ * dₖ * w)`, got {expectedType}"
  let ~q(BitVec $totalExpr) := expectedTypeQ
    | Lean.throwError "pack_bitvec% expected `BitVec (d₁ * ⋯ * dₖ * w)`, got {expectedType}"
  let factors ← mulFactors totalExpr
  if factors.size < 2 then
    Lean.throwError
      "expected BitVec width of form `d₁ * ⋯ * dₖ * w` (at least 2 factors), got {factors}"
  let w := factors.back!
  let vals ← Lean.Elab.liftMacroM <| parsePackedTable factors.pop.toList w body
  have xLit : Q(ℕ) := Lean.mkRawNatLit (packWords vals w)
  have zeroEq : Q($xLit >>> $totalExpr = 0) := (q(Eq.refl 0) : Lean.Expr)
  return q(BitVec.ofFin ⟨$xLit, Nat.lt_two_pow_of_shiftRight_eq_zero $zeroEq⟩)

end BitVec

