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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Fixed-Point Arcsine (`arcsin`) Specification

Parameterized specification for reversible fixed-point arcsine
`|y⟩|b⟩|0⟩^⊗m ↦ |y⟩|(b + z(y)) mod 2^k⟩|0⟩^⊗m` (giving `|y⟩|0⟩|0⟩^⊗m ↦ |y⟩|z(y)⟩|0⟩^⊗m` when
`b = 0`), where both the input `y` and output `z(y)` are `k`-bit signed two's-complement
fixed-point numbers in `[-2, 2)` with `1` sign bit, `1` integer bit, and `k - 2` fractional bits
(`Q2.(k-2)` format, scale `2^(-(k-2))`), and `z(y)` approximates `arcsin(y)` within max absolute
error `≤ ε` over all valid inputs `y ∈ [-1, 1]`.

The resource metric is spacetime (`T count * qubits`) over Clifford + `T` with measurements, where
`qubits = 2 * p.k + arcsinAncillas p` is the total number of data and clean ancilla qubits.
`TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as
`4` `T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-- Bit-width and error parameters for reversible fixed-point `arcsin`. -/
structure ArcsinPrec where
  /-- Register bit-width `k` (`Q2.(k-2)` format: `1` sign bit, `1` integer bit, `k - 2` fractional
  bits). -/
  k : ℕ
  /-- Maximum (`L∞`) absolute error bound over `y ∈ [-1, 1]`. -/
  eps : ℝ

/-- `k = 25` instance (`k = 25`, `ε = 1.25e-7`). -/
noncomputable abbrev ArcsinPrec.k25 : ArcsinPrec where
  k := 25
  eps := 1.25e-7

/-!
## Two's-Complement `Q2.(k-2)` Fixed-Point Encoding & Error Predicates
-/

/-- Signed two's-complement integer in `[-2^(k-1), 2^(k-1) - 1]` represented by a `k`-bit basis
index `u : Fin (2 ^ k)`. -/
abbrev twosCompInt {k : ℕ} (u : Fin (2 ^ k)) : ℤ :=
  (BitVec.ofFin u).toInt

/-- Real value in `[-2, 2)` decoded from a `k`-bit two's-complement `Q2.(k-2)` fixed-point basis
index `u : Fin (2 ^ k)` (`1` sign bit, `1` integer bit, and `k - 2` fractional bits). -/
noncomputable def twosCompFixed {k : ℕ} (u : Fin (2 ^ k)) : ℝ :=
  (twosCompInt u : ℝ) / (2 : ℝ) ^ (k - 2)

/-- Absolute-error condition for a `k`-bit `Q2.(k-2)` fixed-point approximation `z` to `arcsin(y)`
within precision `ε`: `|twosCompFixed z - Real.arcsin (twosCompFixed y)| ≤ ε`. -/
def SatisfiesArcsinAbsError {k : ℕ} (ε : ℝ) (y z : Fin (2 ^ k)) : Prop :=
  |twosCompFixed z - Real.arcsin (twosCompFixed y)| ≤ ε

/-- Valid `k`-bit `Q2.(k-2)` inputs satisfying `|twosCompFixed y| ≤ 1`, expressed decidably on
signed integers as `|twosCompInt y| ≤ 2 ^ (k - 2)` (`2^(k-1) + 1` inputs in `[-1, 1]`). -/
def arcsinValidInputs (k : ℕ) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter fun y => |twosCompInt y| ≤ (2 : ℤ) ^ (k - 2)

/-!
## Reversible Lookup-Addition Unitary
-/

/-- Ideal `2k`-qubit unitary `|y⟩|b⟩ ↦ |y⟩|(b + z(y)) mod 2^k⟩` for an output table
`z : Fin (2 ^ k) → Fin (2 ^ k)`. When `b = 0`, this maps `|y⟩|0⟩ ↦ |y⟩|z(y)⟩`. -/
noncomputable abbrev arcsinTableUnitary {k : ℕ}
    (z : Fin (2 ^ k) → Fin (2 ^ k)) : Unitary (2 ^ (2 * k)) :=
  permutationUnitary (equalTableAddPerm z)

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Arcsin.Var where | v deriving DecidableEq, Inhabited

open Arcsin (Var)
open Arcsin.Var (v)

/-- Number of clean ancilla qubits `arcsinProgram` uses at precision `p`. -/
def arcsinAncillas (p : ArcsinPrec) : ℕ := sorry

/-- Parameterized `arcsin` circuit on `2 * p.k` data wires `rData` (`p.k` output wires `b`
followed by `p.k` input wires `y`, matching `finProdFinEquiv`) and `arcsinAncillas p` clean
ancilla wires `rAnc`. -/
def arcsinProgram {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: when `3 ≤ p.k` and `1 / 2^(p.k - 1) ≤ p.eps` (at least
half-ULP `(1/2) · 2^(-(p.k - 2))` grid resolution), there exists an output table `z` whose values
on all valid inputs `y ∈ arcsinValidInputs p.k` approximate `arcsin(y)` within max absolute
error `≤ p.eps`, and `arcsinProgram p` realizes `arcsinTableUnitary z` as an exact clean subroutine
across all disjoint register placements. -/
theorem arcsin_correctness (p : ArcsinPrec)
    (hk : 3 ≤ p.k) (hε : 1 / (2 : ℝ) ^ (p.k - 1) ≤ p.eps) :
    ∃ z : Fin (2 ^ p.k) → Fin (2 ^ p.k),
      (∀ y ∈ arcsinValidInputs p.k, SatisfiesArcsinAbsError p.eps y (z y)) ∧
      ∀ {n : ℕ}
        (rData : QRegister (2 * p.k) n)
        (rAnc : QRegister (arcsinAncillas p) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj (arcsinTableUnitary z)
          (arcsinProgram p rData rAnc).compile := by sorry

/-- `T`-gate count of `arcsinProgram p`, which the cost theorem requires to use no `TOFF` gates. -/
abbrev arcsinTCount {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n) : ℕ :=
  (arcsinProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `arcsinProgram p`, counting all
`2 * p.k + arcsinAncillas p` data and clean ancilla qubits. -/
abbrev arcsinSpacetime {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n) : ℕ :=
  arcsinTCount p rData rAnc * (2 * p.k + arcsinAncillas p)

/-!
## Spacetime Cost Theorem

The cost theorem forbids primitive `TOFF` gates (so every Toffoli must be decomposed into
Clifford + `T` + measurements) and bounds `arcsinSpacetime` (`T count * qubits`) by a closed `ℕ`
constant at `ArcsinPrec.k25`.
-/

/-- `arcsinProgram p` uses no primitive `TOFF` gates and has spacetime cost at most `cost` across
all register placements. -/
def SatisfiesArcsinSpacetimeBound (p : ArcsinPrec) (cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n),
    (arcsinProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      arcsinSpacetime p rData rAnc ≤ cost

/-- Claimed spacetime cost bound for `arcsinProgram .k25`. -/
def arcsinK25ConstCost : ℕ := sorry

theorem arcsin_k25_const_cost :
    SatisfiesArcsinSpacetimeBound .k25 arcsinK25ConstCost := by sorry

end QuantumComputation.Specs
