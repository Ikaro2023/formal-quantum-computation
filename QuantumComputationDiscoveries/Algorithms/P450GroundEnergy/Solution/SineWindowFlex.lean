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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SineQPE
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradAdder
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroverUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SineWindowPrep

/-!
# Zero-Extra-Persistent-Qubit Flexible `16`-Qubit Sine-Window Preparations (`SineWindowFlex`)

Constructs and verifies `0`-extra-persistent-qubit `16`-qubit Luis–Peřina half-shift sine-window
`DynamicCircuit` preparations (`CleanDyn.CleanRealizes v r r_scr uWinImpl_M ...`)
for reduced QPE walk lengths `M ∈ {48895, 48383, 48255}` (`L = M + 1 ∈ {48896, 48384, 48256}`),
borrowing at most `8 ≤ 16` temporary-AND scratch wires cleanly from `r_scr` (`0` `.TOFF` gates,
`< 2,120` `T` gates, and `≤ 51 / 10 ^ 11` operator-norm error).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SineWindowFlex
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Real
open scoped Matrix Matrix.Norms.L2Operator BigOperators

/-! ## Section 1: Gate-Word Bridge & Stage-1 Grover Ideal Unitary + `col0` Verifier -/

/-- Optionally conjugate `p : DynamicCircuit Var N` by `Circuit.X q` when `neg = true`. -/
def optConjX {Var : Type} {N : ℕ} (neg : Bool) (q : ℕ) (hq : q < N)
    (p : DynamicCircuit Var N) : DynamicCircuit Var N :=
  if neg then OuterWeights.GroverUniform.conjXBlock q hq p else p

@[simp]
theorem count_optConjX_toff {Var : Type} {N : ℕ} (neg : Bool) (q : ℕ) (hq : q < N)
    (p : DynamicCircuit Var N) :
    (optConjX neg q hq p).count PrimitiveGate.TOFF = p.count PrimitiveGate.TOFF := by
  cases neg <;> simp [optConjX]

@[simp]
theorem count_optConjX_t {Var : Type} {N : ℕ} (neg : Bool) (q : ℕ) (hq : q < N)
    (p : DynamicCircuit Var N) :
    (optConjX neg q hq p).count PrimitiveGate.T = p.count PrimitiveGate.T := by
  cases neg <;> simp [optConjX]

/-- Declarative temporary-AND + `CZ` tree on `k` active wires `0 .. k - 1`, allocating fresh
temporary-AND scratch wires `k, k + 1, ...` up to ambient width `N = k + numScr`. -/
inductive PhaseTree : ℕ → Type where
  /-- Leaf `CZ` on wires `i₁ ≠ i₂` of `Fin k`, optionally conjugating either wire by `X`. -/
  | cz {k : ℕ} (i₁ i₂ : Fin k) (hi : i₁ ≠ i₂) (neg₁ neg₂ : Bool) : PhaseTree k
  /-- Allocate wire `k` as `anc := (γ i₁ ⊕ neg₁) ∧ (γ i₂ ⊕ neg₂)` and continue on `k + 1` wires. -/
  | sand {k : ℕ} (i₁ i₂ : Fin k) (hi : i₁ ≠ i₂) (neg₁ neg₂ : Bool) (rest : PhaseTree (k + 1)) :
      PhaseTree k

/-- Number of temporary-AND scratch wires allocated by `t : PhaseTree k`. -/
def PhaseTree.numScr : {k : ℕ} → PhaseTree k → ℕ
  | _, .cz .. => 0
  | _, .sand _ _ _ _ _ rest => rest.numScr + 1

/-- Compile `t : PhaseTree k` into a `DynamicCircuit Var N` where `k + t.numScr = N`. -/
def PhaseTree.toDyn {Var : Type} {N : ℕ} (v : Var) :
    {k : ℕ} → (t : PhaseTree k) → (hN : k + t.numScr = N) → DynamicCircuit Var N
  | _, .cz i₁ i₂ hi neg₁ neg₂, hN =>
      optConjX neg₁ i₁.val (by dsimp [numScr] at hN; omega) <|
      optConjX neg₂ i₂.val (by dsimp [numScr] at hN; omega) <|
      .circuit (OuterWeights.GroverUniform.czCircuit
        ⟨i₁.val, by dsimp [numScr] at hN; omega⟩
        ⟨i₂.val, by dsimp [numScr] at hN; omega⟩
        (by simp only [ne_eq, Fin.mk.injEq]; exact Fin.val_ne_of_ne hi))
  | k, .sand i₁ i₂ hi neg₁ neg₂ rest, hN =>
      have hN' : (k + 1) + rest.numScr = N := by dsimp [numScr] at hN; omega
      optConjX neg₁ i₁.val (by omega) <|
      optConjX neg₂ i₂.val (by omega) <|
      OuterWeights.GroverUniform.andSandBlock v i₁.val i₂.val k (by omega) (by omega) (by omega)
        (Fin.val_ne_of_ne hi) (rest.toDyn v hN')

@[simp]
theorem PhaseTree.count_toff {Var : Type} {N k : ℕ} (v : Var) (t : PhaseTree k)
    (hN : k + t.numScr = N) :
    (t.toDyn v hN).count PrimitiveGate.TOFF = 0 := by
  induction t with
  | cz => simp [PhaseTree.toDyn]
  | sand _ _ _ _ _ rest ih => simp [PhaseTree.toDyn, ih]

@[simp]
theorem PhaseTree.count_t {Var : Type} {N k : ℕ} (v : Var) (t : PhaseTree k)
    (hN : k + t.numScr = N) :
    (t.toDyn v hN).count PrimitiveGate.T = 4 * t.numScr := by
  induction t with
  | cz => simp [PhaseTree.toDyn, PhaseTree.numScr]
  | sand _ _ _ _ _ rest ih =>
      simp only [PhaseTree.toDyn, count_optConjX_t, OuterWeights.GroverUniform.count_andSandBlock_t,
        ih,
        PhaseTree.numScr]
      omega

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SineWindowFlex
