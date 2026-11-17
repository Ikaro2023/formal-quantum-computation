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

public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn

/-!
# Shared Basis-Ket, Binary Split, `tableXorUnitary`, & `sawtoothFn` Helpers
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.InnerTable
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Real Solution.CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

local instance (priority := 100000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-- Re-export of `CleanDyn.CleanRealizes` (`rfl`-identical 4-conjunct clean-ancilla `wp`
realization predicate). -/
abbrev CleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N) : Prop :=
  Solution.CleanDyn.CleanRealizes v rAct rScr U P

/-! ## Section 1: Register Relocation, Basis-Ket Algebra, `bitPermUnitary`, & Buffer Absorption -/

theorem qreg_ext {k n : ℕ} {r₁ r₂ : QRegister k n}
    (h : ∀ i : Fin k, (r₁ i).val = (r₂ i).val) : r₁ = r₂ :=
  QRegister.ext (Function.Embedding.ext fun i ↦ Fin.ext (h i))

theorem concat_compose_block_left {N k s : ℕ}
    (rAct : QRegister k N) (rScr : QRegister s N) (h : rAct.DisjointWires rScr)
    (hk : 0 + k ≤ k + s := by omega) :
    (rAct.concat rScr h).compose (QRegister.block 0 k hk) = rAct :=
  qreg_ext fun i ↦ by
    have hb : QRegister.block 0 k hk i = Fin.castAdd s i := Fin.ext (by simp)
    simp [hb]

theorem concat_compose_block_right {N k s : ℕ}
    (rAct : QRegister k N) (rScr : QRegister s N) (h : rAct.DisjointWires rScr)
    (hs : k + s ≤ k + s := le_rfl) :
    (rAct.concat rScr h).compose (QRegister.block k s hs) = rScr :=
  qreg_ext fun j ↦ by
    have hb : QRegister.block k s hs j = Fin.natAdd k j := Fin.ext (by simp)
    simp [hb]

@[simp]
theorem basisBits_symm_apply {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[simp]
theorem symm_basisBits_apply {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

theorem single_eq_ket {n : ℕ} (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket, basisState]

theorem matrix_ext_ket {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

/-! ## Section 2: `tableXorUnitary`, `ctrlTableXorUnitary`, & Sawtooth Unary-Iteration QROMs -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.InnerTable
