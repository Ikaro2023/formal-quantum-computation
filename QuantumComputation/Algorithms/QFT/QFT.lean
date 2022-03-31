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

public import QuantumComputation.Algorithms.QFT.Verification
public import Mathlib.CategoryTheory.Category.Basic
public import QuantumComputation.Primitives.Measure
import QuantumInfo.States.Mixed.MState

/-!
# Quantum Fourier Transform program and Hoare correctness theorems

This module provides the user-facing formalization of the Quantum Fourier Transform (QFT)
from Section 7.2 of *Quantum Hoare Logic with Classical Variables* (Feng & Ying, 2021):

1. Concrete QFT program AST (`qftProg`) on $n$ qubits ($d = 2^n$)
   and register-embedded QFT program AST (`qftProgAux`) on an $n$-qubit register `r : QRegister n m`
   inside an $m$-qubit system ($d = 2^m$, e.g. $m = 2n$ for
   $\mathcal{H}_{\bar{q}} \otimes \mathcal{H}_{\bar{q}'}$).
2. Main Hoare correctness theorems for the complete QFT program:
   - General Hoare triple (`qftProg_correct`).
   - Basis state evolution
    $|j\rangle \mapsto |\psi_j\rangle = \bigotimes_{k=n}^1 |+_{0.j_k\cdots j_n}\rangle$
     (`qftProg_correct_basis`, Eq. 1777).
   - Superposition evolution $\sum_j \alpha_j |j\rangle \mapsto \sum_j \alpha_j |\psi_j\rangle$
     (`qftProg_correct_superposition`, Eq. 1798).
   - Maximally entangled state evolution
   $|\alpha\rangle_{\bar{q},\bar{q}'} \mapsto |\beta\rangle_{\bar{q},\bar{q}'}$
     (`qftProgAux_correct_entangled`, Eq. 1802).
-/

@[expose] public section

open Operator QProg.Notation
open scoped Matrix ComplexOrder

namespace QFT

variable {Var : Type} [DecidableEq Var]

/-!
## Concrete $n$-qubit QFT program AST and correctness theorems (Section 7.2)
-/

/-- The complete $n$-qubit Quantum Fourier Transform program `QFT(n)` from Section 7.2, with
`SWAP_n` moved to the front so that it implements `qftMatrix n` in the library's bit order
(qubit `0` least significant): `q *= SWAP_n; x := 1; while x ≤ n do ... end`. -/
noncomputable def qftProg (n : ℕ) (x y : Var) : QProg Var (2 ^ n) :=
  qftProgGen n (hadamardAt n) (controlledPhaseAt n) (swapAllUnitary n) x y

/-- General Hoare correctness triple for `qftProg`: for any postcondition observable `A`,
`⦃ A.conjUnitary (star (qftUnitary n)) ⦄ qftProg n x y ⦃ A ⦄`. -/
theorem qftProg_correct (n : ℕ) (x y : Var) (hxy : x ≠ y) (A : Observable (Fin (2 ^ n))) :
    ⦃ fun _ ↦ A.conjUnitary (star (qftUnitary n)) ⦄
    qftProg n x y
    ⦃ fun _ ↦ A ⦄ :=
  .of_eq_wp
    (wp_qftProgGen_const n (hadamardAt n) (controlledPhaseAt n)
          (swapAllUnitary n) x y hxy A).symm

/-- Hoare correctness triple for computational basis states (Section 7.2 Eq. 1777):
starting from basis state $|j\rangle$ (represented by projector `compProjObs j`), `qftProg`
produces the Fourier basis state $|\psi_j\rangle = \bigotimes_{k=n}^1 |+_{0.j_k\cdots j_n}\rangle$
(represented by projector `pureStateObs (qftUnitary n) j`). -/
theorem qftProg_correct_basis (n : ℕ) (x y : Var) (hxy : x ≠ y) (j : Fin (2 ^ n)) :
    ⦃ fun _ ↦ compProjObs j ⦄
    qftProg n x y
    ⦃ fun _ ↦ pureStateObs (qftUnitary n) j ⦄ := by
  simpa using qftProg_correct n x y hxy (pureStateObs (qftUnitary n) j)

/-- Hoare correctness triple for arbitrary superposition states (Section 7.2 Eq. 1798):
for any unitary `U_prep` preparing state
$|\psi_{\mathrm{in}}\rangle = \sum_j \alpha_j |j\rangle = U_{\mathrm{prep}} |0\rangle$,
running `qftProg` produces the superposition
$|\psi_{\mathrm{out}}\rangle = \sum_j \alpha_j |\psi_j\rangle$. -/
theorem qftProg_correct_superposition (n : ℕ) (x y : Var) (hxy : x ≠ y)
    (U_prep : Unitary (2 ^ n)) :
    ⦃ fun _ ↦ pureStateObs U_prep 0 ⦄
    qftProg n x y
    ⦃ fun _ ↦ pureStateObs (qftUnitary n * U_prep) 0 ⦄ := by
  simpa [← mul_assoc] using qftProg_correct n x y hxy (pureStateObs (qftUnitary n * U_prep) 0)

/-!
## Register embedding and maximally entangled state verification (Section 7.2 Eq. 1802)
-/

/-- The QFT program acting on an $n$-qubit register `r : QRegister n m` inside an $m$-qubit system
(such as the primary register $\bar{q}$ of $\mathcal{H}_{\bar{q}} \otimes \mathcal{H}_{\bar{q}'}$
when $m = 2n$). -/
noncomputable def qftProgAux {n m : ℕ} (r : QRegister n m) (x y : Var) : QProg Var (2 ^ m) :=
  qftProgGen n
    (fun i ↦ r.embedUnitary (hadamardAt n i))
    (fun i j k ↦ r.embedUnitary (controlledPhaseAt n i j k))
    (r.embedUnitary (swapAllUnitary n)) x y

/-- Hoare correctness triple for `qftProgAux` on any multi-qubit observable `A`. -/
theorem qftProgAux_correct {n m : ℕ} (r : QRegister n m) (x y : Var) (hxy : x ≠ y)
    (A : Observable (Fin (2 ^ m))) :
    ⦃ fun _ ↦ A.conjUnitary (star (r.embedUnitary (qftUnitary n))) ⦄
    qftProgAux r x y
    ⦃ fun _ ↦ A ⦄ := by
  apply Triple.of_eq_wp
  unfold qftProgAux
  rw [wp_qftProgGen_const _ _ _ _ x y hxy A]
  simp only [qftUnitary, qftCircuitUnitaryGen, outerLoopUnitaryGen,
    innerLoopUnitaryGen, embedUnitary_loopUnitary, ← r.embedUnitary_mul]

/-- Hoare correctness triple for maximally entangled state preparation (Section 7.2 Eq. 1802):
for any unitary `U_alpha` preparing the maximally entangled state
$|\alpha\rangle_{\bar{q},\bar{q}'}$ from $|0\rangle$, running `qftProgAux` on register `r` produces
the state
$|\beta\rangle_{\bar{q},\bar{q}'} =
\frac{1}{\sqrt{2^n}} \sum_{j=0}^{2^n-1} |\psi_j\rangle_{\bar{q}} |j\rangle_{\bar{q}'}$. -/
theorem qftProgAux_correct_entangled {n m : ℕ} (r : QRegister n m) (x y : Var) (hxy : x ≠ y)
    (U_alpha : Unitary (2 ^ m)) :
    ⦃ fun _ ↦ pureStateObs U_alpha 0 ⦄
    qftProgAux r x y
    ⦃ fun _ ↦ pureStateObs (r.embedUnitary (qftUnitary n) * U_alpha) 0 ⦄ :=
    by
  simpa [← mul_assoc] using
    qftProgAux_correct r x y hxy (pureStateObs (r.embedUnitary (qftUnitary n) * U_alpha) 0)

end QFT
