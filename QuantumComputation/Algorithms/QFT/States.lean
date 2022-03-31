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

public import QuantumComputation.Algorithms.QFT.Operators
public import Mathlib.Algebra.Field.ZMod
import QuantumInfo.States.Mixed.MState

/-!
# Quantum Fourier Transform states and product decomposition

This module formalizes the quantum states appearing in Section 7.2 of Feng & Ying (2021):
1. Product states on $n$ qubits (`prodState`).
2. Single-qubit phase states
$|+_\theta\rangle = \frac{1}{\sqrt{2}}(|0\rangle + e^{2\pi i\theta}|1\rangle)$ (`plusPhase`).
3. Binary fraction phases $0.j_k\cdots j_m$ (`binaryFracPhase`).
4. The intermediate states for the inner loop (`innerStateVec`) and outer loop (`outerStateVec`).
5. Action of `hadamardAt` and `controlledPhaseAt` on product states, proving
   the exact step-by-step state evolution of the QFT circuit.
-/

@[expose] public section

open Operator
open scoped Matrix ComplexOrder BigOperators Real

namespace QFT

/-- An $n$-qubit product state vector $\bigotimes_{k=0}^{n-1} |v_k\rangle$, represented in the
computational basis via `basisBits`. -/
noncomputable def prodState (n : ℕ) (v : Fin n → (ZMod 2 → ℂ)) : Fin (2 ^ n) → ℂ :=
  fun j ↦ ∏ k : Fin n, v k (basisBits n j k)

/-- Single-qubit phase state
$|+_\theta\rangle = \frac{1}{\sqrt{2}} (|0\rangle + e^{2\pi i \theta} |1\rangle)$. -/
noncomputable def plusPhase (θ : ℝ) : ZMod 2 → ℂ :=
  fun b ↦ (1 / √2 : ℂ) * Complex.exp (2 * π * Complex.I * (θ * (b.val : ℝ) : ℂ))

/-- Adding a natural number to the phase angle leaves `plusPhase` unchanged ($e^{2\pi i m} = 1$). -/
@[simp]
lemma plusPhase_add_nat (θ : ℝ) (m : ℕ) : plusPhase (θ + m) = plusPhase θ := by
  funext b
  simp only [plusPhase]
  rw [show 2 * (π : ℂ) * Complex.I * ((θ + m : ℝ) * (b.val : ℝ) : ℂ) =
      2 * π * Complex.I * (θ * (b.val : ℝ) : ℂ) +
        ((m * b.val : ℕ) : ℂ) * (2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- The computational basis state $|j\rangle$ is the product state of its basis bits. -/
lemma prodState_basisState (n : ℕ) (j : Fin (2 ^ n)) :
    prodState n (fun k ↦ basisState (basisBits n j k)) = basisState j := by
  funext i
  unfold prodState basisState
  simp only [Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [ite_eq_right hij]
    have hnot : ¬ (∀ k : Fin n, basisBits n i k = basisBits n j k) := by
      intro hall
      exact hij ((basisBits n).injective (funext hall))
    rcases Classical.not_forall.mp hnot with ⟨k, hk⟩
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

/-- Relation between `(-1 : ℤˣ) ^ (a * b)` and `plusPhase ((b.val : ℝ) / 2)`. -/
lemma uzpow_negOne_eq_plusPhase (a b : ZMod 2) :
    (1 / √2 : ℂ) * ↑((-1 : ℤˣ) ^ (a * b)) = plusPhase ((b.val : ℝ) / 2) a := by
  have hab : a * b = ↑(a.val * b.val) := by simp
  rw [hab, uzpow_natCast, plusPhase]
  congr 1
  push_cast
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Action of `hadamardAt n x` on a product state whose `x`-th qubit is `basisState b`. -/
theorem hadamardAt_mulVec_prodState (n : ℕ) (x : Fin n) (v : Fin n → (ZMod 2 → ℂ))
    (b : ZMod 2) (hvx : v x = basisState b) :
    (hadamardAt n x).1 *ᵥ prodState n v =
      prodState n (Function.update v x (plusPhase ((b.val : ℝ) / 2))) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, hadamardAt_apply, prodState]
  let jb := (basisBits n).symm (Function.update (basisBits n i) x b)
  have hjb : basisBits n jb = Function.update (basisBits n i) x b :=
    (basisBits n).apply_symm_apply _
  have h_zero : ∀ j : Fin (2 ^ n), j ≠ jb →
      (if ∀ m ≠ x, basisBits n i m = basisBits n j m then
        (1 / √2 : ℂ) * ↑((-1 : ℤˣ) ^ (basisBits n i x * basisBits n j x)) else 0) *
      (∏ k : Fin n, v k (basisBits n j k)) = 0 := by
    intro j hj
    by_cases hall : ∀ m ≠ x, basisBits n i m = basisBits n j m
    · have hbit : basisBits n j x ≠ b := by
        intro hbx
        apply hj
        apply (basisBits n).injective
        funext m
        rw [hjb]
        by_cases hm : m = x
        · subst hm; simp [hbx]
        · simp [hm, hall m hm]
      have hprod : ∏ k : Fin n, v k (basisBits n j k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ x)
        rw [hvx, basisState, Pi.single_apply, ite_eq_right hbit]
      rw [hprod, mul_zero]
    · rw [ite_eq_right hall, zero_mul]
  rw [Fintype.sum_eq_single jb h_zero]
  have hall : ∀ m ≠ x, basisBits n i m = basisBits n jb m := by
    intro m hm; simp [hjb, hm]
  rw [ite_eq_left hall]
  have hjb_x : basisBits n jb x = b := by simp [hjb]
  rw [hjb_x, uzpow_negOne_eq_plusPhase, ← Finset.mul_prod_erase Finset.univ
    (fun k ↦ Function.update v x (plusPhase ((b.val : ℝ) / 2)) k (basisBits n i k))
    (Finset.mem_univ x), Function.update_self]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ v k (basisBits n jb k)) (Finset.mem_univ x)]
  have hvx_one : v x (basisBits n jb x) = 1 := by
    rw [hvx, hjb_x, basisState, Pi.single_apply, ite_eq_left rfl]
  rw [hvx_one, one_mul]
  apply Finset.prod_congr rfl
  intro k hk
  have hkx : k ≠ x := Finset.ne_of_mem_erase hk
  simp [hjb, hkx]

/-- Action of `controlledPhaseAt n y x k` on a product state whose control qubit `y`
is `basisState b` and target qubit `x` ($x \ne y$) is `plusPhase θ`. -/
theorem controlledPhaseAt_mulVec_prodState (n : ℕ) (y x : Fin n) (k : ℕ)
    (hyx : y ≠ x) (v : Fin n → (ZMod 2 → ℂ)) (b : ZMod 2) (θ : ℝ)
    (hvy : v y = basisState b) (hvx : v x = plusPhase θ) :
    (controlledPhaseAt n y x k).1 *ᵥ prodState n v =
      prodState n (Function.update v x (plusPhase (θ + (b.val : ℝ) / (2 ^ k : ℝ)))) := by
  funext i
  simp only [controlledPhaseAt, diagPhaseUnitary, diagPhaseMatrix, Matrix.mulVec_diagonal,
    prodState]
  by_cases hiy : basisBits n i y = b
  · rw [← Finset.mul_prod_erase Finset.univ (fun m ↦ v m (basisBits n i m)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ
    (fun m ↦ Function.update v x (plusPhase (θ + (b.val : ℝ) / (2 ^ k : ℝ))) m (basisBits n i m))
    (Finset.mem_univ x), Function.update_self, ← mul_assoc]
    congr 1
    · rw [hvx, plusPhase, plusPhase, crPhase, hiy, mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · apply Finset.prod_congr rfl
      intro m hm
      have hmx : m ≠ x := Finset.ne_of_mem_erase hm
      rw [Function.update_of_ne hmx]
  · have hprod_lhs : ∏ m : Fin n, v m (basisBits n i m) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ y)
      rw [hvy, basisState, Pi.single_apply, ite_eq_right hiy]
    have hprod_rhs : ∏ m : Fin n, Function.update v x (plusPhase (θ + (b.val : ℝ) / (2 ^ k : ℝ)))
      m (basisBits n i m) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ y)
      rw [Function.update_of_ne hyx, hvy, basisState, Pi.single_apply, ite_eq_right hiy]
    rw [hprod_lhs, hprod_rhs, mul_zero]

/-!
## Binary fraction phases and intermediate loop states
-/

/-- Binary fraction phase
$0.j_{\ell+1} \cdots j_m = \sum_{s=\ell}^{m-1} j_{s+1} / 2^{s - \ell + 1}$. -/
noncomputable def binaryFracPhase (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      if hm : m < n then
        if m = ℓ.val then
          ((basisBits n j ℓ).val : ℝ) / 2
        else
          binaryFracPhase n j ℓ m + ((basisBits n j ⟨m, hm⟩).val : ℝ) / (2 ^ (m - ℓ.val + 1) : ℝ)
      else
        binaryFracPhase n j ℓ m

@[simp]
lemma binaryFracPhase_start (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) :
    binaryFracPhase n j ℓ (ℓ.val + 1) = ((basisBits n j ℓ).val : ℝ) / 2 := by
  rw [binaryFracPhase, dite_eq_left ℓ.isLt, ite_eq_left rfl]

lemma binaryFracPhase_step (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n)
    {m : ℕ} (hℓm : ℓ.val < m) (hm : m < n) :
    binaryFracPhase n j ℓ (m + 1) =
      binaryFracPhase n j ℓ m + ((basisBits n j ⟨m, hm⟩).val : ℝ) / (2 ^ (m - ℓ.val + 1) : ℝ) := by
  rw [binaryFracPhase, dite_eq_left hm, ite_eq_right (by omega)]

/-- Qubit factors for the outer loop state at outer index `ℓ`. -/
noncomputable def outerQubitVec (n : ℕ) (j : Fin (2 ^ n)) (ℓ : ℕ) (k : Fin n) :
    ZMod 2 → ℂ :=
  if k.val < ℓ then
    plusPhase (binaryFracPhase n j k n)
  else
    basisState (basisBits n j k)

/-- State vector of register $\bar{q}$ at outer loop step $x = \ell + 1$:
$\bigotimes_{k=1}^{\ell-1} |+_{0.j_k\cdots j_n}\rangle \otimes \bigotimes_{k=\ell}^n |j_k\rangle$.
-/
noncomputable def outerStateVec (n : ℕ) (j : Fin (2 ^ n)) (ℓ : ℕ) :
    Fin (2 ^ n) → ℂ :=
  prodState n (outerQubitVec n j ℓ)

/-- Qubit factors for the inner loop state at outer index `ℓ` and inner index `m`. -/
noncomputable def innerQubitVec (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) (m : ℕ) :
    Fin n → ZMod 2 → ℂ :=
  Function.update (outerQubitVec n j ℓ.val) ℓ (plusPhase (binaryFracPhase n j ℓ m))

/-- State vector of register $\bar{q}$ at inner loop step $(x = \ell + 1, y = m + 1)$:
$\bigotimes_{k=1}^{\ell-1} |+_{0.j_k\cdots j_n}\rangle \otimes |+_{0.j_\ell\cdots j_{m-1}}\rangle
\otimes \bigotimes_{k=\ell+1}^n |j_k\rangle$. -/
noncomputable def innerStateVec (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) (m : ℕ) :
    Fin (2 ^ n) → ℂ :=
  prodState n (innerQubitVec n j ℓ m)

@[simp]
lemma outerStateVec_zero (n : ℕ) (j : Fin (2 ^ n)) :
    outerStateVec n j 0 = basisState j := by
  have h : outerQubitVec n j 0 = fun k ↦ basisState (basisBits n j k) := by
    ext k
    simp [outerQubitVec]
  rw [outerStateVec, h, prodState_basisState]

theorem hadamardAt_outerStateVec (n : ℕ) (j : Fin (2 ^ n)) {ℓ : ℕ} (hℓ : ℓ < n) :
    (hadamardAt n ⟨ℓ, hℓ⟩).1 *ᵥ outerStateVec n j ℓ =
      innerStateVec n j ⟨ℓ, hℓ⟩ (ℓ + 1) := by
  unfold outerStateVec innerStateVec innerQubitVec
  rw [hadamardAt_mulVec_prodState n ⟨ℓ, hℓ⟩ (outerQubitVec n j ℓ) (basisBits n j ⟨ℓ, hℓ⟩)
    (by simp [outerQubitVec]), binaryFracPhase_start]

theorem controlledPhaseAt_innerStateVec (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n)
    {m : ℕ} (hℓm : ℓ.val < m) (hm : m < n) :
    (controlledPhaseAt n ⟨m, hm⟩ ℓ (m - ℓ.val + 1)).1 *ᵥ innerStateVec n j ℓ m =
      innerStateVec n j ℓ (m + 1) := by
  unfold innerStateVec innerQubitVec
  have hyx : (⟨m, hm⟩ : Fin n) ≠ ℓ := Fin.ne_of_gt hℓm
  have hvy : Function.update (outerQubitVec n j ℓ.val) ℓ (plusPhase (binaryFracPhase n j ℓ m))
    ⟨m, hm⟩ = basisState (basisBits n j ⟨m, hm⟩) := by
    simp [hyx, outerQubitVec, show ¬ m < ℓ.val by omega]
  rw [controlledPhaseAt_mulVec_prodState n ⟨m, hm⟩ ℓ (m - ℓ.val + 1) hyx _
    (basisBits n j ⟨m, hm⟩) (binaryFracPhase n j ℓ m) hvy (Function.update_self _ _ _),
    Function.update_idem, binaryFracPhase_step n j ℓ hℓm hm]

theorem innerStateVec_end (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) :
    innerStateVec n j ℓ n = outerStateVec n j (ℓ.val + 1) := by
  unfold innerStateVec outerStateVec innerQubitVec
  congr 1
  funext k
  by_cases hk : k = ℓ
  · subst hk
    simp [outerQubitVec]
  · have hne : k.val ≠ ℓ.val := fun h ↦ hk (Fin.ext h)
    simp [hk, outerQubitVec, show (k.val < ℓ.val) ↔ (k.val < ℓ.val + 1) by omega]

/-- Evolution under `innerLoopUnitary n ℓ m`. -/
theorem innerLoopUnitary_mulVec (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n)
    {m : ℕ} (hℓm : ℓ.val < m) (hm : m ≤ n) :
    (innerLoopUnitary n ℓ m).1 *ᵥ innerStateVec n j ℓ m =
      outerStateVec n j (ℓ.val + 1) := by
  rw [← innerStateVec_end n j ℓ]
  exact loopUnitary_mulVec n _ (innerStateVec n j ℓ) hℓm hm
    (fun k hk hℓk ↦ controlledPhaseAt_innerStateVec n j ℓ hℓk hk)

/-- Evolution under `outerLoopUnitary n ℓ`. -/
theorem outerLoopUnitary_mulVec (n : ℕ) (j : Fin (2 ^ n))
    {ℓ : ℕ} (hℓ : ℓ ≤ n) :
    (outerLoopUnitary n ℓ).1 *ᵥ outerStateVec n j ℓ =
      outerStateVec n j n := by
  refine loopUnitary_mulVec n _ (outerStateVec n j) (Nat.zero_le ℓ) hℓ (fun k hk _ ↦ ?_)
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hadamardAt_outerStateVec n j hk,
    innerLoopUnitary_mulVec n j ⟨k, hk⟩ (Nat.lt_succ_self k) (by omega)]

/-- Complete circuit evolution theorem: `qftUnitary n` maps computational basis state $|j\rangle$
to the Fourier product state $|\psi_j\rangle = \bigotimes_{k=n}^1 |+_{0.j_k\cdots j_n}\rangle$,
where $j_1 \cdots j_n$ are the bits of `j` from most to least significant (`basisBits` of the
bit-reversed index). -/
theorem qftUnitary_mulVec_basis (n : ℕ) (j : Fin (2 ^ n)) :
    (qftUnitary n).1 *ᵥ basisState j =
      prodState n (fun k ↦ plusPhase (binaryFracPhase n (bitRevEquiv n j) k n)) := by
  rw [qftUnitary, qftCircuitUnitaryGen, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    Operator.permutationUnitary_mulVec_single, ← basisState,
    ← outerStateVec_zero n (bitRevEquiv n j), outerLoopUnitary_mulVec n _ (Nat.zero_le n),
    outerStateVec]
  congr 1; ext k; simp [outerQubitVec]

private lemma basisBits_bitRevEquiv_div_two_add (n : ℕ) (j : Fin (2 ^ n)) (s : Fin n) :
    ((basisBits n (bitRevEquiv n j) s).val : ℝ) / 2 + (j.val / 2 ^ (n - s.val) : ℕ) =
      (j.val / 2 ^ (n - (s.val + 1)) : ℕ) / 2 := by
  set q := j.val / 2 ^ (n - (s.val + 1))
  have hbit : (basisBits n (bitRevEquiv n j) s).val = q % 2 := by
    rw [basisBits_bitRevEquiv, basisBits_eq_div_mod]
    simp [ZMod.val_natCast, Fin.val_rev, q]
  have hdiv : j.val / 2 ^ (n - s.val) = q / 2 := by
    rw [show n - s.val = n - (s.val + 1) + 1 by omega, pow_succ, Nat.div_div_eq_div_mul]
  rw [hbit, hdiv]
  conv_rhs => rw [← Nat.mod_add_div q 2]
  push_cast
  ring

/-- Closed form for `binaryFracPhase` on a bit-reversed basis index: adding the integer part
`⌊j / 2^(n - ℓ)⌋` yields `⌊j / 2^(n - m)⌋ / 2^(m - ℓ)`. -/
theorem binaryFracPhase_bitRevEquiv_add_div (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n)
    {m : ℕ} (hℓm : ℓ.val < m) (hm : m ≤ n) :
    binaryFracPhase n (bitRevEquiv n j) ℓ m + (j.val / 2 ^ (n - ℓ.val) : ℕ) =
      (j.val / 2 ^ (n - m) : ℕ) / (2 ^ (m - ℓ.val) : ℝ) := by
  induction m, Nat.succ_le_of_lt hℓm using Nat.le_induction with
  | base =>
      simpa [Nat.add_sub_cancel_left] using basisBits_bitRevEquiv_div_two_add n j ℓ
  | succ k hk ih =>
      have hklt : k < n := by omega
      have hstep := basisBits_bitRevEquiv_div_two_add n j ⟨k, hklt⟩
      dsimp only at hstep
      rw [binaryFracPhase_step n _ ℓ (by omega) hklt, add_right_comm, ih (by omega) hklt.le,
        show k + 1 - ℓ.val = k - ℓ.val + 1 by omega, pow_succ', ← div_div,
        ← add_div, add_comm, hstep, div_div]

/-- Evaluating `plusPhase` at `binaryFracPhase n (bitRevEquiv n j) ℓ n` gives the exact dyadic
phase `j * 2^ℓ / 2^n`. -/
theorem plusPhase_binaryFracPhase_bitRevEquiv (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) :
    plusPhase (binaryFracPhase n (bitRevEquiv n j) ℓ n) =
      plusPhase ((j.val * 2 ^ ℓ.val : ℝ) / (2 ^ n : ℝ)) := by
  rw [← plusPhase_add_nat _ (j.val / 2 ^ (n - ℓ.val)),
    binaryFracPhase_bitRevEquiv_add_div n j ℓ ℓ.isLt le_rfl]
  congr 1
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - ℓ.val) * (2 : ℝ) ^ ℓ.val := by
    rw [← pow_add, Nat.sub_add_cancel ℓ.isLt.le]
  rw [Nat.sub_self, pow_zero, Nat.div_one, hpow, mul_div_mul_right _ _ (by positivity)]

/-- Columns of `qftMatrix n` decompose as the Fourier product states
$|\psi_j\rangle = \bigotimes_{k=n}^1 |+_{0.j_k\cdots j_n}\rangle$, where $j_1 \cdots j_n$ are the
bits of `j` from most to least significant (`basisBits` of the bit-reversed index). -/
theorem qftMatrix_col (n : ℕ) (j : Fin (2 ^ n)) :
    (qftMatrix n).col j =
      prodState n (fun k ↦ plusPhase (binaryFracPhase n (bitRevEquiv n j) k n)) := by
  ext i
  have hsum : ∑ k : Fin n, (basisBits n i k).val * 2 ^ (k : ℕ) = i.val :=
    congrArg Fin.val ((finFunctionFinEquiv (m := 2) (n := n)).apply_symm_apply i)
  have hsqrt : √(2 ^ n : ℝ) = √2 ^ n := by
    simpa using Real.sqrt_prod (Finset.range n) (x := fun _ ↦ (2 : ℝ)) (by simp)
  rw [Matrix.col_apply, prodState]
  simp only [plusPhase_binaryFracPhase_bitRevEquiv]
  simp only [plusPhase, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Complex.exp_sum, qftMatrix, hsqrt, one_div_pow, Complex.ofReal_pow]
  congr 1; congr 1
  trans (2 * π * Complex.I * (j.val : ℂ) / (2 ^ n : ℂ)) *
      ∑ x : Fin n, (((basisBits n i x).val * 2 ^ (x : ℕ) : ℕ) : ℂ)
  · rw [← Nat.cast_sum, hsum]
    push_cast
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    push_cast
    ring

/-- The circuit unitary `qftUnitary n` equals the mathematical QFT matrix `qftMatrix n`. -/
@[simp, norm_cast]
theorem val_qftUnitary (n : ℕ) : (qftUnitary n).1 = qftMatrix n := by
  ext i j
  simpa [basisState] using congrFun ((qftUnitary_mulVec_basis n j).trans (qftMatrix_col n j).symm) i

end QFT
