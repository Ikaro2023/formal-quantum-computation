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

public import QuantumComputation.Algorithms.QFT.States
public import QuantumComputation.Circuits.Toffoli
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MeasuresLowEnergiesAux

/-!
# Luis–Peřina Cosine-Window QPE, Approximate `QFT_16†`, and Parseval Variance Bound
Formalizes the quantum phase estimation (QPE) front-end and back-end subroutines and exact Fourier
variance analysis for Cytochrome P450 Compound I (`P450GroundEnergy`):

1. **Little-Endian `QFT` / `QFT†` Unitary Bridge (`Section 1`):**
   - Proves `QFT.qftMatrix b = (QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b).1` and
     `(QFT.qftMatrix b)ᴴ = (QFT.swapAllUnitary b * (QFT.outerLoopUnitary b 0)⁻¹).1` from
     `QFT.outerLoopUnitary_mulVec`, establishing unitarity of `QFT.qftMatrix b` and
     `(QFT.qftMatrix b)ᴴ` in the repository's little-endian `Fin (2 ^ b)` basis convention.
2. **Exact Parseval Circular Variance Identity & Luis–Peřina `π² / (M + 1)²` Bound (`Section 2`):**
   - Proves the cyclic-shift Parseval identity on `Fin (2 ^ b)` and deduces that for any `b`,
     any `M` with `M + 1 < 2 ^ b`, any real window `c : ℕ → ℝ` normalized on `{0, ..., M}`, and any
     true phase `ψ ∈ ℝ`, measuring `(QFT.qftMatrix b)ᴴ` (or `ζ • (QFT.qftMatrix b)ᴴ` with `‖ζ‖ = 1`)
     on `∑_{m ≤ M} c_m e^{i m ψ} |m⟩` yields exact chordal variance `2 - 2 ∑_{m < M} c_m c_{m+1}`.
   - Defines the half-shift Luis–Peřina sine window `sineWindowCoeff (M + 1)` supported on
     `{0, ..., M}` (requiring only `M` walk steps), proves exact unit normalization, and proves
     `2 - 2 ∑_{m < M} c_m c_{m+1} ≤ π² / (M + 1)²`.
   - Proves Hilbert-space L2 state perturbation and chordal RMS perturbation corollaries under
     approximate window preparation (`δ_win`, with exact zero amplitude on `m > M`) and approximate
     inverse QFT (`δ_qft`, up to any unit-modulus global phase `ζ`), directly matching
     `SineQPE.qpeAngle` and `measuresLowEnergies_of_doubledQPE`.
3. **Parametric & Concrete `.TOFF`-Free Window & `QFT†` Circuits (`Sections 3–4`):**
   - `Section 3A`: Algebraic `ℤ[√2]`/`ℤ[ζ_8]` verifier & `38` Ross–Selinger `Rz`/`Ry` circuits.
   - `Section 3B`: Parametric 1-step exact Grover AA `groverSineWindowDyn` (`unitSineWindowCoeff`).
   - `Section 3C`: Ancilla-free `sineWindow49151Circuit : Circuit 16` (`M = 49,151`, `T = 1,866`).
   - `Section 4`: `iqftCircuitGen`, `iqft16Circuit` (`T = 33,747`), `iqft16Sub5kCircuit` (`4,887`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg Real
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

/-! ## Section 1: Little-Endian `QFT` / `QFT†` Unitary Bridge -/

private theorem sum_basisBits_mul_two_pow (b : ℕ) (j : Fin (2 ^ b)) :
    (∑ k : Fin b, (basisBits b j k).val * 2 ^ k.val) = j.val := by
  induction b with
  | zero =>
      have hj : j.val = 0 := by omega
      rw [hj]
      simp
  | succ b ih =>
      let jDiv : Fin (2 ^ b) := ⟨j.val / 2, by
        have hj := j.isLt
        have hp : 2 ^ (b + 1) = 2 * 2 ^ b := pow_succ' 2 b
        omega⟩
      rw [Fin.sum_univ_succ]
      have h0 : (basisBits (b + 1) j 0).val = j.val % 2 := by
        rw [basisBits_eq_div_mod, Fin.val_zero, pow_zero, Nat.div_one, ZMod.val_natCast,
          Nat.mod_mod_of_dvd _ (by decide)]
      have hsucc (r : Fin b) :
          (basisBits (b + 1) j r.succ).val = (basisBits b jDiv r).val := by
        have hp : 2 ^ (r.val + 1) = 2 * 2 ^ r.val := pow_succ' 2 r.val
        simp only [basisBits_eq_div_mod, Fin.val_succ, hp, ← Nat.div_div_eq_div_mul]
        rfl
      simp_rw [h0, Fin.val_zero, pow_zero, mul_one, hsucc, Fin.val_succ, pow_succ']
      have hmul :
          (∑ x : Fin b, (basisBits b jDiv x).val * (2 * 2 ^ x.val)) =
            2 * ∑ x : Fin b, (basisBits b jDiv x).val * 2 ^ x.val := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hmul, ih jDiv]
      exact Nat.mod_add_div j.val 2

private theorem exp_two_pi_I_nat (q : ℕ) :
    Complex.exp (2 * π * Complex.I * (q : ℂ)) = 1 := by
  rw [show (2 : ℂ) * π * Complex.I * (q : ℂ) =
      (q : ℂ) * (π * Complex.I + π * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring_nf

private theorem binaryFracPhase_eq_fin_sum (n : ℕ) (j : Fin (2 ^ n)) (ℓ : Fin n) :
    ∀ m : ℕ, ℓ.val < m → m ≤ n →
      QFT.binaryFracPhase n j ℓ m =
        ∑ s : Fin n,
          if ℓ.val ≤ s.val ∧ s.val < m then
            ((basisBits n j s).val : ℝ) / (2 ^ (s.val - ℓ.val + 1) : ℝ)
          else 0 := by
  intro m hℓm hm
  induction m with
  | zero => omega
  | succ m' ih =>
      by_cases heq : m' = ℓ.val
      · subst heq
        rw [QFT.binaryFracPhase_start, Fintype.sum_eq_single ℓ]
        · rw [ite_eq_left (by omega)]
          simp
        · intro s hs
          have hne : s.val ≠ ℓ.val := fun h ↦ hs (Fin.ext h)
          have hnot : ¬ (ℓ.val ≤ s.val ∧ s.val < ℓ.val + 1) := by omega
          exact ite_eq_right hnot
      · have hlt : ℓ.val < m' := by omega
        have hlt_n : m' < n := by omega
        rw [QFT.binaryFracPhase_step n j ℓ hlt hlt_n, ih hlt hlt_n.le]
        let sLast : Fin n := ⟨m', hlt_n⟩
        have hsplit :
            (∑ s : Fin n,
              if ℓ.val ≤ s.val ∧ s.val < m' + 1 then
                ((basisBits n j s).val : ℝ) / (2 ^ (s.val - ℓ.val + 1) : ℝ)
              else 0) =
            (∑ s : Fin n,
              if ℓ.val ≤ s.val ∧ s.val < m' then
                ((basisBits n j s).val : ℝ) / (2 ^ (s.val - ℓ.val + 1) : ℝ)
              else 0) +
            ((basisBits n j sLast).val : ℝ) / (2 ^ (m' - ℓ.val + 1) : ℝ) := by
          rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ sLast),
            ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ sLast)]
          have h1 : (if ℓ.val ≤ sLast.val ∧ sLast.val < m' + 1 then
              ((basisBits n j sLast).val : ℝ) / (2 ^ (sLast.val - ℓ.val + 1) : ℝ) else 0) =
              ((basisBits n j sLast).val : ℝ) / (2 ^ (m' - ℓ.val + 1) : ℝ) := by
            simp [sLast, hlt.le]
          have h2 : (if ℓ.val ≤ sLast.val ∧ sLast.val < m' then
              ((basisBits n j sLast).val : ℝ) / (2 ^ (sLast.val - ℓ.val + 1) : ℝ) else 0) = 0 := by
            simp [sLast]
          rw [h1, h2, add_zero]
          congr 1
          refine Finset.sum_congr rfl fun s hs ↦ ?_
          have hs_ne : s.val ≠ m' := fun h ↦ (Finset.ne_of_mem_erase hs) (Fin.ext h)
          by_cases hcond : ℓ.val ≤ s.val ∧ s.val < m'
          · rw [ite_eq_left (by omega), ite_eq_left hcond]
          · rw [ite_eq_right (by omega), ite_eq_right hcond]
        rw [hsplit]

private theorem exp_binaryFracPhase_bitRev (n : ℕ) (j : Fin (2 ^ n)) (k : Fin n) (bval : ℕ) :
    Complex.exp (2 * π * Complex.I *
        ((QFT.binaryFracPhase n (bitRevEquiv n j) k n * (bval : ℝ) : ℝ) : ℂ)) =
      Complex.exp (2 * π * Complex.I *
        ((((j.val * 2 ^ k.val * bval : ℕ) : ℝ) / (2 ^ n : ℝ) : ℝ) : ℂ)) := by
  rw [binaryFracPhase_eq_fin_sum n (bitRevEquiv n j) k n k.isLt le_rfl, Finset.sum_mul]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum, ← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  have hprod :
      (∏ r : Fin n,
        Complex.exp (2 * π * Complex.I *
          ((if k.val ≤ (Fin.rev r).val ∧ (Fin.rev r).val < n then
              ((basisBits n (bitRevEquiv n j) (Fin.rev r)).val : ℂ) /
                (2 : ℂ) ^ ((Fin.rev r).val - k.val + 1)
            else 0) * (bval : ℂ)))) =
      ∏ r : Fin n,
        Complex.exp (2 * π * Complex.I *
          ((((basisBits n j r).val * 2 ^ r.val * 2 ^ k.val * bval : ℕ) : ℂ) / (2 : ℂ) ^ n)) := by
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    rw [basisBits_bitRevEquiv, Fin.rev_rev]
    have hr := r.isLt
    have hk := k.isLt
    have hrev : (Fin.rev r).val = n - (r.val + 1) := Fin.val_rev r
    by_cases hrk : r.val + k.val < n
    · have hcond : k.val ≤ (Fin.rev r).val ∧ (Fin.rev r).val < n := by omega
      rw [ite_eq_left hcond]
      have hexp : (Fin.rev r).val - k.val + 1 = n - (r.val + k.val) := by omega
      have hpow : (2 : ℂ) ^ r.val * (2 : ℂ) ^ k.val * (2 : ℂ) ^ (n - (r.val + k.val)) =
          (2 : ℂ) ^ n := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      congr 1
      have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      have h2sub : (2 : ℂ) ^ (n - (r.val + k.val)) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [hexp]
      push_cast
      apply mul_right_cancel₀ h2n
      calc 2 * (π : ℂ) * Complex.I *
            (((basisBits n j r).val : ℂ) / (2 : ℂ) ^ (n - (r.val + k.val)) * (bval : ℂ)) *
            (2 : ℂ) ^ n
          = 2 * (π : ℂ) * Complex.I * ((basisBits n j r).val : ℂ) * (bval : ℂ) *
              ((2 : ℂ) ^ r.val * (2 : ℂ) ^ k.val) *
              ((2 : ℂ) ^ (n - (r.val + k.val)) / (2 : ℂ) ^ (n - (r.val + k.val))) := by
            rw [← hpow]
            ring
        _ = 2 * (π : ℂ) * Complex.I *
              (((basisBits n j r).val : ℂ) * (2 : ℂ) ^ r.val * (2 : ℂ) ^ k.val * (bval : ℂ)) := by
            rw [div_self h2sub]
            ring
        _ = 2 * (π : ℂ) * Complex.I *
              (((basisBits n j r).val : ℂ) * (2 : ℂ) ^ r.val * (2 : ℂ) ^ k.val * (bval : ℂ) /
                (2 : ℂ) ^ n) * (2 : ℂ) ^ n := by
            field_simp [h2n]
    · have hcond : ¬ (k.val ≤ (Fin.rev r).val ∧ (Fin.rev r).val < n) := by omega
      rw [ite_eq_right hcond, zero_mul, mul_zero, Complex.exp_zero]
      let q : ℕ := (basisBits n j r).val * bval * 2 ^ (r.val + k.val - n)
      have hnat :
          (basisBits n j r).val * 2 ^ r.val * 2 ^ k.val * bval = q * 2 ^ n := by
        dsimp [q]
        have hpow_nat : 2 ^ r.val * 2 ^ k.val = 2 ^ (r.val + k.val - n) * 2 ^ n := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        calc (basisBits n j r).val * 2 ^ r.val * 2 ^ k.val * bval
            = (basisBits n j r).val * (2 ^ r.val * 2 ^ k.val) * bval := by ring
          _ = (basisBits n j r).val * (2 ^ (r.val + k.val - n) * 2 ^ n) * bval := by rw [hpow_nat]
          _ = (basisBits n j r).val * bval * 2 ^ (r.val + k.val - n) * 2 ^ n := by ring
      rw [hnat]
      push_cast
      have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      rw [mul_div_cancel_right₀ _ h2n, exp_two_pi_I_nat]
  have hlhs_cast :
      (∏ x : Fin n,
        Complex.exp (2 * (π : ℂ) * Complex.I *
          (((if k.val ≤ (Fin.rev x).val ∧ (Fin.rev x).val < n then
              ((basisBits n (bitRevEquiv n j) (Fin.rev x)).val : ℝ) /
                (2 : ℝ) ^ ((Fin.rev x).val - k.val + 1)
            else 0 : ℝ) : ℂ) * (bval : ℂ)))) =
      ∏ r : Fin n,
        Complex.exp (2 * (π : ℂ) * Complex.I *
          ((if k.val ≤ (Fin.rev r).val ∧ (Fin.rev r).val < n then
              ((basisBits n (bitRevEquiv n j) (Fin.rev r)).val : ℂ) /
                (2 : ℂ) ^ ((Fin.rev r).val - k.val + 1)
            else 0) * (bval : ℂ))) := by
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    by_cases hc : k.val ≤ (Fin.rev r).val ∧ (Fin.rev r).val < n
    · rw [ite_eq_left hc, ite_eq_left hc]
      push_cast
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc]
      push_cast
      rfl
  rw [hlhs_cast, hprod, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  have hsum_nat :
      (∑ r : Fin n, (basisBits n j r).val * 2 ^ r.val * 2 ^ k.val * bval) =
        j.val * 2 ^ k.val * bval := by
    calc (∑ r : Fin n, (basisBits n j r).val * 2 ^ r.val * 2 ^ k.val * bval)
        = (∑ r : Fin n, (basisBits n j r).val * 2 ^ r.val) * (2 ^ k.val * bval) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = j.val * 2 ^ k.val * bval := by
            rw [sum_basisBits_mul_two_pow]
            ring
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast hsum_nat

private lemma sqrt2_pow_eq_sqrt_two_pow (b : ℕ) : (√2 : ℝ) ^ b = √((2 : ℝ) ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pow_succ, pow_succ, ih, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ b)]

/-- `QFT.swapAllUnitary b` is an involution (`swapAllUnitary b * swapAllUnitary b = 1`). -/
theorem swapAllUnitary_mul_self (b : ℕ) :
    QFT.swapAllUnitary b * QFT.swapAllUnitary b = 1 := by
  apply Subtype.ext
  ext i j
  have hbit (x : Fin (2 ^ b)) : bitRevEquiv b (bitRevEquiv b x) = x := by
    apply (basisBits b).injective
    funext k
    rw [basisBits_bitRevEquiv, basisBits_bitRevEquiv, Fin.rev_rev]
  have hcol :
      ((QFT.swapAllUnitary b * QFT.swapAllUnitary b).1.mulVec (basisState j)) i =
        ((1 : Matrix (Fin (2 ^ b)) (Fin (2 ^ b)) ℂ).mulVec (basisState j)) i := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      Operator.permutationUnitary_mulVec_single,
      Operator.permutationUnitary_mulVec_single, hbit, Matrix.one_mulVec]
  simp only [basisState, Matrix.mulVec_single_one] at hcol
  exact hcol

/-- In the little-endian `Fin (2 ^ b)` basis convention, `QFT.qftMatrix b` equals the unitary
`QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b`. -/
theorem outerLoop_mul_swapAll_eq_qftMatrix (b : ℕ) :
    (QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b).1 = QFT.qftMatrix b := by
  ext i j
  have hcol :
      ((QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b).1.mulVec (basisState j)) i =
        QFT.qftMatrix b i j := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      Operator.permutationUnitary_mulVec_single (bitRevEquiv b) j 1]
    change ((QFT.outerLoopUnitary b 0).1.mulVec (basisState (bitRevEquiv b j))) i = _
    rw [← QFT.outerStateVec_zero b (bitRevEquiv b j),
      QFT.outerLoopUnitary_mulVec b (bitRevEquiv b j) (Nat.zero_le b)]
    have hout : QFT.outerStateVec b (bitRevEquiv b j) b i =
        ∏ k : Fin b,
          (1 / √2 : ℂ) * Complex.exp (2 * π * Complex.I *
            ((QFT.binaryFracPhase b (bitRevEquiv b j) k b *
              ((basisBits b i k).val : ℝ) : ℝ) : ℂ)) := by
      unfold QFT.outerStateVec QFT.prodState QFT.outerQubitVec
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [ite_eq_left k.isLt, QFT.plusPhase]
      push_cast
      rfl
    rw [hout, Finset.prod_mul_distrib]
    have hsqrt : (∏ _k : Fin b, (1 / √2 : ℂ)) = (1 / √(2 ^ b : ℝ) : ℂ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← sqrt2_pow_eq_sqrt_two_pow b]
      push_cast
      exact _root_.one_div_pow (√2 : ℂ) b
    rw [hsqrt, QFT.qftMatrix]
    congr 1
    have hprod_exp :
        (∏ k : Fin b,
          Complex.exp (2 * π * Complex.I *
            ((QFT.binaryFracPhase b (bitRevEquiv b j) k b *
              ((basisBits b i k).val : ℝ) : ℝ) : ℂ))) =
        ∏ k : Fin b,
          Complex.exp (2 * π * Complex.I *
            ((((j.val * 2 ^ k.val * (basisBits b i k).val : ℕ) : ℝ) /
              (2 ^ b : ℝ) : ℝ) : ℂ)) := by
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      exact exp_binaryFracPhase_bitRev b j k (basisBits b i k).val
    rw [hprod_exp, ← Complex.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    have hsum_i :
        (∑ k : Fin b, j.val * 2 ^ k.val * (basisBits b i k).val) = j.val * i.val := by
      calc (∑ k : Fin b, j.val * 2 ^ k.val * (basisBits b i k).val)
          = j.val * ∑ k : Fin b, (basisBits b i k).val * 2 ^ k.val := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ = j.val * i.val := by rw [sum_basisBits_mul_two_pow]
    push_cast
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast hsum_i
  simp only [basisState, Matrix.mulVec_single_one] at hcol
  exact hcol

/-- Bundled `b`-qubit Quantum Fourier Transform unitary whose underlying matrix is literally
`QFT.qftMatrix b`. -/
noncomputable def qftMatrixUnitary (b : ℕ) : Unitary (2 ^ b) :=
  ⟨QFT.qftMatrix b, by
    rw [← outerLoop_mul_swapAll_eq_qftMatrix b]
    exact (QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b).2⟩

@[simp]
theorem qftMatrixUnitary_coe (b : ℕ) :
    (qftMatrixUnitary b).1 = QFT.qftMatrix b := rfl

/-- Bundled `b`-qubit inverse Quantum Fourier Transform unitary whose underlying matrix is
`(QFT.qftMatrix b)ᴴ`. -/
noncomputable def iqftMatrixUnitary (b : ℕ) : Unitary (2 ^ b) :=
  (qftMatrixUnitary b)⁻¹

@[simp]
theorem iqftMatrixUnitary_coe (b : ℕ) :
    (iqftMatrixUnitary b).1 = (QFT.qftMatrix b)ᴴ := by
  change (star (qftMatrixUnitary b)).1 = (QFT.qftMatrix b)ᴴ
  rw [Unitary.coe_star, Matrix.star_eq_conjTranspose, qftMatrixUnitary_coe]

/-- Circuit-order decomposition of `(QFT.qftMatrix b)ᴴ`: `(QFT.outerLoopUnitary b 0)⁻¹` followed
by `QFT.swapAllUnitary b`. -/
theorem swapAll_mul_outerLoopInv_eq_iqftMatrix (b : ℕ) :
    (QFT.swapAllUnitary b * (QFT.outerLoopUnitary b 0)⁻¹).1 = (QFT.qftMatrix b)ᴴ := by
  have hinv : (QFT.swapAllUnitary b)⁻¹ = QFT.swapAllUnitary b :=
    inv_eq_of_mul_eq_one_right (swapAllUnitary_mul_self b)
  calc (QFT.swapAllUnitary b * (QFT.outerLoopUnitary b 0)⁻¹).1
      = ((QFT.swapAllUnitary b)⁻¹ * (QFT.outerLoopUnitary b 0)⁻¹).1 := by rw [hinv]
    _ = ((QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b)⁻¹).1 := by
          rw [← _root_.mul_inv_rev]
    _ = ((QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b).1)ᴴ := by
          change (star (QFT.outerLoopUnitary b 0 * QFT.swapAllUnitary b)).1 = _
          rw [Unitary.coe_star, Matrix.star_eq_conjTranspose]
    _ = (QFT.qftMatrix b)ᴴ := by rw [outerLoop_mul_swapAll_eq_qftMatrix]

/-- Bundled `b`-qubit inverse Quantum Fourier Transform up to a unit-modulus global phase `ζ`
(`‖ζ‖ = 1`), matching `SU(2 ^ b)` Clifford+`T` synthesis directly as a `Unitary (2 ^ b)`. -/
noncomputable def phasedIqftUnitary (b : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) : Unitary (2 ^ b) :=
  ⟨ζ • (QFT.qftMatrix b)ᴴ, by
    have hstar_mul : star ζ * ζ = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hζ]
      norm_num
    have hmul_star : ζ * star ζ = 1 := by rw [mul_comm, hstar_mul]
    rw [Matrix.mem_unitaryGroup_iff]
    change (ζ • (iqftMatrixUnitary b).1) * star (ζ • (iqftMatrixUnitary b).1) = 1
    rw [star_smul, smul_mul_smul_comm, hmul_star, one_smul]
    exact Matrix.mem_unitaryGroup_iff.mp (iqftMatrixUnitary b).2⟩

@[simp]
theorem phasedIqftUnitary_coe (b : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (phasedIqftUnitary b ζ hζ).1 = ζ • (QFT.qftMatrix b)ᴴ := rfl

/-! ## Section 2: Cyclic-Shift Parseval Identity & Luis–Peřina `π² / (M + 1)²` Variance Bound -/

/-- Zero-padded real window state `∑_{m=0}^M c_m |m⟩` in `Fin (2 ^ b) → ℂ`. -/
noncomputable def windowVec (b M : ℕ) (c : ℕ → ℝ) : Fin (2 ^ b) → ℂ :=
  fun m ↦ if m.val ≤ M then (c m.val : ℂ) else 0

/-- Zero-padded phase-modulated window state `∑_{m=0}^M c_m e^{i m ψ} |m⟩` in `Fin (2 ^ b) → ℂ`. -/
noncomputable def windowPhaseVec (b M : ℕ) (c : ℕ → ℝ) (ψ : ℝ) : Fin (2 ^ b) → ℂ :=
  fun m ↦ if m.val ≤ M then (c m.val : ℂ) * Complex.exp (Complex.I * (m.val : ℂ) * (ψ : ℂ)) else 0

/-- `windowPhaseVec b M c 0` is `windowVec b M c`. -/
@[simp]
theorem windowPhaseVec_zero (b M : ℕ) (c : ℕ → ℝ) :
    windowPhaseVec b M c 0 = windowVec b M c := by
  funext m
  simp [windowPhaseVec, windowVec]

/-- Squared L2 norm of `windowPhaseVec b M c ψ` when `M < 2 ^ b`. -/
theorem sum_normSq_windowPhaseVec (b M : ℕ) (hM : M < 2 ^ b) (c : ℕ → ℝ) (ψ : ℝ) :
    (∑ m : Fin (2 ^ b), Complex.normSq (windowPhaseVec b M c ψ m)) =
      ∑ m ∈ Finset.range (M + 1), (c m) ^ 2 := by
  have hexp_norm (k : ℕ) : Complex.normSq (Complex.exp (Complex.I * (k : ℂ) * (ψ : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, show Complex.I * (k : ℂ) * (ψ : ℂ) =
        (((k : ℝ) * ψ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_pow]
  have hterm (m : Fin (2 ^ b)) :
      Complex.normSq (windowPhaseVec b M c ψ m) =
        if m.val ≤ M then (c m.val) ^ 2 else 0 := by
    dsimp [windowPhaseVec]
    split_ifs
    · rw [map_mul, Complex.normSq_ofReal, hexp_norm, mul_one, sq]
    · exact map_zero _
  simp_rw [hterm, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k hk ↦ (⟨k, by
      have hk' := Finset.mem_range.mp hk
      omega⟩ : Fin (2 ^ b)))
    (fun k hk ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      dsimp
      have hk' := Finset.mem_range.mp hk
      omega⟩)
    (fun a₁ _ a₂ _ h ↦ congrArg Fin.val h)
    (fun m hm ↦ ⟨m.val, Finset.mem_range.mpr (by
      have hm' := (Finset.mem_filter.mp hm).2
      omega), rfl⟩)
    (fun _ _ ↦ rfl)

/-- Half-shift Luis–Peřina sine-window amplitude `√(2 / L) * sin(π (m + 1/2) / L)` for `m < L`
(and `0` for `m ≥ L`). Setting `L = M + 1` gives support `{0, ..., M}`, requiring at most `M`
controlled walk applications. -/
noncomputable def sineWindowCoeff (L m : ℕ) : ℝ :=
  if m < L then √(2 / (L : ℝ)) * Real.sin (π * ((m : ℝ) + 1 / 2) / (L : ℝ)) else 0

private theorem sum_cos_odd_mul_pi_div {L : ℕ} (hL : 2 ≤ L) :
    (∑ m ∈ Finset.range L, Real.cos ((2 * (m : ℝ) + 1) * (π / (L : ℝ)))) = 0 := by
  let δ : ℝ := π / (L : ℝ)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by positivity
  have hδ_pos : 0 < δ := div_pos Real.pi_pos hL_pos
  have hδ_lt : δ < π := by
    dsimp [δ]
    rw [div_lt_iff₀ hL_pos]
    have h2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    nlinarith [Real.pi_pos]
  have hsin_ne : 2 * Real.sin δ ≠ 0 :=
    mul_ne_zero two_ne_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hδ_pos hδ_lt))
  apply mul_left_cancel₀ hsin_ne
  rw [mul_zero, Finset.mul_sum]
  have hstep (m : ℕ) :
      2 * Real.sin δ * Real.cos ((2 * (m : ℝ) + 1) * δ) =
        Real.sin (2 * ((m + 1 : ℕ) : ℝ) * δ) - Real.sin (2 * (m : ℝ) * δ) := by
    have ha : 2 * ((m + 1 : ℕ) : ℝ) * δ = (2 * (m : ℝ) + 1) * δ + δ := by
      push_cast
      ring
    have hb : 2 * (m : ℝ) * δ = (2 * (m : ℝ) + 1) * δ - δ := by ring
    rw [ha, hb, Real.sin_add, Real.sin_sub]
    ring
  change (∑ m ∈ Finset.range L, 2 * Real.sin δ * Real.cos ((2 * (m : ℝ) + 1) * δ)) = 0
  simp_rw [hstep]
  rw [Finset.sum_range_sub (fun k : ℕ ↦ Real.sin (2 * (k : ℝ) * δ)) L]
  have h2L : 2 * (L : ℝ) * δ = 2 * π := by
    dsimp [δ]
    field_simp [ne_of_gt hL_pos]
  rw [h2L, Real.sin_two_pi, Nat.cast_zero, mul_zero, zero_mul, Real.sin_zero, sub_self]

/-- Exact unit normalization `∑_{m=0}^{L-1} (sineWindowCoeff L m)² = 1` for every `L ≥ 2`. -/
theorem sum_sq_sineWindowCoeff {L : ℕ} (hL : 2 ≤ L) :
    (∑ m ∈ Finset.range L, (sineWindowCoeff L m) ^ 2) = 1 := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := by positivity
  have hterm :
      (∑ m ∈ Finset.range L, (sineWindowCoeff L m) ^ 2) =
        ∑ m ∈ Finset.range L,
          (1 / (L : ℝ)) * (1 - Real.cos ((2 * (m : ℝ) + 1) * (π / (L : ℝ)))) := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hlt : m < L := Finset.mem_range.mp hm
    simp only [sineWindowCoeff, hlt, ↓reduceIte, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / (L : ℝ))]
    let α : ℝ := π * ((m : ℝ) + 1 / 2) / (L : ℝ)
    have h2α : 2 * α = (2 * (m : ℝ) + 1) * (π / (L : ℝ)) := by
      dsimp [α]
      ring
    have hsin2 : 2 * Real.sin α ^ 2 = 1 - Real.cos (2 * α) := by
      have hcos := Real.cos_two_mul α
      have hsq := Real.sin_sq α
      linarith
    rw [← h2α]
    change (2 / (L : ℝ)) * Real.sin α ^ 2 = (1 / (L : ℝ)) * (1 - Real.cos (2 * α))
    rw [show (2 / (L : ℝ)) * Real.sin α ^ 2 = (1 / (L : ℝ)) * (2 * Real.sin α ^ 2) by ring, hsin2]
  rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, sum_cos_odd_mul_pi_div hL, sub_zero,
    one_div_mul_cancel (ne_of_gt hL_pos)]

namespace SineQPE

/-- Eighth root of unity `ω = (1 + i) / √2 = e^{iπ/4}`. -/
noncomputable def omega8 : ℂ := (1 + Complex.I) / (√2 : ℂ)

private lemma sqrt2_complex_ne_zero : (√2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

private lemma sqrt2_complex_sq : (√2 : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private lemma omega8_sq : omega8 ^ 2 = Complex.I := by
  unfold omega8
  rw [div_pow, sqrt2_complex_sq]
  have h : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    calc (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = 2 * Complex.I := by rw [Complex.I_sq]; ring
  rw [h]
  ring

/-- Element `a + b ω + c ω² + d ω³ ∈ ℤ[ω]` where `ω = (1 + i)/√2`, `ω⁴ = -1`. -/
@[ext]
structure CyclotomicEight where
  /-- Coefficient of `1`. -/
  a : ℤ
  /-- Coefficient of `ω`. -/
  b : ℤ
  /-- Coefficient of `ω² = i`. -/
  c : ℤ
  /-- Coefficient of `ω³`. -/
  d : ℤ
  deriving DecidableEq, Repr

namespace CyclotomicEight

/-- Evaluate `a + b ω + c ω² + d ω³` in `ℂ`. -/
noncomputable def toComplex (x : CyclotomicEight) : ℂ :=
  (x.a : ℂ) + (x.b : ℂ) * omega8 + (x.c : ℂ) * omega8 ^ 2 + (x.d : ℂ) * omega8 ^ 3

/-- Addition in `ℤ[ω]`. -/
def add (x y : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

/-- Negation in `ℤ[ω]`. -/
def neg (x : CyclotomicEight) : CyclotomicEight :=
  ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- Multiplication in `ℤ[ω]` using `ω⁴ = -1`. -/
def mul (x y : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
   x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
   x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩

/-- Complex conjugation in `ℤ[ω]`. -/
def conj (x : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a, -x.d, -x.c, -x.b⟩

end CyclotomicEight

/-- Exact `2 × 2` matrix `(√2)⁻ᵏ [[a, b], [c, d]]` over `ℤ[ω, 1/√2]`. -/
structure CyclotomicMat2 where
  /-- Power `k` of `(√2)⁻¹`. -/
  k : ℕ
  /-- Entry `(0, 0)`. -/
  a : CyclotomicEight
  /-- Entry `(0, 1)`. -/
  b : CyclotomicEight
  /-- Entry `(1, 0)`. -/
  c : CyclotomicEight
  /-- Entry `(1, 1)`. -/
  d : CyclotomicEight
  deriving DecidableEq, Repr

namespace CyclotomicMat2

/-- Identity `2 × 2` cyclotomic matrix. -/
def one : CyclotomicMat2 :=
  ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩

/-- Matrix multiplication in `M₂(ℤ[ω, 1/√2])`. -/
def mul (m₁ m₂ : CyclotomicMat2) : CyclotomicMat2 :=
  ⟨m₁.k + m₂.k,
   (m₁.a.mul m₂.a).add (m₁.b.mul m₂.c),
   (m₁.a.mul m₂.b).add (m₁.b.mul m₂.d),
   (m₁.c.mul m₂.a).add (m₁.d.mul m₂.c),
   (m₁.c.mul m₂.b).add (m₁.d.mul m₂.d)⟩

/-- Evaluate `CyclotomicMat2` as a `2 × 2` complex matrix. -/
noncomputable def toMatrix (m : CyclotomicMat2) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((√2 : ℂ)⁻¹ ^ m.k) • !![m.a.toComplex, m.b.toComplex; m.c.toComplex, m.d.toComplex]

end CyclotomicMat2

/-- Primitive 1-qubit Clifford+`T` gate letters (`TOFF = 0`). -/
inductive Gate1 : Type where
  | X | Z | H | S | T
  deriving DecidableEq, Repr

namespace Gate1

/-- Convert a `Gate1` letter into a 1-qubit `Circuit 1`. -/
def toCircuit : Gate1 → Circuit 1
  | .X => Circuit.X 0
  | .Z => Circuit.Z 0
  | .H => Circuit.H 0
  | .S => Circuit.S 0
  | .T => Circuit.T 0

/-- Exact cyclotomic matrix of one `Gate1` letter. -/
def evalCyc : Gate1 → CyclotomicMat2
  | .X => ⟨0, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
  | .Z => ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩
  | .S => ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩⟩
  | .T => ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩
  | .H => ⟨1, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩

private lemma singleton_zero_eq_whole :
    QRegister.singleton (0 : Fin 1) = QRegister.whole 1 := by
  apply QRegister.ext
  ext i
  exact congrArg Fin.val (Subsingleton.elim (QRegister.singleton (0 : Fin 1) i)
    (QRegister.whole 1 i))

theorem eval_toCircuit (g : Gate1) :
    g.toCircuit.eval.1 = g.evalCyc.toMatrix := by
  have hreg : ∀ U : Unitary 2, ((QRegister.singleton (0 : Fin 1)).embedUnitary U).1 = U.1 := by
    intro U
    rw [singleton_zero_eq_whole, QRegister.whole_embedUnitary]
  cases g with
  | X =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.X, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex]
  | Z =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.Z, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex]
  | S =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.S, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex, omega8_sq]
  | T =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.T, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex, omega8]
  | H =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.H, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex, Complex.real_smul]

end Gate1

/-- `SU(2)`-shaped `2 × 2` matrix `[[u, -conj v], [v, conj u]]`. -/
def su2Matrix (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u, -star v; v, star u]

theorem su2Matrix_sub (u₁ v₁ u₂ v₂ : ℂ) :
    su2Matrix u₁ v₁ - su2Matrix u₂ v₂ = su2Matrix (u₁ - u₂) (v₁ - v₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [su2Matrix]; try ring)

theorem su2Matrix_conjTranspose_mul_self (u v : ℂ) :
    (su2Matrix u v)ᴴ * su2Matrix u v =
      ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.star_def, Complex.normSq_eq_conj_mul_self] <;> ring

theorem su2Matrix_mul_conjTranspose_self (u v : ℂ) :
    su2Matrix u v * (su2Matrix u v)ᴴ =
      ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.star_def, Complex.normSq_eq_conj_mul_self] <;> ring

theorem su2Matrix_mem_unitaryGroup {u v : ℂ} (h : Complex.normSq u + Complex.normSq v = 1) :
    su2Matrix u v ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    su2Matrix_mul_conjTranspose_self, h, Complex.ofReal_one, one_smul]

theorem l2_opNorm_one_le {d : ℕ} : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem unitary_opNorm_le_one {d : ℕ} (U : Unitary d) : ‖U.1‖ ≤ 1 := by
  have hmul : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  have hsq : ‖U.1‖ * ‖U.1‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hmul]
    exact l2_opNorm_one_le
  nlinarith [norm_nonneg U.1]

theorem unitary_inv_val {d : ℕ} (U : Unitary d) : (U⁻¹).1 = U.1ᴴ :=
  rfl

/-- Exact C*-norm bound on the difference of two `su2Matrix` operators. -/
theorem norm_su2Matrix_sub_le {u₁ v₁ u₂ v₂ : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsq : (u₁.re - u₂.re) ^ 2 + (u₁.im - u₂.im) ^ 2 +
           (v₁.re - v₂.re) ^ 2 + (v₁.im - v₂.im) ^ 2 ≤ δ ^ 2) :
    ‖su2Matrix u₁ v₁ - su2Matrix u₂ v₂‖ ≤ δ := by
  rw [su2Matrix_sub]
  set du := u₁ - u₂
  set dv := v₁ - v₂
  set S : ℝ := Complex.normSq du + Complex.normSq dv
  have hS_nonneg : 0 ≤ S := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hS_eq : S = (u₁.re - u₂.re) ^ 2 + (u₁.im - u₂.im) ^ 2 +
      (v₁.re - v₂.re) ^ 2 + (v₁.im - v₂.im) ^ 2 := by
    simp only [S, du, dv, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hnorm_sq : ‖su2Matrix du dv‖ * ‖su2Matrix du dv‖ ≤ δ ^ 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, su2Matrix_conjTranspose_mul_self, norm_smul,
      Complex.norm_of_nonneg hS_nonneg]
    calc S * ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ S * 1 := by gcongr; exact l2_opNorm_one_le
      _ = S := mul_one S
      _ ≤ δ ^ 2 := hS_eq ▸ hsq
  nlinarith [norm_nonneg (su2Matrix du dv)]

/-- Embedding any local operator into a `QRegister` is norm-nonincreasing
(`‖r.embedMatrix A‖ ≤ ‖A‖`). -/
theorem embedMatrix_opNorm_le {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    ‖r.embedMatrix A‖ ≤ ‖A‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x ↦ ?_
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM]
  let fOut : Fin (2 ^ k) × (r.Environment → ZMod 2) → ℝ :=
    fun p ↦ ‖(r.embedMatrix A *ᵥ x.ofLp) (r.basisSplitEquiv.symm p)‖ ^ 2
  let fIn : Fin (2 ^ k) × (r.Environment → ZMod 2) → ℝ :=
    fun p ↦ ‖x.ofLp (r.basisSplitEquiv.symm p)‖ ^ 2
  have hOut : (∑ global, ‖(r.embedMatrix A *ᵥ x.ofLp) global‖ ^ 2) =
      ∑ env, ∑ loc, fOut (loc, env) := by
    rw [← r.basisSplitEquiv.symm.sum_comp (fun global ↦ ‖(r.embedMatrix A *ᵥ x.ofLp) global‖ ^ 2)]
    change (∑ p, fOut p) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hIn : (∑ env, ∑ loc, fIn (loc, env)) = ‖x‖ ^ 2 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    change (∑ p, fIn p) = _
    rw [r.basisSplitEquiv.symm.sum_comp (fun global ↦ ‖x.ofLp global‖ ^ 2),
      EuclideanSpace.norm_sq_eq]
  rw [hOut]
  have hslice (env : r.Environment → ZMod 2) :
      (∑ loc : Fin (2 ^ k), fOut (loc, env)) ≤
        ‖A‖ ^ 2 * ∑ loc : Fin (2 ^ k), fIn (loc, env) := by
    let xEnv : EuclideanSpace ℂ (Fin (2 ^ k)) :=
      WithLp.toLp 2 (fun loc ↦ x.ofLp (r.basisSplitEquiv.symm (loc, env)))
    have hmul (loc : Fin (2 ^ k)) :
        (r.embedMatrix A *ᵥ x.ofLp) (r.basisSplitEquiv.symm (loc, env)) =
          (A *ᵥ xEnv.ofLp) loc := by
      rw [r.embedMatrix_mulVec_apply]
      have h1 : r.extractIndex (r.basisSplitEquiv.symm (loc, env)) = loc := by
        rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
      have h2 : (r.basisSplitEquiv (r.basisSplitEquiv.symm (loc, env))).2 = env := by
        rw [Equiv.apply_symm_apply]
      rw [h1, h2]
      rfl
    change (∑ loc, ‖(r.embedMatrix A *ᵥ x.ofLp) (r.basisSplitEquiv.symm (loc, env))‖ ^ 2) ≤ _
    simp_rw [hmul]
    have hbound := Matrix.l2_opNorm_mulVec A xEnv
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hbound
    rw [EuclideanSpace.norm_sq_eq] at hsq
    calc (∑ loc : Fin (2 ^ k), ‖(A *ᵥ xEnv.ofLp) loc‖ ^ 2)
        ≤ (‖A‖ * ‖xEnv‖) ^ 2 := hsq
      _ = ‖A‖ ^ 2 * ‖xEnv‖ ^ 2 := mul_pow _ _ _
      _ = ‖A‖ ^ 2 * ∑ loc : Fin (2 ^ k), fIn (loc, env) := by
        rw [EuclideanSpace.norm_sq_eq]
  calc
    (∑ env, ∑ loc, fOut (loc, env))
      ≤ ∑ env, ‖A‖ ^ 2 * ∑ loc, fIn (loc, env) :=
        Finset.sum_le_sum fun env _ ↦ hslice env
    _ = ‖A‖ ^ 2 * ∑ env, ∑ loc, fIn (loc, env) := by rw [← Finset.mul_sum]
    _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by rw [hIn]
    _ = (‖A‖ * ‖x‖) ^ 2 := (mul_pow _ _ _).symm

theorem embedMatrix_sub {k n : ℕ} (r : QRegister k n)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  rw [sub_eq_add_neg, sub_eq_add_neg, r.embedMatrix_add]
  have hneg : r.embedMatrix (-B) = -r.embedMatrix B := by
    have h := r.embedMatrix_smul (-1 : ℂ) B
    rwa [neg_one_smul, neg_one_smul] at h
  rw [hneg]

/-- Relocating a circuit onto a register preserves operator-norm approximation bounds. -/
theorem norm_onRegister_sub_le {k n : ℕ} (r : QRegister k n) (c : Circuit k)
    (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    ‖(c.onRegister r).eval.1 - r.embedMatrix V‖ ≤ ‖c.eval.1 - V‖ := by
  rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, ← embedMatrix_sub]
  exact embedMatrix_opNorm_le r _

/-- Unitary telescope step `‖U₂ * U₁ - V₂ * V₁‖ ≤ ‖U₂ - V₂‖ + ‖U₁ - V₁‖`. -/
theorem norm_mul_sub_mul_of_le_one {d : ℕ}
    {U₂ U₁ V₂ V₁ : Matrix (Fin d) (Fin d) ℂ}
    (hU₁ : ‖U₁‖ ≤ 1) (hV₂ : ‖V₂‖ ≤ 1) :
    ‖U₂ * U₁ - V₂ * V₁‖ ≤ ‖U₂ - V₂‖ + ‖U₁ - V₁‖ := by
  have hsplit : U₂ * U₁ - V₂ * V₁ = (U₂ - V₂) * U₁ + V₂ * (U₁ - V₁) := by noncomm_ring
  rw [hsplit]
  calc ‖(U₂ - V₂) * U₁ + V₂ * (U₁ - V₁)‖
      ≤ ‖(U₂ - V₂) * U₁‖ + ‖V₂ * (U₁ - V₁)‖ := norm_add_le _ _
    _ ≤ ‖U₂ - V₂‖ * ‖U₁‖ + ‖V₂‖ * ‖U₁ - V₁‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ ‖U₂ - V₂‖ * 1 + 1 * ‖U₁ - V₁‖ := by gcongr
    _ = ‖U₂ - V₂‖ + ‖U₁ - V₁‖ := by ring

/-- Single-qubit `Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2})`. -/
noncomputable def rzMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i : Fin 2 ↦
    if i = 0 then Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ))
    else Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))

/-- Single-qubit `Ry(θ) = [[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]`. -/
noncomputable def ryMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
     (Real.sin (θ / 2) : ℂ),  (Real.cos (θ / 2) : ℂ)]

theorem rzMatrix_eq_su2Matrix (θ : ℝ) :
    rzMatrix θ = su2Matrix (Real.cos (θ / 2) - Complex.I * Real.sin (θ / 2)) 0 := by
  have hexp_pos : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hexp_neg : Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      (Real.cos (θ / 2) : ℂ) - Complex.I * (Real.sin (θ / 2) : ℂ) := by
    have h : -Complex.I * ((θ / 2 : ℝ) : ℂ) = ((-(θ / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [rzMatrix, su2Matrix, Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      one_ne_zero, zero_ne_one, ↓reduceIte, hexp_pos, hexp_neg, RCLike.star_def, map_sub,
      map_mul, map_zero, Complex.conj_ofReal, Complex.conj_I, neg_zero];
     try ring)

theorem ryMatrix_eq_su2Matrix (θ : ℝ) :
    ryMatrix θ = su2Matrix (Real.cos (θ / 2)) (Real.sin (θ / 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ryMatrix, su2Matrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, RCLike.star_def,
      Complex.conj_ofReal]

/-- Bundled unitary `Rz(θ) : Unitary 2`. -/
noncomputable def rzUnitary (θ : ℝ) : Unitary 2 :=
  ⟨rzMatrix θ, by
    rw [rzMatrix_eq_su2Matrix]
    apply su2Matrix_mem_unitaryGroup
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im]
    nlinarith [Real.cos_sq_add_sin_sq (θ / 2)]⟩

/-- Clifford conjugation `S · Z · H · c · H · S` converting any `Rz(θ)` circuit into an `Ry(θ)`
circuit with identical `T`-count and identical operator-norm error. -/
def rzToRyCircuit (c : Circuit 1) : Circuit 1 :=
  Circuit.sequence [Circuit.S 0, Circuit.Z 0, Circuit.H 0, c, Circuit.H 0, Circuit.S 0]

@[simp]
theorem rzToRyCircuit_count_toff (c : Circuit 1) :
    (rzToRyCircuit c).count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := by
  simp [rzToRyCircuit]

@[simp]
theorem rzToRyCircuit_count_t (c : Circuit 1) :
    (rzToRyCircuit c).count PrimitiveGate.T = c.count PrimitiveGate.T := by
  simp [rzToRyCircuit]

theorem norm_rzToRyCircuit_sub_le (c : Circuit 1) (θ : ℝ) :
    ‖(rzToRyCircuit c).eval.1 - ryMatrix θ‖ ≤ ‖c.eval.1 - rzMatrix θ‖ := by
  let uL : Unitary 2 := Qubit.S * Qubit.H
  let uR : Unitary 2 := Qubit.H * (Qubit.Z * Qubit.S)
  have hreg : ∀ U : Unitary 2, ((QRegister.singleton (0 : Fin 1)).embedUnitary U).1 = U.1 := by
    intro U
    have hs : QRegister.singleton (0 : Fin 1) = QRegister.whole 1 := by
      apply QRegister.ext; ext i
      exact congrArg Fin.val (Subsingleton.elim (QRegister.singleton (0 : Fin 1) i)
        (QRegister.whole 1 i))
    rw [hs, QRegister.whole_embedUnitary]
  have heval : (rzToRyCircuit c).eval.1 = uL.1 * c.eval.1 * uR.1 := by
    simp only [rzToRyCircuit, Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity,
      Circuit.eval_single, one_mul, Submonoid.coe_mul, hreg, uL, uR, PrimitiveGate.eval]
    noncomm_ring
  have hry : ryMatrix θ = uL.1 * rzMatrix θ * uR.1 := by
    rw [rzMatrix_eq_su2Matrix, ryMatrix_eq_su2Matrix]
    have hne := sqrt2_complex_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [uL, uR, Qubit.S, Qubit.H, Qubit.Z, su2Matrix, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.real_smul, -Complex.ofReal_cos, -Complex.ofReal_sin];
       field_simp [hne];
       ring_nf;
       try (rw [Complex.I_sq]);
       try (rw [sqrt2_complex_sq]);
       try ring)
  rw [heval, hry, show uL.1 * c.eval.1 * uR.1 - uL.1 * rzMatrix θ * uR.1 =
      uL.1 * (c.eval.1 - rzMatrix θ) * uR.1 by noncomm_ring]
  calc ‖uL.1 * (c.eval.1 - rzMatrix θ) * uR.1‖
      ≤ ‖uL.1 * (c.eval.1 - rzMatrix θ)‖ * ‖uR.1‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖uL.1‖ * ‖c.eval.1 - rzMatrix θ‖) * ‖uR.1‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖c.eval.1 - rzMatrix θ‖) * 1 := by
        gcongr
        · exact unitary_opNorm_le_one uL
        · exact unitary_opNorm_le_one uR
    _ = ‖c.eval.1 - rzMatrix θ‖ := by ring

@[simp]
private lemma extractIndex_singleton_zero_two (i : Fin 4) :
    (QRegister.singleton (0 : Fin 2)).extractIndex i = ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases i <;> decide

@[simp]
private lemma extractIndex_singleton_one_two (i : Fin 4) :
    (QRegister.singleton (1 : Fin 2)).extractIndex i =
      ⟨i.val / 2, by have := i.isLt; omega⟩ := by
  fin_cases i <;> decide

theorem singleton_one_embedMatrix_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (QRegister.singleton (1 : Fin 2)).embedMatrix A =
      !![A 0 0, 0, A 0 1, 0;
         0, A 0 0, 0, A 0 1;
         A 1 0, 0, A 1 1, 0;
         0, A 1 0, 0, A 1 1] := by
  ext i j
  rw [QRegister.embedMatrix_apply]
  simp_rw [QRegister.singleton_one_basisSplit_environment_eq_iff, basisBits_eq_div_mod]
  fin_cases i <;> fin_cases j <;>
    simp [extractIndex_singleton_one_two]

theorem cnot01_eval :
    (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval.1 =
      !![1, 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0;
         0, 1, 0, 0] := by
  change ((QRegister.pair (0 : Fin 2) 1 (by decide)).embedUnitary PrimitiveGate.CNOT.eval).1 = _
  rw [QRegister.pair_zero_one_eq_whole, QRegister.whole_embedUnitary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimitiveGate.eval, PrimitiveGate.cnotUnitary, Operator.permutationUnitary,
      Equiv.Perm.permMatrix, Equiv.swap_apply_def]

/-- Two-CNOT parity-phase gadget `CNOT 0 1 ;; cRz(1) ;; CNOT 0 1`, implementing
`CNOT * (I ⊗ Rz(β)) * CNOT` with 1× the `T`-count and 1× the operator-norm error of `cRz`. -/
def cnotRzCnotCircuit (cRz : Circuit 1) : Circuit 2 :=
  Circuit.sequence [
    Circuit.CNOT 0 1 (by decide),
    cRz.onRegister (QRegister.singleton 1),
    Circuit.CNOT 0 1 (by decide)
  ]

@[simp]
theorem cnotRzCnotCircuit_count_toff (cRz : Circuit 1) :
    (cnotRzCnotCircuit cRz).count PrimitiveGate.TOFF = cRz.count PrimitiveGate.TOFF := by
  simp [cnotRzCnotCircuit]

@[simp]
theorem cnotRzCnotCircuit_count_t (cRz : Circuit 1) :
    (cnotRzCnotCircuit cRz).count PrimitiveGate.T = cRz.count PrimitiveGate.T := by
  simp [cnotRzCnotCircuit]

/-- Ideal 2-qubit parity-phase unitary `CNOT 0 1 * (I ⊗ Rz(β)) * CNOT 0 1`. -/
noncomputable def parityRzUnitary (β : ℝ) : Unitary (2 ^ 2) :=
  (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval *
    (QRegister.singleton (1 : Fin 2)).embedUnitary (rzUnitary β) *
    (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval

theorem parityRzUnitary_eq_diagonal (β : ℝ) :
    (parityRzUnitary β).1 =
      Matrix.diagonal fun i : Fin 4 ↦
        Complex.exp (Complex.I *
          (((2 * ((basisBits 2 i 1).val : ℝ) - 1) *
            (1 - 2 * ((basisBits 2 i 0).val : ℝ)) * (β / 2) : ℝ) : ℂ)) := by
  have hb00 : basisBits 2 (0 : Fin 4) 0 = 0 := by decide
  have hb01 : basisBits 2 (0 : Fin 4) 1 = 0 := by decide
  have hb10 : basisBits 2 (1 : Fin 4) 0 = 1 := by decide
  have hb11 : basisBits 2 (1 : Fin 4) 1 = 0 := by decide
  have hb20 : basisBits 2 (2 : Fin 4) 0 = 0 := by decide
  have hb21 : basisBits 2 (2 : Fin 4) 1 = 1 := by decide
  have hb30 : basisBits 2 (3 : Fin 4) 0 = 1 := by decide
  have hb31 : basisBits 2 (3 : Fin 4) 1 = 1 := by decide
  have hval0 : (0 : ZMod 2).val = 0 := rfl
  have hval1 : (1 : ZMod 2).val = 1 := rfl
  have hc21 : (2 : ℂ) - 1 = 1 := by norm_num
  have hc12 : (1 : ℂ) - 2 = -1 := by norm_num
  dsimp only [parityRzUnitary, Submonoid.coe_mul, QRegister.embedUnitary_val, rzUnitary]
  rw [cnot01_eval, singleton_one_embedMatrix_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzMatrix, Matrix.mul_apply, Fin.sum_univ_four,
      hb00, hb01, hb10, hb11, hb20, hb21, hb30, hb31, hval0, hval1,
      hc21, hc12, mul_neg, -ZMod.natCast_val]

theorem norm_cnotRzCnotCircuit_sub_le (cRz : Circuit 1) (β : ℝ) :
    ‖(cnotRzCnotCircuit cRz).eval.1 - (parityRzUnitary β).1‖ ≤ ‖cRz.eval.1 - rzMatrix β‖ := by
  let cnotU := (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval
  let r1 : QRegister 1 2 := QRegister.singleton 1
  have heval :
      (cnotRzCnotCircuit cRz).eval.1 - (parityRzUnitary β).1 =
        cnotU.1 * ((cRz.onRegister r1).eval.1 - r1.embedMatrix (rzMatrix β)) * cnotU.1 := by
    simp only [cnotRzCnotCircuit, parityRzUnitary, Circuit.sequence, Circuit.eval_seq,
      Circuit.eval_identity, one_mul, Submonoid.coe_mul, QRegister.embedUnitary_val, rzUnitary,
      cnotU, r1]
    noncomm_ring
  rw [heval]
  calc ‖cnotU.1 * ((cRz.onRegister r1).eval.1 - r1.embedMatrix (rzMatrix β)) * cnotU.1‖
      ≤ ‖cnotU.1 * ((cRz.onRegister r1).eval.1 - r1.embedMatrix (rzMatrix β))‖ * ‖cnotU.1‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖cnotU.1‖ * ‖(cRz.onRegister r1).eval.1 - r1.embedMatrix (rzMatrix β)‖) * ‖cnotU.1‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖cRz.eval.1 - rzMatrix β‖) * 1 := by
        gcongr
        · exact unitary_opNorm_le_one cnotU
        · exact norm_onRegister_sub_le r1 cRz (rzMatrix β)
        · exact unitary_opNorm_le_one cnotU
    _ = ‖cRz.eval.1 - rzMatrix β‖ := by ring

/-! ### General `ket` Symbolic Gate Evaluation Toolkit -/

@[simp]
private lemma basisBits_symm_apply (q : ℕ) (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[simp]
private lemma symm_basisBits_apply (q : ℕ) (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem qubit_H_eq_hadamardUnitary : Qubit.H = (hadamardUnitary : Unitary (2 ^ 1)) := by
  have h00 : ((-1 : ℤˣ) ^ ((basisBits 1) 0 ⬝ᵥ (basisBits 1) 0) : ℤˣ) = 1 := by decide
  have h01 : ((-1 : ℤˣ) ^ ((basisBits 1) 0 ⬝ᵥ (basisBits 1) 1) : ℤˣ) = 1 := by decide
  have h10 : ((-1 : ℤˣ) ^ ((basisBits 1) 1 ⬝ᵥ (basisBits 1) 0) : ℤˣ) = 1 := by decide
  have h11 : ((-1 : ℤˣ) ^ ((basisBits 1) 1 ⬝ᵥ (basisBits 1) 1) : ℤˣ) = -1 := by decide
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Qubit.H, hadamardMatrix_apply, walshMatrix_apply, walshChar_apply_apply, h00]
  · simp [Qubit.H, hadamardMatrix_apply, walshMatrix_apply, walshChar_apply_apply, h01]
  · simp [Qubit.H, hadamardMatrix_apply, walshMatrix_apply, walshChar_apply_apply, h10]
  · simp [Qubit.H, hadamardMatrix_apply, walshMatrix_apply, walshChar_apply_apply, h11]

theorem eval_H_eq_hadamardAt (n : ℕ) (q : Fin n) :
    (Circuit.H q).eval = hadamardAt n q := by
  rw [Circuit.eval_single, PrimitiveGate.eval, qubit_H_eq_hadamardUnitary]

theorem hadamardAt_inv (n : ℕ) (q : Fin n) :
    (hadamardAt n q)⁻¹ = hadamardAt n q := by
  rw [← eval_H_eq_hadamardAt, ← Circuit.eval_inverse]
  rfl

/-- Basis permutation swapping physical wires `q` and `r` on `b` qubits. -/
def bitSwapPerm (b : ℕ) (q r : Fin b) : Equiv.Perm (Fin (2 ^ b)) :=
  (basisBits b).trans
    (((Equiv.swap q r).arrowCongr (Equiv.refl (ZMod 2))).trans (basisBits b).symm)

theorem basisBits_bitSwapPerm (b : ℕ) (q r : Fin b) (j : Fin (2 ^ b)) (w : Fin b) :
    basisBits b (bitSwapPerm b q r j) w = basisBits b j (Equiv.swap q r w) := by
  change (basisBits b) ((basisBits b).symm _) w = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem eval_SWAP_mulVec_single (b : ℕ) (q r : Fin b) (hqr : q ≠ r) (j : Fin (2 ^ b)) :
    (Circuit.SWAP q r hqr).eval.1.mulVec (Pi.single j 1) =
      Pi.single (bitSwapPerm b q r j) 1 := by
  rw [Circuit.eval_gate, PrimitiveGate.eval, PrimitiveGate.swapUnitary,
    QRegister.embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors,
    Operator.permutationUnitary_mulVec_single, QRegister.tensorState_single_replaceIndex]
  congr 1
  have hloc0 : ∀ x : Fin 4, basisBits 2 (Equiv.swap (1 : Fin 4) 2 x) 0 = basisBits 2 x 1 := by
    intro x; fin_cases x <;> decide
  have hloc1 : ∀ x : Fin 4, basisBits 2 (Equiv.swap (1 : Fin 4) 2 x) 1 = basisBits 2 x 0 := by
    intro x; fin_cases x <;> decide
  let reg := QRegister.pair q r hqr
  apply (basisBits b).injective
  funext w
  change basisBits b (reg.replaceIndex j _) w = basisBits b (bitSwapPerm b q r j) w
  rw [basisBits_bitSwapPerm]
  by_cases hwq : w = q
  · have h0 : w = reg 0 := hwq
    conv_lhs => rw [h0]
    rw [QRegister.basisBits_replaceIndex_apply, hloc0, QRegister.basisBits_extractIndex,
      hwq, Equiv.swap_apply_left]
    rfl
  · by_cases hwr : w = r
    · have h1 : w = reg 1 := hwr
      conv_lhs => rw [h1]
      rw [QRegister.basisBits_replaceIndex_apply, hloc1, QRegister.basisBits_extractIndex,
        hwr, Equiv.swap_apply_right]
      rfl
    · have hout : w ∉ Set.range reg.wires := by
        rintro ⟨i, hi⟩
        fin_cases i
        · exact hwq hi.symm
        · exact hwr hi.symm
      rw [QRegister.basisBits_replaceIndex_of_not_mem reg j _ w hout,
        Equiv.swap_apply_of_ne_of_ne hwq hwr]

/-- Structurally recursive helper swapping outer wire pairs `⟨k, _⟩` and `⟨b - 1 - k, _⟩`. -/
def swapPairsAux (b : ℕ) : ℕ → ℕ → Circuit b
  | 0, _ => .identity
  | rem + 1, k =>
    if hk : k < b / 2 then
      .seq
        (Circuit.SWAP ⟨k, by omega⟩ ⟨b - 1 - k, by omega⟩
          (by intro h; have h' := congrArg Fin.val h; dsimp at h'; omega))
        (swapPairsAux b rem (k + 1))
    else
      .identity

/-- Bit-reversal circuit on `b` qubits using `⌊b / 2⌋` two-wire `SWAP` gates
(`0` `T`, `0` `TOFF`). -/
def swapAllCircuit (b : ℕ) : Circuit b :=
  swapPairsAux b (b / 2) 0

@[simp]
theorem swapPairsAux_count_toff (b rem k : ℕ) :
    (swapPairsAux b rem k).count PrimitiveGate.TOFF = 0 := by
  induction rem generalizing k with
  | zero => rfl
  | succ r ih =>
    unfold swapPairsAux
    by_cases hk : k < b / 2
    · rw [dite_eq_left hk]
      simp [ih (k + 1)]
    · rw [dite_eq_right hk]
      rfl

@[simp]
theorem swapPairsAux_count_t (b rem k : ℕ) :
    (swapPairsAux b rem k).count PrimitiveGate.T = 0 := by
  induction rem generalizing k with
  | zero => rfl
  | succ r ih =>
    unfold swapPairsAux
    by_cases hk : k < b / 2
    · rw [dite_eq_left hk]
      simp [ih (k + 1)]
    · rw [dite_eq_right hk]
      rfl

@[simp]
theorem swapAllCircuit_count_toff (b : ℕ) :
    (swapAllCircuit b).count PrimitiveGate.TOFF = 0 :=
  swapPairsAux_count_toff b (b / 2) 0

@[simp]
theorem swapAllCircuit_count_t (b : ℕ) :
    (swapAllCircuit b).count PrimitiveGate.T = 0 :=
  swapPairsAux_count_t b (b / 2) 0

private def partialRevIdx (b k : ℕ) (j : Fin (2 ^ b)) : Fin (2 ^ b) :=
  (basisBits b).symm fun w : Fin b ↦
    if w.val < k ∨ b - 1 - w.val < k then basisBits b j (Fin.rev w) else basisBits b j w

private lemma basisBits_partialRevIdx (b k : ℕ) (j : Fin (2 ^ b)) (w : Fin b) :
    basisBits b (partialRevIdx b k j) w =
      if w.val < k ∨ b - 1 - w.val < k then basisBits b j (Fin.rev w) else basisBits b j w :=
  congrFun ((basisBits b).apply_symm_apply _) w

theorem swapAllCircuit_eval (b : ℕ) :
    (swapAllCircuit b).eval = QFT.swapAllUnitary b := by
  apply Subtype.ext
  ext i j
  have hstep : ∀ rem k : ℕ, b / 2 - k = rem → k ≤ b / 2 →
      (swapPairsAux b rem k).eval.1.mulVec (Pi.single (partialRevIdx b k j) 1) =
        Pi.single (partialRevIdx b (b / 2) j) 1 := by
    intro rem
    induction rem with
    | zero =>
      intro k hrem hk_le
      have hkeq : k = b / 2 := by omega
      subst hkeq
      rw [swapPairsAux, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    | succ r ih =>
      intro k hrem hk_le
      have hk : k < b / 2 := by omega
      rw [swapPairsAux, dite_eq_left hk, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, eval_SWAP_mulVec_single]
      have hnext :
          bitSwapPerm b ⟨k, by omega⟩ ⟨b - 1 - k, by omega⟩ (partialRevIdx b k j) =
            partialRevIdx b (k + 1) j := by
        apply (basisBits b).injective
        funext w
        rw [basisBits_bitSwapPerm, basisBits_partialRevIdx, basisBits_partialRevIdx]
        by_cases hwk : w.val = k
        · have hw : w = ⟨k, by omega⟩ := Fin.ext hwk
          have hrev : (⟨b - 1 - k, by omega⟩ : Fin b) = Fin.rev w := by
            ext; simp [Fin.rev, hwk]; omega
          rw [hw, Equiv.swap_apply_left, hrev, ← hw]
          have hcond1 : ¬ ((Fin.rev w).val < k ∨ b - 1 - (Fin.rev w).val < k) := by
            simp [Fin.rev, hwk]; omega
          have hcond2 : w.val < k + 1 ∨ b - 1 - w.val < k + 1 := Or.inl (by omega)
          rw [ite_eq_right hcond1, ite_eq_left hcond2]
        · by_cases hwrev : w.val = b - 1 - k
          · have hw : w = ⟨b - 1 - k, by omega⟩ := Fin.ext hwrev
            have hrev : (⟨k, by omega⟩ : Fin b) = Fin.rev w := by
              ext; simp [Fin.rev, hwrev]; omega
            rw [hw, Equiv.swap_apply_right, hrev, ← hw]
            have hcond1 : ¬ ((Fin.rev w).val < k ∨ b - 1 - (Fin.rev w).val < k) := by
              simp [Fin.rev, hwrev]; omega
            have hcond2 : w.val < k + 1 ∨ b - 1 - w.val < k + 1 := Or.inr (by omega)
            rw [ite_eq_right hcond1, ite_eq_left hcond2]
          · have hne1 : w ≠ ⟨k, by omega⟩ := fun h ↦ hwk (congrArg Fin.val h)
            have hne2 : w ≠ ⟨b - 1 - k, by omega⟩ := fun h ↦ hwrev (congrArg Fin.val h)
            rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
            have hequiv : (w.val < k ∨ b - 1 - w.val < k) ↔
                (w.val < k + 1 ∨ b - 1 - w.val < k + 1) := by
              have hwlt := w.isLt
              omega
            by_cases hc : w.val < k ∨ b - 1 - w.val < k
            · rw [ite_eq_left hc, ite_eq_left (hequiv.mp hc)]
            · rw [ite_eq_right hc, ite_eq_right (mt hequiv.mpr hc)]
      rw [hnext]
      exact ih (k + 1) (by omega) (by omega)
  have h0 : partialRevIdx b 0 j = j := by
    apply (basisBits b).injective
    funext w
    rw [basisBits_partialRevIdx, ite_eq_right (by omega)]
  have htop : partialRevIdx b (b / 2) j = bitRevEquiv b j := by
    apply (basisBits b).injective
    funext w
    rw [basisBits_partialRevIdx, basisBits_bitRevEquiv]
    by_cases hc : w.val < b / 2 ∨ b - 1 - w.val < b / 2
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc]
      have hmid : Fin.rev w = w := by
        ext
        have hwlt := w.isLt
        simp only [Fin.rev]
        omega
      rw [hmid]
  have hcol :
      ((swapAllCircuit b).eval.1.mulVec (basisState j)) i =
        ((QFT.swapAllUnitary b).1.mulVec (basisState j)) i := by
    dsimp [swapAllCircuit, basisState]
    rw [← h0, hstep (b / 2) 0 (by omega) (Nat.zero_le _), htop, h0,
      Operator.permutationUnitary_mulVec_single]
  simp only [basisState, Matrix.mulVec_single_one] at hcol
  exact hcol

/-- Structurally recursive helper for `revLoopCircuit`. -/
def revLoopAux {n : ℕ} (m : ℕ) (stepC : Fin m → Circuit n) : ℕ → ℕ → Circuit n
  | 0, _ => .identity
  | rem + 1, k =>
    if hk : k < m then
      .seq (revLoopAux m stepC rem (k + 1)) (stepC ⟨k, hk⟩)
    else
      .identity

/-- Reverse-ordered loop circuit executing `stepC ⟨m - 1, _⟩` first down to `stepC ⟨k, _⟩` last,
matching `(QFT.loopUnitary m f k)⁻¹` in exact matrix multiplication order. -/
def revLoopCircuit {n : ℕ} (m : ℕ) (stepC : Fin m → Circuit n) (k : ℕ) : Circuit n :=
  revLoopAux m stepC (m - k) k

private lemma filter_erase_fin (m k : ℕ) (hk : k < m) :
    (Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val)).erase ⟨k, hk⟩ =
      Finset.univ.filter (fun i : Fin m ↦ k + 1 ≤ i.val) := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hle⟩
    have hne_val : i.val ≠ k := fun hv ↦ hne (Fin.ext hv)
    omega
  · intro hle
    exact ⟨fun heq ↦ by have hv : i.val = k := congrArg Fin.val heq; omega, by omega⟩

theorem revLoopCircuit_count {n a : ℕ} (g : PrimitiveGate a)
    (m : ℕ) (stepC : Fin m → Circuit n) (k : ℕ) :
    (revLoopCircuit m stepC k).count g =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), (stepC i).count g := by
  have haux : ∀ rem k : ℕ, m - k = rem →
      (revLoopAux m stepC rem k).count g =
        ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), (stepC i).count g := by
    intro rem
    induction rem with
    | zero =>
      intro k hrem
      have hempty : Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val) = ∅ := by
        ext i; simp; omega
      rw [hempty]
      rfl
    | succ r ih =>
      intro k hrem
      have hk : k < m := by omega
      let ik : Fin m := ⟨k, hk⟩
      have hmem : ik ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val) := by
        simp [ik]
      rw [revLoopAux, dite_eq_left hk, Circuit.count_seq, ih (k + 1) (by omega),
        ← Finset.add_sum_erase _ _ hmem, filter_erase_fin m k hk, add_comm]
  exact haux (m - k) k rfl

theorem norm_revLoopCircuit_sub_le {n : ℕ} (m : ℕ)
    (stepC : Fin m → Circuit n) (f : Fin m → Unitary (2 ^ n))
    (ζ : Fin m → ℂ) (ε : Fin m → ℝ) (k : ℕ)
    (hζ : ∀ i, k ≤ i.val → ‖ζ i‖ = 1)
    (hstep : ∀ i, k ≤ i.val → ‖(stepC i).eval.1 - ζ i • ((f i)⁻¹).1‖ ≤ ε i) :
    (‖∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ζ i‖ = 1) ∧
    ‖(revLoopCircuit m stepC k).eval.1 -
        (∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ζ i) •
          ((QFT.loopUnitary m f k)⁻¹).1‖ ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ε i := by
  have haux : ∀ rem k : ℕ, m - k = rem →
      (∀ i, k ≤ i.val → ‖ζ i‖ = 1) →
      (∀ i, k ≤ i.val → ‖(stepC i).eval.1 - ζ i • ((f i)⁻¹).1‖ ≤ ε i) →
      (‖∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ζ i‖ = 1) ∧
      ‖(revLoopAux m stepC rem k).eval.1 -
          (∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ζ i) •
            ((QFT.loopUnitary m f k)⁻¹).1‖ ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ε i := by
    intro rem
    induction rem with
    | zero =>
      intro k hrem _ _
      have hge : m ≤ k := by omega
      have hempty : Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val) = ∅ := by
        ext i; simp; omega
      rw [hempty, Finset.prod_empty, Finset.sum_empty, revLoopAux,
        QFT.loopUnitary_of_ge m f hge, inv_one, one_smul, Circuit.eval_identity, sub_self,
        norm_zero]
      exact ⟨norm_one, le_rfl⟩
    | succ r ih =>
      intro k hrem hζ_k hstep_k
      have hk : k < m := by omega
      let ik : Fin m := ⟨k, hk⟩
      have hmem : ik ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val) := by
        simp [ik]
      obtain ⟨hζ_tl, h_tl⟩ := ih (k + 1) (by omega)
        (fun i hi ↦ hζ_k i (by omega))
        (fun i hi ↦ hstep_k i (by omega))
      have hprod_split :
          (∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ζ i) =
            ζ ik * ∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k + 1 ≤ i.val), ζ i := by
        rw [← Finset.mul_prod_erase _ _ hmem, filter_erase_fin m k hk]
      have hsum_split :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), ε i) =
            ε ik + ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k + 1 ≤ i.val), ε i := by
        rw [← Finset.add_sum_erase _ _ hmem, filter_erase_fin m k hk]
      refine ⟨by rw [hprod_split, norm_mul, hζ_k ik le_rfl, hζ_tl, mul_one], ?_⟩
      rw [revLoopAux, dite_eq_left hk, Circuit.eval_seq, Submonoid.coe_mul,
        QFT.loopUnitary_step m f hk, _root_.mul_inv_rev, Submonoid.coe_mul, hprod_split,
        hsum_split]
      let ζ_tl := ∏ i ∈ Finset.univ.filter (fun i : Fin m ↦ k + 1 ≤ i.val), ζ i
      have hsmul :
          (ζ ik * ζ_tl) • (((f ik)⁻¹).1 * ((QFT.loopUnitary m f (k + 1))⁻¹).1) =
            (ζ ik • ((f ik)⁻¹).1) * (ζ_tl • ((QFT.loopUnitary m f (k + 1))⁻¹).1) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [hsmul]
      have hV₂ : ‖ζ ik • ((f ik)⁻¹).1‖ ≤ 1 := by
        rw [norm_smul, hζ_k ik le_rfl, one_mul]
        exact unitary_opNorm_le_one _
      calc ‖(stepC ik).eval.1 * (revLoopAux m stepC r (k + 1)).eval.1 -
              (ζ ik • ((f ik)⁻¹).1) * (ζ_tl • ((QFT.loopUnitary m f (k + 1))⁻¹).1)‖
          ≤ ‖(stepC ik).eval.1 - ζ ik • ((f ik)⁻¹).1‖ +
              ‖(revLoopAux m stepC r (k + 1)).eval.1 -
                ζ_tl • ((QFT.loopUnitary m f (k + 1))⁻¹).1‖ :=
            norm_mul_sub_mul_of_le_one (unitary_opNorm_le_one _) hV₂
        _ ≤ ε ik + ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k + 1 ≤ i.val), ε i :=
            add_le_add (hstep_k ik le_rfl) h_tl
  exact haux (m - k) k rfl hζ hstep

end SineQPE

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
