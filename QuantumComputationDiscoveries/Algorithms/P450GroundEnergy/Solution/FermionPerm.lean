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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData

/-!
# Jordan–Wigner CAR, Orbital Reflections & Zero-`T` Fermionic Un-Interleaving

This module establishes the Jordan–Wigner canonical anticommutation relations (CAR), orthogonal
projector and involutory reflection identities for `orbitalNumberOp` and `orbitalReflection`,
linearity and rank-1 factorization of `oneBodyHamiltonian`, and the zero-`T` Clifford `fSWAP`
un-interleaving circuit `fswapUninterleave` that separates spin-`0` modes (`2 * p`) onto block
`0 .. N - 1` and spin-`1` modes (`2 * p + 1`) onto block `N .. 2 * N - 1` with identical local
`N`-qubit orbital reflections (`(Z_0 ⋯ Z_{N-1})^2 = 1` cancellation).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-- High-priority parametric `NeZero (2 ^ k)` instance avoiding unary `Nat.succ` unfolding on
large qubit counts. -/
instance (priority := 100000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-!
## Part 1: Jordan–Wigner Parity Strings & Canonical Anticommutation Relations
-/

/-- Diagonal parity string $\prod_{q \in s} Z_q$ on `k` wires. -/
noncomputable def jwParity (k : ℕ) (s : Finset (Fin k)) : Operator (2 ^ k) :=
  Matrix.diagonal fun i ↦ (-1 : ℂ) ^ ∑ q ∈ s, (basisBits k i q).val

/-- Local lowering operator $(|0\rangle\langle 1|)_j$ embedded on wire `j` of `k` wires. -/
noncomputable def jwLowering (k : ℕ) (j : Fin k) : Operator (2 ^ k) :=
  (QRegister.singleton j).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) 1)

theorem jwAnnihilate_eq_jwParity_mul_jwLowering (k : ℕ) (j : Fin k) :
    jwAnnihilate k j = jwParity k (Finset.univ.filter (· < j)) * jwLowering k j := rfl

@[simp]
theorem jwParity_empty (k : ℕ) : jwParity k ∅ = 1 := by
  simp [jwParity]

@[simp]
theorem jwParity_conjTranspose (k : ℕ) (s : Finset (Fin k)) :
    (jwParity k s)ᴴ = jwParity k s := by
  rw [jwParity, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp

@[simp]
theorem jwParity_mul_self (k : ℕ) (s : Finset (Fin k)) :
    jwParity k s * jwParity k s = 1 := by
  rw [jwParity, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one (n := Fin (2 ^ k)) (α := ℂ) with i
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem jwParity_comm (k : ℕ) (s t : Finset (Fin k)) :
    jwParity k s * jwParity k t = jwParity k t * jwParity k s := by
  simp only [jwParity, Matrix.diagonal_mul_diagonal, mul_comm]

theorem jwParity_union_of_disjoint {k : ℕ} {s t : Finset (Fin k)} (hst : Disjoint s t) :
    jwParity k (s ∪ t) = jwParity k s * jwParity k t := by
  simp only [jwParity, Matrix.diagonal_mul_diagonal, Finset.sum_union hst, pow_add]

theorem jwParity_cons {k : ℕ} (q : Fin k) (s : Finset (Fin k)) (hq : q ∉ s) :
    jwParity k (Finset.cons q s hq) = jwParity k {q} * jwParity k s := by
  rw [Finset.cons_eq_insert, ← Finset.singleton_union]
  exact jwParity_union_of_disjoint (Finset.disjoint_singleton_left.mpr hq)

private lemma qubit_z_eq_diagonal :
    Qubit.Z.1 = Matrix.diagonal (fun b : Fin 2 ↦ (-1 : ℂ) ^ b.val) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Qubit.Z]

private lemma basisBits_one_val (x : Fin (2 ^ 1)) :
    (basisBits 1 x 0).val = x.val := by
  fin_cases x <;> decide

private lemma singleton_extractIndex_val {k : ℕ} (q : Fin k) (i : Fin (2 ^ k)) :
    ((QRegister.singleton q).extractIndex i).val = (basisBits k i q).val := by
  rw [← basisBits_one_val ((QRegister.singleton q).extractIndex i),
    QRegister.basisBits_extractIndex, QRegister.singleton_apply]

theorem jwParity_singleton (k : ℕ) (q : Fin k) :
    jwParity k {q} = (QRegister.singleton q).embedMatrix Qubit.Z.1 := by
  rw [qubit_z_eq_diagonal, QRegister.embedMatrix_diagonal, jwParity]
  congr 1
  ext i
  rw [Finset.sum_singleton, singleton_extractIndex_val]

theorem compose_singleton {n k : ℕ} (r : QRegister k n) (q : Fin k) :
    r.compose (QRegister.singleton q) = QRegister.singleton (r q) := by
  ext i
  fin_cases i
  rfl

theorem embedMatrix_jwParity {n k : ℕ} (r : QRegister k n) (s : Finset (Fin k)) :
    r.embedMatrix (jwParity k s) = jwParity n (s.map r.wires) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons q t hqt ih =>
      have hqt' : r q ∉ t.map r.wires := by simp [hqt]
      rw [jwParity_cons, r.embedMatrix_mul, ih, jwParity_singleton,
        ← QRegister.embedMatrix_compose, compose_singleton, ← jwParity_singleton,
        Finset.map_cons, jwParity_cons _ _ hqt']

theorem jwParity_comm_embedMatrix_of_not_mem {k m : ℕ} (s : Finset (Fin k))
    (r : QRegister m k) (hr : ∀ x : Fin m, r x ∉ s) (A : Operator (2 ^ m)) :
    jwParity k s * r.embedMatrix A = r.embedMatrix A * jwParity k s := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons q t hqt ih =>
      have hdisj : (QRegister.singleton q).DisjointWires r := by
        rw [QRegister.disjoint_iff]
        intro a b hab
        fin_cases a
        exact hr b (Finset.mem_cons.mpr (Or.inl hab.symm))
      have hrt : ∀ x : Fin m, r x ∉ t := fun x hx ↦ hr x (Finset.mem_cons_of_mem hx)
      rw [jwParity_cons q t hqt, jwParity_singleton, Matrix.mul_assoc, ih hrt,
        ← Matrix.mul_assoc, QRegister.embedMatrix_comm_of_disjoint _ _ hdisj, Matrix.mul_assoc,
        ← jwParity_singleton]

private lemma single01_mul_self :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) *
      Matrix.single (0 : Fin 2) (1 : Fin 2) 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp

private lemma single01_anticomm_z :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) * Qubit.Z.1 =
      -(Qubit.Z.1 * Matrix.single (0 : Fin 2) (1 : Fin 2) 1) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp [Qubit.Z]

private lemma single01_conj_add :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ *
        Matrix.single (0 : Fin 2) (1 : Fin 2) 1 +
      Matrix.single (0 : Fin 2) (1 : Fin 2) 1 *
        (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem jwLowering_mul_self (k : ℕ) (p : Fin k) :
    jwLowering k p * jwLowering k p = 0 := by
  rw [jwLowering, ← QRegister.embedMatrix_mul, single01_mul_self, QRegister.embedMatrix_zero]

theorem jwLowering_comm_of_ne {k : ℕ} {p q : Fin k} (hpq : p ≠ q) :
    jwLowering k p * jwLowering k q = jwLowering k q * jwLowering k p :=
  QRegister.embedMatrix_comm_of_disjoint _ _ (QRegister.singleton_disjoint hpq) _ _

theorem jwLowering_conjTranspose_comm_of_ne {k : ℕ} {p q : Fin k} (hpq : p ≠ q) :
    (jwLowering k p)ᴴ * jwLowering k q = jwLowering k q * (jwLowering k p)ᴴ := by
  rw [jwLowering, ← QRegister.embedMatrix_conjTranspose]
  exact QRegister.embedMatrix_comm_of_disjoint _ _ (QRegister.singleton_disjoint hpq) _ _

theorem jwLowering_comm_jwParity_of_not_mem {k : ℕ} (p : Fin k) (s : Finset (Fin k))
    (hp : p ∉ s) :
    jwLowering k p * jwParity k s = jwParity k s * jwLowering k p :=
  (jwParity_comm_embedMatrix_of_not_mem s (QRegister.singleton p)
    (fun i ↦ by fin_cases i; exact hp) _).symm

theorem jwLowering_conjTranspose_comm_jwParity_of_not_mem {k : ℕ} (p : Fin k) (s : Finset (Fin k))
    (hp : p ∉ s) :
    (jwLowering k p)ᴴ * jwParity k s = jwParity k s * (jwLowering k p)ᴴ := by
  rw [jwLowering, ← QRegister.embedMatrix_conjTranspose]
  exact (jwParity_comm_embedMatrix_of_not_mem s (QRegister.singleton p)
    (fun i ↦ by fin_cases i; exact hp) _).symm

theorem jwLowering_anticomm_jwParity_of_mem {k : ℕ} (p : Fin k) (s : Finset (Fin k))
    (hp : p ∈ s) :
    jwLowering k p * jwParity k s = -(jwParity k s * jwLowering k p) := by
  have hnot : p ∉ s.erase p := by simp
  have hs : s = Finset.cons p (s.erase p) hnot := by
    ext x
    simp only [Finset.mem_cons, Finset.mem_erase]
    constructor
    · intro hx
      by_cases hxp : x = p
      · exact Or.inl hxp
      · exact Or.inr ⟨hxp, hx⟩
    · rintro (rfl | ⟨_, hx⟩)
      · exact hp
      · exact hx
  have hanti :
      jwLowering k p * (QRegister.singleton p).embedMatrix Qubit.Z.1 =
        -((QRegister.singleton p).embedMatrix Qubit.Z.1 * jwLowering k p) := by
    rw [jwLowering, ← QRegister.embedMatrix_mul, single01_anticomm_z,
      ← neg_one_smul ℂ, QRegister.embedMatrix_smul, QRegister.embedMatrix_mul, neg_one_smul]
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  rw [jwParity_cons p (s.erase p) hnot, jwParity_singleton, ← Matrix.mul_assoc, hanti, neg_mul,
    Matrix.mul_assoc, jwLowering_comm_jwParity_of_not_mem p (s.erase p) hnot, Matrix.mul_assoc]

theorem jwLowering_conjTranspose_anticomm_jwParity_of_mem {k : ℕ} (p : Fin k) (s : Finset (Fin k))
    (hp : p ∈ s) :
    (jwLowering k p)ᴴ * jwParity k s = -(jwParity k s * (jwLowering k p)ᴴ) := by
  have h := congrArg Matrix.conjTranspose (jwLowering_anticomm_jwParity_of_mem p s hp)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, jwParity_conjTranspose] at h
  rw [eq_comm, neg_eq_iff_eq_neg] at h
  exact h

/-- Canonical anticommutation $\{a_p, a_q\} = 0$ for Jordan–Wigner annihilation operators. -/
theorem jwAnnihilate_anticomm (k : ℕ) (p q : Fin k) :
    jwAnnihilate k p * jwAnnihilate k q + jwAnnihilate k q * jwAnnihilate k p = 0 := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have hmem : p ∈ Finset.univ.filter (· < q) := by simp [hpq]
    have hnot : q ∉ Finset.univ.filter (· < p) := by simp [not_lt.mpr hpq.le]
    have h1 : jwAnnihilate k p * jwAnnihilate k q =
        -(jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < q)) *
          (jwLowering k p * jwLowering k q)) := by
      rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwAnnihilate_eq_jwParity_mul_jwLowering]
      calc
        (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p) *
            (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q)
          = jwParity k (Finset.univ.filter (· < p)) *
              (jwLowering k p * jwParity k (Finset.univ.filter (· < q))) * jwLowering k q := by
            simp only [Matrix.mul_assoc]
        _ = -(jwParity k (Finset.univ.filter (· < p)) *
              jwParity k (Finset.univ.filter (· < q)) *
              (jwLowering k p * jwLowering k q)) := by
            rw [jwLowering_anticomm_jwParity_of_mem p _ hmem]
            simp only [mul_neg, neg_mul, Matrix.mul_assoc]
    have h2 : jwAnnihilate k q * jwAnnihilate k p =
        jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < q)) *
          (jwLowering k p * jwLowering k q) := by
      rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwAnnihilate_eq_jwParity_mul_jwLowering]
      calc
        (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q) *
            (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p)
          = jwParity k (Finset.univ.filter (· < q)) *
              (jwLowering k q * jwParity k (Finset.univ.filter (· < p))) * jwLowering k p := by
            simp only [Matrix.mul_assoc]
        _ = (jwParity k (Finset.univ.filter (· < q)) *
              jwParity k (Finset.univ.filter (· < p))) *
              (jwLowering k q * jwLowering k p) := by
            rw [jwLowering_comm_jwParity_of_not_mem q _ hnot]
            simp only [Matrix.mul_assoc]
        _ = jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < q)) *
              (jwLowering k p * jwLowering k q) := by
            rw [jwParity_comm, jwLowering_comm_of_ne hpq.ne']
    rw [h1, h2, neg_add_cancel]
  · have hnot : p ∉ Finset.univ.filter (· < p) := by simp
    have hsq : jwAnnihilate k p * jwAnnihilate k p = 0 := by
      rw [jwAnnihilate_eq_jwParity_mul_jwLowering]
      calc
        (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p) *
            (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p)
          = jwParity k (Finset.univ.filter (· < p)) *
              (jwLowering k p * jwParity k (Finset.univ.filter (· < p))) * jwLowering k p := by
            simp only [Matrix.mul_assoc]
        _ = (jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < p))) *
              (jwLowering k p * jwLowering k p) := by
            rw [jwLowering_comm_jwParity_of_not_mem p _ hnot]
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [jwLowering_mul_self, mul_zero]
    rw [hsq, add_zero]
  · have hnot : p ∉ Finset.univ.filter (· < q) := by simp [not_lt.mpr hqp.le]
    have hmem : q ∈ Finset.univ.filter (· < p) := by simp [hqp]
    have h1 : jwAnnihilate k q * jwAnnihilate k p =
        -(jwParity k (Finset.univ.filter (· < q)) * jwParity k (Finset.univ.filter (· < p)) *
          (jwLowering k q * jwLowering k p)) := by
      rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwAnnihilate_eq_jwParity_mul_jwLowering]
      calc
        (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q) *
            (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p)
          = jwParity k (Finset.univ.filter (· < q)) *
              (jwLowering k q * jwParity k (Finset.univ.filter (· < p))) * jwLowering k p := by
            simp only [Matrix.mul_assoc]
        _ = -(jwParity k (Finset.univ.filter (· < q)) *
              jwParity k (Finset.univ.filter (· < p)) *
              (jwLowering k q * jwLowering k p)) := by
            rw [jwLowering_anticomm_jwParity_of_mem q _ hmem]
            simp only [mul_neg, neg_mul, Matrix.mul_assoc]
    have h2 : jwAnnihilate k p * jwAnnihilate k q =
        jwParity k (Finset.univ.filter (· < q)) * jwParity k (Finset.univ.filter (· < p)) *
          (jwLowering k q * jwLowering k p) := by
      rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwAnnihilate_eq_jwParity_mul_jwLowering]
      calc
        (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p) *
            (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q)
          = jwParity k (Finset.univ.filter (· < p)) *
              (jwLowering k p * jwParity k (Finset.univ.filter (· < q))) * jwLowering k q := by
            simp only [Matrix.mul_assoc]
        _ = (jwParity k (Finset.univ.filter (· < p)) *
              jwParity k (Finset.univ.filter (· < q))) *
              (jwLowering k p * jwLowering k q) := by
            rw [jwLowering_comm_jwParity_of_not_mem p _ hnot]
            simp only [Matrix.mul_assoc]
        _ = jwParity k (Finset.univ.filter (· < q)) * jwParity k (Finset.univ.filter (· < p)) *
              (jwLowering k q * jwLowering k p) := by
            rw [jwParity_comm, jwLowering_comm_of_ne hqp.ne']
    rw [h2, h1, add_neg_cancel]

/-- Nilpotence $a_p^2 = 0$ of each Jordan–Wigner annihilation operator. -/
@[simp]
theorem jwAnnihilate_mul_self (k : ℕ) (p : Fin k) :
    jwAnnihilate k p * jwAnnihilate k p = 0 := by
  have h := jwAnnihilate_anticomm k p p
  have h2 : (2 : ℂ) • (jwAnnihilate k p * jwAnnihilate k p) = 0 := by
    rw [two_smul]
    exact h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

private lemma jwAnnihilate_conjTranspose_anticomm_of_lt {k : ℕ} {p q : Fin k} (hpq : p < q) :
    (jwAnnihilate k p)ᴴ * jwAnnihilate k q + jwAnnihilate k q * (jwAnnihilate k p)ᴴ = 0 := by
  have hpnot : p ∉ Finset.univ.filter (· < p) := by simp
  have hpmem : p ∈ Finset.univ.filter (· < q) := by simp [hpq]
  have hqnot : q ∉ Finset.univ.filter (· < p) := by simp [not_lt.mpr hpq.le]
  have h1 : (jwAnnihilate k p)ᴴ * jwAnnihilate k q =
      -(jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < q)) *
        ((jwLowering k p)ᴴ * jwLowering k q)) := by
    rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwAnnihilate_eq_jwParity_mul_jwLowering,
      Matrix.conjTranspose_mul, jwParity_conjTranspose]
    calc
      ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p))) *
          (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q)
        = jwParity k (Finset.univ.filter (· < p)) *
            ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < q))) * jwLowering k q := by
          rw [jwLowering_conjTranspose_comm_jwParity_of_not_mem p _ hpnot]
          simp only [Matrix.mul_assoc]
      _ = -(jwParity k (Finset.univ.filter (· < p)) *
            jwParity k (Finset.univ.filter (· < q)) *
            ((jwLowering k p)ᴴ * jwLowering k q)) := by
          rw [jwLowering_conjTranspose_anticomm_jwParity_of_mem p _ hpmem]
          simp only [mul_neg, neg_mul, Matrix.mul_assoc]
  have h2 : jwAnnihilate k q * (jwAnnihilate k p)ᴴ =
      jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < q)) *
        ((jwLowering k p)ᴴ * jwLowering k q) := by
    rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwAnnihilate_eq_jwParity_mul_jwLowering,
      Matrix.conjTranspose_mul, jwParity_conjTranspose]
    have stepA :
        (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q) *
            ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p))) =
          jwParity k (Finset.univ.filter (· < q)) * (jwLowering k p)ᴴ *
            (jwLowering k q * jwParity k (Finset.univ.filter (· < p))) := by
      have hc := (jwLowering_conjTranspose_comm_of_ne hpq.ne).symm
      calc
        (jwParity k (Finset.univ.filter (· < q)) * jwLowering k q) *
            ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p)))
          = jwParity k (Finset.univ.filter (· < q)) *
              (jwLowering k q * (jwLowering k p)ᴴ) *
              jwParity k (Finset.univ.filter (· < p)) := by simp only [Matrix.mul_assoc]
        _ = jwParity k (Finset.univ.filter (· < q)) * (jwLowering k p)ᴴ *
              (jwLowering k q * jwParity k (Finset.univ.filter (· < p))) := by
              rw [hc]
              simp only [Matrix.mul_assoc]
    rw [stepA, jwLowering_comm_jwParity_of_not_mem q _ hqnot]
    calc
      jwParity k (Finset.univ.filter (· < q)) * (jwLowering k p)ᴴ *
          (jwParity k (Finset.univ.filter (· < p)) * jwLowering k q)
        = jwParity k (Finset.univ.filter (· < q)) *
            ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p))) *
            jwLowering k q := by simp only [Matrix.mul_assoc]
      _ = (jwParity k (Finset.univ.filter (· < q)) *
            jwParity k (Finset.univ.filter (· < p))) *
            ((jwLowering k p)ᴴ * jwLowering k q) := by
          rw [jwLowering_conjTranspose_comm_jwParity_of_not_mem p _ hpnot]
          simp only [Matrix.mul_assoc]
      _ = jwParity k (Finset.univ.filter (· < p)) * jwParity k (Finset.univ.filter (· < q)) *
            ((jwLowering k p)ᴴ * jwLowering k q) := by
          rw [jwParity_comm]
  rw [h1, h2, neg_add_cancel]

/-- Canonical anticommutation $\{a_p^\dagger, a_q\} = \delta_{pq} I$ for Jordan–Wigner modes. -/
theorem jwAnnihilate_conjTranspose_anticomm (k : ℕ) (p q : Fin k) :
    (jwAnnihilate k p)ᴴ * jwAnnihilate k q + jwAnnihilate k q * (jwAnnihilate k p)ᴴ =
      if p = q then 1 else 0 := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · rw [ite_eq_right hpq.ne]
    exact jwAnnihilate_conjTranspose_anticomm_of_lt hpq
  · rw [ite_eq_left rfl, jwAnnihilate_eq_jwParity_mul_jwLowering, Matrix.conjTranspose_mul,
      jwParity_conjTranspose]
    have hpnot : p ∉ Finset.univ.filter (· < p) := by simp
    have h1 : ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p))) *
        (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p) =
        (jwLowering k p)ᴴ * jwLowering k p := by
      rw [Matrix.mul_assoc (jwLowering k p)ᴴ, ← Matrix.mul_assoc (jwParity k _),
        jwParity_mul_self, one_mul]
    have h2 : (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p) *
        ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p))) =
        jwLowering k p * (jwLowering k p)ᴴ := by
      have hcomm : jwParity k (Finset.univ.filter (· < p)) *
          (jwLowering k p * (jwLowering k p)ᴴ) =
          (jwLowering k p * (jwLowering k p)ᴴ) *
            jwParity k (Finset.univ.filter (· < p)) := by
        rw [jwLowering, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul]
        exact jwParity_comm_embedMatrix_of_not_mem _ (QRegister.singleton p)
          (fun i ↦ by fin_cases i; exact hpnot) _
      calc
        (jwParity k (Finset.univ.filter (· < p)) * jwLowering k p) *
            ((jwLowering k p)ᴴ * jwParity k (Finset.univ.filter (· < p)))
          = (jwParity k (Finset.univ.filter (· < p)) *
              (jwLowering k p * (jwLowering k p)ᴴ)) *
              jwParity k (Finset.univ.filter (· < p)) := by
            simp only [Matrix.mul_assoc]
        _ = (jwLowering k p * (jwLowering k p)ᴴ) *
              (jwParity k (Finset.univ.filter (· < p)) *
                jwParity k (Finset.univ.filter (· < p))) := by
            rw [hcomm, Matrix.mul_assoc]
        _ = jwLowering k p * (jwLowering k p)ᴴ := by
            rw [jwParity_mul_self, mul_one]
    rw [h1, h2, jwLowering, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_add, single01_conj_add,
      QRegister.embedMatrix_one]
  · rw [ite_eq_right hqp.ne']
    have h := congrArg Matrix.conjTranspose (jwAnnihilate_conjTranspose_anticomm_of_lt hqp)
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
    exact h

/-!
## Part 2: General Linear Fermionic Mode, Number Projector & Reflection Algebra
-/

/-- Linear combination $\sum_{p} u_p a_{\mathrm{emb}(p)}$ of Jordan–Wigner annihilation modes. -/
noncomputable def jwLinearMode {m k : ℕ} (emb : Fin m → Fin k) (u : Fin m → ℝ) :
    Operator (2 ^ k) :=
  ∑ p : Fin m, (u p : ℂ) • jwAnnihilate k (emb p)

theorem jwLinearMode_mul_self {m k : ℕ} (emb : Fin m → Fin k) (u : Fin m → ℝ) :
    jwLinearMode emb u * jwLinearMode emb u = 0 := by
  have hexp :
      jwLinearMode emb u * jwLinearMode emb u =
        ∑ p : Fin m, ∑ q : Fin m, ((u p : ℂ) * (u q : ℂ)) •
          (jwAnnihilate k (emb p) * jwAnnihilate k (emb q)) := by
    rw [jwLinearMode, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ ↦ smul_mul_smul_comm _ _ _ _
  have hsum :
      (2 : ℂ) • (jwLinearMode emb u * jwLinearMode emb u) = 0 := by
    rw [two_smul]
    calc
      jwLinearMode emb u * jwLinearMode emb u + jwLinearMode emb u * jwLinearMode emb u
        = (∑ p : Fin m, ∑ q : Fin m, ((u p : ℂ) * (u q : ℂ)) •
            (jwAnnihilate k (emb p) * jwAnnihilate k (emb q))) +
          ∑ p : Fin m, ∑ q : Fin m, ((u q : ℂ) * (u p : ℂ)) •
            (jwAnnihilate k (emb q) * jwAnnihilate k (emb p)) := by
          rw [hexp]
          congr 1
          exact Finset.sum_comm
      _ = ∑ p : Fin m, ∑ q : Fin m, ((u p : ℂ) * (u q : ℂ)) •
            (jwAnnihilate k (emb p) * jwAnnihilate k (emb q) +
              jwAnnihilate k (emb q) * jwAnnihilate k (emb p)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          rw [mul_comm (u q : ℂ) (u p : ℂ), ← smul_add]
      _ = 0 := by simp [jwAnnihilate_anticomm]
  exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)

theorem jwLinearMode_conjTranspose_anticomm {m k : ℕ} {emb : Fin m → Fin k}
    (hemb : Function.Injective emb) (u v : Fin m → ℝ) :
    (jwLinearMode emb u)ᴴ * jwLinearMode emb v + jwLinearMode emb v * (jwLinearMode emb u)ᴴ =
      ((∑ p : Fin m, u p * v p : ℝ) : ℂ) • (1 : Operator (2 ^ k)) := by
  have hconj : (jwLinearMode emb u)ᴴ = ∑ p : Fin m, (u p : ℂ) • (jwAnnihilate k (emb p))ᴴ := by
    simp [jwLinearMode, Matrix.conjTranspose_sum]
  have hexp1 :
      (jwLinearMode emb u)ᴴ * jwLinearMode emb v =
        ∑ p : Fin m, ∑ q : Fin m, ((u p : ℂ) * (v q : ℂ)) •
          ((jwAnnihilate k (emb p))ᴴ * jwAnnihilate k (emb q)) := by
    rw [hconj, jwLinearMode, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ ↦ smul_mul_smul_comm _ _ _ _
  have hexp2 :
      jwLinearMode emb v * (jwLinearMode emb u)ᴴ =
        ∑ p : Fin m, ∑ q : Fin m, ((u p : ℂ) * (v q : ℂ)) •
          (jwAnnihilate k (emb q) * (jwAnnihilate k (emb p))ᴴ) := by
    rw [hconj, jwLinearMode, Finset.sum_mul]
    trans ∑ q : Fin m, ∑ p : Fin m, ((u p : ℂ) * (v q : ℂ)) •
        (jwAnnihilate k (emb q) * (jwAnnihilate k (emb p))ᴴ)
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [smul_mul_smul_comm, mul_comm (v q : ℂ) (u p : ℂ)]
    · exact Finset.sum_comm
  calc
    (jwLinearMode emb u)ᴴ * jwLinearMode emb v + jwLinearMode emb v * (jwLinearMode emb u)ᴴ
      = ∑ p : Fin m, ∑ q : Fin m, ((u p : ℂ) * (v q : ℂ)) •
          ((jwAnnihilate k (emb p))ᴴ * jwAnnihilate k (emb q) +
            jwAnnihilate k (emb q) * (jwAnnihilate k (emb p))ᴴ) := by
        rw [hexp1, hexp2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ ↦ (smul_add _ _ _).symm
    _ = ∑ p : Fin m, ((u p : ℂ) * (v p : ℂ)) • (1 : Operator (2 ^ k)) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.sum_eq_single p]
        · simp [jwAnnihilate_conjTranspose_anticomm]
        · intro q _ hqp
          simp [jwAnnihilate_conjTranspose_anticomm, hemb.ne hqp.symm]
        · intro hp
          exact (hp (Finset.mem_univ p)).elim
    _ = ((∑ p : Fin m, u p * v p : ℝ) : ℂ) • (1 : Operator (2 ^ k)) := by
        rw [← Finset.sum_smul]
        push_cast
        rfl

theorem jwLinearMode_number_idempotent {m k : ℕ} {emb : Fin m → Fin k}
    (hemb : Function.Injective emb) {u : Fin m → ℝ} (hu : ∑ p, u p ^ 2 = 1) :
    ((jwLinearMode emb u)ᴴ * jwLinearMode emb u) *
      ((jwLinearMode emb u)ᴴ * jwLinearMode emb u) =
      (jwLinearMode emb u)ᴴ * jwLinearMode emb u := by
  set b := jwLinearMode emb u
  have hanti : bᴴ * b + b * bᴴ = 1 := by
    have h := jwLinearMode_conjTranspose_anticomm hemb u u
    simp_rw [← sq] at h
    simpa [b, hu] using h
  have htriple : b * bᴴ * b = b := by
    have hmul := congrArg (· * b) hanti
    rw [add_mul, one_mul, Matrix.mul_assoc bᴴ b b, jwLinearMode_mul_self, mul_zero, zero_add]
      at hmul
    exact hmul
  calc
    (bᴴ * b) * (bᴴ * b) = bᴴ * (b * bᴴ * b) := by simp only [Matrix.mul_assoc]
    _ = bᴴ * b := by rw [htriple]

/-- Generic reflection algebra: for an idempotent $P^2 = P$, $R = 1 - 2P$ is an involution. -/
theorem reflection_mul_self_of_idempotent {d : ℕ} {P : Operator d} (hP : P * P = P) :
    (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
  simp only [sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hP]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Hermitian involutory orbital reflection $R_{u,\sigma} = I - 2 \tilde{n}_{u,\sigma}$. -/
noncomputable def orbitalReflection (N : ℕ) (u : Fin N → ℝ) (σ : Fin 2) :
    Operator (2 ^ (2 * N)) :=
  1 - (2 : ℂ) • orbitalNumberOp N u σ

theorem spinOrbital_injective (N : ℕ) (σ : Fin 2) :
    Function.Injective (fun p : Fin N ↦ spinOrbital N p σ) := by
  intro p q hpq
  have hval := congrArg Fin.val hpq
  dsimp [spinOrbital] at hval
  exact Fin.ext (by omega)

theorem orbitalNumberOp_eq_jwLinearMode (N : ℕ) (u : Fin N → ℝ) (σ : Fin 2) :
    orbitalNumberOp N u σ =
      (jwLinearMode (fun p ↦ spinOrbital N p σ) u)ᴴ *
        jwLinearMode (fun p ↦ spinOrbital N p σ) u := rfl

@[simp]
theorem orbitalNumberOp_conjTranspose (N : ℕ) (u : Fin N → ℝ) (σ : Fin 2) :
    (orbitalNumberOp N u σ)ᴴ = orbitalNumberOp N u σ := by
  simp [orbitalNumberOp]

theorem orbitalNumberOp_mul_self (N : ℕ) {u : Fin N → ℝ} (hu : ∑ p, u p ^ 2 = 1) (σ : Fin 2) :
    orbitalNumberOp N u σ * orbitalNumberOp N u σ = orbitalNumberOp N u σ :=
  jwLinearMode_number_idempotent (spinOrbital_injective N σ) hu

@[simp]
theorem orbitalReflection_conjTranspose (N : ℕ) (u : Fin N → ℝ) (σ : Fin 2) :
    (orbitalReflection N u σ)ᴴ = orbitalReflection N u σ := by
  simp [orbitalReflection]

theorem orbitalReflection_mul_self (N : ℕ) {u : Fin N → ℝ} (hu : ∑ p, u p ^ 2 = 1) (σ : Fin 2) :
    orbitalReflection N u σ * orbitalReflection N u σ = 1 :=
  reflection_mul_self_of_idempotent (orbitalNumberOp_mul_self N hu σ)

@[simp]
theorem oneBodyHamiltonian_zero {N : ℕ} :
    oneBodyHamiltonian (0 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  simp [oneBodyHamiltonian]

theorem oneBodyHamiltonian_add {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (A + B) = oneBodyHamiltonian A + oneBodyHamiltonian B := by
  simp only [oneBodyHamiltonian, Matrix.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

theorem oneBodyHamiltonian_smul {N : ℕ} (c : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (c • A) = (c : ℂ) • oneBodyHamiltonian A := by
  simp only [oneBodyHamiltonian, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul,
    Finset.smul_sum]

theorem oneBodyHamiltonian_neg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (-A) = -oneBodyHamiltonian A := by
  rw [← neg_one_smul ℝ A, oneBodyHamiltonian_smul]
  simp

theorem oneBodyHamiltonian_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (A - B) = oneBodyHamiltonian A - oneBodyHamiltonian B := by
  rw [sub_eq_add_neg, oneBodyHamiltonian_add, oneBodyHamiltonian_neg, sub_eq_add_neg]

theorem oneBodyHamiltonian_sum {N : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (∑ i ∈ s, f i) = ∑ i ∈ s, oneBodyHamiltonian (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih => rw [Finset.sum_cons, oneBodyHamiltonian_add, ih, Finset.sum_cons]

/-- Rank-1 bridge: `oneBodyHamiltonian (vecMulVec u u)` equals the spin-summed orbital number
operator `orbitalNumberOp N u 0 + orbitalNumberOp N u 1`. -/
theorem oneBodyHamiltonian_vecMulVec {N : ℕ} (u : Fin N → ℝ) :
    oneBodyHamiltonian (Matrix.vecMulVec u u) =
      orbitalNumberOp N u 0 + orbitalNumberOp N u 1 := by
  rw [oneBodyHamiltonian, Fin.sum_univ_two]
  have hspin (σ : Fin 2) :
      (∑ p : Fin N, ∑ q : Fin N, ((Matrix.vecMulVec u u p q : ℝ) : ℂ) •
          ((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ *
            jwAnnihilate (2 * N) (spinOrbital N q σ))) =
        orbitalNumberOp N u σ := by
    dsimp only [orbitalNumberOp]
    rw [Matrix.conjTranspose_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hconj_p : ((u p : ℂ) • jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ =
        (u p : ℂ) • (jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ := by simp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Matrix.vecMulVec_apply, Complex.ofReal_mul, hconj_p, smul_mul_smul_comm]
  rw [hspin 0, hspin 1]

/-!
## Part 4: Two-Qubit & Adjacent `fSWAP` Gate (`SWAP ;; H ;; CNOT ;; H`)
-/

/-- Local two-qubit controlled-`Z` circuit `H 1 ;;ᶜ CNOT 0 1 ;;ᶜ H 1`. -/
def cz2 : Circuit 2 :=
  have h01 : (0 : Wire 2) ≠ 1 := by decide
  Circuit.H 1 ;;ᶜ Circuit.CNOT 0 1 h01 ;;ᶜ Circuit.H 1

/-- Local two-qubit fermionic SWAP circuit `SWAP 0 1 ;;ᶜ H 1 ;;ᶜ CNOT 0 1 ;;ᶜ H 1`. -/
def fswap2 : Circuit 2 :=
  have h01 : (0 : Wire 2) ≠ 1 := by decide
  Circuit.SWAP 0 1 h01 ;;ᶜ Circuit.H 1 ;;ᶜ Circuit.CNOT 0 1 h01 ;;ᶜ Circuit.H 1

/-- Adjacent fermionic SWAP on wires `i` and `i + 1` of a `k`-qubit circuit:
`SWAP i (i+1) ;;ᶜ H (i+1) ;;ᶜ CNOT i (i+1) ;;ᶜ H (i+1)`. -/
def fswapAdj (k i : ℕ) (hi : i + 1 < k) : Circuit k :=
  let u : Wire k := ⟨i, by omega⟩
  let v : Wire k := ⟨i + 1, hi⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u, v] at this; omega
  Circuit.SWAP u v huv ;;ᶜ Circuit.H v ;;ᶜ Circuit.CNOT u v huv ;;ᶜ Circuit.H v

theorem fswapAdj_eq_onRegister (k i : ℕ) (hi : i + 1 < k) :
    fswapAdj k i hi =
      fswap2.onRegister (QRegister.pair ⟨i, by omega⟩ ⟨i + 1, hi⟩
        (by intro h; have := congrArg Fin.val h; dsimp at this; omega)) := by
  let u : Wire k := ⟨i, by omega⟩
  let v : Wire k := ⟨i + 1, hi⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u, v] at this; omega
  have hp : (QRegister.pair u v huv).compose (QRegister.pair 0 1 (by decide)) =
      QRegister.pair u v huv := by
    ext j
    fin_cases j <;> rfl
  have hs1 : (QRegister.pair u v huv).compose (QRegister.singleton 1) =
      QRegister.singleton v := by
    ext j
    fin_cases j
    rfl
  dsimp only [fswapAdj, fswap2, Circuit.onRegister_seq, Circuit.onRegister_relocates_gate,
    Circuit.SWAP, Circuit.H, Circuit.CNOT, Circuit.single]
  rw [hp, hs1]

@[simp]
theorem fswapAdj_count_t (k i : ℕ) (hi : i + 1 < k) :
    (fswapAdj k i hi).count .T = 0 := by
  simp [fswapAdj]

@[simp]
theorem fswapAdj_count_toff (k i : ℕ) (hi : i + 1 < k) :
    (fswapAdj k i hi).count .TOFF = 0 := by
  simp [fswapAdj]

private lemma singleton0_extractIndex_2 :
    (QRegister.singleton (0 : Wire 2)).extractIndex 0 = 0 ∧
    (QRegister.singleton (0 : Wire 2)).extractIndex 1 = 1 ∧
    (QRegister.singleton (0 : Wire 2)).extractIndex 2 = 0 ∧
    (QRegister.singleton (0 : Wire 2)).extractIndex 3 = 1 := by
  decide

private lemma singleton1_extractIndex_2 :
    (QRegister.singleton (1 : Wire 2)).extractIndex 0 = 0 ∧
    (QRegister.singleton (1 : Wire 2)).extractIndex 1 = 0 ∧
    (QRegister.singleton (1 : Wire 2)).extractIndex 2 = 1 ∧
    (QRegister.singleton (1 : Wire 2)).extractIndex 3 = 1 := by
  decide

private lemma singleton0_agreeOutside_2 (a b : Fin (2 ^ 2)) :
    (QRegister.singleton (0 : Wire 2)).AgreeOutside a b ↔
      basisBits 2 a 1 = basisBits 2 b 1 := by
  rw [← QRegister.basisSplit_environment_eq_iff,
    QRegister.singleton_zero_basisSplit_environment_eq_iff]

private lemma singleton1_agreeOutside_2 (a b : Fin (2 ^ 2)) :
    (QRegister.singleton (1 : Wire 2)).AgreeOutside a b ↔
      basisBits 2 a 0 = basisBits 2 b 0 := by
  rw [← QRegister.basisSplit_environment_eq_iff,
    QRegister.singleton_one_basisSplit_environment_eq_iff]

private lemma singleton0_embedMatrix_2 (M : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) :
    (QRegister.singleton (0 : Wire 2)).embedMatrix M =
      !![M 0 0, M 0 1, 0, 0;
         M 1 0, M 1 1, 0, 0;
         0, 0, M 0 0, M 0 1;
         0, 0, M 1 0, M 1 1] := by
  rcases singleton0_extractIndex_2 with ⟨e0, e1, e2, e3⟩
  ext a b
  rw [QRegister.embedMatrix_apply_of_agreeOutside]
  simp only [singleton0_agreeOutside_2]
  fin_cases a <;> fin_cases b <;>
    simp [e0, e1, e2, e3, show basisBits 2 0 1 = 0 by decide,
      show basisBits 2 1 1 = 0 by decide, show basisBits 2 2 1 = 1 by decide,
      show basisBits 2 3 1 = 1 by decide]

private lemma singleton1_embedMatrix_2 (M : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) :
    (QRegister.singleton (1 : Wire 2)).embedMatrix M =
      !![M 0 0, 0, M 0 1, 0;
         0, M 0 0, 0, M 0 1;
         M 1 0, 0, M 1 1, 0;
         0, M 1 0, 0, M 1 1] := by
  rcases singleton1_extractIndex_2 with ⟨e0, e1, e2, e3⟩
  ext a b
  rw [QRegister.embedMatrix_apply_of_agreeOutside]
  simp only [singleton1_agreeOutside_2]
  fin_cases a <;> fin_cases b <;>
    simp [e0, e1, e2, e3, show basisBits 2 0 0 = 0 by decide,
      show basisBits 2 1 0 = 1 by decide, show basisBits 2 2 0 = 0 by decide,
      show basisBits 2 3 0 = 1 by decide]

private lemma permutationUnitary_4_eq (e : Equiv.Perm (Fin 4)) :
    (Operator.permutationUnitary e).1 =
      Matrix.of (fun a b : Fin 4 ↦ if e b = a then (1 : ℂ) else 0) := by
  ext a b
  have h := congrFun (Operator.permutationUnitary_mulVec_single e b (1 : ℂ)) a
  simpa [Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using h

private lemma sqrt_half_mul_self_complex :
    (↑√(1 / 2 : ℝ) : ℂ) * (↑√(1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by
  norm_cast
  rw [Real.mul_self_sqrt (by positivity)]
  norm_num

theorem cz2_eval_val :
    cz2.eval.1 = Matrix.diagonal ![(1 : ℂ), 1, 1, -1] := by
  have hH : ((Circuit.H (1 : Wire 2)).eval).1 =
      (↑√(1 / 2 : ℝ) : ℂ) • !![(1 : ℂ), 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] := by
    rw [Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val, singleton1_embedMatrix_2]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [PrimitiveGate.eval, Qubit.H]
  have hCNOT : ((Circuit.CNOT (0 : Wire 2) 1 (by decide)).eval).1 =
      !![(1 : ℂ), 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0] := by
    have hs0 : Equiv.swap (1 : Fin (2 ^ 2)) 3 0 = 0 := by decide
    have hs2 : Equiv.swap (1 : Fin (2 ^ 2)) 3 2 = 2 := by decide
    rw [Circuit.CNOT, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary, PrimitiveGate.eval, PrimitiveGate.cnotUnitary,
      permutationUnitary_4_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hs0, hs2]
  have hseq : cz2.eval.1 =
      ((Circuit.H (1 : Wire 2)).eval).1 *
        (((Circuit.CNOT (0 : Wire 2) 1 (by decide)).eval).1 *
          ((Circuit.H (1 : Wire 2)).eval).1) := by
    simp [cz2, Matrix.mul_assoc]
  rw [hseq, hH, hCNOT, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqrt_half_mul_self_complex]
  ext a b
  fin_cases a <;> fin_cases b
  all_goals (simp; try norm_num)

theorem fswap2_eval_eq_cz2_mul_swap :
    fswap2.eval = cz2.eval * (Circuit.SWAP (0 : Wire 2) 1 (by decide)).eval := by
  simp [fswap2, cz2, mul_assoc]

theorem fswap2_eval_val :
    fswap2.eval.1 = !![(1 : ℂ), 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, -1] := by
  have hSWAP : ((Circuit.SWAP (0 : Wire 2) 1 (by decide)).eval).1 =
      !![(1 : ℂ), 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
    have hs0 : Equiv.swap (1 : Fin (2 ^ 2)) 2 0 = 0 := by decide
    have hs3 : Equiv.swap (1 : Fin (2 ^ 2)) 2 3 = 3 := by decide
    rw [Circuit.SWAP, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary, PrimitiveGate.eval, PrimitiveGate.swapUnitary,
      permutationUnitary_4_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hs0, hs3]
  rw [fswap2_eval_eq_cz2_mul_swap, Submonoid.coe_mul, cz2_eval_val, hSWAP]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem fswap2_conjTranspose : fswap2.eval.1ᴴ = fswap2.eval.1 := by
  rw [fswap2_eval_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply]

theorem fswap2_mul_self : fswap2.eval.1 * fswap2.eval.1 = 1 := by
  rw [fswap2_eval_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

private lemma fswap2_conj_lower0 :
    fswap2.eval.1 *
        (QRegister.singleton (0 : Wire 2)).embedMatrix
          (Matrix.single (0 : Fin 2) (1 : Fin 2) 1) *
        fswap2.eval.1ᴴ =
      (QRegister.singleton (0 : Wire 2)).embedMatrix Qubit.Z.1 *
        (QRegister.singleton (1 : Wire 2)).embedMatrix
          (Matrix.single (0 : Fin 2) (1 : Fin 2) 1) := by
  rw [fswap2_conjTranspose, fswap2_eval_val, singleton0_embedMatrix_2, singleton0_embedMatrix_2,
    singleton1_embedMatrix_2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Qubit.Z]

private lemma fswap2_conj_z0_z1 :
    fswap2.eval.1 *
        ((QRegister.singleton (0 : Wire 2)).embedMatrix Qubit.Z.1 *
          (QRegister.singleton (1 : Wire 2)).embedMatrix Qubit.Z.1) *
        fswap2.eval.1ᴴ =
      (QRegister.singleton (0 : Wire 2)).embedMatrix Qubit.Z.1 *
        (QRegister.singleton (1 : Wire 2)).embedMatrix Qubit.Z.1 := by
  rw [fswap2_conjTranspose, fswap2_eval_val, singleton0_embedMatrix_2, singleton1_embedMatrix_2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Qubit.Z]

/-- Adjacent `fSWAP` is Hermitian (`Fᴴ = F`). -/
theorem fswapAdj_eval_conjTranspose (k i : ℕ) (hi : i + 1 < k) :
    (fswapAdj k i hi).eval.1ᴴ = (fswapAdj k i hi).eval.1 := by
  rw [fswapAdj_eq_onRegister, Circuit.eval_onRegister, QRegister.embedUnitary_val,
    ← QRegister.embedMatrix_conjTranspose, fswap2_conjTranspose]

/-- Adjacent `fSWAP` is involutory (`F * F = 1`). -/
theorem fswapAdj_eval_mul_self (k i : ℕ) (hi : i + 1 < k) :
    (fswapAdj k i hi).eval.1 * (fswapAdj k i hi).eval.1 = 1 := by
  rw [fswapAdj_eq_onRegister, Circuit.eval_onRegister, QRegister.embedUnitary_val,
    ← QRegister.embedMatrix_mul, fswap2_mul_self, QRegister.embedMatrix_one]

private lemma fswapAdj_conj_jwAnnihilate_left (k i : ℕ) (hi : i + 1 < k) :
    (fswapAdj k i hi).eval.1 * jwAnnihilate k ⟨i, by omega⟩ * (fswapAdj k i hi).eval.1ᴴ =
      jwAnnihilate k ⟨i + 1, hi⟩ := by
  let u : Wire k := ⟨i, by omega⟩
  let v : Wire k := ⟨i + 1, hi⟩
  have hu_val : u.val = i := rfl
  have hv_val : v.val = i + 1 := rfl
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; omega
  let r : QRegister 2 k := QRegister.pair u v huv
  have heval : (fswapAdj k i hi).eval.1 = r.embedMatrix fswap2.eval.1 := by
    rw [fswapAdj_eq_onRegister, Circuit.eval_onRegister, QRegister.embedUnitary_val]
  have hdisj_par : ∀ x : Fin 2, r x ∉ Finset.univ.filter (· < u) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hx
    fin_cases x
    · dsimp [r] at hx; omega
    · dsimp [r] at hx; omega
  have hlow_u : jwLowering k u =
      r.embedMatrix ((QRegister.singleton (0 : Wire 2)).embedMatrix
        (Matrix.single (0 : Fin 2) (1 : Fin 2) 1)) := by
    rw [← QRegister.embedMatrix_compose, compose_singleton]
    rfl
  have hlow_v : jwLowering k v =
      r.embedMatrix ((QRegister.singleton (1 : Wire 2)).embedMatrix
        (Matrix.single (0 : Fin 2) (1 : Fin 2) 1)) := by
    rw [← QRegister.embedMatrix_compose, compose_singleton]
    rfl
  have hz_u : jwParity k {u} =
      r.embedMatrix ((QRegister.singleton (0 : Wire 2)).embedMatrix Qubit.Z.1) := by
    rw [jwParity_singleton, ← QRegister.embedMatrix_compose, compose_singleton]
    rfl
  have hpar_step :
      Finset.univ.filter (· < v) =
        Finset.cons u (Finset.univ.filter (· < u)) (by simp) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons, Fin.lt_def]
    constructor
    · intro hw
      by_cases hwu : w = u
      · exact Or.inl hwu
      · right
        have hne : w.val ≠ i := fun h ↦ hwu (Fin.ext (by omega))
        omega
    · rintro (rfl | hw) <;> omega
  change (fswapAdj k i hi).eval.1 * jwAnnihilate k u * (fswapAdj k i hi).eval.1ᴴ =
    jwAnnihilate k v
  rw [jwAnnihilate_eq_jwParity_mul_jwLowering, heval, ← Matrix.mul_assoc,
    ← jwParity_comm_embedMatrix_of_not_mem _ r hdisj_par, hlow_u]
  calc
    (jwParity k (Finset.univ.filter (· < u)) * r.embedMatrix fswap2.eval.1 *
        r.embedMatrix ((QRegister.singleton (0 : Wire 2)).embedMatrix
          (Matrix.single (0 : Fin 2) (1 : Fin 2) 1))) *
        (r.embedMatrix fswap2.eval.1)ᴴ
      = jwParity k (Finset.univ.filter (· < u)) *
          r.embedMatrix (fswap2.eval.1 *
            (QRegister.singleton (0 : Wire 2)).embedMatrix
              (Matrix.single (0 : Fin 2) (1 : Fin 2) 1) * fswap2.eval.1ᴴ) := by
        rw [← QRegister.embedMatrix_conjTranspose]
        simp only [Matrix.mul_assoc, ← r.embedMatrix_mul]
    _ = jwParity k (Finset.univ.filter (· < u)) *
          (jwParity k {u} * jwLowering k v) := by
        rw [fswap2_conj_lower0, r.embedMatrix_mul, ← hz_u, ← hlow_v]
    _ = jwAnnihilate k v := by
        rw [← Matrix.mul_assoc, jwParity_comm _ _ {u}, ← jwParity_cons u _ (by simp),
          ← hpar_step, ← jwAnnihilate_eq_jwParity_mul_jwLowering]

/-- Conjugating `jwAnnihilate k q` by `fswapAdj k i hi` swaps adjacent modes `i` and `i + 1` and
fixes all other modes. -/
theorem fswapAdj_conj_jwAnnihilate (k i : ℕ) (hi : i + 1 < k) (q : Fin k) :
    (fswapAdj k i hi).eval.1 * jwAnnihilate k q * (fswapAdj k i hi).eval.1ᴴ =
      jwAnnihilate k (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ q) := by
  let u : Wire k := ⟨i, by omega⟩
  let v : Wire k := ⟨i + 1, hi⟩
  have hu_val : u.val = i := rfl
  have hv_val : v.val = i + 1 := rfl
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; omega
  let r : QRegister 2 k := QRegister.pair u v huv
  have heval : (fswapAdj k i hi).eval.1 = r.embedMatrix fswap2.eval.1 := by
    rw [fswapAdj_eq_onRegister, Circuit.eval_onRegister, QRegister.embedUnitary_val]
  have hunit : (fswapAdj k i hi).eval.1 * (fswapAdj k i hi).eval.1ᴴ = 1 := by
    rw [fswapAdj_eval_conjTranspose, fswapAdj_eval_mul_self]
  change (fswapAdj k i hi).eval.1 * jwAnnihilate k q * (fswapAdj k i hi).eval.1ᴴ =
    jwAnnihilate k (Equiv.swap u v q)
  by_cases hqi : q.val < i
  · have hswap : Equiv.swap u v q = q :=
      Equiv.swap_apply_of_ne_of_ne (by intro h; have := congrArg Fin.val h; omega)
        (by intro h; have := congrArg Fin.val h; omega)
    rw [hswap]
    have hdisj_par : ∀ x : Fin 2, r x ∉ Finset.univ.filter (· < q) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hx
      fin_cases x
      · dsimp [r] at hx; omega
      · dsimp [r] at hx; omega
    have hdisj_low : r.DisjointWires (QRegister.singleton q) := by
      rw [QRegister.disjoint_iff]
      intro x y hxy
      fin_cases y
      fin_cases x
      · have := congrArg Fin.val hxy; dsimp [r] at this; omega
      · have := congrArg Fin.val hxy; dsimp [r] at this; omega
    have hcomm : (fswapAdj k i hi).eval.1 * jwAnnihilate k q =
        jwAnnihilate k q * (fswapAdj k i hi).eval.1 := by
      rw [heval, jwAnnihilate_eq_jwParity_mul_jwLowering, ← Matrix.mul_assoc,
        ← jwParity_comm_embedMatrix_of_not_mem _ r hdisj_par, Matrix.mul_assoc,
        jwLowering, QRegister.embedMatrix_comm_of_disjoint _ _ hdisj_low, ← Matrix.mul_assoc]
    rw [hcomm, Matrix.mul_assoc, hunit, mul_one]
  · by_cases hq_eq_u : q = u
    · subst hq_eq_u
      rw [Equiv.swap_apply_left]
      exact fswapAdj_conj_jwAnnihilate_left k i hi
    · by_cases hq_eq_v : q = v
      · subst hq_eq_v
        rw [Equiv.swap_apply_right, ← fswapAdj_conj_jwAnnihilate_left k i hi]
        calc
          (fswapAdj k i hi).eval.1 *
              ((fswapAdj k i hi).eval.1 * jwAnnihilate k u * (fswapAdj k i hi).eval.1ᴴ) *
              (fswapAdj k i hi).eval.1ᴴ
            = ((fswapAdj k i hi).eval.1 * (fswapAdj k i hi).eval.1) * jwAnnihilate k u *
                ((fswapAdj k i hi).eval.1ᴴ * (fswapAdj k i hi).eval.1ᴴ) := by
              simp only [Matrix.mul_assoc]
          _ = jwAnnihilate k u := by
              rw [fswapAdj_eval_conjTranspose, fswapAdj_eval_mul_self, one_mul, mul_one]
      · -- Case `i + 1 < q`: `{u, v}` is contained in `Finset.univ.filter (· < q)`.
        have hgt : i + 1 < q.val := by
          have hne_u : q.val ≠ i := fun h ↦ hq_eq_u (Fin.ext (by omega))
          have hne_v : q.val ≠ i + 1 := fun h ↦ hq_eq_v (Fin.ext (by omega))
          omega
        have hswap : Equiv.swap u v q = q := Equiv.swap_apply_of_ne_of_ne hq_eq_u hq_eq_v
        rw [hswap]
        let sRest : Finset (Fin k) :=
          Finset.univ.filter (fun w : Fin k ↦ w < q ∧ w ≠ u ∧ w ≠ v)
        have hsplit : Finset.univ.filter (· < q) = {u, v} ∪ sRest := by
          ext w
          simp only [sRest, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_insert, Finset.mem_singleton, Fin.lt_def]
          constructor
          · intro hw
            by_cases hwu : w = u
            · exact Or.inl (Or.inl hwu)
            · by_cases hwv : w = v
              · exact Or.inl (Or.inr hwv)
              · exact Or.inr ⟨hw, hwu, hwv⟩
          · rintro ((rfl | rfl) | ⟨hw, _, _⟩)
            · omega
            · omega
            · exact hw
        have hdisj_uv : Disjoint ({u, v} : Finset (Fin k)) sRest := by
          rw [Finset.disjoint_left]
          intro w hw hrest
          simp only [sRest, Finset.mem_filter, Finset.mem_univ, true_and] at hrest
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hrest.2.1 rfl
          · exact hrest.2.2 rfl
        have hz_uv : jwParity k {u, v} =
            r.embedMatrix ((QRegister.singleton (0 : Wire 2)).embedMatrix Qubit.Z.1 *
              (QRegister.singleton (1 : Wire 2)).embedMatrix Qubit.Z.1) := by
          have huv_not : u ∉ ({v} : Finset (Fin k)) := by simp [huv]
          have hpair_set : ({u, v} : Finset (Fin k)) = Finset.cons u {v} huv_not := by
            ext w
            simp
          rw [hpair_set, jwParity_cons u {v} huv_not, jwParity_singleton, jwParity_singleton,
            r.embedMatrix_mul, ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose,
            compose_singleton, compose_singleton]
          rfl
        have hconj_uv :
            (fswapAdj k i hi).eval.1 * jwParity k {u, v} =
              jwParity k {u, v} * (fswapAdj k i hi).eval.1 := by
          have hc : (fswapAdj k i hi).eval.1 * jwParity k {u, v} * (fswapAdj k i hi).eval.1ᴴ =
              jwParity k {u, v} := by
            rw [heval, hz_uv, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul,
              ← QRegister.embedMatrix_mul, fswap2_conj_z0_z1]
          calc
            (fswapAdj k i hi).eval.1 * jwParity k {u, v}
              = ((fswapAdj k i hi).eval.1 * jwParity k {u, v} * (fswapAdj k i hi).eval.1ᴴ) *
                  (fswapAdj k i hi).eval.1 := by
                rw [Matrix.mul_assoc _ _ (fswapAdj k i hi).eval.1, fswapAdj_eval_conjTranspose,
                  fswapAdj_eval_mul_self, mul_one]
            _ = jwParity k {u, v} * (fswapAdj k i hi).eval.1 := by rw [hc]
        have hdisj_rest : ∀ x : Fin 2, r x ∉ sRest := by
          intro x hx
          simp only [sRest, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          fin_cases x
          · exact hx.2.1 rfl
          · exact hx.2.2 rfl
        have hdisj_low : r.DisjointWires (QRegister.singleton q) := by
          rw [QRegister.disjoint_iff]
          intro x y hxy
          fin_cases y
          fin_cases x
          · exact hq_eq_u hxy.symm
          · exact hq_eq_v hxy.symm
        have hcomm : (fswapAdj k i hi).eval.1 * jwAnnihilate k q =
            jwAnnihilate k q * (fswapAdj k i hi).eval.1 := by
          rw [jwAnnihilate_eq_jwParity_mul_jwLowering, hsplit,
            jwParity_union_of_disjoint hdisj_uv]
          calc
            (fswapAdj k i hi).eval.1 * ((jwParity k {u, v} * jwParity k sRest) * jwLowering k q)
              = ((fswapAdj k i hi).eval.1 * jwParity k {u, v}) * jwParity k sRest *
                  jwLowering k q := by simp only [Matrix.mul_assoc]
            _ = jwParity k {u, v} * (r.embedMatrix fswap2.eval.1 * jwParity k sRest) *
                  jwLowering k q := by
                rw [hconj_uv, heval]
                simp only [Matrix.mul_assoc]
            _ = jwParity k {u, v} * jwParity k sRest *
                  (r.embedMatrix fswap2.eval.1 * jwLowering k q) := by
                rw [← jwParity_comm_embedMatrix_of_not_mem sRest r hdisj_rest]
                simp only [Matrix.mul_assoc]
            _ = ((jwParity k {u, v} * jwParity k sRest) * jwLowering k q) *
                  (fswapAdj k i hi).eval.1 := by
                rw [jwLowering, QRegister.embedMatrix_comm_of_disjoint _ _ hdisj_low, ← heval]
                simp only [Matrix.mul_assoc]
        rw [hcomm, Matrix.mul_assoc, hunit, mul_one]

/-!
## Part 5: Electron-Sector Preservation Under Adjacent `fSWAP`
-/

/-- Basis-index permutation induced by swapping physical wires `u` and `v`. -/
def wireSwapEquiv (k : ℕ) (u v : Fin k) : Equiv.Perm (Fin (2 ^ k)) :=
  (basisBits k).trans
    ((Equiv.piCongrLeft' (fun _ ↦ ZMod 2) (Equiv.swap u v)).trans (basisBits k).symm)

@[simp]
theorem basisBits_wireSwapEquiv (k : ℕ) (u v : Fin k) (idx : Fin (2 ^ k)) (q : Fin k) :
    basisBits k (wireSwapEquiv k u v idx) q = basisBits k idx (Equiv.swap u v q) := by
  change (basisBits k) ((basisBits k).symm _) q = _
  rw [Equiv.apply_symm_apply]
  rfl

private lemma swap12_basisBits_zero (x : Fin (2 ^ 2)) :
    basisBits 2 (Equiv.swap (1 : Fin 4) 2 x) 0 = basisBits 2 x 1 := by
  fin_cases x <;> decide

private lemma swap12_basisBits_one (x : Fin (2 ^ 2)) :
    basisBits 2 (Equiv.swap (1 : Fin 4) 2 x) 1 = basisBits 2 x 0 := by
  fin_cases x <;> decide

private lemma pair_replaceIndex_swap {k : ℕ} (u v : Wire k) (huv : u ≠ v) (idx : Fin (2 ^ k)) :
    (QRegister.pair u v huv).replaceIndex idx
        (Equiv.swap (1 : Fin 4) 2 ((QRegister.pair u v huv).extractIndex idx)) =
      wireSwapEquiv k u v idx := by
  let r := QRegister.pair u v huv
  apply (basisBits k).injective
  funext q
  change basisBits k (r.replaceIndex idx (Equiv.swap (1 : Fin 4) 2 (r.extractIndex idx))) q =
    basisBits k (wireSwapEquiv k u v idx) q
  rw [basisBits_wireSwapEquiv]
  by_cases hqu : q = u
  · have hr0 : u = r 0 := rfl
    rw [hqu, Equiv.swap_apply_left, hr0, r.basisBits_replaceIndex_apply, swap12_basisBits_zero,
      QRegister.basisBits_extractIndex]
    rfl
  · by_cases hqv : q = v
    · have hr1 : v = r 1 := rfl
      rw [hqv, Equiv.swap_apply_right, hr1, r.basisBits_replaceIndex_apply, swap12_basisBits_one,
        QRegister.basisBits_extractIndex]
      rfl
    · have hnot : q ∉ Set.range r.wires := by
        rintro ⟨x, hx⟩
        fin_cases x
        · exact hqu hx.symm
        · exact hqv hx.symm
      rw [r.basisBits_replaceIndex_of_not_mem idx _ q hnot, Equiv.swap_apply_of_ne_of_ne hqu hqv]

private lemma pair_embedUnitary_swapUnitary {k : ℕ} (u v : Wire k) (huv : u ≠ v) :
    ((QRegister.pair u v huv).embedUnitary PrimitiveGate.swapUnitary).1 =
      (Operator.permutationUnitary (wireSwapEquiv k u v)).1 := by
  let r := QRegister.pair u v huv
  suffices hvec : ∀ idx : Fin (2 ^ k),
      ((r.embedUnitary PrimitiveGate.swapUnitary).1).mulVec (Pi.single idx 1) =
        ((Operator.permutationUnitary (wireSwapEquiv k u v)).1).mulVec (Pi.single idx 1) by
    ext a b
    simpa [Matrix.mulVec_single_one] using congrFun (hvec b) a
  intro idx
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors, PrimitiveGate.swapUnitary,
    Operator.permutationUnitary_mulVec_single, r.tensorState_single_replaceIndex,
    pair_replaceIndex_swap, Operator.permutationUnitary_mulVec_single]

private lemma permutationUnitary_conj_diagonal {d : ℕ} (π : Equiv.Perm (Fin d))
    (diag : Fin d → ℂ) (hdiag : ∀ idx, diag (π idx) = diag idx) :
    (Operator.permutationUnitary π).1 * Matrix.diagonal diag *
        (Operator.permutationUnitary π).1ᴴ =
      Matrix.diagonal diag := by
  let U := Operator.permutationUnitary π
  have hunit : U.1 * U.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.2
  have hcomm : U.1 * Matrix.diagonal diag = Matrix.diagonal diag * U.1 := by
    suffices hvec : ∀ idx : Fin d,
        (U.1 * Matrix.diagonal diag).mulVec (Pi.single idx 1) =
          (Matrix.diagonal diag * U.1).mulVec (Pi.single idx 1) by
      ext a b
      simpa [Matrix.mulVec_single_one] using congrFun (hvec b) a
    intro idx
    have hdiag_single (x : Fin d) :
        (Matrix.diagonal diag).mulVec (Pi.single x (1 : ℂ)) = diag x • Pi.single x 1 := by
      ext a
      by_cases hax : a = x <;> simp [Matrix.mulVec_diagonal, hax]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdiag_single, Matrix.mulVec_smul,
      Operator.permutationUnitary_mulVec_single, hdiag_single, hdiag]
  rw [hcomm, Matrix.mul_assoc, hunit, mul_one]

/-- Adjacent `fSWAP` preserves the `η`-electron Hamming-weight sector projector. -/
theorem fswapAdj_conj_electronSectorProjector (k i η : ℕ) (hi : i + 1 < k) :
    (fswapAdj k i hi).eval.1 * electronSectorProjector k η * (fswapAdj k i hi).eval.1ᴴ =
      electronSectorProjector k η := by
  let u : Wire k := ⟨i, by omega⟩
  let v : Wire k := ⟨i + 1, hi⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u, v] at this; omega
  let r : QRegister 2 k := QRegister.pair u v huv
  have hsplit : (fswapAdj k i hi).eval =
      r.embedUnitary cz2.eval * r.embedUnitary PrimitiveGate.swapUnitary := by
    rw [fswapAdj_eq_onRegister, Circuit.eval_onRegister, fswap2_eval_eq_cz2_mul_swap,
      r.embedUnitary_mul]
    congr 2
    rw [Circuit.SWAP, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary]
    rfl
  have hswap_sec :
      (r.embedUnitary PrimitiveGate.swapUnitary).1 * electronSectorProjector k η *
          (r.embedUnitary PrimitiveGate.swapUnitary).1ᴴ =
        electronSectorProjector k η := by
    rw [pair_embedUnitary_swapUnitary, electronSectorProjector]
    refine permutationUnitary_conj_diagonal (wireSwapEquiv k u v) _ fun idx ↦ ?_
    have hsum : (∑ q : Fin k, (basisBits k (wireSwapEquiv k u v idx) q).val) =
        ∑ q : Fin k, (basisBits k idx q).val := by
      simp_rw [basisBits_wireSwapEquiv]
      exact Equiv.sum_comp (Equiv.swap u v) fun q ↦ (basisBits k idx q).val
    rw [hsum]
  have hcz_sec :
      (r.embedUnitary cz2.eval).1 * electronSectorProjector k η *
          (r.embedUnitary cz2.eval).1ᴴ =
        electronSectorProjector k η := by
    have hunit : (r.embedUnitary cz2.eval).1 * (r.embedUnitary cz2.eval).1ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact (r.embedUnitary cz2.eval).2.2
    have hcomm : (r.embedUnitary cz2.eval).1 * electronSectorProjector k η =
        electronSectorProjector k η * (r.embedUnitary cz2.eval).1 := by
      rw [QRegister.embedUnitary_val, cz2_eval_val, r.embedMatrix_diagonal,
        electronSectorProjector, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      ext idx
      exact mul_comm _ _
    rw [hcomm, Matrix.mul_assoc, hunit, mul_one]
  rw [hsplit, Submonoid.coe_mul, Matrix.conjTranspose_mul]
  calc
    (r.embedUnitary cz2.eval).1 * (r.embedUnitary PrimitiveGate.swapUnitary).1 *
        electronSectorProjector k η *
        ((r.embedUnitary PrimitiveGate.swapUnitary).1ᴴ * (r.embedUnitary cz2.eval).1ᴴ)
      = (r.embedUnitary cz2.eval).1 *
          ((r.embedUnitary PrimitiveGate.swapUnitary).1 * electronSectorProjector k η *
            (r.embedUnitary PrimitiveGate.swapUnitary).1ᴴ) *
          (r.embedUnitary cz2.eval).1ᴴ := by simp only [Matrix.mul_assoc]
    _ = electronSectorProjector k η := by rw [hswap_sec, hcz_sec]

/-!
## Part 6: Zero-`T` Fermionic Un-Interleaving Network (`fswapUninterleave`)
-/

/-- Bubble wire `lo + len` leftwards to `lo` via `len` adjacent `fSWAP`s, shifting wires
`lo .. lo + len - 1` right by `+1`. -/
def fswapBubbleLeft (k lo : ℕ) : (len : ℕ) → (h : lo + len < k) → Circuit k
  | 0, _ => .identity
  | d + 1, h => fswapAdj k (lo + d) (by omega) ;;ᶜ fswapBubbleLeft k lo d (by omega)

/-- Mode index image under `fswapBubbleLeft k lo len h`. -/
def bubbleLeftMap (k lo len : ℕ) (h : lo + len < k) (q : Fin k) : Fin k :=
  if q.val < lo then q
  else if q.val < lo + len then ⟨min (q.val + 1) (k - 1), by have := q.isLt; omega⟩
  else if q.val = lo + len then ⟨lo, by omega⟩
  else q

@[simp]
theorem fswapBubbleLeft_count_t (k lo : ℕ) (len : ℕ) (h : lo + len < k) :
    (fswapBubbleLeft k lo len h).count .T = 0 := by
  induction len with
  | zero => rfl
  | succ d ih => simp [fswapBubbleLeft, ih (by omega)]

@[simp]
theorem fswapBubbleLeft_count_toff (k lo : ℕ) (len : ℕ) (h : lo + len < k) :
    (fswapBubbleLeft k lo len h).count .TOFF = 0 := by
  induction len with
  | zero => rfl
  | succ d ih => simp [fswapBubbleLeft, ih (by omega)]

theorem fswapBubbleLeft_conj_electronSectorProjector (k lo η : ℕ) (len : ℕ) (h : lo + len < k) :
    (fswapBubbleLeft k lo len h).eval.1 * electronSectorProjector k η *
        (fswapBubbleLeft k lo len h).eval.1ᴴ =
      electronSectorProjector k η := by
  induction len with
  | zero => simp [fswapBubbleLeft]
  | succ d ih =>
      simp only [fswapBubbleLeft, Circuit.eval_seq, Submonoid.coe_mul, Matrix.conjTranspose_mul]
      calc
        (fswapBubbleLeft k lo d (by omega)).eval.1 * (fswapAdj k (lo + d) (by omega)).eval.1 *
            electronSectorProjector k η *
            ((fswapAdj k (lo + d) (by omega)).eval.1ᴴ *
              (fswapBubbleLeft k lo d (by omega)).eval.1ᴴ)
          = (fswapBubbleLeft k lo d (by omega)).eval.1 *
              ((fswapAdj k (lo + d) (by omega)).eval.1 * electronSectorProjector k η *
                (fswapAdj k (lo + d) (by omega)).eval.1ᴴ) *
              (fswapBubbleLeft k lo d (by omega)).eval.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = electronSectorProjector k η := by
            rw [fswapAdj_conj_electronSectorProjector, ih (by omega)]

private lemma bubbleLeftMap_step (k lo d : ℕ) (h : lo + (d + 1) < k) (q : Fin k) :
    bubbleLeftMap k lo d (by omega)
        (Equiv.swap ⟨lo + d, by omega⟩ ⟨lo + d + 1, by omega⟩ q) =
      bubbleLeftMap k lo (d + 1) h q := by
  let u : Fin k := ⟨lo + d, by omega⟩
  let v : Fin k := ⟨lo + d + 1, by omega⟩
  have hu_val : u.val = lo + d := rfl
  have hv_val : v.val = lo + d + 1 := rfl
  change bubbleLeftMap k lo d (by omega) (Equiv.swap u v q) = bubbleLeftMap k lo (d + 1) h q
  by_cases h1 : q.val < lo
  · have hswap : Equiv.swap u v q = q :=
      Equiv.swap_apply_of_ne_of_ne (by intro heq; have := congrArg Fin.val heq; omega)
        (by intro heq; have := congrArg Fin.val heq; omega)
    rw [hswap]
    simp [bubbleLeftMap, h1]
  · by_cases h2 : q.val < lo + d
    · have hswap : Equiv.swap u v q = q :=
        Equiv.swap_apply_of_ne_of_ne (by intro heq; have := congrArg Fin.val heq; omega)
          (by intro heq; have := congrArg Fin.val heq; omega)
      have h2' : q.val < lo + (d + 1) := by omega
      rw [hswap]
      simp [bubbleLeftMap, h1, h2, h2']
    · by_cases h3 : q = u
      · subst h3
        rw [Equiv.swap_apply_left]
        apply Fin.ext
        dsimp only [bubbleLeftMap]
        split_ifs <;> dsimp [u, v] at * <;> omega
      · by_cases h4 : q = v
        · subst h4
          rw [Equiv.swap_apply_right]
          apply Fin.ext
          dsimp only [bubbleLeftMap]
          split_ifs <;> dsimp [u, v] at * <;> omega
        · have hgt : lo + (d + 1) < q.val := by
            have hne_u : q.val ≠ lo + d := fun heq ↦ h3 (Fin.ext (by omega))
            have hne_v : q.val ≠ lo + d + 1 := fun heq ↦ h4 (Fin.ext (by omega))
            omega
          have hswap : Equiv.swap u v q = q := Equiv.swap_apply_of_ne_of_ne h3 h4
          rw [hswap]
          have h2' : ¬ q.val < lo + (d + 1) := by omega
          have h3' : q.val ≠ lo + d := by omega
          have h4' : q.val ≠ lo + (d + 1) := by omega
          simp [bubbleLeftMap, h1, h2, h2', h3', h4']

theorem fswapBubbleLeft_conj_jwAnnihilate (k lo : ℕ) (len : ℕ) (h : lo + len < k) (q : Fin k) :
    (fswapBubbleLeft k lo len h).eval.1 * jwAnnihilate k q *
        (fswapBubbleLeft k lo len h).eval.1ᴴ =
      jwAnnihilate k (bubbleLeftMap k lo len h q) := by
  induction len generalizing q with
  | zero =>
      have hmap : bubbleLeftMap k lo 0 h q = q := by
        dsimp only [bubbleLeftMap]
        split_ifs with h1 h2 h3
        · rfl
        · omega
        · exact Fin.ext (by dsimp; omega)
        · rfl
      simp [fswapBubbleLeft, hmap]
  | succ d ih =>
      simp only [fswapBubbleLeft, Circuit.eval_seq, Submonoid.coe_mul, Matrix.conjTranspose_mul]
      calc
        (fswapBubbleLeft k lo d (by omega)).eval.1 * (fswapAdj k (lo + d) (by omega)).eval.1 *
            jwAnnihilate k q *
            ((fswapAdj k (lo + d) (by omega)).eval.1ᴴ *
              (fswapBubbleLeft k lo d (by omega)).eval.1ᴴ)
          = (fswapBubbleLeft k lo d (by omega)).eval.1 *
              ((fswapAdj k (lo + d) (by omega)).eval.1 * jwAnnihilate k q *
                (fswapAdj k (lo + d) (by omega)).eval.1ᴴ) *
              (fswapBubbleLeft k lo d (by omega)).eval.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = jwAnnihilate k (bubbleLeftMap k lo (d + 1) h q) := by
            rw [fswapAdj_conj_jwAnnihilate, ih (by omega), bubbleLeftMap_step]

/-- First `m` stages of fermionic un-interleaving on `2 * N` wires (`0 ≤ m ≤ N`). -/
def fswapUninterleaveStages (N : ℕ) : (m : ℕ) → (hm : m ≤ N) → Circuit (2 * N)
  | 0, _ => .identity
  | m + 1, hm =>
      fswapUninterleaveStages N m (by omega) ;;ᶜ fswapBubbleLeft (2 * N) m m (by omega)

/-- Zero-`T` Clifford fermionic un-interleaving circuit on `2 * N` wires: permutes interleaved
modes `spinOrbital N p 0 = 2 * p` to `p` (`0 .. N - 1`) and `spinOrbital N p 1 = 2 * p + 1` to
`N + p` (`N .. 2 * N - 1`). -/
def fswapUninterleave (N : ℕ) : Circuit (2 * N) :=
  fswapUninterleaveStages N N le_rfl

private lemma fswapUninterleaveStages_count_t (N m : ℕ) (hm : m ≤ N) :
    (fswapUninterleaveStages N m hm).count .T = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fswapUninterleaveStages, ih (by omega)]

private lemma fswapUninterleaveStages_count_toff (N m : ℕ) (hm : m ≤ N) :
    (fswapUninterleaveStages N m hm).count .TOFF = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fswapUninterleaveStages, ih (by omega)]

@[simp]
theorem fswapUninterleave_count_t (N : ℕ) :
    (fswapUninterleave N).count .T = 0 :=
  fswapUninterleaveStages_count_t N N le_rfl

@[simp]
theorem fswapUninterleave_count_toff (N : ℕ) :
    (fswapUninterleave N).count .TOFF = 0 :=
  fswapUninterleaveStages_count_toff N N le_rfl

@[simp]
theorem fswapUninterleave_inverse_count_t (N : ℕ) :
    (fswapUninterleave N).inverse.count .T = 0 := by
  simp

@[simp]
theorem fswapUninterleave_inverse_count_toff (N : ℕ) :
    (fswapUninterleave N).inverse.count .TOFF = 0 := by
  simp

private lemma fswapUninterleaveStages_conj_electronSectorProjector (N η m : ℕ) (hm : m ≤ N) :
    (fswapUninterleaveStages N m hm).eval.1 * electronSectorProjector (2 * N) η *
        (fswapUninterleaveStages N m hm).eval.1ᴴ =
      electronSectorProjector (2 * N) η := by
  induction m with
  | zero => simp [fswapUninterleaveStages]
  | succ m ih =>
      simp only [fswapUninterleaveStages, Circuit.eval_seq, Submonoid.coe_mul,
        Matrix.conjTranspose_mul]
      calc
        (fswapBubbleLeft (2 * N) m m (by omega)).eval.1 *
            (fswapUninterleaveStages N m (by omega)).eval.1 *
            electronSectorProjector (2 * N) η *
            ((fswapUninterleaveStages N m (by omega)).eval.1ᴴ *
              (fswapBubbleLeft (2 * N) m m (by omega)).eval.1ᴴ)
          = (fswapBubbleLeft (2 * N) m m (by omega)).eval.1 *
              ((fswapUninterleaveStages N m (by omega)).eval.1 *
                electronSectorProjector (2 * N) η *
                (fswapUninterleaveStages N m (by omega)).eval.1ᴴ) *
              (fswapBubbleLeft (2 * N) m m (by omega)).eval.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = electronSectorProjector (2 * N) η := by
            rw [ih (by omega), fswapBubbleLeft_conj_electronSectorProjector]

/-- `fswapUninterleave N` preserves the `η`-electron Hamming-weight sector projector. -/
theorem fswapUninterleave_conj_electronSectorProjector (N η : ℕ) :
    (fswapUninterleave N).eval.1 * electronSectorProjector (2 * N) η *
        (fswapUninterleave N).eval.1ᴴ =
      electronSectorProjector (2 * N) η :=
  fswapUninterleaveStages_conj_electronSectorProjector N η N le_rfl

private lemma fswapUninterleaveStages_invariant (N m : ℕ) (hm : m ≤ N) :
    (∀ p : Fin N, p.val < m →
      (fswapUninterleaveStages N m hm).eval.1 *
          jwAnnihilate (2 * N) (spinOrbital N p 0) *
          (fswapUninterleaveStages N m hm).eval.1ᴴ =
        jwAnnihilate (2 * N) ⟨p.val, by omega⟩ ∧
      (fswapUninterleaveStages N m hm).eval.1 *
          jwAnnihilate (2 * N) (spinOrbital N p 1) *
          (fswapUninterleaveStages N m hm).eval.1ᴴ =
        jwAnnihilate (2 * N) ⟨m + p.val, by omega⟩) ∧
    (∀ q : Fin (2 * N), 2 * m ≤ q.val →
      (fswapUninterleaveStages N m hm).eval.1 * jwAnnihilate (2 * N) q *
          (fswapUninterleaveStages N m hm).eval.1ᴴ =
        jwAnnihilate (2 * N) q) := by
  induction m with
  | zero =>
      refine ⟨fun p hp ↦ (Nat.not_lt_zero _ hp).elim, fun q _ ↦ ?_⟩
      simp [fswapUninterleaveStages]
  | succ m ih =>
      obtain ⟨ih_lt, ih_ge⟩ := ih (by omega)
      have hconj_step (q : Fin (2 * N)) :
          (fswapUninterleaveStages N (m + 1) hm).eval.1 * jwAnnihilate (2 * N) q *
              (fswapUninterleaveStages N (m + 1) hm).eval.1ᴴ =
            (fswapBubbleLeft (2 * N) m m (by omega)).eval.1 *
              ((fswapUninterleaveStages N m (by omega)).eval.1 * jwAnnihilate (2 * N) q *
                (fswapUninterleaveStages N m (by omega)).eval.1ᴴ) *
              (fswapBubbleLeft (2 * N) m m (by omega)).eval.1ᴴ := by
        simp only [fswapUninterleaveStages, Circuit.eval_seq, Submonoid.coe_mul,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]
      refine ⟨fun p hp ↦ ?_, fun q hq ↦ ?_⟩
      · by_cases hpm : p.val < m
        · obtain ⟨h0, h1⟩ := ih_lt p hpm
          constructor
          · rw [hconj_step, h0, fswapBubbleLeft_conj_jwAnnihilate]
            congr 1
            exact Fin.ext (by simp [bubbleLeftMap, hpm])
          · rw [hconj_step, h1, fswapBubbleLeft_conj_jwAnnihilate]
            congr 1
            have hn1 : ¬ (m + p.val < m) := by omega
            have hn2 : m + p.val < m + m := by omega
            simp only [bubbleLeftMap, hn1, hn2, ↓reduceIte]
            exact Fin.ext (by dsimp; omega)
        · have hpeq : p.val = m := by omega
          constructor
          · have hge0 : 2 * m ≤ (spinOrbital N p 0).val := by dsimp [spinOrbital]; omega
            rw [hconj_step, ih_ge _ hge0, fswapBubbleLeft_conj_jwAnnihilate]
            congr 1
            apply Fin.ext
            dsimp only [bubbleLeftMap]
            split_ifs <;> dsimp [spinOrbital] at * <;> omega
          · have hge1 : 2 * m ≤ (spinOrbital N p 1).val := by dsimp [spinOrbital]; omega
            rw [hconj_step, ih_ge _ hge1, fswapBubbleLeft_conj_jwAnnihilate]
            congr 1
            have hn1 : ¬ (spinOrbital N p 1).val < m := by dsimp [spinOrbital]; omega
            have hn2 : ¬ (spinOrbital N p 1).val < m + m := by dsimp [spinOrbital]; omega
            have hn3 : (spinOrbital N p 1).val ≠ m + m := by dsimp [spinOrbital]; omega
            simp only [bubbleLeftMap, hn1, hn2, hn3, ↓reduceIte]
            exact Fin.ext (by dsimp [spinOrbital]; omega)
      · have hge : 2 * m ≤ q.val := by omega
        rw [hconj_step, ih_ge q hge, fswapBubbleLeft_conj_jwAnnihilate]
        congr 1
        have hn1 : ¬ q.val < m := by omega
        have hn2 : ¬ q.val < m + m := by omega
        have hn3 : q.val ≠ m + m := by omega
        simp [bubbleLeftMap, hn1, hn2, hn3]

/-- Conjugating `jwAnnihilate (2 * N) (spinOrbital N p 0)` by `fswapUninterleave N` yields
`jwAnnihilate (2 * N) ⟨p.val, _⟩` on spin-`0` block wire `p`. -/
theorem fswapUninterleave_conj_jwAnnihilate_zero (N : ℕ) (p : Fin N) :
    (fswapUninterleave N).eval.1 * jwAnnihilate (2 * N) (spinOrbital N p 0) *
        (fswapUninterleave N).eval.1ᴴ =
      jwAnnihilate (2 * N) ⟨p.val, by omega⟩ :=
  ((fswapUninterleaveStages_invariant N N le_rfl).1 p p.isLt).1

/-- Conjugating `jwAnnihilate (2 * N) (spinOrbital N p 1)` by `fswapUninterleave N` yields
`jwAnnihilate (2 * N) ⟨N + p.val, _⟩` on spin-`1` block wire `N + p`. -/
theorem fswapUninterleave_conj_jwAnnihilate_one (N : ℕ) (p : Fin N) :
    (fswapUninterleave N).eval.1 * jwAnnihilate (2 * N) (spinOrbital N p 1) *
        (fswapUninterleave N).eval.1ᴴ =
      jwAnnihilate (2 * N) ⟨N + p.val, by omega⟩ :=
  ((fswapUninterleaveStages_invariant N N le_rfl).1 p p.isLt).2

/-!
## Part 7: Single-Spin Number / Reflection Operators & Spin-Block Factorization
-/

/-- Single-spin `N`-qubit orbital number operator $\tilde{n}_u = b_u^\dagger b_u$ where
$b_u = \sum_{p : \mathrm{Fin}\,N} u_p a_p$. -/
noncomputable def singleSpinNumberOp {N : ℕ} (u : Fin N → ℝ) : Operator (2 ^ N) :=
  let b := ∑ p : Fin N, (u p : ℂ) • jwAnnihilate N p
  bᴴ * b

/-- Single-spin `N`-qubit orbital reflection $R_u = I - 2 \tilde{n}_u$. -/
noncomputable def singleSpinReflection {N : ℕ} (u : Fin N → ℝ) : Operator (2 ^ N) :=
  1 - (2 : ℂ) • singleSpinNumberOp u

@[simp]
theorem singleSpinNumberOp_conjTranspose {N : ℕ} (u : Fin N → ℝ) :
    (singleSpinNumberOp u)ᴴ = singleSpinNumberOp u := by
  simp [singleSpinNumberOp]

theorem singleSpinNumberOp_mul_self {N : ℕ} {u : Fin N → ℝ} (hu : ∑ p, u p ^ 2 = 1) :
    singleSpinNumberOp u * singleSpinNumberOp u = singleSpinNumberOp u :=
  jwLinearMode_number_idempotent Function.injective_id hu

@[simp]
theorem singleSpinReflection_conjTranspose {N : ℕ} (u : Fin N → ℝ) :
    (singleSpinReflection u)ᴴ = singleSpinReflection u := by
  simp [singleSpinReflection]

theorem singleSpinReflection_mul_self {N : ℕ} {u : Fin N → ℝ} (hu : ∑ p, u p ^ 2 = 1) :
    singleSpinReflection u * singleSpinReflection u = 1 :=
  reflection_mul_self_of_idempotent (singleSpinNumberOp_mul_self hu)

/-- Embedding `jwAnnihilate N p` on the spin-`0` block `0 .. N - 1` of `2 * N` wires is literally
`jwAnnihilate (2 * N) ⟨p.val, _⟩`. -/
theorem block_zero_embedMatrix_jwAnnihilate (N : ℕ) (p : Fin N) (h0 : 0 + N ≤ 2 * N := by omega) :
    (QRegister.block 0 N h0).embedMatrix (jwAnnihilate N p) =
      jwAnnihilate (2 * N) ⟨p.val, by omega⟩ := by
  let r0 : QRegister N (2 * N) := QRegister.block 0 N h0
  have hmap : (Finset.univ.filter (· < p)).map r0.wires =
      Finset.univ.filter (· < (⟨p.val, by omega⟩ : Fin (2 * N))) := by
    ext w
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨q, hqp, rfl⟩
      simpa [r0] using hqp
    · intro hw
      refine ⟨⟨w.val, by omega⟩, hw, ?_⟩
      ext
      simp [r0]
  have hlow : r0.embedMatrix (jwLowering N p) =
      jwLowering (2 * N) ⟨p.val, by omega⟩ := by
    rw [jwLowering, jwLowering, ← QRegister.embedMatrix_compose, compose_singleton]
    congr 2
    ext
    simp [r0]
  rw [jwAnnihilate_eq_jwParity_mul_jwLowering, r0.embedMatrix_mul, embedMatrix_jwParity, hmap,
    hlow, ← jwAnnihilate_eq_jwParity_mul_jwLowering]

/-- On spin-`1` block wire `N + p`, `jwAnnihilate (2 * N) ⟨N + p.val, _⟩` factors into the
`p`-independent spin-`0` parity prefix `Z_0 ⋯ Z_{N-1}` times `(QRegister.block N N _).embedMatrix
(jwAnnihilate N p)`. -/
theorem jwAnnihilate_block_one_eq_parity_mul_embedMatrix (N : ℕ) (p : Fin N)
    (h1 : N + N ≤ 2 * N := by omega) :
    jwAnnihilate (2 * N) ⟨N + p.val, by omega⟩ =
      jwParity (2 * N) (Finset.univ.filter (fun w : Fin (2 * N) ↦ w.val < N)) *
        (QRegister.block N N h1).embedMatrix (jwAnnihilate N p) := by
  let r1 : QRegister N (2 * N) := QRegister.block N N h1
  let s0 : Finset (Fin (2 * N)) := Finset.univ.filter (fun w : Fin (2 * N) ↦ w.val < N)
  have hsplit :
      Finset.univ.filter (· < (⟨N + p.val, by omega⟩ : Fin (2 * N))) =
        s0 ∪ (Finset.univ.filter (· < p)).map r1.wires := by
    ext w
    simp only [s0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
      Fin.lt_def]
    constructor
    · intro hw
      by_cases hwN : w.val < N
      · exact Or.inl hwN
      · right
        refine ⟨⟨w.val - N, by omega⟩, by dsimp; omega, ?_⟩
        ext
        dsimp [r1]
        omega
    · rintro (hwN | ⟨q, hqp, rfl⟩)
      · omega
      · dsimp [r1]
        omega
  have hdisj : Disjoint s0 ((Finset.univ.filter (· < p)).map r1.wires) := by
    rw [Finset.disjoint_left]
    intro w hw0 hw1
    rw [Finset.mem_map] at hw1
    rcases hw1 with ⟨q, _, rfl⟩
    simp only [s0, Finset.mem_filter, Finset.mem_univ, true_and, r1, QRegister.block_apply_val]
      at hw0
    omega
  have hlow : r1.embedMatrix (jwLowering N p) =
      jwLowering (2 * N) ⟨N + p.val, by omega⟩ := by
    rw [jwLowering, jwLowering, ← QRegister.embedMatrix_compose, compose_singleton]
    rfl
  rw [jwAnnihilate_eq_jwParity_mul_jwLowering, hsplit, jwParity_union_of_disjoint hdisj,
    Matrix.mul_assoc, ← embedMatrix_jwParity, ← hlow, ← r1.embedMatrix_mul,
    ← jwAnnihilate_eq_jwParity_mul_jwLowering]

private lemma unitary_conj_mul {d : ℕ} (U : Unitary d) (A B : Operator d) :
    U.1 * (A * B) * U.1ᴴ = (U.1 * A * U.1ᴴ) * (U.1 * B * U.1ᴴ) := by
  have h1 : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  calc
    U.1 * (A * B) * U.1ᴴ = (U.1 * A) * (U.1ᴴ * U.1) * (B * U.1ᴴ) := by
      rw [h1, mul_one]
      simp only [Matrix.mul_assoc]
    _ = (U.1 * A * U.1ᴴ) * (U.1 * B * U.1ᴴ) := by simp only [Matrix.mul_assoc]

private lemma unitary_conj_sum {d : ℕ} {ι : Type*} (U : Unitary d) (s : Finset ι)
    (f : ι → Operator d) :
    U.1 * (∑ i ∈ s, f i) * U.1ᴴ = ∑ i ∈ s, U.1 * f i * U.1ᴴ := by
  rw [Finset.mul_sum, Finset.sum_mul]

@[simp]
theorem embedMatrix_neg {n k : ℕ} (r : QRegister k n) (A : Operator (2 ^ k)) :
    r.embedMatrix (-A) = -r.embedMatrix A := by
  rw [← neg_one_smul ℂ A, r.embedMatrix_smul, neg_one_smul]

@[simp]
theorem embedMatrix_sub {n k : ℕ} (r : QRegister k n) (A B : Operator (2 ^ k)) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  rw [sub_eq_add_neg, r.embedMatrix_add, embedMatrix_neg, ← sub_eq_add_neg]

/-- After conjugating by `fswapUninterleave N`, `orbitalNumberOp N u 0` becomes
`singleSpinNumberOp u` embedded on `QRegister.block 0 N`. -/
theorem fswapUninterleave_conj_orbitalNumberOp_zero (N : ℕ) (u : Fin N → ℝ)
    (h0 : 0 + N ≤ 2 * N := by omega) :
    (fswapUninterleave N).eval.1 * orbitalNumberOp N u 0 * (fswapUninterleave N).eval.1ᴴ =
      (QRegister.block 0 N h0).embedMatrix (singleSpinNumberOp u) := by
  let U := (fswapUninterleave N).eval
  let r0 := QRegister.block 0 N h0
  let b := ∑ p : Fin N, (u p : ℂ) • jwAnnihilate (2 * N) (spinOrbital N p 0)
  have hb : U.1 * b * U.1ᴴ = r0.embedMatrix (∑ p : Fin N, (u p : ℂ) • jwAnnihilate N p) := by
    rw [unitary_conj_sum, r0.embedMatrix_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, r0.embedMatrix_smul,
      fswapUninterleave_conj_jwAnnihilate_zero, block_zero_embedMatrix_jwAnnihilate]
  dsimp only [orbitalNumberOp]
  rw [unitary_conj_mul U bᴴ b]
  have hb_conj : U.1 * bᴴ * U.1ᴴ = (U.1 * b * U.1ᴴ)ᴴ := by
    simp [Matrix.mul_assoc]
  rw [hb_conj, hb, ← r0.embedMatrix_conjTranspose, ← r0.embedMatrix_mul]
  rfl

/-- After conjugating by `fswapUninterleave N`, `orbitalNumberOp N u 1` becomes the EXACT SAME
`singleSpinNumberOp u` embedded on `QRegister.block N N`, because the spin-`0` parity prefix
$(Z_0 \cdots Z_{N-1})^2 = 1$ cancels in $b_{u,1}^\dagger b_{u,1}$. -/
theorem fswapUninterleave_conj_orbitalNumberOp_one (N : ℕ) (u : Fin N → ℝ)
    (h1 : N + N ≤ 2 * N := by omega) :
    (fswapUninterleave N).eval.1 * orbitalNumberOp N u 1 * (fswapUninterleave N).eval.1ᴴ =
      (QRegister.block N N h1).embedMatrix (singleSpinNumberOp u) := by
  let U := (fswapUninterleave N).eval
  let r1 := QRegister.block N N h1
  let P0 := jwParity (2 * N) (Finset.univ.filter (fun w : Fin (2 * N) ↦ w.val < N))
  let b := ∑ p : Fin N, (u p : ℂ) • jwAnnihilate (2 * N) (spinOrbital N p 1)
  let bloc := ∑ p : Fin N, (u p : ℂ) • jwAnnihilate N p
  have hb : U.1 * b * U.1ᴴ = P0 * r1.embedMatrix bloc := by
    rw [unitary_conj_sum, r1.embedMatrix_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, r1.embedMatrix_smul, mul_smul_comm,
      fswapUninterleave_conj_jwAnnihilate_one,
      jwAnnihilate_block_one_eq_parity_mul_embedMatrix N p h1]
  dsimp only [orbitalNumberOp]
  rw [unitary_conj_mul U bᴴ b]
  have hb_conj : U.1 * bᴴ * U.1ᴴ = (U.1 * b * U.1ᴴ)ᴴ := by
    simp [Matrix.mul_assoc]
  rw [hb_conj, hb, Matrix.conjTranspose_mul, jwParity_conjTranspose]
  calc
    ((r1.embedMatrix bloc)ᴴ * P0) * (P0 * r1.embedMatrix bloc)
      = (r1.embedMatrix bloc)ᴴ * (P0 * P0) * r1.embedMatrix bloc := by
        simp only [Matrix.mul_assoc]
    _ = r1.embedMatrix (singleSpinNumberOp u) := by
        rw [jwParity_mul_self, mul_one, ← r1.embedMatrix_conjTranspose, ← r1.embedMatrix_mul]
        rfl

/-- Spin-`0` block factorization of `orbitalReflection N u 0` under `fswapUninterleave N`. -/
theorem fswapUninterleave_conj_orbitalReflection_zero (N : ℕ) (u : Fin N → ℝ)
    (h0 : 0 + N ≤ 2 * N := by omega) :
    (fswapUninterleave N).eval.1 * orbitalReflection N u 0 * (fswapUninterleave N).eval.1ᴴ =
      (QRegister.block 0 N h0).embedMatrix (singleSpinReflection u) := by
  have hunit : (fswapUninterleave N).eval.1 * (fswapUninterleave N).eval.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (fswapUninterleave N).eval.2.2
  rw [orbitalReflection, mul_sub, sub_mul, mul_one, hunit, mul_smul_comm, smul_mul_assoc,
    fswapUninterleave_conj_orbitalNumberOp_zero N u h0, singleSpinReflection]
  simp

/-- Spin-`1` block factorization of `orbitalReflection N u 1` under `fswapUninterleave N` into the
exact same local `singleSpinReflection u` on `QRegister.block N N`. -/
theorem fswapUninterleave_conj_orbitalReflection_one (N : ℕ) (u : Fin N → ℝ)
    (h1 : N + N ≤ 2 * N := by omega) :
    (fswapUninterleave N).eval.1 * orbitalReflection N u 1 * (fswapUninterleave N).eval.1ᴴ =
      (QRegister.block N N h1).embedMatrix (singleSpinReflection u) := by
  have hunit : (fswapUninterleave N).eval.1 * (fswapUninterleave N).eval.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (fswapUninterleave N).eval.2.2
  rw [orbitalReflection, mul_sub, sub_mul, mul_one, hunit, mul_smul_comm, smul_mul_assoc,
    fswapUninterleave_conj_orbitalNumberOp_one N u h1, singleSpinReflection]
  simp

/-- Zero-`T` Clifford fermionic un-interleaving circuit on the `2 * 58 = 116` P450 system wires. -/
abbrev p450FswapUninterleave : Circuit (2 * 58) := fswapUninterleave 58

@[simp]
theorem p450FswapUninterleave_count_t : p450FswapUninterleave.count .T = 0 :=
  fswapUninterleave_count_t 58

@[simp]
theorem p450FswapUninterleave_count_toff : p450FswapUninterleave.count .TOFF = 0 :=
  fswapUninterleave_count_toff 58

theorem p450FswapUninterleave_conj_electronSectorProjector (η : ℕ) :
    p450FswapUninterleave.eval.1 * electronSectorProjector (2 * 58) η *
        p450FswapUninterleave.eval.1ᴴ =
      electronSectorProjector (2 * 58) η :=
  fswapUninterleave_conj_electronSectorProjector 58 η

theorem p450FswapUninterleave_conj_orbitalReflection_zero (u : Fin 58 → ℝ)
    (h0 : 0 + 58 ≤ 2 * 58 := by omega) :
    p450FswapUninterleave.eval.1 * orbitalReflection 58 u 0 * p450FswapUninterleave.eval.1ᴴ =
      (QRegister.block 0 58 h0).embedMatrix (singleSpinReflection u) :=
  fswapUninterleave_conj_orbitalReflection_zero 58 u h0

theorem p450FswapUninterleave_conj_orbitalReflection_one (u : Fin 58 → ℝ)
    (h1 : 58 + 58 ≤ 2 * 58 := by omega) :
    p450FswapUninterleave.eval.1 * orbitalReflection 58 u 1 * p450FswapUninterleave.eval.1ᴴ =
      (QRegister.block 58 58 h1).embedMatrix (singleSpinReflection u) :=
  fswapUninterleave_conj_orbitalReflection_one 58 u h1

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
