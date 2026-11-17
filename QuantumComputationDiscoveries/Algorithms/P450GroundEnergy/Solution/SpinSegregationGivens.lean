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

public import QuantumComputationSpecs.Primitives.THCFactorization

/-!
# Spin Segregation, Zero-`CZ` Spin-Mux & Givens Leaf Algebra

Algebraic and pure-Clifford foundation for the P450 DFTHC `SELECT` & basis-rotation layer:

1. **Adjacent `fSWAP` (`0 T`, `0 TOFF`, self-inverse)**:
   `fswapAdjCircuit n j hj` (`CZ(j, j+1) ;; SWAP(j, j+1)`) conjugates `jwAnnihilate n q` by
   `Equiv.swap ⟨j, _⟩ ⟨j + 1, _⟩` and commutes with `electronSectorProjector n η`.
2. **Outer Spin-Segregation Network (`spinSegregateCircuit N`, `0 T`, `0 TOFF`)**:
   Maps interleaved Jordan–Wigner spin-orbitals `spinOrbital N p σ = 2 * p + σ` onto contiguous
   spin blocks `segregatedSpinIndex N p σ = p + N * σ` (`0 .. N-1` for `σ = 0`, `N .. 2N-1` for
   `σ = 1`), preserving `electronSectorProjector (2 * N) η` and conjugating `orbitalNumberOp` and
   `thcHamiltonian`.
3. **Zero-`CZ` Spin-Block Factorization & `SWAP` Multiplexing**:
   Proves that the spin-`0` parity string `P_α = Z_0 ⋯ Z_{N-1}` cancels (`P_αᴴ * P_α = 1`) in
   every bilinear product inside `segregatedOrbitalNumberOp N u 1`, so
   `segregatedOrbitalNumberOp N u 0 = (block 0 N).embedMatrix (singleSpinOrbitalNumberOp N u)` and
   `segregatedOrbitalNumberOp N u 1 = (block N N).embedMatrix (singleSpinOrbitalNumberOp N u)`.
   Consequently, ordinary `SWAP(p, N + p)` (`p = 0 .. N-1`, with **zero `CZ` parity gates**)
   conjugates spin `1` onto spin `0` identically.
4. **Second-Quantized `givensLeaf` Reflection Bridge**:
   Defines `givensPlaneUnitary φ : Unitary 4` and `givensCascadeUnitary N b k : Unitary (2 ^ N)`,
   proving for all `N` (`[NeZero N]`), `b : ℕ`, and `k : Fin N → ℤ`:
   `(givensCascadeUnitary N b k).1ᴴ * (singleton 0).embedMatrix Qubit.Z.1 *
     (givensCascadeUnitary N b k).1 = 1 - (2 : ℂ) • singleSpinOrbitalNumberOp N (givensLeaf b k)`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensOps

open Operator Matrix Circuit QuantumComputation.Specs
open scoped Matrix Circuit.Notation

local instance (priority := 100000) instNeZeroTwoPowLocal (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Two-Qubit Register & Jordan–Wigner Parity Factoring -/

/-- Ordered two-wire register selecting adjacent physical wires `(j, j + 1)`. -/
def pairAdj (n j : ℕ) (hj : j + 1 < n) : QRegister 2 n :=
  QRegister.pair ⟨j, by omega⟩ ⟨j + 1, hj⟩ (by
    intro h
    injection h with hv
    omega)

@[simp]
theorem pairAdj_zero (n j : ℕ) (hj : j + 1 < n) :
    pairAdj n j hj 0 = ⟨j, by omega⟩ := rfl

@[simp]
theorem pairAdj_one (n j : ℕ) (hj : j + 1 < n) :
    pairAdj n j hj 1 = ⟨j + 1, hj⟩ := rfl

theorem pairAdj_compose_singleton_zero (n j : ℕ) (hj : j + 1 < n) :
    (pairAdj n j hj).compose (QRegister.singleton 0) = QRegister.singleton ⟨j, by omega⟩ := by
  ext i
  rw [Subsingleton.elim i 0]
  rfl

theorem pairAdj_compose_singleton_one (n j : ℕ) (hj : j + 1 < n) :
    (pairAdj n j hj).compose (QRegister.singleton 1) = QRegister.singleton ⟨j + 1, hj⟩ := by
  ext i
  rw [Subsingleton.elim i 0]
  rfl

theorem singleton_disjoint_pairAdj {n j : ℕ} (hj : j + 1 < n) {q : Fin n}
    (hq0 : q.val ≠ j) (hq1 : q.val ≠ j + 1) :
    (QRegister.singleton q).DisjointWires (pairAdj n j hj) := by
  rw [QRegister.disjoint_iff]
  intro a b hab
  rw [Subsingleton.elim a 0] at hab
  match b with
  | ⟨0, _⟩ =>
      have hv : q.val = j := congrArg Fin.val hab
      exact hq0 hv
  | ⟨1, _⟩ =>
      have hv : q.val = j + 1 := congrArg Fin.val hab
      exact hq1 hv

theorem pairAdj_embedMatrix_comm_singleton {n j : ℕ} (hj : j + 1 < n) {q : Fin n}
    (hq0 : q.val ≠ j) (hq1 : q.val ≠ j + 1) (A : Operator 4) (B : Operator 2) :
    (pairAdj n j hj).embedMatrix A * (QRegister.singleton q).embedMatrix B =
      (QRegister.singleton q).embedMatrix B * (pairAdj n j hj).embedMatrix A :=
  QRegister.embedMatrix_comm_of_disjoint (pairAdj n j hj) (QRegister.singleton q)
    (QRegister.disjoint_comm.mp (singleton_disjoint_pairAdj hj hq0 hq1)) A B

/-- Single-qubit Pauli-`Z` embedded at wire `r` of an `n`-qubit system. -/
noncomputable def embedPauliZ (n : ℕ) (r : Fin n) : Operator (2 ^ n) :=
  (QRegister.singleton r).embedMatrix Qubit.Z.1

/-- Single-qubit lowering matrix `|0⟩⟨1|` embedded at wire `r` of an `n`-qubit system. -/
noncomputable def embedLower (n : ℕ) (r : Fin n) : Operator (2 ^ n) :=
  (QRegister.singleton r).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))

theorem qubitZ_eq_diagonal :
    Qubit.Z.1 = Matrix.diagonal (fun b : Fin 2 ↦ (-1 : ℂ) ^ b.val) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qubit.Z]

theorem extractIndex_singleton_val {n : ℕ} (r : Fin n) (i : Fin (2 ^ n)) :
    ((QRegister.singleton r).extractIndex i).val = (basisBits n i r).val := by
  have hb := QRegister.basisBits_extractIndex (QRegister.singleton r) i 0
  have h0 : basisBits 1 ((QRegister.singleton r).extractIndex i) 0 =
      (((QRegister.singleton r).extractIndex i).val : ZMod 2) := by
    rw [basisBits_eq_div_mod]
    have hlt : ((QRegister.singleton r).extractIndex i).val < 2 :=
      ((QRegister.singleton r).extractIndex i).isLt
    simp [Nat.mod_eq_of_lt hlt]
  have hval := congrArg ZMod.val (h0.symm.trans hb)
  have hlt : ((QRegister.singleton r).extractIndex i).val < 2 :=
    ((QRegister.singleton r).extractIndex i).isLt
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] using hval

theorem embedPauliZ_eq_diagonal (n : ℕ) (r : Fin n) :
    embedPauliZ n r = Matrix.diagonal (fun i : Fin (2 ^ n) ↦ (-1 : ℂ) ^ (basisBits n i r).val) := by
  unfold embedPauliZ
  rw [qubitZ_eq_diagonal, QRegister.embedMatrix_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [extractIndex_singleton_val]
  · simp [hij]

/-- Finite product of diagonal matrices over any `Finset` (commuting automatically). -/
noncomputable def zString (n : ℕ) (s : Finset (Fin n)) : Operator (2 ^ n) :=
  Matrix.diagonal (fun i : Fin (2 ^ n) ↦ (-1 : ℂ) ^ ∑ r ∈ s, (basisBits n i r).val)

theorem zString_empty (n : ℕ) : zString n ∅ = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [zString]
  · simp [zString, hij]

theorem zString_singleton (n : ℕ) (r : Fin n) :
    zString n {r} = embedPauliZ n r := by
  rw [embedPauliZ_eq_diagonal]
  ext i j
  by_cases hij : i = j <;> simp [zString, hij]

theorem zString_union_disjoint {n : ℕ} {s t : Finset (Fin n)} (hd : Disjoint s t) :
    zString n (s ∪ t) = zString n s * zString n t := by
  unfold zString
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  rw [Finset.sum_union hd, pow_add]

theorem jwAnnihilate_eq_zString_mul (n : ℕ) (q : Fin n) :
    jwAnnihilate n q = zString n (Finset.univ.filter (· < q)) * embedLower n q := rfl

/-- If every wire in `s` avoids `{j, j + 1}`, `zString n s` commutes with any operator embedded on
`pairAdj n j hj`. -/
theorem zString_comm_pairAdj {n j : ℕ} (hj : j + 1 < n) {s : Finset (Fin n)}
    (hs : ∀ r ∈ s, r.val ≠ j ∧ r.val ≠ j + 1) (A : Operator 4) :
    (pairAdj n j hj).embedMatrix A * zString n s =
      zString n s * (pairAdj n j hj).embedMatrix A := by
  induction s using Finset.cons_induction with
  | empty => simp [zString_empty]
  | cons a t hat ih =>
      have hdisj_at : Disjoint ({a} : Finset (Fin n)) t := by simp [hat]
      have hcons : Finset.cons a t hat = {a} ∪ t := by
        rw [Finset.cons_eq_insert, Finset.insert_eq]
      rw [hcons, zString_union_disjoint hdisj_at, zString_singleton]
      have ha := hs a (by simp)
      have hcomm_a :
          (pairAdj n j hj).embedMatrix A * embedPauliZ n a =
            embedPauliZ n a * (pairAdj n j hj).embedMatrix A :=
        pairAdj_embedMatrix_comm_singleton hj ha.1 ha.2 A Qubit.Z.1
      have hcomm_t :
          (pairAdj n j hj).embedMatrix A * zString n t =
            zString n t * (pairAdj n j hj).embedMatrix A :=
        ih (fun r hr ↦ hs r (by simp [hr]))
      calc
        (pairAdj n j hj).embedMatrix A * (embedPauliZ n a * zString n t)
            = ((pairAdj n j hj).embedMatrix A * embedPauliZ n a) * zString n t := by
                rw [Matrix.mul_assoc]
        _ = embedPauliZ n a * ((pairAdj n j hj).embedMatrix A * zString n t) := by
                rw [hcomm_a, Matrix.mul_assoc]
        _ = (embedPauliZ n a * zString n t) * (pairAdj n j hj).embedMatrix A := by
                rw [hcomm_t, Matrix.mul_assoc]

/-! ## Section 2: Local Two-Qubit Fermionic Modes (`localA0`, `localZ0`, `localA1`) -/

/-- Local two-qubit Jordan–Wigner operators on `Fin 4`. -/
noncomputable def localA0 : Operator 4 :=
  (QRegister.singleton (0 : Fin 2)).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))

noncomputable def localZ0 : Operator 4 :=
  (QRegister.singleton (0 : Fin 2)).embedMatrix Qubit.Z.1

noncomputable def localA1 : Operator 4 :=
  (QRegister.singleton (1 : Fin 2)).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))

theorem pairAdj_embed_localA0 (n j : ℕ) (hj : j + 1 < n) :
    (pairAdj n j hj).embedMatrix localA0 = embedLower n ⟨j, by omega⟩ := by
  unfold localA0 embedLower
  rw [← QRegister.embedMatrix_compose, pairAdj_compose_singleton_zero]

theorem pairAdj_embed_localA1 (n j : ℕ) (hj : j + 1 < n) :
    (pairAdj n j hj).embedMatrix localA1 = embedLower n ⟨j + 1, hj⟩ := by
  unfold localA1 embedLower
  rw [← QRegister.embedMatrix_compose, pairAdj_compose_singleton_one]

theorem pairAdj_embed_localZ0 (n j : ℕ) (hj : j + 1 < n) :
    (pairAdj n j hj).embedMatrix localZ0 = embedPauliZ n ⟨j, by omega⟩ := by
  unfold localZ0 embedPauliZ
  rw [← QRegister.embedMatrix_compose, pairAdj_compose_singleton_zero]

theorem filter_lt_j_plus_one {n j : ℕ} (hj : j + 1 < n) :
    Finset.univ.filter (fun r : Fin n ↦ r < ⟨j + 1, hj⟩) =
      Finset.univ.filter (fun r : Fin n ↦ r < ⟨j, by omega⟩) ∪ {⟨j, by omega⟩} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
  omega

theorem jwAnnihilate_at_pair_zero {n j : ℕ} (hj : j + 1 < n) :
    jwAnnihilate n ⟨j, by omega⟩ =
      zString n (Finset.univ.filter (fun r : Fin n ↦ r < ⟨j, by omega⟩)) *
        (pairAdj n j hj).embedMatrix localA0 := by
  rw [jwAnnihilate_eq_zString_mul, pairAdj_embed_localA0]

theorem jwAnnihilate_at_pair_one {n j : ℕ} (hj : j + 1 < n) :
    jwAnnihilate n ⟨j + 1, hj⟩ =
      zString n (Finset.univ.filter (fun r : Fin n ↦ r < ⟨j, by omega⟩)) *
        (pairAdj n j hj).embedMatrix (localZ0 * localA1) := by
  rw [jwAnnihilate_eq_zString_mul, filter_lt_j_plus_one hj]
  have hd : Disjoint (Finset.univ.filter (fun r : Fin n ↦ r < ⟨j, by omega⟩))
      ({⟨j, by omega⟩} : Finset (Fin n)) := by
    rw [Finset.disjoint_singleton_right]
    simp
  rw [zString_union_disjoint hd, zString_singleton, QRegister.embedMatrix_mul,
    pairAdj_embed_localZ0, pairAdj_embed_localA1, Matrix.mul_assoc]

/-! ## Section 4: `cz2Circuit`, `fswap2Circuit` & `fswapAdjCircuit` -/

private theorem unitary_val_mul {d : ℕ} (U V : Operator.Unitary d) :
    (U * V).1 = U.1 * V.1 := rfl

private theorem extractIndex_singleton0 (x : Fin 4) :
    (QRegister.singleton (0 : Wire 2)).extractIndex x = ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases x <;> apply Fin.ext <;> rw [extractIndex_singleton_val, basisBits_eq_div_mod] <;>
    decide

private theorem extractIndex_singleton1 (x : Fin 4) :
    (QRegister.singleton (1 : Wire 2)).extractIndex x =
      ⟨(x.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases x <;> apply Fin.ext <;> rw [extractIndex_singleton_val, basisBits_eq_div_mod] <;>
    decide

private theorem env_singleton0_iff (i j : Fin 4) :
    (((QRegister.singleton (0 : Wire 2)).basisSplitEquiv i).2 =
      ((QRegister.singleton (0 : Wire 2)).basisSplitEquiv j).2) ↔
      i.val / 2 = j.val / 2 := by
  rw [QRegister.singleton_zero_basisSplit_environment_eq_iff]
  fin_cases i <;> fin_cases j <;> decide

private theorem env_singleton1_iff (i j : Fin 4) :
    (((QRegister.singleton (1 : Wire 2)).basisSplitEquiv i).2 =
      ((QRegister.singleton (1 : Wire 2)).basisSplitEquiv j).2) ↔
      i.val % 2 = j.val % 2 := by
  rw [QRegister.singleton_one_basisSplit_environment_eq_iff]
  fin_cases i <;> fin_cases j <;> decide

private theorem singleton0_embedMatrix_apply (A : Operator 2) (i j : Fin (2 ^ 2)) :
    (QRegister.singleton (0 : Wire 2)).embedMatrix A i j =
      if i.val / 2 = j.val / 2 then
        A ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
      else 0 := by
  rw [QRegister.embedMatrix_apply, extractIndex_singleton0 i, extractIndex_singleton0 j]
  by_cases h : ((QRegister.singleton (0 : Wire 2)).basisSplitEquiv i).2 =
      ((QRegister.singleton (0 : Wire 2)).basisSplitEquiv j).2
  · simp only [h, (env_singleton0_iff i j).mp h, ↓reduceIte, mul_one]
  · have h' : ¬ (i.val / 2 = j.val / 2) := mt (env_singleton0_iff i j).mpr h
    simp only [h, h', ↓reduceIte, mul_zero]

private theorem singleton1_embedMatrix_apply (A : Operator 2) (i j : Fin (2 ^ 2)) :
    (QRegister.singleton (1 : Wire 2)).embedMatrix A i j =
      if i.val % 2 = j.val % 2 then
        A ⟨(i.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ ⟨(j.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
      else 0 := by
  rw [QRegister.embedMatrix_apply, extractIndex_singleton1 i, extractIndex_singleton1 j]
  by_cases h : ((QRegister.singleton (1 : Wire 2)).basisSplitEquiv i).2 =
      ((QRegister.singleton (1 : Wire 2)).basisSplitEquiv j).2
  · simp only [h, (env_singleton1_iff i j).mp h, ↓reduceIte, mul_one]
  · have h' : ¬ (i.val % 2 = j.val % 2) := mt (env_singleton1_iff i j).mpr h
    simp only [h, h', ↓reduceIte, mul_zero]

private theorem localA0_apply (i j : Fin 4) :
    localA0 i j =
      if i.val / 2 = j.val / 2 then
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
          ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
      else 0 :=
  singleton0_embedMatrix_apply _ i j

private theorem localZ0_apply (i j : Fin 4) :
    localZ0 i j =
      if i.val / 2 = j.val / 2 then
        Qubit.Z.1 ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
      else 0 :=
  singleton0_embedMatrix_apply _ i j

private theorem localA1_apply (i j : Fin 4) :
    localA1 i j =
      if i.val % 2 = j.val % 2 then
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
          ⟨(i.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ ⟨(j.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
      else 0 :=
  singleton1_embedMatrix_apply _ i j

/-! ## Section 5: General `fSWAP` Networks & `spinSegregateCircuit N` -/

/-! ## Section 6: Segregated Orbital Operators, Zero-`CZ` Spin-Block Factorization & Spin Swap -/

/-- Orbital number operator on a single `N`-qubit spin block. -/
noncomputable def singleSpinOrbitalNumberOp (N : ℕ) (u : Fin N → ℝ) : Operator (2 ^ N) :=
  let b := ∑ p : Fin N, (u p : ℂ) • jwAnnihilate N p
  bᴴ * b

/-! ## Section 7: Two-Qubit Givens Unitary & `givensLeaf` Reflection Bridge -/

/-- Exact 4×4 single-excitation Givens unitary `G_4(φ)` in little-endian basis
(`|0⟩ = (0,0)`, `|1⟩ = (1,0)`, `|2⟩ = (0,1)`, `|3⟩ = (1,1)`), fixing `|0⟩, |3⟩` and rotating
`|1⟩ ↦ cos φ |1⟩ - sin φ |2⟩`, `|2⟩ ↦ sin φ |1⟩ + cos φ |2⟩`. -/
noncomputable def givensPlaneMatrix (φ : ℝ) : Operator 4 :=
  !![1, 0, 0, 0;
     0, (Real.cos φ : ℂ), (Real.sin φ : ℂ), 0;
     0, (-(Real.sin φ) : ℂ), (Real.cos φ : ℂ), 0;
     0, 0, 0, 1]

private theorem star_complex_cos_ofReal (φ : ℝ) :
    (starRingEnd ℂ) (Complex.cos (φ : ℂ)) = Complex.cos (φ : ℂ) := by
  rw [← Complex.ofReal_cos]
  exact Complex.conj_ofReal (Real.cos φ)

private theorem star_complex_sin_ofReal (φ : ℝ) :
    (starRingEnd ℂ) (Complex.sin (φ : ℂ)) = Complex.sin (φ : ℂ) := by
  rw [← Complex.ofReal_sin]
  exact Complex.conj_ofReal (Real.sin φ)

theorem givensPlaneMatrix_conjTranspose_mul_self (φ : ℝ) :
    (givensPlaneMatrix φ)ᴴ * givensPlaneMatrix φ = 1 := by
  have hcs : Complex.cos (φ : ℂ) ^ 2 + Complex.sin (φ : ℂ) ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq (φ : ℂ)
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [givensPlaneMatrix, star_complex_cos_ofReal, star_complex_sin_ofReal]
  · linear_combination hcs
  · ring
  · ring
  · linear_combination hcs

/-- Bundled two-qubit Givens unitary `G_4(φ) : Unitary 4`. -/
noncomputable def givensPlaneUnitary (φ : ℝ) : Unitary 4 :=
  ⟨givensPlaneMatrix φ, by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using givensPlaneMatrix_conjTranspose_mul_self φ⟩

@[simp]
theorem givensPlaneUnitary_val (φ : ℝ) :
    (givensPlaneUnitary φ).1 = givensPlaneMatrix φ := rfl

theorem givensPlane_conj_localA0 (φ : ℝ) :
    (givensPlaneMatrix φ)ᴴ * localA0 * givensPlaneMatrix φ =
      (Real.cos φ : ℂ) • localA0 + (Real.sin φ : ℂ) • (localZ0 * localA1) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [givensPlaneMatrix, localA0_apply, localZ0_apply, localA1_apply, Qubit.Z,
      star_complex_cos_ofReal, star_complex_sin_ofReal]

/-- **Fused-Apex `p = 0` Identity**: Conjugating `Z_0` on wires `(0, 1)` by `G_4(φ)` equals
`Z_0 * G_4(2 * φ)` (and `G_4(-2 * φ) * Z_0`), collapsing `G_0(φ)ᴴ * Z_0 * G_0(φ)` from two Givens
rotations into **one** double-angle Givens rotation! -/
theorem givensPlane_conj_localZ0_eq_mul_double (φ : ℝ) :
    (givensPlaneMatrix φ)ᴴ * localZ0 * givensPlaneMatrix φ =
      localZ0 * givensPlaneMatrix (2 * φ) := by
  unfold givensPlaneMatrix
  rw [Real.cos_two_mul', Real.sin_two_mul]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [localZ0_apply, Qubit.Z,
      star_complex_cos_ofReal, star_complex_sin_ofReal] <;>
    ring

/-- Adjacent Givens rotation unitary on wires `(p, p + 1)` of an `N`-qubit register. -/
noncomputable def givensAdjUnitary (N p : ℕ) (hp : p + 1 < N) (φ : ℝ) : Unitary (2 ^ N) :=
  (pairAdj N p hp).embedUnitary (givensPlaneUnitary φ)

theorem givensAdjUnitary_conj_jwAnnihilate_self (N p : ℕ) (hp : p + 1 < N) (φ : ℝ) :
    (givensAdjUnitary N p hp φ).1ᴴ * jwAnnihilate N ⟨p, by omega⟩ * (givensAdjUnitary N p hp φ).1 =
      (Real.cos φ : ℂ) • jwAnnihilate N ⟨p, by omega⟩ +
        (Real.sin φ : ℂ) • jwAnnihilate N ⟨p + 1, hp⟩ := by
  let r := pairAdj N p hp
  simp only [givensAdjUnitary, QRegister.embedUnitary_val, givensPlaneUnitary_val,
    ← QRegister.embedMatrix_conjTranspose]
  rw [jwAnnihilate_at_pair_zero hp, jwAnnihilate_at_pair_one hp]
  have hcommZ :
      r.embedMatrix (givensPlaneMatrix φ)ᴴ *
          zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) =
        zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) *
          r.embedMatrix (givensPlaneMatrix φ)ᴴ := by
    apply zString_comm_pairAdj hp
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hx
    omega
  calc
    r.embedMatrix (givensPlaneMatrix φ)ᴴ *
        (zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) *
          r.embedMatrix localA0) * r.embedMatrix (givensPlaneMatrix φ)
        = (r.embedMatrix (givensPlaneMatrix φ)ᴴ *
            zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩))) *
            (r.embedMatrix localA0 * r.embedMatrix (givensPlaneMatrix φ)) := by
              simp [Matrix.mul_assoc]
    _ = zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) *
          (r.embedMatrix (givensPlaneMatrix φ)ᴴ * r.embedMatrix localA0 *
            r.embedMatrix (givensPlaneMatrix φ)) := by
            rw [hcommZ]; simp [Matrix.mul_assoc]
    _ = zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) *
          r.embedMatrix ((Real.cos φ : ℂ) • localA0 + (Real.sin φ : ℂ) • (localZ0 * localA1)) := by
            rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul, givensPlane_conj_localA0]
    _ = (Real.cos φ : ℂ) •
          (zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) *
            r.embedMatrix localA0) +
        (Real.sin φ : ℂ) •
          (zString N (Finset.univ.filter (fun x : Fin N ↦ x < ⟨p, by omega⟩)) *
            r.embedMatrix (localZ0 * localA1)) := by
            rw [QRegister.embedMatrix_add, QRegister.embedMatrix_smul,
              QRegister.embedMatrix_smul, Matrix.mul_add, Algebra.mul_smul_comm,
              Algebra.mul_smul_comm]

theorem givensAdjUnitary_conj_jwAnnihilate_of_lt (N p : ℕ) (hp : p + 1 < N) (φ : ℝ)
    {q : Fin N} (hq : q.val < p) :
    (givensAdjUnitary N p hp φ).1ᴴ * jwAnnihilate N q * (givensAdjUnitary N p hp φ).1 =
      jwAnnihilate N q := by
  let r := pairAdj N p hp
  simp only [givensAdjUnitary, QRegister.embedUnitary_val, givensPlaneUnitary_val,
    ← QRegister.embedMatrix_conjTranspose, jwAnnihilate_eq_zString_mul]
  have hcommZ :
      r.embedMatrix (givensPlaneMatrix φ)ᴴ * zString N (Finset.univ.filter (· < q)) =
        zString N (Finset.univ.filter (· < q)) * r.embedMatrix (givensPlaneMatrix φ)ᴴ := by
    apply zString_comm_pairAdj hp
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hx
    omega
  have hcommA :
      r.embedMatrix (givensPlaneMatrix φ)ᴴ * embedLower N q =
        embedLower N q * r.embedMatrix (givensPlaneMatrix φ)ᴴ :=
    pairAdj_embedMatrix_comm_singleton hp (by omega) (by omega) _ _
  calc
    r.embedMatrix (givensPlaneMatrix φ)ᴴ *
        (zString N (Finset.univ.filter (· < q)) * embedLower N q) *
        r.embedMatrix (givensPlaneMatrix φ)
        = (r.embedMatrix (givensPlaneMatrix φ)ᴴ * zString N (Finset.univ.filter (· < q))) *
            embedLower N q * r.embedMatrix (givensPlaneMatrix φ) := by simp [Matrix.mul_assoc]
    _ = zString N (Finset.univ.filter (· < q)) *
          (r.embedMatrix (givensPlaneMatrix φ)ᴴ * embedLower N q) *
          r.embedMatrix (givensPlaneMatrix φ) := by rw [hcommZ]; simp [Matrix.mul_assoc]
    _ = zString N (Finset.univ.filter (· < q)) * embedLower N q *
          (r.embedMatrix (givensPlaneMatrix φ)ᴴ * r.embedMatrix (givensPlaneMatrix φ)) := by
          rw [hcommA]; simp [Matrix.mul_assoc]
    _ = zString N (Finset.univ.filter (· < q)) * embedLower N q := by
          rw [← QRegister.embedMatrix_mul, givensPlaneMatrix_conjTranspose_mul_self,
            QRegister.embedMatrix_one, Matrix.mul_one]

/-- Prefix product `U_m = G_0(φ 0) * G_1(φ 1) * ... * G_{m-1}(φ (m-1))` for `m < N`
(corresponding to circuit execution in reverse plane order `p = m - 1` down to `0`). -/
noncomputable def givensCascadePrefix (N : ℕ) (φ : ℕ → ℝ) : (m : ℕ) → (hm : m < N) → Unitary (2 ^ N)
  | 0, _ => 1
  | m + 1, hm => givensCascadePrefix N φ m (by omega) * givensAdjUnitary N m hm (φ m)

theorem givensCascadePrefix_conj_jwAnnihilate_zero (N : ℕ) (φ : ℕ → ℝ) (m : ℕ) (hm : m < N) :
    (givensCascadePrefix N φ m hm).1ᴴ * jwAnnihilate N ⟨0, by omega⟩ *
        (givensCascadePrefix N φ m hm).1 =
      (∑ p : Fin m, (((∏ q ∈ Finset.range p.val, Real.sin (φ q)) * Real.cos (φ p.val) : ℝ) : ℂ) •
          jwAnnihilate N ⟨p.val, by omega⟩) +
        ((∏ q ∈ Finset.range m, Real.sin (φ q) : ℝ) : ℂ) • jwAnnihilate N ⟨m, hm⟩ := by
  induction m with
  | zero => simp [givensCascadePrefix]
  | succ m ih =>
      simp only [givensCascadePrefix, unitary_val_mul, Matrix.conjTranspose_mul]
      let Gm := givensAdjUnitary N m hm (φ m)
      have hstep :
          Gm.1ᴴ * ((givensCascadePrefix N φ m (by omega)).1ᴴ *
              jwAnnihilate N ⟨0, by omega⟩ * (givensCascadePrefix N φ m (by omega)).1) * Gm.1 =
            Gm.1ᴴ * (givensCascadePrefix N φ m (by omega)).1ᴴ *
              jwAnnihilate N ⟨0, by omega⟩ *
              ((givensCascadePrefix N φ m (by omega)).1 * Gm.1) := by
        simp [Matrix.mul_assoc]
      rw [← hstep, ih (by omega), Matrix.mul_add, Matrix.add_mul]
      have hsum_part :
          Gm.1ᴴ * (∑ p : Fin m,
              (((∏ q ∈ Finset.range p.val, Real.sin (φ q)) * Real.cos (φ p.val) : ℝ) : ℂ) •
                jwAnnihilate N ⟨p.val, by omega⟩) * Gm.1 =
            ∑ p : Fin m,
              (((∏ q ∈ Finset.range p.val, Real.sin (φ q)) * Real.cos (φ p.val) : ℝ) : ℂ) •
                jwAnnihilate N ⟨p.val, by omega⟩ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        congr 1
        exact givensAdjUnitary_conj_jwAnnihilate_of_lt N m hm (φ m) p.isLt
      have htail_part :
          Gm.1ᴴ * (((∏ q ∈ Finset.range m, Real.sin (φ q) : ℝ) : ℂ) •
              jwAnnihilate N ⟨m, by omega⟩) * Gm.1 =
            (((∏ q ∈ Finset.range m, Real.sin (φ q)) * Real.cos (φ m) : ℝ) : ℂ) •
                jwAnnihilate N ⟨m, by omega⟩ +
              ((∏ q ∈ Finset.range (m + 1), Real.sin (φ q) : ℝ) : ℂ) •
                jwAnnihilate N ⟨m + 1, hm⟩ := by
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [givensAdjUnitary_conj_jwAnnihilate_self N m hm (φ m), smul_add, smul_smul, smul_smul,
          Finset.prod_range_succ]
        push_cast
        rfl
      rw [hsum_part, htail_part, Fin.sum_univ_castSucc]
      simp [add_assoc]

/-- Full `(N - 1)`-plane Givens cascade unitary `G_0(φ_0) ⋯ G_{N-2}(φ_{N-2})` for `givensLeaf b k`,
where `φ_p = 2 * (2 * π * k_p / 2^b) = 2 * π * k_p / 2^(b - 1)`. -/
noncomputable def givensLeafAngle (N b : ℕ) (k : Fin N → ℤ) (q : ℕ) : ℝ :=
  if h : q < N then 2 * (2 * Real.pi * (k ⟨q, h⟩ : ℝ) / 2 ^ b) else 0

noncomputable def givensCascadeUnitary (N : ℕ) [NeZero N] (b : ℕ) (k : Fin N → ℤ) :
    Unitary (2 ^ N) :=
  givensCascadePrefix N (givensLeafAngle N b k) (N - 1)
    (Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne N)) Nat.zero_lt_one)

theorem givensCascadeUnitary_conj_jwAnnihilate_zero (N : ℕ) [NeZero N] (b : ℕ) (k : Fin N → ℤ) :
    (givensCascadeUnitary N b k).1ᴴ * jwAnnihilate N ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ *
        (givensCascadeUnitary N b k).1 =
      ∑ p : Fin N, (givensLeaf b k p : ℂ) • jwAnnihilate N p := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne N)).symm⟩
  unfold givensCascadeUnitary
  simp only [Nat.add_sub_cancel]
  rw [givensCascadePrefix_conj_jwAnnihilate_zero]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    have hp_eq : (⟨p.val, by omega⟩ : Fin (n + 1)) = p.castSucc := rfl
    rw [hp_eq]
    congr 1
    congr 1
    have hmap :
        (Finset.univ.filter (· < p.castSucc)).map Fin.valEmbedding = Finset.range p.val := by
      rw [Finset.filter_gt_eq_Iio, Fin.map_valEmbedding_Iio]
      simp [Nat.Iio_eq_range]
    have hprod :
        ∏ q ∈ Finset.univ.filter (· < p.castSucc),
            Real.sin (2 * (2 * Real.pi * (k q : ℝ) / 2 ^ b)) =
          ∏ q ∈ Finset.range p.val, Real.sin (givensLeafAngle (n + 1) b k q) := by
      rw [← hmap, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro q _
      simp [givensLeafAngle, q.isLt]
    rw [← hprod]
    have hp_ne : p.val ≠ n := ne_of_lt p.isLt
    have hlt : p.val < n + 1 := by omega
    simp only [givensLeaf, givensLeafAngle, hlt, ↓reduceDIte, Fin.val_castSucc,
      Nat.add_right_cancel_iff, hp_ne, ↓reduceIte]
    rfl
  · have hlast_eq : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [hlast_eq]
    congr 1
    congr 1
    have hlast_val : (Fin.last n).val = n := Fin.val_last n
    have hmap :
        (Finset.univ.filter (· < Fin.last n)).map Fin.valEmbedding = Finset.range n := by
      rw [Finset.filter_gt_eq_Iio, Fin.map_valEmbedding_Iio, hlast_val, Nat.Iio_eq_range]
    have hprod :
        ∏ q ∈ Finset.univ.filter (· < Fin.last n),
            Real.sin (2 * (2 * Real.pi * (k q : ℝ) / 2 ^ b)) =
          ∏ q ∈ Finset.range n, Real.sin (givensLeafAngle (n + 1) b k q) := by
      rw [← hmap, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro q _
      simp [givensLeafAngle, q.isLt]
    rw [← hprod]
    simp [givensLeaf]

private theorem embedMatrix_sub {k n : ℕ} (r : QRegister k n) (A B : Operator (2 ^ k)) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ B, r.embedMatrix_add, r.embedMatrix_smul,
    neg_one_smul, ← sub_eq_add_neg]

theorem pauliZ_zero_eq_one_sub_two_numOp (N : ℕ) [NeZero N] :
    (QRegister.singleton (⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ : Fin N)).embedMatrix Qubit.Z.1 =
      1 - (2 : ℂ) • ((jwAnnihilate N ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)ᴴ *
        jwAnnihilate N ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩) := by
  let z0 : Fin N := ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  change (QRegister.singleton z0).embedMatrix Qubit.Z.1 =
    1 - (2 : ℂ) • ((jwAnnihilate N z0)ᴴ * jwAnnihilate N z0)
  have hfilt : Finset.univ.filter (· < z0) = ∅ := by
    ext q
    simp [z0]
  have hjw0 : jwAnnihilate N z0 =
      (QRegister.singleton z0).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) := by
    rw [jwAnnihilate_eq_zString_mul, hfilt, zString_empty, Matrix.one_mul]
    rfl
  rw [hjw0, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul,
    ← QRegister.embedMatrix_smul, ← QRegister.embedMatrix_one (QRegister.singleton z0),
    ← embedMatrix_sub]
  congr 1
  change Qubit.Z.1 = (1 : Operator 2) - (2 : ℂ) •
    ((Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ *
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.Z]
  norm_num

/-- **Master `givensLeaf` Reflection Theorem**: Conjugating Pauli-`Z` on wire `0` of an `N`-qubit
single-spin register by `givensCascadeUnitary N b k` produces the exact orbital reflection
`1 - 2 • singleSpinOrbitalNumberOp N (givensLeaf b k)`. -/
theorem givensCascadeUnitary_conj_pauliZ0 (N : ℕ) [NeZero N] (b : ℕ) (k : Fin N → ℤ) :
    let z0 : Fin N := ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
    (givensCascadeUnitary N b k).1ᴴ * (QRegister.singleton z0).embedMatrix Qubit.Z.1 *
        (givensCascadeUnitary N b k).1 =
      1 - (2 : ℂ) • singleSpinOrbitalNumberOp N (givensLeaf b k) := by
  intro z0
  let U := givensCascadeUnitary N b k
  have hUU : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  have hUU' : U.1 * U.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.2
  change U.1ᴴ * (QRegister.singleton z0).embedMatrix Qubit.Z.1 * U.1 =
    1 - (2 : ℂ) • singleSpinOrbitalNumberOp N (givensLeaf b k)
  rw [pauliZ_zero_eq_one_sub_two_numOp N, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
  congr 1
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  have hconj : U.1ᴴ * jwAnnihilate N z0 * U.1 =
      ∑ p : Fin N, (givensLeaf b k p : ℂ) • jwAnnihilate N p :=
    givensCascadeUnitary_conj_jwAnnihilate_zero N b k
  have hconj_dag :
      U.1ᴴ * (jwAnnihilate N z0)ᴴ * U.1 =
        (∑ p : Fin N, (givensLeaf b k p : ℂ) • jwAnnihilate N p)ᴴ := by
    rw [← hconj]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold singleSpinOrbitalNumberOp
  dsimp only []
  rw [← hconj_dag, ← hconj]
  calc
    U.1ᴴ * ((jwAnnihilate N z0)ᴴ * jwAnnihilate N z0) * U.1
        = U.1ᴴ * (jwAnnihilate N z0)ᴴ * (U.1 * U.1ᴴ) * jwAnnihilate N z0 * U.1 := by
            rw [hUU']; simp [Matrix.mul_assoc]
    _ = (U.1ᴴ * (jwAnnihilate N z0)ᴴ * U.1) * (U.1ᴴ * jwAnnihilate N z0 * U.1) := by
            simp [Matrix.mul_assoc]

/-- **`N`-Qubit Fused-Apex `p = 0` Identity**: Conjugating Pauli-`Z` on wire `0` by the `p = 0`
plane unitary `G_0(φ)` equals `Z_0 * G_0(2 * φ)`, collapsing the `p = 0` apex of `Uᴴ * Z_0 * U`
from two Givens rotations to **one** double-angle Givens rotation! -/
theorem givensAdjUnitary_zero_conj_pauliZ0 (N : ℕ) (hN : 1 < N) (φ : ℝ) :
    let z0 : Fin N := ⟨0, by omega⟩
    (givensAdjUnitary N 0 hN φ).1ᴴ * (QRegister.singleton z0).embedMatrix Qubit.Z.1 *
        (givensAdjUnitary N 0 hN φ).1 =
      (QRegister.singleton z0).embedMatrix Qubit.Z.1 *
        (givensAdjUnitary N 0 hN (2 * φ)).1 := by
  intro z0
  have hz0 : (QRegister.singleton z0).embedMatrix Qubit.Z.1 =
      (pairAdj N 0 hN).embedMatrix localZ0 := (pairAdj_embed_localZ0 N 0 hN).symm
  simp only [givensAdjUnitary, QRegister.embedUnitary_val, givensPlaneUnitary_val,
    ← QRegister.embedMatrix_conjTranspose, hz0, ← QRegister.embedMatrix_mul]
  rw [givensPlane_conj_localZ0_eq_mul_double]

/-- Tail product `G_1(φ 1) * G_2(φ 2) * ... * G_m(φ m)` (`1 .. m`, omitting apex `p = 0`). -/
noncomputable def givensCascadeTail (N : ℕ) (φ : ℕ → ℝ) :
    (t : ℕ) → (ht : t + 1 < N) → Unitary (2 ^ N)
  | 0, _ => 1
  | t + 1, ht => givensCascadeTail N φ t (by omega) * givensAdjUnitary N (t + 1) ht (φ (t + 1))

theorem givensCascadePrefix_eq_zero_mul_tail (N : ℕ) (φ : ℕ → ℝ) (t : ℕ) (ht : t + 1 < N) :
    givensCascadePrefix N φ (t + 1) ht =
      givensAdjUnitary N 0 (by omega) (φ 0) * givensCascadeTail N φ t ht := by
  induction t with
  | zero =>
      simp [givensCascadePrefix, givensCascadeTail]
  | succ t ih =>
      rw [givensCascadePrefix, givensCascadeTail, ih (by omega), mul_assoc]

/-- **Fused-Apex `givensLeaf` Reflection Theorem**: For `1 < N`, conjugating the fused apex
`Z_0 * G_0(2 * φ_0)` by the `(N - 2)`-plane tail `G_1(φ_1) ⋯ G_{N-2}(φ_{N-2})` produces the exact
orbital reflection `1 - 2 • singleSpinOrbitalNumberOp N (givensLeaf b k)`. -/
theorem givensCascadeTail_conj_fusedApex (N : ℕ) (hN : 1 < N) (b : ℕ) (k : Fin N → ℤ) :
    let z0 : Fin N := ⟨0, by omega⟩
    let U_tail := givensCascadeTail N (givensLeafAngle N b k) (N - 2) (by omega)
    U_tail.1ᴴ *
        ((QRegister.singleton z0).embedMatrix Qubit.Z.1 *
          (givensAdjUnitary N 0 hN (2 * givensLeafAngle N b k 0)).1) *
        U_tail.1 =
      1 - (2 : ℂ) • singleSpinOrbitalNumberOp N (givensLeaf b k) := by
  have : NeZero N := ⟨by omega⟩
  intro z0 U_tail
  have hsplit : givensCascadeUnitary N b k =
      givensAdjUnitary N 0 hN (givensLeafAngle N b k 0) * U_tail := by
    unfold givensCascadeUnitary U_tail
    have h1 := givensCascadePrefix_eq_zero_mul_tail N (givensLeafAngle N b k) (N - 2) (by omega)
    convert h1 using 2
    omega
  have hmaster := givensCascadeUnitary_conj_pauliZ0 N b k
  dsimp only at hmaster
  rw [← hmaster, hsplit, unitary_val_mul, Matrix.conjTranspose_mul]
  calc
    U_tail.1ᴴ *
        ((QRegister.singleton z0).embedMatrix Qubit.Z.1 *
          (givensAdjUnitary N 0 hN (2 * givensLeafAngle N b k 0)).1) *
        U_tail.1
        = U_tail.1ᴴ *
            ((givensAdjUnitary N 0 hN (givensLeafAngle N b k 0)).1ᴴ *
              (QRegister.singleton z0).embedMatrix Qubit.Z.1 *
              (givensAdjUnitary N 0 hN (givensLeafAngle N b k 0)).1) *
            U_tail.1 := by
              rw [givensAdjUnitary_zero_conj_pauliZ0 N hN]
    _ = (U_tail.1ᴴ * (givensAdjUnitary N 0 hN (givensLeafAngle N b k 0)).1ᴴ) *
          (QRegister.singleton z0).embedMatrix Qubit.Z.1 *
          ((givensAdjUnitary N 0 hN (givensLeafAngle N b k 0)).1 * U_tail.1) := by
            simp [Matrix.mul_assoc]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensOps

end
