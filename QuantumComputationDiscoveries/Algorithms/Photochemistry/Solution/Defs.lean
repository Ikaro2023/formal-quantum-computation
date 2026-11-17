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
public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Primitives.Measure
public import QuantumComputationSpecs.Algorithms.StoppingPower
open scoped Matrix
@[expose] public section
namespace QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open Operator
variable {Var : Type}

/-- Qubits per Cartesian coordinate, `n_g` (paper Table IV). -/
abbrev gridBits_frozen : ℕ := 8

/-- The `η = 234` particles: the nuclei `0–46`, then the electrons (the paper's order, Fig. 8). -/
abbrev Particle_frozen := Fin 234

/-- Width `3 η n_g = 5616` of the system register. -/
abbrev systemQubits_frozen : ℕ := 3 * 234 * gridBits_frozen

/--
Box width `L = 44 Å` (paper Table IV) in Bohr radii, with `a₀ = 0.529177210544 Å`
(CODATA 2022).
-/
noncomputable abbrev boxWidth_frozen : ℝ := 44 / 0.529177210544

/-- Grid spacing `Δ = L / (2^{n_g} - 1)` (paper Eq. 5). -/
noncomputable abbrev gridSpacing_frozen : ℝ := boxWidth_frozen / (2 ^ gridBits_frozen - 1)

/-- Evolution time `t = 1 fs` in units of `ħ / E_h = 2.4188843265864 × 10⁻¹⁷ s` (CODATA 2022). -/
noncomputable abbrev evolutionTime_frozen : ℝ := 100 / 2.4188843265864

/-- Atomic number of nucleus `i < 47`: nuclei `0–22` are C, `23–42` H, `43–45` N and `46` O. -/
def atomicNumber_frozen (i : Particle_frozen) : ℕ :=
  if i < 23 then 6 else if i < 43 then 1 else if i < 46 then 7 else 8

/-- Signed charge `(-1)^{σ_i} ζ_i`: `Z` for a nucleus, `-1` for an electron (paper Eqs. 2–3). -/
def charge_frozen (i : Particle_frozen) : ℤ := if i < 47 then atomicNumber_frozen i else -1

/--
AME2020 atomic mass, in daltons, of the most abundant isotope with atomic number
`Z = 1, 6, 7, 8`: ¹H, ¹²C, ¹⁴N, ¹⁶O.
-/
noncomputable def atomicMass_frozen : ℕ → ℝ
  | 1 => 1.007825031898
  | 6 => 12
  | 7 => 14.00307400425
  | _ => 15.99491461926

/--
Mass `m_i` in units of `m_e`: `1` for an electron; for a nucleus, the atomic mass over
`m_e = 5.485799090441 × 10⁻⁴ u` (CODATA 2022) less `Z` electrons. Electron binding energies,
below `2 × 10⁻⁷` of the mass, are neglected.
-/
noncomputable def mass_frozen (i : Particle_frozen) : ℝ :=
  if i < 47 then atomicMass_frozen (atomicNumber_frozen i) / 5.485799090441e-4 -
      atomicNumber_frozen i else 1

/--
Register of coordinate `w` of particle `i`: three consecutive `n_g`-qubit registers per
particle, in particle order.
-/
def coordinateRegister_frozen (i : Particle_frozen)
    (w : Fin 3) : QRegister gridBits_frozen systemQubits_frozen :=
  .block (gridBits_frozen *
      (3 * i + w)) gridBits_frozen (by unfold systemQubits_frozen gridBits_frozen; omega)

/--
Two's-complement value in `[-2^{n_g-1}, 2^{n_g-1} - 1]` of an `n_g`-qubit basis index
(paper Eq. 4).
-/
def twosComplement_frozen (k : Fin (2 ^ gridBits_frozen)) : ℤ :=
    (k.val : ℤ).bmod (2 ^ gridBits_frozen)

/-- Grid position `q_w` of particle `i` in basis state `x`, at `r = q Δ` (paper Eq. 6). -/
def position_frozen (x : Fin (2 ^ systemQubits_frozen)) (i : Particle_frozen) (w : Fin 3) : ℤ :=
  twosComplement_frozen ((coordinateRegister_frozen i w).extractIndex x)

/--
Kinetic energy `T = (2π² / L²) Σ_i Σ_q (‖q‖² / m_i) QFT_i† |q⟩⟨q|_i QFT_i` (paper Eq. 10).
`QFT_i` is the QFT on each coordinate register of particle `i` and `‖q‖² = Σ_w q_w²`, so `T` is a
sum of terms on single coordinate registers.
-/
noncomputable def kineticEnergy_frozen : Operator (2 ^ systemQubits_frozen) :=
  let F := QFT.qftMatrix gridBits_frozen
  ∑ i, ∑ w, ((2 * Real.pi ^ 2 / (boxWidth_frozen ^ 2 * mass_frozen i) : ℝ) : ℂ) •
    (coordinateRegister_frozen i w).embedMatrix
      (Fᴴ * Matrix.diagonal (fun k ↦ (twosComplement_frozen k ^ 2 : ℂ)) * F)

/--
Squared saturation distance in units of `Δ²`: `Γ̃² = 2^{n_Γ} = 8` (`n_Γ = 3`, paper Table IV and
Eq. E7) for a nucleus–nucleus pair, `1` otherwise.
-/
def saturationSq_frozen (i j : Particle_frozen) : ℕ := if i < 47 ∧ j < 47 then 8 else 1

/--
Potential energy `Σ_{i ≠ j} c_i c_j / (2 max(r_ij, Γ̃_ij Δ))`, diagonal in the position basis,
with `r_ij = Δ ‖q_i - q_j‖` and `Γ̃_ij² = saturationSq i j`: Coulomb terms capped at `1 / Δ`
(paper Eqs. 8–9) and nucleus–nucleus terms at `1 / (Γ̃ Δ)` (Sec. III A 1, Eqs. 23–25).
-/
noncomputable def potentialEnergy_frozen : Operator (2 ^ systemQubits_frozen) :=
  Matrix.diagonal fun x ↦ ∑ i, ∑ j, if i = j then 0 else
    (charge_frozen i * charge_frozen j / (2 * gridSpacing_frozen *
      √((max (∑ w, (position_frozen x i w - position_frozen x j w) ^ 2)
          (saturationSq_frozen i j) : ℤ) : ℝ)) : ℝ)

/-- The Hamiltonian `H = T + V` (paper Eq. 2, discretized as in Eqs. 8–10 and 23–25). -/
noncomputable def hamiltonian_frozen : Operator (2 ^ systemQubits_frozen) :=
    kineticEnergy_frozen + potentialEnergy_frozen
end QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs

section QhlCompatLemmas
open Operator Matrix HermitianMat
open scoped ComplexOrder MatrixOrder QHLExpectation
namespace QuantumComputation.Specs.PhotochemistrySolution.QhlAux
noncomputable def qMeasure_outcome_herm {d : ℕ} (M : Operator d)
    (H : HermitianMat (Fin d) ℂ) : HermitianMat (Fin d) ℂ :=
  ⟨Mᴴ * H.1 * M, Matrix.isHermitian_conjTranspose_mul_mul M H.2⟩

@[simp]
lemma qMeasure_outcome_herm_mat {d : ℕ} (M : Operator d) (H : HermitianMat (Fin d) ℂ) :
    (qMeasure_outcome_herm M H).mat = Mᴴ * H.mat * M := rfl

lemma qMeasure_outcome_herm_eq_conj {d : ℕ} (M : Operator d) (H : HermitianMat (Fin d) ℂ) :
    qMeasure_outcome_herm M H = HermitianMat.conj Mᴴ H := by
  ext1; simp [HermitianMat.conj_apply_mat]

lemma qMeasure_outcome_nonneg {d : ℕ} (M : Operator d) {H : HermitianMat (Fin d) ℂ}
    (hH : 0 ≤ H) : 0 ≤ qMeasure_outcome_herm M H := by
  rw [qMeasure_outcome_herm_eq_conj]; exact H.conj_nonneg _ hH

lemma qMeasure_outcome_le_sq {d : ℕ} (M : Operator d) (A : Observable (Fin d)) :
    qMeasure_outcome_herm M A.1 ≤
    (⟨Mᴴ * M, Matrix.isHermitian_conjTranspose_mul_self M⟩ :
      HermitianMat (Fin d) ℂ) := by
  have h_one : (⟨Mᴴ * M, Matrix.isHermitian_conjTranspose_mul_self M⟩ :
      HermitianMat (Fin d) ℂ) = HermitianMat.conj Mᴴ 1 := by
    ext1; simp [HermitianMat.conj_apply_mat]
  rw [qMeasure_outcome_herm_eq_conj, h_one]; exact HermitianMat.conj_mono A.2.2

section
variable {d i : ℕ}

lemma qMeasure_sum_sq_le_one (ℳ : Measurement d i) :
    (∑ o : Fin i, (⟨(ℳ.1 o)ᴴ * (ℳ.1 o),
      Matrix.isHermitian_conjTranspose_mul_self (ℳ.1 o)⟩ :
        HermitianMat (Fin d) ℂ)) ≤ 1 := by
  change (1 - (∑ o : Fin i, (⟨(ℳ.1 o)ᴴ * (ℳ.1 o),
      Matrix.isHermitian_conjTranspose_mul_self (ℳ.1 o)⟩ :
        HermitianMat (Fin d) ℂ)).1).PosSemidef
  have h_mat_sum : (∑ o : Fin i, (⟨(ℳ.1 o)ᴴ * (ℳ.1 o),
      Matrix.isHermitian_conjTranspose_mul_self (ℳ.1 o)⟩ :
        HermitianMat (Fin d) ℂ)).1 =
      ∑ o : Fin i, (ℳ.1 o)ᴴ * (ℳ.1 o) :=
    map_sum (AddSubgroup.subtype (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))) _ _
  rw [h_mat_sum]; exact ℳ.2

lemma qMeasure_sum_nonneg (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    0 ≤ ∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1 :=
  Finset.sum_nonneg fun o _ ↦ qMeasure_outcome_nonneg (ℳ.1 o) (A o).2.1

lemma qMeasure_sum_le_one (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    (∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1) ≤ 1 :=
  (Finset.sum_le_sum fun o _ ↦ qMeasure_outcome_le_sq (ℳ.1 o) (A o)).trans
    (qMeasure_sum_sq_le_one ℳ)

lemma qMeasure_sum_in_observables (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    0 ≤ (∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1) ∧
    (∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1) ≤ 1 :=
  ⟨qMeasure_sum_nonneg ℳ A, qMeasure_sum_le_one ℳ A⟩

noncomputable def qMeasure_obs_map (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    Observable (Fin d) :=
  ⟨∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1,
   qMeasure_sum_in_observables ℳ A⟩

@[simp]
lemma qMeasure_obs_map_coe (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    (qMeasure_obs_map ℳ A).1 = ∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1 := rfl

end

noncomputable def qAssign_obs_map {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    Observable (Fin d) :=
  A.conjUnitary (star U)

@[simp]
lemma qAssign_obs_map_mat {d : ℕ} (U : Unitary d) (M : Observable (Fin d)) :
    (qAssign_obs_map U M).1.1 = U.1ᴴ * M.1.1 * U.1 := by
  simp [qAssign_obs_map, Observable.conjUnitary, Matrix.star_eq_conjTranspose]

@[simp]
protected lemma qAssign_obs_map_val {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    (qAssign_obs_map U A).1 = HermitianMat.conj U.1ᴴ A.1 := by
  ext1;
  simp [qAssign_obs_map, Observable.conjUnitary, Matrix.star_eq_conjTranspose,
      HermitianMat.conj_apply_mat]

lemma qAssign_obs_map_comp {d : ℕ} (U₁ U₂ : Unitary d) (A : Observable (Fin d)) :
    qAssign_obs_map U₁ (qAssign_obs_map U₂ A) = qAssign_obs_map (U₂ * U₁) A := by
  simp [qAssign_obs_map, Observable.conjUnitary_conjUnitary, ← star_mul]

noncomputable def wpQAssignCompat {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (θ : CQAssertion (Store Var) d) : CQAssertion (Store Var) d :=
  fun σ ↦ qAssign_obs_map U (θ σ)

lemma conjUnitary_star_comp {d : ℕ} (U₁ U₂ : Unitary d) (A : Observable (Fin d)) :
    (A.conjUnitary (star U₂)).conjUnitary (star U₁) = A.conjUnitary (star (U₂ * U₁)) := by
  rw [Observable.conjUnitary_conjUnitary, ← star_mul]

@[simp]
lemma wp_qMeasure_apply {Var : Type} [DecidableEq Var] {d i : ℕ} [NeZero d]
    (ℳ : Measurement d i) (x : Var) (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    wp (.qMeasure x ℳ) θ σ =
      qMeasure_obs_map ℳ (fun o ↦ θ.subst x ↑o.1 σ) := by
  apply Subtype.ext
  simp [qMeasure_obs_map_coe, qMeasure_outcome_herm_eq_conj]

abbrev triple {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (Θ : CQAssertion (Store Var) d) (c : QProg Var d) (Ψ : CQAssertion (Store Var) d) : Prop :=
  Triple Θ c Ψ

def hadamardPhase (x : ZMod 2) : ℂ := if x = 1 then -1 else 1

theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem hadamardAt_apply_phase (n : ℕ) (x : Fin n) (i j : Fin (2 ^ n)) :
    (hadamardAt n x).1 i j =
      if ∀ m ≠ x, basisBits n i m = basisBits n j m then
        (1 / Real.sqrt 2 : ℂ) * hadamardPhase (basisBits n i x * basisBits n j x)
      else 0 := by
  rw [hadamardAt_apply]
  split_ifs with h
  · apply congrArg ((1 / Real.sqrt 2 : ℂ) * ·)
    rcases zmodTwo_eq_zero_or_one (basisBits n i x * basisBits n j x) with h0 | h1
    · rw [h0]; simp [hadamardPhase]
    · rw [h1]; simp [hadamardPhase]
  · rfl

abbrev basisBitsEquiv (q : ℕ) : Fin (2 ^ q) ≃ BitAssignment q := basisBits q

theorem basisBits_div_mod (q : ℕ) (j : Fin (2 ^ q)) (i : Fin q) :
    @DFunLike.coe (no_index (Fin (2 ^ q) ≃ BitAssignment q)) (no_index (Fin (2 ^ q)))
      (no_index fun _ => BitAssignment q) (no_index EquivLike.toFunLike) (basisBits q) j i =
      (j.val / 2 ^ i.val % 2 : ℕ) :=
  basisBits_eq_div_mod q j i

@[simp]
theorem basisBits_0 (q : ℕ) (i : Fin q) :
    @DFunLike.coe (no_index (Fin (2 ^ q) ≃ BitAssignment q)) (no_index (Fin (2 ^ q)))
      (no_index fun _ => BitAssignment q) (no_index EquivLike.toFunLike) (basisBits q)
      (@OfNat.ofNat (no_index (Fin (2 ^ q))) 0 (no_index inferInstance)) i = 0 := by
  simp [basisBits_div_mod]

@[simp]
lemma basisBits_bitRevEquiv_coe (n : ℕ) (j : Fin (2 ^ n)) (k : Fin n) :
    @DFunLike.coe (no_index (Fin (2 ^ n) ≃ BitAssignment n)) (no_index (Fin (2 ^ n)))
      (no_index fun _ => BitAssignment n) (no_index EquivLike.toFunLike) (basisBits n)
      (bitRevEquiv n j) k = basisBits n j (Fin.rev k) :=
  basisBits_bitRevEquiv n j k

end QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
namespace QuantumComputation.Specs.PhotochemistrySolution.QRegExt
open _root_.QRegister

@[simp]
theorem basisBits_extractIdx {k n : ℕ} (r : QRegister k n) (j : Fin (2 ^ n)) (i : Fin k) :
    @DFunLike.coe (no_index (Fin (2 ^ k) ≃ BitAssignment k)) (no_index (Fin (2 ^ k)))
      (no_index fun _ => BitAssignment k) (no_index EquivLike.toFunLike) (basisBits k)
      (r.extractIndex j) i = basisBits n j (r i) :=
  r.basisBits_extractIndex j i

theorem basisBits_replaceIdx_apply {k n : ℕ} (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) (i : Fin k) :
    @DFunLike.coe (no_index (Fin (2 ^ n) ≃ BitAssignment n)) (no_index (Fin (2 ^ n)))
      (no_index fun _ => BitAssignment n) (no_index EquivLike.toFunLike) (basisBits n)
      (r.replaceIndex global localIndex) (no_index (r i)) = basisBits k localIndex i :=
  r.basisBits_replaceIndex_apply global localIndex i

theorem basisBits_replaceIdx_of_not_mem {k n : ℕ} (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) (q : Wire n) (hq : q ∉ Set.range r.wires) :
    @DFunLike.coe (no_index (Fin (2 ^ n) ≃ BitAssignment n)) (no_index (Fin (2 ^ n)))
      (no_index fun _ => BitAssignment n) (no_index EquivLike.toFunLike) (basisBits n)
      (r.replaceIndex global localIndex) q = basisBits n global q :=
  r.basisBits_replaceIndex_of_not_mem global localIndex q hq

end QuantumComputation.Specs.PhotochemistrySolution.QRegExt
open QuantumComputation.Specs.PhotochemistrySolution.QRegExt
end QhlCompatLemmas
