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

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MeasuresLowEnergiesAux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.RefEnergyCerts

/-!
# `63`-Electron Reference State & Ground-Energy Upper Bound

Certifies a normalized `63`-electron reference state `dfthcRefState` for `thcHamiltonian P450.dfthc`
with verified variational energy upper bound `dfthcRefEnergy`, together with sector-number
conservation `thcHamiltonian_comm_electronSectorProjector` and the instantiated Rayleigh–Ritz
ground-energy and window-threshold corollaries (`exists_isEigen_le_dfthcRefEnergy` and
`T_le_dfthcRefEnergy_add_delta`).
-/

@[expose] public section


namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RefEnergy
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs Operator Matrix Real
open scoped Matrix

/-! ## Section 1: Particle-Number Sector Conservation -/

private def hammingWt (k : ℕ) (i : Fin (2 ^ k)) : ℕ :=
  ∑ q : Fin k, (basisBits k i q).val

private lemma basisBits_one_zero_val (x : Fin (2 ^ 1)) :
    (basisBits 1 x 0).val = x.val := by
  fin_cases x <;> decide

private lemma singleton_extractIndex_val {k : ℕ} (p : Fin k) (i : Fin (2 ^ k)) :
    ((QRegister.singleton p).extractIndex i).val = (basisBits k i p).val := by
  rw [← basisBits_one_zero_val ((QRegister.singleton p).extractIndex i),
    QRegister.basisBits_extractIndex, QRegister.singleton_apply]

private lemma jwLowering_hammingWt_of_ne_zero {k : ℕ} {p : Fin k} {i j : Fin (2 ^ k)}
    (hne : jwLowering k p i j ≠ 0) :
    hammingWt k i + 1 = hammingWt k j := by
  rw [jwLowering, QRegister.embedMatrix_apply_of_agreeOutside] at hne
  have hmul := mul_ne_zero_iff.mp hne
  have hsingle := hmul.1
  have hagree : (QRegister.singleton p).AgreeOutside i j := by
    by_contra hna
    simp [hna] at hne
  rw [QRegister.singleton_agreeOutside] at hagree
  have hex_i : ((QRegister.singleton p).extractIndex i).val = 0 := by
    generalize hx : (QRegister.singleton p).extractIndex i = xi at hsingle ⊢
    generalize hy : (QRegister.singleton p).extractIndex j = xj at hsingle
    fin_cases xi <;> fin_cases xj <;> simp at hsingle ⊢
  have hex_j : ((QRegister.singleton p).extractIndex j).val = 1 := by
    generalize hx : (QRegister.singleton p).extractIndex i = xi at hsingle
    generalize hy : (QRegister.singleton p).extractIndex j = xj at hsingle ⊢
    fin_cases xi <;> fin_cases xj <;> simp at hsingle ⊢
  rw [singleton_extractIndex_val] at hex_i hex_j
  have hi_split :=
    (Finset.add_sum_erase Finset.univ (fun q ↦ (basisBits k i q).val) (Finset.mem_univ p)).symm
  have hj_split :=
    (Finset.add_sum_erase Finset.univ (fun q ↦ (basisBits k j q).val) (Finset.mem_univ p)).symm
  have herase :
      ∑ q ∈ Finset.univ.erase p, (basisBits k i q).val =
        ∑ q ∈ Finset.univ.erase p, (basisBits k j q).val := by
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    rw [hagree q (Finset.ne_of_mem_erase hq)]
  unfold hammingWt
  omega

private lemma jwAnnihilate_hammingWt_of_ne_zero {k : ℕ} {p : Fin k} {i j : Fin (2 ^ k)}
    (hne : jwAnnihilate k p i j ≠ 0) :
    hammingWt k i + 1 = hammingWt k j := by
  rw [jwAnnihilate_eq_jwParity_mul_jwLowering, jwParity, Matrix.diagonal_mul] at hne
  exact jwLowering_hammingWt_of_ne_zero (right_ne_zero_of_mul hne)

private lemma jwCreate_hammingWt_of_ne_zero {k : ℕ} {p : Fin k} {i j : Fin (2 ^ k)}
    (hne : (jwAnnihilate k p)ᴴ i j ≠ 0) :
    hammingWt k j + 1 = hammingWt k i := by
  rw [Matrix.conjTranspose_apply, star_ne_zero] at hne
  exact jwAnnihilate_hammingWt_of_ne_zero hne

private lemma jwCreate_mul_jwAnnihilate_hammingWt {k : ℕ} (p q : Fin k) (i j : Fin (2 ^ k))
    (hne : ((jwAnnihilate k p)ᴴ * jwAnnihilate k q) i j ≠ 0) :
    hammingWt k i = hammingWt k j := by
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 := jwCreate_hammingWt_of_ne_zero (left_ne_zero_of_mul hm)
  have h2 := jwAnnihilate_hammingWt_of_ne_zero (right_ne_zero_of_mul hm)
  omega

private lemma comm_electronSectorProjector_of_hammingWt {k η : ℕ} {A : Operator (2 ^ k)}
    (hA : ∀ i j, A i j ≠ 0 → hammingWt k i = hammingWt k j) :
    A * electronSectorProjector k η = electronSectorProjector k η * A := by
  ext i j
  change (A * Matrix.diagonal (fun x ↦ if hammingWt k x = η then (1 : ℂ) else 0)) i j =
    (Matrix.diagonal (fun x ↦ if hammingWt k x = η then (1 : ℂ) else 0) * A) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : A i j = 0
  · simp [hij]
  · rw [hA i j hij, mul_comm]

private lemma comm_smul_right {d : ℕ} {A P : Operator d} (c : ℂ) (h : A * P = P * A) :
    (c • A) * P = P * (c • A) := by
  rw [Matrix.smul_mul, h, Matrix.mul_smul]

private lemma comm_add_right {d : ℕ} {A B P : Operator d}
    (hA : A * P = P * A) (hB : B * P = P * B) :
    (A + B) * P = P * (A + B) := by
  rw [Matrix.add_mul, Matrix.mul_add, hA, hB]

private lemma comm_mul_right {d : ℕ} {A B P : Operator d}
    (hA : A * P = P * A) (hB : B * P = P * B) :
    (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

private lemma comm_sum_right {ι : Type*} {d : ℕ} (s : Finset ι) (f : ι → Operator d)
    (P : Operator d) (hf : ∀ x ∈ s, f x * P = P * f x) :
    (∑ x ∈ s, f x) * P = P * (∑ x ∈ s, f x) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl hf

private lemma oneBodyHamiltonian_comm_sector {N : ℕ} (h : Matrix (Fin N) (Fin N) ℝ) (η : ℕ) :
    oneBodyHamiltonian h * electronSectorProjector (2 * N) η =
      electronSectorProjector (2 * N) η * oneBodyHamiltonian h := by
  unfold oneBodyHamiltonian
  refine comm_sum_right _ _ _ fun σ _ ↦ comm_sum_right _ _ _ fun p _ ↦
    comm_sum_right _ _ _ fun q _ ↦ comm_smul_right _ ?_
  exact comm_electronSectorProjector_of_hammingWt (jwCreate_mul_jwAnnihilate_hammingWt _ _)

private lemma orbitalNumberOp_comm_sector {N : ℕ} (χ : Fin N → ℝ) (σ : Fin 2) (η : ℕ) :
    orbitalNumberOp N χ σ * electronSectorProjector (2 * N) η =
      electronSectorProjector (2 * N) η * orbitalNumberOp N χ σ := by
  have hexp : orbitalNumberOp N χ σ =
      ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) •
        ((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ *
          jwAnnihilate (2 * N) (spinOrbital N q σ)) := by
    dsimp only [orbitalNumberOp]
    rw [Matrix.conjTranspose_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hconj : ((χ p : ℂ) • jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ =
        (χ p : ℂ) • (jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ := by simp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hconj, smul_mul_smul_comm]
  rw [hexp]
  refine comm_sum_right _ _ _ fun p _ ↦ comm_sum_right _ _ _ fun q _ ↦ comm_smul_right _ ?_
  exact comm_electronSectorProjector_of_hammingWt (jwCreate_mul_jwAnnihilate_hammingWt _ _)

/-! ## Section 2: Midpoint DFTHC Hamiltonian & State-Independent Perturbation Bound -/

/-- Spin-summed orbital number operator `n_{u,0} + n_{u,1}` on `2 * 58` wires. -/
noncomputable def spinSummedNumberOp (u : Fin 58 → ℝ) : Operator (2 ^ (2 * 58)) :=
  orbitalNumberOp 58 u 0 + orbitalNumberOp 58 u 1

/-- Unshifted linear fragment sum `∑_{b < 29} w^{(rc)}_b (n_{u_b, 0} + n_{u_b, 1})` evaluated at
approximate leaf vectors `midChi`. -/
noncomputable def midFragmentK (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ)
    (r : Fin 9) (c : Fin 14) : Operator (2 ^ (2 * 58)) :=
  ∑ b : Fin 29, (P450.weight r c b.castSucc : ℂ) • spinSummedNumberOp (midChi r b)

/-- Normalized fragment LCU operator evaluated at approximate leaf vectors `midChi`. -/
noncomputable def midFragmentLCU (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ)
    (r : Fin 9) (c : Fin 14) : Operator (2 ^ (2 * 58)) :=
  ((15360 : ℂ)⁻¹) •
    ((innerMantissa r c 29 : ℂ) • (1 : Operator (2 ^ (2 * 58))) -
      ∑ b : Fin 29, ∑ σ : Fin 2,
        ((innerMantissa r c b.castSucc : ℂ) / 2) • orbitalReflection 58 (midChi r b) σ)

/-- Midpoint-approximated P450 DFTHC Hamiltonian assembled from approximate one-body vectors `midOB`
and approximate leaf vectors `midChi` with the exact DFTHC scalar weights. -/
noncomputable def dfthcMidHamiltonian (midOB : Fin 58 → Fin 58 → ℝ)
    (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ) : Operator (2 ^ (2 * 58)) :=
  ((∑ ℓ : Fin 58, (P450.oneBodyEigenvalue ℓ : ℂ) • spinSummedNumberOp (midOB ℓ)) +
    ∑ r : Fin 9, ∑ c : Fin 14,
      (P450.fragmentShift r c : ℂ) • midFragmentK midChi r c) +
  ∑ r : Fin 9, ∑ c : Fin 14, (2 : ℂ)⁻¹ • (midFragmentK midChi r c * midFragmentK midChi r c)

private lemma midFragmentLCU_conjTranspose (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ)
    (r : Fin 9) (c : Fin 14) :
    (midFragmentLCU midChi r c)ᴴ = midFragmentLCU midChi r c := by
  unfold midFragmentLCU
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_sum, orbitalReflection_conjTranspose, Complex.star_def, map_inv₀,
    map_ofNat, map_div₀, map_intCast]

private lemma midFragmentShift_add_eq_midFragmentLCU (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ)
    (r : Fin 9) (c : Fin 14) :
    (P450.fragmentShift r c : ℂ) • (1 : Operator (2 ^ (2 * 58))) +
      midFragmentK midChi r c =
      (fragmentScale r c : ℂ) • midFragmentLCU midChi r c := by
  have h := abstract_lcu_contraction
    (fun b σ ↦ orbitalNumberOp 58 (midChi r b) σ)
    (fun b ↦ (innerMantissa r c b : ℝ))
    (fragmentScale r c)
  have hw29 : P450.weight r c 29 =
      (innerMantissa r c 29 : ℝ) * fragmentScale r c / 15360 :=
    weight_eq_innerMantissa r c 29
  have hwb (b : Fin 29) : P450.weight r c b.castSucc =
      (innerMantissa r c b.castSucc : ℝ) * fragmentScale r c / 15360 :=
    weight_eq_innerMantissa r c b.castSucc
  have hshift : P450.fragmentShift r c =
      (innerMantissa r c 29 : ℝ) * fragmentScale r c / 15360 -
        ∑ b : Fin 29, (innerMantissa r c b.castSucc : ℝ) * fragmentScale r c / 15360 := by
    unfold P450.fragmentShift
    rw [hw29]
    simp only [hwb]
  simpa only [hshift, hwb, Complex.ofReal_intCast, orbitalReflection, midFragmentLCU,
    midFragmentK, spinSummedNumberOp] using h

private lemma thcHamiltonian_dfthc_eq_midForm :
    thcHamiltonian P450.dfthc =
      dfthcMidHamiltonian P450.oneBodyVector (fun r b ↦ P450.leafVector (leafIndex r b)) := by
  unfold thcHamiltonian dfthcMidHamiltonian
  congr 1
  · change oneBodyHamiltonian
      ((∑ ℓ : Fin 58, P450.oneBodyEigenvalue ℓ •
          Matrix.vecMulVec (P450.oneBodyVector ℓ) (P450.oneBodyVector ℓ)) +
        ∑ μ : Fin 261, (∑ r : Fin 9, ∑ c : Fin 14,
            P450.fragmentShift r c * P450.fragmentVector r c μ) •
          Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ)) = _
    rw [oneBodyHamiltonian_add, oneBodyHamiltonian_sum, oneBodyHamiltonian_sum]
    congr 1
    · refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
      rw [oneBodyHamiltonian_smul, oneBodyHamiltonian_vecMulVec]
      rfl
    · have hmu (μ : Fin 261) :
          oneBodyHamiltonian ((∑ r : Fin 9, ∑ c : Fin 14,
              P450.fragmentShift r c * P450.fragmentVector r c μ) •
            Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ)) =
          ∑ r : Fin 9, ∑ c : Fin 14,
            (P450.fragmentShift r c : ℂ) •
              ((P450.fragmentVector r c μ : ℂ) •
                spinSummedNumberOp (P450.leafVector μ)) := by
        rw [oneBodyHamiltonian_smul, oneBodyHamiltonian_vecMulVec]
        simp only [spinSummedNumberOp, Complex.ofReal_sum, Complex.ofReal_mul,
          Finset.sum_smul, mul_smul]
      simp only [hmu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [← Finset.smul_sum, sum_fragmentVector_smul]
      rfl
  · have hchi : P450.dfthc.chi = P450.leafVector := rfl
    have hzeta (μ ν : Fin 261) : P450.dfthc.zeta μ ν =
        ∑ r : Fin 9, ∑ c : Fin 14,
          P450.fragmentVector r c μ * P450.fragmentVector r c ν := by
      change (∑ r : Fin 9, ∑ c : Fin 14,
        Matrix.vecMulVec (P450.fragmentVector r c)
          (P450.fragmentVector r c)) μ ν = _
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    simp only [hchi, hzeta]
    have hfactor (r : Fin 9) (c : Fin 14) :
        (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
          ((P450.fragmentVector r c μ * P450.fragmentVector r c ν : ℝ) : ℂ) •
            (orbitalNumberOp 58 (P450.leafVector μ) σ *
              orbitalNumberOp 58 (P450.leafVector ν) τ)) =
        midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c *
          midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c := by
      have hK : (∑ μ : Fin 261, (P450.fragmentVector r c μ : ℂ) •
          spinSummedNumberOp (P450.leafVector μ)) =
          midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c :=
        sum_fragmentVector_smul r c _
      rw [← hK, sum_smul_mul_sum_smul]
      have hspin (μ ν : Fin 261) :
          spinSummedNumberOp (P450.leafVector μ) * spinSummedNumberOp (P450.leafVector ν) =
            ∑ σ : Fin 2, ∑ τ : Fin 2,
              orbitalNumberOp 58 (P450.leafVector μ) σ *
                orbitalNumberOp 58 (P450.leafVector ν) τ :=
        fin2_add_mul_add _ _
      simp only [hspin, Finset.smul_sum]
      exact (sum4_swap _).symm
    have hswap :
        (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
          ((∑ r : Fin 9, ∑ c : Fin 14,
            P450.fragmentVector r c μ * P450.fragmentVector r c ν : ℝ) : ℂ) •
            (orbitalNumberOp 58 (P450.leafVector μ) σ *
              orbitalNumberOp 58 (P450.leafVector ν) τ)) =
        ∑ r : Fin 9, ∑ c : Fin 14,
          midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c *
            midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c := by
      simp only [Complex.ofReal_sum, Finset.sum_smul]
      rw [sum6_swap]
      exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ hfactor r c
    rw [hswap]
    simp only [Finset.smul_sum]

private lemma oneBodyVector_sum_sq (ℓ : Fin 58) : ∑ p, P450.oneBodyVector ℓ p ^ 2 = 1 :=
  givensLeaf_sum_sq 15 _

private lemma leafVector_sum_sq (μ : Fin 261) : ∑ p, P450.leafVector μ p ^ 2 = 1 :=
  givensLeaf_sum_sq 15 _

section PerturbationProof

attribute [local irreducible] P450.leafAngleTable P450.oneBodyAngleTable
  P450.oneBodyWeights P450.fragmentWeights P450.innerWeights
  DataArrays.leafAngleTableArr DataArrays.oneBodyAngleTableArr
  DataArrays.oneBodyWeightsArr DataArrays.fragmentWeightsArr
  QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DataArrays.innerWeightsArr
  oneBodyWeightInt fragmentWeightNat innerMantissa
  P450.leafVector P450.oneBodyVector

private lemma abstract_sos_sub_quadratic {d : ℕ} (H H' : Operator d)
    (t : Fin 58 → ℝ) (N1 N2 : Fin 58 → Fin 2 → Operator d)
    (w2 : Fin 9 → Fin 14 → ℝ) (A1 A2 : Fin 9 → Fin 14 → Operator d)
    (hop : H - H' =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2, (t ℓ : ℂ) • (N1 ℓ σ - N2 ℓ σ)) +
      ∑ r : Fin 9, ∑ c : Fin 14, (w2 r c : ℂ) • ((A1 r c)ᴴ * A1 r c - (A2 r c)ᴴ * A2 r c))
    (ψ : Fin d → ℂ) :
    (star ψ ⬝ᵥ (H *ᵥ ψ)).re - (star ψ ⬝ᵥ (H' *ᵥ ψ)).re =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2, t ℓ *
        ((star ψ ⬝ᵥ (N1 ℓ σ *ᵥ ψ)).re - (star ψ ⬝ᵥ (N2 ℓ σ *ᵥ ψ)).re)) +
      (∑ r : Fin 9, ∑ c : Fin 14, w2 r c *
        ((∑ i, Complex.normSq ((A1 r c *ᵥ ψ) i)) -
          (∑ i, Complex.normSq ((A2 r c *ᵥ ψ) i)))) := by
  have hre : (star ψ ⬝ᵥ (H *ᵥ ψ)).re - (star ψ ⬝ᵥ (H' *ᵥ ψ)).re =
      (star ψ ⬝ᵥ ((H - H') *ᵥ ψ)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  rw [hre, hop, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  congr 1
  · simp only [sum_mulVec_eq, smul_mulVec_eq, Matrix.sub_mulVec, dotProduct_sum,
      dotProduct_smul, dotProduct_sub, smul_eq_mul, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
  · simp only [sum_mulVec_eq, smul_mulVec_eq, Matrix.sub_mulVec, dotProduct_sum,
      dotProduct_smul, dotProduct_sub, smul_eq_mul, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re,
      dotProduct_star_conjTranspose_mul_self_re]

private lemma dfthcMidHamiltonian_sub_sos_form
    (midOB : Fin 58 → Fin 58 → ℝ) (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re -
        (star ψ ⬝ᵥ (dfthcMidHamiltonian midOB midChi *ᵥ ψ)).re =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2, P450.oneBodyEigenvalue ℓ *
        ((star ψ ⬝ᵥ (orbitalNumberOp 58 (P450.oneBodyVector ℓ) σ *ᵥ ψ)).re -
          (star ψ ⬝ᵥ (orbitalNumberOp 58 (midOB ℓ) σ *ᵥ ψ)).re)) +
      (∑ r : Fin 9, ∑ c : Fin 14, (2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) *
        ((∑ i, Complex.normSq ((fragmentLCU r c *ᵥ ψ) i)) -
          (∑ i, Complex.normSq ((midFragmentLCU midChi r c *ᵥ ψ) i)))) := by
  have hfrag_diff (r : Fin 9) (c : Fin 14) :
      ((P450.fragmentShift r c : ℂ) •
          midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c +
        (2 : ℂ)⁻¹ • (midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c *
          midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c)) -
      ((P450.fragmentShift r c : ℂ) • midFragmentK midChi r c +
        (2 : ℂ)⁻¹ • (midFragmentK midChi r c * midFragmentK midChi r c)) =
      ((2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit : ℝ) : ℂ) •
        (((fragmentLCU r c)ᴴ * fragmentLCU r c) -
          ((midFragmentLCU midChi r c)ᴴ * midFragmentLCU midChi r c)) := by
    have h1 := abstract_fragment_square_identity
      (midFragmentK (fun r' b ↦ P450.leafVector (leafIndex r' b)) r c)
      (fragmentLCU r c) (fragmentLCU_conjTranspose r c)
      (P450.fragmentShift r c) (fragmentScale r c)
      (fragmentShift_add_sum_eq_fragmentLCU r c)
    have h2 := abstract_fragment_square_identity
      (midFragmentK midChi r c)
      (midFragmentLCU midChi r c) (midFragmentLCU_conjTranspose midChi r c)
      (P450.fragmentShift r c) (fragmentScale r c)
      (midFragmentShift_add_eq_midFragmentLCU midChi r c)
    have hnonneg : 0 ≤ 4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit := by
      have := coefficientUnit_pos
      positivity
    have hS : 2⁻¹ * fragmentScale r c ^ 2 =
        2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit := by
      rw [Real.sq_sqrt hnonneg]
      ring
    rw [hS] at h1 h2
    have hsub := congrArg₂ (· - ·) h1 h2
    rw [add_sub_add_right_eq_sub, ← smul_sub] at hsub
    exact hsub
  refine abstract_sos_sub_quadratic _ _ _ _ _ _ _ _ ?_ ψ
  rw [thcHamiltonian_dfthc_eq_midForm]
  unfold dfthcMidHamiltonian
  have rearr {d : ℕ} (a1 b1 c1 a2 b2 c2 : Operator d) :
      (a1 + b1 + c1) - (a2 + b2 + c2) = (a1 - a2) + ((b1 + c1) - (b2 + c2)) := by abel
  rw [rearr]
  refine congrArg₂ (· + ·) ?_ ?_
  · unfold spinSummedNumberOp
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
    rw [Fin.sum_univ_two, ← smul_sub, ← smul_add]
    exact congrArg (_ • ·) (by abel)
  · simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ hfrag_diff r c

private lemma sum_normSq_add_le {d : ℕ} (x y : Fin d → ℂ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : ∑ i, Complex.normSq (x i) ≤ A ^ 2) (hy : ∑ i, Complex.normSq (y i) ≤ B ^ 2) :
    ∑ i, Complex.normSq ((x + y) i) ≤ (A + B) ^ 2 := by
  let p : Fin 2 → ℝ := ![A, B]
  have hp : ∀ k ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ p k := by
    intro k _
    fin_cases k <;> simp [p, hA.le, hB.le]
  have hpt (i : Fin d) :
      Complex.normSq (x i + y i) ≤
        (A + B) * (A⁻¹ * Complex.normSq (x i) + B⁻¹ * Complex.normSq (y i)) := by
    let z : Fin 2 → ℂ := ![(A⁻¹ : ℂ) * x i, (B⁻¹ : ℂ) * y i]
    have hcs := complex_normSq_weighted_sum_le Finset.univ p z hp
    have hlhs : (∑ k : Fin 2, (p k : ℂ) * z k) = x i + y i := by
      rw [Fin.sum_univ_two]
      simp only [p, z, Matrix.cons_val_zero, Matrix.cons_val_one, ← mul_assoc]
      have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
      have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
      rw [mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0, one_mul, one_mul]
    have hrhs : (∑ j : Fin 2, p j) * (∑ k : Fin 2, p k * Complex.normSq (z k)) =
        (A + B) * (A⁻¹ * Complex.normSq (x i) + B⁻¹ * Complex.normSq (y i)) := by
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [p, z, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_inv₀,
        Complex.normSq_ofReal]
      field_simp [hA.ne', hB.ne']
    rwa [hlhs, hrhs] at hcs
  calc ∑ i, Complex.normSq ((x + y) i)
      ≤ ∑ i, (A + B) * (A⁻¹ * Complex.normSq (x i) + B⁻¹ * Complex.normSq (y i)) :=
        Finset.sum_le_sum fun i _ ↦ hpt i
    _ = (A + B) * (A⁻¹ * (∑ i, Complex.normSq (x i)) + B⁻¹ * (∑ i, Complex.normSq (y i))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (A + B) * (A⁻¹ * A ^ 2 + B⁻¹ * B ^ 2) := by
        have hAB : 0 ≤ A + B := by linarith
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hAB
        · exact mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hA.le)
        · exact mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hB.le)
    _ = (A + B) ^ 2 := by
        field_simp [hA.ne', hB.ne']

private lemma abs_sum_normSq_sub_le {d : ℕ} (x y : Fin d → ℂ) {M δ : ℝ}
    (hM : 0 < M) (hδ : 0 < δ)
    (hy : ∑ i, Complex.normSq (y i) ≤ M ^ 2)
    (hdiff : ∑ i, Complex.normSq ((x - y) i) ≤ δ ^ 2) :
    |(∑ i, Complex.normSq (x i)) - (∑ i, Complex.normSq (y i))| ≤ (2 * M + δ) * δ := by
  have hpt (i : Fin d) :
      |Complex.normSq (x i) - Complex.normSq (y i)| ≤
        (δ / M) * Complex.normSq (y i) + (M / δ + 1) * Complex.normSq ((x - y) i) := by
    let yr := (y i).re
    let yi := (y i).im
    let dr := (x i - y i).re
    let di := (x i - y i).im
    have hns_y : Complex.normSq (y i) = yr ^ 2 + yi ^ 2 := by
      rw [Complex.normSq_apply]; ring
    have hns_d : Complex.normSq ((x - y) i) = dr ^ 2 + di ^ 2 := by
      change Complex.normSq (x i - y i) = dr ^ 2 + di ^ 2
      rw [Complex.normSq_apply]; ring
    have hns_x : Complex.normSq (x i) = (yr + dr) ^ 2 + (yi + di) ^ 2 := by
      have hx_eq : x i = y i + (x i - y i) := by ring
      rw [hx_eq, Complex.normSq_apply, Complex.add_re, Complex.add_im]
      ring
    rw [hns_x, hns_y, hns_d, abs_le]
    have hsq1 : 0 ≤ (δ / M) * (yr - (M / δ) * dr) ^ 2 := by positivity
    have hsq2 : 0 ≤ (δ / M) * (yi - (M / δ) * di) ^ 2 := by positivity
    have hsq3 : 0 ≤ (δ / M) * (yr + (M / δ) * dr) ^ 2 := by positivity
    have hsq4 : 0 ≤ (δ / M) * (yi + (M / δ) * di) ^ 2 := by positivity
    have hid1 : (δ / M) * (yr - (M / δ) * dr) ^ 2 =
        (δ / M) * yr ^ 2 - 2 * yr * dr + (M / δ) * dr ^ 2 := by
      field_simp [hM.ne', hδ.ne']; ring
    have hid2 : (δ / M) * (yi - (M / δ) * di) ^ 2 =
        (δ / M) * yi ^ 2 - 2 * yi * di + (M / δ) * di ^ 2 := by
      field_simp [hM.ne', hδ.ne']; ring
    have hid3 : (δ / M) * (yr + (M / δ) * dr) ^ 2 =
        (δ / M) * yr ^ 2 + 2 * yr * dr + (M / δ) * dr ^ 2 := by
      field_simp [hM.ne', hδ.ne']; ring
    have hid4 : (δ / M) * (yi + (M / δ) * di) ^ 2 =
        (δ / M) * yi ^ 2 + 2 * yi * di + (M / δ) * di ^ 2 := by
      field_simp [hM.ne', hδ.ne']; ring
    constructor <;> nlinarith [sq_nonneg dr, sq_nonneg di]
  calc |(∑ i, Complex.normSq (x i)) - (∑ i, Complex.normSq (y i))|
      = |∑ i, (Complex.normSq (x i) - Complex.normSq (y i))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |Complex.normSq (x i) - Complex.normSq (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((δ / M) * Complex.normSq (y i) + (M / δ + 1) * Complex.normSq ((x - y) i)) :=
        Finset.sum_le_sum fun i _ ↦ hpt i
    _ = (δ / M) * (∑ i, Complex.normSq (y i)) +
          (M / δ + 1) * (∑ i, Complex.normSq ((x - y) i)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (δ / M) * M ^ 2 + (M / δ + 1) * δ ^ 2 := by
        refine add_le_add (mul_le_mul_of_nonneg_left hy (by positivity))
          (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = (2 * M + δ) * δ := by
        field_simp [hM.ne', hδ.ne']; ring

private lemma jwLinearMode_normSq_bounds {m k : ℕ} {emb : Fin m → Fin k}
    (hemb : Function.Injective emb) (w : Fin m → ℝ) (φ : Fin (2 ^ k) → ℂ) :
    let b := jwLinearMode emb w
    (∑ i, Complex.normSq ((b *ᵥ φ) i)) ≤ (∑ p, w p ^ 2) * (∑ i, Complex.normSq (φ i)) ∧
      (∑ i, Complex.normSq ((bᴴ *ᵥ φ) i)) ≤ (∑ p, w p ^ 2) * (∑ i, Complex.normSq (φ i)) := by
  intro b
  have hanti := jwLinearMode_conjTranspose_anticomm hemb w w
  simp_rw [← sq] at hanti
  have hre := congrArg (fun M : Operator (2 ^ k) ↦ (star φ ⬝ᵥ (M *ᵥ φ)).re) hanti
  have hlhs :
      (star φ ⬝ᵥ ((bᴴ * b + b * bᴴ) *ᵥ φ)).re =
        (∑ i, Complex.normSq ((b *ᵥ φ) i)) + (∑ i, Complex.normSq ((bᴴ *ᵥ φ) i)) := by
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re,
      dotProduct_star_conjTranspose_mul_self_re]
    have hbb : b * bᴴ = (bᴴ)ᴴ * bᴴ := by rw [Matrix.conjTranspose_conjTranspose]
    rw [hbb, dotProduct_star_conjTranspose_mul_self_re]
  have hrhs :
      (star φ ⬝ᵥ ((((∑ p, w p ^ 2 : ℝ) : ℂ) • (1 : Operator (2 ^ k))) *ᵥ φ)).re =
        (∑ p, w p ^ 2) * (∑ i, Complex.normSq (φ i)) := by
    rw [smul_mulVec_eq, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      dotProduct_star_self_re]
  rw [hlhs, hrhs] at hre
  have hnn1 : 0 ≤ ∑ i, Complex.normSq ((b *ᵥ φ) i) :=
    Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
  have hnn2 : 0 ≤ ∑ i, Complex.normSq ((bᴴ *ᵥ φ) i) :=
    Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
  exact ⟨by linarith, by linarith⟩

private lemma orbitalNumberOp_perturbation_bounds_gen {N : ℕ} (hN : (N : ℝ) ≤ 64)
    {u u' : Fin N → ℝ} {δc : ℝ}
    (hδc : 0 < δc) (hu : ∑ p, u p ^ 2 = 1) (herr : ∀ p, |u p - u' p| ≤ δc)
    (σ : Fin 2) (ψ : Fin (2 ^ (2 * N)) → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    |(star ψ ⬝ᵥ (orbitalNumberOp N u σ *ᵥ ψ)).re -
        (star ψ ⬝ᵥ (orbitalNumberOp N u' σ *ᵥ ψ)).re| ≤ (2 + 8 * δc) * (8 * δc) ∧
      ∑ i, Complex.normSq (((orbitalNumberOp N u' σ - orbitalNumberOp N u σ) *ᵥ ψ) i) ≤
        ((2 + 8 * δc) * (8 * δc)) ^ 2 := by
  have hd_sq : ∑ p : Fin N, (u' p - u p) ^ 2 ≤ (8 * δc) ^ 2 := by
    have hpt (p : Fin N) : (u' p - u p) ^ 2 ≤ δc ^ 2 := by
      have h := herr p
      rw [abs_sub_comm] at h
      exact sq_le_sq.mpr (by rwa [abs_of_pos hδc])
    calc ∑ p : Fin N, (u' p - u p) ^ 2
        ≤ ∑ _p : Fin N, δc ^ 2 := Finset.sum_le_sum fun p _ ↦ hpt p
      _ = (N : ℝ) * δc ^ 2 := by simp
      _ ≤ 64 * δc ^ 2 := mul_le_mul_of_nonneg_right hN (sq_nonneg δc)
      _ = (8 * δc) ^ 2 := by ring
  have hu'_sq : ∑ p : Fin N, u' p ^ 2 ≤ (1 + 8 * δc) ^ 2 := by
    have hδ8 : 0 < 8 * δc := by positivity
    have hpt (p : Fin N) :
        u' p ^ 2 ≤ (1 + 8 * δc) * u p ^ 2 + (1 + (8 * δc)⁻¹) * (u' p - u p) ^ 2 := by
      have hsq : 0 ≤ (8 * δc) * (u p - (8 * δc)⁻¹ * (u' p - u p)) ^ 2 := by positivity
      have hid : (8 * δc) * (u p - (8 * δc)⁻¹ * (u' p - u p)) ^ 2 =
          (8 * δc) * u p ^ 2 - 2 * u p * (u' p - u p) + (8 * δc)⁻¹ * (u' p - u p) ^ 2 := by
        field_simp [hδ8.ne']; ring
      have hexp : u' p ^ 2 = u p ^ 2 + 2 * u p * (u' p - u p) + (u' p - u p) ^ 2 := by ring
      nlinarith
    calc ∑ p : Fin N, u' p ^ 2
        ≤ ∑ p : Fin N, ((1 + 8 * δc) * u p ^ 2 + (1 + (8 * δc)⁻¹) * (u' p - u p) ^ 2) :=
          Finset.sum_le_sum fun p _ ↦ hpt p
      _ = (1 + 8 * δc) * (∑ p, u p ^ 2) + (1 + (8 * δc)⁻¹) * (∑ p, (u' p - u p) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 + 8 * δc) * 1 + (1 + (8 * δc)⁻¹) * (8 * δc) ^ 2 := by
          rw [hu]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hd_sq (by positivity))
      _ = (1 + 8 * δc) ^ 2 := by
          field_simp [hδ8.ne']; ring
  set emb := fun p : Fin N ↦ spinOrbital N p σ
  set bu := jwLinearMode emb u
  set bu' := jwLinearMode emb u'
  set bd := jwLinearMode emb (fun p ↦ u' p - u p)
  have hemb : Function.Injective emb := spinOrbital_injective N σ
  have hbd_eq : bu' - bu = bd := by
    simp only [bu', bu, bd, jwLinearMode, ← Finset.sum_sub_distrib, Complex.ofReal_sub, sub_smul]
  have hbu_ψ : ∑ i, Complex.normSq ((bu *ᵥ ψ) i) ≤ 1 ^ 2 := by
    have h := (jwLinearMode_normSq_bounds hemb u ψ).1
    rw [one_pow]
    simpa only [bu, hu, hψ, mul_one] using h
  have hbd_only : ∑ i, Complex.normSq ((bd *ᵥ ψ) i) ≤ (8 * δc) ^ 2 := by
    have h := (jwLinearMode_normSq_bounds hemb (fun p ↦ u' p - u p) ψ).1
    rw [hψ, mul_one] at h
    exact h.trans hd_sq
  have hbd_ψ : ∑ i, Complex.normSq ((bu' *ᵥ ψ - bu *ᵥ ψ) i) ≤ (8 * δc) ^ 2 := by
    rw [← Matrix.sub_mulVec, hbd_eq]
    exact hbd_only
  have hexp_diff :
      |(star ψ ⬝ᵥ (orbitalNumberOp N u σ *ᵥ ψ)).re -
          (star ψ ⬝ᵥ (orbitalNumberOp N u' σ *ᵥ ψ)).re| ≤ (2 + 8 * δc) * (8 * δc) := by
    rw [orbitalNumberOp_eq_jwLinearMode N u σ, orbitalNumberOp_eq_jwLinearMode N u' σ,
      dotProduct_star_conjTranspose_mul_self_re, dotProduct_star_conjTranspose_mul_self_re,
      abs_sub_comm]
    have h := abs_sum_normSq_sub_le (bu' *ᵥ ψ) (bu *ᵥ ψ) zero_lt_one (by positivity) hbu_ψ hbd_ψ
    simpa only [bu', bu, emb, two_mul, one_add_one_eq_two] using h
  have hop_decomp :
      (orbitalNumberOp N u' σ - orbitalNumberOp N u σ) *ᵥ ψ =
        (bu'ᴴ *ᵥ (bd *ᵥ ψ)) + (bdᴴ *ᵥ (bu *ᵥ ψ)) := by
    rw [orbitalNumberOp_eq_jwLinearMode N u' σ, orbitalNumberOp_eq_jwLinearMode N u σ]
    have halg : bu'ᴴ * bu' - buᴴ * bu = bu'ᴴ * bd + bdᴴ * bu := by
      rw [← hbd_eq, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
      abel
    change (bu'ᴴ * bu' - buᴴ * bu) *ᵥ ψ = _
    rw [halg, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have ht1 : ∑ i, Complex.normSq ((bu'ᴴ *ᵥ (bd *ᵥ ψ)) i) ≤ ((1 + 8 * δc) * (8 * δc)) ^ 2 := by
    have h1 := (jwLinearMode_normSq_bounds hemb u' (bd *ᵥ ψ)).2
    calc ∑ i, Complex.normSq ((bu'ᴴ *ᵥ (bd *ᵥ ψ)) i)
        ≤ (∑ p, u' p ^ 2) * (∑ i, Complex.normSq ((bd *ᵥ ψ) i)) := h1
      _ ≤ (1 + 8 * δc) ^ 2 * (8 * δc) ^ 2 :=
          mul_le_mul hu'_sq hbd_only
            (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _) (sq_nonneg _)
      _ = ((1 + 8 * δc) * (8 * δc)) ^ 2 := by ring
  have ht2 : ∑ i, Complex.normSq ((bdᴴ *ᵥ (bu *ᵥ ψ)) i) ≤ (8 * δc) ^ 2 := by
    have h1 := (jwLinearMode_normSq_bounds hemb (fun p ↦ u' p - u p) (bu *ᵥ ψ)).2
    calc ∑ i, Complex.normSq ((bdᴴ *ᵥ (bu *ᵥ ψ)) i)
        ≤ (∑ p, (u' p - u p) ^ 2) * (∑ i, Complex.normSq ((bu *ᵥ ψ) i)) := h1
      _ ≤ (8 * δc) ^ 2 * 1 ^ 2 :=
          mul_le_mul hd_sq hbu_ψ
            (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _) (sq_nonneg _)
      _ = (8 * δc) ^ 2 := by ring
  have hvec_diff :
      ∑ i, Complex.normSq (((orbitalNumberOp N u' σ - orbitalNumberOp N u σ) *ᵥ ψ) i) ≤
        ((2 + 8 * δc) * (8 * δc)) ^ 2 := by
    rw [hop_decomp]
    have hsum := sum_normSq_add_le (bu'ᴴ *ᵥ (bd *ᵥ ψ)) (bdᴴ *ᵥ (bu *ᵥ ψ))
      (by positivity) (by positivity) ht1 ht2
    have heq : ((1 + 8 * δc) * (8 * δc) + 8 * δc) ^ 2 = ((2 + 8 * δc) * (8 * δc)) ^ 2 := by ring
    rwa [heq] at hsum
  exact ⟨hexp_diff, hvec_diff⟩

private lemma orbitalNumberOp_perturbation_bounds {u u' : Fin 58 → ℝ} {δc : ℝ}
    (hδc : 0 < δc) (hu : ∑ p, u p ^ 2 = 1) (herr : ∀ p, |u p - u' p| ≤ δc)
    (σ : Fin 2) (ψ : Fin (2 ^ (2 * 58)) → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    |(star ψ ⬝ᵥ (orbitalNumberOp 58 u σ *ᵥ ψ)).re -
        (star ψ ⬝ᵥ (orbitalNumberOp 58 u' σ *ᵥ ψ)).re| ≤ (2 + 8 * δc) * (8 * δc) ∧
      ∑ i, Complex.normSq (((orbitalNumberOp 58 u' σ - orbitalNumberOp 58 u σ) *ᵥ ψ) i) ≤
        ((2 + 8 * δc) * (8 * δc)) ^ 2 :=
  orbitalNumberOp_perturbation_bounds_gen (by norm_num) hδc hu herr σ ψ hψ

private lemma sum_castSucc_le_sum {n : ℕ} (f : Fin (n + 1) → ℕ) :
    (∑ b : Fin n, f b.castSucc) ≤ ∑ b : Fin (n + 1), f b := by
  rw [Fin.sum_univ_castSucc]
  exact Nat.le_add_right _ _

private lemma abstract_fragmentLCU_sub_normSq_le {d : ℕ}
    (N1 N2 : Fin 29 → Fin 2 → Operator d)
    (m : Fin 30 → ℤ) (hm : ∑ b : Fin 30, (m b).natAbs = 15360)
    (A1 A2 : Operator d)
    (hA1_def : A1 = ((15360 : ℂ)⁻¹) • ((m 29 : ℂ) • (1 : Operator d) -
      ∑ b : Fin 29, ∑ σ : Fin 2, ((m b.castSucc : ℂ) / 2) • ((1 : Operator d) - (2 : ℂ) • N1 b σ)))
    (hA2_def : A2 = ((15360 : ℂ)⁻¹) • ((m 29 : ℂ) • (1 : Operator d) -
      ∑ b : Fin 29, ∑ σ : Fin 2, ((m b.castSucc : ℂ) / 2) • ((1 : Operator d) - (2 : ℂ) • N2 b σ)))
    (ψ : Fin d → ℂ) {εN : ℝ} (hεN : 0 < εN)
    (hA1_norm : ∑ i, Complex.normSq ((A1 *ᵥ ψ) i) ≤ 1 ^ 2)
    (hNb : ∀ b σ, ∑ i, Complex.normSq (((N2 b σ - N1 b σ) *ᵥ ψ) i) ≤ εN ^ 2) :
    |(∑ i, Complex.normSq ((A1 *ᵥ ψ) i)) - (∑ i, Complex.normSq ((A2 *ᵥ ψ) i))| ≤
      (2 + 2 * εN) * (2 * εN) := by
  let coef : Fin 29 → ℝ := fun b ↦ (m b.castSucc : ℝ) / 15360
  let wv : Fin 29 → Fin d → ℂ := fun b x ↦
    (((N2 b 0 - N1 b 0) *ᵥ ψ) + ((N2 b 1 - N1 b 1) *ᵥ ψ)) x
  have hrefl (M1 M2 : Operator d) :
      ((1 : Operator d) - (2 : ℂ) • M1) - ((1 : Operator d) - (2 : ℂ) • M2) =
        (2 : ℂ) • (M2 - M1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hA : A2 - A1 =
      ∑ b : Fin 29, (coef b : ℂ) • ((N2 b 0 - N1 b 0) + (N2 b 1 - N1 b 1)) := by
    rw [hA2_def, hA1_def, ← smul_sub, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_sub_distrib, Fin.sum_univ_two, ← smul_sub, ← smul_sub, hrefl, hrefl,
      smul_smul, smul_smul, ← smul_add, smul_smul]
    refine congrArg (· • _) ?_
    dsimp only [coef]
    push_cast
    ring
  have hdiff_x (x : Fin d) :
      ((A2 - A1) *ᵥ ψ) x = ∑ b : Fin 29, (coef b : ℂ) * wv b x := by
    rw [hA, sum_mulVec_eq]
    simp only [smul_mulVec_eq, Matrix.add_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wv]
  have hwv (b : Fin 29) (_ : b ∈ (Finset.univ : Finset (Fin 29))) :
      ∑ x, Complex.normSq (wv b x) ≤ (2 * εN) ^ 2 := by
    have hsum := sum_normSq_add_le _ _ hεN hεN (hNb b 0) (hNb b 1)
    have htwo : (εN + εN) ^ 2 = (2 * εN) ^ 2 := by ring
    rwa [htwo] at hsum
  have hl1 : ∑ b : Fin 29, |coef b| ≤ 1 := by
    have hcb (b : Fin 29) : |coef b| = ((m b.castSucc).natAbs : ℝ) / 15360 := by
      simp only [coef, abs_div, ← natAbs_cast_real]
      norm_num
    have hsub_sum : (∑ b : Fin 29, (m b.castSucc).natAbs) ≤ ∑ b : Fin 30, (m b).natAbs :=
      sum_castSucc_le_sum (n := 29) (fun b ↦ (m b).natAbs)
    rw [hm] at hsub_sum
    have hreal : (∑ b : Fin 29, ((m b.castSucc).natAbs : ℝ)) ≤ 15360 := by
      exact_mod_cast hsub_sum
    simp only [hcb, ← Finset.sum_div]
    linarith
  have h2εN : 0 < 2 * εN := by linarith
  have hA_diff : ∑ x, Complex.normSq ((A2 *ᵥ ψ - A1 *ᵥ ψ) x) ≤ (2 * εN) ^ 2 := by
    have heq_fn (x : Fin d) :
        Complex.normSq ((A2 *ᵥ ψ - A1 *ᵥ ψ) x) =
          Complex.normSq (∑ b : Fin 29, (coef b : ℂ) * wv b x) := by
      rw [← Matrix.sub_mulVec, hdiff_x]
    rw [Finset.sum_congr rfl fun x _ ↦ heq_fn x]
    exact sum_normSq_lcu_vec_le Finset.univ coef wv ((2 * εN) ^ 2) (sq_nonneg _) hwv hl1
  rw [abs_sub_comm]
  have habs := abs_sum_normSq_sub_le (A2 *ᵥ ψ) (A1 *ᵥ ψ) zero_lt_one h2εN hA1_norm hA_diff
  have htot_eq : (2 * 1 + 2 * εN) * (2 * εN) = (2 + 2 * εN) * (2 * εN) := by ring
  rwa [htot_eq] at habs

private lemma abstract_weighted_sos_bound
    (t : Fin 58 → ℝ) (e1 : Fin 58 → Fin 2 → ℝ)
    (w2 : Fin 9 → Fin 14 → ℝ) (hw2 : ∀ r c, 0 ≤ w2 r c) (e2 : Fin 9 → Fin 14 → ℝ)
    {εTot W : ℝ}
    (he1 : ∀ ℓ σ, |e1 ℓ σ| ≤ εTot) (he2 : ∀ r c, |e2 r c| ≤ εTot)
    (hW : (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |t ℓ|) + (∑ r : Fin 9, ∑ c : Fin 14, w2 r c) = W) :
    |(∑ ℓ : Fin 58, ∑ σ : Fin 2, t ℓ * e1 ℓ σ) +
      (∑ r : Fin 9, ∑ c : Fin 14, w2 r c * e2 r c)| ≤ W * εTot := by
  have h1 :
      |∑ ℓ : Fin 58, ∑ σ : Fin 2, t ℓ * e1 ℓ σ| ≤
        (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |t ℓ|) * εTot := by
    calc |∑ ℓ : Fin 58, ∑ σ : Fin 2, t ℓ * e1 ℓ σ|
        ≤ ∑ ℓ : Fin 58, ∑ σ : Fin 2, |t ℓ| * |e1 ℓ σ| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ ↦ ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
          rw [abs_mul]
      _ ≤ ∑ ℓ : Fin 58, ∑ _σ : Fin 2, |t ℓ| * εTot :=
          Finset.sum_le_sum fun ℓ _ ↦ Finset.sum_le_sum fun σ _ ↦
            mul_le_mul_of_nonneg_left (he1 ℓ σ) (abs_nonneg _)
      _ = (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |t ℓ|) * εTot := by simp only [Finset.sum_mul]
  have h2 :
      |∑ r : Fin 9, ∑ c : Fin 14, w2 r c * e2 r c| ≤
        (∑ r : Fin 9, ∑ c : Fin 14, w2 r c) * εTot := by
    calc |∑ r : Fin 9, ∑ c : Fin 14, w2 r c * e2 r c|
        ≤ ∑ r : Fin 9, ∑ c : Fin 14, w2 r c * |e2 r c| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
          rw [abs_mul, abs_of_nonneg (hw2 r c)]
      _ ≤ ∑ r : Fin 9, ∑ c : Fin 14, w2 r c * εTot :=
          Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun c _ ↦
            mul_le_mul_of_nonneg_left (he2 r c) (hw2 r c)
      _ = (∑ r : Fin 9, ∑ c : Fin 14, w2 r c) * εTot := by simp only [Finset.sum_mul]
  calc |(∑ ℓ : Fin 58, ∑ σ : Fin 2, t ℓ * e1 ℓ σ) +
        (∑ r : Fin 9, ∑ c : Fin 14, w2 r c * e2 r c)|
      ≤ |∑ ℓ : Fin 58, ∑ σ : Fin 2, t ℓ * e1 ℓ σ| +
          |∑ r : Fin 9, ∑ c : Fin 14, w2 r c * e2 r c| := abs_add_le _ _
    _ ≤ (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |t ℓ|) * εTot +
          (∑ r : Fin 9, ∑ c : Fin 14, w2 r c) * εTot := add_le_add h1 h2
    _ = ((∑ ℓ : Fin 58, ∑ _σ : Fin 2, |t ℓ|) +
          (∑ r : Fin 9, ∑ c : Fin 14, w2 r c)) * εTot := by ring
    _ = W * εTot := by rw [hW]

/-- State-independent energy perturbation bound: if `midOB` and `midChi` approximate
`P450.oneBodyVector` and `P450.leafVector` within `2.5 × 10⁻⁸` per entry, then on *every*
normalized state `ψ`, `thcHamiltonian P450.dfthc` and `dfthcMidHamiltonian midOB midChi` have
expectations within `0.0004` Ha (`0.4` mHa). -/
theorem dfthc_energy_sub_mid_le
    (midOB : Fin 58 → Fin 58 → ℝ) (midChi : Fin 9 → Fin 29 → Fin 58 → ℝ)
    (hOB : ∀ ℓ p, |P450.oneBodyVector ℓ p - midOB ℓ p| ≤ (25 : ℝ) / 1000000000)
    (hChi : ∀ r b p, |P450.leafVector (leafIndex r b) p - midChi r b p| ≤ (25 : ℝ) / 1000000000)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    |(star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re -
        (star ψ ⬝ᵥ (dfthcMidHamiltonian midOB midChi *ᵥ ψ)).re| ≤ 0.0004 := by
  let δc : ℝ := (25 : ℝ) / 1000000000
  let εN : ℝ := (2 + 8 * δc) * (8 * δc)
  let εTot : ℝ := (2 + 2 * εN) * (2 * εN)
  have hδc : 0 < δc := by dsimp [δc]; norm_num
  have hεN : 0 < εN := by dsimp [εN, δc]; norm_num
  have hεN_le_tot : εN ≤ εTot := by dsimp [εN, εTot, δc]; norm_num
  have hnum : (2 * 97.3864 : ℝ) * εTot ≤ 0.0004 := by dsimp [εTot, εN, δc]; norm_num
  have hob_pt (ℓ : Fin 58) (σ : Fin 2) :
      |(star ψ ⬝ᵥ (orbitalNumberOp 58 (P450.oneBodyVector ℓ) σ *ᵥ ψ)).re -
          (star ψ ⬝ᵥ (orbitalNumberOp 58 (midOB ℓ) σ *ᵥ ψ)).re| ≤ εTot :=
    (orbitalNumberOp_perturbation_bounds hδc (oneBodyVector_sum_sq ℓ) (hOB ℓ) σ ψ hψ).1.trans
      hεN_le_tot
  have hfrag_pt (r : Fin 9) (c : Fin 14) :
      |(∑ i, Complex.normSq ((fragmentLCU r c *ᵥ ψ) i)) -
          (∑ i, Complex.normSq ((midFragmentLCU midChi r c *ᵥ ψ) i))| ≤ εTot := by
    have hA1_norm : ∑ i, Complex.normSq ((fragmentLCU r c *ᵥ ψ) i) ≤ 1 ^ 2 := by
      rw [one_pow, ← hψ]
      exact sum_normSq_fragmentLCU_mulVec_le r c ψ
    exact abstract_fragmentLCU_sub_normSq_le
      (fun b σ ↦ orbitalNumberOp 58 (P450.leafVector (leafIndex r b)) σ)
      (fun b σ ↦ orbitalNumberOp 58 (midChi r b) σ)
      (innerMantissa r c) (innerWeights_l1_eq_15360 r c)
      (fragmentLCU r c) (midFragmentLCU midChi r c) rfl rfl ψ hεN hA1_norm
      (fun b σ ↦ (orbitalNumberOp_perturbation_bounds hδc (leafVector_sum_sq (leafIndex r b))
        (hChi r b) σ ψ hψ).2)
  have hq_nn : 0 ≤ P450.coefficientUnit := le_of_lt coefficientUnit_pos
  have hw2_nn (r : Fin 9) (c : Fin 14) :
      0 ≤ 2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hq_nn
  rw [dfthcMidHamiltonian_sub_sos_form midOB midChi ψ]
  exact (abstract_weighted_sos_bound _ _ _ hw2_nn _ hob_pt hfrag_pt
    outer_sos_weights_sum_eq_two_lambda).trans hnum

end PerturbationProof

/-! ## Section 3: Single-Determinant CAR Expectation & Reference State -/

attribute [local irreducible] P450.leafAngleTable P450.oneBodyAngleTable
  P450.oneBodyWeights P450.fragmentWeights P450.innerWeights
  DataArrays.leafAngleTableArr DataArrays.oneBodyAngleTableArr
  DataArrays.oneBodyWeightsArr DataArrays.fragmentWeightsArr
  QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DataArrays.innerWeightsArr
  oneBodyWeightInt fragmentWeightNat innerMantissa

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RefEnergy

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix
open scoped Matrix

/-- Any THC Hamiltonian `thcHamiltonian thc` conserves total electron number and therefore
commutes with `electronSectorProjector (2 * N) η` for every `η`. -/
theorem thcHamiltonian_comm_electronSectorProjector {N M : ℕ}
    (thc : THCFactorization N M) (η : ℕ) :
    thcHamiltonian thc * electronSectorProjector (2 * N) η =
      electronSectorProjector (2 * N) η * thcHamiltonian thc := by
  unfold thcHamiltonian
  refine RefEnergy.comm_add_right (RefEnergy.oneBodyHamiltonian_comm_sector _ _)
    (RefEnergy.comm_smul_right _ <| RefEnergy.comm_sum_right _ _ _ fun σ _ ↦
      RefEnergy.comm_sum_right _ _ _ fun τ _ ↦
      RefEnergy.comm_sum_right _ _ _ fun μ _ ↦
      RefEnergy.comm_sum_right _ _ _ fun ν _ ↦
      RefEnergy.comm_smul_right _ <| RefEnergy.comm_mul_right
        (RefEnergy.orbitalNumberOp_comm_sector _ _ _)
        (RefEnergy.orbitalNumberOp_comm_sector _ _ _))

/-- Specialization of `thcHamiltonian_comm_electronSectorProjector` to `P450.dfthc` on the
`63`-electron sector. -/
theorem thcHamiltonian_dfthc_comm_electronSectorProjector :
    thcHamiltonian P450.dfthc * electronSectorProjector (2 * 58) 63 =
      electronSectorProjector (2 * 58) 63 * thcHamiltonian P450.dfthc :=
  thcHamiltonian_comm_electronSectorProjector P450.dfthc 63

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
