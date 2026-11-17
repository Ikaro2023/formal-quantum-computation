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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Base
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert1
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert2
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert3
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert4

/-!
# Quartet (`33`/`30`, `D = 3,000`) Deep Variational Bound

Composes `TightGapDeep63Base` and certificate modules `TightGapDeep63Cert1..4` with the remaining
`17` `decide +kernel` checks to establish the `63`-electron variational Rayleigh-quotient,
eigenvalue, and phase-estimation threshold upper bound `eRef = -130.1526` Ha on
`thcHamiltonian P450.dfthc`.

## References

* B. Huron, J. P. Malrieu, and P. Rancurel, "Iterative perturbation calculations of ground and
  excited state energies from multiconfigurational zeroth-order wavefunctions," *J. Chem. Phys.*
  **58**(12), 5745–5759 (1973), https://doi.org/10.1063/1.1679199.
* G. H. Low et al., "Fast Quantum Simulation of Electronic Structure by Spectral Amplification,"
  *Phys. Rev. X* **15**(4), 041016 (2025), https://doi.org/10.1103/pb2g-j9cw.
* J. J. Goings et al., "Reliably assessing the electronic structure of cytochrome P450 on today's
  classical computers and tomorrow's quantum computers," *Proc. Natl. Acad. Sci. U.S.A.*
  **119**(38), e2203533119 (2022), https://doi.org/10.1073/pnas.2203533119.
-/

set_option maxRecDepth 100000

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert5
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataA
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataB
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataC

lemma modes7_cert_7b_ok : checkBlockModesSliceCert 7 7 7 0 97518429299057368 = true := by
  decide +kernel

lemma modes7_cert_8a_ok : checkBlockModesSliceCert 8 0 7 0 34409720323552384 = true := by
  decide +kernel

lemma modes7_cert_8b_ok : checkBlockModesSliceCert 8 7 7 0 64586524025770594 = true := by
  decide +kernel

lemma ob_cert_ok : checkObCert = true := by
  decide +kernel

lemma final_scale_cert_ok : checkFinalScaleCert = true := by
  decide +kernel

lemma exch_cert_0_ok : checkBlockExchCert 0 8325915944166768 0 = true := by
  decide +kernel

lemma exch_cert_1_ok : checkBlockExchCert 1 7296102674442162 0 = true := by
  decide +kernel

lemma exch_cert_2_ok : checkBlockExchCert 2 5462407046393591 0 = true := by
  decide +kernel

lemma exch_cert_3_ok : checkBlockExchCert 3 8849961447814409 0 = true := by
  decide +kernel

lemma exch_cert_4_ok : checkBlockExchCert 4 4460281320348629 0 = true := by
  decide +kernel

lemma exch_cert_5_ok : checkBlockExchCert 5 8651134748811043 0 = true := by
  decide +kernel

lemma exch_cert_6_ok : checkBlockExchCert 6 5516414852967609 0 = true := by
  decide +kernel

lemma exch_cert_7_ok : checkBlockExchCert 7 4760898606397264 0 = true := by
  decide +kernel

lemma exch_cert_8_ok : checkBlockExchCert 8 6557652866423357 0 = true := by
  decide +kernel

lemma s12_slice_13_ok : checkPhase12SliceCert 1701 239 s12Slice13Cert = true := by
  decide +kernel

lemma s12_slice_14_ok : checkPhase12SliceCert 1940 310 s12Slice14Cert = true := by
  decide +kernel

lemma s12_slice_15_ok : checkPhase12SliceCert 2250 750 s12Slice15Cert = true := by
  decide +kernel

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert5

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Matrix BigOperators QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapBase
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataA
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataB
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataC
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert1
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert2
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert3
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert4
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert5

/-- Certified Quartet (`33`/`30`, `D = 3,000`) variational upper bound (`-130.1526` Ha) on
`dfthc`. -/
noncomputable def deepRefEnergy : ℝ := -130.1526

/-- Reference-energy alias for `deepRefEnergy` (`-130.1526` Ha). -/
noncomputable abbrev dfthcDeepRefEnergyVar : ℝ := deepRefEnergy

theorem exists_state63_leDeepRefEnergy :
    ∃ ψ : Fin (2 ^ (2 * 58)) → ℂ,
      electronSectorProjector (2 * 58) 63 *ᵥ ψ = ψ ∧
      (∑ i, Complex.normSq (ψ i) = 1) ∧
      (star ψ ⬝ᵥ (thcHamiltonian dfthc *ᵥ ψ)).re ≤ deepRefEnergy := by
  unfold deepRefEnergy
  exact exists_state63_leDeepRefEnergy_of_certs
    (cayley_of_ranges cayley_r0_ok cayley_r1_ok cayley_r2_ok)
    (rotOb_of_ranges rot_ob_0_ok rot_ob_1_ok rot_ob_2_ok)
    (rotBlk0_of_ranges rot_blk_0_ok rot_blk_1_ok rot_blk_2_ok rot_blk_3_ok)
    (rotBlk1_of_ranges rot_blk_4_ok rot_blk_5_ok rot_blk_6_ok rot_blk_7_ok)
    (rotBlk2_of_ranges rot_blk_8_ok rot_blk_9_ok rot_blk_10_ok rot_blk_11_ok)
    diag_e0_ok diag_e1_ok diag_e2_ok diag_e3_ok
    diag_e4_ok diag_e5_ok diag_e6_ok diag_e7_ok
    s12_slice_0_ok s12_slice_1_ok s12_slice_2_ok s12_slice_3_ok
    s12_slice_4_ok s12_slice_5_ok s12_slice_6_ok s12_slice_7_ok
    s12_slice_8_ok s12_slice_9_ok s12_slice_10_ok s12_slice_11_ok
    s12_slice_12_ok s12_slice_13_ok s12_slice_14_ok s12_slice_15_ok
    s12_merge_ok ob_cert_ok
    exch_cert_0_ok exch_cert_1_ok exch_cert_2_ok exch_cert_3_ok exch_cert_4_ok
    exch_cert_5_ok exch_cert_6_ok exch_cert_7_ok exch_cert_8_ok
    modes7_cert_0a_ok modes7_cert_0b_ok
    modes7_cert_1a_ok modes7_cert_1b_ok
    modes7_cert_2a_ok modes7_cert_2b_ok
    modes7_cert_3a_ok modes7_cert_3b_ok
    modes7_cert_4a_ok modes7_cert_4b_ok
    modes7_cert_5a_ok modes7_cert_5b_ok
    modes7_cert_6a_ok modes7_cert_6b_ok
    modes7_cert_7a_ok modes7_cert_7b_ok
    modes7_cert_8a_ok modes7_cert_8b_ok
    final_scale_cert_ok

theorem exists_eigen63_leDeepRefEnergy :
    ∃ (E₀ : ℝ) (φ₀ : Fin (2 ^ (2 * 58)) → ℂ),
      IsEigen63 E₀ φ₀ ∧ ∑ i, Complex.normSq (φ₀ i) = 1 ∧ E₀ ≤ deepRefEnergy := by
  obtain ⟨ψ, hproj, hnorm, henergy_le⟩ := exists_state63_leDeepRefEnergy
  obtain ⟨E₀, φ₀, hHφ, hPφ, hne, hnorm₀, hle⟩ :=
    exists_eigen_of_variational
      (thcHamiltonian_isHermitian dfthc)
      (electronSectorProjector_isHermitian (2 * 58) 63)
      (electronSectorProjector_mul_self (2 * 58) 63)
      (thcHamiltonian_comm_electronSectorProjector dfthc 63)
      hproj hnorm henergy_le
  exact ⟨E₀, φ₀, ⟨hHφ, hPφ, hne⟩, hnorm₀, hle⟩

theorem deep_exists_eigen63_le :
    ∀ T : ℝ, (∀ E' φ, IsEigen63 E' φ → T ≤ E' + 0.1) → T ≤ deepRefEnergy + 0.1 := by
  intro T hT
  obtain ⟨E₀, φ₀, heig, _, hle⟩ := exists_eigen63_leDeepRefEnergy
  linarith [hT E₀ φ₀ heig]

theorem deep63_exists_eigen63_le :
    ∀ T : ℝ, (∀ E' φ, TightGapBase.IsEigen63 E' φ → T ≤ E' + 0.1) →
      T ≤ (-130.1526 : ℝ) + 0.1 := by
  intro T hT
  simpa only [deepRefEnergy] using deep_exists_eigen63_le T hT

/-- Variational threshold bound `E₀(63e) ≤ -130.1526` Ha, definitionally matching
`P450RefVarBound (-130.1526)` and `DfthcRefEnergyBound (-130.1526)`. -/
theorem p450RefVarBound_tightGapDeep63 :
    ∀ (T : ℝ),
      (∀ (E' : ℝ) (φ : Fin (2 ^ (2 * 58)) → ℂ),
        (thcHamiltonian P450.dfthc *ᵥ φ = (E' : ℂ) • φ ∧
          electronSectorProjector (2 * 58) 63 *ᵥ φ = φ ∧ φ ≠ 0) →
        T ≤ E' + 0.1) →
      T ≤ (-130.1526 : ℝ) + 0.1 :=
  deep63_exists_eigen63_le

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63
