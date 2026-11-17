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
public import QuantumComputationSpecs.Algorithms.StoppingPower
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CyclotomicPhaseCheck
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SubCoin62UlpCertShard0
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SubCoin62UlpCertShard1
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SubCoin62UlpCertShard2
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SubCoin62UlpCertShard3
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage25W314Splice

/-!
# Photochemistry: Photoactivated Double Proton-Coupled Electron Transfer

Specification of `1 fs` of time evolution under the pre-Born–Oppenheimer molecular Hamiltonian of
Pocrnic et al. (arXiv:2602.11272v1) for its reaction 5, C₂₃H₂₀N₃O: `η = 234` particles (`47`
nuclei and `187` electrons) on a first-quantized real-space grid with `n_g = 8` qubits per
Cartesian coordinate, in a box of width `L = 44 Å` (paper Eqs. 2–10 and 23–25, Tables I and IV,
atomic units). The specification costs the time evolution, not an estimate of an observable such
as a proton-transfer yield. The photoexcited initial state is arbitrary; its preparation, which the
paper expects to be subdominant and leaves to future work (Sec. V), is not costed:

* `photochemistry_correctness`: the program acts on the system register with clean ancillas
  as `e^{-iHt}`, `t = 1 fs`, up to a global phase, within spectral-norm error `0.01`.
* `photochemistry_const_cost`: the program is over Clifford + `T` with measurements, and its
  spacetime volume (qubits × `T` count) is at most `photochemistryConstCost`. It has no `TOFF`
  gates, so each Toffoli is built from Clifford + `T` gates and the correctness proof covers that
  construction.

Two baselines, both for the paper's qubitization with generalized QSP at block-encoding error
`ε = 10^-2` on `6198` qubits (Table I), which `photochemistry_correctness` implies. Both charge `4`
`T` gates per Toffoli, the Toffoli of Jones (2013) from `4` `T` gates, an ancilla, a measurement
and a classically controlled `CZ`.
* Paper: `2.73 × 10^11` Toffolis (`1.09 × 10^12` `T` gates), spacetime `6.77 × 10^15` (Table I).
* QSP-rescaled: `2.01 × 10^11` Toffolis (`8.04 × 10^11` `T` gates), spacetime `4.98 × 10^15`,
  rescaling the `1.21 × 10^7` walk steps of Eq. C4 to `8.93 × 10^6` via the Jacobi–Anger degree
  bound of Pocrnic and Motlagh (2026, Theorem 2) at `ε_exp = ε / 12.95` (Table IV).

References:
* M. Pocrnic, I. Loaiza, J. M. Arrazola, N. Wiebe, D. Motlagh, *Efficient Simulation of
  Pre-Born-Oppenheimer Dynamics on a Quantum Computer*, https://arxiv.org/abs/2602.11272 (2026).
* M. Pocrnic, D. Motlagh, *Improved constant factors for qubitized Hamiltonian simulation*,
  https://arxiv.org/abs/2608.02734 (2026).
* C. Jones, *Low-overhead constructions for the fault-tolerant Toffoli gate*, Phys. Rev. A 87,
  022328 (2013).
* B. Şahinoğlu, R. D. Somma, *Hamiltonian simulation in the low-energy subspace*, npj Quantum Inf.
  7, 119 (2021), https://arxiv.org/abs/2006.02660.
* P. J. Mohr, D. B. Newell, B. N. Taylor, E. Tiesinga, *CODATA recommended values of the
  fundamental physical constants: 2022*, Rev. Mod. Phys. 97, 025002 (2025).
* M. Wang, W. J. Huang, F. G. Kondev, G. Audi, S. Naimi, *The AME 2020 atomic mass evaluation
  (II). Tables, graphs and references*, Chinese Phys. C 45, 030003 (2021).
-/

@[expose] public section
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs

section
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs

-- ============================================================================
-- Section 5. 32 Single-a Fused (`EE + NN`, Both Polarities) Kernel Certificates
-- ============================================================================

set_option autoImplicit false in
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
theorem tSub62OneA_all : ∀ a : Nat, a < 32 → checkOneABothSub62 a = true := by
  intro a ha
  rcases (by omega :
      a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨
      a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨
      a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 19 ∨ a = 20 ∨ a = 21 ∨ a = 22 ∨ a = 23 ∨
      a = 24 ∨ a = 25 ∨ a = 26 ∨ a = 27 ∨ a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tSub62OneA_0
  · exact tSub62OneA_1
  · exact tSub62OneA_2
  · exact tSub62OneA_3
  · exact tSub62OneA_4
  · exact tSub62OneA_5
  · exact tSub62OneA_6
  · exact tSub62OneA_7
  · exact tSub62OneA_8
  · exact tSub62OneA_9
  · exact tSub62OneA_10
  · exact tSub62OneA_11
  · exact tSub62OneA_12
  · exact tSub62OneA_13
  · exact tSub62OneA_14
  · exact tSub62OneA_15
  · exact tSub62OneA_16
  · exact tSub62OneA_17
  · exact tSub62OneA_18
  · exact tSub62OneA_19
  · exact tSub62OneA_20
  · exact tSub62OneA_21
  · exact tSub62OneA_22
  · exact tSub62OneA_23
  · exact tSub62OneA_24
  · exact tSub62OneA_25
  · exact tSub62OneA_26
  · exact tSub62OneA_27
  · exact tSub62OneA_28
  · exact tSub62OneA_29
  · exact tSub62OneA_30
  · exact tSub62OneA_31

set_option autoImplicit false in
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
noncomputable def shiftWState_subCoin_sub62 : ℝ :=
  GrayCodeKinNuc.shiftTier1WalkParametric
    midEESub62 Coul18K2Certs.midNNK2 Coul18K2Certs.midENK2

set_option autoImplicit false in
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
noncomputable def epsBlockSubCoinSub62 : ℝ :=
  Stage5StackCerts.epsBlockCap
    Stage5StackCerts.alphaTier1WalkFull
    (((1415061 : ℕ) : ℝ) / ((10 ^ 11 : ℕ) : ℝ))
    (((36075 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ))
    (((25760 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ))
    (((20126 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ))

set_option autoImplicit false in
set_option maxHeartbeats 16000000 in
-- rational bound and bundle elaboration
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
theorem hCap_subCoin_sub62 : 4231872 * epsBlockSubCoinSub62 ≤ 100 :=
  Stage5StackCerts.hCap_of_pot_cap (C := 1767928)
    (by
      unfold Stage5StackCerts.alphaTier1WalkFull ScreenFermatCore.alphaFermatCoin
      rw [ClusterPotSlice.gridSpacing_eq_rat]
      norm_num)
    (by norm_num)
    (by
      unfold Stage5StackCerts.alphaTier1WalkFull ScreenFermatCore.alphaFermatCoin
      rw [ClusterPotSlice.gridSpacing_eq_rat]
      norm_num)

set_option autoImplicit false in
set_option maxHeartbeats 16000000 in
-- rational bound and bundle elaboration
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
theorem hham_subCoin_sub62_tight :
    (WStateStage4Ulp.alphaWState * evolutionTime_frozen) *
      epsBlockSubCoinSub62 ≤ 7108616859 / 10 ^ 12 :=
  (Stage5StackCerts.hham_of_pot_cap (C := 1767927219 / 1000)
    (by
      unfold WStateStage4Ulp.alphaWState
        Stage5StackCerts.alphaTier1WalkFull ScreenFermatCore.alphaFermatCoin
      rw [ClusterPotSlice.gridSpacing_eq_rat]
      norm_num)
    (by norm_num)
    (by
      unfold evolutionTime_frozen
      rw [ClusterPotSlice.gridSpacing_eq_rat])).trans (by norm_num)

set_option autoImplicit false in
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
theorem epsBlockTier1WalkOf_eq_epsBlockSubCoinSub62 :
    GrayCodeKinNuc.epsBlockTier1WalkOf
      (((36075 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ))
      (((25760 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ))
      (((20126 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) = epsBlockSubCoinSub62 := by
  unfold GrayCodeKinNuc.epsBlockTier1WalkOf
    GenWeightsSelect.epsBlockGenOf
    epsBlockSubCoinSub62 Stage5StackCerts.epsBlockCap
  rfl

set_option autoImplicit false in
set_option exponentiation.threshold 256 in
open Real QuantumComputation.Specs PhotochemistrySolution in
open scoped BigOperators in
theorem blockApprox_wstate_subCoin_sub62 :
    SelectCompactAnc.BlockApproxSpecGen
      hamiltonian_frozen
      WStateStage4Ulp.alphaWState
      shiftWState_subCoin_sub62
      epsBlockSubCoinSub62
      aImplWState_subCoin_sub62 := by
  have ulp_ee : ∀ (pol : Bool) {d2 : ℕ},
      PopBernstein.Is3DBoxDistSq d2 → ¬(d2 % 8 = 7) →
      |((273022058496 : ℝ) / ((1 : ℝ) * 5714023029)) *
          expFnSub62Pol false pol d2 -
        ((-24823 : ℤ) : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √((max d2 1 : ℕ) : ℝ)| ≤ ((36075 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by
    intro pol d2 h3d hm7
    have h := sub62_pol_ulp false pol tSub62OneA_all h3d hm7
    dsimp only [sub62Mc, sub62DcMilli, sub62EpsMilli] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    push_cast at h ⊢
    exact h
  have ulp_nn : ∀ (pol : Bool) {d2 : ℕ},
      PopBernstein.Is3DBoxDistSq d2 → ¬(d2 % 8 = 7) →
      |((136511029248 : ℝ) / ((1 : ℝ) * 5714023029)) *
          expFnSub62Pol true pol d2 -
        ((-8958 : ℤ) : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √((max d2 8 : ℕ) : ℝ)| ≤ ((25760 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by
    intro pol d2 h3d hm7
    have h := sub62_pol_ulp true pol tSub62OneA_all h3d hm7
    dsimp only [sub62Mc, sub62DcMilli, sub62EpsMilli] at h
    simp only [↓reduceIte] at h
    push_cast at h ⊢
    exact h
  have ulp_en : ∀ {d2 : ℕ},
      PopBernstein.Is3DBoxDistSq d2 → ¬(d2 % 8 = 7) →
      |((136511029248 : ℝ) / ((1 : ℝ) * 5714023029)) *
          Coul18K2Certs.expFnK2
            Coul18K2Certs.wgtENQtr 1564629
            ZHi30.fnNN30
            WStateStage4Ulp.word512DualLegLo6 false d2 -
        ((-11431 : ℤ) : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √((max d2 1 : ℕ) : ℝ)| ≤ ((20126 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by
    intro d2 h3d hm7
    have h := Coul18K2Certs.channel_ulp_k2_fast
      .en Coul18K2Certs.tB2K2_all h3d hm7
    dsimp only [Coul18K2Certs.chMcK2,
      Coul18K2Certs.chWgtK2,
      Coul18K2Certs.chTotWK2,
      Coul18K2Certs.chFn30K2,
      Coul18K2Certs.chIsNNK2,
      Coul18K2Certs.chDcMilliK2,
      Coul18K2Certs.chEpsMilliK2] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    push_cast at h ⊢
    exact h
  obtain ⟨hEE, hNN, hEN⟩ := vSub62_unit
  obtain ⟨hEEErr, hNNErr, hENErr⟩ := vSub62_err_of_pol_ulp ulp_ee ulp_nn ulp_en
  rw [← epsBlockTier1WalkOf_eq_epsBlockSubCoinSub62]
  exact GrayCodeKinNuc.blockApproxSpecGen_tier1Walk_wke744_parametric
    WStateStage4Ulp.gEETier1Walk
    WStateStage4Ulp.gNNTier1Walk
    midEESub62
    Coul18K2Certs.midNNK2
    Coul18K2Certs.midENK2
    (by positivity) (by positivity) (by positivity)
    (by
      rw [epsBlockTier1WalkOf_eq_epsBlockSubCoinSub62]
      exact hCap_subCoin_sub62)
    vEESub62 vNNSub62 Coul18K2Certs.vENK2 hEE hNN hEN
    (fun x n1 e1 e2 hlt ↦ by
      unfold GrayCodeKinNuc.denomEETier1Walk
      exact hEEErr x n1 e1 e2 hlt)
    (fun x n1 n2 e1 hlt ↦ by
      unfold GrayCodeKinNuc.denomNNTier1WalkVal
      exact hNNErr x n1 n2 e1 hlt)
    (fun x n1 e1 ↦ by
      unfold GrayCodeKinNuc.denomENTier1Walk
      exact hENErr x n1 e1)

end QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs
end
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution
namespace WalkCostStack

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem hm_le80_stack : 62 ≤ 80 := by omega

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem hn_le24_stack : 23 ≤ 24 := by omega

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem hActStage1_stack {V : Type} {m : ℕ} {S : Wire m → Prop}
    (v' : V) (rT : QRegister RouterSelectWiringA.dLayout m)
    (hS : ∀ w : Wire RouterSelectWiringA.dLayout,
      Stage5StackCore.ActiveOuterCoinStackOf 23 314 62 w → S (rT w)) :
    SelectOracles.DynWires S
      (Stage1WRouter1260.stage1NucOptWRouter1256Chunk8W300AsymPkg.o1.fwdAmb v' rT) ∧
    SelectOracles.DynWires S
      (Stage1WRouter1260.stage1NucOptWRouter1256Chunk8W300AsymPkg.revAmb v' rT) :=
  Stage1WRouter1260.dynWires_stage1NucOptWRouter1256Chunk8W300AsymPkg_stack
    (by omega : 300 ≤ 314) (by omega : 39 ≤ 62) v' rT hS

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
noncomputable def coulPkg_stack :=
  Coulomb18K2.coulOWScrPkg13_certChk_m72_k123_tap29_1034

set_option autoImplicit false in
set_option Elab.async false in
set_option maxHeartbeats 2000000 in
-- rational bound and bundle elaboration
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
noncomputable def potPortBStage4InPlaceMux2_stack :
    DeferMux2Wp198Opt.Stage4ReflCoin24PotOraclePortBInPlace
      17 214 3060 3072 Stage4Coul18K2.potExpectK2DualLegK17 :=
  DeferMux2Wp193K2.wstateStage4InPlaceMux2Held_k2
    (Wp := 214) (WpU := 200) (kU := 14) (WpC := 201) (kC := 13)
    (by decide) (by decide) (by decide) (by decide)
    ShortBin7Pre56.shortBin7Pre56Pkg57
    (by decide : 57 ≤ 58)
    ShortBin7Pre56.shortBin7Pre56Pkg57_ctrlSafe
    (Dist18P26Dual.dist18HeldSplitPkg 14 (by decide) (by decide))
    (Dist18P26Dual.dist18HeldSplitPkg 13 (by decide) (by decide))
    MidOWTap29Xor240.midOWTap29XorPkg_240
    coulPkg_stack
    (by decide) (by decide) (by decide) (by decide)
    (by
      have := Coulomb18K2.coulOWScrPkg13_certChk_m72_k123_tap29_1034_kMid
      dsimp only [coulPkg_stack]
      omega)
    (by decide) (by decide)
    (by
      have := Coulomb18K2.coulOWScrPkg13_certChk_m72_k123_tap29_1034_kRest
      dsimp only [coulPkg_stack]
      omega)
    (by
      have := Coulomb18K2.coulOWScrPkg13_certChk_m72_k123_tap29_1034_kRest
      dsimp only [coulPkg_stack]
      omega)
    (by decide) (by decide)

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
noncomputable def wstateStage4InPlacePortBMux2_stack :
    Stage25PolyMCoin.Stage4ReflCoin23PotOraclePortBInPlace 18 214 3060 3072
      SubCoin62Stage4.potExpectK2Sub62 :=
  SubCoin62Stage4.wstateStg4Mux2_csa180_wp198_sbMid62
    potPortBStage4InPlaceMux2_stack rfl

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem htUsel_stack :
    1256 + ((Stage25W314Splice.stage2ElecAlwaysLoPkgW314At19156.tLoadE + 5038 + 908) +
      (3060 + 446)) + 4 * (62 + 1) ≤ 30116 := by
  have := Stage25W314Splice.stage2ElecAlwaysLoPkgW314At19156_tLoadE
  omega

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem htCsel_stack :
    1256 + ((Stage25W314Splice.stage2ElecAlwaysLoPkgW314At19156.tLoadE + 5038 + 908) +
      (3072 + 450)) + 4 * (62 + 1) ≤ 30132 := by
  have := Stage25W314Splice.stage2ElecAlwaysLoPkgW314At19156_tLoadE
  omega

set_option autoImplicit false in
set_option Elab.async false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
-- rational bound and bundle elaboration
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
noncomputable def bundleWState_stack :
    Stage5StackCore.OuterCoinSelectBundleStackAsym
      23 314 62 30116 30132
      (Nat.le_refl 23) hm_le80_stack SubCoin62Certs.aImplWState_subCoin_sub62 :=
  Stage25PolyMCoin.outerCoinSelectBundleStackPoly_ofStage25InPlace
    (by omega : 53 ≤ 62) hm_le80_stack
    hn_le24_stack (by omega : 39 + 23 ≤ 62)
    (by omega : 62 + 1 ≤ 314) (by omega : 314 ≤ 1500)
    Stage1WRouter1260.stage1NucOptWRouter1256Chunk8W300AsymPkg
    @hActStage1_stack
    Stage1CoinDecode.validOuterW11_decodeTier1W11Opt1424Coin.validCoin
    SubCoin62Stage4.rW18Sub41_k2
    wstateStage4InPlacePortBMux2_stack
    (Stage25W314Splice.stage25PolyPkgInPlace_alwaysLo_w314_wp100
      (by omega : 53 ≤ 62) hn_le24_stack (by omega : 39 + 23 ≤ 62)
      (by omega : 314 ≤ 314) (by omega : 314 ≤ 886)
      Stage25W314Splice.stage2ElecAlwaysLoPkgW314At19156
      (by omega : 214 ≤ 609) (by omega : 100 + 214 ≤ 314)
      Stage1WRouter1260.stage1NucOptWRouter1256Chunk8W300AsymPkg.o1
      SubCoin62Stage4.rW18Sub41_k2
      wstateStage4InPlacePortBMux2_stack)
    htUsel_stack htCsel_stack
    SubCoin62Certs.sum_coin0_bOuterZeroNErem_k2_sub62_eq

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem hm_init_le_stack : 4 * (62 + 1) ≤ 497 := by omega

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem hCost_stack_eq :
    (5616 + Stage5StackCore.outerCoinAncillasStack 23 314 62) *
      DepthArithWalk.bidirTotalTAsym 3326847 30116 30132 76 245 =
      605980010227389 := by decide

set_option autoImplicit false in
set_option Elab.async false in
set_option exponentiation.threshold 8192 in
open Operator QProg DynamicCircuit Matrix Circuit Qubit in
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt in
open PhotochemistrySolution in
theorem hCost_stack :
    (systemQubits_frozen + Stage5StackCore.outerCoinAncillasStack 23 314 62) *
      DepthArithWalk.bidirTotalTAsym 3326847 30116 30132 76 245 ≤
      605980010227389 := by
  rw [WStateTop.hSys5616_wstate, hCost_stack_eq]

export _root_.QuantumComputation.Specs.PhotochemistrySolution.NoEndRefl
  (outerCoinProgNoEndReflHalf_correctness)
export _root_.QuantumComputation.Specs.PhotochemistrySolution.NoEndRefl
  (outerCoinProgNoEndReflHalf_const_cost)

end WalkCostStack
end QuantumComputation.Specs.PhotochemistrySolution
end

set_option allowUnsafeReducibility true in
attribute [local irreducible]
  QuantumComputation.Specs.PhotochemistrySolution.Stage25W314Splice.stage2ElecAlwaysLoPkgW314At19156
  QuantumComputation.Specs.PhotochemistrySolution.WalkCostStack.coulPkg_stack
  QuantumComputation.Specs.PhotochemistrySolution.WalkCostStack.potPortBStage4InPlaceMux2_stack
  QuantumComputation.Specs.PhotochemistrySolution.WalkCostStack.wstateStage4InPlacePortBMux2_stack
  QuantumComputation.Specs.PhotochemistrySolution.WalkCostStack.bundleWState_stack
  QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs.aImplWState_subCoin_sub62
  QuantumComputation.Specs.PhotochemistrySolution.NoEndRefl.outerCoinProgNoEndReflHalf

namespace QuantumComputation.Specs

open Operator
open scoped Matrix Real

/-! ## C₂₃H₂₀N₃O Instance -/

namespace Photochemistry

/-- Qubits per Cartesian coordinate, `n_g` (paper Table IV). -/
abbrev gridBits : ℕ := 8

/-- The `η = 234` particles: the nuclei `0–46`, then the electrons (the paper's order, Fig. 8). -/
abbrev Particle := Fin 234

/-- Width `3 η n_g = 5616` of the system register. -/
abbrev systemQubits : ℕ := 3 * 234 * gridBits

/-- Box width `L = 44 Å` (paper Table IV) in Bohr radii, with `a₀ = 0.529177210544 Å`
(CODATA 2022). -/
noncomputable abbrev boxWidth : ℝ := 44 / 0.529177210544

/-- Grid spacing `Δ = L / (2^{n_g} - 1)` (paper Eq. 5). -/
noncomputable abbrev gridSpacing : ℝ := boxWidth / (2 ^ gridBits - 1)

/-- Evolution time `t = 1 fs` in units of `ħ / E_h = 2.4188843265864 × 10⁻¹⁷ s` (CODATA 2022). -/
noncomputable abbrev evolutionTime : ℝ := 100 / 2.4188843265864

/-- Atomic number of nucleus `i < 47`: nuclei `0–22` are C, `23–42` H, `43–45` N and `46` O. -/
def atomicNumber (i : Particle) : ℕ :=
  if i < 23 then 6 else if i < 43 then 1 else if i < 46 then 7 else 8

/-- Signed charge `(-1)^{σ_i} ζ_i`: `Z` for a nucleus, `-1` for an electron (paper Eqs. 2–3). -/
def charge (i : Particle) : ℤ := if i < 47 then atomicNumber i else -1

/-- AME2020 atomic mass, in daltons, of the most abundant isotope with atomic number
`Z = 1, 6, 7, 8`: ¹H, ¹²C, ¹⁴N, ¹⁶O. -/
noncomputable def atomicMass : ℕ → ℝ
  | 1 => 1.007825031898
  | 6 => 12
  | 7 => 14.00307400425
  | _ => 15.99491461926

/-- Mass `m_i` in units of `m_e`: `1` for an electron; for a nucleus, the atomic mass over
`m_e = 5.485799090441 × 10⁻⁴ u` (CODATA 2022) less `Z` electrons. Electron binding energies,
below `2 × 10⁻⁷` of the mass, are neglected. -/
noncomputable def mass (i : Particle) : ℝ :=
  if i < 47 then atomicMass (atomicNumber i) / 5.485799090441e-4 - atomicNumber i else 1

/-- Register of coordinate `w` of particle `i`: three consecutive `n_g`-qubit registers per
particle, in particle order. -/
def coordinateRegister (i : Particle) (w : Fin 3) : QRegister gridBits systemQubits :=
  .block (gridBits * (3 * i + w)) gridBits (by unfold systemQubits gridBits; omega)

/-- Two's-complement value in `[-2^{n_g-1}, 2^{n_g-1} - 1]` of an `n_g`-qubit basis index
(paper Eq. 4). -/
def twosComplement (k : Fin (2 ^ gridBits)) : ℤ := (k.val : ℤ).bmod (2 ^ gridBits)

/-- Grid position `q_w` of particle `i` in basis state `x`, at `r = q Δ` (paper Eq. 6). -/
def position (x : Fin (2 ^ systemQubits)) (i : Particle) (w : Fin 3) : ℤ :=
  twosComplement ((coordinateRegister i w).extractIndex x)

/-- Kinetic energy `T = (2π² / L²) Σ_i Σ_q (‖q‖² / m_i) QFT_i† |q⟩⟨q|_i QFT_i` (paper Eq. 10).
`QFT_i` is the QFT on each coordinate register of particle `i` and `‖q‖² = Σ_w q_w²`, so `T` is a
sum of terms on single coordinate registers. -/
noncomputable def kineticEnergy : Operator (2 ^ systemQubits) :=
  let F := QFT.qftMatrix gridBits
  ∑ i, ∑ w, ((2 * π ^ 2 / (boxWidth ^ 2 * mass i) : ℝ) : ℂ) •
    (coordinateRegister i w).embedMatrix
      (Fᴴ * Matrix.diagonal (fun k ↦ (twosComplement k ^ 2 : ℂ)) * F)

/-- Squared saturation distance in units of `Δ²`: `Γ̃² = 2^{n_Γ} = 8` (`n_Γ = 3`, paper Table IV and
Eq. E7) for a nucleus–nucleus pair, `1` otherwise. -/
def saturationSq (i j : Particle) : ℕ := if i < 47 ∧ j < 47 then 8 else 1

/-- Potential energy `Σ_{i ≠ j} c_i c_j / (2 max(r_ij, Γ̃_ij Δ))`, diagonal in the position basis,
with `r_ij = Δ ‖q_i - q_j‖` and `Γ̃_ij² = saturationSq i j`: Coulomb terms capped at `1 / Δ`
(paper Eqs. 8–9) and nucleus–nucleus terms at `1 / (Γ̃ Δ)` (Sec. III A 1, Eqs. 23–25). -/
noncomputable def potentialEnergy : Operator (2 ^ systemQubits) :=
  Matrix.diagonal fun x ↦ ∑ i, ∑ j, if i = j then 0 else
    (charge i * charge j / (2 * gridSpacing *
      √((max (∑ w, (position x i w - position x j w) ^ 2) (saturationSq i j) : ℤ) : ℝ)) : ℝ)

/-- The Hamiltonian `H = T + V` (paper Eq. 2, discretized as in Eqs. 8–10 and 23–25). -/
noncomputable def hamiltonian : Operator (2 ^ systemQubits) := kineticEnergy + potentialEnergy

end Photochemistry

open Photochemistry

/-! ## Candidate Program & Correctness / Cost Theorems -/

/-- By default we allow only a single variable. -/
inductive Photochemistry.Var where | v deriving DecidableEq, Inhabited

open Photochemistry (Var)
open Photochemistry.Var (v)

/-- Number of clean ancilla qubits `photochemistryProgram` uses. -/
def photochemistryAncillas : ℕ := 417

/-- Circuit for `e^{-iHt}`, `t = 1 fs`, on system wires `rSys` and clean ancilla wires `rAnc`. -/
noncomputable def photochemistryProgram {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister photochemistryAncillas n) : DynamicCircuit Var n :=
  PhotochemistrySolution.NoEndRefl.outerCoinProgNoEndReflHalf
    PhotochemistrySolution.CompactCauchy.hd_3326847_le
    PhotochemistrySolution.CompactCauchy.cleanWalkCertHalf_subCoin_3326847
    PhotochemistrySolution.SubCoin62Certs.blockApprox_wstate_subCoin_sub62
    (PhotochemistrySolution.TopHadBridge.hs_tier1Walk_of_alpha_le
      PhotochemistrySolution.WStateStage4Ulp.alphaWState_le)
    PhotochemistrySolution.WalkCostStack.bundleWState_stack v rSys rAnc

/-- `photochemistryProgram` realizes a unitary that maps every `|Ψ₀⟩ ⊗ |0⟩` to within
Euclidean distance `ε = 0.01` of `e^{-iHt} |Ψ₀⟩ ⊗ |0⟩`, `t = 1 fs`, up to a global phase. This
implies the paper's requirement, a block encoding of `e^{-iHt}` within `ε = 10^-2` (Table IV).
The bound holds on every input state (`P = 1`), as does the paper's operator-norm guarantee
(Theorems 1–2); it is not restricted to antisymmetric states or to a low-energy subspace, on which
product-formula error can depend on an effective low-energy norm instead of `‖H‖` (Şahinoğlu and
Somma 2021). With no catalyst, phase-gradient states are prepared within the run, and a single
unitary `W` excludes randomized compilers such as qDRIFT. -/
theorem photochemistry_correctness {n : ℕ}
    (rSys : QRegister systemQubits n) (rAnc : QRegister photochemistryAncillas n)
    (hdisj : rSys.DisjointWires rAnc) :
    ∃ W, ApproximatesTimeEvolution hamiltonian evolutionTime 0.01 1 W ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W
        (photochemistryProgram rSys rAnc).compile := by
  set_option exponentiation.threshold 8192 in
  have : Fintype Var := ⟨{v}, fun x ↦ by
    cases x
    simp⟩
  exact
    PhotochemistrySolution.WalkCostStack.outerCoinProgNoEndReflHalf_correctness
      PhotochemistrySolution.CompactCauchy.hd_3326847_le
      PhotochemistrySolution.CompactCauchy.cleanWalkCertHalf_subCoin_3326847
      PhotochemistrySolution.SubCoin62Certs.blockApprox_wstate_subCoin_sub62
      (PhotochemistrySolution.TopHadBridge.hs_tier1Walk_of_alpha_le
        PhotochemistrySolution.WStateStage4Ulp.alphaWState_le)
      le_rfl
      PhotochemistrySolution.SubCoin62Certs.hham_subCoin_sub62_tight
      PhotochemistrySolution.CompactCauchy.tot_err_subCoin_3326847
      PhotochemistrySolution.WalkCostStack.bundleWState_stack v rSys rAnc hdisj

/-- Claimed spacetime volume of `1 fs` of evolution. -/
def photochemistryConstCost : ℕ := 605980010227389

/-- Over Clifford + `T` with measurements, the spacetime volume (qubits times `T` count) of `1 fs`
of evolution is at most `photochemistryConstCost`. `TOFF` gates are excluded, so each Toffoli is
costed by the Clifford + `T` construction the program uses, such as `4` `T` gates with an ancilla
and a measurement; measurements cost `0` and a `qIf` costs its worse branch. -/
theorem photochemistry_const_cost {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister photochemistryAncillas n) :
    (photochemistryProgram rSys rAnc).count PrimitiveGate.TOFF = 0 ∧
      (systemQubits + photochemistryAncillas) *
          (photochemistryProgram rSys rAnc).count PrimitiveGate.T ≤
        photochemistryConstCost := by
  exact
    PhotochemistrySolution.WalkCostStack.outerCoinProgNoEndReflHalf_const_cost
      PhotochemistrySolution.CompactCauchy.hd_3326847_le
      PhotochemistrySolution.WalkCostStack.hm_init_le_stack
      PhotochemistrySolution.CompactCauchy.cleanWalkCertHalf_subCoin_3326847
      PhotochemistrySolution.SubCoin62Certs.blockApprox_wstate_subCoin_sub62
      (PhotochemistrySolution.TopHadBridge.hs_tier1Walk_of_alpha_le
        PhotochemistrySolution.WStateStage4Ulp.alphaWState_le)
      PhotochemistrySolution.WalkCostStack.bundleWState_stack
      PhotochemistrySolution.WalkCostStack.hCost_stack v rSys rAnc

end QuantumComputation.Specs
