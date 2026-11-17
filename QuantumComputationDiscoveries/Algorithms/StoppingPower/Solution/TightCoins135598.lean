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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.TightCoinAnfSpine
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sTier6Cert
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspRoundedTiersA
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspRoundedTiersB
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency false

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace TierTightSpine

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
  ModWrapCoarse8PureMomentum.modWrapNeZeroPow2
  PosSlots24BranchConcrete.instNeZeroTwoPow

local instance (priority := 1000000) instNeZeroTwoPowTightCoins (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFastTightCoins (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFastTightCoins (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

section ParAuxCoins79To101
open QuantumComputation
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
open FullSysPrepare6Slot (fullSysCoinIdx)
open MeasureBranchHadamardSem (ket sqrtHalf)
open PosPostPrep80MergedVep (ket_eq_single_local)
open SegmentAndTopClosure (rCleanSubW cleanZeroEmbedIdx compressCleanUnitary)
open ZeroAncillaUSP hiding ket
open ZeroSubwireCoinPrep80
open Coin3PerHorizon5799
open CoinPrepSub85AndAlphaOpt
open GqspCleanCoinAndGuardBridge

theorem tBound_a135598_c79_za :
    (pCoinPrepZeroAncParityGen coinU0_15 mux2_4 mux3_4).tBound ≤ 79 := by
  rw [tBound_pCoinPrepZeroAncParityGen_eq]
  decide
/-- Zero-ancilla 3-qubit coin unitary `uCoin3WIdealA135598_c79_za` (`79 T`, `≤ 182860 nHa` at `α
  = 135,598`). -/
noncomputable def uCoin3WIdealA135598_c79_za : Unitary (2 ^ 3) :=
  uCoin3ZeroAncParityGen coinU0_15 mux2_4 mux3_4
theorem uCoin3WIdealA135598_c79_za_sixSlot_err :
    ∑ k : Fin 6,
      |(135598 : ℝ) * ‖uCoin3WIdealA135598_c79_za.1 (fullSysCoinIdx k) 0‖ ^ 2 - wIdealRat k| ≤
      ((( 182860 : ℕ) : ℝ) / 1000000000) := by
  have hz0 : coin3Col0AmpGen coinU0_15 mux2_4 mux3_4 5 = ((sqrtHalf : ℂ) ^ 82) * (⟨-387892903936,
    -888440094720, 120569987072, -101822496768⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_4_1_eval, mux3_4_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk0 :=
    amp_weight_err_le _ 82 ⟨-387892903936, -888440094720, 120569987072,
    -101822496768⟩ 135598 1 3441613 100 61413 1000000000 hz0 (by
    decide) (by decide) (by decide) (by decide)
  have hz1 : coin3Col0AmpGen coinU0_15 mux2_4 mux3_4 4 = ((sqrtHalf : ℂ) ^ 82) * (⟨135489126400,
    -340540260352, 174330478592, -34168373248⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_4_0_eval, mux3_4_00_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk1 :=
    amp_weight_err_le _ 82 ⟨135489126400, -340540260352, 174330478592,
    -34168373248⟩ 135598 1 51871 125 38458 1000000000 hz1 (by
    decide) (by decide) (by decide) (by decide)
  have hz2 : coin3Col0AmpGen coinU0_15 mux2_4 mux3_4 0 = ((sqrtHalf : ℂ) ^ 82) * (⟨-800643874816,
    226608283648, 194991620096, 666579238912⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_4_0_eval, mux3_4_00_eval]
    simp only [toMatrix_entry00, mul_sqrtHalf_zw]
    congr 1
  have hk2 :=
    amp_weight_err_le _ 82 ⟨-800643874816, 226608283648, 194991620096,
    666579238912⟩ 135598 1 231140195423637 4294967296 33086 1000000000 hz2 (by
    decide) (by decide) (by decide) (by decide)
  have hz3 : coin3Col0AmpGen coinU0_15 mux2_4 mux3_4 6 = ((sqrtHalf : ℂ) ^ 82) * (⟨232399568896,
    294962855936, 496978362368, 58600194048⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_4_0_eval, mux3_4_01_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk3 :=
    amp_weight_err_le _ 82 ⟨232399568896, 294962855936, 496978362368,
    58600194048⟩ 135598 1 75557863725914323419136 3754873682634714703 3951 1000000000 hz3 (by
    decide) (by decide) (by decide) (by decide)
  have hz4 : coin3Col0AmpGen coinU0_15 mux2_4 mux3_4 1 = ((sqrtHalf : ℂ) ^ 82) * (⟨635767881728,
    345029214208, 259018719232, 293597609984⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_4_1_eval, mux3_4_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk4 :=
    amp_weight_err_le _ 82 ⟨635767881728, 345029214208, 259018719232,
    293597609984⟩ 135598 1 115221930763381 4294967296 8278 1000000000 hz4 (by
    decide) (by decide) (by decide) (by decide)
  have hz5 : coin3Col0AmpGen coinU0_15 mux2_4 mux3_4 7 = ((sqrtHalf : ℂ) ^ 82) * (⟨-308065861632,
    17192976384, 283700101120, -418447360000⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_4_1_eval, mux3_4_11_eval]
    simp only [toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk5 :=
    amp_weight_err_le _ 82 ⟨-308065861632, 17192976384, 283700101120,
    -418447360000⟩ 135598 1 0 1 37674 1000000000 hz5 (by decide) (by decide) (by decide) (by decide)
  have hcol := uCoin3ZeroAncParityGen_col0_eq coinU0_15 mux2_4 mux3_4 mux3_4_affine
  dsimp only [uCoin3WIdealA135598_c79_za]
  exact gqsp_sixSlot_err_of_col0_eq_gen ha135598_div1 (hcol 4) (hcol 5) (hcol 0) (hcol 6) (hcol 1)
    (hcol 7) wIdealRat_eq_div hk0 hk1 hk2 hk3 hk4 hk5 (by decide)
/-- Certified `79 T` zero-ancilla `Coin3CleanProgSpecOfWeights wIdealRat` at `α = 135,598` (`≤
  182860 nHa`). -/
noncomputable def coinCleanWIdealA135598_c79_za : Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ)
    79 ((182860 : ℝ) / 1000000000) :=
  mkCoin3CleanProgSpecOfZeroAncParityGenWeights coinU0_15 mux2_4 mux3_4 mux3_4_affine
    tBound_a135598_c79_za (le_trans uCoin3WIdealA135598_c79_za_sixSlot_err (by norm_num))

theorem tBound_a135598_c84 :
    (pCoinPrepParityGen coinU0_15 mux2_5 mux3_8).tBound ≤ 84 := by
  rw [tBound_pCoinPrepParityGen_eq]
  decide
/-- Synthesized 3-qubit coin unitary `uCoin3WIdealA135598_c84` (`84 T`, `≤ 84573 nHa` at `α =
  135,598`). -/
noncomputable def uCoin3WIdealA135598_c84 : Unitary (2 ^ 3) :=
  uCoin3ParityGen coinU0_15 mux2_5 mux3_8
theorem uCoin3WIdealA135598_c84_sixSlot_err :
    ∑ k : Fin 6,
      |(135598 : ℝ) * ‖uCoin3WIdealA135598_c84.1 (fullSysCoinIdx k) 0‖ ^ 2 - wIdealRat k| ≤
      ((( 84573 : ℕ) : ℝ) / 1000000000) := by
  have hz0 : coin3Col0AmpGen coinU0_15 mux2_5 mux3_8 5 = ((sqrtHalf : ℂ) ^ 83) * (⟨259033923584,
    -169996189696, -1028804050944, -483802480640⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_5_1_eval, mux3_8_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk0 :=
    amp_weight_err_le _ 83 ⟨259033923584, -169996189696, -1028804050944,
    -483802480640⟩ 135598 1 3441613 100 33361 1000000000 hz0 (by
    decide) (by decide) (by decide) (by decide)
  have hz1 : coin3Col0AmpGen coinU0_15 mux2_5 mux3_8 4 = ((sqrtHalf : ℂ) ^ 83) * (⟨110842871808,
    13634633728, -372166885376, 359007256576⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_5_0_eval, mux3_8_00_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk1 :=
    amp_weight_err_le _ 83 ⟨110842871808, 13634633728, -372166885376,
    359007256576⟩ 135598 1 51871 125 1310 1000000000 hz1 (by
    decide) (by decide) (by decide) (by decide)
  have hz2 : coin3Col0AmpGen coinU0_15 mux2_5 mux3_8 0 = ((sqrtHalf : ℂ) ^ 83) * (⟨-765130178560,
    -298714136576, -205612122112, 1297857118208⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_5_0_eval, mux3_8_00_eval]
    simp only [toMatrix_entry00, mul_sqrtHalf_zw]
    congr 1
  have hk2 :=
    amp_weight_err_le _ 83 ⟨-765130178560, -298714136576, -205612122112,
    1297857118208⟩ 135598 1 231140195423637 4294967296 6682 1000000000 hz2 (by
    decide) (by decide) (by decide) (by decide)
  have hz3 : coin3Col0AmpGen coinU0_15 mux2_5 mux3_8 6 = ((sqrtHalf : ℂ) ^ 83) * (⟨-694618685440,
    -124146155520, 194636677120, 469856419840⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_5_0_eval, mux3_8_01_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk3 :=
    amp_weight_err_le _ 83 ⟨-694618685440, -124146155520, 194636677120,
    469856419840⟩ 135598 1 75557863725914323419136 3754873682634714703 6889 1000000000 hz3 (by
    decide) (by decide) (by decide) (by decide)
  have hz4 : coin3Col0AmpGen coinU0_15 mux2_5 mux3_8 1 = ((sqrtHalf : ℂ) ^ 83) * (⟨-990039244800,
    -715302895616, 613818564608, -159206342656⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_5_1_eval, mux3_8_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk4 :=
    amp_weight_err_le _ 83 ⟨-990039244800, -715302895616, 613818564608,
    -159206342656⟩ 135598 1 115221930763381 4294967296 36330 1000000000 hz4 (by
    decide) (by decide) (by decide) (by decide)
  have hz5 : coin3Col0AmpGen coinU0_15 mux2_5 mux3_8 7 = ((sqrtHalf : ℂ) ^ 83) * (⟨941361201152,
    -337804001280, -463634169856, 993481719808⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_5_1_eval, mux3_8_11_eval]
    simp only [toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk5 :=
    amp_weight_err_le _ 83 ⟨941361201152, -337804001280, -463634169856,
    993481719808⟩ 135598 1 0 1 1 1000000000 hz5 (by decide) (by decide) (by decide) (by decide)
  have hcol := uCoin3ParityGen_col0_eq coinU0_15 mux2_5 mux3_8
  dsimp only [uCoin3WIdealA135598_c84]
  exact gqsp_sixSlot_err_of_col0_eq_gen ha135598_div1 (hcol 4) (hcol 5) (hcol 0) (hcol 6) (hcol 1)
    (hcol 7) wIdealRat_eq_div hk0 hk1 hk2 hk3 hk4 hk5 (by decide)
/-- Certified `84 T` `Coin3CleanProgSpecOfWeights wIdealRat` at `α = 135,598` (`≤ 84573 nHa`). -/
noncomputable def coinCleanWIdealA135598_c84 : Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ) 84
    ((84573 : ℝ) / 1000000000) :=
  mkCoin3CleanProgSpecOfParityGenWeights coinU0_15 mux2_5 mux3_8 tBound_a135598_c84 (le_trans
    uCoin3WIdealA135598_c84_sixSlot_err (by norm_num))

theorem tBound_a135598_c88 :
    (pCoinPrepParityGen coinU0_15 mux2_6 mux3_11).tBound ≤ 88 := by
  rw [tBound_pCoinPrepParityGen_eq]
  decide
/-- Synthesized 3-qubit coin unitary `uCoin3WIdealA135598_c88` (`88 T`, `≤ 41830 nHa` at `α =
  135,598`). -/
noncomputable def uCoin3WIdealA135598_c88 : Unitary (2 ^ 3) :=
  uCoin3ParityGen coinU0_15 mux2_6 mux3_11
theorem uCoin3WIdealA135598_c88_sixSlot_err :
    ∑ k : Fin 6,
      |(135598 : ℝ) * ‖uCoin3WIdealA135598_c88.1 (fullSysCoinIdx k) 0‖ ^ 2 - wIdealRat k| ≤
      ((( 41830 : ℕ) : ℝ) / 1000000000) := by
  have hz0 : coin3Col0AmpGen coinU0_15 mux2_6 mux3_11 5 = ((sqrtHalf : ℂ) ^ 87) * (⟨3130240532480,
    1836637487104, 3048304803840, -817625038848⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_6_1_eval, mux3_11_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk0 :=
    amp_weight_err_le _ 87 ⟨3130240532480, 1836637487104, 3048304803840,
    -817625038848⟩ 135598 1 3441613 100 2330 1000000000 hz0 (by
    decide) (by decide) (by decide) (by decide)
  have hz1 : coin3Col0AmpGen coinU0_15 mux2_6 mux3_11 4 = ((sqrtHalf : ℂ) ^ 87) * (⟨-695965057024,
    243693256704, -485461327872, 202498899968⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_6_0_eval, mux3_11_00_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk1 :=
    amp_weight_err_le _ 87 ⟨-695965057024, 243693256704, -485461327872,
    202498899968⟩ 135598 1 51871 125 1587 1000000000 hz1 (by
    decide) (by decide) (by decide) (by decide)
  have hz2 : coin3Col0AmpGen coinU0_15 mux2_6 mux3_11 0 = ((sqrtHalf : ℂ) ^ 87) * (⟨-3570168496128,
    363396595712, 2029969735680, 3843182034944⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_6_0_eval, mux3_11_00_eval]
    simp only [toMatrix_entry00, mul_sqrtHalf_zw]
    congr 1
  have hk2 :=
    amp_weight_err_le _ 87 ⟨-3570168496128, 363396595712, 2029969735680,
    3843182034944⟩ 135598 1 231140195423637 4294967296 29219 1000000000 hz2 (by
    decide) (by decide) (by decide) (by decide)
  have hz3 : coin3Col0AmpGen coinU0_15 mux2_6 mux3_11 6 = ((sqrtHalf : ℂ) ^ 87) * (⟨-1743171616768,
    -2712856952832, -987186069504, 649261481984⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_6_0_eval, mux3_11_01_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk3 :=
    amp_weight_err_le _ 87 ⟨-1743171616768, -2712856952832, -987186069504,
    649261481984⟩ 135598 1 75557863725914323419136 3754873682634714703 183 1000000000 hz3 (by
    decide) (by decide) (by decide) (by decide)
  have hz4 : coin3Col0AmpGen coinU0_15 mux2_6 mux3_11 1 = ((sqrtHalf : ℂ) ^ 87) * (⟨568806342656,
    1284170055680, -5780539441152, -495273902080⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_6_1_eval, mux3_11_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk4 :=
    amp_weight_err_le _ 87 ⟨568806342656, 1284170055680, -5780539441152,
    -495273902080⟩ 135598 1 115221930763381 4294967296 8510 1000000000 hz4 (by
    decide) (by decide) (by decide) (by decide)
  have hz5 : coin3Col0AmpGen coinU0_15 mux2_6 mux3_11 7 = ((sqrtHalf : ℂ) ^ 87) * (⟨1278694391808,
    1702663028736, -3686623346688, 3511009935360⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_6_1_eval, mux3_11_11_eval]
    simp only [toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk5 :=
    amp_weight_err_le _ 87 ⟨1278694391808, 1702663028736, -3686623346688,
    3511009935360⟩ 135598 1 0 1 1 1000000000 hz5 (by decide) (by decide) (by decide) (by decide)
  have hcol := uCoin3ParityGen_col0_eq coinU0_15 mux2_6 mux3_11
  dsimp only [uCoin3WIdealA135598_c88]
  exact gqsp_sixSlot_err_of_col0_eq_gen ha135598_div1 (hcol 4) (hcol 5) (hcol 0) (hcol 6) (hcol 1)
    (hcol 7) wIdealRat_eq_div hk0 hk1 hk2 hk3 hk4 hk5 (by decide)
/-- Certified `88 T` `Coin3CleanProgSpecOfWeights wIdealRat` at `α = 135,598` (`≤ 41830 nHa`). -/
noncomputable def coinCleanWIdealA135598_c88 : Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ) 88
    ((41830 : ℝ) / 1000000000) :=
  mkCoin3CleanProgSpecOfParityGenWeights coinU0_15 mux2_6 mux3_11 tBound_a135598_c88 (le_trans
    uCoin3WIdealA135598_c88_sixSlot_err (by norm_num))

theorem tBound_a135598_c90 :
    (pCoinPrepParityGen coinU0_15 mux2_8 mux3_13).tBound ≤ 90 := by
  rw [tBound_pCoinPrepParityGen_eq]
  decide
/-- Synthesized 3-qubit coin unitary `uCoin3WIdealA135598_c90` (`90 T`, `≤ 19747 nHa` at `α =
  135,598`). -/
noncomputable def uCoin3WIdealA135598_c90 : Unitary (2 ^ 3) :=
  uCoin3ParityGen coinU0_15 mux2_8 mux3_13
theorem uCoin3WIdealA135598_c90_sixSlot_err :
    ∑ k : Fin 6,
      |(135598 : ℝ) * ‖uCoin3WIdealA135598_c90.1 (fullSysCoinIdx k) 0‖ ^ 2 - wIdealRat k| ≤
      ((( 19747 : ℕ) : ℝ) / 1000000000) := by
  have hz0 : coin3Col0AmpGen coinU0_15 mux2_8 mux3_13 5 = ((sqrtHalf : ℂ) ^ 89) * (⟨1951156666368,
    -108596822016, -4849131323392, -7538324013056⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_8_1_eval, mux3_13_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk0 :=
    amp_weight_err_le _ 89 ⟨1951156666368, -108596822016, -4849131323392,
    -7538324013056⟩ 135598 1 3441613 100 7354 1000000000 hz0 (by
    decide) (by decide) (by decide) (by decide)
  have hz1 : coin3Col0AmpGen coinU0_15 mux2_8 mux3_13 4 = ((sqrtHalf : ℂ) ^ 89) * (⟨-1498884866048,
    2130645614592, -1980881698816, 1677002276864⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_8_0_eval, mux3_13_00_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk1 :=
    amp_weight_err_le _ 89 ⟨-1498884866048, 2130645614592, -1980881698816,
    1677002276864⟩ 135598 1 51871 125 1393 1000000000 hz1 (by
    decide) (by decide) (by decide) (by decide)
  have hz2 : coin3Col0AmpGen coinU0_15 mux2_8 mux3_13 0 = ((sqrtHalf : ℂ) ^ 89) * (⟨-2292120027136,
    8295685292032, 4842290413568, 6941461970944⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_8_0_eval, mux3_13_00_eval]
    simp only [toMatrix_entry00, mul_sqrtHalf_zw]
    congr 1
  have hk2 :=
    amp_weight_err_le _ 89 ⟨-2292120027136, 8295685292032, 4842290413568,
    6941461970944⟩ 135598 1 231140195423637 4294967296 4089 1000000000 hz2 (by
    decide) (by decide) (by decide) (by decide)
  have hz3 : coin3Col0AmpGen coinU0_15 mux2_8 mux3_13 6 = ((sqrtHalf : ℂ) ^ 89) * (⟨2235752775680,
    5611456561152, 3235674849280, 699255488512⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_8_0_eval, mux3_13_01_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk3 :=
    amp_weight_err_le _ 89 ⟨2235752775680, 5611456561152, 3235674849280,
    699255488512⟩ 135598 1 75557863725914323419136 3754873682634714703 2316 1000000000 hz3 (by
    decide) (by decide) (by decide) (by decide)
  have hz4 : coin3Col0AmpGen coinU0_15 mux2_8 mux3_13 1 = ((sqrtHalf : ℂ) ^ 89) * (⟨-1337035063296,
    -8309568438272, -780358647808, 4733366435840⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_8_1_eval, mux3_13_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk4 :=
    amp_weight_err_le _ 89 ⟨-1337035063296, -8309568438272, -780358647808,
    4733366435840⟩ 135598 1 115221930763381 4294967296 4594 1000000000 hz4 (by
    decide) (by decide) (by decide) (by decide)
  have hz5 : coin3Col0AmpGen coinU0_15 mux2_8 mux3_13 7 = ((sqrtHalf : ℂ) ^ 89) * (⟨-2662556762112,
    -4267979046912, 8698390904832, -8033402880000⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_8_1_eval, mux3_13_11_eval]
    simp only [toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk5 :=
    amp_weight_err_le _ 89 ⟨-2662556762112, -4267979046912, 8698390904832,
    -8033402880000⟩ 135598 1 0 1 1 1000000000 hz5 (by decide) (by decide) (by decide) (by decide)
  have hcol := uCoin3ParityGen_col0_eq coinU0_15 mux2_8 mux3_13
  dsimp only [uCoin3WIdealA135598_c90]
  exact gqsp_sixSlot_err_of_col0_eq_gen ha135598_div1 (hcol 4) (hcol 5) (hcol 0) (hcol 6) (hcol 1)
    (hcol 7) wIdealRat_eq_div hk0 hk1 hk2 hk3 hk4 hk5 (by decide)
/-- Certified `90 T` `Coin3CleanProgSpecOfWeights wIdealRat` at `α = 135,598` (`≤ 19747 nHa`). -/
noncomputable def coinCleanWIdealA135598_c90 : Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ) 90
    ((19747 : ℝ) / 1000000000) :=
  mkCoin3CleanProgSpecOfParityGenWeights coinU0_15 mux2_8 mux3_13 tBound_a135598_c90 (le_trans
    uCoin3WIdealA135598_c90_sixSlot_err (by norm_num))

theorem tBound_a135598_c96_ultra :
    (pCoinPrepParityGen coinU0_15 mux2_11 mux3_17).tBound ≤ 96 := by
  rw [tBound_pCoinPrepParityGen_eq]
  decide
/-- Synthesized 3-qubit coin unitary `uCoin3WIdealA135598_c96_ultra` (`96 T`, `≤ 3817 nHa` at `α
  = 135,598`). -/
noncomputable def uCoin3WIdealA135598_c96_ultra : Unitary (2 ^ 3) :=
  uCoin3ParityGen coinU0_15 mux2_11 mux3_17
theorem uCoin3WIdealA135598_c96_ultra_sixSlot_err :
    ∑ k : Fin 6,
      |(135598 : ℝ) * ‖uCoin3WIdealA135598_c96_ultra.1 (fullSysCoinIdx k) 0‖ ^ 2 - wIdealRat k| ≤
      ((( 3817 : ℕ) : ℝ) / 1000000000) := by
  have hz0 : coin3Col0AmpGen coinU0_15 mux2_11 mux3_17 5 = ((sqrtHalf : ℂ) ^ 95) *
    (⟨-34502990626816, -23895545479168, -44553348317184, -53613321781248⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_11_1_eval, mux3_17_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk0 :=
    amp_weight_err_le _ 95 ⟨-34502990626816, -23895545479168, -44553348317184,
    -53613321781248⟩ 135598 1 3441613 100 27 1000000000 hz0 (by
    decide) (by decide) (by decide) (by decide)
  have hz1 : coin3Col0AmpGen coinU0_15 mux2_11 mux3_17 4 = ((sqrtHalf : ℂ) ^ 95) * (⟨-9566997708800,
    1506686271488, 22997511438336, -22634980966400⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_11_0_eval, mux3_17_00_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk1 :=
    amp_weight_err_le _ 95 ⟨-9566997708800, 1506686271488, 22997511438336,
    -22634980966400⟩ 135598 1 51871 125 872 1000000000 hz1 (by
    decide) (by decide) (by decide) (by decide)
  have hz2 : coin3Col0AmpGen coinU0_15 mux2_11 mux3_17 0 = ((sqrtHalf : ℂ) ^ 95) *
    (⟨-31754320609280, 44586256826368, 44894957600768, 59023126691840⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_11_0_eval, mux3_17_00_eval]
    simp only [toMatrix_entry00, mul_sqrtHalf_zw]
    congr 1
  have hk2 :=
    amp_weight_err_le _ 95 ⟨-31754320609280, 44586256826368, 44894957600768,
    59023126691840⟩ 135598 1 231140195423637 4294967296 1322 1000000000 hz2 (by
    decide) (by decide) (by decide) (by decide)
  have hz3 : coin3Col0AmpGen coinU0_15 mux2_11 mux3_17 6 = ((sqrtHalf : ℂ) ^ 95) * (⟨33225950887936,
    44905695019008, -24967315980288, -16328031207424⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_11_0_eval, mux3_17_01_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk3 :=
    amp_weight_err_le _ 95 ⟨33225950887936, 44905695019008, -24967315980288,
    -16328031207424⟩ 135598 1 75557863725914323419136 3754873682634714703 528 1000000000 hz3 (by
    decide) (by decide) (by decide) (by decide)
  have hz4 : coin3Col0AmpGen coinU0_15 mux2_11 mux3_17 1 = ((sqrtHalf : ℂ) ^ 95) * (⟨18581672689664,
    8403321618432, 86096260104192, -15428420108288⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_11_1_eval, mux3_17_10_eval]
    simp only [toMatrix_entry00, toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk4 :=
    amp_weight_err_le _ 95 ⟨18581672689664, 8403321618432, 86096260104192,
    -15428420108288⟩ 135598 1 115221930763381 4294967296 1067 1000000000 hz4 (by
    decide) (by decide) (by decide) (by decide)
  have hz5 : coin3Col0AmpGen coinU0_15 mux2_11 mux3_17 7 = ((sqrtHalf : ℂ) ^ 95) * (⟨-9670336970752,
    -30418904547328, 52689165615104, -44094827003904⟩ : Zw).toComplex := by
    dsimp only [coin3Col0AmpGen]
    rw [wordMatrix2_eq_of_eval _ _ coinU0_15_eval, mux2_11_1_eval, mux3_17_11_eval]
    simp only [toMatrix_entry10, mul_sqrtHalf_zw]
    congr 1
  have hk5 :=
    amp_weight_err_le _ 95 ⟨-9670336970752, -30418904547328, 52689165615104,
    -44094827003904⟩ 135598 1 0 1 1 1000000000 hz5 (by decide) (by decide) (by decide) (by decide)
  have hcol := uCoin3ParityGen_col0_eq coinU0_15 mux2_11 mux3_17
  dsimp only [uCoin3WIdealA135598_c96_ultra]
  exact gqsp_sixSlot_err_of_col0_eq_gen ha135598_div1 (hcol 4) (hcol 5) (hcol 0) (hcol 6) (hcol 1)
    (hcol 7) wIdealRat_eq_div hk0 hk1 hk2 hk3 hk4 hk5 (by decide)
/-- Certified `96 T` `Coin3CleanProgSpecOfWeights wIdealRat` at `α = 135,598` (`≤ 3817 nHa`). -/
noncomputable def coinCleanWIdealA135598_c96_ultra : Coin3CleanProgSpecOfWeights wIdealRat (135598 :
    ℝ) 96 ((3817 : ℝ) / 1000000000) :=
  mkCoin3CleanProgSpecOfParityGenWeights coinU0_15 mux2_11 mux3_17 tBound_a135598_c96_ultra
    (le_trans uCoin3WIdealA135598_c96_ultra_sixSlot_err (by norm_num))
end ParAuxCoins79To101

section Part2_TierCompactMasterSpine

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open PrimitiveGate (T)
open SpecsAux SpecsAux.SpecMirror
open GeneralBetaAndAlphaTopEndpoint (GeneralBetaSegmentCert)
open GidneySignalRotPart1 (gidneyRotToffEquiv)
open ZeroSubwireCoinPrep80 (wIdealRat)
open Slot3Norm1s36_161w (Norm1sTier)
open GqspCatPrepSub600Nano (catPrepErrUltra1q)
open GqspSlot3UltraBkAnd8TierCert (IsCertifiedNorm1sTier6 s3EpsUltraBkNano)
open GqspCleanCoinAndGuardBridge (Coin3CleanProgSpecOfWeights OneAngleExtHkHorizonCertTable)
open GqspTiersA135598 (gqsp_Tier1Pkg gqsp_Tier2Pkg gqsp_Tier3Pkg)
open GqspTiersB135598 (gqsp_Tier6Pkg gqsp_Tier9Pkg)
/-- `K = 1` segment schedule `R_j = j + 1` (`55` segments across `t = 1..10`). -/
def gqsp_ScheduleK1_135598 : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
end Part2_TierCompactMasterSpine

end TierTightSpine

end QuantumComputation.Specs.StoppingPowerSolution
