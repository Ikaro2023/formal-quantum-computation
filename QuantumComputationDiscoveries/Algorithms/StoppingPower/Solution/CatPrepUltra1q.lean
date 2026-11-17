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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SingleCatSelect80


@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspCatPrepSub600Nano

section
namespace GqspCatPrepSub600Nano
set_option exponentiation.threshold 256
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix Matrix.Norms.L2Operator BigOperators
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel TFreeLaurentGQSP
open CatalyzedLaurentGQSP
open CatalyzedLaurentGQSPBridge (cosTaylor sinTaylor cos_sin_taylor_alternating)
open ZeroAncillaUSP CatalystPrep
open SingleCatClosure (kActSingleCatClosure mActSingleCatClosure rCatTotInSingleCat
  rCatScratchInSingleCat inCatTotSingleCat rAncInSingleCat inCatScratchSingleCat pCat0SingleCat
  uCatNormSingleCat substActiveSingleCat substActiveSingleCat_count_TOFF
  substActiveSingleCat_count_T_le realizesCleanWorkspace_substActiveSingleCat singleCat_pCat0_pin
  catalyst_sandwich_of_smul_norm)
open SingleCatClosure.ZeroAncCatPrep1q (pythPhase norm_pythPhase p0Mat2 singleton_embed_p0Mat2
  norm_mul_p0Mat2_le seqProd_smul norm_seqProd_sub_mul_seqProd_proj_le seqProd_mul_absorb
  eq_add_mul_sqrt2 mat2Zw_entry_even_re mat2Zw_entry_even_im mat2Zw_entry_odd_re mat2Zw_entry_odd_im
  ideal_col0_of_ge2 pi_bounds_2pow64 complex_norm_le_of_re_im lin_comb_bounds catPrepWord
  catPrepWord_of_ge20 zCatBit zCatBit_of_ge20 wire_err_zero_0 wire_err_zero_1 wire_err_zero_2
  wire_err_le_tail)
/-- Per-wire `{H, S, T}` synthesis words (`idx = 0..30` active, `idx ≥ 31` Hadamard). -/
def catPrepWordUltra : ℕ → List HSTGate
  | 0 => [.H, .S, .S]
  | 1 => [.H, .S, .S, .S]
  | 2 => [.H, .T, .S, .S, .S]
  | 3 =>
      [.H, .H, .S, .S, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
      .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
      .T, .H, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T,
     .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H]
  | 4 =>
      [.H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
      .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
      .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T]
  | 5 =>
      [.H, .H, .S, .S, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
      .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
      .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H]
  | 6 =>
      [.H, .H, .S, .S, .H, .S, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
      .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .S, .T,
     .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H]
  | 7 =>
      [.H, .H, .S, .S, .H, .S, .S, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
      .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T]
  | 8 =>
      [.H, .H, .S, .S, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
      .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
      .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .T]
  | 9 =>
      [.H, .H, .S, .S, .H, .S, .S, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
      .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
      .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H]
  | 10 =>
      [.H, .H, .S, .S, .H, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
      .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T]
  | 11 =>
      [.H, .S, .S, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
      .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
      .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .S, .T,
     .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T]
  | 12 =>
      [.H, .H, .S, .S, .H, .S, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T,
      .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
      .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T]
  | 13 =>
      [.H, .H, .S, .S, .H, .S, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
      .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
      .S, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T]
  | 14 =>
      [.H, .H, .S, .S, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
      .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
      .H, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H]
  | 15 =>
      [.H, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
      .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
      .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T]
  | 16 =>
      [.H, .H, .S, .S, .H, .S, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
      .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
      .T, .H, .S, .T,
     .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .S]
  | 17 =>
      [.H, .H, .S, .S, .H, .S, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
      .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
      .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T]
  | 18 =>
      [.H, .S, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
      .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
      .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S]
  | 19 =>
      [.H, .S, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H,
      .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
      .S, .T, .H, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S]
  | 20 =>
      [.H, .S, .S, .S, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
      .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
      .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T]
  | 21 =>
      [.H, .H, .S, .S, .H, .S, .S, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
      .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T]
  | 22 =>
      [.H, .H, .S, .S, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
      .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
      .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T]
  | 23 =>
      [.H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
      .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
      .H, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S]
  | 24 =>
      [.H, .H, .S, .S, .H, .S, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
      .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
      .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .T,
     .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T]
  | 25 =>
      [.H, .S, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
      .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T,
      .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T,
     .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T,
       .H, .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T]
  | 26 =>
      [.H, .H, .S, .S, .H, .S, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T,
      .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
      .S, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T]
  | 27 =>
      [.H, .H, .S, .S, .H, .S, .S, .S, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
      .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
      .T, .H, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T]
  | 28 =>
      [.H, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
      .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .H, .S,
       .S, .H, .S, .S, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T,
       .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .T, .H,
     .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S,
       .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T]
  | 29 =>
      [.H, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
      .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .H, .S,
       .S, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H,
       .S, .T, .H, .S, .T,
     .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .S, .T, .H,
     .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S,
     .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T]
  | 30 =>
      [.H, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
      .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
      .T, .H, .S, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T,
       .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T,
       .H, .S, .T, .H, .S,
     .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
       .S, .T, .H, .T, .H,
     .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .H, .S,
       .S, .H, .S, .S, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H,
       .T, .H, .T, .H, .S,
     .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
       .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
       .H, .S, .T, .H, .T,
     .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
       .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
       .T, .H, .S, .T, .H,
     .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T,
       .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S,
       .T, .H, .T, .H, .T,
     .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T]
  | _ => [.H]
theorem catPrepWordUltra_of_ge31 {idx : ℕ} (h : 31 ≤ idx) : catPrepWordUltra idx = [.H] := by
  match idx with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 => omega
  | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => omega
  | _ + 31 => rfl
/-- Zero-ancilla 1-qubit `{H, S, T}` catalyst preparation circuit on `B_tot` wires. -/
def cCatPrepUltra1qGen (B_tot : ℕ) : Circuit B_tot :=
  Circuit.sequence (List.ofFn fun i : Fin B_tot ↦ hstWordCircuit (catPrepWordUltra i.val) i.rev)
@[simp] theorem count_toff_cCatPrepUltra1qGen (B_tot : ℕ) :
    (cCatPrepUltra1qGen B_tot).count PrimitiveGate.TOFF = 0 := by
  rw [cCatPrepUltra1qGen, Circuit.count_sequence, List.map_ofFn, List.sum_ofFn]
  simp
theorem sum_fin_le_sum_fin31_of_zero_ge31 (f : ℕ → ℕ) (hf : ∀ k, 31 ≤ k → f k = 0) (B_tot : ℕ) : (∑
    i : Fin B_tot, f i.val) ≤ ∑ k : Fin 31, f k.val := by
  have h_inc : ∀ m : ℕ, (∑ i : Fin m, f i.val) ≤ ∑ i : Fin (m + 1), f i.val := by
    intro m
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc]
    exact Nat.le_add_right _ _
  have h_step : ∀ m : ℕ, 31 ≤ m → (∑ i : Fin (m + 1), f i.val) = ∑ i : Fin m, f i.val := by
    intro m hm
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hf m hm, add_zero]
  by_cases hB : B_tot ≤ 31
  · have h_sub : ∀ d : ℕ, (∑ i : Fin (31 - d), f i.val) ≤ ∑ k : Fin 31, f k.val := by
      intro d
      induction d with
      | zero => exact le_rfl
      | succ d ih =>
        by_cases hd : d < 31
        · have heq : 31 - d = (31 - (d + 1)) + 1 := by omega
          exact (h_inc (31 - (d + 1))).trans (heq ▸ ih)
        · have heq : 31 - (d + 1) = 31 - d := by omega
          exact heq ▸ ih
    obtain ⟨d, rfl⟩ : ∃ d, B_tot = 31 - d := ⟨31 - B_tot, by omega⟩
    exact h_sub d
  · have h_add : ∀ d : ℕ, (∑ i : Fin (31 + d), f i.val) = ∑ k : Fin 31, f k.val := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        have h1 : 31 + (d + 1) = (31 + d) + 1 := by omega
        rw [h1, h_step (31 + d) (by omega), ih]
    obtain ⟨d, rfl⟩ : ∃ d, B_tot = 31 + d := ⟨B_tot - 31, by omega⟩
    exact (h_add d).le
theorem count_t_cCatPrepUltra1qGen_le (B_tot : ℕ) : (cCatPrepUltra1qGen B_tot).count PrimitiveGate.T
    ≤ 3650 := by
  rw [cCatPrepUltra1qGen, Circuit.count_sequence, List.map_ofFn]
  simp only [Function.comp_def, count_t_hstWordCircuit]
  rw [List.sum_ofFn]
  refine (sum_fin_le_sum_fin31_of_zero_ge31
    (fun k ↦ hstWordTCount (catPrepWordUltra k)) ?_ B_tot).trans ?_
  · intro k hk
    rw [catPrepWordUltra_of_ge31 hk]
    rfl
  · rw [← List.sum_ofFn]
    decide +kernel
/-- Pythagorean triple `(zp, zq, zr)` table for `zCatBitUltra` on wires `3..30`. -/
def zCatPythUltra : ℕ → ℤ × ℤ × ℤ
  | 3 => (-921481583739735112, 381690169461411066, 997404478952732170)
  | 4 => (-491983113844970059, 1187752305905469780, 1285613831791006141)
  | 5 => (233868093510737575, 564607523162440632, 611126779297039993)
  | 6 => (-7733497619798881, -3203319598732800, 8370677504662369)
  | 7 => (-910284848570555715, 377052329900382292, 985285220137004933)
  | 8 => (-25361600155341480, -10505118747836218, 27451198195079882)
  | 9 => (-141831150949825208, 58748386290080406, 153516931546460410)
  | 10 => (-553435593375728136, -1336111715438824310, 1446196899508508186)
  | 11 => (465951039663277675, 1124905319359685892, 1217588743741911517)
  | 12 => (-86662151812850223, 35896638625230536, 93802437182750705)
  | 13 => (814607423769040083, -337421442936170156, 881724721788359285)
  | 14 => (-710196171300563863, 294172886098598184, 768710796493426825)
  | 15 => (467347314057577041, 193581595820240680, 505853087563121009)
  | 16 => (-128795426563539688, 310939665583357734, 336558668788629610)
  | 17 => (-331546832727528417, 800424860128482056, 866373625523858945)
  | 18 => (-832397287868381637, 344790245919547516, 900980331933999245)
  | 19 => (432202923483720968, -1043430159561400074, 1129400666260740250)
  | 20 => (-138995808772357680, 57573949106862818, 150447979288661282)
  | 21 => (740073564671353927, 306548507639093736, 801049854042256345)
  | 22 => (49259623307071320, 20404004051249578, 53318232056942522)
  | 23 => (731502976401163153, -302998453740464904, 791773116146837425)
  | 24 => (-38721254997361912, -16038868972115766, 41911584394716250)
  | 25 => (898489891871093291, 372166698867853860, 972518451002717341)
  | 26 => (-553151561766939163, -1335426002463820116, 1445454689134772845)
  | 27 => (-251166045028787435, 104036382258571308, 271860168117461533)
  | 28 => (1, 0, 1)
  | 29 => (-1, 0, 1)
  | 30 => (-516313125760450629, -516313125759681460, 730177024881130829)
  | _ => (1, 0, 1)
/-- Per-wire rationalized unit global phase for `catPrepWordUltra`. -/
noncomputable def zCatBitUltra (idx : ℕ) : ℂ :=
  if idx ≤ 1 then 1
  else if idx = 2 then Complex.exp (-(phaseGradAngle 2 * Complex.I))
  else if idx < 31 then
    let t := zCatPythUltra idx
    pythPhase t.1 t.2.1 t.2.2
  else 1
theorem zCatBitUltra_of_ge31 {idx : ℕ} (h : 31 ≤ idx) : zCatBitUltra idx = 1 := by
  unfold zCatBitUltra
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
/-- Executable check that `zCatPythUltra idx` is a positive-denominator Pythagorean triple. -/
def checkPythUltra (idx : ℕ) : Bool :=
  let t := zCatPythUltra idx
  decide (0 < t.2.2) && decide (t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2)
theorem checkPythUltra_all : (List.range 31).all checkPythUltra = true := by decide +kernel
theorem norm_zCatBitUltra (idx : ℕ) : ‖zCatBitUltra idx‖ = 1 := by
  unfold zCatBitUltra
  by_cases h1 : idx ≤ 1
  · simp [h1]
  · rw [ite_eq_right h1]
    by_cases h2 : idx = 2
    · simp only [h2, ↓reduceIte]
      simpa [neg_mul] using Complex.norm_exp_ofReal_mul_I (-phaseGradAngle 2)
    · rw [ite_eq_right h2]
      by_cases h31 : idx < 31
      · rw [ite_eq_left h31]
        have hc := List.all_eq_true.mp checkPythUltra_all idx (List.mem_range.mpr h31)
        simp only [checkPythUltra, Bool.and_eq_true, decide_eq_true_eq] at hc
        have hpos : (0 : ℝ) < ((zCatPythUltra idx).2.2 : ℝ) := Int.cast_pos.mpr hc.1
        have hsq : (((zCatPythUltra idx).1 ^ 2 + (zCatPythUltra idx).2.1 ^ 2 : ℤ) : ℝ) =
            (((zCatPythUltra idx).2.2 ^ 2 : ℤ) : ℝ) := congrArg Int.cast hc.2
        push_cast at hsq
        exact norm_pythPhase _ _ _ hpos hsq
      · simp [h31]
/-- Global phase product across `B_tot` wires of `cCatPrepUltra1qGen`. -/
noncomputable def zCatGlobalUltra (B_tot : ℕ) : ℂ := ∏ i : Fin B_tot, zCatBitUltra i.val
theorem norm_zCatGlobalUltra (B_tot : ℕ) : ‖zCatGlobalUltra B_tot‖ = 1 := by
  unfold zCatGlobalUltra
  rw [norm_prod]
  exact Finset.prod_eq_one (fun i _ ↦ norm_zCatBitUltra i.val)
theorem sqrt2_bounds_2pow64 : (0x16a09e667f3bcc908 / 2 ^ 64 : ℝ) ≤ √2 ∧ √2 ≤ (0x16a09e667f3bcc909 /
    2 ^ 64 : ℝ) := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0x16a09e667f3bcc908 / 2 ^ 64)]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0x16a09e667f3bcc909 / 2 ^ 64)]
    exact Real.sqrt_le_sqrt (by norm_num)
theorem cos_sin_deg56_bracket {θ θ_lo θ_hi c_lo c_hi s_lo s_hi : ℝ} (h0 : 0 ≤ θ_lo) (hlo : θ_lo ≤ θ)
    (hhi : θ ≤ θ_hi) (hclo : c_lo ≤ 1 - θ_hi ^ 2 / 2 + θ_lo ^ 4 / 24 - θ_hi ^ 6 / 720 +
    θ_lo ^ 8 / 40320 - θ_hi ^
    10 / 3628800) (hchi : 1 - θ_lo ^ 2 / 2 + θ_hi ^ 4 / 24 - θ_lo ^ 6 / 720 + θ_hi ^ 8 / 40320 -
      θ_lo ^ 10 / 3628800 + θ_hi ^ 12 / 479001600 ≤ c_hi) (hslo : s_lo ≤ θ_lo - θ_hi ^ 3 / 6 +
      θ_lo ^ 5 / 120 - θ_hi ^
    7 / 5040 + θ_lo ^ 9 / 362880 - θ_hi ^ 11 / 39916800) (hshi : θ_hi - θ_lo ^ 3 / 6 +
      θ_hi ^ 5 / 120 - θ_lo ^ 7 / 5040 + θ_hi ^ 9 / 362880 - θ_lo ^ 11 / 39916800 + θ_hi ^ 13 /
      6227020800 ≤ s_hi) : c_lo ≤
    Real.cos θ ∧ Real.cos θ ≤ c_hi ∧ s_lo ≤ Real.sin θ ∧ Real.sin θ ≤ s_hi := by
  have hθ0 : 0 ≤ θ := h0.trans hlo
  have hc6 := (cos_sin_taylor_alternating 5 θ hθ0).1
  have hc7 := (cos_sin_taylor_alternating 6 θ hθ0).1
  have hs6 := (cos_sin_taylor_alternating 5 θ hθ0).2
  have hs7 := (cos_sin_taylor_alternating 6 θ hθ0).2
  have hp (n : ℕ) : θ_lo ^ n ≤ θ ^ n ∧ θ ^ n ≤ θ_hi ^ n :=
    ⟨pow_le_pow_left₀ h0 hlo n, pow_le_pow_left₀ hθ0 hhi n⟩
  dsimp [cosTaylor, sinTaylor, Nat.factorial] at hc6 hc7 hs6 hs7
  norm_num at hc6 hc7 hs6 hs7
  exact ⟨by linarith [(hp 2).2, (hp 4).1, (hp 6).2, (hp 8).1, (hp 10).2],
    by linarith [(hp 2).1, (hp 4).2, (hp 6).1, (hp 8).2, (hp 10).1, (hp 12).2],
    by linarith [(hp 3).2, (hp 5).1, (hp 7).2, (hp 9).1, (hp 11).2],
    by linarith [(hp 3).1, (hp 5).2, (hp 7).1, (hp 9).2, (hp 11).1, (hp 13).2]⟩
theorem abs_lin_sqrt2_2pow64_le {wa wb v klo khi e : ℝ}
    (hv_lo : klo ≤ wb - v / 2) (hv_hi : wb - v / 2 ≤ khi)
    (he_lo : -e ≤ wa + (if 0 ≤ klo then klo * (0x16a09e667f3bcc908 / 2 ^ 64)
                        else klo * (0x16a09e667f3bcc909 / 2 ^ 64)))
    (he_hi : wa + (if 0 ≤ khi then khi * (0x16a09e667f3bcc909 / 2 ^ 64)
                   else khi * (0x16a09e667f3bcc908 / 2 ^ 64)) ≤ e) :
    |wa + wb * √2 - (v / 2) * √2| ≤ e := by
  have hsq2 := sqrt2_bounds_2pow64
  have hrew : wa + wb * √2 - (v / 2) * √2 = wa + (wb - v / 2) * √2 := by ring
  rw [hrew, abs_le]
  constructor
  · by_cases hk : 0 ≤ klo <;> simp only [hk, ↓reduceIte] at he_lo <;> nlinarith [hsq2.1, hsq2.2]
  · by_cases hk : 0 ≤ khi <;> simp only [hk, ↓reduceIte] at he_hi <;> nlinarith [hsq2.1, hsq2.2]
theorem certify_wire_col0_ultra {idx : ℕ} (h2 : 2 ≤ idx)
    {m : Mat2Zw} (hw : evalList (catPrepWordUltra idx) matId = m) {zp zq zr : ℤ}
    (hz : zCatBitUltra idx = pythPhase zp zq zr) {w0ra w0rb w0ia w0ib w1ra w1rb w1ia w1ib : ℝ}
    (hm0r : (m.toMatrix 0 0).re = w0ra + w0rb * √2) (hm0i : (m.toMatrix 0 0).im = w0ia + w0ib * √2)
    (hm1r : (m.toMatrix 1 0).re = w1ra + w1rb * √2) (hm1i : (m.toMatrix 1 0).im = w1ia + w1ib * √2)
    {θ_lo θ_hi c_lo c_hi s_lo s_hi : ℝ} (hθ0 : 0 ≤ θ_lo)
    (hθ_lo : θ_lo ≤ (0x3243f6a8885a308d2 : ℝ) / 2 ^ 64 / (2 : ℝ) ^ (idx + 1))
    (hθ_hi : (0x3243f6a8885a308d4 : ℝ) / 2 ^ 64 / (2 : ℝ) ^ (idx + 1) ≤ θ_hi)
    (hclo : c_lo ≤ 1 - θ_hi ^ 2 / 2 + θ_lo ^ 4 / 24 - θ_hi ^ 6 / 720
      + θ_lo ^ 8 / 40320 - θ_hi ^ 10 / 3628800)
    (hchi : 1 - θ_lo ^ 2 / 2 + θ_hi ^ 4 / 24 - θ_lo ^ 6 / 720
      + θ_hi ^ 8 / 40320 - θ_lo ^ 10 / 3628800 + θ_hi ^ 12 / 479001600 ≤ c_hi)
    (hslo : s_lo ≤ θ_lo - θ_hi ^ 3 / 6 + θ_lo ^ 5 / 120 - θ_hi ^ 7 / 5040
      + θ_lo ^ 9 / 362880 - θ_hi ^ 11 / 39916800)
    (hshi : θ_hi - θ_lo ^ 3 / 6 + θ_hi ^ 5 / 120 - θ_lo ^ 7 / 5040
      + θ_hi ^ 9 / 362880 - θ_lo ^ 11 / 39916800 + θ_hi ^ 13 / 6227020800 ≤ s_hi)
    {k0r_lo k0r_hi e0r k0i_lo k0i_hi e0i k1r_lo k1r_hi e1r k1i_lo k1i_hi e1i c0 c1 bnd : ℝ}
    (hk0r_lo : k0r_lo ≤ w0rb - ((if 0 ≤ (zp : ℝ) / zr then ((zp : ℝ) / zr) * c_hi
      else ((zp : ℝ) / zr) * c_lo) + (if 0 ≤ -((zq : ℝ) / zr) then (-((zq : ℝ) / zr)) * s_hi
      else (-((zq : ℝ) / zr)) * s_lo)) / 2)
    (hk0r_hi : w0rb - ((if 0 ≤ (zp : ℝ) / zr then ((zp : ℝ) / zr) * c_lo
      else ((zp : ℝ) / zr) * c_hi) + (if 0 ≤ -((zq : ℝ) / zr) then (-((zq : ℝ) / zr)) * s_lo
      else (-((zq : ℝ) / zr)) * s_hi)) / 2 ≤ k0r_hi)
    (he0r_lo : -e0r ≤ w0ra + (if 0 ≤ k0r_lo then k0r_lo * (0x16a09e667f3bcc908 / 2 ^ 64)
      else k0r_lo * (0x16a09e667f3bcc909 / 2 ^ 64)))
    (he0r_hi : w0ra + (if 0 ≤ k0r_hi then k0r_hi * (0x16a09e667f3bcc909 / 2 ^ 64)
      else k0r_hi * (0x16a09e667f3bcc908 / 2 ^ 64)) ≤ e0r)
    (hk0i_lo : k0i_lo ≤ w0ib - ((if 0 ≤ (zq : ℝ) / zr then ((zq : ℝ) / zr) * c_hi
      else ((zq : ℝ) / zr) * c_lo) + (if 0 ≤ (zp : ℝ) / zr then ((zp : ℝ) / zr) * s_hi
      else ((zp : ℝ) / zr) * s_lo)) / 2)
    (hk0i_hi : w0ib - ((if 0 ≤ (zq : ℝ) / zr then ((zq : ℝ) / zr) * c_lo
      else ((zq : ℝ) / zr) * c_hi) + (if 0 ≤ (zp : ℝ) / zr then ((zp : ℝ) / zr) * s_lo
      else ((zp : ℝ) / zr) * s_hi)) / 2 ≤ k0i_hi)
    (he0i_lo : -e0i ≤ w0ia + (if 0 ≤ k0i_lo then k0i_lo * (0x16a09e667f3bcc908 / 2 ^ 64)
      else k0i_lo * (0x16a09e667f3bcc909 / 2 ^ 64)))
    (he0i_hi : w0ia + (if 0 ≤ k0i_hi then k0i_hi * (0x16a09e667f3bcc909 / 2 ^ 64)
      else k0i_hi * (0x16a09e667f3bcc908 / 2 ^ 64)) ≤ e0i)
    (hk1r_lo : k1r_lo ≤ w1rb - ((if 0 ≤ (zp : ℝ) / zr then ((zp : ℝ) / zr) * c_hi
      else ((zp : ℝ) / zr) * c_lo) + (if 0 ≤ (zq : ℝ) / zr then ((zq : ℝ) / zr) * s_hi
      else ((zq : ℝ) / zr) * s_lo)) / 2)
    (hk1r_hi : w1rb - ((if 0 ≤ (zp : ℝ) / zr then ((zp : ℝ) / zr) * c_lo
      else ((zp : ℝ) / zr) * c_hi) + (if 0 ≤ (zq : ℝ) / zr then ((zq : ℝ) / zr) * s_lo
      else ((zq : ℝ) / zr) * s_hi)) / 2 ≤ k1r_hi)
    (he1r_lo : -e1r ≤ w1ra + (if 0 ≤ k1r_lo then k1r_lo * (0x16a09e667f3bcc908 / 2 ^ 64)
      else k1r_lo * (0x16a09e667f3bcc909 / 2 ^ 64)))
    (he1r_hi : w1ra + (if 0 ≤ k1r_hi then k1r_hi * (0x16a09e667f3bcc909 / 2 ^ 64)
      else k1r_hi * (0x16a09e667f3bcc908 / 2 ^ 64)) ≤ e1r)
    (hk1i_lo : k1i_lo ≤ w1ib - ((if 0 ≤ (zq : ℝ) / zr then ((zq : ℝ) / zr) * c_hi
      else ((zq : ℝ) / zr) * c_lo) + (if 0 ≤ -((zp : ℝ) / zr) then (-((zp : ℝ) / zr)) * s_hi
      else (-((zp : ℝ) / zr)) * s_lo)) / 2)
    (hk1i_hi : w1ib - ((if 0 ≤ (zq : ℝ) / zr then ((zq : ℝ) / zr) * c_lo
      else ((zq : ℝ) / zr) * c_hi) + (if 0 ≤ -((zp : ℝ) / zr) then (-((zp : ℝ) / zr)) * s_lo
      else (-((zp : ℝ) / zr)) * s_hi)) / 2 ≤ k1i_hi)
    (he1i_lo : -e1i ≤ w1ia + (if 0 ≤ k1i_lo then k1i_lo * (0x16a09e667f3bcc908 / 2 ^ 64)
      else k1i_lo * (0x16a09e667f3bcc909 / 2 ^ 64)))
    (he1i_hi : w1ia + (if 0 ≤ k1i_hi then k1i_hi * (0x16a09e667f3bcc909 / 2 ^ 64)
      else k1i_hi * (0x16a09e667f3bcc908 / 2 ^ 64)) ≤ e1i)
    (hc0_0 : 0 ≤ c0) (hc0 : e0r ^ 2 + e0i ^ 2 ≤ c0 ^ 2)
    (hc1_0 : 0 ≤ c1) (hc1 : e1r ^ 2 + e1i ^ 2 ≤ c1 ^ 2) (hbnd : c0 + c1 ≤ bnd) :
    ‖(wordMatrix2 (catPrepWordUltra idx) -
        zCatBitUltra idx • (idealPhaseGradDiagBit idx * Qubit.H).1) * p0Mat2‖ ≤ bnd := by
  let D := wordMatrix2 (catPrepWordUltra idx) -
    zCatBitUltra idx • (idealPhaseGradDiagBit idx * Qubit.H).1
  have hpi := pi_bounds_2pow64
  have hθ_b : θ_lo ≤ phaseGradAngle idx ∧ phaseGradAngle idx ≤ θ_hi := by
    unfold phaseGradAngle
    exact ⟨hθ_lo.trans (div_le_div_of_nonneg_right hpi.1 (by positivity)),
      (div_le_div_of_nonneg_right hpi.2 (by positivity)).trans hθ_hi⟩
  rcases cos_sin_deg56_bracket hθ0 hθ_b.1 hθ_b.2 hclo hchi hslo hshi with ⟨hcl, hch, hsl, hsh⟩
  rcases ideal_col0_of_ge2 h2 zp zq zr with ⟨hi0r, hi0i, hi1r, hi1i⟩
  have hw_eq : wordMatrix2 (catPrepWordUltra idx) = m.toMatrix := by
    unfold wordMatrix2; rw [hw]
  have hD0r : (D 0 0).re = w0ra + w0rb * √2 - (((zp : ℝ) / zr * Real.cos (phaseGradAngle idx)
      + (-((zq : ℝ) / zr)) * Real.sin (phaseGradAngle idx)) / 2) * √2 := by
    dsimp only [D]; rw [Matrix.sub_apply, Complex.sub_re, hw_eq, hz, hm0r, hi0r]; ring
  have hD0i : (D 0 0).im = w0ia + w0ib * √2 - (((zq : ℝ) / zr * Real.cos (phaseGradAngle idx)
      + ((zp : ℝ) / zr) * Real.sin (phaseGradAngle idx)) / 2) * √2 := by
    dsimp only [D]; rw [Matrix.sub_apply, Complex.sub_im, hw_eq, hz, hm0i, hi0i]
  have hD1r : (D 1 0).re = w1ra + w1rb * √2 - (((zp : ℝ) / zr * Real.cos (phaseGradAngle idx)
      + ((zq : ℝ) / zr) * Real.sin (phaseGradAngle idx)) / 2) * √2 := by
    dsimp only [D]; rw [Matrix.sub_apply, Complex.sub_re, hw_eq, hz, hm1r, hi1r]
  have hD1i : (D 1 0).im = w1ia + w1ib * √2 - (((zq : ℝ) / zr * Real.cos (phaseGradAngle idx)
      + (-((zp : ℝ) / zr)) * Real.sin (phaseGradAngle idx)) / 2) * √2 := by
    dsimp only [D]; rw [Matrix.sub_apply, Complex.sub_im, hw_eq, hz, hm1i, hi1i]; ring
  have hl0r := lin_comb_bounds hcl hch hsl hsh (a := (zp : ℝ) / zr) (b := -((zq : ℝ) / zr))
  have hl0i := lin_comb_bounds hcl hch hsl hsh (a := (zq : ℝ) / zr) (b := (zp : ℝ) / zr)
  have hl1r := lin_comb_bounds hcl hch hsl hsh (a := (zp : ℝ) / zr) (b := (zq : ℝ) / zr)
  have hl1i := lin_comb_bounds hcl hch hsl hsh (a := (zq : ℝ) / zr) (b := -((zp : ℝ) / zr))
  have hb0r : |(D 0 0).re| ≤ e0r := by
    rw [hD0r]; exact abs_lin_sqrt2_2pow64_le (by linarith [hl0r.2]) (by linarith [hl0r.1])
      he0r_lo he0r_hi
  have hb0i : |(D 0 0).im| ≤ e0i := by
    rw [hD0i]; exact abs_lin_sqrt2_2pow64_le (by linarith [hl0i.2]) (by linarith [hl0i.1])
      he0i_lo he0i_hi
  have hb1r : |(D 1 0).re| ≤ e1r := by
    rw [hD1r]; exact abs_lin_sqrt2_2pow64_le (by linarith [hl1r.2]) (by linarith [hl1r.1])
      he1r_lo he1r_hi
  have hb1i : |(D 1 0).im| ≤ e1i := by
    rw [hD1i]; exact abs_lin_sqrt2_2pow64_le (by linarith [hl1i.2]) (by linarith [hl1i.1])
      he1i_lo he1i_hi
  refine (norm_mul_p0Mat2_le D).trans ?_
  exact (add_le_add (complex_norm_le_of_re_im hc0_0 hb0r hb0i hc0)
    (complex_norm_le_of_re_im hc1_0 hb1r hb1i hc1)).trans hbnd
theorem wire_err_zero_ultra_0 : (wordMatrix2 (catPrepWordUltra 0) - zCatBitUltra 0 •
    (idealPhaseGradDiagBit 0 * Qubit.H).1) * p0Mat2 = 0 := by
  simpa [catPrepWordUltra, zCatBitUltra, catPrepWord, zCatBit] using wire_err_zero_0
theorem wire_err_zero_ultra_1 : (wordMatrix2 (catPrepWordUltra 1) - zCatBitUltra 1 •
    (idealPhaseGradDiagBit 1 * Qubit.H).1) * p0Mat2 = 0 := by
  simpa [catPrepWordUltra, zCatBitUltra, catPrepWord, zCatBit] using wire_err_zero_1
theorem wire_err_zero_ultra_2 : (wordMatrix2 (catPrepWordUltra 2) - zCatBitUltra 2 •
    (idealPhaseGradDiagBit 2 * Qubit.H).1) * p0Mat2 = 0 := by
  simpa [catPrepWordUltra, zCatBitUltra, catPrepWord, zCatBit] using wire_err_zero_2
theorem wire_err_le_ultra_tail {idx : ℕ} (h31 : 31 ≤ idx) : ‖(wordMatrix2 (catPrepWordUltra idx) -
    zCatBitUltra idx • (idealPhaseGradDiagBit idx * Qubit.H).1) * p0Mat2‖ ≤ (4442885 / 1000000 : ℝ)
    * (1 / 2 : ℝ) ^
    (idx + 1) := by
  have h20 : 20 ≤ idx := Nat.le_trans (by decide : 20 ≤ 31) h31
  rw [catPrepWordUltra_of_ge31 h31, zCatBitUltra_of_ge31 h31, ← catPrepWord_of_ge20 h20,
    ← zCatBit_of_ge20 h20]
  exact wire_err_le_tail h20
/-- Per-wire head error bound numerator in units of `10⁻¹²`. -/
def wireBoundUltraN12 : ℕ → ℕ
  | 0 | 1 | 2 => 0
  | 5 => 1
  | 13 | 20 | 21 | 30 => 2
  | 9 | 10 | 11 | 15 | 16 | 17 | 23 | 28 | 29 => 3
  | 4 | 6 | 19 | 24 | 25 => 4
  | 3 | 7 | 8 | 12 | 14 | 18 | 27 => 5
  | 22 | 26 => 6
  | _ => 0
/-- Floor division on `ℤ` for positive denominators using only non-negative `/` division. -/
def zFloorDiv (n d : ℤ) : ℤ := if 0 ≤ n then n / d else -(((-n) + d - 1) / d)
/-- Ceiling division on `ℤ` for positive denominators. -/
def zCeilDiv (n d : ℤ) : ℤ := -zFloorDiv (-n) d
/-- Monomial power lower bound at fixed-point denominator `sh`. -/
def zPowLo (sh x : ℤ) : ℕ → ℤ
  | 0 => sh
  | d + 1 => zFloorDiv (zPowLo sh x d * x) sh
/-- Monomial power upper bound at fixed-point denominator `sh`. -/
def zPowHi (sh x : ℤ) : ℕ → ℤ
  | 0 => sh
  | d + 1 => zCeilDiv (zPowHi sh x d * x) sh
/-- Scaled column-0 real/imaginary `ℤ[√2]` coefficients of `m` at denominator `2^80`. -/
def mat2ZwCol0Coeffs80 (m : Mat2Zw) : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  let k := m.h / 2
  let sh : ℤ := (2 : ℤ) ^ 80
  let dk : ℤ := (2 : ℤ) ^ k
  let dk1 : ℤ := (2 : ℤ) ^ (k + 1)
  if m.h % 2 = 0 then
    (zFloorDiv (m.m00.c0 * sh) dk, zFloorDiv ((m.m00.c1 - m.m00.c3) * sh) dk1,
     zFloorDiv (m.m00.c2 * sh) dk, zFloorDiv ((m.m00.c1 + m.m00.c3) * sh) dk1,
     zFloorDiv (m.m10.c0 * sh) dk, zFloorDiv ((m.m10.c1 - m.m10.c3) * sh) dk1,
     zFloorDiv (m.m10.c2 * sh) dk, zFloorDiv ((m.m10.c1 + m.m10.c3) * sh) dk1)
  else
    (zFloorDiv ((m.m00.c1 - m.m00.c3) * sh) dk1, zFloorDiv (m.m00.c0 * sh) dk1,
     zFloorDiv ((m.m00.c1 + m.m00.c3) * sh) dk1, zFloorDiv (m.m00.c2 * sh) dk1,
     zFloorDiv ((m.m10.c1 - m.m10.c3) * sh) dk1, zFloorDiv (m.m10.c0 * sh) dk1,
     zFloorDiv ((m.m10.c1 + m.m10.c3) * sh) dk1, zFloorDiv (m.m10.c2 * sh) dk1)
/-- Exact equality check for `mat2ZwCol0Coeffs80` against `m.toMatrix`. -/
def checkMat2ZwCol080 (m : Mat2Zw) (w0ra w0rb w0ia w0ib w1ra w1rb w1ia w1ib : ℤ) : Bool :=
  let k := m.h / 2
  let sh : ℤ := (2 : ℤ) ^ 80
  if m.h % 2 = 0 then
    decide (w0ra * (2 : ℤ) ^ k = m.m00.c0 * sh) &&
    decide (w0rb * (2 : ℤ) ^ (k + 1) = (m.m00.c1 - m.m00.c3) * sh) &&
    decide (w0ia * (2 : ℤ) ^ k = m.m00.c2 * sh) &&
    decide (w0ib * (2 : ℤ) ^ (k + 1) = (m.m00.c1 + m.m00.c3) * sh) &&
    decide (w1ra * (2 : ℤ) ^ k = m.m10.c0 * sh) &&
    decide (w1rb * (2 : ℤ) ^ (k + 1) = (m.m10.c1 - m.m10.c3) * sh) &&
    decide (w1ia * (2 : ℤ) ^ k = m.m10.c2 * sh) &&
    decide (w1ib * (2 : ℤ) ^ (k + 1) = (m.m10.c1 + m.m10.c3) * sh)
  else
    decide (w0ra * (2 : ℤ) ^ (k + 1) = (m.m00.c1 - m.m00.c3) * sh) &&
    decide (w0rb * (2 : ℤ) ^ (k + 1) = m.m00.c0 * sh) &&
    decide (w0ia * (2 : ℤ) ^ (k + 1) = (m.m00.c1 + m.m00.c3) * sh) &&
    decide (w0ib * (2 : ℤ) ^ (k + 1) = m.m00.c2 * sh) &&
    decide (w1ra * (2 : ℤ) ^ (k + 1) = (m.m10.c1 - m.m10.c3) * sh) &&
    decide (w1rb * (2 : ℤ) ^ (k + 1) = m.m10.c0 * sh) &&
    decide (w1ia * (2 : ℤ) ^ (k + 1) = (m.m10.c1 + m.m10.c3) * sh) &&
    decide (w1ib * (2 : ℤ) ^ (k + 1) = m.m10.c2 * sh)
/-- Witness generator `(kLo, kHi, e)` for a single real/imaginary matrix component. -/
def compWitness80 (zr za zb wa wb cLo cHi sLo sHi : ℤ) : ℤ × ℤ × ℤ :=
  let vLo := (if 0 ≤ za then zFloorDiv (za * cLo) zr else zFloorDiv (za * cHi) zr) +
    (if 0 ≤ zb then zFloorDiv (zb * sLo) zr else zFloorDiv (zb * sHi) zr)
  let vHi := (if 0 ≤ za then zCeilDiv (za * cHi) zr else zCeilDiv (za * cLo) zr) +
    (if 0 ≤ zb then zCeilDiv (zb * sHi) zr else zCeilDiv (zb * sLo) zr)
  let kLo := wb - zCeilDiv vHi 2
  let kHi := wb - zFloorDiv vLo 2
  let p64 : ℤ := (2 : ℤ) ^ 64
  let sLo2 : ℤ := 0x16a09e667f3bcc908
  let sHi2 : ℤ := 0x16a09e667f3bcc909
  let loVal := wa + (if 0 ≤ kLo then zFloorDiv (kLo * sLo2) p64 else zFloorDiv (kLo * sHi2) p64)
  let hiVal := wa + (if 0 ≤ kHi then zCeilDiv (kHi * sHi2) p64 else zCeilDiv (kHi * sLo2) p64)
  let e := max 0 (max (-loVal) hiVal)
  (kLo, kHi, e)
/-- Exact integer check certifying component error bound `e / sh`. -/
def compCheck80 (zr za zb wa wb kLo kHi e cLo cHi sLo sHi : ℤ) : Bool :=
  let uHi : ℤ := (if 0 ≤ za then za * cHi else za * cLo) +
    (if 0 ≤ zb then zb * sHi else zb * sLo)
  let uLo : ℤ := (if 0 ≤ za then za * cLo else za * cHi) +
    (if 0 ≤ zb then zb * sLo else zb * sHi)
  let p64 : ℤ := (2 : ℤ) ^ 64
  let sLo2 : ℤ := 0x16a09e667f3bcc908
  let sHi2 : ℤ := 0x16a09e667f3bcc909
  decide (uHi ≤ 2 * zr * (wb - kLo)) &&
  decide (2 * zr * (wb - kHi) ≤ uLo) &&
  decide (-e * p64 ≤ wa * p64 + (if 0 ≤ kLo then kLo * sLo2 else kLo * sHi2)) &&
  decide (wa * p64 + (if 0 ≤ kHi then kHi * sHi2 else kHi * sLo2) ≤ e * p64)
/-- Degree-5/6 cosine/sine polynomial bracket check at fixed-point denominator `sh`. -/
def checkCosSinPoly80 (sh tLo tHi cLo cHi sLo sHi : ℤ) : Bool := decide (cLo * 3628800 * sh ^
    9 ≤ 3628800 * sh ^ 10 - 1814400 * tHi ^ 2 * sh ^ 8 + 151200 * tLo ^ 4 * sh ^ 6 - 5040 *
    tHi ^ 6 * sh ^ 4 + 90 * tLo ^ 8 * sh ^ 2 - tHi ^ 10) && decide (479001600 * sh ^ 12 -
    239500800 * tLo ^ 2 * sh ^ 10 + 19958400 * tHi ^ 4 * sh ^ 8 - 665280 * tLo ^ 6 * sh ^ 6 +
    11880 * tHi ^ 8 * sh ^ 4 - 132 * tLo ^ 10 * sh ^ 2 + tHi ^ 12 ≤ cHi * 479001600 * sh ^ 11)
    && decide (sLo * 39916800 * sh ^ 10 ≤ 39916800 * tLo * sh ^ 10 - 6652800 * tHi ^ 3 * sh ^
    8 + 332640 * tLo ^ 5 * sh ^ 6 - 7920 * tHi ^ 7 * sh ^ 4 + 110 * tLo ^ 9 * sh ^ 2 - tHi ^
    11) && decide (6227020800 * tHi * sh ^ 12 - 1037836800 * tLo ^ 3 * sh ^ 10 + 51891840 *
    tHi ^ 5 * sh ^ 8 - 1235520 * tLo ^ 7 * sh ^ 6 + 17160 * tHi ^ 9 * sh ^ 4 - 156 * tLo ^ 11
    * sh ^ 2 + tHi ^ 13 ≤ sHi * 6227020800 * sh ^ 12)
/-- Executable end-to-end column-0 error verifier for wire `idx ∈ [3..30]`. -/
def checkWireUltra (idx : ℕ) : Bool :=
  let sh : ℤ := (2 : ℤ) ^ 80
  let m := evalList (catPrepWordUltra idx) matId
  let pyth := zCatPythUltra idx
  let zp := pyth.1
  let zq := pyth.2.1
  let zr := pyth.2.2
  let cw := mat2ZwCol0Coeffs80 m
  let w0ra := cw.1
  let w0rb := cw.2.1
  let w0ia := cw.2.2.1
  let w0ib := cw.2.2.2.1
  let w1ra := cw.2.2.2.2.1
  let w1rb := cw.2.2.2.2.2.1
  let w1ia := cw.2.2.2.2.2.2.1
  let w1ib := cw.2.2.2.2.2.2.2
  let dAng : ℤ := (2 : ℤ) ^ (64 + idx + 1)
  let tLo := zFloorDiv (0x3243f6a8885a308d2 * sh) dAng
  let tHi := zCeilDiv (0x3243f6a8885a308d4 * sh) dAng
  let cLo := sh - zCeilDiv (zPowHi sh tHi 2) 2 + zFloorDiv (zPowLo sh tLo 4) 24
    - zCeilDiv (zPowHi sh tHi 6) 720 + zFloorDiv (zPowLo sh tLo 8) 40320
    - zCeilDiv (zPowHi sh tHi 10) 3628800
  let cHi := sh - zFloorDiv (zPowLo sh tLo 2) 2 + zCeilDiv (zPowHi sh tHi 4) 24
    - zFloorDiv (zPowLo sh tLo 6) 720 + zCeilDiv (zPowHi sh tHi 8) 40320
    - zFloorDiv (zPowLo sh tLo 10) 3628800 + zCeilDiv (zPowHi sh tHi 12) 479001600
  let sLo := tLo - zCeilDiv (zPowHi sh tHi 3) 6 + zFloorDiv (zPowLo sh tLo 5) 120
    - zCeilDiv (zPowHi sh tHi 7) 5040 + zFloorDiv (zPowLo sh tLo 9) 362880
    - zCeilDiv (zPowHi sh tHi 11) 39916800
  let sHi := tHi - zFloorDiv (zPowLo sh tLo 3) 6 + zCeilDiv (zPowHi sh tHi 5) 120
    - zFloorDiv (zPowLo sh tLo 7) 5040 + zCeilDiv (zPowHi sh tHi 9) 362880
    - zFloorDiv (zPowLo sh tLo 11) 39916800 + zCeilDiv (zPowHi sh tHi 13) 6227020800
  let wit0r := compWitness80 zr zp (-zq) w0ra w0rb cLo cHi sLo sHi
  let wit0i := compWitness80 zr zq zp w0ia w0ib cLo cHi sLo sHi
  let wit1r := compWitness80 zr zp zq w1ra w1rb cLo cHi sLo sHi
  let wit1i := compWitness80 zr zq (-zp) w1ia w1ib cLo cHi sLo sHi
  let e0r := wit0r.2.2
  let e0i := wit0i.2.2
  let e1r := wit1r.2.2
  let e1i := wit1i.2.2
  let aSq : ℤ := e0r ^ 2 + e0i ^ 2
  let cSq : ℤ := e1r ^ 2 + e1i ^ 2
  let mCap : ℤ := zFloorDiv ((wireBoundUltraN12 idx : ℤ) * sh) 1000000000000
  decide (0 < zr) &&
  checkMat2ZwCol080 m w0ra w0rb w0ia w0ib w1ra w1rb w1ia w1ib &&
  decide (0 ≤ tLo) &&
  decide (tLo * dAng ≤ 0x3243f6a8885a308d2 * sh) &&
  decide (0x3243f6a8885a308d4 * sh ≤ tHi * dAng) &&
  checkCosSinPoly80 sh tLo tHi cLo cHi sLo sHi &&
  compCheck80 zr zp (-zq) w0ra w0rb wit0r.1 wit0r.2.1 e0r cLo cHi sLo sHi &&
  compCheck80 zr zq zp w0ia w0ib wit0i.1 wit0i.2.1 e0i cLo cHi sLo sHi &&
  compCheck80 zr zp zq w1ra w1rb wit1r.1 wit1r.2.1 e1r cLo cHi sLo sHi &&
  compCheck80 zr zq (-zp) w1ia w1ib wit1i.1 wit1i.2.1 e1i cLo cHi sLo sHi &&
  decide (0 ≤ mCap) &&
  decide (mCap * 1000000000000 ≤ (wireBoundUltraN12 idx : ℤ) * sh) &&
  decide (aSq + cSq ≤ mCap ^ 2) &&
  decide (4 * aSq * cSq ≤ (mCap ^ 2 - aSq - cSq) ^ 2)
theorem real_cast_le_of_decide {a b : ℤ} (h : decide (a ≤ b) = true) : (a : ℝ) ≤ (b : ℝ) :=
  Int.cast_le.mpr (of_decide_eq_true h)
theorem real_cast_pos_of_decide {a : ℤ} (h : decide (0 < a) = true) : (0 : ℝ) < (a : ℝ) :=
  Int.cast_pos.mpr (of_decide_eq_true h)
theorem le_of_mul_pos_le {x y p : ℝ} (hp : 0 < p) (h : x * p ≤ y * p) : x ≤ y := by
  by_contra hlt
  have hgt : y < x := lt_of_not_ge hlt
  linarith [mul_lt_mul_of_pos_right hgt hp]
theorem div_pow2_eq_div_scale80 {w c : ℤ} {p : ℕ} (h : decide (w * (2 : ℤ) ^ p = c * (2 : ℤ) ^ 80) =
    true) : (c : ℝ) / (2 : ℝ) ^ p = (w : ℝ) / (2 : ℝ) ^ 80 := by
  have hz : ((w * (2 : ℤ) ^ p : ℤ) : ℝ) = ((c * (2 : ℤ) ^ 80 : ℤ) : ℝ) :=
    congrArg Int.cast (of_decide_eq_true h)
  push_cast at hz
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hs : (2 : ℝ) ^ 80 ≠ 0 := by positivity
  rw [div_eq_div_iff hp hs]
  linarith
theorem mat2Zw_col0_of_check (m : Mat2Zw) {w0ra w0rb w0ia w0ib w1ra w1rb w1ia w1ib : ℤ} (h :
    checkMat2ZwCol080 m w0ra w0rb w0ia w0ib w1ra w1rb w1ia w1ib = true) : (m.toMatrix 0 0).re =
    (w0ra : ℝ) / (2 : ℝ) ^ 80
    + ((w0rb : ℝ) / (2 : ℝ) ^ 80) * √2 ∧ (m.toMatrix 0 0).im = (w0ia : ℝ) / (2 : ℝ) ^ 80 +
      ((w0ib : ℝ) / (2 : ℝ) ^ 80) * √2 ∧ (m.toMatrix 1 0).re = (w1ra : ℝ) / (2 : ℝ) ^ 80 +
      ((w1rb : ℝ) / (2 : ℝ) ^ 80) * √2 ∧
    (m.toMatrix 1 0).im = (w1ia : ℝ) / (2 : ℝ) ^ 80 + ((w1ib : ℝ) / (2 : ℝ) ^ 80) * √2 := by
  unfold checkMat2ZwCol080 at h
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  by_cases he : m.h % 2 = 0
  · rw [ite_eq_left he] at h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    have hk : m.h = 2 * (m.h / 2) := by omega
    have hr0 := mat2Zw_entry_even_re m (m.h / 2) hk 0
    have hi0 := mat2Zw_entry_even_im m (m.h / 2) hk 0
    have hr1 := mat2Zw_entry_even_re m (m.h / 2) hk 1
    have hi1 := mat2Zw_entry_even_im m (m.h / 2) hk 1
    simp only [↓reduceIte, h10] at hr0 hi0 hr1 hi1
    rw [← Int.cast_sub] at hr0 hr1
    rw [← Int.cast_add] at hi0 hi1
    exact ⟨eq_add_mul_sqrt2 hr0 (div_pow2_eq_div_scale80 h1) (div_pow2_eq_div_scale80 h2),
      eq_add_mul_sqrt2 hi0 (div_pow2_eq_div_scale80 h3) (div_pow2_eq_div_scale80 h4),
      eq_add_mul_sqrt2 hr1 (div_pow2_eq_div_scale80 h5) (div_pow2_eq_div_scale80 h6),
      eq_add_mul_sqrt2 hi1 (div_pow2_eq_div_scale80 h7) (div_pow2_eq_div_scale80 h8)⟩
  · rw [ite_eq_right he] at h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    have hk : m.h = 2 * (m.h / 2) + 1 := by omega
    have hr0 := mat2Zw_entry_odd_re m (m.h / 2) hk 0
    have hi0 := mat2Zw_entry_odd_im m (m.h / 2) hk 0
    have hr1 := mat2Zw_entry_odd_re m (m.h / 2) hk 1
    have hi1 := mat2Zw_entry_odd_im m (m.h / 2) hk 1
    simp only [↓reduceIte, h10] at hr0 hi0 hr1 hi1
    rw [← Int.cast_sub] at hr0 hr1
    rw [← Int.cast_add] at hi0 hi1
    exact ⟨eq_add_mul_sqrt2 hr0 (div_pow2_eq_div_scale80 h1) (div_pow2_eq_div_scale80 h2),
      eq_add_mul_sqrt2 hi0 (div_pow2_eq_div_scale80 h3) (div_pow2_eq_div_scale80 h4),
      eq_add_mul_sqrt2 hr1 (div_pow2_eq_div_scale80 h5) (div_pow2_eq_div_scale80 h6),
      eq_add_mul_sqrt2 hi1 (div_pow2_eq_div_scale80 h7) (div_pow2_eq_div_scale80 h8)⟩
private theorem eq_imp_le {a b c d : ℝ} (h : c ≤ d) (h1 : a = c) (h2 : b = d) : a ≤ b := by
  linarith
theorem cos_sin_poly_of_check {sh tLo tHi cLo cHi sLo sHi : ℤ} (hsh : (0 : ℝ) < (sh : ℝ)) (h :
    checkCosSinPoly80 sh tLo tHi cLo cHi sLo sHi = true) : ((cLo : ℝ) / (sh : ℝ) ≤ 1 - ((tHi : ℝ) /
    (sh : ℝ)) ^ 2 / 2 +
    ((tLo : ℝ) / (sh : ℝ)) ^ 4 / 24 - ((tHi : ℝ) / (sh : ℝ)) ^ 6 / 720 + ((tLo : ℝ) / (sh : ℝ)) ^ 8
      / 40320 - ((tHi : ℝ) / (sh : ℝ)) ^ 10 / 3628800) ∧ (1 - ((tLo : ℝ) / (sh : ℝ)) ^ 2 / 2 +
      ((tHi : ℝ) / (sh :
    ℝ)) ^ 4 / 24 - ((tLo : ℝ) / (sh : ℝ)) ^ 6 / 720 + ((tHi : ℝ) / (sh : ℝ)) ^ 8 / 40320 -
      ((tLo : ℝ) / (sh : ℝ)) ^ 10 / 3628800 + ((tHi : ℝ) / (sh : ℝ)) ^ 12 / 479001600 ≤ (cHi : ℝ) /
      (sh : ℝ)) ∧ ((sLo : ℝ) /
    (sh : ℝ) ≤ (tLo : ℝ) / (sh : ℝ) - ((tHi : ℝ) / (sh : ℝ)) ^ 3 / 6 + ((tLo : ℝ) / (sh : ℝ)) ^ 5 /
      120 - ((tHi : ℝ) / (sh : ℝ)) ^ 7 / 5040 + ((tLo : ℝ) / (sh : ℝ)) ^ 9 / 362880 - ((tHi : ℝ) /
      (sh : ℝ)) ^ 11 /
    39916800) ∧ ((tHi : ℝ) / (sh : ℝ) - ((tLo : ℝ) / (sh : ℝ)) ^ 3 / 6 + ((tHi : ℝ) / (sh : ℝ)) ^ 5
      / 120 - ((tLo : ℝ) / (sh : ℝ)) ^ 7 / 5040 + ((tHi : ℝ) / (sh : ℝ)) ^ 9 / 362880 - ((tLo : ℝ) /
      (sh : ℝ)) ^ 11
    / 39916800 + ((tHi : ℝ) / (sh : ℝ)) ^ 13 / 6227020800 ≤ (sHi : ℝ) / (sh : ℝ)) := by
  unfold checkCosSinPoly80 at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hc1, hc2⟩, hs1⟩, hs2⟩
  have hne : (sh : ℝ) ≠ 0 := hsh.ne'
  have hr1 := real_cast_le_of_decide hc1
  have hr2 := real_cast_le_of_decide hc2
  have hr3 := real_cast_le_of_decide hs1
  have hr4 := real_cast_le_of_decide hs2
  push_cast at hr1 hr2 hr3 hr4
  exact ⟨le_of_mul_pos_le (by positivity : (0 : ℝ) < 3628800 * (sh : ℝ) ^ 10)
      (eq_imp_le hr1 (by field_simp [hne]) (by
        field_simp [hne]
        ring)),
    le_of_mul_pos_le (by positivity : (0 : ℝ) < 479001600 * (sh : ℝ) ^ 12)
      (eq_imp_le hr2 (by
        field_simp [hne]
        ring) (by field_simp [hne])),
    le_of_mul_pos_le (by positivity : (0 : ℝ) < 39916800 * (sh : ℝ) ^ 11)
      (eq_imp_le hr3 (by field_simp [hne]) (by
        field_simp [hne]
        ring)),
    le_of_mul_pos_le (by positivity : (0 : ℝ) < 6227020800 * (sh : ℝ) ^ 13)
      (eq_imp_le hr4 (by
        field_simp [hne]
        ring) (by field_simp [hne]))⟩
theorem sign_div_pos_ite {z d : ℤ} (hd : (0 : ℝ) < (d : ℝ)) (x y : ℝ) : (if (0 : ℝ) ≤ (z : ℝ)
    / (d : ℝ) then ((z : ℝ) / (d : ℝ)) * x else ((z : ℝ) / (d : ℝ)) * y) =
    (if 0 ≤ z then (z : ℝ) * x else (z : ℝ) * y) / (d : ℝ) := by
  by_cases hz : 0 ≤ z
  · have hz0 : ((0 : ℤ) : ℝ) ≤ (z : ℝ) := Int.cast_le.mpr hz
    rw [Int.cast_zero] at hz0
    have hdiv : (0 : ℝ) ≤ (z : ℝ) / (d : ℝ) := div_nonneg hz0 hd.le
    rw [ite_eq_left hdiv, ite_eq_left hz, mul_div_right_comm]
  · have hlt : (z : ℝ) < 0 := Int.cast_lt_zero.mpr (lt_of_not_ge hz)
    have hdiv : ¬ ((0 : ℝ) ≤ (z : ℝ) / (d : ℝ)) := not_le.mpr (div_neg_of_neg_of_pos hlt hd)
    rw [ite_eq_right hdiv, ite_eq_right hz, mul_div_right_comm]
theorem comp_bounds_of_check {sh zr za zb wa wb kLo kHi e cLo cHi sLo sHi : ℤ}
    (hsh : (0 : ℝ) < (sh : ℝ)) (hzr : (0 : ℝ) < (zr : ℝ))
    (h : compCheck80 zr za zb wa wb kLo kHi e cLo cHi sLo sHi = true) : ((kLo : ℝ) / (sh : ℝ)
    ≤ (wb : ℝ) / (sh : ℝ) - ((if 0 ≤ (za : ℝ) / (zr : ℝ) then ((za : ℝ) / (zr : ℝ)) * ((cHi :
    ℝ) / (sh : ℝ)) else ((za : ℝ) / (zr : ℝ)) * ((cLo : ℝ) / (sh : ℝ))) + (if 0 ≤ (zb : ℝ) /
    (zr : ℝ) then ((zb : ℝ) / (zr : ℝ)) * ((sHi : ℝ) / (sh : ℝ)) else ((zb : ℝ) / (zr : ℝ)) *
    ((sLo : ℝ) / (sh : ℝ)))) / 2) ∧ ((wb : ℝ) / (sh : ℝ) - ((if 0 ≤ (za : ℝ) / (zr : ℝ) then
    ((za : ℝ) / (zr : ℝ)) * ((cLo : ℝ) / (sh : ℝ)) else ((za : ℝ) / (zr : ℝ)) * ((cHi : ℝ) /
    (sh : ℝ))) + (if 0 ≤ (zb : ℝ) / (zr : ℝ) then ((zb : ℝ) / (zr : ℝ)) * ((sLo : ℝ) / (sh :
    ℝ)) else ((zb : ℝ) / (zr : ℝ)) * ((sHi : ℝ) / (sh : ℝ)))) / 2 ≤ (kHi : ℝ) / (sh : ℝ)) ∧
    (-((e : ℝ) / (sh : ℝ)) ≤ (wa : ℝ) / (sh : ℝ) + (if 0 ≤ (kLo : ℝ) / (sh : ℝ) then ((kLo :
    ℝ) / (sh : ℝ)) * (0x16a09e667f3bcc908 / 2 ^ 64) else ((kLo : ℝ) / (sh : ℝ)) *
    (0x16a09e667f3bcc909 / 2 ^ 64))) ∧ ((wa : ℝ) / (sh : ℝ) + (if 0 ≤ (kHi : ℝ) / (sh : ℝ)
    then ((kHi : ℝ) / (sh : ℝ)) * (0x16a09e667f3bcc909 / 2 ^ 64) else ((kHi : ℝ) / (sh : ℝ)) *
    (0x16a09e667f3bcc908 / 2 ^ 64)) ≤ (e : ℝ) / (sh : ℝ)) := by
  unfold compCheck80 at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hk1, hk2⟩, he1⟩, he2⟩
  have hsh0 : (sh : ℝ) ≠ 0 := hsh.ne'
  have hzr0 : (zr : ℝ) ≠ 0 := hzr.ne'
  have hr1 := real_cast_le_of_decide hk1
  have hr2 := real_cast_le_of_decide hk2
  have hr3 := real_cast_le_of_decide he1
  have hr4 := real_cast_le_of_decide he2
  push_cast at hr1 hr2 hr3 hr4
  have hite (z x y : ℤ) : ((if 0 ≤ z then (z : ℝ) * ((x : ℝ) / (sh : ℝ))
      else (z : ℝ) * ((y : ℝ) / (sh : ℝ))) / (zr : ℝ)) * (2 * (zr : ℝ) * (sh : ℝ)) =
      2 * (if 0 ≤ z then (z : ℝ) * (x : ℝ) else (z : ℝ) * (y : ℝ)) := by
    by_cases hz : 0 ≤ z
    · simp only [hz, ↓reduceIte]
      field_simp [hsh0, hzr0]
    · simp only [hz, ↓reduceIte]
      field_simp [hsh0, hzr0]
  have hmul (w : ℤ) : ((w : ℝ) / (sh : ℝ)) * (2 * (zr : ℝ) * (sh : ℝ)) = 2 * (zr : ℝ) * (w : ℝ) :=
    by
    field_simp [hsh0]
  have h64 (k : ℤ) (c : ℝ) : ((wa : ℝ) / (sh : ℝ) + (k : ℝ) * (c / 2 ^ 64) / (sh : ℝ)) *
      ((sh : ℝ) * (2 : ℝ) ^ 64) = (wa : ℝ) * (2 : ℝ) ^ 64 + (k : ℝ) * c := by field_simp [hsh0]
  have he64 : ((e : ℝ) / (sh : ℝ)) * ((sh : ℝ) * (2 : ℝ) ^ 64) = (e : ℝ) * (2 : ℝ) ^ 64 := by
    field_simp [hsh0]
  have hne64 : (-((e : ℝ) / (sh : ℝ))) * ((sh : ℝ) * (2 : ℝ) ^ 64) = -(e : ℝ) * (2 : ℝ) ^ 64 := by
    field_simp [hsh0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sign_div_pos_ite hzr, sign_div_pos_ite hzr]
    refine le_of_mul_pos_le (by positivity : (0 : ℝ) < 2 * (zr : ℝ) * (sh : ℝ)) ?_
    linarith [hite za cHi cLo, hite zb sHi sLo, hmul wb, hmul kLo, hr1]
  · rw [sign_div_pos_ite hzr, sign_div_pos_ite hzr]
    refine le_of_mul_pos_le (by positivity : (0 : ℝ) < 2 * (zr : ℝ) * (sh : ℝ)) ?_
    linarith [hite za cLo cHi, hite zb sLo sHi, hmul wb, hmul kHi, hr2]
  · rw [sign_div_pos_ite hsh]
    refine le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) * (2 : ℝ) ^ 64) ?_
    by_cases hk : 0 ≤ kLo
    · simp only [hk, ↓reduceIte] at hr3 ⊢
      linarith [hne64, h64 kLo 0x16a09e667f3bcc908]
    · simp only [hk, ↓reduceIte] at hr3 ⊢
      linarith [hne64, h64 kLo 0x16a09e667f3bcc909]
  · rw [sign_div_pos_ite hsh]
    refine le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) * (2 : ℝ) ^ 64) ?_
    by_cases hk : 0 ≤ kHi
    · simp only [hk, ↓reduceIte] at hr4 ⊢
      linarith [he64, h64 kHi 0x16a09e667f3bcc909]
    · simp only [hk, ↓reduceIte] at hr4 ⊢
      linarith [he64, h64 kHi 0x16a09e667f3bcc908]
theorem sqrt_add_sqrt_le_of_int {sh e0r e0i e1r e1i mCap : ℤ} {bndNat : ℕ} (hsh : (0 : ℝ) < (sh :
    ℝ)) (hm0 : decide (0 ≤ mCap) = true) (hmB : decide (mCap * 1000000000000 ≤ (bndNat : ℤ) * sh) =
    true) (hsum :
    decide (e0r ^ 2 + e0i ^ 2 + (e1r ^ 2 + e1i ^ 2) ≤ mCap ^ 2) = true) (hprod : decide (4 *
      (e0r ^ 2 + e0i ^ 2) * (e1r ^ 2 + e1i ^ 2) ≤ (mCap ^ 2 - (e0r ^ 2 + e0i ^ 2) - (e1r ^ 2 +
      e1i ^ 2)) ^ 2) = true) :
    √(((e0r : ℝ) / (sh : ℝ)) ^ 2 + ((e0i : ℝ) / (sh : ℝ)) ^ 2) + √(((e1r : ℝ) / (sh : ℝ)) ^ 2 +
      ((e1i : ℝ) / (sh : ℝ)) ^ 2) ≤ (bndNat : ℝ) / 1000000000000 := by
  have hsh0 : (sh : ℝ) ≠ 0 := hsh.ne'
  have hr0 := real_cast_le_of_decide hm0
  have hrB := real_cast_le_of_decide hmB
  have hrs := real_cast_le_of_decide hsum
  have hrp := real_cast_le_of_decide hprod
  push_cast at hr0 hrB hrs hrp
  set a : ℝ := ((e0r : ℝ) / (sh : ℝ)) ^ 2 + ((e0i : ℝ) / (sh : ℝ)) ^ 2
  set c : ℝ := ((e1r : ℝ) / (sh : ℝ)) ^ 2 + ((e1i : ℝ) / (sh : ℝ)) ^ 2
  set m : ℝ := (mCap : ℝ) / (sh : ℝ)
  have ha0 : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hm_nonneg : 0 ≤ m := div_nonneg hr0 hsh.le
  have hac_le : a + c ≤ m ^ 2 :=
    le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) ^ 2) (eq_imp_le hrs (by
      dsimp only [a, c]
      field_simp [hsh0]) (by
      dsimp only [m]
      field_simp [hsh0]))
  have h4ac_le : 4 * a * c ≤ (m ^ 2 - a - c) ^ 2 :=
    le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) ^ 4) (eq_imp_le hrp (by
      dsimp only [a, c]
      field_simp [hsh0]) (by
      dsimp only [a, c, m]
      field_simp [hsh0]))
  have hcross : 2 * (√a * √c) ≤ m ^ 2 - a - c := by
    nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt hc0, h4ac_le, mul_nonneg (Real.sqrt_nonneg a)
      (Real.sqrt_nonneg c), hac_le]
  have hsum_le_m : √a + √c ≤ m := by
    nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt hc0, hcross, hm_nonneg, Real.sqrt_nonneg a,
      Real.sqrt_nonneg c]
  have hm_le_bnd : m ≤ (bndNat : ℝ) / 1000000000000 :=
    le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) * 1000000000000) (eq_imp_le hrB (by
      dsimp only [m]
      field_simp [hsh0]) (by ring))
  exact hsum_le_m.trans hm_le_bnd
theorem wire_err_le_ultra_of_check {idx : ℕ} (h3 : 3 ≤ idx) (h31 : idx < 31) (hchk : checkWireUltra
    idx = true) : ‖(wordMatrix2 (catPrepWordUltra idx) - zCatBitUltra idx • (idealPhaseGradDiagBit
    idx *
    Qubit.H).1) * p0Mat2‖ ≤ (wireBoundUltraN12 idx : ℝ) / 1000000000000 := by
  unfold checkWireUltra at hchk
  dsimp only [] at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hzr_b, hm_b⟩, ht0_b⟩, htl_b⟩, hth_b⟩, hcs_b⟩,
    hc0r_b⟩, hc0i_b⟩, hc1r_b⟩, hc1i_b⟩, hm0_b⟩, hmB_b⟩, hsum_b⟩, hprod_b⟩
  set sh : ℤ := (2 : ℤ) ^ 80
  set m := evalList (catPrepWordUltra idx) matId
  set zp := (zCatPythUltra idx).1
  set zq := (zCatPythUltra idx).2.1
  set zr := (zCatPythUltra idx).2.2
  have hsh : (0 : ℝ) < (sh : ℝ) := real_cast_pos_of_decide (by decide)
  have hzr : (0 : ℝ) < (zr : ℝ) := real_cast_pos_of_decide hzr_b
  rcases mat2Zw_col0_of_check m hm_b with ⟨hm0r, hm0i, hm1r, hm1i⟩
  rcases cos_sin_poly_of_check hsh hcs_b with ⟨hclo, hchi, hslo, hshi⟩
  rcases comp_bounds_of_check (sh := sh) hsh hzr hc0r_b with ⟨hk0r_lo, hk0r_hi, he0r_lo, he0r_hi⟩
  rcases comp_bounds_of_check (sh := sh) hsh hzr hc0i_b with ⟨hk0i_lo, hk0i_hi, he0i_lo, he0i_hi⟩
  rcases comp_bounds_of_check (sh := sh) hsh hzr hc1r_b with ⟨hk1r_lo, hk1r_hi, he1r_lo, he1r_hi⟩
  rcases comp_bounds_of_check (sh := sh) hsh hzr hc1i_b with ⟨hk1i_lo, hk1i_hi, he1i_lo, he1i_hi⟩
  rw [Int.cast_neg, neg_div] at hk0r_lo hk0r_hi hk1i_lo hk1i_hi
  have hz : zCatBitUltra idx = pythPhase zp zq zr := by
    unfold zCatBitUltra
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h31]
  have ht0 : (0 : ℝ) ≤ ((zFloorDiv (0x3243f6a8885a308d2 * sh) ((2 : ℤ) ^ (64 + idx + 1)) : ℤ) : ℝ) /
      (sh : ℝ) := by
    have h0z := real_cast_le_of_decide ht0_b
    push_cast at h0z
    exact div_nonneg h0z hsh.le
  have hang_eq (z : ℤ) (c : ℝ) :
      ((z : ℝ) / (sh : ℝ)) * ((sh : ℝ) * (2 : ℝ) ^ (64 + idx + 1)) = (z : ℝ) * (2 : ℝ) ^ (64 + idx +
        1) ∧
      (c / 2 ^ 64 / (2 : ℝ) ^ (idx + 1)) * ((sh : ℝ) * (2 : ℝ) ^ (64 + idx + 1)) = c * (sh : ℝ) :=
        by
    refine ⟨by rw [← mul_assoc, div_mul_cancel₀ _ hsh.ne'], ?_⟩
    have hp : (2 : ℝ) ^ 64 * (2 : ℝ) ^ (idx + 1) ≠ 0 := by positivity
    rw [show (2 : ℝ) ^ (64 + idx + 1) = (2 : ℝ) ^ 64 * (2 : ℝ) ^ (idx + 1) by
      rw [Nat.add_assoc, pow_add],
      div_div, mul_comm (sh : ℝ), ← mul_assoc, div_mul_cancel₀ _ hp]
  have htl : ((zFloorDiv (0x3243f6a8885a308d2 * sh) ((2 : ℤ) ^ (64 + idx + 1)) : ℤ) : ℝ) /
      (sh : ℝ) ≤ (0x3243f6a8885a308d2 : ℝ) / 2 ^ 64 / (2 : ℝ) ^ (idx + 1) := by
    have hr : (((zFloorDiv (0x3243f6a8885a308d2 * sh) ((2 : ℤ) ^ (64 + idx + 1)) *
        (2 : ℤ) ^ (64 + idx + 1) : ℤ) : ℝ)) ≤ ((0x3243f6a8885a308d2 * sh : ℤ) : ℝ) :=
      real_cast_le_of_decide htl_b
    push_cast at hr
    refine le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) * (2 : ℝ) ^ (64 + idx + 1)) ?_
    rw [(hang_eq (zFloorDiv (0x3243f6a8885a308d2 * sh) ((2 : ℤ) ^ (64 + idx +
      1))) (0x3243f6a8885a308d2 : ℝ)).1,
      (hang_eq (zFloorDiv (0x3243f6a8885a308d2 * sh) ((2 : ℤ) ^ (64 + idx +
        1))) (0x3243f6a8885a308d2 : ℝ)).2]
    linarith
  have hth : (0x3243f6a8885a308d4 : ℝ) / 2 ^ 64 / (2 : ℝ) ^ (idx + 1) ≤
      ((zCeilDiv (0x3243f6a8885a308d4 * sh) ((2 : ℤ) ^ (64 + idx + 1)) : ℤ) : ℝ) / (sh : ℝ) := by
    have hr : ((0x3243f6a8885a308d4 * sh : ℤ) : ℝ) ≤ (((zCeilDiv (0x3243f6a8885a308d4 * sh)
        ((2 : ℤ) ^ (64 + idx + 1)) * (2 : ℤ) ^ (64 + idx + 1) : ℤ) : ℝ)) :=
      real_cast_le_of_decide hth_b
    push_cast at hr
    refine le_of_mul_pos_le (by positivity : (0 : ℝ) < (sh : ℝ) * (2 : ℝ) ^ (64 + idx + 1)) ?_
    rw [(hang_eq (zCeilDiv (0x3243f6a8885a308d4 * sh) ((2 : ℤ) ^ (64 + idx +
      1))) (0x3243f6a8885a308d4 : ℝ)).2,
      (hang_eq (zCeilDiv (0x3243f6a8885a308d4 * sh) ((2 : ℤ) ^ (64 + idx + 1))) (0x3243f6a8885a308d4
        : ℝ)).1]
    linarith
  have hsh_eq : (sh : ℝ) = (2 : ℝ) ^ 80 := by norm_num [sh]
  rw [← hsh_eq] at hm0r hm0i hm1r hm1i
  have hbnd := sqrt_add_sqrt_le_of_int hsh hm0_b hmB_b hsum_b hprod_b
  exact certify_wire_col0_ultra (by omega : 2 ≤ idx)
    (rfl : evalList (catPrepWordUltra idx) matId = m) hz hm0r hm0i hm1r hm1i ht0 htl hth hclo
    hchi hslo hshi hk0r_lo hk0r_hi he0r_lo he0r_hi hk0i_lo hk0i_hi he0i_lo he0i_hi hk1r_lo
    hk1r_hi he1r_lo he1r_hi hk1i_lo hk1i_hi he1i_lo he1i_hi (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)).ge (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity)).ge
    hbnd
theorem checkWireUltra_all : (List.range' 3 28).all checkWireUltra = true := by decide +kernel
theorem wire_err_le_ultra_head {idx : ℕ} (h : idx < 31) : ‖(wordMatrix2 (catPrepWordUltra idx) -
    zCatBitUltra idx • (idealPhaseGradDiagBit idx * Qubit.H).1) * p0Mat2‖ ≤ (wireBoundUltraN12 idx :
    ℝ) /
    1000000000000 := by
  match idx with
  | 0 =>
    rw [wire_err_zero_ultra_0]
    simp [wireBoundUltraN12]
  | 1 =>
    rw [wire_err_zero_ultra_1]
    simp [wireBoundUltraN12]
  | 2 =>
    rw [wire_err_zero_ultra_2]
    simp [wireBoundUltraN12]
  | k + 3 =>
    have hmem : k + 3 ∈ List.range' 3 28 := List.mem_range'.mpr ⟨k, by omega, by omega⟩
    exact wire_err_le_ultra_of_check (by omega) h
      (List.all_eq_true.mp checkWireUltra_all (k + 3) hmem)
theorem geom_half_tail31_sum_le (B_tot : ℕ) : (∑ i : Fin B_tot, if 31 ≤ i.val then (1 / 2 : ℝ)
    ^ (i.val + 1) else 0) ≤ (1 / 2 : ℝ) ^ 31 := by
  have hexact : ∀ m : ℕ, (∑ i : Fin m, if 31 ≤ i.val then (1 / 2 : ℝ) ^ (i.val + 1) else 0) =
      (1 / 2 : ℝ) ^ 31 - (if 31 ≤ m then (1 / 2 : ℝ) ^ m else (1 / 2 : ℝ) ^ 31) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      by_cases hm31 : 31 ≤ m
      · have hm32 : 31 ≤ m + 1 := by omega
        simp only [hm31, hm32, ↓reduceIte]
        rw [pow_succ]; ring
      · by_cases hm30 : m = 30
        · subst hm30; norm_num
        · have hm32 : ¬ (31 ≤ m + 1) := by omega
          simp only [hm31, hm32, ↓reduceIte]; ring
  rw [hexact B_tot]
  by_cases hB : 31 ≤ B_tot
  · simp only [hB, ↓reduceIte]
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ B_tot := by positivity
    linarith
  · simp only [hB, ↓reduceIte]; linarith
/-- Ultra-tight 1-qubit `{H, S, T}` single-catalyst preparation error cap (`23 / 10^10`
= `2.3` nHa one-way, `4.6` nHa round-trip `≤ 5 / 10^9 ≤ 500 / 10^9`). -/
noncomputable def catPrepErrUltra1q : ℝ := (23 : ℝ) / 10000000000
theorem catPrepErrUltra1q_nonneg : 0 ≤ catPrepErrUltra1q := by
  unfold catPrepErrUltra1q; norm_num
theorem sum_wire_err_le_catPrepErrUltra1q (B_tot : ℕ) : (∑ i : Fin B_tot, ‖(wordMatrix2
    (catPrepWordUltra i.val) - zCatBitUltra i.val • (idealPhaseGradDiagBit i.val * Qubit.H).1) *
    p0Mat2‖) ≤ catPrepErrUltra1q
    := by
  have hpoint (i : Fin B_tot) : ‖(wordMatrix2 (catPrepWordUltra i.val) - zCatBitUltra i.val •
      (idealPhaseGradDiagBit i.val * Qubit.H).1) * p0Mat2‖ ≤ (wireBoundUltraN12 i.val : ℝ) /
      1000000000000 + (if 31 ≤ i.val then (4442885 / 1000000 : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)
      else 0) := by
    by_cases h31 : 31 ≤ i.val
    · simp only [h31, ↓reduceIte]
      have h0 : (0 : ℝ) ≤ (wireBoundUltraN12 i.val : ℝ) / 1000000000000 := by positivity
      linarith [wire_err_le_ultra_tail h31]
    · simp only [h31, ↓reduceIte, add_zero]
      exact wire_err_le_ultra_head (Nat.lt_of_not_le h31)
  refine (Finset.sum_le_sum (fun i _ ↦ hpoint i)).trans ?_
  rw [Finset.sum_add_distrib]
  have hhead : (∑ i : Fin B_tot, (wireBoundUltraN12 i.val : ℝ) / 1000000000000) ≤
      (103 : ℝ) / 1000000000000 := by
    have hnat : (∑ i : Fin B_tot, wireBoundUltraN12 i.val) ≤ 103 := by
      refine (sum_fin_le_sum_fin31_of_zero_ge31 wireBoundUltraN12 ?_ B_tot).trans ?_
      · intro k hk
        match k with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => omega
        | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => omega
        | _ + 31 => rfl
      · rw [← List.sum_ofFn]; decide +kernel
    calc (∑ i : Fin B_tot, (wireBoundUltraN12 i.val : ℝ) / 1000000000000)
      _ = ((∑ i : Fin B_tot, wireBoundUltraN12 i.val : ℕ) : ℝ) / 1000000000000 := by
          push_cast; rw [Finset.sum_div]
      _ ≤ (103 : ℝ) / 1000000000000 :=
          div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by norm_num)
  have htail : (∑ i : Fin B_tot, (if 31 ≤ i.val then (4442885 / 1000000 : ℝ) * (1 / 2 : ℝ) ^
      (i.val + 1) else 0)) ≤ (4442885 / 1000000 : ℝ) * (1 / 2 : ℝ) ^ 31 := by
    have hpull : (∑ i : Fin B_tot, (if 31 ≤ i.val then (4442885 / 1000000 : ℝ) * (1 / 2 : ℝ) ^
        (i.val + 1) else 0)) = (4442885 / 1000000 : ℝ) * (∑ i : Fin B_tot, if 31 ≤ i.val then
        (1 / 2 : ℝ) ^ (i.val + 1) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; split_ifs <;> ring
    rw [hpull]
    exact mul_le_mul_of_nonneg_left (geom_half_tail31_sum_le B_tot) (by norm_num)
  refine (add_le_add hhead htail).trans ?_
  unfold catPrepErrUltra1q; norm_num
theorem cCatPrepUltra1qGen_approx (B_tot : ℕ) : ‖((cCatPrepUltra1qGen B_tot).eval.1 -
    zCatGlobalUltra B_tot • (U_cat_B_prep B_tot).1) * (QRegister.whole B_tot).basisOutcomeProjector
    0‖ ≤ catPrepErrUltra1q := by
  let idB : QRegister B_tot B_tot := QRegister.whole B_tot
  let W : Fin B_tot → Operator (2 ^ B_tot) := fun i ↦
    (QRegister.singleton i.rev).embedMatrix (wordMatrix2 (catPrepWordUltra i.val))
  let U : Fin B_tot → Operator (2 ^ B_tot) := fun i ↦ (QRegister.singleton i.rev).embedMatrix
      (zCatBitUltra i.val • (idealPhaseGradDiagBit i.val * Qubit.H).1)
  let P : Fin B_tot → Operator (2 ^ B_tot) := fun i ↦
    (QRegister.singleton i.rev).basisOutcomeProjector 0
  have hW_eq : (cCatPrepUltra1qGen B_tot).eval.1 = seqProd W := by
    rw [cCatPrepUltra1qGen, eval_sequence_ofFn_eq_seqProd, seqProd_coe_unitary]
    congr 1; funext i
    exact hstWordCircuit_eval_eq_embedMatrix (catPrepWordUltra i.val) i.rev
  have hU_eq : zCatGlobalUltra B_tot • (U_cat_B_prep B_tot).1 = seqProd U := by
    unfold U_cat_B_prep zCatGlobalUltra
    rw [seqProd_coe_unitary, ← seqProd_smul]
    congr 1; funext i
    rw [Circuit.eval_single, PrimitiveGate.eval, ← QRegister.embedUnitary_mul,
      QRegister.embedUnitary_val, ← QRegister.embedMatrix_smul]
  have hW_norm (i : Fin B_tot) : ‖W i‖ ≤ 1 := by
    have hev : W i = ((hstWordCircuit (catPrepWordUltra i.val) i.rev).eval).1 :=
      (hstWordCircuit_eval_eq_embedMatrix (catPrepWordUltra i.val) i.rev).symm
    rw [hev]
    exact BridgeDuhamel.norm_of_mem_unitaryGroup_le_one
      ((hstWordCircuit (catPrepWordUltra i.val) i.rev).eval).2
  have hU_norm (i : Fin B_tot) : ‖U i‖ ≤ 1 := by
    let u2 : Unitary 2 := ⟨zCatBitUltra i.val • (idealPhaseGradDiagBit i.val * Qubit.H).1,
      smul_mem_unitaryGroup_of_norm_eq_one (norm_zCatBitUltra i.val)
        (idealPhaseGradDiagBit i.val * Qubit.H).2⟩
    have hu : U i = ((QRegister.singleton i.rev).embedUnitary u2).1 := rfl
    rw [hu]
    exact BridgeDuhamel.norm_of_mem_unitaryGroup_le_one
      ((QRegister.singleton i.rev).embedUnitary u2).2
  have hP_norm (i : Fin B_tot) : ‖P i‖ ≤ 1 := BridgeDuhamel.norm_basisOutcomeProjector_le_one _ 0
  have hDisj (i j : Fin B_tot) (hij : i ≠ j) :
      (QRegister.singleton i.rev).DisjointWires (QRegister.singleton j.rev) := by
    rw [QRegister.disjoint_iff]; intro a b; fin_cases a; fin_cases b
    exact fun h ↦ hij (by simpa using congrArg Fin.rev h)
  have hCW (i j : Fin B_tot) (hij : i ≠ j) : W i * P j = P j * W i :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ (hDisj i j hij) _ 0
  have hCU (i j : Fin B_tot) (hij : i ≠ j) : U i * P j = P j * U i :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ (hDisj i j hij) _ 0
  have hAbs : seqProd P * idB.basisOutcomeProjector 0 = idB.basisOutcomeProjector 0 := by
    apply seqProd_mul_absorb
    intro i
    have hcomp : idB.compose (QRegister.singleton i.rev) = QRegister.singleton i.rev := by
      ext a; rfl
    simpa [P, hcomp] using
      TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul idB (QRegister.singleton i.rev)
  rw [hW_eq, hU_eq, ← hAbs, ← Matrix.mul_assoc]
  refine (norm_mul_le _ _).trans ?_
  have hIdNorm : ‖idB.basisOutcomeProjector 0‖ ≤ 1 :=
    BridgeDuhamel.norm_basisOutcomeProjector_le_one idB 0
  refine (mul_le_mul_of_nonneg_left hIdNorm (norm_nonneg _)).trans ?_
  rw [mul_one]
  refine (norm_seqProd_sub_mul_seqProd_proj_le W U P hW_norm hU_norm hP_norm hCW hCU).trans ?_
  refine (Finset.sum_le_sum (fun i _ ↦ ?_)).trans (sum_wire_err_le_catPrepErrUltra1q B_tot)
  have hFactor : (W i - U i) * P i = (QRegister.singleton i.rev).embedMatrix ((wordMatrix2
      (catPrepWordUltra i.val) - zCatBitUltra i.val • (idealPhaseGradDiagBit i.val *
      Qubit.H).1) * p0Mat2) := by
    dsimp only [W, U, P]
    rw [← singleton_embed_p0Mat2 i.rev, ← BridgeDuhamel.embedMatrix_sub,
      ← QRegister.embedMatrix_mul]
  rw [hFactor]
  exact BridgeDuhamel.norm_embedMatrix_le (QRegister.singleton i.rev) _
/-- General `B_tot`-wire round-trip T-count of `cCatPrepUltra1qGen`. -/
abbrev cInitUltraSingleCat_T_gen (B_tot : ℕ) : ℕ :=
  2 * (cCatPrepUltra1qGen B_tot).count PrimitiveGate.T
/-- Concrete 48-wire round-trip T-count (`2 * 3650 = 7300`) of `cInitUltraSingleCat`. -/
abbrev cInitUltraSingleCat_T : ℕ := 7300
/-- Ideal phase-matched `B_tot`-wire catalyst preparation unitary for `zCatGlobalUltra`. -/
noncomputable def uCat1qUltraIdeal (B_tot : ℕ) : Unitary (2 ^ B_tot) :=
  ⟨zCatGlobalUltra B_tot • (U_cat_B_prep B_tot).1,
    smul_mem_unitaryGroup_of_norm_eq_one (norm_zCatGlobalUltra B_tot) (U_cat_B_prep B_tot).2⟩
/-- Embedded ideal phase-matched catalyst preparation unitary on `kActSingleCatClosure`. -/
noncomputable def uCatPrepUltraSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  (rCatTotInSingleCat mPayload B_tot kWorkConst).embedUnitary (uCat1qUltraIdeal B_tot)
theorem uCatPrepUltraSingleCat_eq_smul_norm (mPayload B_tot kWorkConst : ℕ) :
    (uCatPrepUltraSingleCat mPayload B_tot kWorkConst).1 = (zCatGlobalUltra B_tot *
    phaseGradGlobalPhase B_tot) • (uCatNormSingleCat
    mPayload B_tot kWorkConst).1 := by
  have hNormVal : (U_cat_B_normalized B_tot).1 =
      star (phaseGradGlobalPhase B_tot) • (U_cat_B_prep B_tot).1 := rfl
  have hIdealVal : (uCat1qUltraIdeal B_tot).1 =
      zCatGlobalUltra B_tot • (U_cat_B_prep B_tot).1 := rfl
  have hPh : phaseGradGlobalPhase B_tot * star (phaseGradGlobalPhase B_tot) = 1 := by
    have hn := norm_phaseGradGlobalPhase B_tot
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
      Complex.ofReal_one]
  unfold uCatPrepUltraSingleCat uCatNormSingleCat
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, hNormVal, hIdealVal,
    QRegister.embedMatrix_smul, QRegister.embedMatrix_smul, smul_smul, mul_assoc, hPh, mul_one]
/-- Active-register 1-qubit `{H, S, T}` ultra catalyst preparation circuit (`0` `.TOFF`). -/
def cInitUltraSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Circuit (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  Circuit.onRegister (rCatTotInSingleCat mPayload B_tot kWorkConst) (cCatPrepUltra1qGen B_tot)
/-- Synthesized ultra single-catalyst forward preparation unitary on `kActSingleCatClosure`. -/
noncomputable def vPrepUltraSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  (cInitUltraSingleCat mPayload B_tot kWorkConst).eval
/-- Synthesized ultra single-catalyst inverse teardown unitary on `kActSingleCatClosure`. -/
noncomputable def vInvUltraSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  ((cInitUltraSingleCat mPayload B_tot kWorkConst).eval)⁻¹
theorem vInvUltraSingleCat_mul_vPrepUltraSingleCat (mPayload B_tot kWorkConst : ℕ) :
    vInvUltraSingleCat mPayload B_tot kWorkConst * vPrepUltraSingleCat mPayload B_tot
    kWorkConst = 1 := inv_mul_cancel _
theorem vInvUltraSingleCat_mul_vPrepUltraSingleCat_val (mPayload B_tot kWorkConst : ℕ) :
    (vInvUltraSingleCat mPayload B_tot kWorkConst).1 * (vPrepUltraSingleCat mPayload B_tot
    kWorkConst).1 = 1 := by
  rw [← Submonoid.coe_mul, vInvUltraSingleCat_mul_vPrepUltraSingleCat, OneMemClass.coe_one]
/-- Dynamic single-catalyst preparation circuit (`0` `.TOFF`) matching `mkInitSingleCatDyn`. -/
noncomputable def mkInitUltraSingleCatDyn {Var : Type}
    {mPayload B_tot kWorkConst mWork n : ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister
    (kActSingleCatClosure mPayload B_tot kWorkConst) n) (rWork : QRegister mWork n)
    (_hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n := substActiveSingleCat
    (Nat.le_trans (by decide : 1 ≤ 28) hm28) v rAct rWork
    (cInitUltraSingleCat mPayload B_tot kWorkConst)
/-- Dynamic single-catalyst teardown circuit (`0` `.TOFF`) matching `mkUninitSingleCatDyn`. -/
noncomputable def mkUninitUltraSingleCatDyn {Var : Type}
    {mPayload B_tot kWorkConst mWork n : ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister
    (kActSingleCatClosure mPayload B_tot kWorkConst) n) (rWork : QRegister mWork n)
    (_hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n := substActiveSingleCat
    (Nat.le_trans (by decide : 1 ≤ 28) hm28) v rAct rWork
    (cInitUltraSingleCat mPayload B_tot kWorkConst).inverse
@[simp] theorem count_toff_mkInitUltraSingleCatDyn {Var : Type}
    {mPayload B_tot kWorkConst mWork n : ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister
    (kActSingleCatClosure mPayload B_tot kWorkConst) n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (mkInitUltraSingleCatDyn hm28 v rAct rWork hDisj).count PrimitiveGate.TOFF = 0 :=
    substActiveSingleCat_count_TOFF _ _ _ _ _
@[simp] theorem count_toff_mkUninitUltraSingleCatDyn {Var : Type}
    {mPayload B_tot kWorkConst mWork n : ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister
    (kActSingleCatClosure mPayload B_tot kWorkConst) n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (mkUninitUltraSingleCatDyn hm28 v rAct rWork hDisj).count PrimitiveGate.TOFF = 0 :=
    substActiveSingleCat_count_TOFF _ _ _ _ _
theorem count_t_mkInitUltraSingleCat_add_uninit_gen_le {Var : Type} {mPayload B_tot kWorkConst mWork
    n : ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister (kActSingleCatClosure mPayload B_tot
    kWorkConst)
    n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : (mkInitUltraSingleCatDyn
      hm28 v rAct rWork hDisj).count PrimitiveGate.T + (mkUninitUltraSingleCatDyn hm28 v rAct rWork
    hDisj).count PrimitiveGate.T ≤ cInitUltraSingleCat_T_gen B_tot := by
  unfold mkInitUltraSingleCatDyn mkUninitUltraSingleCatDyn
  refine (Nat.add_le_add (substActiveSingleCat_count_T_le _ _ _ _ _)
    (substActiveSingleCat_count_T_le _ _ _ _ _)).trans ?_
  rw [Circuit.count_inverse_of_ne PrimitiveGate.T (by decide) (by decide),
    Circuit.count_inverse_of_ne PrimitiveGate.TOFF (by decide) (by decide)]
  simp only [cInitUltraSingleCat, Circuit.count_onRegister, count_toff_cCatPrepUltra1qGen,
    cInitUltraSingleCat_T_gen]
  omega
theorem count_t_mkInitUltraSingleCat_add_uninit_le {Var : Type} {mPayload B_tot kWorkConst mWork n :
    ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister (kActSingleCatClosure mPayload B_tot
    kWorkConst) n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : (mkInitUltraSingleCatDyn hm28 v
      rAct rWork hDisj).count PrimitiveGate.T + (mkUninitUltraSingleCatDyn hm28 v rAct rWork
      hDisj).count
    PrimitiveGate.T ≤ cInitUltraSingleCat_T := by
  refine (count_t_mkInitUltraSingleCat_add_uninit_gen_le hm28 v rAct rWork hDisj).trans ?_
  have h := count_t_cCatPrepUltra1qGen_le B_tot
  dsimp [cInitUltraSingleCat_T_gen, cInitUltraSingleCat_T]
  omega
theorem realizesCleanWorkspace_mkInitUltraSingleCatDyn {Var : Type} [Fintype Var]
    [DecidableEq Var] {mPayload B_tot kWorkConst mWork n : ℕ} (hm28 : 28 ≤ mWork) (v : Var)
    (rAct : QRegister (kActSingleCatClosure mPayload B_tot kWorkConst) n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
    (vPrepUltraSingleCat mPayload B_tot kWorkConst)
    (mkInitUltraSingleCatDyn hm28 v rAct rWork hDisj) :=
    realizesCleanWorkspace_substActiveSingleCat (Nat.le_trans (by decide : 1 ≤ 28) hm28) v
    rAct rWork hDisj (cInitUltraSingleCat mPayload B_tot kWorkConst)
theorem realizesCleanWorkspace_mkUninitUltraSingleCatDyn {Var : Type} [Fintype Var] [DecidableEq
    Var] {mPayload B_tot kWorkConst mWork n : ℕ} (hm28 : 28 ≤ mWork) (v : Var) (rAct : QRegister
    (kActSingleCatClosure mPayload B_tot kWorkConst) n) (rWork : QRegister mWork n) (hDisj :
      rAct.DisjointWires rWork) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (vInvUltraSingleCat
    mPayload B_tot kWorkConst) (mkUninitUltraSingleCatDyn hm28 v rAct rWork hDisj) := by
  unfold mkUninitUltraSingleCatDyn vInvUltraSingleCat
  rw [← Circuit.eval_inverse]
  exact realizesCleanWorkspace_substActiveSingleCat (Nat.le_trans (by decide : 1 ≤ 28) hm28) v
    rAct rWork hDisj (cInitUltraSingleCat mPayload B_tot kWorkConst).inverse
theorem norm_vPrepUltraSingleCat_sub_le_catPrepErrUltra1q (mPayload B_tot kWorkConst : ℕ) :
    ‖((vPrepUltraSingleCat mPayload B_tot kWorkConst).1 - (uCatPrepUltraSingleCat mPayload B_tot
    kWorkConst).1) *
    pCat0SingleCat mPayload B_tot kWorkConst‖ ≤ catPrepErrUltra1q := by
  let rCat := rCatTotInSingleCat mPayload B_tot kWorkConst
  have hCompId : rCat.compose (QRegister.whole B_tot) = rCat :=
    QRegister.ext (Function.Embedding.ext fun _ ↦ rfl)
  have hAbs : rCat.basisOutcomeProjector 0 * pCat0SingleCat mPayload B_tot kWorkConst =
      pCat0SingleCat mPayload B_tot kWorkConst :=
      TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) (inCatTotSingleCat B_tot kWorkConst)
  have hV : (vPrepUltraSingleCat mPayload B_tot kWorkConst).1 =
      rCat.embedMatrix (cCatPrepUltra1qGen B_tot).eval.1 := by
    dsimp only [vPrepUltraSingleCat, cInitUltraSingleCat, rCat]
    rw [Circuit.eval_onRegister, QRegister.embedUnitary_val]
  have hU : (uCatPrepUltraSingleCat mPayload B_tot kWorkConst).1 =
      rCat.embedMatrix (zCatGlobalUltra B_tot • (U_cat_B_prep B_tot).1) := rfl
  have hP : rCat.embedMatrix ((QRegister.whole B_tot).basisOutcomeProjector 0) =
      rCat.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hCompId,
      ← QRegister.basisOutcomeProjector]
  have hProd : ((vPrepUltraSingleCat mPayload B_tot kWorkConst).1 - (uCatPrepUltraSingleCat
      mPayload B_tot kWorkConst).1) * pCat0SingleCat mPayload B_tot kWorkConst =
      rCat.embedMatrix (((cCatPrepUltra1qGen B_tot).eval.1 - zCatGlobalUltra B_tot •
      (U_cat_B_prep B_tot).1) * (QRegister.whole B_tot).basisOutcomeProjector 0) *
      pCat0SingleCat mPayload B_tot kWorkConst := by
    rw [rCat.embedMatrix_mul, BridgeDuhamel.embedMatrix_sub, ← hV, ← hU, hP, Matrix.mul_assoc, hAbs]
  rw [hProd]
  refine (norm_mul_le _ _).trans ((mul_le_mul (BridgeDuhamel.norm_embedMatrix_le rCat _)
    (BridgeDuhamel.norm_basisOutcomeProjector_le_one _ 0) (norm_nonneg _) (norm_nonneg
    _)).trans ?_)
  rw [mul_one]
  exact cCatPrepUltra1qGen_approx B_tot
theorem norm_vPrepUltraSingleCat_anc_sub_le_catPrepErrUltra1q (mPayload B_tot kWorkConst : ℕ) :
    let anc : QRegister (mActSingleCatClosure mPayload B_tot kWorkConst)
        (systemQubits + mActSingleCatClosure mPayload B_tot kWorkConst) :=
      .block systemQubits (mActSingleCatClosure mPayload B_tot kWorkConst) le_rfl
    ‖((vPrepUltraSingleCat mPayload B_tot kWorkConst).1 -
        (uCatPrepUltraSingleCat mPayload B_tot kWorkConst).1) *
      anc.basisOutcomeProjector 0‖ ≤ catPrepErrUltra1q := by
  dsimp only
  let anc := rAncInSingleCat mPayload B_tot kWorkConst
  have hAbs : pCat0SingleCat mPayload B_tot kWorkConst * anc.basisOutcomeProjector 0 =
      anc.basisOutcomeProjector 0 := TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul
      anc (inCatScratchSingleCat mPayload B_tot kWorkConst)
  change ‖((vPrepUltraSingleCat mPayload B_tot kWorkConst).1 - (uCatPrepUltraSingleCat
    mPayload B_tot kWorkConst).1) * anc.basisOutcomeProjector 0‖ ≤ catPrepErrUltra1q
  rw [← hAbs, ← Matrix.mul_assoc]
  refine (norm_mul_le _ _).trans ((mul_le_mul
    (norm_vPrepUltraSingleCat_sub_le_catPrepErrUltra1q mPayload B_tot kWorkConst)
    (BridgeDuhamel.norm_basisOutcomeProjector_le_one anc 0) (norm_nonneg _)
    catPrepErrUltra1q_nonneg).trans ?_)
  rw [mul_one]
theorem catalyst_sandwich_ultra_singleCat {mPayload B_tot kWorkConst : ℕ}
    (A P : Operator (2 ^ systemQubits)) (t ε_evol : ℝ) (R_j : ℕ) (W_seg W_eff : Unitary (2 ^
    (kActSingleCatClosure mPayload B_tot kWorkConst))) (hAHerm : A.IsHermitian)
    (hPHerm : P.IsHermitian) (hPIdem : P * P = P) (hInter : W_seg.1 * (uCatNormSingleCat
    mPayload B_tot kWorkConst).1 * pCat0SingleCat mPayload B_tot kWorkConst =
    (uCatNormSingleCat mPayload B_tot kWorkConst).1 * W_eff.1 * pCat0SingleCat mPayload B_tot
    kWorkConst) (hCommCat : W_eff.1 * pCat0SingleCat mPayload B_tot kWorkConst =
    pCat0SingleCat mPayload B_tot kWorkConst * W_eff.1)
    (hPow : ApproximatesTimeEvolution A t ε_evol P (W_eff ^ R_j)) : ApproximatesTimeEvolution
    A t (ε_evol + 2 * catPrepErrUltra1q) P (unitarySandwichPow (vInvUltraSingleCat mPayload
    B_tot kWorkConst) W_seg (vPrepUltraSingleCat mPayload B_tot kWorkConst) R_j) :=
    catalyst_sandwich_of_smul_norm A P t ε_evol catPrepErrUltra1q R_j
    (zCatGlobalUltra B_tot * phaseGradGlobalPhase B_tot)
    (vInvUltraSingleCat mPayload B_tot kWorkConst)
    (vPrepUltraSingleCat mPayload B_tot kWorkConst)
    (uCatPrepUltraSingleCat mPayload B_tot kWorkConst)
    (uCatNormSingleCat mPayload B_tot kWorkConst) W_seg W_eff
    (pCat0SingleCat mPayload B_tot kWorkConst) (vInvUltraSingleCat_mul_vPrepUltraSingleCat_val
    mPayload B_tot kWorkConst) hAHerm hPHerm hPIdem (singleCat_pCat0_pin P)
    (uCatPrepUltraSingleCat_eq_smul_norm mPayload B_tot kWorkConst) hInter hCommCat
    (norm_vPrepUltraSingleCat_anc_sub_le_catPrepErrUltra1q mPayload B_tot kWorkConst) hPow
end GqspCatPrepSub600Nano
end
end GqspCatPrepSub600Nano

end QuantumComputation.Specs.StoppingPowerSolution
end
