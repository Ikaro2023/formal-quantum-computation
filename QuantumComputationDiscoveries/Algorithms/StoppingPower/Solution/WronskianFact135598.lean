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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WronskianUv135598

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspWronskianFact135598

section
set_option compiler.extract_closed false
namespace GqspWronskianFact135598
section WronskianFact135598
set_option maxRecDepth 4000000
set_option exponentiation.threshold 256
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert (prodRangeLinear_p26
    prodRangeLinear_p26_add prodRangeLinear_p26_one_eq_fact)
open GqspWronskian62592 (powBinDepth powBinDepth_eq StrictListBind
    gqsp_zwLenEq gqsp_zwGetD gqsp_zwMaxMagLoop gqsp_zwMillerResLoop)
open GqspWronskianUV135598 (gqsp_b135598_k409600_cheb_scale0
    gqsp_b135598_k409600_cheb_Bw gqsp_v_c0 gqsp_v_c1 gqsp_v_c2)
private def blockProd (st : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, a => Nat.mul (blockProd st m a) (Nat.add a (Nat.mul st m))
private theorem pow_le_prodRangeLinear (a : ℕ) : ∀ n : ℕ, a ^ n ≤ prodRangeLinear_p26 a n
  | 0 => Nat.le_refl 1
  | k + 1 => by
      rw [Nat.pow_succ, prodRangeLinear_p26]
      exact Nat.mul_le_mul (pow_le_prodRangeLinear a k) (Nat.le_add_right a k)
private theorem blockProd_pow_le (st a : ℕ) :
    ∀ m : ℕ, (blockProd st m a) ^ st ≤ prodRangeLinear_p26 a (st * m)
  | 0 => by simp [blockProd, prodRangeLinear_p26]
  | m + 1 => by
      rw [show st * (m + 1) = st * m + st by ring, prodRangeLinear_p26_add, blockProd]
      simp only [Nat.mul_eq, Nat.add_eq]
      rw [Nat.mul_pow]
      exact Nat.mul_le_mul (blockProd_pow_le st a m) (pow_le_prodRangeLinear (a + st * m) st)
private lemma fact_bound_abstract (S P2_K B M K N_big Aux B_blk L_mk L_big F_big Z : ℕ)
    (hscale : S ≤ P2_K) (h2_K : P2_K = 2 ^ K) (hbase : 2 * Aux ≤ B_blk)
    (hP400 : Aux = B ^ M) (hNM : N_big = M * K) (hB : B_blk ^ K ≤ L_mk) (hL : L_mk = L_big)
    (hfact : L_big = F_big) (hZ : Z = 0) : S * B ^ N_big ≤ 2 ^ Z * F_big := by
  subst h2_K hP400 hNM hL hfact hZ
  calc S * B ^ (M * K)
    _ = S * (B ^ M) ^ K := congrArg (S * ·) (Nat.pow_mul B M K)
    _ ≤ 2 ^ K * (B ^ M) ^ K := Nat.mul_le_mul_right _ hscale
    _ = (2 * B ^ M) ^ K := (Nat.mul_pow 2 (B ^ M) K).symm
    _ ≤ B_blk ^ K := Nat.pow_le_pow_left hbase K
    _ ≤ L_mk := hB
    _ = 2 ^ 0 * L_mk := (Nat.one_mul L_mk).symm
set_option maxHeartbeats 4800000 in
-- kernel Wronskian factorial/chunk v verification
private theorem scale_ble :
    Nat.ble gqsp_b135598_k409600_cheb_scale0 (powBinDepth 11 2 1024) = true := by decide +kernel
set_option maxHeartbeats 4800000 in
-- kernel Wronskian factorial/chunk v verification
private theorem base400_ble :
    Nat.ble (2 * powBinDepth 9 135598 400) (blockProd 1024 400 1) = true := by decide +kernel
theorem gqsp_b135598_k409600_fact_bound_nat : gqsp_b135598_k409600_cheb_scale0 * 135598 ^
    409600 ≤ 2 ^ 0 * (409600 : ℕ).factorial := fact_bound_abstract
    gqsp_b135598_k409600_cheb_scale0 (powBinDepth 11 2 1024) 135598 400 1024 409600
    (powBinDepth 9 135598 400) (blockProd 1024 400 1) (prodRangeLinear_p26 1 (1024 * 400))
    (prodRangeLinear_p26 1 409600) (409600 : ℕ).factorial 0 (Nat.ble_eq.mp scale_ble)
    (powBinDepth_eq 11 2 1024 (by decide)) (Nat.ble_eq.mp base400_ble)
    (powBinDepth_eq 9 135598 400 (by decide)) (by decide) (blockProd_pow_le 1024 1 400)
    (congrArg (prodRangeLinear_p26 1) (by decide : 1024 * 400 = 409600))
    (prodRangeLinear_p26_one_eq_fact 409600) rfl
noncomputable def gqsp_vC0Checks (c0 : List ℕ) : Bool :=
  gqsp_zwLenEq 45201 c0 0 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45199 c0)
    6277101735386853975512926850978760124971226014122491520119 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45200 c0)
    6277101735386798624050786705747500416602554407669458119791 &&
  Nat.ble (gqsp_zwMaxMagLoop gqsp_b135598_k409600_cheb_Bw c0 0)
    1010286984355221450013431795359437313032315913 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 45199 1 c0 0) 3070301018
noncomputable def gqsp_vC1Checks (c1 : List ℕ) : Bool :=
  gqsp_zwLenEq 45200 c1 0 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45198 c1)
    6277101735386875464315395722952600666423885149350380352061 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45199 c1)
    6277101735386864241575976988302854741604850110498276281552 &&
  Nat.ble (gqsp_zwMaxMagLoop gqsp_b135598_k409600_cheb_Bw c1 0)
    1010286984355221450013431795359437313032315913 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 45200 45200
    (6277101735386853975512926850978760124971226014122491520119 ::
    6277101735386798624050786705747500416602554407669458119791 :: c1) 0) 3063669512
noncomputable def gqsp_vC2Checks (c2 : List ℕ) : Bool :=
  gqsp_zwLenEq 45199 c2 0 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45197 c2) gqsp_b135598_k409600_cheb_Bw &&
  Nat.ble (gqsp_zwMaxMagLoop gqsp_b135598_k409600_cheb_Bw c2 0)
    1010286984355221450013431795359437313032315913 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 45199 90400
    (6277101735386875464315395722952600666423885149350380352061 ::
    6277101735386864241575976988302854741604850110498276281552 :: c2) 0) 3082572214
set_option maxHeartbeats 4800000 in
-- kernel Wronskian factorial/chunk v verification
theorem gqsp_vC0Bundle : StrictListBind gqsp_v_c0 gqsp_vC0Checks = true := by decide +kernel
set_option maxHeartbeats 4800000 in
-- kernel Wronskian factorial/chunk v verification
theorem gqsp_vC1Bundle : StrictListBind gqsp_v_c1 gqsp_vC1Checks = true := by decide +kernel
set_option maxHeartbeats 4800000 in
-- kernel Wronskian factorial/chunk v verification
theorem gqsp_vC2Bundle : StrictListBind gqsp_v_c2 gqsp_vC2Checks = true := by decide +kernel
end WronskianFact135598
end GqspWronskianFact135598
end
end GqspWronskianFact135598

end QuantumComputation.Specs.StoppingPowerSolution
end
