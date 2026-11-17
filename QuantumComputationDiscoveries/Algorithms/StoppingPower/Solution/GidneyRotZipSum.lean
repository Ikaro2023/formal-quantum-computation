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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DisjointWiresSymm

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModGidneyGuardWrap28
@[expose] public section
namespace GidneyGuardWrap28
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux.SpecMirror
open PhaseGradSignalRot hiding IntertwinesCat
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open GridGuard654ReflAux
open GidneySignalRotPart1
open GidneySignalRotGuardWrap
theorem sum_range_getD_eq_zipWith_sum (g : ℕ → ℕ → ℕ) :
    ∀ (l₁ l₂ : List ℕ), l₁.length = l₂.length →
      (∑ j ∈ Finset.range l₁.length, g (l₁.getD j 0) (l₂.getD j 0)) =
        (List.zipWith g l₁ l₂).sum
  | [], [], _ => by simp
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.zipWith_cons_cons, List.sum_cons]
    rw [sum_range_getD_eq_zipWith_sum g as bs h, add_comm]
theorem list_getD_lt_of_all_lt :
    ∀ (l : List ℕ) (B : ℕ), l.all (· < B) = true → ∀ j < l.length, l.getD j 0 < B
  | [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | a :: as, B, hall, 0, _ => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    simpa [List.getD_cons_zero] using hall.1
  | a :: as, B, hall, j + 1, hj => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
    simpa [List.getD_cons_succ] using list_getD_lt_of_all_lt as B hall.2 j hj
theorem sum_gidneyRotToffEquiv_eq_of_list_zip_sum (M : ℕ) (C_opt_list : List ℕ)
    (C : Fin (M + 1) → Fin (2 ^ 42)) (hC : ∀ i : Fin (M + 1), C i = Fin.ofNat (2 ^ 42)
    (C_opt_list.getD i.val 0)) (hlen : C_opt_list.length = M + 1)
    (hall_lt : C_opt_list.all (· < 4398046511104) = true) (S_rot : ℕ) (hzip : (List.zipWith
    (fun a _ ↦ gidneyRotToffEquiv a) C_opt_list C_opt_list).sum = S_rot) :
    (∑ t : Fin (M + 1), gidneyRotToffEquiv (C t).val) = S_rot := by
  rw [← biPrefixGidneyRotToffSum_eq_univ_sum]
  unfold biPrefixGidneyRotToffSum
  have hcongr : (∑ j ∈ Finset.range (M + 1), gidneyRotToffEquiv (biCode M C j).val) = ∑ j ∈
      Finset.range C_opt_list.length, gidneyRotToffEquiv (C_opt_list.getD j 0) := by
    rw [hlen]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hj_code : biCode M C j = C ⟨j, hj⟩ := by simp [biCode, hj]
    have hlt : C_opt_list.getD j 0 < 2 ^ 42 :=
      list_getD_lt_of_all_lt C_opt_list 4398046511104 hall_lt j (by rw [hlen]; exact hj)
    have hval : (C ⟨j, hj⟩).val = C_opt_list.getD j 0 := by
      rw [hC ⟨j, hj⟩]
      exact Nat.mod_eq_of_lt hlt
    rw [hj_code, hval]
  rw [hcongr,
    sum_range_getD_eq_zipWith_sum
      (fun a _ ↦ gidneyRotToffEquiv a) C_opt_list C_opt_list rfl, hzip]
end GidneyGuardWrap28
end
end ModGidneyGuardWrap28

end QuantumComputation.Specs.StoppingPowerSolution
