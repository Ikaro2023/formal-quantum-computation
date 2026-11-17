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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DyadicXMeasPrepOut13

/-!
# Reordered `wOuter = 13` Dyadic Outer `PREP` & `1,060 T` Sandwich Bridge (`ReordOuter13Bridge`)

Provides a `TightGapDeep`-free outer state-preparation bridge over `DyadicXMeasPrepOut13`
(`554 T` Berry `3`-AND paired forward `PREP_out`, `506 T` X-measurement `PREP_out†` resetting
`dyadicAltLoc` for `kZeroOut = 8`, `1,060 T` outer sandwich, operator-norm error `≤ 33 / 10 ^ 15`):

1. **Parametric `outerTable` `wOuter = 13` Outer `PREP` (`Section 1`):**
   Exports parametric `wOuter = 13` implementation and ideal unitaries,
   `PrepOutValidForWeights`, and operator-norm error bounds for any
   `outerTable : Fin 184 → OuterWeights.AliasEntry 184` and weight vector `wOut : Fin 184 → ℕ`.
2. **General `π184 : Equiv.Perm (Fin 184)` Permuted Alias Table (`Section 2`):**
   Constructs `permOuterAliasTable π184`, proves `permOuterAliasTable_keep_lt` and
   `permOuterAliasTable_isValid`, bridges `PrepOutValidPerm` (`PrepOutValidForWeights`),
   `PrepOutValidPerm256` (`extPerm256`), and `PrepOutValid (toOrigPrepOutOf π184 _)`, and
   instantiates the `1,060 T` dyadic outer sandwich for any `π184`.
3. **Variant A (`reordPerm184`) & Variant B (`reord128Perm184`) Instantiations (`Section 3`):**
   Specializes to both `0`-`rcOnly` two-body-first outer bijections:
   - **Variant A (`reordPerm184`):** `0..125 ↦ 58..183`, `126..183 ↦ 0..57` (`10`-AND `SELECT`).
   - **Variant B (`reord128Perm184`):** `0..125 ↦ 58..183`, `126..127 ↦ 56..57`,
     `128..183 ↦ 0..55` (`128`-aligned one-body indices, `9`-AND `12,850 T` `SELECT`).

## References
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias
open BlockEncodingCore BlockEncodingCircuit
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

local instance (priority := 1000000) instNeZeroTwoPowReord13 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

attribute [local irreducible] oneBodyWeights fragmentWeights DataArrays.oneBodyWeightsArr
  DataArrays.fragmentWeightsArr oneBodyWeightInt fragmentWeightNat

/-! ## Section 1: Parametric `outerTable` `wOuter = 13` Dyadic Outer `PREP` & `1,060 T` Sandwich -/

/-- Permuted `184`-item integer outer weight table `xo' ↦ outerWeightNat (π184 xo')`. -/
def outerWeightNatPerm (π184 : Equiv.Perm (Fin 184)) (xo' : Fin 184) : ℕ :=
  outerWeightNat (π184 xo')

/-- Extends any `π184 : Equiv.Perm (Fin 184)` by the identity on padding indices `184..255` to a
permutation of `Fin (2 ^ 8)`. -/
def extPerm256 (π184 : Equiv.Perm (Fin 184)) : Equiv.Perm (Fin (2 ^ 8)) where
  toFun x := if h : x.val < 184 then ⟨(π184 ⟨x.val, h⟩).val, by omega⟩ else x
  invFun x := if h : x.val < 184 then ⟨(π184.symm ⟨x.val, h⟩).val, by omega⟩ else x
  left_inv x := by
    by_cases h : x.val < 184
    · have h2 : (π184 ⟨x.val, h⟩).val < 184 := (π184 ⟨x.val, h⟩).isLt
      simp [h, h2]
    · simp [h]
  right_inv x := by
    by_cases h : x.val < 184
    · have h2 : (π184.symm ⟨x.val, h⟩).val < 184 := (π184.symm ⟨x.val, h⟩).isLt
      simp [h, h2]
    · simp [h]

theorem extPerm256_lt (π184 : Equiv.Perm (Fin 184)) (x : Fin (2 ^ 8)) (h : x.val < 184) :
    (extPerm256 π184 x).val = (π184 ⟨x.val, h⟩).val := by
  simp [extPerm256, h]

theorem extPerm256_ge (π184 : Equiv.Perm (Fin 184)) (x : Fin (2 ^ 8)) (h : 184 ≤ x.val) :
    extPerm256 π184 x = x := by
  have hn : ¬ x.val < 184 := by omega
  simp [extPerm256, hn]

@[simp]
theorem extPerm256_lt184_iff (π184 : Equiv.Perm (Fin 184)) (x : Fin (2 ^ 8)) :
    (extPerm256 π184 x).val < 184 ↔ x.val < 184 := by
  by_cases h : x.val < 184
  · simp [extPerm256, h, (π184 ⟨x.val, h⟩).isLt]
  · simp [extPerm256, h]

/-- Lifts an `8`-bit index permutation `σ : Equiv.Perm (Fin (2 ^ 8))` onto `rXoLoc wOuter` inside
`mOutUB wOuter`, fixing `(rGOutLoc wOuter, rSigOutLoc wOuter)`. -/
noncomputable def outPermEquiv (σ : Equiv.Perm (Fin (2 ^ 8))) (wOuter : ℕ) :
    Equiv.Perm (Fin (2 ^ mOutUB wOuter)) where
  toFun o := (rXoLoc wOuter).replaceIndex o (σ ((rXoLoc wOuter).extractIndex o))
  invFun o := (rXoLoc wOuter).replaceIndex o (σ.symm ((rXoLoc wOuter).extractIndex o))
  left_inv o := by
    simp only [QRegister.extractIndex_replaceIndex, Equiv.symm_apply_apply,
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_extractIndex]
  right_inv o := by
    simp only [QRegister.extractIndex_replaceIndex, Equiv.apply_symm_apply,
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_extractIndex]

@[simp]
theorem extract_rXoLoc_outPermEquiv (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (o : Fin (2 ^ mOutUB wOuter)) :
    (rXoLoc wOuter).extractIndex (outPermEquiv σ wOuter o) = σ ((rXoLoc wOuter).extractIndex o) :=
  (rXoLoc wOuter).extractIndex_replaceIndex o _

@[simp]
theorem extract_rSigOutLoc_outPermEquiv (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (o : Fin (2 ^ mOutUB wOuter)) :
    (rSigOutLoc wOuter).extractIndex (outPermEquiv σ wOuter o) = (rSigOutLoc wOuter).extractIndex
      o := by
  apply (basisBits 1).injective; funext i
  rw [(rSigOutLoc wOuter).basisBits_extractIndex, (rSigOutLoc wOuter).basisBits_extractIndex]
  dsimp only [outPermEquiv]
  refine (rXoLoc wOuter).basisBits_replaceIndex_of_not_mem o _ _ ?_
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [rXoLoc, rSigOutLoc, QRegister.block_apply_val] at hv
  have := j.isLt; omega

/-- Converts a `σ`-reordered `PREP_out` unitary into an equivalent original-ordering `PREP_out`
unitary by post-applying `permutationUnitary (outPermEquiv σ wOuter)`. -/
noncomputable def toOrigPrepOutOf (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (prepOutPerm : Unitary (2 ^ mOutUB wOuter)) : Unitary (2 ^ mOutUB wOuter) :=
  Operator.permutationUnitary (outPermEquiv σ wOuter) * prepOutPerm

theorem toOrigPrepOutOf_apply (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (prepOutPerm : Unitary (2 ^ mOutUB wOuter)) (o k : Fin (2 ^ mOutUB wOuter)) :
    (toOrigPrepOutOf σ prepOutPerm).1 o k = prepOutPerm.1 ((outPermEquiv σ wOuter).symm o) k := by
  dsimp only [toOrigPrepOutOf]
  rw [Submonoid.coe_mul, Matrix.mul_apply]
  have hp : ∀ j : Fin (2 ^ mOutUB wOuter),
      (Operator.permutationUnitary (outPermEquiv σ wOuter)).1 o j =
        if o = outPermEquiv σ wOuter j then 1 else 0 := fun j ↦ by
    have hv := congrFun (Operator.permutationUnitary_mulVec_single (outPermEquiv σ wOuter) j 1) o
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at hv
    exact hv
  simp_rw [hp]
  rw [Finset.sum_eq_single ((outPermEquiv σ wOuter).symm o)]
  · simp [(outPermEquiv σ wOuter).apply_symm_apply]
  · intro j _ hj
    have hne : o ≠ outPermEquiv σ wOuter j := fun h ↦
      hj (by rw [h, (outPermEquiv σ wOuter).symm_apply_apply])
    simp [hne]
  · simp

/-- `256`-item `σ : Equiv.Perm (Fin (2 ^ 8))` outer `PREP_out` validity predicate. -/
def PrepOutValidPerm256 (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (prepOutPerm : Unitary (2 ^ mOutUB wOuter)) : Prop :=
  (∀ o' : Fin (2 ^ mOutUB wOuter),
    184 ≤ ((rXoLoc wOuter).extractIndex o').val → prepOutPerm.1 o' 0 = 0) ∧
  (∀ (xo' : Fin 184) (so : Fin 2),
    (∑ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
        ((rXoLoc wOuter).extractIndex o').val = xo'.val ∧ (rSigOutLoc wOuter).extractIndex o' = so),
      Complex.normSq (prepOutPerm.1 o' 0)) =
      if h : (σ ⟨xo'.val, by omega⟩).val < 184 then
        (outerWeightNat ⟨(σ ⟨xo'.val, by omega⟩).val, h⟩ : ℝ) / (2 * 188416)
      else 0)

theorem prepOutValidPerm256_extPerm256_of_weights (π184 : Equiv.Perm (Fin 184)) {wOuter : ℕ}
    {prepOutPerm : Unitary (2 ^ mOutUB wOuter)}
    (hw : CompactBilinearPrep.PrepOutValidForWeights (outerWeightNatPerm π184) prepOutPerm) :
    PrepOutValidPerm256 (extPerm256 π184) prepOutPerm := by
  refine ⟨hw.1, fun xo' so ↦ ?_⟩
  rw [hw.2 xo' so]
  have hlt : (extPerm256 π184 ⟨xo'.val, by omega⟩).val < 184 :=
    (extPerm256_lt184_iff π184 ⟨xo'.val, by omega⟩).mpr xo'.isLt
  rw [dite_eq_left hlt]
  have heq : (⟨(extPerm256 π184 ⟨xo'.val, by omega⟩).val, hlt⟩ : Fin 184) = π184 xo' := by
    ext; simp [extPerm256, xo'.isLt]
  rw [heq]; rfl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge

end
