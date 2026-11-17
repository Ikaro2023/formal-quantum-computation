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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Half-Step Sum-of-Squares Block-Encoding `U_B` for Cytochrome P450
Constructs and verifies the 4-step half-step SOS block-encoding unitary `U_B` (`PREP_out`,
`PREP_mid`, `SELECT`, `PREP_mid†`) for `thcHamiltonian P450.dfthc` in the spin-blocked basis
(`p450FswapUninterleave`):

1. **Spin-Blocked DFTHC SOS Bridge:** Conjugates `SumOfSquares.thcHamiltonian_sub_lowerBound_eq_sos`
   by
   the zero-`T` Clifford `p450FswapUninterleave` (`FermionPerm`), mapping `orbitalReflection`
   to `singleSpinReflection` on `rSpin0` (`0..57`) or `rSpin1` (`58..115`).
2. **Parametric Register Layout & Half-Step SOS-to-Isometry Theorem:** Defines `rSysUB` (`116`
   wires), `rOutUB` (`8 + w_go + 1` wires), and `rMidUB` (`5 + w_gi + 1` wires) for arbitrary outer
   and inner coherent-alias garbage widths `(w_go, w_gi)`, proves the circuit-level `SELECT`
   conjugation identity (`58` Fredkins + `G(u_{rowIdx})` + center `CZ` + `58` Fredkins + `Z` phase),
   and establishes both the full operator SOS-to-isometry identity and the norm-squared Rayleigh
   quotient identity.
3. **Operator-Norm & Catalytic Perturbation Bounds:** Proves `‖U_B_impl.1 - U_B_ideal.1‖ ≤
   δ_out + 2 * δ_mid + δ_sel` and the exact-catalyst (`δ_sel = 0`) state-vector `L²` bound on
   `phaseGradientState 14`.
4. **Zero-`TOFF` `DynamicCircuit` Realizations & `T`-Counts:** Appended in Section 4.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit QProg Solution.CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-- High-priority parametric `NeZero (2 ^ k)` instance avoiding unary `Nat.succ` unfolding. -/
instance (priority := 100000) instNeZeroTwoPowUB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: DFTHC Sign/Index Accessors, `p450RowVector` & Spin-Blocked SOS Bridge -/

/-- Flattened signed integer mantissa `m^{(rc)}_b` (`rc = 14 * r + c ∈ Fin 126`, `b ∈ Fin 30`). -/
def innerMantissaFlat (rc : Fin 126) (b : Fin 30) : ℤ :=
  innerMantissa ⟨rc.val / 14, by omega⟩ ⟨rc.val % 14, by omega⟩ b

/-- Sign bit of the one-body weight `n_ℓ` (`true` iff `t_ℓ < 0`). -/
def neg1b (ℓ : Fin 58) : Bool :=
  decide (oneBodyWeightInt ℓ < 0)

/-- Sign bit of the inner mantissa `m^{(rc)}_b` (`true` iff `m^{(rc)}_b < 0`). -/
def negIn (rc : Fin 126) (b : Fin 30) : Bool :=
  decide (innerMantissaFlat rc b < 0)

/-- Zero-padded `8`-bit extension of `neg1b` to `Fin (2 ^ 8)`. -/
def neg1bPadded (xo : Fin (2 ^ 8)) : Bool :=
  if h : xo.val < 58 then neg1b ⟨xo.val, h⟩ else false

/-- Zero-padded `(7, 5)`-bit extension of `negIn` to `Fin (2 ^ 7) → Fin (2 ^ 5) → Bool`. -/
def negInPadded (rc : Fin (2 ^ 7)) (b : Fin (2 ^ 5)) : Bool :=
  if h : rc.val < 126 ∧ b.val < 30 then negIn ⟨rc.val, h.1⟩ ⟨b.val, h.2⟩ else false

/-- Combined `184`-entry outer integer weight (`|n_ℓ|` for `0..57`, `n_{rc}` for `58..183`). -/
def outerWeightNat (xo : Fin 184) : ℕ :=
  if h : xo.val < 58 then
    (oneBodyWeightInt ⟨xo.val, h⟩).natAbs
  else
    fragmentWeightNat ⟨(xo.val - 58) / 14, by omega⟩ ⟨(xo.val - 58) % 14, by omega⟩

theorem neg1b_eq_true_iff (ℓ : Fin 58) :
    neg1b ℓ = true ↔ P450.oneBodyEigenvalue ℓ < 0 := by
  rw [neg1b, decide_eq_true_iff, oneBodyEigenvalue_eq_weightInt]
  have hq : 0 < P450.coefficientUnit := coefficientUnit_pos
  constructor
  · intro hlt
    exact mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hlt) hq
  · intro hlt
    by_contra hge
    have hnn : (0 : ℝ) ≤ (oneBodyWeightInt ℓ : ℝ) := by exact_mod_cast not_lt.mp hge
    linarith [mul_nonneg hnn hq.le]

theorem oneBodySign_eq_neg1b (ℓ : Fin 58) :
    oneBodySign ℓ = if neg1b ℓ then -1 else 1 := by
  unfold oneBodySign
  by_cases h : neg1b ℓ = true
  · have hlt : P450.oneBodyEigenvalue ℓ < 0 := (neg1b_eq_true_iff ℓ).mp h
    simp [h, hlt]
  · have hf : neg1b ℓ = false := Bool.eq_false_iff.mpr h
    have hnot : ¬ P450.oneBodyEigenvalue ℓ < 0 := mt (neg1b_eq_true_iff ℓ).mpr h
    simp [hf, hnot]

theorem int_natAbs_mul_sign (z : ℤ) :
    (z.natAbs : ℝ) * (if decide (z < 0) then (-1 : ℝ) else 1) = (z : ℝ) := by
  by_cases h : z < 0
  · simp only [h, decide_true, ↓reduceIte, mul_neg, mul_one]
    have hz : (z.natAbs : ℤ) = -z := by omega
    have hR := congrArg (Int.cast (R := ℝ)) hz
    simp only [Int.cast_natCast, Int.cast_neg] at hR
    linarith
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, mul_one]
    have hz : (z.natAbs : ℤ) = z := by omega
    have hR := congrArg (Int.cast (R := ℝ)) hz
    simpa only [Int.cast_natCast] using hR

-- Seal all large literal tables so downstream proofs never unfold them.
attribute [local irreducible] oneBodyWeightInt fragmentWeightNat innerMantissa

theorem innerMantissaFlat_natAbs_mul_sign (rc : Fin 126) (b : Fin 30) :
    ((innerMantissaFlat rc b).natAbs : ℝ) * (if negIn rc b then (-1 : ℝ) else 1) =
      (innerMantissaFlat rc b : ℝ) :=
  int_natAbs_mul_sign (innerMantissaFlat rc b)

theorem outerWeightNat_lt_58_mul_unit (ℓ : Fin 58) :
    (outerWeightNat ⟨ℓ.val, by omega⟩ : ℝ) * P450.coefficientUnit =
      |P450.oneBodyEigenvalue ℓ| := by
  have hlt : (⟨ℓ.val, by omega⟩ : Fin 184).val < 58 := ℓ.isLt
  simp only [outerWeightNat, hlt, ↓reduceDIte, Fin.eta]
  rw [oneBodyEigenvalue_eq_weightInt, abs_mul, abs_of_pos coefficientUnit_pos]
  refine congrArg (· * P450.coefficientUnit) ?_
  by_cases h : oneBodyWeightInt ℓ < 0
  · have hz : ((oneBodyWeightInt ℓ).natAbs : ℤ) = -oneBodyWeightInt ℓ := by omega
    have hR := congrArg (Int.cast (R := ℝ)) hz
    simp only [Int.cast_natCast, Int.cast_neg] at hR
    rw [abs_of_neg (Int.cast_lt_zero.mpr h), hR]
  · have hz : ((oneBodyWeightInt ℓ).natAbs : ℤ) = oneBodyWeightInt ℓ := by omega
    have hR := congrArg (Int.cast (R := ℝ)) hz
    simp only [Int.cast_natCast] at hR
    have hnn : (0 : ℝ) ≤ (oneBodyWeightInt ℓ : ℝ) := by exact_mod_cast not_lt.mp h
    rw [abs_of_nonneg hnn, hR]

theorem sum_innerMantissaFlat_natAbs (rc : Fin 126) :
    ∑ b : Fin 30, (innerMantissaFlat rc b).natAbs = 15360 :=
  innerWeights_l1_eq_15360 ⟨rc.val / 14, by omega⟩ ⟨rc.val % 14, by omega⟩

/-- Equivalence `Fin 58 ⊕ (Fin 9 × Fin 14) ≃ Fin 184` splitting outer indices into one-body and
two-body entries. -/
def outerIndexEquiv : Fin 58 ⊕ (Fin 9 × Fin 14) ≃ Fin 184 where
  toFun
    | .inl ℓ => ⟨ℓ.val, by omega⟩
    | .inr (r, c) => ⟨58 + 14 * r.val + c.val, by omega⟩
  invFun xo :=
    if h : xo.val < 58 then
      .inl ⟨xo.val, h⟩
    else
      .inr (⟨(xo.val - 58) / 14, by omega⟩, ⟨(xo.val - 58) % 14, by omega⟩)
  left_inv
    | .inl ℓ => by simp [ℓ.isLt]
    | .inr (r, c) => by
        have hnot : ¬ (58 + 14 * r.val + c.val < 58) := by omega
        simp only [hnot, ↓reduceDIte, Sum.inr.injEq, Prod.mk.injEq]
        refine ⟨Fin.ext (by dsimp; omega), Fin.ext (by dsimp; omega)⟩
  right_inv xo := by
    by_cases h : xo.val < 58
    · simp [h]
    · simp only [h, ↓reduceDIte]
      exact Fin.ext (by dsimp; omega)

/-- Unified `319`-row orbital vector table (`0..57` = `oneBodyVector`, `58..318` = `leafVector`). -/
noncomputable def p450RowVector (idx : Fin 319) : Fin 58 → ℝ :=
  if h : idx.val < 58 then
    P450.oneBodyVector ⟨idx.val, h⟩
  else
    P450.leafVector ⟨idx.val - 58, by omega⟩

theorem p450RowVector_sum_sq (idx : Fin 319) :
    ∑ p : Fin 58, p450RowVector idx p ^ 2 = 1 := by
  unfold p450RowVector
  split_ifs
  · exact givensLeaf_sum_sq 15 _
  · exact givensLeaf_sum_sq 15 _

/-- Spin-`0` system block `0..57` inside the `116`-qubit spin-blocked system space. -/
abbrev rSpin0 : QRegister 58 (2 * 58) := QRegister.block 0 58 (by omega)

/-- Spin-`1` system block `58..115` inside the `116`-qubit spin-blocked system space. -/
abbrev rSpin1 : QRegister 58 (2 * 58) := QRegister.block 58 58 (by omega)

@[simp]
theorem singleSpinNumberOp_conjTranspose {N : ℕ} (u : Fin N → ℝ) :
    (singleSpinNumberOp u)ᴴ = singleSpinNumberOp u := by
  simp [singleSpinNumberOp]

theorem singleSpinNumberOp_mul_self {N : ℕ} {u : Fin N → ℝ} (hu : ∑ p, u p ^ 2 = 1) :
    singleSpinNumberOp u * singleSpinNumberOp u = singleSpinNumberOp u :=
  jwLinearMode_number_idempotent Function.injective_id hu

@[simp]
theorem singleSpinReflection_conjTranspose {N : ℕ} (u : Fin N → ℝ) :
    (singleSpinReflection u)ᴴ = singleSpinReflection u := by
  simp [singleSpinReflection]

theorem singleSpinReflection_mul_self {N : ℕ} {u : Fin N → ℝ} (hu : ∑ p, u p ^ 2 = 1) :
    singleSpinReflection u * singleSpinReflection u = 1 :=
  reflection_mul_self_of_idempotent (singleSpinNumberOp_mul_self hu)

/-- Spin-blocked orbital reflection on `2 * 58` qubits (`singleSpinReflection u` on `rSpin0` or
`rSpin1`). -/
noncomputable def blockedOrbitalReflection (u : Fin 58 → ℝ) (σ : Fin 2) :
    Operator (2 ^ (2 * 58)) :=
  if σ = 0 then
    rSpin0.embedMatrix (singleSpinReflection u)
  else
    rSpin1.embedMatrix (singleSpinReflection u)

@[simp]
theorem blockedOrbitalReflection_conjTranspose (u : Fin 58 → ℝ) (σ : Fin 2) :
    (blockedOrbitalReflection u σ)ᴴ = blockedOrbitalReflection u σ := by
  unfold blockedOrbitalReflection
  split_ifs
  · rw [← rSpin0.embedMatrix_conjTranspose, singleSpinReflection_conjTranspose]
  · rw [← rSpin1.embedMatrix_conjTranspose, singleSpinReflection_conjTranspose]

theorem blockedOrbitalReflection_mul_self {u : Fin 58 → ℝ} (hu : ∑ p, u p ^ 2 = 1) (σ : Fin 2) :
    blockedOrbitalReflection u σ * blockedOrbitalReflection u σ = 1 := by
  unfold blockedOrbitalReflection
  split_ifs
  · rw [← rSpin0.embedMatrix_mul, singleSpinReflection_mul_self hu, rSpin0.embedMatrix_one]
  · rw [← rSpin1.embedMatrix_mul, singleSpinReflection_mul_self hu, rSpin1.embedMatrix_one]

theorem fswapUninterleave_conj_orbitalReflection (u : Fin 58 → ℝ) (σ : Fin 2) :
    p450FswapUninterleave.eval.1 * orbitalReflection 58 u σ * p450FswapUninterleave.eval.1ᴴ =
      blockedOrbitalReflection u σ := by
  fin_cases σ
  · exact p450FswapUninterleave_conj_orbitalReflection_zero u
  · exact p450FswapUninterleave_conj_orbitalReflection_one u

/-- Spin-blocked one-body projector `(I - sgn(t_ℓ) R^{blocked}_{u_ℓ, σ}) / 2`. -/
noncomputable def blockedOneBodyProjector (ℓ : Fin 58) (σ : Fin 2) :
    Operator (2 ^ (2 * 58)) :=
  (2 : ℂ)⁻¹ • (1 - (oneBodySign ℓ : ℂ) • blockedOrbitalReflection (P450.oneBodyVector ℓ) σ)

/-- Spin-blocked normalized Hermitian LCU operator `A^{blocked}_{rc}` for fragment `(r, c)`. -/
noncomputable def blockedFragmentLCU (r : Fin 9) (c : Fin 14) :
    Operator (2 ^ (2 * 58)) :=
  ((15360 : ℂ)⁻¹) •
    ((innerMantissa r c 29 : ℂ) • (1 : Operator (2 ^ (2 * 58))) -
      ∑ b : Fin 29, ∑ σ : Fin 2,
        ((innerMantissa r c b.castSucc : ℂ) / 2) •
          blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ)

/-- Spin-blocked P450 DFTHC Hamiltonian `U_fswap · H_DFTHC · U_fswap†`. -/
noncomputable def p450HBlocked : Operator (2 ^ (2 * 58)) :=
  p450FswapUninterleave.eval.1 * thcHamiltonian P450.dfthc * p450FswapUninterleave.eval.1ᴴ

@[simp]
theorem blockedOneBodyProjector_conjTranspose (ℓ : Fin 58) (σ : Fin 2) :
    (blockedOneBodyProjector ℓ σ)ᴴ = blockedOneBodyProjector ℓ σ := by
  unfold blockedOneBodyProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, blockedOrbitalReflection_conjTranspose]
  have h1 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  have h2 : star (oneBodySign ℓ : ℂ) = (oneBodySign ℓ : ℂ) := Complex.conj_ofReal _
  rw [h1, h2]

@[simp]
theorem blockedFragmentLCU_conjTranspose (r : Fin 9) (c : Fin 14) :
    (blockedFragmentLCU r c)ᴴ = blockedFragmentLCU r c := by
  unfold blockedFragmentLCU
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_sum]
  have h1 : star ((15360 : ℂ)⁻¹) = (15360 : ℂ)⁻¹ := by norm_num
  have h2 : star (innerMantissa r c 29 : ℂ) = (innerMantissa r c 29 : ℂ) := by simp
  rw [h1, h2]
  refine congrArg (fun M ↦ ((15360 : ℂ)⁻¹) •
      ((innerMantissa r c 29 : ℂ) • (1 : Operator (2 ^ (2 * 58))) - M)) ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Matrix.conjTranspose_smul, blockedOrbitalReflection_conjTranspose]
  have h3 : star ((innerMantissa r c b.castSucc : ℂ) / 2) =
      (innerMantissa r c b.castSucc : ℂ) / 2 := by simp
  rw [h3]

private theorem conj_unitary_mul {d : ℕ} (U : Unitary d) (A B : Operator d) :
    U.1 * (A * B) * U.1ᴴ = (U.1 * A * U.1ᴴ) * (U.1 * B * U.1ᴴ) := by
  have h1 : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  calc U.1 * (A * B) * U.1ᴴ = (U.1 * A) * (U.1ᴴ * U.1) * (B * U.1ᴴ) := by
        rw [h1, mul_one]; simp only [Matrix.mul_assoc]
    _ = (U.1 * A * U.1ᴴ) * (U.1 * B * U.1ᴴ) := by simp only [Matrix.mul_assoc]

private theorem conj_unitary_one {d : ℕ} (U : Unitary d) :
    U.1 * (1 : Operator d) * U.1ᴴ = 1 := by
  rw [mul_one, ← Matrix.star_eq_conjTranspose]
  exact U.2.2

theorem fswapUninterleave_conj_oneBodyProjector (ℓ : Fin 58) (σ : Fin 2) :
    p450FswapUninterleave.eval.1 * oneBodyProjector ℓ σ * p450FswapUninterleave.eval.1ᴴ =
      blockedOneBodyProjector ℓ σ := by
  unfold oneBodyProjector blockedOneBodyProjector
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, conj_unitary_one,
    mul_smul_comm, smul_mul_assoc, fswapUninterleave_conj_orbitalReflection]

theorem fswapUninterleave_conj_fragmentLCU (r : Fin 9) (c : Fin 14) :
    p450FswapUninterleave.eval.1 * fragmentLCU r c * p450FswapUninterleave.eval.1ᴴ =
      blockedFragmentLCU r c := by
  unfold fragmentLCU blockedFragmentLCU
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    conj_unitary_one, Finset.mul_sum, Finset.sum_mul]
  refine congrArg (fun M ↦ ((15360 : ℂ)⁻¹) •
      ((innerMantissa r c 29 : ℂ) • (1 : Operator (2 ^ (2 * 58))) - M)) ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [mul_smul_comm, smul_mul_assoc, fswapUninterleave_conj_orbitalReflection]

/-- Spin-blocked Sum-of-Squares decomposition of `p450HBlocked - dfthcLowerBound • 1`. -/
theorem p450HBlocked_sub_lowerBound_eq_sos :
    p450HBlocked - (dfthcLowerBound : ℂ) • 1 =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2,
        ((|P450.oneBodyEigenvalue ℓ| : ℝ) : ℂ) •
          ((blockedOneBodyProjector ℓ σ)ᴴ * blockedOneBodyProjector ℓ σ)) +
      (∑ r : Fin 9, ∑ c : Fin 14,
        ((2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit : ℝ) : ℂ) •
          ((blockedFragmentLCU r c)ᴴ * blockedFragmentLCU r c)) := by
  let U := p450FswapUninterleave.eval
  have hlhs : p450HBlocked - (dfthcLowerBound : ℂ) • 1 =
      U.1 * (thcHamiltonian P450.dfthc - (dfthcLowerBound : ℂ) • 1) * U.1ᴴ := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, conj_unitary_one]
    rfl
  rw [hlhs, thcHamiltonian_sub_lowerBound_eq_sos, mul_add, add_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    refine Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [conj_unitary_mul, oneBodyProjector_conjTranspose, fswapUninterleave_conj_oneBodyProjector,
      blockedOneBodyProjector_conjTranspose]
  · simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    rw [conj_unitary_mul, fragmentLCU_conjTranspose, fswapUninterleave_conj_fragmentLCU,
      blockedFragmentLCU_conjTranspose]

/-- Width `8 + w_go + 1` of the outer state-preparation register `rOut = (x_o, g_out, σ_out)`. -/
abbrev mOutUB (w_go : ℕ) : ℕ := 8 + w_go + 1

/-- Width `5 + w_gi + 1` of the inner state-preparation register `rMid = (b, g_in, σ_in)`. -/
abbrev mMidUB (w_gi : ℕ) : ℕ := 5 + w_gi + 1

/-- Combined block-encoding ancilla width `mOutUB w_go + mMidUB w_gi`. -/
abbrev mAncUB (w_go w_gi : ℕ) : ℕ := mOutUB w_go + mMidUB w_gi

/-- Total active qubit count `116 + mAncUB w_go w_gi` of `U_B`. -/
abbrev nUB (w_go w_gi : ℕ) : ℕ := 2 * 58 + mAncUB w_go w_gi

/-- `116`-wire system register `0..115` inside `nUB w_go w_gi`. -/
abbrev rSysUB (w_go w_gi : ℕ) : QRegister (2 * 58) (nUB w_go w_gi) :=
  QRegister.block 0 (2 * 58) (by dsimp [nUB, mAncUB, mOutUB, mMidUB]; omega)

/-- Outer ancilla register `rOut` (`8 + w_go + 1` wires) inside `nUB w_go w_gi`. -/
abbrev rOutUB (w_go w_gi : ℕ) : QRegister (mOutUB w_go) (nUB w_go w_gi) :=
  QRegister.block (2 * 58) (mOutUB w_go) (by dsimp [nUB, mAncUB, mOutUB, mMidUB]; omega)

/-- Inner ancilla register `rMid` (`5 + w_gi + 1` wires) inside `nUB w_go w_gi`. -/
abbrev rMidUB (w_go w_gi : ℕ) : QRegister (mMidUB w_gi) (nUB w_go w_gi) :=
  QRegister.block (2 * 58 + mOutUB w_go) (mMidUB w_gi)
    (by dsimp [nUB, mAncUB, mOutUB, mMidUB]; omega)

/-- Full ancilla register `rAll = rOut ++ rMid` inside `nUB w_go w_gi`. -/
abbrev rAllUB (w_go w_gi : ℕ) : QRegister (mAncUB w_go w_gi) (nUB w_go w_gi) :=
  QRegister.block (2 * 58) (mAncUB w_go w_gi) (by dsimp [nUB, mAncUB, mOutUB, mMidUB]; omega)

/-- Local `x_o` (`8` bits) sub-register of `rOut`. -/
abbrev rXoLoc (w_go : ℕ) : QRegister 8 (mOutUB w_go) :=
  QRegister.block 0 8 (by dsimp [mOutUB]; omega)

/-- Local `σ_out` (`1` bit) sub-register of `rOut`. -/
abbrev rSigOutLoc (w_go : ℕ) : QRegister 1 (mOutUB w_go) :=
  QRegister.block (8 + w_go) 1 (by dsimp [mOutUB]; omega)

/-- Local `b` (`5` bits) sub-register of `rMid`. -/
abbrev rBLoc (w_gi : ℕ) : QRegister 5 (mMidUB w_gi) :=
  QRegister.block 0 5 (by dsimp [mMidUB]; omega)

/-- Local `g_in` (`w_gi` bits) sub-register of `rMid`. -/
abbrev rGInLoc (w_gi : ℕ) : QRegister w_gi (mMidUB w_gi) :=
  QRegister.block 5 w_gi (by dsimp [mMidUB]; omega)

/-- Local `σ_in` (`1` bit) sub-register of `rMid`. -/
abbrev rSigInLoc (w_gi : ℕ) : QRegister 1 (mMidUB w_gi) :=
  QRegister.block (5 + w_gi) 1 (by dsimp [mMidUB]; omega)

/-- Ambient `x_o` (`8` bits) register inside `nUB w_go w_gi`. -/
abbrev rXoUB (w_go w_gi : ℕ) : QRegister 8 (nUB w_go w_gi) :=
  (rOutUB w_go w_gi).compose (rXoLoc w_go)

theorem disjoint_rSysUB_rOutUB (w_go w_gi : ℕ) :
    (rSysUB w_go w_gi).DisjointWires (rOutUB w_go w_gi) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have h := congrArg Fin.val heq
  simp [rSysUB, rOutUB] at h
  omega

theorem disjoint_rSysUB_rMidUB (w_go w_gi : ℕ) :
    (rSysUB w_go w_gi).DisjointWires (rMidUB w_go w_gi) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have h := congrArg Fin.val heq
  simp [rSysUB, rMidUB] at h
  omega

theorem disjoint_rOutUB_rMidUB (w_go w_gi : ℕ) :
    (rOutUB w_go w_gi).DisjointWires (rMidUB w_go w_gi) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have h := congrArg Fin.val heq
  simp [rOutUB, rMidUB] at h
  omega

theorem disjoint_rAllUB_rSysUB (w_go w_gi : ℕ) :
    (rAllUB w_go w_gi).DisjointWires (rSysUB w_go w_gi) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have h := congrArg Fin.val heq
  simp [rAllUB, rSysUB] at h
  omega

theorem rAllUB_eq_concat (w_go w_gi : ℕ) :
    rAllUB w_go w_gi =
      (rOutUB w_go w_gi).concat (rMidUB w_go w_gi) (disjoint_rOutUB_rMidUB w_go w_gi) := by
  ext idx
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
  · simp [rAllUB, rOutUB]
  · simp [rAllUB, rMidUB]
    omega

/-! ### Computational-Basis Block Splitting & `embedKet` -/

/-- Split `Fin (2 ^ (a + b))` into its low `a`-bit block and high `b`-bit block. -/
def splitBlockEquiv (a b : ℕ) : Fin (2 ^ (a + b)) ≃ Fin (2 ^ a) × Fin (2 ^ b) :=
  (basisBits (a + b)).trans
    (((Equiv.arrowCongr finSumFinEquiv (Equiv.refl (ZMod 2))).symm).trans
      ((Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (ZMod 2)).trans
        (Equiv.prodCongr (basisBits a).symm (basisBits b).symm)))

theorem splitBlockEquiv_fst (a b : ℕ) (x : Fin (2 ^ (a + b))) :
    (splitBlockEquiv a b x).1 = (QRegister.block 0 a (by omega)).extractIndex x := by
  apply (basisBits a).injective
  funext i
  change basisBits a (splitBlockEquiv a b x).1 i =
    basisBits a ((QRegister.block 0 a (by omega)).extractIndex x) i
  rw [QRegister.basisBits_extractIndex]
  simp only [splitBlockEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst,
    Equiv.apply_symm_apply]
  change basisBits (a + b) x (finSumFinEquiv (Sum.inl i)) =
    basisBits (a + b) x ((QRegister.block 0 a (by omega)).wires i)
  refine congrArg (basisBits (a + b) x) ?_
  ext
  simp

theorem splitBlockEquiv_snd (a b : ℕ) (x : Fin (2 ^ (a + b))) :
    (splitBlockEquiv a b x).2 = (QRegister.block a b (by omega)).extractIndex x := by
  apply (basisBits b).injective
  funext j
  change basisBits b (splitBlockEquiv a b x).2 j =
    basisBits b ((QRegister.block a b (by omega)).extractIndex x) j
  rw [QRegister.basisBits_extractIndex]
  simp only [splitBlockEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
    Equiv.apply_symm_apply]
  congr 1

/-- Three-factor computational-basis equivalence `(sys, out, mid)` on `nUB w_go w_gi`. -/
def ubSplitEquiv (w_go w_gi : ℕ) :
    Fin (2 ^ nUB w_go w_gi) ≃
      Fin (2 ^ (2 * 58)) × Fin (2 ^ mOutUB w_go) × Fin (2 ^ mMidUB w_gi) :=
  (splitBlockEquiv (2 * 58) (mAncUB w_go w_gi)).trans
    (Equiv.prodCongr (Equiv.refl _) (splitBlockEquiv (mOutUB w_go) (mMidUB w_gi)))

theorem ubSplitEquiv_apply (w_go w_gi : ℕ) (g : Fin (2 ^ nUB w_go w_gi)) :
    ubSplitEquiv w_go w_gi g =
      ((rSysUB w_go w_gi).extractIndex g,
       (rOutUB w_go w_gi).extractIndex g,
       (rMidUB w_go w_gi).extractIndex g) := by
  have hout : (QRegister.block 0 (mOutUB w_go) (by dsimp [mAncUB]; omega)).extractIndex
      ((rAllUB w_go w_gi).extractIndex g) = (rOutUB w_go w_gi).extractIndex g := by
    rw [← QRegister.extractIndex_compose]
    congr 1; ext i; simp [rAllUB, rOutUB]
  have hmid : (QRegister.block (mOutUB w_go) (mMidUB w_gi) (by dsimp [mAncUB]; omega)).extractIndex
      ((rAllUB w_go w_gi).extractIndex g) = (rMidUB w_go w_gi).extractIndex g := by
    rw [← QRegister.extractIndex_compose]
    congr 1; ext j; simp [rAllUB, rMidUB]; omega
  apply Prod.ext
  · simp only [ubSplitEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst,
      Equiv.refl_apply, splitBlockEquiv_fst]
  · apply Prod.ext
    · simp only [ubSplitEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
        splitBlockEquiv_fst, splitBlockEquiv_snd]
      exact hout
    · simp only [ubSplitEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
        splitBlockEquiv_snd]
      exact hmid

/-- Product state `|ψ⟩_sys ⊗ |o⟩_out ⊗ |m⟩_mid` inside `Fin (2 ^ nUB w_go w_gi) → ℂ`. -/
noncomputable def embedKet {w_go w_gi : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    Fin (2 ^ nUB w_go w_gi) → ℂ :=
  fun g ↦
    if (rOutUB w_go w_gi).extractIndex g = o ∧ (rMidUB w_go w_gi).extractIndex g = m then
      ψ ((rSysUB w_go w_gi).extractIndex g)
    else 0

theorem embedKet_zero_zero_eq_tensorState {w_go w_gi : ℕ} (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    embedKet (w_go := w_go) (w_gi := w_gi) ψ 0 0 =
      (rSysUB w_go w_gi).tensorState ψ (Pi.single 0 1) := by
  funext g
  have hiff : ((rOutUB w_go w_gi).extractIndex g = 0 ∧ (rMidUB w_go w_gi).extractIndex g = 0) ↔
      ((rSysUB w_go w_gi).basisSplitEquiv g).2 = 0 := by
    rw [Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
      Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
    constructor
    · rintro ⟨ho, hm⟩
      funext ⟨w, hw⟩
      change basisBits (nUB w_go w_gi) g w = 0
      have hge : 2 * 58 ≤ w.val := by
        by_contra hlt
        exact hw ⟨⟨w.val, by omega⟩, by ext; simp [rSysUB]⟩
      by_cases hlt : w.val < 2 * 58 + mOutUB w_go
      · have hw_eq : w = (rOutUB w_go w_gi) ⟨w.val - 2 * 58, by omega⟩ := by
          ext; simp [rOutUB]; omega
        rw [hw_eq]
        exact ho _
      · have hw_lt : w.val < nUB w_go w_gi := w.isLt
        have hw_eq : w = (rMidUB w_go w_gi)
            ⟨w.val - (2 * 58 + mOutUB w_go),
              by dsimp [nUB, mAncUB, mOutUB, mMidUB] at hw_lt ⊢; omega⟩ := by
          ext; simp [rMidUB]; omega
        rw [hw_eq]
        exact hm _
    · intro henv
      refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
      · have hnot : (rOutUB w_go w_gi) i ∉ Set.range (rSysUB w_go w_gi).wires := by
          rintro ⟨x, hx⟩; have hv := congrArg Fin.val hx; simp [rSysUB, rOutUB] at hv; omega
        exact congrFun henv ⟨_, hnot⟩
      · have hnot : (rMidUB w_go w_gi) j ∉ Set.range (rSysUB w_go w_gi).wires := by
          rintro ⟨x, hx⟩; have hv := congrArg Fin.val hx; simp [rSysUB, rMidUB] at hv; omega
        exact congrFun henv ⟨_, hnot⟩
  dsimp [embedKet, QRegister.tensorState]
  by_cases h : ((rSysUB w_go w_gi).basisSplitEquiv g).2 = 0
  · simp [hiff.mpr h, h]
  · have hn := mt hiff.mp h
    rcases not_and_or.mp hn with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

@[simp]
theorem embedKet_zero {w_go w_gi : ℕ} (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    embedKet (w_go := w_go) (w_gi := w_gi) 0 o m = 0 := by
  funext g; simp [embedKet]

theorem embedKet_smul {w_go w_gi : ℕ} (c : ℂ) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    embedKet (c • ψ) o m = c • embedKet ψ o m := by
  funext g; dsimp [embedKet]; split_ifs <;> simp

theorem embedKet_add {w_go w_gi : ℕ} (ψ₁ ψ₂ : Fin (2 ^ (2 * 58)) → ℂ)
    (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    embedKet (ψ₁ + ψ₂) o m = embedKet ψ₁ o m + embedKet ψ₂ o m := by
  funext g; dsimp [embedKet]; split_ifs <;> simp

theorem embedKet_sum {w_go w_gi : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin (2 ^ (2 * 58)) → ℂ)
    (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    embedKet (∑ i ∈ s, f i) o m = ∑ i ∈ s, embedKet (f i) o m := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih => rw [Finset.sum_cons, Finset.sum_cons, embedKet_add, ih]

private theorem embedMatrix_mulVec_apply_replaceIndex {n m : ℕ} (r : QRegister m n)
    (A : Operator (2 ^ m)) (v : Fin (2 ^ n) → ℂ) (g : Fin (2 ^ n)) :
    (r.embedMatrix A *ᵥ v) g =
      ∑ j : Fin (2 ^ m), A (r.extractIndex g) j * v (r.replaceIndex g j) :=
  r.embedMatrix_mulVec_apply A v g

theorem embedMatrix_rSysUB_mulVec_embedKet {w_go w_gi : ℕ}
    (A : Operator (2 ^ (2 * 58))) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    ((rSysUB w_go w_gi).embedMatrix A) *ᵥ embedKet ψ o m = embedKet (A *ᵥ ψ) o m := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex]
  have ho (s' : Fin (2 ^ (2 * 58))) :
      (rOutUB w_go w_gi).extractIndex ((rSysUB w_go w_gi).replaceIndex g s') =
        (rOutUB w_go w_gi).extractIndex g :=
    (rOutUB w_go w_gi).extractIndex_replaceIndex_of_disjoint _
      (QRegister.disjoint_comm.mp (disjoint_rSysUB_rOutUB w_go w_gi)) g s'
  have hm (s' : Fin (2 ^ (2 * 58))) :
      (rMidUB w_go w_gi).extractIndex ((rSysUB w_go w_gi).replaceIndex g s') =
        (rMidUB w_go w_gi).extractIndex g :=
    (rMidUB w_go w_gi).extractIndex_replaceIndex_of_disjoint _
      (QRegister.disjoint_comm.mp (disjoint_rSysUB_rMidUB w_go w_gi)) g s'
  have hsum :
      (∑ s' : Fin (2 ^ (2 * 58)),
        A ((rSysUB w_go w_gi).extractIndex g) s' *
          embedKet ψ o m ((rSysUB w_go w_gi).replaceIndex g s')) =
      ∑ s' : Fin (2 ^ (2 * 58)),
        A ((rSysUB w_go w_gi).extractIndex g) s' *
          if (rOutUB w_go w_gi).extractIndex g = o ∧ (rMidUB w_go w_gi).extractIndex g = m then
            ψ s'
          else 0 := by
    refine Finset.sum_congr rfl fun s' _ ↦ ?_
    dsimp [embedKet]
    rw [ho, hm, QRegister.extractIndex_replaceIndex]
  rw [hsum]
  dsimp [embedKet]
  by_cases h : (rOutUB w_go w_gi).extractIndex g = o ∧ (rMidUB w_go w_gi).extractIndex g = m
  · simp [h, Matrix.mulVec, dotProduct]
  · simp [h]

theorem embedMatrix_rOutUB_mulVec_embedKet {w_go w_gi : ℕ}
    (B : Operator (2 ^ mOutUB w_go)) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    ((rOutUB w_go w_gi).embedMatrix B) *ᵥ embedKet ψ o m =
      ∑ o' : Fin (2 ^ mOutUB w_go), (B o' o) • embedKet ψ o' m := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex, Finset.sum_apply]
  have hs (o' : Fin (2 ^ mOutUB w_go)) :
      (rSysUB w_go w_gi).extractIndex ((rOutUB w_go w_gi).replaceIndex g o') =
        (rSysUB w_go w_gi).extractIndex g :=
    (rSysUB w_go w_gi).extractIndex_replaceIndex_of_disjoint _
      (disjoint_rSysUB_rOutUB w_go w_gi) g o'
  have hm (o' : Fin (2 ^ mOutUB w_go)) :
      (rMidUB w_go w_gi).extractIndex ((rOutUB w_go w_gi).replaceIndex g o') =
        (rMidUB w_go w_gi).extractIndex g :=
    (rMidUB w_go w_gi).extractIndex_replaceIndex_of_disjoint _
      (QRegister.disjoint_comm.mp (disjoint_rOutUB_rMidUB w_go w_gi)) g o'
  have hsum :
      (∑ o' : Fin (2 ^ mOutUB w_go),
        B ((rOutUB w_go w_gi).extractIndex g) o' *
          embedKet ψ o m ((rOutUB w_go w_gi).replaceIndex g o')) =
      ∑ o' : Fin (2 ^ mOutUB w_go),
        B ((rOutUB w_go w_gi).extractIndex g) o' *
          if o' = o ∧ (rMidUB w_go w_gi).extractIndex g = m then
            ψ ((rSysUB w_go w_gi).extractIndex g)
          else 0 := by
    refine Finset.sum_congr rfl fun o' _ ↦ ?_
    dsimp [embedKet]
    rw [hs, hm, QRegister.extractIndex_replaceIndex]
  rw [hsum]
  dsimp [embedKet]
  by_cases hmg : (rMidUB w_go w_gi).extractIndex g = m
  · rw [Finset.sum_eq_single o, Finset.sum_eq_single ((rOutUB w_go w_gi).extractIndex g)]
    · simp [hmg]
    · intro o' _ ho'; simp [ho'.symm]
    · simp
    · intro o' _ ho'; simp [ho']
    · simp
  · simp [hmg]

theorem embedMatrix_rMidUB_mulVec_embedKet {w_go w_gi : ℕ}
    (C : Operator (2 ^ mMidUB w_gi)) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    ((rMidUB w_go w_gi).embedMatrix C) *ᵥ embedKet ψ o m =
      ∑ m' : Fin (2 ^ mMidUB w_gi), (C m' m) • embedKet ψ o m' := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex, Finset.sum_apply]
  have hs (m' : Fin (2 ^ mMidUB w_gi)) :
      (rSysUB w_go w_gi).extractIndex ((rMidUB w_go w_gi).replaceIndex g m') =
        (rSysUB w_go w_gi).extractIndex g :=
    (rSysUB w_go w_gi).extractIndex_replaceIndex_of_disjoint _
      (disjoint_rSysUB_rMidUB w_go w_gi) g m'
  have ho (m' : Fin (2 ^ mMidUB w_gi)) :
      (rOutUB w_go w_gi).extractIndex ((rMidUB w_go w_gi).replaceIndex g m') =
        (rOutUB w_go w_gi).extractIndex g :=
    (rOutUB w_go w_gi).extractIndex_replaceIndex_of_disjoint _
      (disjoint_rOutUB_rMidUB w_go w_gi) g m'
  have hsum :
      (∑ m' : Fin (2 ^ mMidUB w_gi),
        C ((rMidUB w_go w_gi).extractIndex g) m' *
          embedKet ψ o m ((rMidUB w_go w_gi).replaceIndex g m')) =
      ∑ m' : Fin (2 ^ mMidUB w_gi),
        C ((rMidUB w_go w_gi).extractIndex g) m' *
          if (rOutUB w_go w_gi).extractIndex g = o ∧ m' = m then
            ψ ((rSysUB w_go w_gi).extractIndex g)
          else 0 := by
    refine Finset.sum_congr rfl fun m' _ ↦ ?_
    dsimp [embedKet]
    rw [hs, ho, QRegister.extractIndex_replaceIndex]
  rw [hsum]
  dsimp [embedKet]
  by_cases hog : (rOutUB w_go w_gi).extractIndex g = o
  · rw [Finset.sum_eq_single m, Finset.sum_eq_single ((rMidUB w_go w_gi).extractIndex g)]
    · simp [hog]
    · intro m' _ hm'; simp [hm'.symm]
    · simp
    · intro m' _ hm'; simp [hm']
    · simp
  · simp [hog]

theorem projMid_mulVec_embedKet {w_go w_gi : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    ((rMidUB w_go w_gi).basisOutcomeProjector 0) *ᵥ embedKet ψ o m =
      if m = 0 then embedKet ψ o 0 else 0 := by
  funext g
  rw [(rMidUB w_go w_gi).basisOutcomeProjector_mulVec]
  by_cases hm0 : m = 0
  · subst hm0
    dsimp [embedKet]
    by_cases hg : (rMidUB w_go w_gi).extractIndex g = 0 <;> simp [hg]
  · simp only [hm0, ↓reduceIte, Pi.zero_apply]
    dsimp [embedKet]
    by_cases hg : (rMidUB w_go w_gi).extractIndex g = 0 <;> simp [hg, Ne.symm hm0]

theorem projAll_mulVec_embedKet {w_go w_gi : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o : Fin (2 ^ mOutUB w_go)) (m : Fin (2 ^ mMidUB w_gi)) :
    ((rAllUB w_go w_gi).basisOutcomeProjector 0) *ᵥ embedKet ψ o m =
      if o = 0 ∧ m = 0 then embedKet ψ 0 0 else 0 := by
  have hall0 (g : Fin (2 ^ nUB w_go w_gi)) :
      (rAllUB w_go w_gi).extractIndex g = 0 ↔
        (rOutUB w_go w_gi).extractIndex g = 0 ∧ (rMidUB w_go w_gi).extractIndex g = 0 := by
    rw [rAllUB_eq_concat, Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
      Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
      Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
    constructor
    · intro h
      exact ⟨fun i ↦ by simpa using h (Fin.castAdd _ i),
        fun j ↦ by simpa using h (Fin.natAdd _ j)⟩
    · rintro ⟨ho, hm⟩ idx
      obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
      · simpa using ho i
      · simpa using hm j
  funext g
  rw [(rAllUB w_go w_gi).basisOutcomeProjector_mulVec]
  by_cases hom : o = 0 ∧ m = 0
  · rcases hom with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte]
    dsimp [embedKet]
    by_cases hg : (rAllUB w_go w_gi).extractIndex g = 0
    · obtain ⟨ho0, hm0⟩ := (hall0 g).mp hg
      simp [hg, ho0, hm0]
    · have hn := mt (hall0 g).mpr hg
      rcases not_and_or.mp hn with ho0 | hm0
      · simp [hg, ho0]
      · simp [hg, hm0]
  · simp only [hom, ↓reduceIte, Pi.zero_apply]
    dsimp [embedKet]
    by_cases hg : (rAllUB w_go w_gi).extractIndex g = 0
    · obtain ⟨ho0, hm0⟩ := (hall0 g).mp hg
      rcases not_and_or.mp hom with ho | hm
      · simp [hg, ho0, hm0, Ne.symm ho]
      · simp [hg, ho0, hm0, Ne.symm hm]
    · simp [hg]

private theorem basisOutcomeProjector_mul_eq_ite {k n : ℕ} (r : QRegister k n)
    (a b : Fin (2 ^ k)) :
    r.basisOutcomeProjector a * r.basisOutcomeProjector b =
      if a = b then r.basisOutcomeProjector a else 0 := by
  by_cases hab : a = b
  · subst hab; simp [r.basisOutcomeProjector_mul_self]
  · rw [ite_eq_right hab, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases ha : r.extractIndex i = a <;> simp [ha, hab]
    · simp [Matrix.diagonal_apply_ne _ hij]

/-- Computational-basis multiplexed unitary: applies `F c` on `rTgt` when `rCtrl` holds basis
value `c : Fin (2 ^ k_c)`. -/
noncomputable def muxUnitary {n k_c k_t : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    (hdisj : rCtrl.DisjointWires rTgt)
    (F : Fin (2 ^ k_c) → Unitary (2 ^ k_t)) : Unitary (2 ^ n) :=
  ⟨∑ c : Fin (2 ^ k_c), rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1, by
    have hcomm (c : Fin (2 ^ k_c)) (A : Operator (2 ^ k_t)) :
        rCtrl.basisOutcomeProjector c * rTgt.embedMatrix A =
          rTgt.embedMatrix A * rCtrl.basisOutcomeProjector c :=
      rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj (compProj c) A
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
    have hterm_adj (c : Fin (2 ^ k_c)) :
        (rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1)ᴴ =
          rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1ᴴ := by
      rw [Matrix.conjTranspose_mul, rCtrl.basisOutcomeProjector_conjTranspose,
        ← rTgt.embedMatrix_conjTranspose, hcomm]
    simp_rw [hterm_adj]
    rw [Finset.sum_mul]
    trans ∑ c : Fin (2 ^ k_c), rCtrl.basisOutcomeProjector c
    · refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [Finset.mul_sum, Finset.sum_eq_single c]
      · have hFc : (F c).1ᴴ * (F c).1 = 1 := by
          rw [← Matrix.star_eq_conjTranspose]; exact (F c).2.1
        calc (rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1ᴴ) *
              (rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1)
            = rCtrl.basisOutcomeProjector c *
                (rTgt.embedMatrix (F c).1ᴴ * rCtrl.basisOutcomeProjector c) *
                rTgt.embedMatrix (F c).1 := by simp only [Matrix.mul_assoc]
          _ = (rCtrl.basisOutcomeProjector c * rCtrl.basisOutcomeProjector c) *
                (rTgt.embedMatrix (F c).1ᴴ * rTgt.embedMatrix (F c).1) := by
              rw [← hcomm]; simp only [Matrix.mul_assoc]
          _ = rCtrl.basisOutcomeProjector c := by
              rw [rCtrl.basisOutcomeProjector_mul_self, ← rTgt.embedMatrix_mul, hFc,
                rTgt.embedMatrix_one, mul_one]
      · intro c' _ hne
        calc (rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1ᴴ) *
              (rCtrl.basisOutcomeProjector c' * rTgt.embedMatrix (F c').1)
            = rTgt.embedMatrix (F c).1ᴴ *
                (rCtrl.basisOutcomeProjector c * rCtrl.basisOutcomeProjector c') *
                rTgt.embedMatrix (F c').1 := by
              rw [hcomm]; simp only [Matrix.mul_assoc]
          _ = 0 := by
              rw [basisOutcomeProjector_mul_eq_ite, ite_eq_right hne.symm, mul_zero, zero_mul]
      · simp
    · exact rCtrl.sum_basisOutcomeProjector⟩

@[simp]
theorem muxUnitary_inv {n k_c k_t : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    (hdisj : rCtrl.DisjointWires rTgt)
    (F : Fin (2 ^ k_c) → Unitary (2 ^ k_t)) :
    (muxUnitary rCtrl rTgt hdisj F)⁻¹ =
      muxUnitary rCtrl rTgt hdisj (fun c ↦ (F c)⁻¹) := by
  apply Subtype.ext
  change (muxUnitary rCtrl rTgt hdisj F).1ᴴ = _
  dsimp only [muxUnitary]
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hcomm : rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1ᴴ =
      rTgt.embedMatrix (F c).1ᴴ * rCtrl.basisOutcomeProjector c :=
    rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj (compProj c) (F c).1ᴴ
  rw [Matrix.conjTranspose_mul, rCtrl.basisOutcomeProjector_conjTranspose,
    ← rTgt.embedMatrix_conjTranspose, ← hcomm]
  rfl

theorem muxUnitary_mulVec_of_proj {n k_c k_t : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    (hdisj : rCtrl.DisjointWires rTgt)
    (F : Fin (2 ^ k_c) → Unitary (2 ^ k_t))
    (c₀ : Fin (2 ^ k_c)) (v : Fin (2 ^ n) → ℂ)
    (hv : ∀ g, rCtrl.extractIndex g ≠ c₀ → v g = 0) :
    (muxUnitary rCtrl rTgt hdisj F).1 *ᵥ v = (rTgt.embedMatrix (F c₀).1) *ᵥ v := by
  dsimp only [muxUnitary]
  rw [sum_mulVec_eq, Finset.sum_eq_single c₀]
  · have hcomm : rCtrl.basisOutcomeProjector c₀ * rTgt.embedMatrix (F c₀).1 =
        rTgt.embedMatrix (F c₀).1 * rCtrl.basisOutcomeProjector c₀ :=
      rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj (compProj c₀) (F c₀).1
    rw [hcomm, ← Matrix.mulVec_mulVec]
    congr 1
    funext g
    rw [rCtrl.basisOutcomeProjector_mulVec]
    by_cases h : rCtrl.extractIndex g = c₀
    · simp [h]
    · simp [h, hv g h]
  · intro c _ hne
    have hcomm : rCtrl.basisOutcomeProjector c * rTgt.embedMatrix (F c).1 =
        rTgt.embedMatrix (F c).1 * rCtrl.basisOutcomeProjector c :=
      rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj (compProj c) (F c).1
    rw [hcomm, ← Matrix.mulVec_mulVec]
    have hzero : rCtrl.basisOutcomeProjector c *ᵥ v = 0 := by
      funext g
      rw [rCtrl.basisOutcomeProjector_mulVec, Pi.zero_apply]
      by_cases h : rCtrl.extractIndex g = c
      · exact (ite_eq_left h).trans (hv g (h ▸ hne))
      · exact ite_eq_right h
    rw [hzero, Matrix.mulVec_zero]
  · simp

/-! ### `58`-Pair Controlled-SWAP Circuit & Center `CZ` Gate -/

private theorem embedMatrix_perm_mulVec_single {n m : ℕ} (r : QRegister m n)
    (π : Equiv.Perm (Fin (2 ^ m))) (g : Fin (2 ^ n)) :
    (r.embedMatrix (Operator.permutationUnitary π).1) *ᵥ Pi.single g 1 =
      Pi.single (r.replaceIndex g (π (r.extractIndex g))) 1 := by
  rw [r.embedMatrix_mulVec_single_factors, Operator.permutationUnitary_mulVec_single,
    r.tensorState_single_replaceIndex]

/-- Three-qubit Fredkin (controlled-SWAP) circuit `CNOT 2 1 ;;ᶜ TOFF 0 1 2 ;;ᶜ CNOT 2 1` (`1`
`TOFF`, `0` `T`). -/
def fredkin3 : Circuit 3 :=
  Circuit.CNOT 2 1 (by decide) ;;ᶜ
    Circuit.TOFF 0 1 2 (by decide) (by decide) (by decide) ;;ᶜ
    Circuit.CNOT 2 1 (by decide)

@[simp]
theorem fredkin3_count_t : fredkin3.count .T = 0 := by decide

@[simp]
theorem fredkin3_count_toff : fredkin3.count .TOFF = 1 := by decide

/-- Basis-index permutation on `3` qubits for `fredkin3` (swaps bits `1` and `2` when bit `0` is
`1`, i.e. swaps `3 ↔ 5`). -/
def fredkin3Perm : Equiv.Perm (Fin (2 ^ 3)) := Equiv.swap 3 5

theorem fredkin3_eval : fredkin3.eval = Operator.permutationUnitary fredkin3Perm := by
  have hg (g : Fin (2 ^ 3)) :
      fredkin3.eval.1 *ᵥ Pi.single g 1 =
        (Operator.permutationUnitary fredkin3Perm).1 *ᵥ Pi.single g 1 := by
    have h1 : (Circuit.CNOT (2 : Wire 3) 1 (by decide)).eval =
        (QRegister.pair (2 : Wire 3) 1 (by decide)).embedUnitary
          (Operator.permutationUnitary (Equiv.swap (1 : Fin 4) (3 : Fin 4))) := rfl
    have h2 : (Circuit.TOFF (0 : Wire 3) 1 2 (by decide) (by decide) (by decide)).eval =
        (QRegister.triple (0 : Wire 3) 1 2 (by decide) (by decide) (by decide)).embedUnitary
          (Operator.permutationUnitary (Equiv.swap (3 : Fin 8) (7 : Fin 8))) := rfl
    dsimp only [fredkin3, Circuit.eval_seq, Submonoid.coe_mul]
    rw [h1, h2, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      embedMatrix_perm_mulVec_single, embedMatrix_perm_mulVec_single,
      embedMatrix_perm_mulVec_single, Operator.permutationUnitary_mulVec_single]
    congr 1
    fin_cases g <;> decide
  apply Subtype.ext
  ext i g
  have h := congrFun (hg g) i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact h

theorem basisBits_fredkin3Perm (x : Fin (2 ^ 3)) (q : Wire 3) :
    basisBits 3 (fredkin3Perm x) q =
      if basisBits 3 x 0 = 1 then basisBits 3 x (Equiv.swap 1 2 q) else basisBits 3 x q := by
  fin_cases x <;> fin_cases q <;> decide

/-- `k`-prefix of the `N`-pair controlled-SWAP circuit on `1 + 2 * N` wires (`wire 0` controls
swapping `wire (1 + p)` with `wire (1 + N + p)` for `p < k`). -/
def cswapPrefixCircuit (N : ℕ) : (k : ℕ) → k ≤ N → Circuit (1 + 2 * N)
  | 0, _ => .identity
  | k + 1, hk =>
      cswapPrefixCircuit N k (by omega) ;;ᶜ
        fredkin3.onRegister
          (QRegister.triple ⟨0, by omega⟩ ⟨1 + k, by omega⟩ ⟨1 + N + k, by omega⟩
            (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
            (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
            (by intro h; have := congrArg Fin.val h; dsimp at this; omega))

/-- Full `N`-pair controlled-SWAP circuit on `1 + 2 * N` wires (`N` `TOFF`s, `0` `T`). -/
def cswapBlockCircuit (N : ℕ) : Circuit (1 + 2 * N) :=
  cswapPrefixCircuit N N le_rfl

theorem cswapPrefixCircuit_count_t (N : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N), (cswapPrefixCircuit N k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, hk => by simp [cswapPrefixCircuit, cswapPrefixCircuit_count_t N k (by omega)]

theorem cswapPrefixCircuit_count_toff (N : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N), (cswapPrefixCircuit N k hk).count .TOFF = k
  | 0, _ => rfl
  | k + 1, hk => by
      simp only [cswapPrefixCircuit, Circuit.count_seq, Circuit.count_onRegister,
        fredkin3_count_toff, cswapPrefixCircuit_count_toff N k (by omega)]

@[simp]
theorem cswapBlockCircuit_count_t (N : ℕ) : (cswapBlockCircuit N).count .T = 0 :=
  cswapPrefixCircuit_count_t N N le_rfl

@[simp]
theorem cswapBlockCircuit_count_toff (N : ℕ) : (cswapBlockCircuit N).count .TOFF = N :=
  cswapPrefixCircuit_count_toff N N le_rfl

/-- Underlying wire map on `2 * N` swapping `p ↔ N + p` for `p < k` (`k ≤ N`). -/
def spinSwapPrefixWireMap (N k : ℕ) (hk : k ≤ N) (w : Wire (2 * N)) : Wire (2 * N) :=
  if h1 : w.val < k then ⟨N + w.val, by omega⟩
  else if h2 : N ≤ w.val ∧ w.val < N + k then ⟨w.val - N, by omega⟩
  else w

theorem spinSwapPrefixWireMap_involutive (N k : ℕ) (hk : k ≤ N) (w : Wire (2 * N)) :
    spinSwapPrefixWireMap N k hk (spinSwapPrefixWireMap N k hk w) = w := by
  by_cases h1 : w.val < k
  · have hs1 : spinSwapPrefixWireMap N k hk w = ⟨N + w.val, by omega⟩ := by
      unfold spinSwapPrefixWireMap; exact dite_eq_left h1
    rw [hs1]
    unfold spinSwapPrefixWireMap
    have hn1 : ¬ (N + w.val < k) := by omega
    have hn2 : N ≤ N + w.val ∧ N + w.val < N + k := by omega
    rw [dite_eq_right hn1, dite_eq_left hn2]
    ext; dsimp; omega
  · by_cases h2 : N ≤ w.val ∧ w.val < N + k
    · have hs1 : spinSwapPrefixWireMap N k hk w = ⟨w.val - N, by omega⟩ := by
        unfold spinSwapPrefixWireMap; rw [dite_eq_right h1, dite_eq_left h2]
      rw [hs1]
      unfold spinSwapPrefixWireMap
      have hy : w.val - N < k := by omega
      rw [dite_eq_left hy]
      ext; dsimp; omega
    · have hs1 : spinSwapPrefixWireMap N k hk w = w := by
        unfold spinSwapPrefixWireMap; rw [dite_eq_right h1, dite_eq_right h2]
      rw [hs1, hs1]

/-- Wire permutation on `2 * N` swapping `p ↔ N + p` for `p < k` (`k ≤ N`). -/
def spinSwapPrefixWirePerm (N k : ℕ) (hk : k ≤ N) : Equiv.Perm (Wire (2 * N)) where
  toFun := spinSwapPrefixWireMap N k hk
  invFun := spinSwapPrefixWireMap N k hk
  left_inv := spinSwapPrefixWireMap_involutive N k hk
  right_inv := spinSwapPrefixWireMap_involutive N k hk

/-- Basis-index permutation on `2 * N` qubits swapping `p ↔ N + p` for `p < N`. -/
def spinSwapEquiv (N : ℕ) : Equiv.Perm (Fin (2 ^ (2 * N))) :=
  (basisBits (2 * N)).trans
    ((Equiv.arrowCongr (spinSwapPrefixWirePerm N N le_rfl) (Equiv.refl (ZMod 2))).trans
      (basisBits (2 * N)).symm)

theorem basisBits_spinSwapEquiv (N : ℕ) (x : Fin (2 ^ (2 * N))) (w : Wire (2 * N)) :
    basisBits (2 * N) (spinSwapEquiv N x) w =
      basisBits (2 * N) x (spinSwapPrefixWirePerm N N le_rfl w) := by
  simp only [spinSwapEquiv, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.arrowCongr_apply]
  rfl

theorem spinSwapEquiv_eq_symm_bits (N : ℕ) (x : Fin (2 ^ (2 * N))) :
    spinSwapEquiv N x =
      (basisBits (2 * N)).symm (fun w ↦
        basisBits (2 * N) x (spinSwapPrefixWirePerm N N le_rfl w)) := by
  apply (basisBits (2 * N)).injective
  funext w
  rw [Equiv.apply_symm_apply]
  exact basisBits_spinSwapEquiv N x w

theorem spinSwapEquiv_involutive (N : ℕ) (x : Fin (2 ^ (2 * N))) :
    spinSwapEquiv N (spinSwapEquiv N x) = x := by
  apply (basisBits (2 * N)).injective
  funext w
  rw [basisBits_spinSwapEquiv, basisBits_spinSwapEquiv]
  exact congrArg (basisBits (2 * N) x) (spinSwapPrefixWireMap_involutive N N le_rfl w)

theorem spinSwapEquiv_symm (N : ℕ) : (spinSwapEquiv N).symm = spinSwapEquiv N := by
  apply Equiv.ext
  intro x
  rw [Equiv.symm_apply_eq, spinSwapEquiv_involutive]

theorem spinSwapUnitary_conj_block0 (N : ℕ) (A : Operator (2 ^ N))
    (h0 : 0 + N ≤ 2 * N := by omega) (h1 : N + N ≤ 2 * N := by omega) :
    (Operator.permutationUnitary (spinSwapEquiv N)).1 *
        (QRegister.block 0 N h0).embedMatrix A *
        (Operator.permutationUnitary (spinSwapEquiv N)).1ᴴ =
      (QRegister.block N N h1).embedMatrix A := by
  have hU_apply (a b : Fin (2 ^ (2 * N))) :
      (Operator.permutationUnitary (spinSwapEquiv N)).1 a b =
        if spinSwapEquiv N b = a then 1 else 0 := by
    have h := congrFun (Operator.permutationUnitary_mulVec_single (spinSwapEquiv N) b (1 : ℂ)) a
    rw [Matrix.mulVec_single_one] at h
    change (Operator.permutationUnitary (spinSwapEquiv N)).1 a b = _ at h
    rw [h, Pi.single_apply]
    by_cases hab : a = spinSwapEquiv N b <;> simp [hab, eq_comm]
  have hinv (a b : Fin (2 ^ (2 * N))) :
      (spinSwapEquiv N b = a) ↔ (b = spinSwapEquiv N a) := by
    rw [← (spinSwapEquiv N).eq_symm_apply, spinSwapEquiv_symm, eq_comm]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (spinSwapEquiv N j)]
  · rw [Matrix.conjTranspose_apply, hU_apply, ite_eq_left (spinSwapEquiv_involutive N j),
      star_one, mul_one, Matrix.mul_apply, Finset.sum_eq_single (spinSwapEquiv N i)]
    · rw [hU_apply, ite_eq_left (spinSwapEquiv_involutive N i), one_mul,
        QRegister.embedMatrix_apply_of_agreeOutside,
        QRegister.embedMatrix_apply_of_agreeOutside]
      have hex (z : Fin (2 ^ (2 * N))) :
          (QRegister.block 0 N h0).extractIndex (spinSwapEquiv N z) =
            (QRegister.block N N h1).extractIndex z := by
        apply (basisBits N).injective
        funext p
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
          basisBits_spinSwapEquiv]
        refine congrArg (basisBits (2 * N) z) ?_
        change spinSwapPrefixWireMap N N le_rfl ((QRegister.block 0 N h0).wires p) =
          (QRegister.block N N h1).wires p
        unfold spinSwapPrefixWireMap
        have hp0 : ((QRegister.block 0 N h0).wires p).val < N := by simp
        rw [dite_eq_left hp0]
        ext; simp
      have hagr : (QRegister.block 0 N h0).AgreeOutside (spinSwapEquiv N i) (spinSwapEquiv N j) ↔
          (QRegister.block N N h1).AgreeOutside i j := by
        constructor
        · intro ha w hw
          have hwlt : w.val < N := by
            by_contra hge
            exact hw ⟨⟨w.val - N, by omega⟩, by ext; simp; omega⟩
          let w' : Wire (2 * N) := ⟨N + w.val, by omega⟩
          have hw' : w' ∉ Set.range (QRegister.block 0 N h0).wires := by
            rintro ⟨q, hq⟩; have hv := congrArg Fin.val hq; simp [w'] at hv; omega
          have hstep := ha w' hw'
          rw [basisBits_spinSwapEquiv, basisBits_spinSwapEquiv] at hstep
          have hmap : spinSwapPrefixWirePerm N N le_rfl w' = w := by
            change spinSwapPrefixWireMap N N le_rfl w' = w
            unfold spinSwapPrefixWireMap
            have hn1 : ¬ (w'.val < N) := by dsimp [w']; omega
            have hn2 : N ≤ w'.val ∧ w'.val < N + N := by dsimp [w']; omega
            rw [dite_eq_right hn1, dite_eq_left hn2]
            ext; dsimp [w']; omega
          rwa [hmap] at hstep
        · intro ha w hw
          have hwge : N ≤ w.val := by
            by_contra hlt
            exact hw ⟨⟨w.val, by omega⟩, by ext; simp⟩
          let w' : Wire (2 * N) := ⟨w.val - N, by omega⟩
          have hw' : w' ∉ Set.range (QRegister.block N N h1).wires := by
            rintro ⟨q, hq⟩; have hv := congrArg Fin.val hq; simp [w'] at hv; omega
          have hstep := ha w' hw'
          rw [basisBits_spinSwapEquiv, basisBits_spinSwapEquiv]
          have hmap : spinSwapPrefixWirePerm N N le_rfl w = w' := by
            change spinSwapPrefixWireMap N N le_rfl w = w'
            unfold spinSwapPrefixWireMap
            have hn1 : ¬ (w.val < N) := by omega
            have hn2 : N ≤ w.val ∧ w.val < N + N := by omega
            rw [dite_eq_right hn1, dite_eq_left hn2]
          rwa [hmap]
      rw [hex i, hex j]
      by_cases h : (QRegister.block N N h1).AgreeOutside i j <;> simp [hagr, h]
    · intro k _ hk
      rw [hU_apply, ite_eq_right (mt (hinv i k).mp hk), zero_mul]
    · simp
  · intro l _ hl
    rw [Matrix.conjTranspose_apply, hU_apply, ite_eq_right (mt (hinv j l).mp hl),
      star_zero, mul_zero]
  · simp

theorem cswapBlockCircuit_eval (N : ℕ) :
    (cswapBlockCircuit N).eval =
      muxUnitary (QRegister.singleton 0) (QRegister.block 1 (2 * N) (by omega))
        (by
          rw [QRegister.disjoint_iff]
          intro i j heq
          have hv := congrArg Fin.val heq
          fin_cases i
          simp at hv
          omega)
        (fun σ ↦ if σ = 0 then 1 else Operator.permutationUnitary (spinSwapEquiv N)) := by
  let rCtrl : QRegister 1 (1 + 2 * N) := QRegister.singleton 0
  let rBlk : QRegister (2 * N) (1 + 2 * N) := QRegister.block 1 (2 * N) (by omega)
  have hdisj : rCtrl.DisjointWires rBlk := by
    rw [QRegister.disjoint_iff]; intro i j heq; fin_cases i
    have hv := congrArg Fin.val heq; simp [rCtrl, rBlk] at hv; omega
  let stepPerm : (k : ℕ) → k ≤ N → Fin (2 ^ (1 + 2 * N)) → Fin (2 ^ (1 + 2 * N)) :=
    fun k hk g ↦
      if basisBits (1 + 2 * N) g 0 = 0 then g
      else rBlk.replaceIndex g
        ((basisBits (2 * N)).symm fun w ↦
          basisBits (2 * N) (rBlk.extractIndex g) (spinSwapPrefixWirePerm N k hk w))
  have hpref : ∀ (k : ℕ) (hk : k ≤ N) (g : Fin (2 ^ (1 + 2 * N))),
      (cswapPrefixCircuit N k hk).eval.1 *ᵥ Pi.single g 1 = Pi.single (stepPerm k hk g) 1 := by
    intro k hk
    induction k with
    | zero =>
        intro g
        simp only [cswapPrefixCircuit, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
        congr 1
        dsimp [stepPerm]
        split_ifs with h0
        · rfl
        · have hid : ((basisBits (2 * N)).symm fun w ↦
              basisBits (2 * N) (rBlk.extractIndex g) (spinSwapPrefixWirePerm N 0 hk w)) =
                rBlk.extractIndex g := by
            have hpw : ∀ w, spinSwapPrefixWirePerm N 0 hk w = w := fun w ↦ by
              change spinSwapPrefixWireMap N 0 hk w = w
              unfold spinSwapPrefixWireMap
              have hn1 : ¬ (w.val < 0) := by omega
              have hn2 : ¬ (N ≤ w.val ∧ w.val < N + 0) := by omega
              rw [dite_eq_right hn1, dite_eq_right hn2]
            simp_rw [hpw]
            exact (basisBits (2 * N)).symm_apply_apply (rBlk.extractIndex g)
          rw [hid, rBlk.replaceIndex_extractIndex]
    | succ k ih =>
        intro g
        let rTr := QRegister.triple (⟨0, by omega⟩ : Wire (1 + 2 * N))
          ⟨1 + k, by omega⟩ ⟨1 + N + k, by omega⟩
          (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
          (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
          (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
        simp only [cswapPrefixCircuit, Circuit.eval_seq, Circuit.eval_onRegister,
          Submonoid.coe_mul, QRegister.embedUnitary_val, ← Matrix.mulVec_mulVec,
          ih (by omega) g, fredkin3_eval, embedMatrix_perm_mulVec_single]
        congr 1
        let g₁ := stepPerm k (by omega) g
        change rTr.replaceIndex g₁ (fredkin3Perm (rTr.extractIndex g₁)) = stepPerm (k + 1) hk g
        apply (basisBits (1 + 2 * N)).injective
        funext q
        have hbit0_g₁ : basisBits (1 + 2 * N) g₁ 0 = basisBits (1 + 2 * N) g 0 := by
          dsimp [g₁, stepPerm]
          split_ifs with h0
          · rfl
          · have hnot : (0 : Wire (1 + 2 * N)) ∉ Set.range rBlk.wires := by
              rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi; simp [rBlk] at hv
            exact rBlk.basisBits_replaceIndex_of_not_mem g _ 0 hnot
        have htr0 : basisBits 3 (rTr.extractIndex g₁) 0 = basisBits (1 + 2 * N) g 0 := by
          rw [rTr.basisBits_extractIndex]; exact hbit0_g₁
        by_cases h0 : basisBits (1 + 2 * N) g 0 = 0
        · have hg₁ : g₁ = g := by dsimp [g₁, stepPerm]; rw [ite_eq_left h0]
          have hfp : fredkin3Perm (rTr.extractIndex g₁) = rTr.extractIndex g₁ := by
            apply (basisBits 3).injective; funext j
            rw [basisBits_fredkin3Perm, htr0, h0]; simp
          rw [hfp, rTr.replaceIndex_extractIndex, hg₁]
          dsimp [stepPerm]; rw [ite_eq_left h0]
        · have h1 : basisBits (1 + 2 * N) g 0 = 1 := by
            rcases hval : basisBits (1 + 2 * N) g 0 with ⟨v, hv⟩
            interval_cases v
            · exact (h0 hval).elim
            · rfl
          have hg₁_bit (u : Wire (2 * N)) :
              basisBits (1 + 2 * N) g₁ ⟨1 + u.val, by omega⟩ =
                basisBits (1 + 2 * N) g
                  ⟨1 + (spinSwapPrefixWirePerm N k (by omega) u).val, by omega⟩ := by
            dsimp [g₁, stepPerm]
            rw [ite_eq_right h0]
            have hrBlk_u : rBlk u = ⟨1 + u.val, by omega⟩ := by ext; simp [rBlk]
            rw [← hrBlk_u, rBlk.basisBits_replaceIndex_apply]
            change ((basisBits (2 * N)) ((basisBits (2 * N)).symm _)) u = _
            rw [Equiv.apply_symm_apply, rBlk.basisBits_extractIndex]
            rfl
          change basisBits (1 + 2 * N)
              (rTr.replaceIndex g₁ (fredkin3Perm (rTr.extractIndex g₁))) q =
            basisBits (1 + 2 * N) (stepPerm (k + 1) hk g) q
          by_cases hq0 : q.val = 0
          · have hq_eq : q = rTr 0 := by ext; simp [rTr, hq0]
            rw [hq_eq, rTr.basisBits_replaceIndex_apply, basisBits_fredkin3Perm, htr0, h1,
              ite_eq_left rfl]
            have hsw0 : Equiv.swap (1 : Wire 3) 2 0 = 0 := by decide
            rw [hsw0, htr0]
            dsimp [stepPerm]; rw [ite_eq_right h0]
            have hnot : rTr 0 ∉ Set.range rBlk.wires := by
              rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi; simp [rTr, rBlk] at hv
            rw [rBlk.basisBits_replaceIndex_of_not_mem _ _ (rTr 0) hnot]
            rfl
          · obtain ⟨u, rfl⟩ : ∃ u : Wire (2 * N), q = rBlk u :=
              ⟨⟨q.val - 1, by omega⟩, by ext; simp [rBlk]; omega⟩
            have hrhs : basisBits (1 + 2 * N) (stepPerm (k + 1) hk g) (rBlk u) =
                basisBits (1 + 2 * N) g
                  ⟨1 + (spinSwapPrefixWirePerm N (k + 1) hk u).val, by omega⟩ := by
              dsimp [stepPerm]
              rw [ite_eq_right h0, rBlk.basisBits_replaceIndex_apply]
              rw [Equiv.apply_symm_apply, rBlk.basisBits_extractIndex]
              rfl
            rw [hrhs]
            by_cases hu1 : u.val = k
            · have hq_tr1 : rBlk u = rTr 1 := by ext; simp [rBlk, rTr, hu1]
              rw [hq_tr1, rTr.basisBits_replaceIndex_apply, basisBits_fredkin3Perm, htr0, h1,
                ite_eq_left rfl, show Equiv.swap (1 : Wire 3) 2 1 = 2 by decide,
                rTr.basisBits_extractIndex]
              have htr2 : rTr 2 = ⟨1 + (⟨N + k, by omega⟩ : Wire (2 * N)).val, by omega⟩ := by
                ext; simp [rTr]; omega
              rw [htr2, hg₁_bit]
              refine congrArg (basisBits _ _) ?_; ext; dsimp
              change 1 + (spinSwapPrefixWireMap N k (by omega) ⟨N + k, by omega⟩).val =
                1 + (spinSwapPrefixWireMap N (k + 1) hk u).val
              unfold spinSwapPrefixWireMap
              have hc1 : ¬ ((⟨N + k, by omega⟩ : Wire (2 * N)).val < k) := by dsimp; omega
              have hc2 : ¬ (N ≤ (⟨N + k, by omega⟩ : Wire (2 * N)).val ∧
                  (⟨N + k, by omega⟩ : Wire (2 * N)).val < N + k) := by dsimp; omega
              have hc3 : u.val < k + 1 := by omega
              rw [dite_eq_right hc1, dite_eq_right hc2, dite_eq_left hc3]
              dsimp; omega
            · by_cases hu2 : u.val = N + k
              · have hq_tr2 : rBlk u = rTr 2 := by ext; simp [rBlk, rTr, hu2]; omega
                rw [hq_tr2, rTr.basisBits_replaceIndex_apply, basisBits_fredkin3Perm, htr0, h1,
                  ite_eq_left rfl, show Equiv.swap (1 : Wire 3) 2 2 = 1 by decide,
                  rTr.basisBits_extractIndex]
                have htr1 : rTr 1 = ⟨1 + (⟨k, by omega⟩ : Wire (2 * N)).val, by omega⟩ := rfl
                rw [htr1, hg₁_bit]
                refine congrArg (basisBits _ _) ?_; ext; dsimp
                change 1 + (spinSwapPrefixWireMap N k (by omega) ⟨k, by omega⟩).val =
                  1 + (spinSwapPrefixWireMap N (k + 1) hk u).val
                unfold spinSwapPrefixWireMap
                have hc1 : ¬ ((⟨k, by omega⟩ : Wire (2 * N)).val < k) := by dsimp; omega
                have hc2 : ¬ (N ≤ (⟨k, by omega⟩ : Wire (2 * N)).val ∧
                    (⟨k, by omega⟩ : Wire (2 * N)).val < N + k) := by dsimp; omega
                have hc3 : ¬ (u.val < k + 1) := by omega
                have hc4 : N ≤ u.val ∧ u.val < N + (k + 1) := by omega
                rw [dite_eq_right hc1, dite_eq_right hc2, dite_eq_right hc3, dite_eq_left hc4]
                dsimp; omega
              · have hnot_tr : rBlk u ∉ Set.range rTr.wires := by
                  rintro ⟨j, hj⟩
                  have hv := congrArg Fin.val hj
                  fin_cases j <;> simp [rTr, rBlk] at hv <;> omega
                rw [rTr.basisBits_replaceIndex_of_not_mem _ _ (rBlk u) hnot_tr]
                have hqu' : rBlk u = ⟨1 + u.val, by omega⟩ := by ext; simp [rBlk]
                rw [hqu', hg₁_bit]
                refine congrArg (basisBits _ _) ?_; ext; dsimp
                change 1 + (spinSwapPrefixWireMap N k (by omega) u).val =
                  1 + (spinSwapPrefixWireMap N (k + 1) hk u).val
                unfold spinSwapPrefixWireMap
                by_cases hlt : u.val < k
                · have hlt' : u.val < k + 1 := by omega
                  rw [dite_eq_left hlt, dite_eq_left hlt']
                · have hlt' : ¬ (u.val < k + 1) := by omega
                  rw [dite_eq_right hlt, dite_eq_right hlt']
                  by_cases hmid : N ≤ u.val ∧ u.val < N + k
                  · have hmid' : N ≤ u.val ∧ u.val < N + (k + 1) := by omega
                    rw [dite_eq_left hmid, dite_eq_left hmid']
                  · have hmid' : ¬ (N ≤ u.val ∧ u.val < N + (k + 1)) := by omega
                    rw [dite_eq_right hmid, dite_eq_right hmid']
  apply Subtype.ext
  ext a g
  have hlhs := congrFun (hpref N le_rfl g) a
  rw [Matrix.mulVec_single_one] at hlhs
  have hrhs_vec :
      (muxUnitary rCtrl rBlk hdisj
        (fun σ ↦ if σ = 0 then 1 else Operator.permutationUnitary (spinSwapEquiv N))).1 *ᵥ
          Pi.single g 1 = Pi.single (stepPerm N le_rfl g) 1 := by
    rw [muxUnitary_mulVec_of_proj rCtrl rBlk hdisj _ (rCtrl.extractIndex g) (Pi.single g 1)
      (fun g' hg' ↦ Pi.single_eq_of_ne (fun heq ↦ hg' (congrArg rCtrl.extractIndex heq)) 1)]
    have hc0 : rCtrl.extractIndex g = 0 ↔ basisBits (1 + 2 * N) g 0 = 0 := by
      rw [Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
      exact ⟨fun h ↦ h 0, fun h i ↦ by fin_cases i; exact h⟩
    by_cases h0 : rCtrl.extractIndex g = 0
    · rw [ite_eq_left h0, Submonoid.coe_one, rBlk.embedMatrix_one, Matrix.one_mulVec]
      dsimp [stepPerm]; rw [ite_eq_left (hc0.mp h0)]
    · rw [ite_eq_right h0, embedMatrix_perm_mulVec_single]
      dsimp [stepPerm]; rw [ite_eq_right (mt hc0.mpr h0), spinSwapEquiv_eq_symm_bits]
  have hrhs := congrFun hrhs_vec a
  rw [Matrix.mulVec_single_one] at hrhs
  exact hlhs.trans hrhs.symm

/-! ### `SELECT` Boolean/Index Logic, Branch Unitary & Circuit Decomposition -/

/-- One-body branch flag `x_o < 58` on `Fin (2 ^ 8)`. -/
def isOneBodyXo (xo : Fin (2 ^ 8)) : Bool :=
  decide (xo.val < 58)

/-- `7`-bit inner fragment index `rc(x_o)` (`0` when `x_o < 58`, `(x_o - 58) % 128` otherwise). -/
def rcBitsOfXo (xo : Fin (2 ^ 8)) : Fin (2 ^ 7) :=
  ⟨if xo.val < 58 then 0 else (xo.val - 58) % 128, by split_ifs <;> omega⟩

/-- Exact magic-constant quotient `⌊rc / 14⌋ = ⌊(⌊rc/2⌋ + ⌊rc/16⌋ + 1) / 8⌋` on `Fin (2 ^ 7)`. -/
def rDiv14OfRc (rc : Fin (2 ^ 7)) : Fin 9 :=
  ⟨(rc.val / 2 + rc.val / 16 + 1) / 8, by omega⟩

theorem rDiv14OfRc_eq_div (rc : Fin (2 ^ 7)) (h : rc.val < 126) :
    (rDiv14OfRc rc).val = rc.val / 14 := by
  revert h; revert rc; decide +kernel

/-- `319`-row table index `rowIdx(x_o, b)` (`x_o` for one-body, `58 + 29 r + min(b, 28)` for
two-body). -/
def rowIdxOf (xo : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) : Fin 319 :=
  if h : xo.val < 58 then
    ⟨xo.val, by omega⟩
  else
    ⟨58 + 29 * (rDiv14OfRc (rcBitsOfXo xo)).val + min b.val 28, by omega⟩

/-- Reflection enable bit `en_R` (`σ_in == 1` for one-body, `b < 29` for two-body). -/
def enROf (xo : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) (si : Fin 2) : Bool :=
  if isOneBodyXo xo then decide (si = 1) else decide (b.val < 29)

/-- Spin-swap control `σ_sel` (`σ_out` for one-body, `σ_in` for two-body). -/
def sigSelOf (xo : Fin (2 ^ 8)) (so si : Fin 2) : Fin 2 :=
  if isOneBodyXo xo then so else si

/-- Phase negation bit `negPhase` (`(σ_in == 1) && !neg1b(x_o)` for one-body,
`negIn(rc, 29)` for `b = 29`, `!negIn(rc, b)` for `b < 29`). -/
def negPhaseOf (xo : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) (si : Fin 2) : Bool :=
  if isOneBodyXo xo then
    decide (si = 1) && !(neg1bPadded xo)
  else
    xor (negInPadded (rcBitsOfXo xo) b) (decide (b.val < 29))

/-- Bundled involutory Hermitian `Unitary (2 ^ (2 * 58))` for `blockedOrbitalReflection` on
`p450RowVector idx`. -/
noncomputable def blockedRowReflectionUnitary (idx : Fin 319) (σ : Fin 2) :
    Unitary (2 ^ (2 * 58)) :=
  ⟨blockedOrbitalReflection (p450RowVector idx) σ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      blockedOrbitalReflection_conjTranspose]
    exact blockedOrbitalReflection_mul_self (p450RowVector_sum_sq idx) σ⟩

/-- Signed branch unitary on `2 * 58` system qubits for `(xo, so, b, si)`. -/
noncomputable def selectBranchUnitary (xo : Fin (2 ^ 8)) (so : Fin 2)
    (b : Fin (2 ^ 5)) (si : Fin 2) : Unitary (2 ^ (2 * 58)) :=
  let phase : ℂ := if negPhaseOf xo b si then -1 else 1
  let base : Operator (2 ^ (2 * 58)) :=
    if enROf xo b si then
      (blockedRowReflectionUnitary (rowIdxOf xo b) (sigSelOf xo so si)).1
    else 1
  ⟨phase • base, by
    have hp : star phase * phase = 1 := by
      dsimp [phase]; split_ifs <;> norm_num
    have hb : base * baseᴴ = 1 := by
      dsimp [base]
      split_ifs
      · rw [← Matrix.star_eq_conjTranspose]
        exact (blockedRowReflectionUnitary _ _).2.2
      · simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      smul_mul_smul_comm, mul_comm phase (star phase), hp, one_smul, hb]⟩

@[simp]
theorem selectBranchUnitary_conjTranspose (xo : Fin (2 ^ 8)) (so : Fin 2)
    (b : Fin (2 ^ 5)) (si : Fin 2) :
    (selectBranchUnitary xo so b si).1ᴴ = (selectBranchUnitary xo so b si).1 := by
  dsimp only [selectBranchUnitary, blockedRowReflectionUnitary]
  rw [Matrix.conjTranspose_smul]
  have hp : star (if negPhaseOf xo b si then (-1 : ℂ) else 1) =
      if negPhaseOf xo b si then (-1 : ℂ) else 1 := by
    split_ifs <;> norm_num
  have hb : (if enROf xo b si then
        blockedOrbitalReflection (p450RowVector (rowIdxOf xo b)) (sigSelOf xo so si)
      else (1 : Operator (2 ^ (2 * 58))))ᴴ =
      if enROf xo b si then
        blockedOrbitalReflection (p450RowVector (rowIdxOf xo b)) (sigSelOf xo so si)
      else 1 := by
    split_ifs
    · exact blockedOrbitalReflection_conjTranspose _ _
    · exact Matrix.conjTranspose_one
  rw [hp, hb]

/-- Extract `(xo, so, b, si)` from a combined ancilla basis index
`a : Fin (2 ^ mAncUB w_go w_gi)`. -/
def decodeSelectCtrl {w_go w_gi : ℕ} (a : Fin (2 ^ mAncUB w_go w_gi)) :
    Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 5) × Fin 2 :=
  let om := splitBlockEquiv (mOutUB w_go) (mMidUB w_gi) a
  ((rXoLoc w_go).extractIndex om.1,
   (rSigOutLoc w_go).extractIndex om.1,
   (rBLoc w_gi).extractIndex om.2,
   (rSigInLoc w_gi).extractIndex om.2)

/-! ### Step 2 & Step 4 Multiplexed `PREP_mid` & Full 4-Step `U_B` -/

/-! ### Half-Step SOS-to-Isometry & Rayleigh Norm-Squared Theorems -/

/-! ## Section 3: Operator-Norm & Catalytic `phaseGradientState 14` Perturbation Bounds -/

section PerturbationBounds

open scoped Matrix.Norms.L2Operator

/-- `nUB w_go w_gi`-qubit walk/block-encoding subregister inside `(nUB w_go w_gi) + k_cat` wires. -/
abbrev rUBInCat (w_go w_gi k_cat : ℕ) : QRegister (nUB w_go w_gi) (nUB w_go w_gi + k_cat) :=
  QRegister.block 0 (nUB w_go w_gi) (by omega)

/-- `k_cat`-qubit catalyst subregister (e.g., `k_cat = 14` holding `phaseGradientState 14`) inside
`(nUB w_go w_gi) + k_cat` wires. -/
abbrev rCatInCat (w_go w_gi k_cat : ℕ) : QRegister k_cat (nUB w_go w_gi + k_cat) :=
  QRegister.block (nUB w_go w_gi) k_cat (by omega)

theorem disjoint_rUBInCat_rCatInCat (w_go w_gi k_cat : ℕ) :
    (rUBInCat w_go w_gi k_cat).DisjointWires (rCatInCat w_go w_gi k_cat) :=
  QRegister.block_disjoint_of_le 0 (nUB w_go w_gi) (nUB w_go w_gi) k_cat
    (by omega) (by omega) (by omega)

/-- Product state `|v⟩_UB ⊗ |cat⟩_cat` inside `Fin (2 ^ (nUB w_go w_gi + k_cat)) → ℂ`. -/
noncomputable def tensorUBCat {w_go w_gi k_cat : ℕ}
    (v : Fin (2 ^ nUB w_go w_gi) → ℂ) (cat : Fin (2 ^ k_cat) → ℂ) :
    Fin (2 ^ (nUB w_go w_gi + k_cat)) → ℂ :=
  fun g ↦ v ((rUBInCat w_go w_gi k_cat).extractIndex g) *
    cat ((rCatInCat w_go w_gi k_cat).extractIndex g)

theorem embedMatrix_rUBInCat_mulVec_tensorUBCat {w_go w_gi k_cat : ℕ}
    (A : Operator (2 ^ nUB w_go w_gi))
    (v : Fin (2 ^ nUB w_go w_gi) → ℂ) (cat : Fin (2 ^ k_cat) → ℂ) :
    ((rUBInCat w_go w_gi k_cat).embedMatrix A) *ᵥ tensorUBCat v cat =
      tensorUBCat (A *ᵥ v) cat := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex]
  have hstep :
      (∑ u : Fin (2 ^ nUB w_go w_gi),
        A ((rUBInCat w_go w_gi k_cat).extractIndex g) u *
          tensorUBCat v cat ((rUBInCat w_go w_gi k_cat).replaceIndex g u)) =
      ∑ u : Fin (2 ^ nUB w_go w_gi),
        (A ((rUBInCat w_go w_gi k_cat).extractIndex g) u * v u) *
          cat ((rCatInCat w_go w_gi k_cat).extractIndex g) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tensorUBCat]
    have hcat :
        (rCatInCat w_go w_gi k_cat).extractIndex ((rUBInCat w_go w_gi k_cat).replaceIndex g u) =
          (rCatInCat w_go w_gi k_cat).extractIndex g :=
      (rCatInCat w_go w_gi k_cat).extractIndex_replaceIndex_of_disjoint _
        (QRegister.disjoint_comm.mp (disjoint_rUBInCat_rCatInCat w_go w_gi k_cat)) g u
    rw [hcat, QRegister.extractIndex_replaceIndex, mul_assoc]
  rw [hstep, ← Finset.sum_mul]
  rfl

end PerturbationBounds

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore
