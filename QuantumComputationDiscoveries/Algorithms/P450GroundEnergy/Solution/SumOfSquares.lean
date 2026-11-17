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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm

/-!
# Exact Sum-of-Squares Decomposition for Cytochrome P450 DFTHC
Proves the exact Sum-of-Squares (SOS) operator identity and spectral Rayleigh bounds for
`thcHamiltonian P450.dfthc`:

1. **Verified Integer Table Theorems (`decide +kernel`):**
   - `table_shapes_and_bounds`, `innerWeights_l1_eq_15360`, `outerWeights_sum_eq_188416`, plus angle
     table range bounds `< 2 ^ 13`.
2. **Exact SOS Lower Bound (`dfthcLowerBound`):**
   - Exact rational value `-20819928884476879 / 154350387200000` (`≈ -134.887441892189` Ha) and
     rational bracket `-134.8875 < dfthcLowerBound < -134.8874`.
3. **Jordan–Wigner CAR & Involutory Orbital Reflections:**
   - Canonical anticommutation relations for `jwAnnihilate`, Hermiticity and idempotency of
     `orbitalNumberOp N u σ` for unit real `u`, and involutory unitarity of
     `orbitalReflection N u σ`.
4. **Fragment LCU Contractions & Global SOS Identity (`thcHamiltonian_sub_lowerBound_eq_sos`):**
   - Exact cancellation of the centered shift `fragmentShift` into the normalized LCU `fragmentLCU`
     and exact global SOS decomposition with total outer weight `2 * 97.3864` (`2 * Λ`, zero wasted
     padding), yielding Rayleigh-quotient and eigenvalue bounds in
     `[dfthcLowerBound, dfthcLowerBound + 2 * 97.3864]`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Solution.DataArrays
open scoped Matrix

/-! ## Section 1: Integer Weight Accessors & Verified Table Theorems -/

/-- Signed integer weight `n_ℓ` from `oneBodyWeightsArr` for one-body eigenpair `ℓ`. -/
def oneBodyWeightInt (ℓ : Fin 58) : ℤ :=
  P450.fromOffset (oneBodyWeightsArr.getD ℓ.val (2 ^ 14))

/-- Outer natural-number weight `n_{rc}` from `fragmentWeightsArr` for fragment `(r, c)`. -/
def fragmentWeightNat (r : Fin 9) (c : Fin 14) : ℕ :=
  (fragmentWeightsArr.getD r.val #[]).getD c.val 0

/-- Signed integer mantissa `m^{(rc)}_b` from `innerWeightsArr` for fragment `(r, c)` and
column `b < 30` (`b = 29` stores `m^{(rc)}_B`). -/
def innerMantissa (r : Fin 9) (c : Fin 14) (b : Fin 30) : ℤ :=
  P450.fromOffset ((innerWeightsArr.getD (14 * r.val + c.val) #[]).getD b.val (2 ^ 14))

/-- Combined leaf index `29 * r + b < 261` for outer group `r` and inner leaf `b`. -/
abbrev leafIndex (r : Fin 9) (b : Fin 29) : Fin 261 :=
  ⟨29 * r.val + b.val, by omega⟩

/-- Shapes and angle-index bounds (`< 2 ^ 13`) of all five unpacked `P450` parameter tables. -/
theorem table_shapes_and_bounds :
    leafAngleTableArr.size = 261 ∧ oneBodyAngleTableArr.size = 58 ∧
    (∀ row ∈ leafAngleTableArr.toList ++ oneBodyAngleTableArr.toList,
      row.size = 57 ∧ ∀ k ∈ row.toList, k < 2 ^ 13) ∧
    oneBodyWeightsArr.size = 58 ∧ fragmentWeightsArr.size = 9 ∧
    (∀ row ∈ fragmentWeightsArr.toList, row.size = 14) ∧
    innerWeightsArr.size = 126 ∧
    (∀ row ∈ innerWeightsArr.toList, row.size = 30) := by
  decide +kernel

/-- Row-list form of the inner alias-sampling L1 identity `∑_b |m^{(rc)}_b| = 15360`. -/
theorem innerWeights_toList_l1_eq_15360 :
    ∀ row ∈ innerWeightsArr.toList,
      row.size = 30 ∧ (row.toList.map fun x ↦ (P450.fromOffset x).natAbs).sum = 15360 := by
  decide +kernel

/-- Row-list form of the outer alias-sampling L1 identity `∑_ℓ |n_ℓ| + ∑_{r,c} n_{rc} = 188416`. -/
theorem outerWeights_toList_sum_eq_188416 :
    (oneBodyWeightsArr.toList.map fun x ↦ (P450.fromOffset x).natAbs).sum +
      (fragmentWeightsArr.toList.map fun row ↦ row.toList.sum).sum = 188416 := by
  decide +kernel

theorem oneBody_neg_list_sum_eq :
    ((List.finRange 58).map fun ℓ ↦
      if oneBodyWeightInt ℓ < 0 then 2 * oneBodyWeightInt ℓ else 0).sum = -31264 := by
  decide +kernel

theorem fragmentShift_sq_list_sum_eq :
    ((List.finRange 9).map fun r ↦
      ((List.finRange 14).map fun c ↦
        (fragmentWeightNat r c : ℤ) *
          (innerMantissa r c 29 -
            ((List.finRange 29).map fun b : Fin 29 ↦
              innerMantissa r c b.castSucc).sum) ^ 2).sum).sum =
      27097250746140 := by
  decide +kernel

theorem oneBodyEigenvalue_eq_weightInt (ℓ : Fin 58) :
    P450.oneBodyEigenvalue ℓ = (oneBodyWeightInt ℓ : ℝ) * P450.coefficientUnit :=
  Solution.DataArrays.oneBodyEigenvalue_eq_arr ℓ

theorem weight_eq_innerMantissa (r : Fin 9) (c : Fin 14) (b : Fin 30) :
    P450.weight r c b =
      (innerMantissa r c b : ℝ) *
        √(4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) / 15360 :=
  Solution.DataArrays.weight_eq_arr r c b

-- Seal all large literal bitvectors and unpacked arrays so downstream tactics never unfold them.
attribute [local irreducible] P450.leafAngleTable P450.oneBodyAngleTable
  P450.oneBodyWeights P450.fragmentWeights P450.innerWeights
  leafAngleTableArr oneBodyAngleTableArr
  oneBodyWeightsArr fragmentWeightsArr innerWeightsArr

theorem array_getD_mem_toList {α : Type*} (a : Array α) (d : α) (i : ℕ) (hi : i < a.size) :
    a.getD i d ∈ a.toList := by
  simp only [Array.getD, hi, ↓reduceDIte]
  exact Array.getElem_mem_toList hi

theorem array_fin_sum_eq_toList_map_sum {α M : Type*} [AddCommMonoid M]
    (a : Array α) (d : α) {n : ℕ} (f : α → M) (hsize : a.size = n) :
    (∑ i : Fin n, f (a.getD i.val d)) = (a.toList.map f).sum := by
  subst hsize
  have hlist : a.toList.map f = List.ofFn (fun i : Fin a.size ↦ f (a.getD i.val d)) := by
    apply List.ext_getElem
    · simp only [List.length_map, Array.length_toList, List.length_ofFn]
    · intro i h1 _h2
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_ofFn]
      have hi : i < a.size := by simpa using h1
      simp only [Array.getD, hi, ↓reduceDIte]
      rfl
  rw [hlist, List.sum_ofFn]

/-- For every fragment `(r, c)`, the inner integer mantissas sum in absolute value to `15360`. -/
theorem innerWeights_l1_eq_15360 (r : Fin 9) (c : Fin 14) :
    ∑ b : Fin 30, (innerMantissa r c b).natAbs = 15360 := by
  obtain ⟨_, _, _, _, _, _, hiw, _⟩ := table_shapes_and_bounds
  have hidx : 14 * r.val + c.val < innerWeightsArr.size := by omega
  have hmem := array_getD_mem_toList innerWeightsArr #[] (14 * r.val + c.val) hidx
  obtain ⟨hrsize, hrsum⟩ := innerWeights_toList_l1_eq_15360 _ hmem
  unfold innerMantissa
  rw [array_fin_sum_eq_toList_map_sum _ (2 ^ 14) (fun x ↦ (P450.fromOffset x).natAbs) hrsize]
  exact hrsum

/-- The outer integer weights sum to `188416` (`= 184 * 1024`). -/
theorem outerWeights_sum_eq_188416 :
    (∑ ℓ : Fin 58, (oneBodyWeightInt ℓ).natAbs) +
      (∑ r : Fin 9, ∑ c : Fin 14, fragmentWeightNat r c) = 188416 := by
  obtain ⟨_, _, _, hob, hfw, hfw_rows, _⟩ := table_shapes_and_bounds
  have h1 : (∑ ℓ : Fin 58, (oneBodyWeightInt ℓ).natAbs) =
      (oneBodyWeightsArr.toList.map fun x ↦ (P450.fromOffset x).natAbs).sum := by
    unfold oneBodyWeightInt
    exact array_fin_sum_eq_toList_map_sum oneBodyWeightsArr (2 ^ 14)
      (fun x ↦ (P450.fromOffset x).natAbs) hob
  have h2 : (∑ r : Fin 9, ∑ c : Fin 14, fragmentWeightNat r c) =
      (fragmentWeightsArr.toList.map fun row ↦ row.toList.sum).sum := by
    unfold fragmentWeightNat
    have hrow_sum (r : Fin 9) :
        (∑ c : Fin 14, (fragmentWeightsArr.getD r.val #[]).getD c.val 0) =
          (fragmentWeightsArr.getD r.val #[]).toList.sum := by
      have hr : r.val < fragmentWeightsArr.size := by omega
      have hrsize := hfw_rows _ (array_getD_mem_toList fragmentWeightsArr #[] r.val hr)
      simpa only [id_eq, List.map_id] using array_fin_sum_eq_toList_map_sum _ 0 id hrsize
    simp only [hrow_sum]
    exact array_fin_sum_eq_toList_map_sum fragmentWeightsArr #[] (fun row ↦ row.toList.sum) hfw
  rw [h1, h2, outerWeights_toList_sum_eq_188416]

attribute [local irreducible] oneBodyWeightInt fragmentWeightNat innerMantissa

theorem natAbs_cast_real (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  have hnn : (0 : ℝ) ≤ ((z.natAbs : ℕ) : ℝ) := Nat.cast_nonneg z.natAbs
  rcases Int.natAbs_eq z with h | h
  · conv_rhs => rw [h]
    rw [Int.cast_natCast, abs_of_nonneg hnn]
  · conv_rhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg hnn]

/-! ## Section 2: Exact SOS Lower Bound `dfthcLowerBound` & Rational Bounds -/

/-- Exact sum-of-squares lower bound on `thcHamiltonian P450.dfthc`. -/
noncomputable def dfthcLowerBound : ℝ :=
  (∑ ℓ : Fin 58, if P450.oneBodyEigenvalue ℓ < 0 then 2 * P450.oneBodyEigenvalue ℓ else 0) -
    2⁻¹ * ∑ r : Fin 9, ∑ c : Fin 14, P450.fragmentShift r c ^ 2

theorem coefficientUnit_pos : 0 < P450.coefficientUnit := by
  unfold P450.coefficientUnit
  norm_num

/-- Fragment scale factor `S_{rc} = √(4 n_{rc} q)`. -/
noncomputable abbrev fragmentScale (r : Fin 9) (c : Fin 14) : ℝ :=
  √(4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit)

theorem fragmentShift_eq_innerMantissa (r : Fin 9) (c : Fin 14) :
    P450.fragmentShift r c =
      ((innerMantissa r c 29 : ℝ) - ∑ b : Fin 29, (innerMantissa r c b.castSucc : ℝ)) *
        fragmentScale r c / 15360 := by
  unfold P450.fragmentShift
  rw [weight_eq_innerMantissa]
  simp only [weight_eq_innerMantissa, ← Finset.sum_div, ← Finset.sum_mul]
  ring

/-- `dfthcLowerBound` is an exact rational number (`≈ -134.887441892189` Ha). -/
theorem dfthcLowerBound_eq_rat :
    dfthcLowerBound = -20819928884476879 / 154350387200000 := by
  unfold dfthcLowerBound
  have hq : 0 < P450.coefficientUnit := coefficientUnit_pos
  have hob_term (ℓ : Fin 58) :
      (if P450.oneBodyEigenvalue ℓ < 0 then 2 * P450.oneBodyEigenvalue ℓ else 0) =
        ((if oneBodyWeightInt ℓ < 0 then 2 * oneBodyWeightInt ℓ else 0 : ℤ) : ℝ) *
          P450.coefficientUnit := by
    rw [oneBodyEigenvalue_eq_weightInt]
    have hiff : (oneBodyWeightInt ℓ : ℝ) * P450.coefficientUnit < 0 ↔ oneBodyWeightInt ℓ < 0 := by
      rw [mul_neg_iff]
      constructor
      · rintro (⟨_, hlt⟩ | ⟨hlt, _⟩)
        · linarith
        · exact Int.cast_lt_zero.mp hlt
      · intro hlt
        exact Or.inr ⟨Int.cast_lt_zero.mpr hlt, hq⟩
    rw [if_congr hiff rfl rfl]
    split_ifs <;> push_cast <;> ring
  have hob_sum :
      (∑ ℓ : Fin 58, if P450.oneBodyEigenvalue ℓ < 0 then 2 * P450.oneBodyEigenvalue ℓ else 0) =
        (-31264 : ℝ) * P450.coefficientUnit := by
    simp only [hob_term, ← Finset.sum_mul]
    congr 1
    rw [← Int.cast_sum, Fin.sum_univ_def, oneBody_neg_list_sum_eq]
    norm_num
  have hshift_sq (r : Fin 9) (c : Fin 14) :
      P450.fragmentShift r c ^ 2 =
        (((fragmentWeightNat r c : ℤ) *
            (innerMantissa r c 29 - ∑ b : Fin 29, innerMantissa r c b.castSucc) ^ 2 : ℤ) : ℝ) *
          (4 * P450.coefficientUnit / 15360 ^ 2) := by
    rw [fragmentShift_eq_innerMantissa]
    have hnonneg : 0 ≤ 4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit := by positivity
    have hsq : fragmentScale r c ^ 2 = 4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit :=
      Real.sq_sqrt hnonneg
    rw [div_pow, mul_pow, hsq]
    push_cast
    ring
  have hshift_sum :
      (∑ r : Fin 9, ∑ c : Fin 14, P450.fragmentShift r c ^ 2) =
        (27097250746140 : ℝ) * (4 * P450.coefficientUnit / 15360 ^ 2) := by
    simp only [hshift_sq, ← Finset.sum_mul]
    congr 1
    have hint :
        (∑ r : Fin 9, ∑ c : Fin 14,
          (fragmentWeightNat r c : ℤ) *
            (innerMantissa r c 29 - ∑ b : Fin 29, innerMantissa r c b.castSucc) ^ 2) =
        27097250746140 := by
      simp only [Fin.sum_univ_def]
      exact fragmentShift_sq_list_sum_eq
    have hcast :
        ((∑ r : Fin 9, ∑ c : Fin 14,
          (fragmentWeightNat r c : ℤ) *
            (innerMantissa r c 29 -
              ∑ b : Fin 29, innerMantissa r c b.castSucc) ^ 2 : ℤ) : ℝ) =
        27097250746140 := by
      rw [hint]
      norm_num
    simpa only [Int.cast_sum] using hcast
  rw [hob_sum, hshift_sum]
  unfold P450.coefficientUnit
  norm_num

theorem sum_smul_mul_sum_smul {ι : Type*} [Fintype ι] {d : ℕ}
    (u : ι → ℝ) (A B : ι → Operator d) :
    (∑ p : ι, (u p : ℂ) • A p) * (∑ q : ι, (u q : ℂ) • B q) =
      ∑ p : ι, ∑ q : ι, ((u p * u q : ℝ) : ℂ) • (A p * B q) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [smul_mul_smul_comm, Complex.ofReal_mul]

/-- Sign `±1` of `P450.oneBodyEigenvalue ℓ` (`-1` when `< 0`, `+1` when `≥ 0`). -/
noncomputable def oneBodySign (ℓ : Fin 58) : ℝ :=
  if P450.oneBodyEigenvalue ℓ < 0 then -1 else 1

/-- Projector `(I - sgn(t_ℓ) R_{u_ℓ, σ}) / 2` onto the occupied (`t_ℓ ≥ 0`) or empty (`t_ℓ < 0`)
spin-orbital mode `(u_ℓ, σ)`. -/
noncomputable def oneBodyProjector (ℓ : Fin 58) (σ : Fin 2) : Operator (2 ^ (2 * 58)) :=
  (2 : ℂ)⁻¹ • (1 - (oneBodySign ℓ : ℂ) • orbitalReflection 58 (P450.oneBodyVector ℓ) σ)

/-- Normalized Hermitian LCU operator `A_{rc}` for DFTHC fragment `(r, c)`. -/
noncomputable def fragmentLCU (r : Fin 9) (c : Fin 14) : Operator (2 ^ (2 * 58)) :=
  ((15360 : ℂ)⁻¹) •
    ((innerMantissa r c 29 : ℂ) • (1 : Operator (2 ^ (2 * 58))) -
      ∑ b : Fin 29, ∑ σ : Fin 2,
        ((innerMantissa r c b.castSucc : ℂ) / 2) •
          orbitalReflection 58 (P450.leafVector (leafIndex r b)) σ)

theorem oneBodyProjector_conjTranspose (ℓ : Fin 58) (σ : Fin 2) :
    (oneBodyProjector ℓ σ)ᴴ = oneBodyProjector ℓ σ := by
  simp only [oneBodyProjector, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, orbitalReflection_conjTranspose, Complex.star_def, map_inv₀,
    map_ofNat, Complex.conj_ofReal]

theorem fragmentLCU_conjTranspose (r : Fin 9) (c : Fin 14) :
    (fragmentLCU r c)ᴴ = fragmentLCU r c := by
  unfold fragmentLCU
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_sum, orbitalReflection_conjTranspose, Complex.star_def, map_inv₀,
    map_ofNat, map_div₀, map_intCast]

theorem abstract_lcu_contraction {d : ℕ}
    (nOp : Fin 29 → Fin 2 → Operator d) (m : Fin 30 → ℝ) (S : ℝ) :
    let w : Fin 30 → ℝ := fun b ↦ m b * S / 15360
    let W : ℝ := w 29 - ∑ b : Fin 29, w b.castSucc
    let R : Fin 29 → Fin 2 → Operator d := fun b σ ↦ 1 - (2 : ℂ) • nOp b σ
    let A : Operator d := ((15360 : ℂ)⁻¹) •
      ((m 29 : ℂ) • (1 : Operator d) -
        ∑ b : Fin 29, ∑ σ : Fin 2, ((m b.castSucc : ℂ) / 2) • R b σ)
    (W : ℂ) • (1 : Operator d) +
      ∑ b : Fin 29, (w b.castSucc : ℂ) • (nOp b 0 + nOp b 1) = (S : ℂ) • A := by
  intro w W R A
  have hn (b : Fin 29) :
      nOp b 0 + nOp b 1 = (1 : Operator d) - ∑ σ : Fin 2, (2 : ℂ)⁻¹ • R b σ := by
    rw [Fin.sum_univ_two]
    simp only [R]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  simp only [hn, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hwW :
      (W : ℂ) + ∑ b : Fin 29, (w b.castSucc : ℂ) =
        (S : ℂ) * ((15360 : ℂ)⁻¹ * (m 29 : ℂ)) := by
    simp only [W, w, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hsum :
      (∑ b : Fin 29, (w b.castSucc : ℂ) • ∑ σ : Fin 2, (2 : ℂ)⁻¹ • R b σ) =
        (S : ℂ) • ((15360 : ℂ)⁻¹ •
          ∑ b : Fin 29, ∑ σ : Fin 2, ((m b.castSucc : ℂ) / 2) • R b σ) := by
    simp only [Finset.smul_sum, smul_smul, w, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
    congr 1
    ring
  calc (W : ℂ) • (1 : Operator d) +
          ((∑ b : Fin 29, (w b.castSucc : ℂ)) • (1 : Operator d) -
            ∑ b : Fin 29, (w b.castSucc : ℂ) • ∑ σ : Fin 2, (2 : ℂ)⁻¹ • R b σ)
      = ((W : ℂ) + ∑ b : Fin 29, (w b.castSucc : ℂ)) • (1 : Operator d) -
          ∑ b : Fin 29, (w b.castSucc : ℂ) • ∑ σ : Fin 2, (2 : ℂ)⁻¹ • R b σ := by
        rw [← add_sub_assoc, ← add_smul]
    _ = (S : ℂ) • A := by
        rw [hwW, hsum]
        simp only [A, smul_sub, smul_smul]

/-- Exact fragment LCU contraction: the centered shift `fragmentShift r c` cancels the
`∑_{b<29} w_b I` terms identically, leaving `(fragmentScale r c) • fragmentLCU r c`. -/
theorem fragmentShift_add_sum_eq_fragmentLCU (r : Fin 9) (c : Fin 14) :
    (P450.fragmentShift r c : ℂ) • (1 : Operator (2 ^ (2 * 58))) +
      ∑ b : Fin 29, (P450.weight r c b.castSucc : ℂ) •
        (orbitalNumberOp 58 (P450.leafVector (leafIndex r b)) 0 +
          orbitalNumberOp 58 (P450.leafVector (leafIndex r b)) 1) =
      (fragmentScale r c : ℂ) • fragmentLCU r c := by
  have h := abstract_lcu_contraction
    (fun b σ ↦ orbitalNumberOp 58 (P450.leafVector (leafIndex r b)) σ)
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
  simpa only [hshift, hwb, Complex.ofReal_intCast, orbitalReflection, fragmentLCU] using h

theorem abstract_oneBody_sos_term {d : ℕ}
    (Nop : Operator d) (hH : Nopᴴ = Nop) (hIdem : Nop * Nop = Nop) (t : ℝ) :
    let s : ℝ := if t < 0 then -1 else 1
    let R : Operator d := 1 - (2 : ℂ) • Nop
    let P : Operator d := (2 : ℂ)⁻¹ • (1 - (s : ℂ) • R)
    ((|t| : ℝ) : ℂ) • (Pᴴ * P) =
      (t : ℂ) • Nop - ((if t < 0 then t else 0 : ℝ) : ℂ) • (1 : Operator d) := by
  intro s R P
  by_cases ht : t < 0
  · have hs : s = -1 := by simp only [s, ht, ↓reduceIte]
    have hP : P = 1 - Nop := by
      simp only [P, R, hs, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul,
        sub_neg_eq_add]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hPh : Pᴴ = 1 - Nop := by rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
    have hPP : (1 - Nop) * (1 - Nop) = 1 - Nop := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hIdem]
      abel
    simp only [ht, ↓reduceIte]
    rw [abs_of_neg ht, hPh, hP, hPP, Complex.ofReal_neg, neg_smul, smul_sub, neg_sub]
  · have hnn : 0 ≤ t := not_lt.mp ht
    have hs : s = 1 := by simp only [s, ht, ↓reduceIte]
    have hP : P = Nop := by
      simp only [P, R, hs, Complex.ofReal_one, one_smul, sub_sub_cancel, smul_smul]
      norm_num
    simp only [ht, ↓reduceIte]
    rw [abs_of_nonneg hnn, hP, hH, hIdem, Complex.ofReal_zero, zero_smul, sub_zero]

/-- Equivalence `Fin 9 × Fin 29 ≃ Fin 261` induced by `leafIndex`. -/
def leafEquiv : Fin 9 × Fin 29 ≃ Fin 261 where
  toFun rb := leafIndex rb.1 rb.2
  invFun μ := (⟨μ.val / 29, by omega⟩, ⟨μ.val % 29, by omega⟩)
  left_inv rb := by
    ext
    · dsimp only [leafIndex]; omega
    · dsimp only [leafIndex]; omega
  right_inv μ := by
    ext
    dsimp only [leafIndex]
    omega

theorem leafEquiv_apply (rb : Fin 9 × Fin 29) :
    leafEquiv rb = leafIndex rb.1 rb.2 := rfl

theorem sum_fragmentVector_smul {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (r : Fin 9) (c : Fin 14) (X : Fin 261 → M) :
    (∑ μ : Fin 261, (P450.fragmentVector r c μ : ℂ) • X μ) =
      ∑ b : Fin 29, (P450.weight r c b.castSucc : ℂ) • X (leafIndex r b) := by
  rw [← leafEquiv.sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single r]
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    have hdiv : (leafEquiv (r, b)).val / 29 = r.val := by
      rw [leafEquiv_apply]
      dsimp only [leafIndex]
      omega
    have hfin : (⟨(leafEquiv (r, b)).val % 29, by omega⟩ : Fin 30) = b.castSucc :=
      Fin.ext (by dsimp only [leafEquiv_apply, leafIndex, Fin.val_castSucc]; omega)
    simp only [P450.fragmentVector, hdiv, ↓reduceIte, hfin]
    rfl
  · intro r' _ hr'
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    have hdiv : (leafEquiv (r', b)).val / 29 ≠ r.val := by
      have hne : r'.val ≠ r.val := Fin.val_ne_of_ne hr'
      rw [leafEquiv_apply]
      dsimp only [leafIndex]
      omega
    simp only [P450.fragmentVector, hdiv, ↓reduceIte, Complex.ofReal_zero, zero_smul]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

theorem abstract_fragment_square_identity {d : ℕ}
    (K A : Operator d) (hA : Aᴴ = A) (W S : ℝ)
    (hL : (W : ℂ) • (1 : Operator d) + K = (S : ℂ) • A) :
    (W : ℂ) • K + (2 : ℂ)⁻¹ • (K * K) + ((2⁻¹ * W ^ 2 : ℝ) : ℂ) • (1 : Operator d) =
      ((2⁻¹ * S ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
  have hsq : ((W : ℂ) • (1 : Operator d) + K) * ((W : ℂ) • (1 : Operator d) + K) =
      ((W ^ 2 : ℝ) : ℂ) • (1 : Operator d) + ((2 * W : ℝ) : ℂ) • K + K * K := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hSA : ((S : ℂ) • A) * ((S : ℂ) • A) = ((S ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_pow, sq]
  have heq : ((W ^ 2 : ℝ) : ℂ) • (1 : Operator d) + ((2 * W : ℝ) : ℂ) • K + K * K =
      ((S ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [← hsq, hL, hSA]
  have hmul := congrArg (fun M : Operator d ↦ (2 : ℂ)⁻¹ • M) heq
  have hrhs : ((2⁻¹ * S ^ 2 : ℝ) : ℂ) • (Aᴴ * A) =
      (2 : ℂ)⁻¹ • ((S ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [smul_smul]
    push_cast
    rfl
  rw [hrhs, ← hmul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.ofReal_pow]
  ring

theorem fin2_add_mul_add {d : ℕ} (B C : Fin 2 → Operator d) :
    (B 0 + B 1) * (C 0 + C 1) = ∑ σ : Fin 2, ∑ τ : Fin 2, B σ * C τ := by
  simp only [Fin.sum_univ_two, Matrix.add_mul, Matrix.mul_add]
  abel

theorem sum4_swap {I J K L M : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [AddCommMonoid M] (f : I → J → K → L → M) :
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ l : L, f i j k l) =
      ∑ k : K, ∑ l : L, ∑ i : I, ∑ j : J, f i j k l := by
  have h1 (i : I) : (∑ j : J, ∑ k : K, ∑ l : L, f i j k l) =
      ∑ k : K, ∑ j : J, ∑ l : L, f i j k l := Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h2 (i : I) : (∑ j : J, ∑ l : L, f i j k l) =
      ∑ l : L, ∑ j : J, f i j k l := Finset.sum_comm
  simp only [h2]
  exact Finset.sum_comm

theorem sum6_swap {A B C D E F M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    [AddCommMonoid M] (g : A → B → C → D → E → F → M) :
    (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, ∑ e : E, ∑ f : F, g a b c d e f) =
      ∑ e : E, ∑ f : F, ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, g a b c d e f := by
  have h1 (a : A) (b : B) :
      (∑ c : C, ∑ d : D, ∑ e : E, ∑ f : F, g a b c d e f) =
        ∑ e : E, ∑ f : F, ∑ c : C, ∑ d : D, g a b c d e f :=
    sum4_swap _
  simp only [h1]
  exact sum4_swap _

theorem smul_add_sub_two_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (t c : ℂ) (N0 N1 one : M) :
    t • (N0 + N1) - ((2 : ℂ) * c) • one = (t • N0 - c • one) + (t • N1 - c • one) := by
  rw [smul_add, two_mul, add_smul]
  abel

theorem add_three_sub_sub {M : Type*} [AddCommGroup M] (H1 F1 H2 E1 E2 : M) :
    (H1 + F1) + H2 - (E1 - E2) = (H1 - E1) + (F1 + H2 + E2) := by
  abel

/-- **Exact Global DFTHC Sum-of-Squares Decomposition.** -/
theorem thcHamiltonian_sub_lowerBound_eq_sos :
    thcHamiltonian P450.dfthc - (dfthcLowerBound : ℂ) • 1 =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2,
        ((|P450.oneBodyEigenvalue ℓ| : ℝ) : ℂ) •
          ((oneBodyProjector ℓ σ)ᴴ * oneBodyProjector ℓ σ)) +
      (∑ r : Fin 9, ∑ c : Fin 14,
        ((2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit : ℝ) : ℂ) •
          ((fragmentLCU r c)ᴴ * fragmentLCU r c)) := by
  let nOp : (Fin 58 → ℝ) → Operator (2 ^ (2 * 58)) :=
    fun u ↦ orbitalNumberOp 58 u 0 + orbitalNumberOp 58 u 1
  let K : Fin 9 → Fin 14 → Operator (2 ^ (2 * 58)) :=
    fun r c ↦ ∑ b : Fin 29, (P450.weight r c b.castSucc : ℂ) •
      nOp (P450.leafVector (leafIndex r b))
  have h1e : oneBodyHamiltonian P450.dfthc.h1eMod =
      (∑ ℓ : Fin 58, (P450.oneBodyEigenvalue ℓ : ℂ) • nOp (P450.oneBodyVector ℓ)) +
        ∑ r : Fin 9, ∑ c : Fin 14, (P450.fragmentShift r c : ℂ) • K r c := by
    change oneBodyHamiltonian
      ((∑ ℓ : Fin 58, P450.oneBodyEigenvalue ℓ •
          Matrix.vecMulVec (P450.oneBodyVector ℓ) (P450.oneBodyVector ℓ)) +
        ∑ μ : Fin 261, (∑ r : Fin 9, ∑ c : Fin 14,
            P450.fragmentShift r c * P450.fragmentVector r c μ) •
          Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ)) = _
    rw [oneBodyHamiltonian_add, oneBodyHamiltonian_sum, oneBodyHamiltonian_sum]
    congr 1
    · refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
      rw [oneBodyHamiltonian_smul, oneBodyHamiltonian_vecMulVec]
    · have hmu (μ : Fin 261) :
          oneBodyHamiltonian ((∑ r : Fin 9, ∑ c : Fin 14,
              P450.fragmentShift r c * P450.fragmentVector r c μ) •
            Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ)) =
          ∑ r : Fin 9, ∑ c : Fin 14,
            (P450.fragmentShift r c : ℂ) •
              ((P450.fragmentVector r c μ : ℂ) • nOp (P450.leafVector μ)) := by
        rw [oneBodyHamiltonian_smul, oneBodyHamiltonian_vecMulVec]
        simp only [nOp, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, mul_smul]
      simp only [hmu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [← Finset.smul_sum, sum_fragmentVector_smul]
  have h2e :
      (2 : ℂ)⁻¹ • (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
        (P450.dfthc.zeta μ ν : ℂ) •
          (orbitalNumberOp 58 (P450.dfthc.chi μ) σ *
            orbitalNumberOp 58 (P450.dfthc.chi ν) τ)) =
        ∑ r : Fin 9, ∑ c : Fin 14, (2 : ℂ)⁻¹ • (K r c * K r c) := by
    have hchi : P450.dfthc.chi = P450.leafVector := rfl
    have hzeta (μ ν : Fin 261) : P450.dfthc.zeta μ ν =
        ∑ r : Fin 9, ∑ c : Fin 14,
          P450.fragmentVector r c μ * P450.fragmentVector r c ν := by
      change (∑ r : Fin 9, ∑ c : Fin 14,
        Matrix.vecMulVec (P450.fragmentVector r c)
          (P450.fragmentVector r c)) μ ν = _
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    simp only [hchi, hzeta]
    have hswap :
        (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
          ((∑ r : Fin 9, ∑ c : Fin 14,
            P450.fragmentVector r c μ * P450.fragmentVector r c ν : ℝ) : ℂ) •
            (orbitalNumberOp 58 (P450.leafVector μ) σ *
              orbitalNumberOp 58 (P450.leafVector ν) τ)) =
        ∑ r : Fin 9, ∑ c : Fin 14, K r c * K r c := by
      have hfactor (r : Fin 9) (c : Fin 14) :
          (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
            ((P450.fragmentVector r c μ * P450.fragmentVector r c ν : ℝ) : ℂ) •
              (orbitalNumberOp 58 (P450.leafVector μ) σ *
                orbitalNumberOp 58 (P450.leafVector ν) τ)) =
          K r c * K r c := by
        have hK : (∑ μ : Fin 261, (P450.fragmentVector r c μ : ℂ) •
            nOp (P450.leafVector μ)) = K r c := sum_fragmentVector_smul r c _
        rw [← hK, sum_smul_mul_sum_smul]
        have hspin (μ ν : Fin 261) :
            nOp (P450.leafVector μ) * nOp (P450.leafVector ν) =
              ∑ σ : Fin 2, ∑ τ : Fin 2,
                orbitalNumberOp 58 (P450.leafVector μ) σ *
                  orbitalNumberOp 58 (P450.leafVector ν) τ :=
          fin2_add_mul_add _ _
        simp only [hspin, Finset.smul_sum]
        exact (sum4_swap _).symm
      simp only [Complex.ofReal_sum, Finset.sum_smul]
      rw [sum6_swap]
      exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ hfactor r c
    rw [hswap]
    simp only [Finset.smul_sum]
  have hob_sos :
      (∑ ℓ : Fin 58, (P450.oneBodyEigenvalue ℓ : ℂ) • nOp (P450.oneBodyVector ℓ)) -
        ((∑ ℓ : Fin 58, if P450.oneBodyEigenvalue ℓ < 0 then
            2 * P450.oneBodyEigenvalue ℓ else 0 : ℝ) : ℂ) • 1 =
      ∑ ℓ : Fin 58, ∑ σ : Fin 2,
        ((|P450.oneBodyEigenvalue ℓ| : ℝ) : ℂ) •
          ((oneBodyProjector ℓ σ)ᴴ * oneBodyProjector ℓ σ) := by
    rw [Complex.ofReal_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
    have hu : ∑ p, P450.oneBodyVector ℓ p ^ 2 = 1 := givensLeaf_sum_sq 15 _
    have h0 := abstract_oneBody_sos_term
      (orbitalNumberOp 58 (P450.oneBodyVector ℓ) 0)
      (orbitalNumberOp_conjTranspose 58 (P450.oneBodyVector ℓ) 0)
      (orbitalNumberOp_mul_self 58 hu 0)
      (P450.oneBodyEigenvalue ℓ)
    have h1 := abstract_oneBody_sos_term
      (orbitalNumberOp 58 (P450.oneBodyVector ℓ) 1)
      (orbitalNumberOp_conjTranspose 58 (P450.oneBodyVector ℓ) 1)
      (orbitalNumberOp_mul_self 58 hu 1)
      (P450.oneBodyEigenvalue ℓ)
    rw [Fin.sum_univ_two]
    have hp0 :
        ((|P450.oneBodyEigenvalue ℓ| : ℝ) : ℂ) •
            ((oneBodyProjector ℓ 0)ᴴ * oneBodyProjector ℓ 0) =
          (P450.oneBodyEigenvalue ℓ : ℂ) • orbitalNumberOp 58 (P450.oneBodyVector ℓ) 0 -
            ((if P450.oneBodyEigenvalue ℓ < 0 then
              P450.oneBodyEigenvalue ℓ else 0 : ℝ) : ℂ) • 1 :=
      h0
    have hp1 :
        ((|P450.oneBodyEigenvalue ℓ| : ℝ) : ℂ) •
            ((oneBodyProjector ℓ 1)ᴴ * oneBodyProjector ℓ 1) =
          (P450.oneBodyEigenvalue ℓ : ℂ) • orbitalNumberOp 58 (P450.oneBodyVector ℓ) 1 -
            ((if P450.oneBodyEigenvalue ℓ < 0 then
              P450.oneBodyEigenvalue ℓ else 0 : ℝ) : ℂ) • 1 :=
      h1
    rw [hp0, hp1]
    have hite :
        ((if P450.oneBodyEigenvalue ℓ < 0 then 2 * P450.oneBodyEigenvalue ℓ else 0 : ℝ) : ℂ) =
          (2 : ℂ) * ((if P450.oneBodyEigenvalue ℓ < 0 then
            P450.oneBodyEigenvalue ℓ else 0 : ℝ) : ℂ) := by
      split_ifs <;> push_cast <;> ring
    rw [hite]
    exact smul_add_sub_two_smul _ _ _ _ _
  have hfrag_sos :
      (∑ r : Fin 9, ∑ c : Fin 14, (P450.fragmentShift r c : ℂ) • K r c) +
        (∑ r : Fin 9, ∑ c : Fin 14, (2 : ℂ)⁻¹ • (K r c * K r c)) +
        ((2⁻¹ * ∑ r : Fin 9, ∑ c : Fin 14, P450.fragmentShift r c ^ 2 : ℝ) : ℂ) • 1 =
      ∑ r : Fin 9, ∑ c : Fin 14,
        ((2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit : ℝ) : ℂ) •
          ((fragmentLCU r c)ᴴ * fragmentLCU r c) := by
    simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    have hsq_id := abstract_fragment_square_identity
      (K r c) (fragmentLCU r c) (fragmentLCU_conjTranspose r c)
      (P450.fragmentShift r c) (fragmentScale r c)
      (fragmentShift_add_sum_eq_fragmentLCU r c)
    rw [hsq_id]
    have hnonneg : 0 ≤ 4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit := by
      have := coefficientUnit_pos
      positivity
    have hS : fragmentScale r c ^ 2 = 4 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit :=
      Real.sq_sqrt hnonneg
    have hscalar : 2⁻¹ * fragmentScale r c ^ 2 =
        2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit := by
      rw [hS]
      ring
    rw [hscalar]
  unfold thcHamiltonian dfthcLowerBound
  rw [h1e, h2e, Complex.ofReal_sub, sub_smul, add_three_sub_sub, hob_sos, hfrag_sos]

/-- The outer nonnegative SOS weights sum to `2 * 97.3864` (`2 * Λ`), with zero wasted padding. -/
theorem outer_sos_weights_sum_eq_two_lambda :
    (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |P450.oneBodyEigenvalue ℓ|) +
      (∑ r : Fin 9, ∑ c : Fin 14, 2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) =
      2 * 97.3864 := by
  have hq : 0 ≤ P450.coefficientUnit := le_of_lt coefficientUnit_pos
  have hob (ℓ : Fin 58) :
      (∑ _σ : Fin 2, |P450.oneBodyEigenvalue ℓ|) =
        2 * ((oneBodyWeightInt ℓ).natAbs : ℝ) * P450.coefficientUnit := by
    rw [Fin.sum_univ_two, oneBodyEigenvalue_eq_weightInt, abs_mul, abs_of_nonneg hq,
      ← natAbs_cast_real]
    ring
  simp only [hob]
  have hfactor :
      (∑ ℓ : Fin 58, 2 * ((oneBodyWeightInt ℓ).natAbs : ℝ) * P450.coefficientUnit) +
        (∑ r : Fin 9, ∑ c : Fin 14, 2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) =
      2 * (((∑ ℓ : Fin 58, (oneBodyWeightInt ℓ).natAbs) +
          (∑ r : Fin 9, ∑ c : Fin 14, fragmentWeightNat r c) : ℕ) : ℝ) *
        P450.coefficientUnit := by
    have h1 :
        (∑ ℓ : Fin 58, 2 * ((oneBodyWeightInt ℓ).natAbs : ℝ) * P450.coefficientUnit) =
          (∑ ℓ : Fin 58, ((oneBodyWeightInt ℓ).natAbs : ℝ)) * (2 * P450.coefficientUnit) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ℓ _ ↦ by ring
    have h2 :
        (∑ r : Fin 9, ∑ c : Fin 14, 2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) =
          (∑ r : Fin 9, ∑ c : Fin 14, (fragmentWeightNat r c : ℝ)) *
            (2 * P450.coefficientUnit) := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
    rw [h1, h2, Nat.cast_add]
    simp only [Nat.cast_sum]
    ring
  rw [hfactor, outerWeights_sum_eq_188416]
  unfold P450.coefficientUnit
  norm_num

/-! ## Section 5: Rayleigh Quotient & Eigenvalue Spectrum Bounds -/

theorem weighted_sq_sum_le {ι : Type*} (s : Finset ι) (p x : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    (∑ i ∈ s, p i * x i) ^ 2 ≤ (∑ j ∈ s, p j) * (∑ i ∈ s, p i * x i ^ 2) := by
  have hlagrange :
      2 * ((∑ j ∈ s, p j) * (∑ i ∈ s, p i * x i ^ 2) - (∑ i ∈ s, p i * x i) ^ 2) =
        ∑ j ∈ s, ∑ i ∈ s, p j * p i * (x j - x i) ^ 2 := by
    have hterm (j i : ι) :
        p j * p i * (x j - x i) ^ 2 =
          p j * (p i * x i ^ 2) + (p j * x j ^ 2) * p i - 2 * ((p j * x j) * (p i * x i)) := by
      ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  have hnn : 0 ≤ ∑ j ∈ s, ∑ i ∈ s, p j * p i * (x j - x i) ^ 2 :=
    Finset.sum_nonneg fun j hj ↦ Finset.sum_nonneg fun i hi ↦
      mul_nonneg (mul_nonneg (hp j hj) (hp i hi)) (sq_nonneg _)
  linarith

theorem complex_normSq_weighted_sum_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) (z : ι → ℂ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Complex.normSq (∑ i ∈ s, (p i : ℂ) * z i) ≤
      (∑ j ∈ s, p j) * (∑ i ∈ s, p i * Complex.normSq (z i)) := by
  have hre : (∑ i ∈ s, (p i : ℂ) * z i).re = ∑ i ∈ s, p i * (z i).re := by
    simp [Complex.re_sum]
  have him : (∑ i ∈ s, (p i : ℂ) * z i).im = ∑ i ∈ s, p i * (z i).im := by
    simp [Complex.im_sum]
  have h1 := weighted_sq_sum_le s p (fun i ↦ (z i).re) hp
  have h2 := weighted_sq_sum_le s p (fun i ↦ (z i).im) hp
  have hns (w : ℂ) : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  rw [hns, hre, him]
  calc (∑ i ∈ s, p i * (z i).re) ^ 2 + (∑ i ∈ s, p i * (z i).im) ^ 2
      ≤ (∑ j ∈ s, p j) * (∑ i ∈ s, p i * (z i).re ^ 2) +
          (∑ j ∈ s, p j) * (∑ i ∈ s, p i * (z i).im ^ 2) := add_le_add h1 h2
    _ = (∑ j ∈ s, p j) * (∑ i ∈ s, p i * Complex.normSq (z i)) := by
        simp only [hns, mul_add, Finset.sum_add_distrib]

theorem dotProduct_star_self_re {d : ℕ} (v : Fin d → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
  simp [dotProduct, ← Complex.normSq_eq_conj_mul_self, Complex.re_sum]

theorem dotProduct_star_conjTranspose_mul_self_re {d : ℕ} (M : Operator d)
    (ψ : Fin d → ℂ) :
    (star ψ ⬝ᵥ ((Mᴴ * M) *ᵥ ψ)).re = ∑ i, Complex.normSq ((M *ᵥ ψ) i) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    dotProduct_star_self_re]

theorem sum_normSq_isometry_mulVec {d : ℕ} (U : Operator d) (hU : Uᴴ * U = 1)
    (ψ : Fin d → ℂ) :
    ∑ i, Complex.normSq ((U *ᵥ ψ) i) = ∑ i, Complex.normSq (ψ i) := by
  rw [← dotProduct_star_conjTranspose_mul_self_re, hU, Matrix.one_mulVec, dotProduct_star_self_re]

theorem smul_mulVec_eq {d : ℕ} (a : ℂ) (M : Operator d) (ψ : Fin d → ℂ) :
    (a • M) *ᵥ ψ = a • (M *ᵥ ψ) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    mul_assoc, Finset.mul_sum]

theorem sum_mulVec_eq {ι : Type*} {d : ℕ} (s : Finset ι) (M : ι → Operator d)
    (ψ : Fin d → ℂ) :
    (∑ k ∈ s, M k) *ᵥ ψ = ∑ k ∈ s, (M k *ᵥ ψ) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem normSq_half_add_le (z₀ z₁ : ℂ) :
    Complex.normSq ((z₀ + z₁) / 2) ≤ (Complex.normSq z₀ + Complex.normSq z₁) / 2 := by
  have hdiv : (z₀ + z₁) / 2 = ((2⁻¹ : ℝ) : ℂ) * (z₀ + z₁) := by
    push_cast
    ring
  rw [hdiv, map_mul, Complex.normSq_ofReal, Complex.normSq_apply (z₀ + z₁),
    Complex.normSq_apply z₀, Complex.normSq_apply z₁, Complex.add_re, Complex.add_im]
  have hre : 0 ≤ (z₀.re - z₁.re) ^ 2 := sq_nonneg _
  have him : 0 ≤ (z₀.im - z₁.im) ^ 2 := sq_nonneg _
  linarith

theorem sum_normSq_lcu_vec_le {ι : Type*} {d : ℕ} (s : Finset ι)
    (c : ι → ℝ) (w : ι → Fin d → ℂ) (S : ℝ) (hS : 0 ≤ S)
    (hw : ∀ i ∈ s, ∑ x, Complex.normSq (w i x) ≤ S)
    (hl1 : ∑ i ∈ s, |c i| ≤ 1) :
    ∑ x : Fin d, Complex.normSq (∑ i ∈ s, (c i : ℂ) * w i x) ≤ S := by
  let p : ι → ℝ := fun i ↦ |c i|
  let z : ι → Fin d → ℂ := fun i x ↦ (if 0 ≤ c i then (1 : ℂ) else -1) * w i x
  have hcz (i : ι) (x : Fin d) : (c i : ℂ) * w i x = (p i : ℂ) * z i x := by
    simp only [p, z, ← mul_assoc]
    by_cases h : 0 ≤ c i
    · simp only [h, ↓reduceIte, abs_of_nonneg h, mul_one]
    · have hn : c i < 0 := not_le.mp h
      simp only [h, ↓reduceIte, abs_of_neg hn, Complex.ofReal_neg, mul_neg, mul_one, neg_neg]
  have hznorm (i : ι) (x : Fin d) : Complex.normSq (z i x) = Complex.normSq (w i x) := by
    simp only [z, map_mul]
    split_ifs <;> simp only [Complex.normSq_neg, map_one, one_mul]
  have hp : ∀ i ∈ s, 0 ≤ p i := fun i _ ↦ abs_nonneg (c i)
  have hpt (x : Fin d) :
      Complex.normSq (∑ i ∈ s, (c i : ℂ) * w i x) ≤
        (∑ j ∈ s, p j) * (∑ i ∈ s, p i * Complex.normSq (w i x)) := by
    simp only [hcz]
    simpa only [hznorm] using complex_normSq_weighted_sum_le s p (fun i ↦ z i x) hp
  calc ∑ x : Fin d, Complex.normSq (∑ i ∈ s, (c i : ℂ) * w i x)
      ≤ ∑ x : Fin d, (∑ j ∈ s, p j) * (∑ i ∈ s, p i * Complex.normSq (w i x)) :=
        Finset.sum_le_sum fun x _ ↦ hpt x
    _ = (∑ j ∈ s, p j) * ∑ i ∈ s, p i * (∑ x, Complex.normSq (w i x)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [← Finset.mul_sum]
    _ ≤ (∑ j ∈ s, p j) * ∑ i ∈ s, p i * S := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg hp)
        exact Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hw i hi) (hp i hi)
    _ = (∑ j ∈ s, p j) ^ 2 * S := by
        rw [← Finset.sum_mul, sq, mul_assoc]
    _ ≤ 1 * S := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        have hsum_nn : 0 ≤ ∑ j ∈ s, p j := Finset.sum_nonneg hp
        nlinarith [hl1]
    _ = S := one_mul S

theorem abstract_oneBodyProjector_normSq_le {d : ℕ} (R : Operator d)
    (hR_conj : Rᴴ = R) (hR_mul : R * R = 1) (s : ℝ) (hs : s ^ 2 = 1)
    (ψ : Fin d → ℂ) :
    let P : Operator d := (2 : ℂ)⁻¹ • (1 - (s : ℂ) • R)
    ∑ i, Complex.normSq ((P *ᵥ ψ) i) ≤ ∑ i, Complex.normSq (ψ i) := by
  intro P
  have hR_iso : Rᴴ * R = 1 := by rw [hR_conj, hR_mul]
  have hpt (x : Fin d) :
      Complex.normSq ((P *ᵥ ψ) x) ≤
        (Complex.normSq (ψ x) + Complex.normSq ((R *ᵥ ψ) x)) / 2 := by
    have hpx : (P *ᵥ ψ) x = (ψ x + (-(s : ℂ) * (R *ᵥ ψ) x)) / 2 := by
      simp only [P, smul_mulVec_eq, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul]
      ring
    rw [hpx]
    have h1 := normSq_half_add_le (ψ x) (-(s : ℂ) * (R *ᵥ ψ) x)
    have hns : Complex.normSq (-(s : ℂ) * (R *ᵥ ψ) x) = Complex.normSq ((R *ᵥ ψ) x) := by
      rw [map_mul, Complex.normSq_neg, Complex.normSq_ofReal, ← sq, hs, one_mul]
    rw [hns] at h1
    exact h1
  calc ∑ x, Complex.normSq ((P *ᵥ ψ) x)
      ≤ ∑ x, (Complex.normSq (ψ x) + Complex.normSq ((R *ᵥ ψ) x)) / 2 :=
        Finset.sum_le_sum fun x _ ↦ hpt x
    _ = ((∑ x, Complex.normSq (ψ x)) + ∑ x, Complex.normSq ((R *ᵥ ψ) x)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = ∑ x, Complex.normSq (ψ x) := by
        rw [sum_normSq_isometry_mulVec R hR_iso ψ]
        ring

theorem sum_normSq_oneBodyProjector_mulVec_le (ℓ : Fin 58) (σ : Fin 2)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    ∑ i, Complex.normSq ((oneBodyProjector ℓ σ *ᵥ ψ) i) ≤ ∑ i, Complex.normSq (ψ i) := by
  have hs : oneBodySign ℓ ^ 2 = 1 := by
    unfold oneBodySign
    split_ifs <;> norm_num
  exact abstract_oneBodyProjector_normSq_le _
    (orbitalReflection_conjTranspose 58 _ σ)
    (orbitalReflection_mul_self 58 (givensLeaf_sum_sq 15 _) σ) _ hs ψ

theorem abstract_fragmentLCU_normSq_le {d : ℕ}
    (R : Fin 29 → Fin 2 → Operator d)
    (hR_conj : ∀ b σ, (R b σ)ᴴ = R b σ)
    (hR_mul : ∀ b σ, R b σ * R b σ = 1)
    (m : Fin 30 → ℤ) (hm : ∑ b : Fin 30, (m b).natAbs = 15360)
    (ψ : Fin d → ℂ) :
    let A : Operator d := ((15360 : ℂ)⁻¹) •
      ((m 29 : ℂ) • (1 : Operator d) -
        ∑ b : Fin 29, ∑ σ : Fin 2, ((m b.castSucc : ℂ) / 2) • R b σ)
    ∑ i, Complex.normSq ((A *ᵥ ψ) i) ≤ ∑ i, Complex.normSq (ψ i) := by
  intro A
  let S : ℝ := ∑ x, Complex.normSq (ψ x)
  have hS : 0 ≤ S := Finset.sum_nonneg fun x _ ↦ Complex.normSq_nonneg (ψ x)
  let c : Fin 30 → ℝ := fun b ↦ (m b : ℝ) / 15360
  let w : Fin 30 → Fin d → ℂ := fun b x ↦
    if h : b.val < 29 then
      -(((R ⟨b.val, h⟩ 0 *ᵥ ψ) x + (R ⟨b.val, h⟩ 1 *ᵥ ψ) x) / 2)
    else
      ψ x
  have hAx (x : Fin d) : (A *ᵥ ψ) x = ∑ b : Fin 30, (c b : ℂ) * w b x := by
    rw [Fin.sum_univ_castSucc]
    have h29_lt : ¬ (29 : Fin 30).val < 29 := by decide
    have hlast_eq : (Fin.last 29 : Fin 30) = 29 := rfl
    have hlast : (c (Fin.last 29) : ℂ) * w (Fin.last 29) x =
        (15360 : ℂ)⁻¹ * ((m 29 : ℂ) * ψ x) := by
      simp only [w, c, hlast_eq, h29_lt, ↓reduceDIte]
      push_cast
      ring
    have hb (b : Fin 29) :
        (c b.castSucc : ℂ) * w b.castSucc x =
          -((15360 : ℂ)⁻¹ *
            (((m b.castSucc : ℂ) / 2) * (R b 0 *ᵥ ψ) x +
              ((m b.castSucc : ℂ) / 2) * (R b 1 *ᵥ ψ) x)) := by
      have hblt : b.castSucc.val < 29 := b.isLt
      have hbeq : (⟨b.castSucc.val, hblt⟩ : Fin 29) = b := Fin.ext rfl
      simp only [w, hblt, ↓reduceDIte, hbeq, c]
      push_cast
      ring
    simp only [A, smul_mulVec_eq, Matrix.sub_mulVec, Matrix.one_mulVec, sum_mulVec_eq,
      Fin.sum_univ_two, Matrix.add_mulVec, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
      Pi.add_apply, smul_eq_mul, hlast, hb, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  have hw : ∀ b ∈ (Finset.univ : Finset (Fin 30)), ∑ x, Complex.normSq (w b x) ≤ S := by
    intro b _
    by_cases h : b.val < 29
    · simp only [w, h, ↓reduceDIte, Complex.normSq_neg]
      let b' : Fin 29 := ⟨b.val, h⟩
      have hiso0 : (R b' 0)ᴴ * R b' 0 = 1 := by rw [hR_conj, hR_mul]
      have hiso1 : (R b' 1)ᴴ * R b' 1 = 1 := by rw [hR_conj, hR_mul]
      calc ∑ x, Complex.normSq (((R b' 0 *ᵥ ψ) x + (R b' 1 *ᵥ ψ) x) / 2)
          ≤ ∑ x, (Complex.normSq ((R b' 0 *ᵥ ψ) x) + Complex.normSq ((R b' 1 *ᵥ ψ) x)) / 2 :=
            Finset.sum_le_sum fun x _ ↦ normSq_half_add_le _ _
        _ = ((∑ x, Complex.normSq ((R b' 0 *ᵥ ψ) x)) +
              ∑ x, Complex.normSq ((R b' 1 *ᵥ ψ) x)) / 2 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
        _ = S := by
            rw [sum_normSq_isometry_mulVec (R b' 0) hiso0 ψ,
              sum_normSq_isometry_mulVec (R b' 1) hiso1 ψ]
            dsimp only [S]
            ring
    · simp only [w, h, ↓reduceDIte]
      exact le_rfl
  have hl1 : ∑ b : Fin 30, |c b| ≤ 1 := by
    have hcb (b : Fin 30) : |c b| = ((m b).natAbs : ℝ) / 15360 := by
      simp only [c, abs_div, ← natAbs_cast_real]
      norm_num
    simp only [hcb, ← Finset.sum_div, ← Nat.cast_sum, hm]
    norm_num
  simp only [hAx]
  exact sum_normSq_lcu_vec_le Finset.univ c w S hS hw hl1

theorem sum_normSq_fragmentLCU_mulVec_le (r : Fin 9) (c : Fin 14)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    ∑ i, Complex.normSq ((fragmentLCU r c *ᵥ ψ) i) ≤ ∑ i, Complex.normSq (ψ i) :=
  abstract_fragmentLCU_normSq_le
    (fun b σ ↦ orbitalReflection 58 (P450.leafVector (leafIndex r b)) σ)
    (fun _b σ ↦ orbitalReflection_conjTranspose 58 _ σ)
    (fun _b σ ↦ orbitalReflection_mul_self 58 (givensLeaf_sum_sq 15 _) σ)
    (innerMantissa r c)
    (innerWeights_l1_eq_15360 r c)
    ψ

theorem abstract_sos_conjTranspose {d : ℕ} (H : Operator d) (E₀ : ℝ)
    (w₁ : Fin 58 → Fin 2 → ℝ) (P : Fin 58 → Fin 2 → Operator d)
    (w₂ : Fin 9 → Fin 14 → ℝ) (A : Fin 9 → Fin 14 → Operator d)
    (hSOS : H - (E₀ : ℂ) • 1 =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2, (w₁ ℓ σ : ℂ) • ((P ℓ σ)ᴴ * P ℓ σ)) +
      (∑ r : Fin 9, ∑ c : Fin 14, (w₂ r c : ℂ) • ((A r c)ᴴ * A r c))) :
    Hᴴ = H := by
  have heq : H = (E₀ : ℂ) • 1 +
      ((∑ ℓ : Fin 58, ∑ σ : Fin 2, (w₁ ℓ σ : ℂ) • ((P ℓ σ)ᴴ * P ℓ σ)) +
      (∑ r : Fin 9, ∑ c : Fin 14, (w₂ r c : ℂ) • ((A r c)ᴴ * A r c))) := by
    rw [← hSOS, add_sub_cancel]
  rw [heq]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_ofReal]

/-- `thcHamiltonian P450.dfthc` is Hermitian. -/
theorem thcHamiltonian_dfthc_conjTranspose :
    (thcHamiltonian P450.dfthc)ᴴ = thcHamiltonian P450.dfthc :=
  abstract_sos_conjTranspose
    (thcHamiltonian P450.dfthc) dfthcLowerBound
    (fun ℓ _ ↦ |P450.oneBodyEigenvalue ℓ|) oneBodyProjector
    (fun r c ↦ 2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) fragmentLCU
    thcHamiltonian_sub_lowerBound_eq_sos

theorem abstract_sos_quadratic_diff {d : ℕ} (H : Operator d) (E₀ : ℝ)
    (w₁ : Fin 58 → Fin 2 → ℝ) (P : Fin 58 → Fin 2 → Operator d)
    (w₂ : Fin 9 → Fin 14 → ℝ) (A : Fin 9 → Fin 14 → Operator d)
    (hSOS : H - (E₀ : ℂ) • 1 =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2, (w₁ ℓ σ : ℂ) • ((P ℓ σ)ᴴ * P ℓ σ)) +
      (∑ r : Fin 9, ∑ c : Fin 14, (w₂ r c : ℂ) • ((A r c)ᴴ * A r c)))
    (ψ : Fin d → ℂ) :
    (star ψ ⬝ᵥ (H *ᵥ ψ)).re - E₀ * (∑ i, Complex.normSq (ψ i)) =
      (∑ ℓ : Fin 58, ∑ σ : Fin 2, w₁ ℓ σ * (∑ i, Complex.normSq ((P ℓ σ *ᵥ ψ) i))) +
      (∑ r : Fin 9, ∑ c : Fin 14, w₂ r c * (∑ i, Complex.normSq ((A r c *ᵥ ψ) i))) := by
  have hsub :
      (star ψ ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ ψ)).re =
        (star ψ ⬝ᵥ (H *ᵥ ψ)).re - E₀ * (∑ i, Complex.normSq (ψ i)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec_eq,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, dotProduct_star_self_re]
  rw [← hsub, hSOS, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  congr 1
  · simp only [sum_mulVec_eq, smul_mulVec_eq, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, dotProduct_star_conjTranspose_mul_self_re]
  · simp only [sum_mulVec_eq, smul_mulVec_eq, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, dotProduct_star_conjTranspose_mul_self_re]

/-- Homogeneous Rayleigh-quotient bounds on `thcHamiltonian P450.dfthc` for every state `ψ`. -/
theorem thcHamiltonian_dfthc_quadratic_bounds (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    dfthcLowerBound * (∑ i, Complex.normSq (ψ i)) ≤
        (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re ∧
      (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re ≤
        (dfthcLowerBound + 2 * 97.3864) * (∑ i, Complex.normSq (ψ i)) := by
  let S := ∑ i, Complex.normSq (ψ i)
  have hdiff :
      (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re - dfthcLowerBound * S =
        (∑ ℓ : Fin 58, ∑ σ : Fin 2,
          |P450.oneBodyEigenvalue ℓ| *
            (∑ i, Complex.normSq ((oneBodyProjector ℓ σ *ᵥ ψ) i))) +
        (∑ r : Fin 9, ∑ c : Fin 14,
          (2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) *
            (∑ i, Complex.normSq ((fragmentLCU r c *ᵥ ψ) i))) :=
    abstract_sos_quadratic_diff
      (thcHamiltonian P450.dfthc) dfthcLowerBound
      (fun ℓ _ ↦ |P450.oneBodyEigenvalue ℓ|) oneBodyProjector
      (fun r c ↦ 2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) fragmentLCU
      thcHamiltonian_sub_lowerBound_eq_sos ψ
  have hhq : 0 ≤ P450.coefficientUnit := le_of_lt coefficientUnit_pos
  have hlow : 0 ≤ (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re - dfthcLowerBound * S := by
    rw [hdiff]
    refine add_nonneg
      (Finset.sum_nonneg fun ℓ _ ↦ Finset.sum_nonneg fun σ _ ↦
        mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _))
      (Finset.sum_nonneg fun r _ ↦ Finset.sum_nonneg fun c _ ↦
        mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _))
  have hhigh :
      (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re - dfthcLowerBound * S ≤
        (2 * 97.3864) * S := by
    rw [hdiff]
    have h1 :
        (∑ ℓ : Fin 58, ∑ σ : Fin 2,
          |P450.oneBodyEigenvalue ℓ| *
            (∑ i, Complex.normSq ((oneBodyProjector ℓ σ *ᵥ ψ) i))) ≤
        (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |P450.oneBodyEigenvalue ℓ|) * S := by
      simp only [Finset.sum_mul]
      exact Finset.sum_le_sum fun ℓ _ ↦ Finset.sum_le_sum fun σ _ ↦
        mul_le_mul_of_nonneg_left (sum_normSq_oneBodyProjector_mulVec_le ℓ σ ψ) (abs_nonneg _)
    have h2 :
        (∑ r : Fin 9, ∑ c : Fin 14,
          (2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) *
            (∑ i, Complex.normSq ((fragmentLCU r c *ᵥ ψ) i))) ≤
        (∑ r : Fin 9, ∑ c : Fin 14,
          2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) * S := by
      simp only [Finset.sum_mul]
      exact Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun c _ ↦
        mul_le_mul_of_nonneg_left (sum_normSq_fragmentLCU_mulVec_le r c ψ) (by positivity)
    calc _ ≤ (∑ ℓ : Fin 58, ∑ _σ : Fin 2, |P450.oneBodyEigenvalue ℓ|) * S +
            (∑ r : Fin 9, ∑ c : Fin 14,
              2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit) * S := add_le_add h1 h2
      _ = ((∑ ℓ : Fin 58, ∑ _σ : Fin 2, |P450.oneBodyEigenvalue ℓ|) +
            (∑ r : Fin 9, ∑ c : Fin 14,
              2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit)) * S := by ring
      _ = (2 * 97.3864) * S := by rw [outer_sos_weights_sum_eq_two_lambda]
  constructor <;> linarith

/-- **Eigenvalue Bounds:** Every real eigenvalue `E` of `thcHamiltonian P450.dfthc` (with nonzero
eigenvector `ψ`) lies in `[dfthcLowerBound, dfthcLowerBound + 2 * 97.3864]`. -/
theorem thcHamiltonian_dfthc_eigenvalue_mem_Icc (E : ℝ) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (heig : thcHamiltonian P450.dfthc *ᵥ ψ = (E : ℂ) • ψ) (hne : ψ ≠ 0) :
    E ∈ Set.Icc dfthcLowerBound (dfthcLowerBound + 2 * 97.3864) := by
  have hpos : 0 < ∑ i, Complex.normSq (ψ i) := by
    by_contra hle
    have hzero : ∑ i, Complex.normSq (ψ i) = 0 :=
      le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Complex.normSq_nonneg (ψ i)).mp hzero
    apply hne
    ext i
    exact Complex.normSq_eq_zero.mp (hall i (Finset.mem_univ i))
  have hray : (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re =
      E * ∑ i, Complex.normSq (ψ i) := by
    rw [heig, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, dotProduct_star_self_re]
  have ⟨hlo, hhi⟩ := thcHamiltonian_dfthc_quadratic_bounds ψ
  rw [hray] at hlo hhi
  exact ⟨le_of_mul_le_mul_right hlo hpos, le_of_mul_le_mul_right hhi hpos⟩

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
