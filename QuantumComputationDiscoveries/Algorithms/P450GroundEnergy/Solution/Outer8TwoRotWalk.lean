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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Prep
public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20Reduced2504
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145SOSPermBridge

set_option exponentiation.threshold 512

@[expose] public section

/-!
# Exact Column-`0` `L¹` Grover-`184` Perturbation & Zero-Walk-Error `wOuter = 8` Outer `PREP`

Eliminates the `2 * M * δOut` QPE walk-loop perturbation (`δOut = 0` inside `WalkRefl2ErrLe`,
`δStep = δSelFwd + δSelBwd`, `= 0` for exact `SELECT`) by absorbing the synthesized `wOuter = 8`
outer `PREP` unitary `prepOutImpl` directly into the spin-blocked SOS Hamiltonian
`fullQuantP450HBlocked prepOutImpl prepMid B_sel` (`eLB = dfthcLowerBound`, `lam = 97.3864`),
and proving a tight closed-form column-`0` `L¹` probability deviation bound `grover184L1Upper`
across the `9`-qubit Grover-`184` + real `4`-qubit packet coin `optCoin10Unitary` + zero-shear
QROM/CSWAP permutation `postPerm17Bits`:
- **`Word25` (`730 T/Refl2 = 375 + 355`, `87 ≤ sUb`):** `εOut_L1 ≤ 2 / 10 ^ 10`,
  `2 * 97.3864 * εOut_L1 ≤ 0.039 µHa` (`δStep = 0`, valid directly at `M = 46,687`).
- **`Word19` (`694 T/Refl2 = 357 + 337`, `87 ≤ sUb`):** `εOut_L1 ≤ 13 / 10 ^ 7`,
  `2 * 97.3864 * εOut_L1 ≤ 253.3 µHa` (`δStep = 0`).

## References
- V. Kliuchnikov, D. Maslov, and M. Mosca, *Quantum Inf. Comput.* **13**, 607–630 (2013),
  arXiv:1206.5236.
- N. J. Ross and P. Selinger, *Quantum Inf. Comput.* **16**, 901–953 (2016), arXiv:1403.2975.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145L1
open QuantumComputation.Specs QuantumComputation.Specs.P450
section GroverL1

open Operator QProg Matrix Circuit Real
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CoherentAlias
open Solution.OuterWeights.GroverUniform
open scoped Matrix BigOperators Circuit.Notation

theorem val_lt_two_pow_iff_bits_zero {n m : ℕ} (g : Fin (2 ^ n)) :
    g.val < 2 ^ m ↔ ∀ i : Fin n, m ≤ i.val → basisBits n g i = 0 := by
  constructor
  · intro hlt i hi
    have hpow : 2 ^ m ≤ 2 ^ i.val := Nat.pow_le_pow_right (by omega) hi
    have hdiv : g.val / 2 ^ i.val = 0 :=
      Nat.div_eq_zero_iff.mpr (Or.inr (lt_of_lt_of_le hlt hpow))
    rw [basisBits_eq_div_mod, hdiv]; norm_num
  · intro hzero
    suffices heq : g.val = g.val % 2 ^ m by
      rw [heq]; exact Nat.mod_lt g.val (by positivity)
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_mod_two_pow]
    by_cases hkm : k < m
    · simp [hkm]
    · simp only [hkm, decide_false, Bool.false_and]
      by_cases hkn : k < n
      · have hz := hzero ⟨k, hkn⟩ (Nat.le_of_not_lt hkm)
        rw [basisBits_eq_testBit] at hz; dsimp only at hz
        cases htb : g.val.testBit k
        · rfl
        · rw [htb] at hz; simp at hz
      · exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le g.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

theorem uAGroverUnitary_mulVec_zero_of_ge (b : ℕ) (W : Unitary 2)
    (y : Fin (2 ^ (b + 1))) (hy : 2 ^ b ≤ y.val) :
    ((uAGroverUnitary b W).1 *ᵥ Pi.single 0 1) y =
      (((1 / √2 : ℝ) ^ b : ℝ) : ℂ) * W.1 1 0 := by
  let r := QRegister.singleton (⟨b, by omega⟩ : Wire (b + 1))
  have hb1 : basisBits (b + 1) y ⟨b, by omega⟩ = 1 := by
    rcases SelectSwapQROM.bit_cases (basisBits (b + 1) y ⟨b, by omega⟩) with h0 | h1
    · exfalso
      have hlt : y.val < 2 ^ b := (val_lt_two_pow_iff_bits_zero y).mpr fun i hi ↦ by
        have hid : i = ⟨b, by omega⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        rwa [hid]
      omega
    · exact h1
  have hr_ext : r.extractIndex y = 1 := by
    apply (basisBits 1).injective
    funext i; fin_cases i
    change basisBits 1 (r.extractIndex y) 0 = basisBits 1 1 0
    have hb11 : basisBits 1 1 0 = 1 := by decide
    rw [r.basisBits_extractIndex, hb11]; simpa [r] using hb1
  have hr0_lt : (r.replaceIndex y 0).val < 2 ^ b := by
    rw [val_lt_two_pow_iff_bits_zero]
    intro i hi
    have hid : i = r 0 := Fin.ext (by have := i.isLt; simp [r]; omega)
    rw [hid, r.basisBits_replaceIndex_apply]; decide
  have hr1_not_lt : ¬ (r.replaceIndex y 1).val < 2 ^ b := by
    rw [val_lt_two_pow_iff_bits_zero]
    intro h
    have hz := h (r 0) (by simp [r])
    rw [r.basisBits_replaceIndex_apply] at hz
    exact absurd hz (by decide)
  have hsum2 (f : Fin (2 ^ 1) → ℂ) : (∑ i : Fin (2 ^ 1), f i) = f 0 + f 1 :=
    Fin.sum_univ_two f
  simp only [uAGroverUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val]
  rw [r.embedMatrix_mulVec_apply, hsum2]
  change W.1 (r.extractIndex y) 0 *
      ((hadamardPrefix b (b + 1) (by omega)).eval.1 *ᵥ Pi.single 0 1) (r.replaceIndex y 0) +
    W.1 (r.extractIndex y) 1 *
      ((hadamardPrefix b (b + 1) (by omega)).eval.1 *ᵥ Pi.single 0 1) (r.replaceIndex y 1) = _
  rw [hadamardPrefix_mulVec_zero _ _ _ (r.replaceIndex y 0),
    hadamardPrefix_mulVec_zero _ _ _ (r.replaceIndex y 1),
    ite_eq_left hr0_lt, ite_eq_right hr1_not_lt, hr_ext, mul_zero, add_zero, mul_comm]

theorem card_filter_val_lt2 {d M : ℕ} (hM : M ≤ d) :
    (Finset.univ.filter (fun g : Fin d ↦ g.val < M)).card = M := by
  have heq : Finset.univ.filter (fun g : Fin d ↦ g.val < M) =
      (Finset.range M).attach.map
        ⟨fun x ↦ ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hM⟩,
         fun x y h ↦ Subtype.ext (Fin.mk.inj h)⟩ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_attach]
    refine ⟨fun hg ↦ ⟨⟨g.val, Finset.mem_range.mpr hg⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, rfl⟩
    exact Finset.mem_range.mp hx
  rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]

theorem block_extractIndex_val2 (a m : ℕ) (h : a + m ≤ a + m) (g : Fin (2 ^ (a + m))) :
    ((QRegister.block a m h).extractIndex g).val = g.val / 2 ^ a := by
  have hlt : g.val / 2 ^ a < 2 ^ m :=
    Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact g.isLt)
  suffices hfin : (QRegister.block a m h).extractIndex g = ⟨g.val / 2 ^ a, hlt⟩ by
    exact congrArg Fin.val hfin
  apply (basisBits m).injective
  funext i
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod,
    QRegister.block_apply_val]
  dsimp only
  rw [Nat.pow_add 2 a i.val, Nat.div_div_eq_div_mul]

theorem grover_good_prob_eq (b K : ℕ) (hK : K ≤ 2 ^ b) (W : Unitary 2) :
    (∑ y : Fin (2 ^ (b + 1)),
      if decide (y.val < K) then
        Complex.normSq (((uAGroverUnitary b W).1 *ᵥ Pi.single 0 1) y)
      else 0) =
    (K : ℝ) / (2 ^ b : ℝ) * Complex.normSq (W.1 0 0) := by
  have hterm :
      (∑ y : Fin (2 ^ (b + 1)),
        if decide (y.val < K) then
          Complex.normSq (((uAGroverUnitary b W).1 *ᵥ Pi.single 0 1) y)
        else 0) =
      ∑ y : Fin (2 ^ (b + 1)),
        if y.val < K then ((1 / √2 : ℝ) ^ b) ^ 2 * Complex.normSq (W.1 0 0) else 0 := by
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases hy : y.val < K
    · rw [decide_eq_true hy, ite_eq_left rfl, ite_eq_left hy,
        uAGroverUnitary_mulVec_zero_of_lt b W y (lt_of_lt_of_le hy hK),
        map_mul, Complex.normSq_ofReal, sq]
    · simp [hy]
  have hK_le : K ≤ 2 ^ (b + 1) := le_trans hK (Nat.pow_le_pow_right (by omega) (by omega))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpow_sq : ((1 / √2 : ℝ) ^ b) ^ 2 = 1 / (2 ^ b : ℝ) := by
    rw [← pow_mul, mul_comm b 2, pow_mul, div_pow, one_pow, hs2_sq, _root_.one_div_pow]
  rw [hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    card_filter_val_lt2 hK_le, nsmul_eq_mul, hpow_sq]
  ring

theorem hadamardPrefix_tensor (a b : ℕ) :
    (hadamardPrefix a (a + (b + 1)) (by omega)).eval.1 *ᵥ Pi.single 0 1 =
      (QRegister.block a (b + 1) (by omega)).tensorState (Pi.single 0 1)
        (fun _ ↦ (((1 / √2 : ℝ) ^ a : ℝ) : ℂ)) := by
  let rG : QRegister (b + 1) (a + (b + 1)) := QRegister.block a (b + 1) (by omega)
  funext x
  rw [hadamardPrefix_mulVec_zero]
  simp only [QRegister.tensorState, Pi.single_apply]
  have hzero : rG.extractIndex x = 0 ↔ x.val < 2 ^ a := by
    rw [Fin.ext_iff, block_extractIndex_val2 a (b + 1) _ x, Fin.val_zero, Nat.div_eq_zero_iff]
    have h2a : 0 < 2 ^ a := by positivity
    omega
  by_cases hx : x.val < 2 ^ a
  · rw [ite_eq_left hx, ite_eq_left (hzero.mpr hx), one_mul]
  · rw [ite_eq_right hx, ite_eq_right (mt hzero.mp hx), zero_mul]

theorem prepGroverUnitary_mulVec_zero_of_mid (a b K : ℕ) (hK : K ≤ 2 ^ b) (W : Unitary 2)
    (g : Fin (2 ^ (a + (b + 1)))) (hlo : 2 ^ a * K ≤ g.val) (hhi : g.val < 2 ^ (a + b)) :
    let p : ℝ := (K : ℝ) / (2 ^ b : ℝ) * Complex.normSq (W.1 0 0)
    ((prepGroverUnitary a b K W).1 *ᵥ Pi.single 0 1) g =
      ((1 - 4 * p : ℝ) : ℂ) * (((1 / √2 : ℝ) ^ (a + b) : ℝ) : ℂ) * W.1 0 0 := by
  intro p
  have : NeZero (2 ^ (b + 1)) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
  let rG : QRegister (b + 1) (a + (b + 1)) := QRegister.block a (b + 1) (by omega)
  have h2a : 0 < 2 ^ a := by positivity
  have hdiv_ge : K ≤ (rG.extractIndex g).val := by
    rw [block_extractIndex_val2 a (b + 1) _ g]
    exact (Nat.le_div_iff_mul_le h2a).mpr (by simpa [mul_comm] using hlo)
  have hdiv_lt : (rG.extractIndex g).val < 2 ^ b := by
    rw [block_extractIndex_val2 a (b + 1) _ g]
    exact Nat.div_lt_of_lt_mul (by rwa [← pow_add])
  have hnot_lt : ¬ (rG.extractIndex g).val < K := not_lt.mpr hdiv_ge
  simp only [prepGroverUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    QRegister.embedUnitary_val]
  rw [hadamardPrefix_tensor a b, rG.embedMatrix_mulVec_tensorState]
  simp only [QRegister.tensorState]
  rw [groverStepUnitary, groverStepGen_mulVec_single_zero, grover_good_prob_eq b K hK W]
  simp only [decide_eq_false hnot_lt, Bool.false_eq_true, ↓reduceIte,
    uAGroverUnitary_mulVec_zero_of_lt b W (rG.extractIndex g) hdiv_lt]
  have hpow_ab : (((1 / √2 : ℝ) ^ (a + b) : ℝ) : ℂ) =
      (((1 / √2 : ℝ) ^ a : ℝ) : ℂ) * (((1 / √2 : ℝ) ^ b : ℝ) : ℂ) := by
    rw [pow_add, Complex.ofReal_mul]
  dsimp only [p]; rw [hpow_ab]; ring

theorem prepGroverUnitary_mulVec_zero_of_ge_two_pow (a b K : ℕ) (hK : K ≤ 2 ^ b) (W : Unitary 2)
    (g : Fin (2 ^ (a + (b + 1)))) (hge : 2 ^ (a + b) ≤ g.val) :
    let p : ℝ := (K : ℝ) / (2 ^ b : ℝ) * Complex.normSq (W.1 0 0)
    ((prepGroverUnitary a b K W).1 *ᵥ Pi.single 0 1) g =
      ((1 - 4 * p : ℝ) : ℂ) * (((1 / √2 : ℝ) ^ (a + b) : ℝ) : ℂ) * W.1 1 0 := by
  intro p
  have : NeZero (2 ^ (b + 1)) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
  let rG : QRegister (b + 1) (a + (b + 1)) := QRegister.block a (b + 1) (by omega)
  have h2a : 0 < 2 ^ a := by positivity
  have hdiv_ge : 2 ^ b ≤ (rG.extractIndex g).val := by
    rw [block_extractIndex_val2 a (b + 1) _ g]
    exact (Nat.le_div_iff_mul_le h2a).mpr (by rw [← pow_add]; simpa [add_comm] using hge)
  have hnot_lt : ¬ (rG.extractIndex g).val < K := not_lt.mpr (le_trans hK hdiv_ge)
  simp only [prepGroverUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    QRegister.embedUnitary_val]
  rw [hadamardPrefix_tensor a b, rG.embedMatrix_mulVec_tensorState]
  simp only [QRegister.tensorState]
  rw [groverStepUnitary, groverStepGen_mulVec_single_zero, grover_good_prob_eq b K hK W]
  simp only [decide_eq_false hnot_lt, Bool.false_eq_true, ↓reduceIte,
    uAGroverUnitary_mulVec_zero_of_ge b W (rG.extractIndex g) hdiv_ge]
  have hpow_ab : (((1 / √2 : ℝ) ^ (a + b) : ℝ) : ℂ) =
      (((1 / √2 : ℝ) ^ a : ℝ) : ℂ) * (((1 / √2 : ℝ) ^ b : ℝ) : ℂ) := by
    rw [pow_add, Complex.ofReal_mul]
  dsimp only [p]; rw [hpow_ab]; ring

theorem unitary2_normSq_col0_sum (W : Unitary 2) :
    Complex.normSq (W.1 0 0) + Complex.normSq (W.1 1 0) = 1 := by
  have hcol : (W.1ᴴ * W.1) 0 0 = 1 := by
    have h1 : W.1ᴴ * W.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact W.2.1
    rw [h1]; rfl
  have hre := congrArg Complex.re hcol
  simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, RCLike.star_def,
    mul_comm (starRingEnd ℂ _) _, Complex.mul_conj, Complex.add_re, Complex.ofReal_re,
    Complex.one_re] using hre

/-! ## Section 2: `17`-Qubit Ket Expansion & `Word25` / `Word19` Column-`0` `L¹` Bounds -/

theorem sum_abs_normSq_sub_of_injective {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (idx : ι → β) (hidx : Function.Injective idx)
    (a₁ a₂ : ι → ℂ) (v₁ v₂ : β → ℂ)
    (hv₁ : ∀ b, v₁ b = ∑ t : ι, if idx t = b then a₁ t else 0)
    (hv₂ : ∀ b, v₂ b = ∑ t : ι, if idx t = b then a₂ t else 0) :
    (∑ b : β, |Complex.normSq (v₁ b) - Complex.normSq (v₂ b)|) =
      ∑ t : ι, |Complex.normSq (a₁ t) - Complex.normSq (a₂ t)| := by
  have hpt (b : β) :
      |Complex.normSq (v₁ b) - Complex.normSq (v₂ b)| =
        ∑ t : ι, if idx t = b then |Complex.normSq (a₁ t) - Complex.normSq (a₂ t)| else 0 := by
    rw [hv₁ b, hv₂ b]
    by_cases hex : ∃ t₀ : ι, idx t₀ = b
    · obtain ⟨t₀, ht₀⟩ := hex
      have hs1 : (∑ t : ι, if idx t = b then a₁ t else 0) = a₁ t₀ := by
        rw [Finset.sum_eq_single t₀]
        · simp [ht₀]
        · intro t _ hne; exact ite_eq_right fun h ↦ hne (hidx (h.trans ht₀.symm))
        · intro h; exact (h (Finset.mem_univ t₀)).elim
      have hs2 : (∑ t : ι, if idx t = b then a₂ t else 0) = a₂ t₀ := by
        rw [Finset.sum_eq_single t₀]
        · simp [ht₀]
        · intro t _ hne; exact ite_eq_right fun h ↦ hne (hidx (h.trans ht₀.symm))
        · intro h; exact (h (Finset.mem_univ t₀)).elim
      have hsr : (∑ t : ι,
          if idx t = b then |Complex.normSq (a₁ t) - Complex.normSq (a₂ t)| else 0) =
          |Complex.normSq (a₁ t₀) - Complex.normSq (a₂ t₀)| := by
        rw [Finset.sum_eq_single t₀]
        · simp [ht₀]
        · intro t _ hne; exact ite_eq_right fun h ↦ hne (hidx (h.trans ht₀.symm))
        · intro h; exact (h (Finset.mem_univ t₀)).elim
      rw [hs1, hs2, hsr]
    · have hall : ∀ t : ι, idx t ≠ b := fun t h ↦ hex ⟨t, h⟩
      simp [hall]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp

/-- `17`-bit assignment placing `x : Fin (2 ^ 8)` on `0..7`, `c : Fin (2 ^ 4)` on `12..15`,
`s : Fin 2` on `16`, and `0` on `8..11`. -/
def inBits17 (x : Fin (2 ^ 8)) (s : Fin 2) (c : Fin (2 ^ 4)) : BitAssignment 17 :=
  fun w ↦
    if hw0 : w.val < 8 then basisBits 8 x ⟨w.val, hw0⟩
    else if hwK : 12 ≤ w.val ∧ w.val < 16 then basisBits 4 c ⟨w.val - 12, by omega⟩
    else if w.val = 16 then (s.val : ZMod 2)
    else 0

theorem inBits17_injective :
    Function.Injective (fun t : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) ↦ inBits17 t.1 t.2.1 t.2.2) := by
  rintro ⟨x1, s1, c1⟩ ⟨x2, s2, c2⟩ h
  have hx : x1 = x2 := by
    have hb : basisBits 8 x1 = basisBits 8 x2 := funext fun i ↦ by
      have hi := congrFun h ⟨i.val, by have := i.isLt; omega⟩
      simpa [inBits17, i.isLt] using hi
    exact (basisBits 8).injective hb
  have hc : c1 = c2 := by
    have hb : basisBits 4 c1 = basisBits 4 c2 := funext fun j ↦ by
      have hj := congrFun h ⟨12 + j.val, by have := j.isLt; omega⟩
      have hlt := j.isLt
      simpa [inBits17, show ¬ (12 + j.val < 8) by omega,
        show 12 ≤ 12 + j.val ∧ 12 + j.val < 16 by omega] using hj
    exact (basisBits 4).injective hb
  have hs : s1 = s2 := by
    have hs0 := congrFun h ⟨16, by decide⟩
    dsimp [inBits17] at hs0
    fin_cases s1 <;> fin_cases s2 <;> simp_all
  subst hx hc hs; rfl

/-- `4`-bit index on `kLoc` with bit `0` set (`1`) and bits `1..3` cleared (`0`). -/
noncomputable def jAux4 : Fin (2 ^ 4) :=
  (basisBits 4).symm (fun j : Fin 4 ↦ if j.val = 0 then 1 else 0)

/-- Embed `x : Fin (2 ^ 8)` into the lower half `0..255` of `Fin (2 ^ 9)`. -/
def lo512 (x : Fin (2 ^ 8)) : Fin (2 ^ 9) :=
  ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩

/-- Embed `x : Fin (2 ^ 8)` into the upper half `256..511` of `Fin (2 ^ 9)`. -/
def hi512 (x : Fin (2 ^ 8)) : Fin (2 ^ 9) :=
  ⟨x.val + 256, Nat.add_lt_add_right x.isLt 256⟩

theorem basisBits_lo512_eight (x : Fin (2 ^ 8)) :
    basisBits 9 (lo512 x) 8 = 0 := by
  rw [basisBits_eq_div_mod]
  have h : (lo512 x).val / 2 ^ (8 : Fin 9).val = 0 := by
    change x.val / 256 = 0; have := x.isLt; omega
  rw [h]; rfl

theorem basisBits_hi512_eight (x : Fin (2 ^ 8)) :
    basisBits 9 (hi512 x) 8 = 1 := by
  rw [basisBits_eq_div_mod]
  have h : (hi512 x).val / 2 ^ (8 : Fin 9).val = 1 := by
    change (x.val + 256) / 256 = 1; have := x.isLt; omega
  rw [h]; rfl

theorem wouter8InitPost_col0
    (rG9 : QRegister 9 17) (rK4 : QRegister 4 17) (wSpin17 : Wire 17)
    (hrG9_lo : ∀ i : Fin 8, rG9 ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩)
    (hrG9_8 : rG9 8 = ⟨12, by decide⟩)
    (hrK4 : ∀ j : Fin 4, rK4 j = ⟨12 + j.val, by omega⟩)
    (hwSpin : wSpin17 = ⟨16, by decide⟩)
    (C : Unitary (2 ^ 4))
    (uPost : Unitary (2 ^ 17)) (fPost : BitAssignment 17 → BitAssignment 17)
    (huPost : ∀ γ : BitAssignment 17,
      uPost.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (fPost γ))
    (u : Unitary (2 ^ 9)) (o : Fin (2 ^ 17)) :
    let U := uPost * (rK4.embedUnitary C * (Circuit.H wSpin17).eval * rG9.embedUnitary u)
    let idx : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → Fin (2 ^ 17) := fun t ↦
      (basisBits 17).symm (fPost (inBits17 t.1 t.2.1 t.2.2))
    let amp : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → ℂ := fun t ↦
      (u.1 (lo512 t.1) 0 * C.1 t.2.2 0 +
        u.1 (hi512 t.1) 0 * C.1 t.2.2 jAux4) * SelectSwapQROM.sqrtHalf
    U.1 o 0 = ∑ t : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4), if idx t = o then amp t else 0 := by
  intro U idx amp
  have hb0 (w : ℕ) (i : Fin w) : basisBits w 0 i = 0 := by
    rw [basisBits_eq_testBit, Fin.val_zero, Nat.zero_testBit]; rfl
  have hk0 : (Pi.single (0 : Fin (2 ^ 17)) 1 : Fin (2 ^ 17) → ℂ) = SelectSwapQROM.ket 0 := by
    have h0 : basisBits 17 0 = 0 := funext fun w ↦ hb0 17 w
    simpa [h0] using SelectSwapQROM.single_eq_ket (0 : Fin (2 ^ 17))
  have hlocG9 : Comparators.localIdx rG9 (0 : BitAssignment 17) = 0 := by
    apply (basisBits 9).injective
    rw [Comparators.localIdx, Equiv.apply_symm_apply]
    funext i; exact (hb0 9 i).symm
  have hrG9_cases (i : Fin 9) : (rG9 i).val < 8 ∨ (rG9 i).val = 12 := by
    by_cases hi : i.val < 8
    · left; have h := congrArg Fin.val (hrG9_lo ⟨i.val, hi⟩); simpa using h.trans_lt hi
    · right; have hid : i = 8 := Fin.ext (by omega); rw [hid, hrG9_8]
  set βG : Fin (2 ^ 9) → BitAssignment 17 := fun y ↦
    Comparators.writeReg (0 : BitAssignment 17) rG9 (basisBits 9 y)
  have hSpin0 (y : Fin (2 ^ 9)) : βG y wSpin17 = 0 := by
    apply Comparators.writeReg_apply_of_not_mem
    rintro ⟨i, hi⟩
    rcases hrG9_cases i with h | h <;> { rw [hi, hwSpin] at h; dsimp at h; omega }
  have hKneSpin (j : Fin 4) : rK4 j ≠ wSpin17 := by
    intro h; have hk := congrArg Fin.val (hrK4 j); rw [h, hwSpin] at hk; dsimp at hk; omega
  have hK0_eq : rK4 0 = rG9 8 := by rw [hrK4 0, hrG9_8]; rfl
  have hK_not_mem (j : Fin 4) (hj : j.val ≠ 0) : rK4 j ∉ Set.range rG9.wires := by
    rintro ⟨i, hi⟩; have hk := congrArg Fin.val (hrK4 j)
    rcases hrG9_cases i with h | h <;> { rw [hi] at h; dsimp at hk; omega }
  have hKLoc0 (x : Fin (2 ^ 8)) (s : Fin 2) :
      Comparators.localIdx rK4 (Function.update (βG (lo512 x)) wSpin17 (s.val : ZMod 2)) =
        0 := by
    apply (basisBits 4).injective
    rw [Comparators.localIdx, Equiv.apply_symm_apply]
    funext j
    change Function.update (βG (lo512 x)) wSpin17 (s.val : ZMod 2) (rK4 j) = basisBits 4 0 j
    rw [hb0 4 j, Function.update_of_ne (hKneSpin j)]
    by_cases hj : j.val = 0
    · have hj0 : j = (0 : Fin 4) := Fin.ext hj
      rw [hj0]; dsimp only [βG]
      rw [hK0_eq, Comparators.writeReg_apply_reg, basisBits_lo512_eight]
    · exact Comparators.writeReg_apply_of_not_mem _ _ _ _ (hK_not_mem j hj)
  have hKLoc1 (x : Fin (2 ^ 8)) (s : Fin 2) :
      Comparators.localIdx rK4
          (Function.update (βG (hi512 x)) wSpin17 (s.val : ZMod 2)) = jAux4 := by
    apply (basisBits 4).injective
    rw [Comparators.localIdx, jAux4, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    funext j; rw [Function.update_of_ne (hKneSpin j)]
    by_cases hj : j.val = 0
    · have hj0 : j = (0 : Fin 4) := Fin.ext hj
      rw [hj0]; dsimp only [βG]
      rw [hK0_eq, Comparators.writeReg_apply_reg, basisBits_hi512_eight]; decide
    · rw [ite_eq_right hj]
      exact Comparators.writeReg_apply_of_not_mem _ _ _ _ (hK_not_mem j hj)
  have hWriteEq (x : Fin (2 ^ 8)) (y : Fin (2 ^ 9))
      (hy8 : ∀ i : Fin 8, basisBits 9 y ⟨i.val, by omega⟩ = basisBits 8 x i)
      (s : Fin 2) (c : Fin (2 ^ 4)) :
      Comparators.writeReg (Function.update (βG y) wSpin17 (s.val : ZMod 2)) rK4
          (basisBits 4 c) = inBits17 x s c := by
    funext w
    by_cases hwK : 12 ≤ w.val ∧ w.val < 16
    · have hmem : w = rK4 ⟨w.val - 12, by omega⟩ :=
        Fin.ext (by have := congrArg Fin.val (hrK4 ⟨w.val - 12, by omega⟩); dsimp at this; omega)
      conv_lhs => rw [hmem]
      rw [Comparators.writeReg_apply_reg]; dsimp only [inBits17]
      simp [show ¬ (w.val < 8) by omega, hwK]
    · have hnotK : w ∉ Set.range rK4.wires := by
        rintro ⟨j, rfl⟩; have hk := congrArg Fin.val (hrK4 j); dsimp at hk
        exact hwK ⟨by omega, by omega⟩
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hnotK]
      by_cases hwS : w = wSpin17
      · subst hwS; rw [Function.update_self, hwSpin]; dsimp only [inBits17]; simp
      · rw [Function.update_of_ne hwS]
        by_cases hwX : w.val < 8
        · have hmemG : w = rG9 ⟨w.val, by omega⟩ :=
            Fin.ext (by have := congrArg Fin.val (hrG9_lo ⟨w.val, hwX⟩); simpa using this.symm)
          conv_lhs => rw [hmemG]
          dsimp only [βG]
          rw [Comparators.writeReg_apply_reg, hy8 ⟨w.val, hwX⟩]
          dsimp only [inBits17]; simp [hwX]
        · have hnotG : w ∉ Set.range rG9.wires := by
            rintro ⟨i, hi⟩
            rcases hrG9_cases i with h | h <;> { rw [hi] at h; omega }
          dsimp only [βG]
          rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hnotG]
          have hw16 : w.val ≠ 16 := fun h ↦ hwS (Fin.ext (by rw [hwSpin]; exact h))
          dsimp only [inBits17]; simp [hwX, hwK, hw16]
  have hy8_0 (x : Fin (2 ^ 8)) (i : Fin 8) :
      basisBits 9 (lo512 x) ⟨i.val, by omega⟩ = basisBits 8 x i := by
    rw [basisBits_eq_testBit, basisBits_eq_testBit]; rfl
  have hy8_1 (x : Fin (2 ^ 8)) (i : Fin 8) :
      basisBits 9 (hi512 x) ⟨i.val, by omega⟩ = basisBits 8 x i := by
    rw [basisBits_eq_testBit, basisBits_eq_testBit]; dsimp only [hi512]
    have hmod : x.val = (x.val + 256) % 2 ^ 8 := by omega
    conv_rhs => rw [hmod, Nat.testBit_mod_two_pow]
    simp [i.isLt]; rfl
  have hg_init : (rG9.embedUnitary u).1 *ᵥ Pi.single 0 1 =
      ∑ x : Fin (2 ^ 8), (u.1 (lo512 x) 0 • SelectSwapQROM.ket (βG (lo512 x)) +
        u.1 (hi512 x) 0 • SelectSwapQROM.ket (βG (hi512 x))) := by
    have hraw : (rG9.embedUnitary u).1 *ᵥ Pi.single 0 1 =
        ∑ y : Fin (2 ^ 9), u.1 y 0 • SelectSwapQROM.ket (βG y) := by
      rw [hk0, QRegister.embedUnitary_val]
      simpa only [hlocG9, βG] using Comparators.embedMatrix_mulVec_ket rG9 u.1 0
    rw [hraw]
    let e512 : Fin (256 + 256) ≃ Fin (2 ^ 9) := finCongr (by decide)
    rw [← e512.sum_comp, Fin.sum_univ_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have he0 : e512 (Fin.castAdd 256 x) = lo512 x := rfl
    have he1 : e512 (Fin.natAdd 256 x) = hi512 x := Fin.ext (Nat.add_comm 256 x.val)
    rw [he0, he1]
  have hstep (x : Fin (2 ^ 8)) :
      (uPost.1 * ((rK4.embedUnitary C).1 * ((Circuit.H wSpin17).eval.1))) *ᵥ
        (u.1 (lo512 x) 0 • SelectSwapQROM.ket (βG (lo512 x)) +
          u.1 (hi512 x) 0 • SelectSwapQROM.ket (βG (hi512 x))) =
      ∑ s : Fin 2, ∑ c : Fin (2 ^ 4),
        amp (x, s, c) • SelectSwapQROM.ket (fPost (inBits17 x s c)) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      SelectSwapQROM.ket_H, hSpin0, SelectSwapQROM.bitSign, ↓reduceIte, one_smul,
      smul_add, smul_smul, QRegister.embedUnitary_val, Comparators.embedMatrix_mulVec_ket]
    have h00 := hKLoc0 x 0; have h01 := hKLoc0 x 1
    have h10 := hKLoc1 x 0; have h11 := hKLoc1 x 1
    have hw00 := fun c ↦ hWriteEq x (lo512 x) (hy8_0 x) 0 c
    have hw01 := fun c ↦ hWriteEq x (lo512 x) (hy8_0 x) 1 c
    have hw10 := fun c ↦ hWriteEq x (hi512 x) (hy8_1 x) 0 c
    have hw11 := fun c ↦ hWriteEq x (hi512 x) (hy8_1 x) 1 c
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one] at h00 h01 h10 h11
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one] at hw00 hw01 hw10 hw11
    rw [h00, h01, h10, h11]
    simp_rw [hw00, hw01, hw10, hw11, Matrix.mulVec_sum, Matrix.mulVec_smul, huPost,
      Finset.smul_sum, smul_smul, Fin.sum_univ_two]
    rw [add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ ↦ ?_)
      (Finset.sum_congr rfl fun c _ ↦ ?_) <;>
      { rw [← add_smul]; refine congrArg (· • _) ?_; dsimp only [amp]; ring }
  have hmul : U.1 o 0 = (U.1 *ᵥ Pi.single 0 1) o := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hmul]; dsimp only [U]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
  have hassoc : (uPost.1 * ((rK4.embedUnitary C).1 * (Circuit.H wSpin17).eval.1 *
      (rG9.embedUnitary u).1)) *ᵥ Pi.single 0 1 =
    (uPost.1 * ((rK4.embedUnitary C).1 * (Circuit.H wSpin17).eval.1)) *ᵥ
      ((rG9.embedUnitary u).1 *ᵥ Pi.single 0 1) := by
    simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  rw [hassoc, hg_init, Matrix.mulVec_sum]
  simp_rw [hstep]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SelectSwapQROM.ket, basisState,
    Pi.single_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun s _ ↦
    Finset.sum_congr rfl fun c _ ↦ ?_
  dsimp only [idx]
  by_cases h : (basisBits 17).symm (fPost (inBits17 x s c)) = o
  · simp [h]
  · simp [h, Ne.symm h]

end GroverL1
/-! ## Section 3: Polymorphic `Word19` Wrappers & Zero-Walk-Error `fullQuantP450HBlocked` Bridge -/

section SOSAndOuterClosures

open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.CoherentAlias Solution.AliasPrep
open Solution.OptFactoredMag30AndCoin9
open Solution.Tuned162StepSympAnfQrom21
open Solution.TopIntegrationBridge Solution.ReordOuter13Bridge
open Solution.Cat11CompactPhase2Bridge
open Solution.CompactTuned162StepZeroCmp20
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk
open Solution.Phase2MidSandwich
open Solution.ZeroRcHotPrepMid21Fast
open Solution.CompactZeroCmp20OuterParam
open Solution.CompactStepZeroCmp20OuterParam
open Solution.StepOuter8Pi145Outer
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowOuter8Pi145L1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

theorem sum_normSq_unitary_col0 {d : ℕ} [NeZero d] (U : Unitary d) :
    (∑ o : Fin d, Complex.normSq (U.1 o 0)) = 1 := by
  have h : (U.1ᴴ * U.1) 0 0 = 1 := by
    have h1 : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
    rw [h1, Matrix.one_apply_eq]
  have hre := congrArg Complex.re h
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    mul_comm (starRingEnd ℂ _) _, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re,
    Complex.one_re] using hre

/-- Exact half-step system operator `∑ m, |prepMid(rc7)_{m, 0}|² B_sel(o', m)` for arbitrary
`(prepMid, B_sel)` without `< 184` support truncation. -/
noncomputable def fullHalfSystemOp {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (o' : Fin (2 ^ mOutUB wOuter)) : Operator (2 ^ (2 * 58)) :=
  ∑ m : Fin (2 ^ mMidUB wInner2),
    (Complex.normSq ((prepMid ((rXo7Loc wOuter).extractIndex o')).1 m 0) : ℂ) • (B_sel o' m).1

/-- Exact spin-blocked SOS Hamiltonian realized by `ubDirectXo7PureUnitary`
at `(eLB, lam) = (dfthcLowerBound, 97.3864)` (`δOut = 0`, `δIdx = 0`). -/
noncomputable def fullQuantP450HBlocked {wOuter wInner2 : ℕ}
    (prepOut : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58))) :
    Operator (2 ^ (2 * 58)) :=
  (dfthcLowerBound : ℂ) • 1 +
    ((2 * 97.3864 : ℝ) : ℂ) • ∑ o' : Fin (2 ^ mOutUB wOuter),
      (Complex.normSq (prepOut.1 o' 0) : ℂ) •
        ((fullHalfSystemOp prepMid B_sel o')ᴴ * fullHalfSystemOp prepMid B_sel o')

theorem prepMidDirectXo7MuxUnitary_mulVec_embedKet {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' m =
      ∑ m' : Fin (2 ^ mMidUB wInner2),
        ((prepMid ((rXo7Loc wOuter).extractIndex o')).1 m' m) • embedKet ψ o' m' := by
  have hxo (g : Fin (2 ^ nUB wOuter wInner2))
      (hne : (rXo7UB wOuter wInner2).extractIndex g ≠ (rXo7Loc wOuter).extractIndex o') :
      embedKet ψ o' m g = 0 := by
    dsimp [embedKet]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g = o' ∧
      (rMidUB wOuter wInner2).extractIndex g = m
    · exact absurd (by rw [show rXo7UB wOuter wInner2 =
        (rOutUB wOuter wInner2).compose (rXo7Loc wOuter) from rfl,
        QRegister.extractIndex_compose, hc.1]) hne
    · simp [hc]
  unfold prepMidDirectXo7MuxUnitary
  rw [muxUnitary_mulVec_of_proj _ _ _ _ ((rXo7Loc wOuter).extractIndex o') _ hxo,
    embedMatrix_rMidUB_mulVec_embedKet]

theorem sum_inv_ite_embedKet {wOuter wInner2 : ℕ} (U : Unitary (2 ^ mMidUB wInner2))
    (m : Fin (2 ^ mMidUB wInner2)) (A : Operator (2 ^ (2 * 58)))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o : Fin (2 ^ mOutUB wOuter)) :
    (U.1 m 0) • (∑ x : Fin (2 ^ mMidUB wInner2), ((U⁻¹).1 x m) •
        if x = 0 then embedKet (w_gi := wInner2) (A *ᵥ ψ) o 0 else 0) =
      embedKet (w_gi := wInner2) (((Complex.normSq (U.1 m 0) : ℂ) • A) *ᵥ ψ) o 0 := by
  rw [Finset.sum_eq_single 0]
  · have hadj : (U⁻¹).1 0 m = star (U.1 m 0) := rfl
    rw [ite_eq_left rfl, hadj, smul_smul, Complex.star_def, Complex.mul_conj,
      ← embedKet_smul, Matrix.smul_mulVec]
  · intro x _ hx; rw [ite_eq_right hx, smul_zero]
  · intro h0; exact (h0 (Finset.mem_univ 0)).elim

theorem projMid_directXo7_selectPure_eq_fullHalfSystemOp {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (hSelAll : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      selectPure.1 *ᵥ embedKet ψ o' m = embedKet ((B_sel o' m).1 *ᵥ ψ) o' m)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) :
    (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
        (((prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid)⁻¹ *
          selectPure * prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' 0) =
      embedKet (fullHalfSystemOp prepMid B_sel o' *ᵥ ψ) o' 0 := by
  let rc7 := (rXo7Loc wOuter).extractIndex o'
  have hinv : (prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid)⁻¹ =
      prepMidDirectXo7MuxUnitary wOuter wInner2 (fun r ↦ (prepMid r)⁻¹) := muxUnitary_inv _ _ _ _
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hinv,
    prepMidDirectXo7MuxUnitary_mulVec_embedKet, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hterm (m : Fin (2 ^ mMidUB wInner2)) :
      ((prepMid rc7).1 m 0) •
        ((rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
          ((prepMidDirectXo7MuxUnitary wOuter wInner2 fun r ↦ (prepMid r)⁻¹).1 *ᵥ
            (selectPure.1 *ᵥ embedKet ψ o' m))) =
      embedKet (((Complex.normSq ((prepMid rc7).1 m 0) : ℂ) • (B_sel o' m).1) *ᵥ ψ) o' 0 := by
    rw [hSelAll ψ o' m]
    simp only [prepMidDirectXo7MuxUnitary_mulVec_embedKet, Matrix.mulVec_sum,
      Matrix.mulVec_smul, projMid_mulVec_embedKet]
    exact sum_inv_ite_embedKet (prepMid rc7) m _ ψ o'
  refine (Finset.sum_congr rfl fun m _ ↦ hterm m).trans ?_
  rw [← embedKet_sum, ← Matrix.sum_mulVec]; rfl

theorem dotProduct_star_embedKet_ortho2 {wOuter wInner2 : ℕ}
    (α β : Fin (2 ^ (2 * 58)) → ℂ) (o₁ o₂ : Fin (2 ^ mOutUB wOuter)) :
    dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) α o₁ 0))
      (embedKet (w_go := wOuter) (w_gi := wInner2) β o₂ 0) =
    if o₁ = o₂ then dotProduct (star α) β else 0 := by
  dsimp only [dotProduct, Pi.star_apply]
  let term : Fin (2 ^ (2 * 58)) × Fin (2 ^ mOutUB wOuter) × Fin (2 ^ mMidUB wInner2) → ℂ :=
    fun ⟨s, o, m⟩ ↦ if (o = o₁ ∧ m = 0) ∧ (o = o₂ ∧ m = 0) then star (α s) * β s else 0
  have hpt (g : Fin (2 ^ nUB wOuter wInner2)) :
      star (embedKet (w_go := wOuter) (w_gi := wInner2) α o₁ 0 g) *
        embedKet (w_go := wOuter) (w_gi := wInner2) β o₂ 0 g =
      term (ubSplitEquiv wOuter wInner2 g) := by
    rw [ubSplitEquiv_apply]; dsimp only [embedKet, term]
    by_cases h1 : (rOutUB wOuter wInner2).extractIndex g = o₁ ∧
      (rMidUB wOuter wInner2).extractIndex g = 0
    · by_cases h2 : (rOutUB wOuter wInner2).extractIndex g = o₂ ∧
        (rMidUB wOuter wInner2).extractIndex g = 0
      · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
      · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right (fun h ↦ h2 h.2), mul_zero]
    · rw [ite_eq_right h1, star_zero, zero_mul, ite_eq_right (fun h ↦ h1 h.1)]
  simp_rw [hpt]
  rw [Equiv.sum_comp (ubSplitEquiv wOuter wInner2), Fintype.sum_prod_type]
  by_cases hoo : o₁ = o₂
  · subst hoo; simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single o₁]
    · rw [Finset.sum_eq_single 0]
      · simp [term]
      · intro m _ hm; simp [term, hm]
      · simp
    · intro o _ ho; simp [term, ho]
    · simp
  · simp only [hoo, ↓reduceIte]
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun o _ ↦ Finset.sum_eq_zero fun m _ ↦ ?_
    dsimp [term]; split_ifs with hc
    · exact absurd (hc.1.1.symm.trans hc.2.1) hoo
    · rfl

theorem dotProduct_star_mulVec {d : ℕ} (A : Operator d) (x y : Fin d → ℂ) :
    dotProduct (star (A *ᵥ x)) y = dotProduct (star x) (Aᴴ *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

theorem eq_of_projAll_and_dotProduct_embedKet2 {wOuter wInner2 : ℕ}
    {u w : Fin (2 ^ nUB wOuter wInner2) → ℂ}
    (hu : (rAllUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ u = u)
    (hw : (rAllUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ w = w)
    (hdot : ∀ φ : Fin (2 ^ (2 * 58)) → ℂ,
      dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)) u =
        dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)) w) :
    u = w := by
  let d := u - w
  have hd_proj : (rAllUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ d = d := by
    dsimp [d]; rw [Matrix.mulVec_sub, hu, hw]
  let dSys (s : Fin (2 ^ (2 * 58))) : ℂ := d ((ubSplitEquiv wOuter wInner2).symm (s, 0, 0))
  have hd_eq : d = embedKet (w_go := wOuter) (w_gi := wInner2) dSys 0 0 := by
    funext g
    have hall0 : (rAllUB wOuter wInner2).extractIndex g = 0 ↔
        (rOutUB wOuter wInner2).extractIndex g = 0 ∧ (rMidUB wOuter wInner2).extractIndex g =
            0 := by
      rw [rAllUB_eq_concat, Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
        Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
        Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
      exact ⟨fun h ↦ ⟨fun i ↦ by simpa using h (Fin.castAdd _ i),
          fun j ↦ by simpa using h (Fin.natAdd _ j)⟩,
        fun ⟨ho, hm⟩ idx ↦ by
          obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
          · simpa using ho i
          · simpa using hm j⟩
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g = 0 ∧
      (rMidUB wOuter wInner2).extractIndex g = 0
    · have hsp : (ubSplitEquiv wOuter wInner2).symm ((rSysUB wOuter wInner2).extractIndex g, 0,
        0) = g := by
        rw [← hc.1, ← hc.2, ← ubSplitEquiv_apply, Equiv.symm_apply_apply]
      dsimp [embedKet, dSys]; rw [ite_eq_left hc, hsp]
    · have hnall : (rAllUB wOuter wInner2).extractIndex g ≠ 0 := fun h ↦ hc (hall0.mp h)
      have hdg := congrFun hd_proj.symm g
      rw [(rAllUB wOuter wInner2).basisOutcomeProjector_mulVec, ite_eq_right hnall] at hdg
      dsimp [embedKet]; rw [hdg, ite_eq_right hc]
  have hd0 : dotProduct (star dSys) dSys = 0 := by
    have h1 : dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) dSys 0 0)) d = 0 := by
      dsimp [d]; rw [dotProduct_sub, sub_eq_zero]; exact hdot dSys
    rw [hd_eq, dotProduct_star_embedKet_ortho2, ite_eq_left rfl] at h1; exact h1
  have hsum0 : (∑ s : Fin (2 ^ (2 * 58)), Complex.normSq (dSys s)) = 0 := by
    have hc : ((∑ s, Complex.normSq (dSys s) : ℝ) : ℂ) = dotProduct (star dSys) dSys := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun s _ ↦ by rw [mul_comm, Complex.mul_conj]
    exact Complex.ofReal_eq_zero.mp (hc.trans hd0)
  have hdSys0 : dSys = 0 := funext fun s ↦ Complex.normSq_eq_zero.mp (le_antisymm
    ((Finset.single_le_sum (fun i _ ↦ Complex.normSq_nonneg (dSys i))
      (Finset.mem_univ s)).trans_eq hsum0) (Complex.normSq_nonneg _))
  have hd_zero : d = 0 := by rw [hd_eq, hdSys0]; ext g; simp [embedKet]
  exact sub_eq_zero.mp hd_zero

theorem fullQuant_pulledMid_quadForm {wOuter wInner2 : ℕ}
    (prepOut : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (hSelAll : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      selectPure.1 *ᵥ embedKet ψ o' m = embedKet ((B_sel o' m).1 *ᵥ ψ) o' m)
    (φ χ : Fin (2 ^ (2 * 58)) → ℂ) :
    let U_B := ubDirectXo7PureUnitary prepOut prepMid selectPure
    let P_mid := (rMidUB wOuter wInner2).basisOutcomeProjector 0
    dotProduct (star (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)))
        (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0)) =
      dotProduct (star φ)
        (((2 * 97.3864 : ℂ)⁻¹ •
          (fullQuantP450HBlocked prepOut prepMid B_sel - (dfthcLowerBound : ℂ) • 1)) *ᵥ χ) := by
  intro U_B P_mid
  have hfwd (ξ : Fin (2 ^ (2 * 58)) → ℂ) :
      P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) ξ 0 0) =
        ∑ o' : Fin (2 ^ mOutUB wOuter), (prepOut.1 o' 0) •
          embedKet (w_gi := wInner2) (fullHalfSystemOp prepMid B_sel o' *ᵥ ξ) o' 0 := by
    dsimp only [P_mid, U_B, ubDirectXo7PureUnitary]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val,
      embedMatrix_rOutUB_mulVec_embedKet, Matrix.mulVec_sum, Matrix.mulVec_smul]
    refine Finset.sum_congr rfl fun o' _ ↦ ?_
    have h := projMid_directXo7_selectPure_eq_fullHalfSystemOp prepMid selectPure B_sel hSelAll ξ o'
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at h
    rw [h]
  rw [hfwd φ, hfwd χ, star_sum, sum_dotProduct]
  have hrow (o₁ : Fin (2 ^ mOutUB wOuter)) :
      dotProduct (star ((prepOut.1 o₁ 0) • embedKet (w_gi := wInner2)
          (fullHalfSystemOp prepMid B_sel o₁ *ᵥ φ) o₁ 0))
        (∑ o₂ : Fin (2 ^ mOutUB wOuter), (prepOut.1 o₂ 0) • embedKet (w_gi := wInner2)
          (fullHalfSystemOp prepMid B_sel o₂ *ᵥ χ) o₂ 0) =
      dotProduct (star φ)
        (((Complex.normSq (prepOut.1 o₁ 0) : ℂ) •
          ((fullHalfSystemOp prepMid B_sel o₁)ᴴ * fullHalfSystemOp prepMid B_sel o₁)) *ᵥ χ) := by
    rw [dotProduct_sum, Finset.sum_eq_single o₁]
    · rw [star_smul, smul_dotProduct, dotProduct_smul, dotProduct_star_embedKet_ortho2,
        ite_eq_left rfl, dotProduct_star_mulVec, Matrix.mulVec_mulVec,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, Complex.star_def,
        mul_comm (starRingEnd ℂ (prepOut.1 o₁ 0)) (prepOut.1 o₁ 0), Complex.mul_conj]
    · intro o₂ _ ho₂
      rw [star_smul, smul_dotProduct, dotProduct_smul, dotProduct_star_embedKet_ortho2,
        ite_eq_right ho₂.symm, smul_zero, smul_zero]
    · simp
  simp_rw [hrow, ← dotProduct_sum, ← Matrix.sum_mulVec]
  unfold fullQuantP450HBlocked
  rw [add_sub_cancel_left, smul_smul]
  have hinv : (2 * 97.3864 : ℂ)⁻¹ * ((2 * 97.3864 : ℝ) : ℂ) = 1 := by
    push_cast; exact inv_mul_cancel₀ (by norm_num)
  rw [hinv, one_smul]

/-- Zero-walk-error (`δOut = 0, δIdx = 0`) `PulledSOSBlockEncoding` for ANY `prepOut` and
`prepMid` when `selectPure` acts branchwise via `B_sel`. -/
theorem pulledSOSBlockEncoding_ubDirectXo7Pure_fullQuant {wOuter wInner2 : ℕ}
    (prepOut : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (hSelAll : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      selectPure.1 *ᵥ embedKet ψ o' m = embedKet ((B_sel o' m).1 *ᵥ ψ) o' m) :
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2)
      (fullQuantP450HBlocked prepOut prepMid B_sel) dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOut prepMid selectPure) := by
  let U_B := ubDirectXo7PureUnitary prepOut prepMid selectPure
  let P_mid := (rMidUB wOuter wInner2).basisOutcomeProjector 0
  let P_in := (rAllUB wOuter wInner2).basisOutcomeProjector 0
  have hdot_mid := fullQuant_pulledMid_quadForm prepOut prepMid selectPure B_sel hSelAll
  refine ⟨by norm_num, fun ψ E heig hnorm ↦ ?_⟩
  let e₁ := (rSysUB wOuter wInner2).tensorState ψ (Pi.single 0 1)
  have he₁ : e₁ = embedKet (w_go := wOuter) (w_gi := wInner2) ψ 0 0 :=
    (embedKet_zero_zero_eq_tensorState ψ).symm
  have hPin : P_in *ᵥ e₁ = e₁ := by rw [he₁, projAll_mulVec_embedKet, ite_eq_left ⟨rfl, rfl⟩]
  have hdot_norm {d : ℕ} (v : Fin d → ℂ) :
      ((∑ i : Fin d, Complex.normSq (v i) : ℝ) : ℂ) = dotProduct (star v) v := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm, Complex.mul_conj]
  have he₁_norm : (∑ g : Fin (2 ^ nUB wOuter wInner2), Complex.normSq (e₁ g)) = 1 :=
    Complex.ofReal_injective
      ((hdot_norm e₁).trans (by rw [he₁, dotProduct_star_embedKet_ortho2, ite_eq_left rfl,
        ← hdot_norm ψ, hnorm]))
  have hvec : (((2 * 97.3864 : ℂ)⁻¹ •
        (fullQuantP450HBlocked prepOut prepMid B_sel - (dfthcLowerBound : ℂ) • 1)) *ᵥ ψ) =
      (((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • ψ := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, heig, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← sub_smul, smul_smul]
    refine congrArg (· • ψ) ?_; push_cast; ring
  let v_mid := P_mid *ᵥ (U_B.1 *ᵥ e₁)
  have hsq_eq : (∑ g : Fin (2 ^ nUB wOuter wInner2), Complex.normSq (v_mid g)) =
      (E - dfthcLowerBound) / (2 * 97.3864) := by
    apply Complex.ofReal_injective
    rw [hdot_norm v_mid]; dsimp only [v_mid]; rw [he₁, hdot_mid ψ ψ, hvec, dotProduct_smul,
      ← hdot_norm ψ, hnorm, Complex.ofReal_one, smul_eq_mul, mul_one]
  have hsq_nn : 0 ≤ (E - dfthcLowerBound) / (2 * 97.3864) :=
    hsq_eq ▸ Finset.sum_nonneg fun g _ ↦ Complex.normSq_nonneg _
  have hsq_le1 : (E - dfthcLowerBound) / (2 * 97.3864) ≤ 1 := by
    rw [← hsq_eq, ← he₁_norm]
    have hproj_le : (∑ g, Complex.normSq (v_mid g)) ≤ ∑ g, Complex.normSq ((U_B.1 *ᵥ e₁) g) := by
      refine Finset.sum_le_sum fun g _ ↦ ?_
      dsimp only [v_mid, P_mid]
      rw [(rMidUB wOuter wInner2).basisOutcomeProjector_mulVec]
      split_ifs <;> [exact le_rfl; simp [Complex.normSq_nonneg]]
    have hiso : (∑ g, Complex.normSq ((U_B.1 *ᵥ e₁) g)) = ∑ g, Complex.normSq (e₁ g) := by
      apply Complex.ofReal_injective
      have hU : U_B.1ᴴ * U_B.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U_B.2.1
      rw [hdot_norm _, hdot_norm e₁, dotProduct_star_mulVec, Matrix.mulVec_mulVec, hU,
        Matrix.one_mulVec]
    exact hproj_le.trans hiso.le
  have hlo : dfthcLowerBound ≤ E := by
    have : 0 ≤ E - dfthcLowerBound :=
      ((div_nonneg_iff.mp hsq_nn).resolve_right (fun ⟨_, h⟩ ↦ by norm_num at h)).1
    linarith
  have hhi : E ≤ dfthcLowerBound + 2 * 97.3864 := by
    have : E - dfthcLowerBound ≤ 2 * 97.3864 := (div_le_one (by norm_num)).mp hsq_le1
    linarith
  refine ⟨hPin, he₁_norm, hlo, hhi, ?_⟩
  change P_in *ᵥ ((U_B.1ᴴ * P_mid * U_B.1) *ᵥ e₁) =
    (((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • e₁
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine eq_of_projAll_and_dotProduct_embedKet2 ?_ ?_ fun φ ↦ ?_
  · rw [Matrix.mulVec_mulVec, (rAllUB wOuter wInner2).basisOutcomeProjector_mul_self]
  · rw [Matrix.mulVec_smul, hPin]
  · have hPinφ : P_in *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0 =
        embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0 := by
      dsimp only [P_in]; rw [projAll_mulVec_embedKet, ite_eq_left ⟨rfl, rfl⟩]
    calc dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0))
            (P_in *ᵥ (U_B.1ᴴ *ᵥ (P_mid *ᵥ (U_B.1 *ᵥ e₁))))
        = dotProduct (star (P_in *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0))
            (U_B.1ᴴ *ᵥ (P_mid *ᵥ (U_B.1 *ᵥ e₁))) := by
          dsimp only [P_in]
          rw [dotProduct_star_mulVec, (rAllUB wOuter wInner2).basisOutcomeProjector_conjTranspose]
      _ = dotProduct (star (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0))
            ((P_mid * P_mid) *ᵥ (U_B.1 *ᵥ e₁)) := by
          rw [hPinφ, ← dotProduct_star_mulVec U_B.1]
          dsimp only [P_mid]
          rw [(rMidUB wOuter wInner2).basisOutcomeProjector_mul_self]
      _ = dotProduct (star (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)))
            (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) ψ 0 0)) := by
          rw [← Matrix.mulVec_mulVec, ← he₁]; dsimp only [P_mid]
          conv_rhs => rw [dotProduct_star_mulVec ((rMidUB wOuter wInner2).basisOutcomeProjector 0),
            (rMidUB wOuter wInner2).basisOutcomeProjector_conjTranspose]
      _ = dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0))
            ((((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • e₁) := by
          rw [hdot_mid φ ψ, hvec, he₁, ← embedKet_smul, dotProduct_star_embedKet_ortho2,
            ite_eq_left rfl]

theorem norm_unitary_le_one {d : ℕ} [NeZero d] (U : Unitary d) : ‖U.1‖ ≤ 1 :=
  QubitisedWalk.opNorm_le_of_vecNormSq_mulVec U.1 zero_le_one fun v ↦ by
    rw [_root_.one_pow, one_mul]
    have hU : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
    have h : ((QubitisedWalk.vecNormSq (U.1 *ᵥ v) : ℝ) : ℂ) = ((QubitisedWalk.vecNormSq v : ℝ) :
        ℂ) := by
      have hd (w : Fin d → ℂ) : ((QubitisedWalk.vecNormSq w : ℝ) : ℂ) = dotProduct (star w) w := by
        unfold QubitisedWalk.vecNormSq
        simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm, Complex.mul_conj]
      rw [hd, hd, dotProduct_star_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    exact (Complex.ofReal_injective h).le

theorem norm_fullHalfSystemOp_le_one {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (o' : Fin (2 ^ mOutUB wOuter)) :
    ‖fullHalfSystemOp prepMid B_sel o'‖ ≤ 1 := by
  unfold fullHalfSystemOp
  refine (norm_sum_le _ _).trans ?_
  have hle : (∑ m : Fin (2 ^ mMidUB wInner2),
        ‖(Complex.normSq ((prepMid ((rXo7Loc wOuter).extractIndex o')).1 m 0) : ℂ) •
          (B_sel o' m).1‖) ≤
      ∑ m : Fin (2 ^ mMidUB wInner2),
        Complex.normSq ((prepMid ((rXo7Loc wOuter).extractIndex o')).1 m 0) := by
    refine Finset.sum_le_sum fun m _ ↦ ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
    exact mul_le_of_le_one_right (Complex.normSq_nonneg _) (norm_unitary_le_one (B_sel o' m))
  exact hle.trans_eq (sum_normSq_unitary_col0 _)

theorem opNorm_mul_le2 {d : ℕ} [NeZero d] (A B : Operator d) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  QubitisedWalk.opNorm_le_of_vecNormSq_mulVec (A * B) (mul_nonneg (norm_nonneg A) (norm_nonneg B))
    fun v ↦ by
      rw [← Matrix.mulVec_mulVec, mul_pow, mul_assoc]
      exact (QubitisedWalk.vecNormSq_mulVec_le_opNorm_sq A (B *ᵥ v)).trans
        (mul_le_mul_of_nonneg_left (QubitisedWalk.vecNormSq_mulVec_le_opNorm_sq B v)
          (sq_nonneg ‖A‖))

theorem norm_fullQuantP450HBlocked_sub_le_l1 {wOuter wInner2 : ℕ}
    (u₁ u₂ : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58))) :
    ‖fullQuantP450HBlocked u₁ prepMid B_sel - fullQuantP450HBlocked u₂ prepMid B_sel‖ ≤
      2 * 97.3864 *
        ∑ o' : Fin (2 ^ mOutUB wOuter),
            |Complex.normSq (u₁.1 o' 0) - Complex.normSq (u₂.1 o' 0)| := by
  have hdiff : fullQuantP450HBlocked u₁ prepMid B_sel - fullQuantP450HBlocked u₂ prepMid B_sel =
      ((2 * 97.3864 : ℝ) : ℂ) • ∑ o' : Fin (2 ^ mOutUB wOuter),
        ((Complex.normSq (u₁.1 o' 0) - Complex.normSq (u₂.1 o' 0) : ℝ) : ℂ) •
          ((fullHalfSystemOp prepMid B_sel o')ᴴ * fullHalfSystemOp prepMid B_sel o') := by
    unfold fullQuantP450HBlocked
    rw [add_sub_add_left_eq_sub, ← smul_sub, ← Finset.sum_sub_distrib]
    refine congrArg (((2 * 97.3864 : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun o' _ ↦ ?_)
    rw [Complex.ofReal_sub, sub_smul]
  rw [hdiff, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by norm_num)
  refine Finset.sum_le_sum fun o' _ ↦ ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  have hM := norm_fullHalfSystemOp_le_one prepMid B_sel o'
  have hMh : ‖(fullHalfSystemOp prepMid B_sel o')ᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  exact (opNorm_mul_le2 _ _).trans
    ((mul_le_mul hMh hM (norm_nonneg _) zero_le_one).trans (by norm_num))

theorem dotProduct_star_single_one {d : ℕ} (i : Fin d) (w : Fin d → ℂ) :
    dotProduct (star (Pi.single i (1 : ℂ))) w = w i := by
  simp only [dotProduct, Pi.star_apply]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro k hk; simp [Pi.single_eq_of_ne hk]

theorem hermitian_eq_of_eigenvector_quadForm {d : ℕ}
    {H₂ H₁ : Operator d} (hH₁ : H₁.IsHermitian)
    (hquad : ∀ (φ : Fin d → ℂ) (E : ℝ),
      H₁ *ᵥ φ = (E : ℂ) • φ → (∑ i : Fin d, Complex.normSq (φ i)) = 1 →
      ∀ χ : Fin d → ℂ,
        dotProduct (star χ) (((2 * 97.3864 : ℂ)⁻¹ • (H₂ - (dfthcLowerBound : ℂ) • 1)) *ᵥ φ) =
          dotProduct (star χ) ((((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • φ)) :
    H₂ = H₁ := by
  let V : Unitary d := hH₁.eigenvectorUnitary
  have hColZero (j : Fin d) : (H₂ - H₁) *ᵥ (V.1 *ᵥ Pi.single j 1) = 0 := by
    let φ : Fin d → ℂ := ⇑(hH₁.eigenvectorBasis j)
    let E : ℝ := hH₁.eigenvalues j
    have hVφ : V.1 *ᵥ Pi.single j 1 = φ := hH₁.eigenvectorUnitary_mulVec j
    rw [hVφ]
    have hNorm : (∑ i : Fin d, Complex.normSq (φ i)) = 1 := by
      have hcol : ∀ i, φ i = V.1 i j := fun i ↦ (hH₁.eigenvectorUnitary_apply i j).symm
      have h1 : (V.1ᴴ * V.1) j j = 1 := by
        have hv : V.1ᴴ * V.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact V.2.1
        rw [hv, Matrix.one_apply_eq]
      have hre := congrArg Complex.re h1
      simp_rw [hcol]
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
        mul_comm (starRingEnd ℂ _) _, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re,
        Complex.one_re] using hre
    have hEig : H₁ *ᵥ φ = (E : ℂ) • φ := by
      have h := hH₁.mulVec_eigenvectorBasis j
      dsimp only [φ, E]; rw [h]; ext i; simp [Complex.real_smul]
    have hsc1 : (((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • φ =
        (((2 * 97.3864 : ℂ)⁻¹ • (H₁ - (dfthcLowerBound : ℂ) • 1)) *ᵥ φ) := by
      rw [Matrix.smul_mulVec, Matrix.sub_mulVec, hEig, Matrix.smul_mulVec, Matrix.one_mulVec,
        ← sub_smul, smul_smul]
      refine congrArg (· • φ) ?_; push_cast; ring
    funext i
    have h1 := hquad φ E hEig hNorm (Pi.single i 1)
    rw [hsc1, dotProduct_star_single_one, dotProduct_star_single_one,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul] at h1
    have hinv_ne : (2 * 97.3864 : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by norm_num)
    have h2 := mul_left_cancel₀ hinv_ne h1
    simp only [Matrix.sub_mulVec, Pi.sub_apply] at h2 ⊢
    exact sub_eq_zero.mpr (sub_left_inj.mp h2)
  have hMatZero : (H₂ - H₁) * V.1 = 0 := by
    ext i j
    have h' : (((H₂ - H₁) * V.1) *ᵥ Pi.single j 1) i = 0 := by
      rw [← Matrix.mulVec_mulVec]
      simpa only [Pi.zero_apply] using congrFun (hColZero j) i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.zero_apply] using h'
  have hVV : V.1 * V.1ᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact V.2.2
  have hSubZero : H₂ - H₁ = 0 := by
    calc H₂ - H₁ = (H₂ - H₁) * (V.1 * V.1ᴴ) := by rw [hVV, mul_one]
      _ = ((H₂ - H₁) * V.1) * V.1ᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hMatZero, zero_mul]
  exact sub_eq_zero.mp hSubZero

/-- Spectral uniqueness: any Hermitian `H₁` block-encoded by `ubDirectXo7PureUnitary prepOut prepMid
selectPure` at `(dfthcLowerBound, 97.3864)` equals `fullQuantP450HBlocked prepOut prepMid B_sel`. -/
theorem fullQuantP450HBlocked_eq_of_pulledSOS {wOuter wInner2 : ℕ}
    {H₁ : Operator (2 ^ (2 * 58))} (hH₁ : H₁.IsHermitian)
    (prepOut : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (hSelAll : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      selectPure.1 *ᵥ embedKet ψ o' m = embedKet ((B_sel o' m).1 *ᵥ ψ) o' m)
    (hSOS₁ : PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) H₁ dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOut prepMid selectPure)) :
    fullQuantP450HBlocked prepOut prepMid B_sel = H₁ := by
  let U_B := ubDirectXo7PureUnitary prepOut prepMid selectPure
  let P_mid := (rMidUB wOuter wInner2).basisOutcomeProjector 0
  let P_in := (rAllUB wOuter wInner2).basisOutcomeProjector 0
  have hdot_mid := fullQuant_pulledMid_quadForm prepOut prepMid selectPure B_sel hSelAll
  refine hermitian_eq_of_eigenvector_quadForm hH₁ fun φ E hEig hNorm χ ↦ ?_
  obtain ⟨_, _, _, _, hjord⟩ := hSOS₁.jordanRelation φ E hEig hNorm
  let e₁ := (rSysUB wOuter wInner2).tensorState φ (Pi.single 0 1)
  have he₁ : e₁ = embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0 :=
    (embedKet_zero_zero_eq_tensorState φ).symm
  have hPinχ : P_in *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0 =
      embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0 := by
    dsimp only [P_in]; rw [projAll_mulVec_embedKet, ite_eq_left ⟨rfl, rfl⟩]
  have hlhs :
      dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0))
          (P_in *ᵥ (U_B.1ᴴ *ᵥ (P_mid *ᵥ (U_B.1 *ᵥ e₁)))) =
        dotProduct (star χ)
          (((2 * 97.3864 : ℂ)⁻¹ •
            (fullQuantP450HBlocked prepOut prepMid B_sel - (dfthcLowerBound : ℂ) • 1)) *ᵥ φ) := by
    calc dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0))
            (P_in *ᵥ (U_B.1ᴴ *ᵥ (P_mid *ᵥ (U_B.1 *ᵥ e₁))))
        = dotProduct (star (P_in *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0))
            (U_B.1ᴴ *ᵥ (P_mid *ᵥ (U_B.1 *ᵥ e₁))) := by
          dsimp only [P_in]
          rw [dotProduct_star_mulVec, (rAllUB wOuter wInner2).basisOutcomeProjector_conjTranspose]
      _ = dotProduct (star (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0))
            ((P_mid * P_mid) *ᵥ (U_B.1 *ᵥ e₁)) := by
          rw [hPinχ, ← dotProduct_star_mulVec U_B.1]
          dsimp only [P_mid]
          rw [(rMidUB wOuter wInner2).basisOutcomeProjector_mul_self]
      _ = dotProduct (star (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0)))
            (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)) := by
          rw [← Matrix.mulVec_mulVec, ← he₁]; dsimp only [P_mid]
          conv_rhs => rw [dotProduct_star_mulVec ((rMidUB wOuter wInner2).basisOutcomeProjector 0),
            (rMidUB wOuter wInner2).basisOutcomeProjector_conjTranspose]
      _ = _ := hdot_mid χ φ
  have hrhs :
      dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0))
          ((((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • e₁) =
        dotProduct (star χ) ((((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • φ) := by
    rw [he₁, ← embedKet_smul, dotProduct_star_embedKet_ortho2, ite_eq_left rfl]
  have h1 := congrArg (dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0))) hjord
  change dotProduct (star (embedKet χ 0 0)) (P_in *ᵥ ((U_B.1ᴴ * P_mid * U_B.1) *ᵥ e₁)) =
    dotProduct (star (embedKet χ 0 0)) ((((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • e₁)
    at h1
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hlhs, hrhs] at h1
  exact h1

theorem blockedOrbitalReflection_comm_electronSectorProjector2
    (u : Fin 58 → ℝ) (σ : Fin 2) (η : ℕ) :
    blockedOrbitalReflection u σ * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * blockedOrbitalReflection u σ := by
  let U := p450FswapUninterleave.eval
  have hU1 : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
  have hsec : U.1 * electronSectorProjector (2 * 58) η * U.1ᴴ =
      electronSectorProjector (2 * 58) η :=
    p450FswapUninterleave_conj_electronSectorProjector η
  rw [← fswapUninterleave_conj_orbitalReflection u σ]
  calc (U.1 * orbitalReflection 58 u σ * U.1ᴴ) * electronSectorProjector (2 * 58) η
      = (U.1 * orbitalReflection 58 u σ * U.1ᴴ) *
          (U.1 * electronSectorProjector (2 * 58) η * U.1ᴴ) := by rw [hsec]
    _ = U.1 * (orbitalReflection 58 u σ * (U.1ᴴ * U.1) *
          electronSectorProjector (2 * 58) η) * U.1ᴴ := by simp only [Matrix.mul_assoc]
    _ = U.1 * (electronSectorProjector (2 * 58) η * (U.1ᴴ * U.1) *
          orbitalReflection 58 u σ) * U.1ᴴ := by
        have horb : orbitalReflection 58 u σ = OrbitalBridge.orbitalReflection 58 u σ := rfl
        rw [hU1, mul_one, mul_one, horb,
          OrbitalBridge.orbitalReflection_comm_electronSectorProjector 58 η u σ]
    _ = (U.1 * electronSectorProjector (2 * 58) η * U.1ᴴ) *
          (U.1 * orbitalReflection 58 u σ * U.1ᴴ) := by simp only [Matrix.mul_assoc]
    _ = electronSectorProjector (2 * 58) η *
          (U.1 * orbitalReflection 58 u σ * U.1ᴴ) := by rw [hsec]

theorem fullQuantP450HBlocked_comm_electronSectorProjector {wOuter wInner2 : ℕ}
    (prepOut : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (η : ℕ)
    (hB : ∀ o' m, (B_sel o' m).1 * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * (B_sel o' m).1) :
    fullQuantP450HBlocked prepOut prepMid B_sel * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * fullQuantP450HBlocked prepOut prepMid B_sel := by
  let P := electronSectorProjector (2 * 58) η
  have hPh : Pᴴ = P := PerturbedQPEClosure.electronSectorProjector_isHermitian (2 * 58) η
  have hM (o' : Fin (2 ^ mOutUB wOuter)) : fullHalfSystemOp prepMid B_sel o' * P =
      P * fullHalfSystemOp prepMid B_sel o' := by
    unfold fullHalfSystemOp; dsimp only [P]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hB]
  have hMh (o' : Fin (2 ^ mOutUB wOuter)) : (fullHalfSystemOp prepMid B_sel o')ᴴ * P =
      P * (fullHalfSystemOp prepMid B_sel o')ᴴ := by
    have hc := congrArg Matrix.conjTranspose (hM o')
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPh] at hc
    exact hc.symm
  have hsq (o' : Fin (2 ^ mOutUB wOuter)) :
      ((fullHalfSystemOp prepMid B_sel o')ᴴ * fullHalfSystemOp prepMid B_sel o') *
          electronSectorProjector (2 * 58) η =
        electronSectorProjector (2 * 58) η *
          ((fullHalfSystemOp prepMid B_sel o')ᴴ * fullHalfSystemOp prepMid B_sel o') := by
    change ((fullHalfSystemOp prepMid B_sel o')ᴴ * fullHalfSystemOp prepMid B_sel o') * P =
      P * ((fullHalfSystemOp prepMid B_sel o')ᴴ * fullHalfSystemOp prepMid B_sel o')
    rw [Matrix.mul_assoc, hM o', ← Matrix.mul_assoc, hMh o', Matrix.mul_assoc]
  unfold fullQuantP450HBlocked
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    Finset.sum_mul, Finset.mul_sum]
  exact congrArg (_ + ((2 * 97.3864 : ℝ) : ℂ) • ·)
    (Finset.sum_congr rfl fun o' _ ↦ congrArg _ (hsq o'))

theorem norm_electronSectorProjector_le_one2 (k η : ℕ) :
    ‖electronSectorProjector k η‖ ≤ 1 :=
  QubitisedWalk.opNorm_le_of_vecNormSq_mulVec (electronSectorProjector k η) zero_le_one fun v ↦ by
    rw [_root_.one_pow, one_mul]; unfold QubitisedWalk.vecNormSq
    exact PerturbedQPEClosure.sum_normSq_electronSectorProjector_mulVec_le k η v

theorem agreesOnElectronSector_of_comm_opNorm_and_agrees {η : ℕ}
    {H₂ H₁ B : Operator (2 ^ (2 * 58))} {ε δ₁ δ : ℝ}
    (hcomm : H₂ * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * H₂)
    (hop : ‖H₂ - H₁‖ ≤ ε)
    (h₁ : AgreesOnElectronSector 58 η H₁ B δ₁)
    (hδ : ε + δ₁ ≤ δ) :
    AgreesOnElectronSector 58 η H₂ B δ := by
  let P := electronSectorProjector (2 * 58) η
  have hP : ‖P‖ ≤ 1 := norm_electronSectorProjector_le_one2 (2 * 58) η
  have hsplit : P * (H₂ - B) * P = P * (H₂ - H₁) * P + P * (H₁ - B) * P := by
    have hsub : H₂ - B = (H₂ - H₁) + (H₁ - B) := by abel
    rw [hsub, Matrix.mul_add, Matrix.add_mul]
  have hP21 : ‖P * (H₂ - H₁) * P‖ ≤ ε := by
    calc ‖P * (H₂ - H₁) * P‖
        ≤ ‖P * (H₂ - H₁)‖ * ‖P‖ := opNorm_mul_le2 _ _
      _ ≤ ‖P * (H₂ - H₁)‖ * 1 := mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = ‖P * (H₂ - H₁)‖ := mul_one _
      _ ≤ ‖P‖ * ‖H₂ - H₁‖ := opNorm_mul_le2 _ _
      _ ≤ 1 * ‖H₂ - H₁‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ ε := by rw [one_mul]; exact hop
  refine ⟨hcomm, ?_⟩
  change ‖P * (H₂ - B) * P‖ ≤ δ
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hP21 h₁.2).trans hδ)

/-- Master `AgreesOnElectronSector 58 63` theorem for `fullQuantP450HBlocked` at arbitrary
`(wOuter, wInner2)` from any Hermitian `H₁` block-encoded at `prepOutIdeal` and column-`0` `L¹`
probability deviation `εOut` (`‖fullQuant(prepOutImpl) - H₁‖ ≤ 2 * 97.3864 * εOut`). -/
theorem agreesOnElectronSector_fullQuant_of_pulledSOS_and_l1 {wOuter wInner2 : ℕ}
    {H₁ : Operator (2 ^ (2 * 58))} (hH₁ : H₁.IsHermitian)
    (prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (sP : Unitary (2 ^ nUB wOuter wInner2))
    (B_sel : Fin (2 ^ mOutUB wOuter) → Fin (2 ^ mMidUB wInner2) → Unitary (2 ^ (2 * 58)))
    (hSelAll : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      sP.1 *ᵥ embedKet ψ o' m = embedKet ((B_sel o' m).1 *ᵥ ψ) o' m)
    (hComm : ∀ o' m, (B_sel o' m).1 * electronSectorProjector (2 * 58) 63 =
      electronSectorProjector (2 * 58) 63 * (B_sel o' m).1)
    (hSOS₁ : PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) H₁ dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOutIdeal prepMid sP))
    {εOut δIn δ_H : ℝ}
    (hL1 : (∑ o' : Fin (2 ^ mOutUB wOuter),
      |Complex.normSq (prepOutImpl.1 o' 0) - Complex.normSq (prepOutIdeal.1 o' 0)|) ≤ εOut)
    (hInner : AgreesOnElectronSector 58 63 H₁ BlockEncodingCore.p450HBlocked δIn)
    (hδ : 2 * 97.3864 * εOut + δIn ≤ δ_H) :
    AgreesOnElectronSector 58 63
      (fullQuantP450HBlocked prepOutImpl prepMid B_sel)
      BlockEncodingCore.p450HBlocked δ_H := by
  have hEq : fullQuantP450HBlocked prepOutIdeal prepMid B_sel = H₁ :=
    fullQuantP450HBlocked_eq_of_pulledSOS hH₁ prepOutIdeal prepMid sP B_sel hSelAll hSOS₁
  have hop : ‖fullQuantP450HBlocked prepOutImpl prepMid B_sel - H₁‖ ≤
      2 * 97.3864 * εOut := by
    rw [← hEq]
    exact (norm_fullQuantP450HBlocked_sub_le_l1 prepOutImpl prepOutIdeal prepMid B_sel).trans
      (mul_le_mul_of_nonneg_left hL1 (by norm_num))
  exact agreesOnElectronSector_of_comm_opNorm_and_agrees
    (fullQuantP450HBlocked_comm_electronSectorProjector prepOutImpl prepMid B_sel 63 hComm)
    hop hInner hδ

attribute [irreducible] fullQuantP450HBlocked

end SOSAndOuterClosures

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145L1

end

/-!
# Support-Disjoint `20-T` Outer Coin, Affine-`alt` `π145` Table & Exact `L¹` Word Certs

Core primitives for the `wOuter = 8` (`kZeroOut = 4`) zero-shear outer `PREP` architecture:
1. An ancilla-free `4`-qubit `20-T` (`10`-`ctrlH`, `0 TOFF`, `0` scratch) outer packet coin
   `orthCoin10Circuit` preparing dyadic weights `[0, 4, 0, 128, 64, 256, 8, 16, 256, 16, 256,
   16, 1, 1, 1, 1]` on `|0000⟩` while mapping `|0001⟩` (`jAux4 = 1`) to `|0000⟩` (`w₀ = 0`),
   eliminating all cross terms between the `9`-qubit Grover-`184` `0..255` and `256..511` branches.
2. A `10`-AND (`40 T`, `0 TOFF`) reversible packet multiplexer `pktMux10Rev2` (`pKeepMux25_2`
   at `25` ANDs = `100 T`).
3. A `184`-entry zero-shear `π145` outer alias table `pi145OuterTable` preserving `pi145Perm`
   and `pi145WeightNat` while making `alt` bit `7` group-constant and `alt` bit `6` affine in
   `x₁` alone (`0` `x₀` dependence), cutting the forward QROM `alt` lookup from `6` ANDs to `4`
   ANDs (`-8 T` on forward `PREP_out`).
4. Exact `ℤ[√2]` column-`0` `L¹` verifiers and three Pareto `Clifford+T` magnitude words:
   `mag8To23Word9` (`9 T`, `630 T/Refl2`), `mag8To23Word15` (`15 T`, `666 T/Refl2`), and
   `mag8To23Word17` (`17 T`, `678 T/Refl2`).

## References
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: 10.22331/q-2018-06-18-74.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, *Quantum* **3**, 208 (2019),
  DOI: 10.22331/q-2019-12-02-208.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024),
  DOI: 10.22331/q-2024-06-17-1375.
- N. J. Ross and P. Selinger, *Quantum Inf. Comput.* **16**(11–12), 901–953 (2016),
  DOI: 10.26421/QIC16.11-12-1.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Pi145Fast2RotCore
open QuantumComputation.Specs QuantumComputation.Specs.P450

/-! ## Section 1: Computable Coin Gates, Affine-`alt` `π145` Table & `ℤ[√2]` `L¹` Certs -/

section ComputableCerts

open Circuit
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CoherentAlias
open Solution.OptU2Grover184PrepOut13
open Solution.OuterWeights.GroverUniform
open Solution.StepOuter8Pi145Outer
open scoped BigOperators Circuit.Notation

/-- Elementary `4`-qubit self-inverse gate used in `orthCoin10Circuit`. -/
inductive CoinGate4 : Type where
  | x (w : Wire 4)
  | cnot (c t : Wire 4) (h : c ≠ t)
  | ch (c t : Wire 4) (h : c ≠ t)

/-- Lower a `CoinGate4` to a `4`-qubit `Circuit 4`. -/
def CoinGate4.toCircuit : CoinGate4 → Circuit 4
  | .x w => Circuit.X w
  | .cnot c t h => Circuit.CNOT c t h
  | .ch c t h => ctrlH.onRegister (QRegister.pair c t h)

/-- Toggle bit `w` of a `4`-qubit computational basis index. -/
def flipBit4 (w : Wire 4) (j : Fin (2 ^ 4)) : Fin (2 ^ 4) :=
  setBitIdx j w (basisBits 4 j w + 1)

/-- Action of `CNOT c t` on `4`-qubit computational basis indices. -/
def cnotFlip4 (c t : Wire 4) (j : Fin (2 ^ 4)) : Fin (2 ^ 4) :=
  setBitIdx j t (basisBits 4 j t + basisBits 4 j c)

/-- Check that `st j` has an even rational component whenever control bit `c` is `1`. -/
def evenCtrlH (c : Wire 4) (st : Fin (2 ^ 4) → ℤ × ℤ) : Bool :=
  (List.finRange (2 ^ 4)).all fun j ↦
    if j.val.testBit c.val then decide ((st j).1 % 2 = 0) else true

/-- Symbolic `ℤ[√2] / 32` state update under `ctrlH` with control `c` and target `t`. -/
def stepCtrlHAmp (c t : Wire 4) (st : Fin (2 ^ 4) → ℤ × ℤ) (x : Fin (2 ^ 4)) : ℤ × ℤ :=
  if x.val.testBit c.val then
    let p0 := st (setBitIdx x t 0)
    let p1 := st (setBitIdx x t 1)
    if x.val.testBit t.val then
      (p0.2 - p1.2, p0.1 / 2 - p1.1 / 2)
    else
      (p0.2 + p1.2, p0.1 / 2 + p1.1 / 2)
  else
    st x

/-- Validity check for one `CoinGate4` step in `ℤ[√2] / 32`. -/
def CoinGate4.validAmp : CoinGate4 → (Fin (2 ^ 4) → ℤ × ℤ) → Bool
  | .x _, _ => true
  | .cnot _ _ _, _ => true
  | .ch c _ _, st => evenCtrlH c st

/-- Symbolic `ℤ[√2] / 32` state transformer for one `CoinGate4`. -/
def CoinGate4.stepAmp : CoinGate4 → (Fin (2 ^ 4) → ℤ × ℤ) → (Fin (2 ^ 4) → ℤ × ℤ)
  | .x w, st => fun j ↦ st (flipBit4 w j)
  | .cnot c t _, st => fun j ↦ st (cnotFlip4 c t j)
  | .ch c t _, st => stepCtrlHAmp c t st

/-- Check that every `ctrlH` along `gs` preserves integrality in `ℤ[√2] / 32`. -/
def validCoinGates : List CoinGate4 → (Fin (2 ^ 4) → ℤ × ℤ) → Bool
  | [], _ => true
  | g :: gs, st => g.validAmp st && validCoinGates gs (g.stepAmp st)

/-- Symbolic `ℤ[√2] / 32` evolution along a `List CoinGate4` from left to right. -/
def stepCoinGates : List CoinGate4 → (Fin (2 ^ 4) → ℤ × ℤ) → (Fin (2 ^ 4) → ℤ × ℤ)
  | [], st => st
  | g :: gs, st => stepCoinGates gs (g.stepAmp st)

/-- `18`-gate (`10`-`ctrlH` = `20 T`, `0 TOFF`) gate list for `orthCoin10Circuit`. -/
def orthCoin10Gates : List CoinGate4 :=
  [ .x 0,
    .ch 0 1 (by decide),
    .cnot 1 0 (by decide),
    .ch 0 2 (by decide),
    .ch 2 3 (by decide),
    .ch 3 1 (by decide),
    .ch 1 2 (by decide),
    .cnot 0 1 (by decide),
    .cnot 2 0 (by decide),
    .ch 0 2 (by decide),
    .cnot 3 2 (by decide),
    .ch 2 3 (by decide),
    .cnot 3 0 (by decide),
    .ch 0 2 (by decide),
    .cnot 2 1 (by decide),
    .cnot 1 3 (by decide),
    .ch 3 0 (by decide),
    .ch 3 1 (by decide) ]

/-- Ancilla-free `4`-qubit `20-T` (`0 TOFF`) support-disjoint outer packet coin circuit. -/
def orthCoin10Circuit : Circuit 4 :=
  Circuit.sequence (orthCoin10Gates.map CoinGate4.toCircuit)

/-- Ancilla-free `4`-qubit `20-T` (`0 TOFF`) inverse outer packet coin circuit. -/
def orthCoin10InvCircuit : Circuit 4 :=
  Circuit.sequence (orthCoin10Gates.reverse.map CoinGate4.toCircuit)

/-- Exact integer packet weights (`sum = 1024`, `w 0 = 0`) for `orthCoin10Circuit`. -/
def coin10Weight : Fin (2 ^ 4) → ℕ :=
  ![0, 4, 0, 128, 64, 256, 8, 16, 256, 16, 256, 16, 1, 1, 1, 1]

/-- Initial `ℤ[√2] / 32` representation of `|0000⟩` (`basisState 0`). -/
def basis0Amp (j : Fin (2 ^ 4)) : ℤ × ℤ :=
  if j.val == 0 then (32, 0) else (0, 0)

/-- Initial `ℤ[√2] / 32` representation of `|0001⟩` (`basisState 1`, `jAux4`). -/
def basis1Amp (j : Fin (2 ^ 4)) : ℤ × ℤ :=
  if j.val == 1 then (32, 0) else (0, 0)

/-- Final `ℤ[√2] / 32` column-`0` vector of `orthCoin10Circuit`. -/
def coinCol0Amp : Fin (2 ^ 4) → ℤ × ℤ :=
  stepCoinGates orthCoin10Gates basis0Amp

/-- Final `ℤ[√2] / 32` column-`1` vector of `orthCoin10Circuit`. -/
def coinCol1Amp : Fin (2 ^ 4) → ℤ × ℤ :=
  stepCoinGates orthCoin10Gates basis1Amp

theorem sumCoin10Weight : ∑ c : Fin (2 ^ 4), coin10Weight c = 1024 := by
  decide +kernel

theorem validCoinGatesBasis0 :
    validCoinGates orthCoin10Gates basis0Amp = true := by decide +kernel

theorem validCoinGatesBasis1 :
    validCoinGates orthCoin10Gates basis1Amp = true := by decide +kernel

theorem coinCol0Amp_weight_ok :
    ((List.finRange (2 ^ 4)).all fun c ↦
      decide ((coinCol0Amp c).1 * (coinCol0Amp c).2 = 0 ∧
        (coinCol0Amp c).1 * (coinCol0Amp c).1 +
          2 * ((coinCol0Amp c).2 * (coinCol0Amp c).2) =
          (coin10Weight c : ℤ))) = true := by decide +kernel

theorem coinCol0Amp_zero_ok :
    decide (coinCol0Amp 0 = (0, 0)) = true := by decide +kernel

theorem coinCol1Amp_eq_basis0_ok :
    ((List.finRange (2 ^ 4)).all fun c ↦
      decide (coinCol1Amp c = basis0Amp c)) = true := by decide +kernel

/-- Boolean `10`-AND keep-selector function paired with `coin10Weight`. -/
def pktKeepSel10 (k : Fin 10 → ZMod 2) (q : Fin 4 → ZMod 2) : ZMod 2 :=
  let u0 := ParamDyadicOuter13.mux2Bit (q 1) (k 2) (k 7)
  let u1 := ParamDyadicOuter13.mux2Bit (q 1) (k 6) (k 3)
  let u2 := ParamDyadicOuter13.mux2Bit (q 1) (k 8) (k 4)
  let u3 := (1 + q 1) * k 0
  let u4 := ParamDyadicOuter13.mux2Bit (q 0) u1 u2
  let u5 := ParamDyadicOuter13.mux2Bit (q 0) (k 9) (k 5)
  let u6 := ParamDyadicOuter13.mux2Bit (q 0) (k 1) u3
  let u7 := ParamDyadicOuter13.mux2Bit (q 2) u0 u4
  let u8 := ParamDyadicOuter13.mux2Bit (q 2) u5 u6
  ParamDyadicOuter13.mux2Bit (q 3) u7 u8

/-- Swap-indicator bit (`0` on keep, `1` on swap) for `keep : Fin 1024` and `c : Fin 16`. -/
def pktSwapBit10 (keep : Fin 1024) (c : Fin 16) : ZMod 2 :=
  1 + pktKeepSel10 (basisBits 10 keep) (basisBits 4 c)

/-- Exact `ℤ[√2]` Boolean verifier certifying `wordCountT w = tExpected` and
`2 * (1 - p) * (1 - 4 * p) ^ 2 ≤ epsNum / epsDen` for `p = (23 / 32) * |W_{0,0}|²`. -/
def checkOrthGrover184L1Word (tExpected epsNum epsDen : ℕ) (w : List Gate1) : Bool :=
  (wordCountT w == tExpected) &&
  decide (0 < epsDen) &&
  let M := evalWordCyc w
  let D : ℕ := 2 ^ M.k
  let qZ2 := M.a.normSqZ2
  let oneSubP := (Z2.ofNat (32 * D)).sub (qZ2.scaleNat 23)
  let oneSub4P := (Z2.ofNat (8 * D)).sub (qZ2.scaleNat 23)
  let numZ2 := oneSubP.mul (oneSub4P.mul oneSub4P)
  ((Z2.ofNat (epsNum * 1024 * D ^ 3)).sub (numZ2.scaleNat epsDen)).geZero

@[simp] theorem countOrthCoin10Circuit_toff : orthCoin10Circuit.count .TOFF = 0 := rfl
@[simp] theorem countOrthCoin10Circuit_t : orthCoin10Circuit.count .T = 20 := rfl
@[simp] theorem countOrthCoin10InvCircuit_toff : orthCoin10InvCircuit.count .TOFF = 0 := rfl
@[simp] theorem countOrthCoin10InvCircuit_t : orthCoin10InvCircuit.count .T = 20 := rfl

end ComputableCerts

/-! ## Section 2: `orthCoin10Unitary` Support-Disjointness, `pKeepMux25_2` & Exact `L¹` Law -/

noncomputable section

open Operator QProg Matrix Circuit Real
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.Comparators
open Solution.BlockEncodingCore
open Solution.CoherentAlias
open Solution.OuterWeights.GroverUniform
open Solution.SelectSwapQROM
open Solution.OptFactoredMag30AndCoin9
open Solution.OptU2Grover184PrepOut13
open Solution.ReordOuter13Bridge
open Solution.StepOuter8Pi145Outer
open Solution.StepOuter8Pi145L1
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowFast2RotCore (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- `4`-qubit support-disjoint outer packet coin unitary realized by `orthCoin10Circuit`. -/
def orthCoin10Unitary : Unitary (2 ^ 4) := orthCoin10Circuit.eval

/-- Relocated `20-T`, `0-TOFF` forward outer packet coin dynamic circuit (`0` scratch wires). -/
def orthCoin10Dyn {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) : DynamicCircuit Var N :=
  .circuit (orthCoin10Circuit.onRegister rPkt)

/-- Relocated `20-T`, `0-TOFF` inverse outer packet coin dynamic circuit (`0` scratch wires). -/
def orthCoin10InvDyn {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) : DynamicCircuit Var N :=
  .circuit (orthCoin10InvCircuit.onRegister rPkt)

@[simp]
theorem countOrthCoin10Dyn_toff {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (orthCoin10Dyn (Var := Var) rPkt).count .TOFF = 0 := by
  simp [orthCoin10Dyn]

@[simp]
theorem countOrthCoin10Dyn_t {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (orthCoin10Dyn (Var := Var) rPkt).count .T = 20 := by
  simp [orthCoin10Dyn]

@[simp]
theorem countOrthCoin10InvDyn_toff {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (orthCoin10InvDyn (Var := Var) rPkt).count .TOFF = 0 := by
  simp [orthCoin10InvDyn]

@[simp]
theorem countOrthCoin10InvDyn_t {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (orthCoin10InvDyn (Var := Var) rPkt).count .T = 20 := by
  simp [orthCoin10InvDyn]

theorem CoinGate4.eval_toCircuit_inv (g : CoinGate4) :
    g.toCircuit.eval⁻¹ = g.toCircuit.eval := by
  cases g with
  | x w => exact (Circuit.eval_inverse (Circuit.X w)).symm
  | cnot c t h => exact (Circuit.eval_inverse (Circuit.CNOT c t h)).symm
  | ch c t h =>
      have hh : Qubit.H⁻¹ = Qubit.H := (eq_inv_of_mul_eq_one_left Qubit.H_sq).symm
      rw [CoinGate4.toCircuit, Circuit.eval_onRegister, eval_ctrlH, ← QRegister.embedUnitary_inv,
        predCtrlUnitary_inv, hh]

theorem eval_sequence_reverse_coinGates :
    ∀ gs : List CoinGate4,
      (Circuit.sequence (gs.reverse.map CoinGate4.toCircuit)).eval =
        (Circuit.sequence (gs.map CoinGate4.toCircuit)).eval⁻¹
  | [] => by simp
  | g :: gs => by
      have happ (l₁ l₂ : List (Circuit 4)) :
          (Circuit.sequence (l₁ ++ l₂)).eval =
            (Circuit.sequence l₂).eval * (Circuit.sequence l₁).eval := by
        induction l₁ with
        | nil => simp
        | cons c cs ih => simp [List.cons_append, ih, mul_assoc]
      rw [List.reverse_cons, List.map_append, happ, eval_sequence_reverse_coinGates gs,
        List.map_singleton, List.map_cons, Circuit.sequence_cons, Circuit.sequence_cons,
        Circuit.sequence_nil, Circuit.eval_seq, Circuit.eval_seq, Circuit.eval_identity,
        one_mul, _root_.mul_inv_rev, CoinGate4.eval_toCircuit_inv]

theorem evalOrthCoin10InvCircuit :
    orthCoin10InvCircuit.eval = orthCoin10Circuit.eval⁻¹ :=
  eval_sequence_reverse_coinGates orthCoin10Gates

theorem cleanRealizesOrthCoin10Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s : ℕ} (v : Var) (rPkt : QRegister 4 N) (rScr : QRegister s N)
    (hdisj : rPkt.DisjointWires rScr) :
    Solution.CleanDyn.CleanRealizes v rPkt rScr orthCoin10Unitary (orthCoin10Dyn rPkt) :=
  Solution.CleanDyn.CleanRealizes.circuit v rPkt rScr hdisj orthCoin10Circuit
    countOrthCoin10Circuit_toff

theorem cleanRealizesOrthCoin10InvDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s : ℕ} (v : Var) (rPkt : QRegister 4 N) (rScr : QRegister s N)
    (hdisj : rPkt.DisjointWires rScr) :
    Solution.CleanDyn.CleanRealizes v rPkt rScr orthCoin10Unitary⁻¹ (orthCoin10InvDyn rPkt) := by
  have hc := Solution.CleanDyn.CleanRealizes.circuit v rPkt rScr hdisj orthCoin10InvCircuit
    countOrthCoin10InvCircuit_toff
  rwa [evalOrthCoin10InvCircuit] at hc

/-- Dyadic `(p.1 + p.2 * √2) / 32` amplitude value in `ℂ`. -/
def amp32Val (p : ℤ × ℤ) : ℂ :=
  ((((p.1 : ℝ) + (p.2 : ℝ) * √2) / 32 : ℝ) : ℂ)

/-- `4`-qubit state vector assembled from `16` dyadic `ℤ[√2] / 32` amplitudes. -/
def evalAmp32 (st : Fin (2 ^ 4) → ℤ × ℤ) : Fin (2 ^ 4) → ℂ :=
  ∑ j : Fin (2 ^ 4), amp32Val (st j) • basisState j

theorem evalAmp32_apply (st : Fin (2 ^ 4) → ℤ × ℤ) (x : Fin (2 ^ 4)) :
    evalAmp32 st x = amp32Val (st x) := by
  dsimp only [evalAmp32]
  rw [Finset.sum_apply, Finset.sum_eq_single x]
  · simp [basisState]
  · intro j _ hjx; simp [basisState, Pi.single_eq_of_ne hjx.symm]
  · simp

theorem flipBit4_involutive (w : Wire 4) (j : Fin (2 ^ 4)) :
    flipBit4 w (flipBit4 w j) = j := by
  revert j w; decide

theorem cnotFlip4_involutive (c t : Wire 4) (h : c ≠ t) (j : Fin (2 ^ 4)) :
    cnotFlip4 c t (cnotFlip4 c t j) = j := by
  revert j h t c; decide

theorem mulVec_permAmp32 {M : Operator (2 ^ 4)} {f : Fin (2 ^ 4) → Fin (2 ^ 4)}
    (hf : ∀ j, f (f j) = j) (hM : ∀ j, M *ᵥ basisState j = basisState (f j))
    (st : Fin (2 ^ 4) → ℤ × ℤ) :
    M *ᵥ evalAmp32 st = evalAmp32 (fun x ↦ st (f x)) := by
  funext x; rw [evalAmp32_apply]; dsimp only [evalAmp32]
  rw [Matrix.mulVec_sum, Finset.sum_apply, Finset.sum_eq_single (f x)]
  · rw [Matrix.mulVec_smul, hM, hf]; simp [basisState]
  · intro j _ hjf
    have hne : f j ≠ x := fun h ↦ hjf (by rw [← h, hf])
    rw [Matrix.mulVec_smul, hM]; simp [basisState, Pi.single_eq_of_ne hne.symm]
  · simp

theorem qubit_H_entries :
    Qubit.H.1 0 0 = ((1 / √2 : ℝ) : ℂ) ∧ Qubit.H.1 1 0 = ((1 / √2 : ℝ) : ℂ) ∧
    Qubit.H.1 0 1 = ((1 / √2 : ℝ) : ℂ) ∧ Qubit.H.1 1 1 = -((1 / √2 : ℝ) : ℂ) := by
  simp [Qubit.H, Complex.real_smul, one_div]

theorem amp32Val_mul_pos (p : ℤ × ℤ) (hp : p.1 % 2 = 0) :
    amp32Val p * ((1 / √2 : ℝ) : ℂ) = amp32Val (p.2, p.1 / 2) := by
  have h2 : p.1 = 2 * (p.1 / 2) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hp)).symm
  have h2r : (p.1 : ℝ) = 2 * ((p.1 / 2 : ℤ) : ℝ) := by exact_mod_cast h2
  have hsq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  dsimp only [amp32Val]; rw [← Complex.ofReal_mul]; congr 1
  rw [h2r]; field_simp [hs0]; linear_combination -((p.1 / 2 : ℤ) : ℝ) * hsq

theorem amp32Val_add_pos (p q : ℤ × ℤ) (hp : p.1 % 2 = 0) (hq : q.1 % 2 = 0) :
    amp32Val p * ((1 / √2 : ℝ) : ℂ) + amp32Val q * ((1 / √2 : ℝ) : ℂ) =
      amp32Val (p.2 + q.2, p.1 / 2 + q.1 / 2) := by
  rw [amp32Val_mul_pos p hp, amp32Val_mul_pos q hq]
  dsimp only [amp32Val]; rw [← Complex.ofReal_add]; congr 1; push_cast; ring

theorem amp32Val_sub_pos (p1 p0 : ℤ × ℤ) (h1 : p1.1 % 2 = 0) (h0 : p0.1 % 2 = 0) :
    amp32Val p1 * -((1 / √2 : ℝ) : ℂ) + amp32Val p0 * ((1 / √2 : ℝ) : ℂ) =
      amp32Val (p0.2 - p1.2, p0.1 / 2 - p1.1 / 2) := by
  have hneg : amp32Val p1 * -((1 / √2 : ℝ) : ℂ) =
      -(amp32Val p1 * ((1 / √2 : ℝ) : ℂ)) := by ring
  rw [hneg, amp32Val_mul_pos p1 h1, amp32Val_mul_pos p0 h0]
  dsimp only [amp32Val]; rw [← Complex.ofReal_neg, ← Complex.ofReal_add]; congr 1; push_cast; ring

theorem pair_ctrl_fires (c t : Wire 4) (h : c ≠ t) (j : Fin (2 ^ 4)) :
    ((((QRegister.pair c t h).compose (QRegister.block 0 1 (by omega))).extractIndex j).val == 1) =
      j.val.testBit c.val := by
  revert h j t c; decide

theorem setBitIdx_other_ne (t : Wire 4) (j x : Fin (2 ^ 4))
    (hjx : j ≠ x) (hjy : j ≠ flipBit4 t x) :
    setBitIdx j t 0 ≠ x ∧ setBitIdx j t 1 ≠ x := by
  revert hjy hjx x j t; decide

theorem flipBit4_props (c t : Wire 4) (h : c ≠ t) (x : Fin (2 ^ 4)) :
    flipBit4 t x ≠ x ∧ (flipBit4 t x).val.testBit c.val = x.val.testBit c.val ∧
    (x.val.testBit t.val = false → basisBits 4 x t = 0 ∧ setBitIdx x t 0 = x ∧
      setBitIdx x t 1 = flipBit4 t x ∧ basisBits 4 (flipBit4 t x) t = 1 ∧
      setBitIdx (flipBit4 t x) t 0 = x ∧ setBitIdx (flipBit4 t x) t 1 = flipBit4 t x) ∧
    (x.val.testBit t.val = true → basisBits 4 x t = 1 ∧ setBitIdx x t 0 = flipBit4 t x ∧
      setBitIdx x t 1 = x ∧ basisBits 4 (flipBit4 t x) t = 0 ∧
      setBitIdx (flipBit4 t x) t 0 = flipBit4 t x ∧ setBitIdx (flipBit4 t x) t 1 = x) := by
  revert h x t c; decide

theorem eval_ctrlHAmp32 (c t : Wire 4) (h : c ≠ t) (st : Fin (2 ^ 4) → ℤ × ℤ)
    (heven : evenCtrlH c st = true) :
    (ctrlH.onRegister (QRegister.pair c t h)).eval.1 *ᵥ evalAmp32 st =
      evalAmp32 (stepCtrlHAmp c t st) := by
  rw [Circuit.eval_onRegister, eval_ctrlH, QRegister.embedUnitary_val]
  dsimp only [ctrlUnitary, predCtrlUnitary]
  have ht_last : QRegister.pair c t h (Fin.last 1) = t := rfl
  funext x; rw [evalAmp32_apply]; dsimp only [evalAmp32]
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  obtain ⟨hyx, hcy, hxt0, hxt1⟩ := flipBit4_props c t h x
  set y := flipBit4 t x
  have hother (j : Fin (2 ^ 4)) (hjx : j ≠ x) (hjy : j ≠ y) :
      (((QRegister.pair c t h).embedMatrix
          (predCtrlMatrix (fun u : Fin 2 ↦ u.val == 1) Qubit.H.1)) *ᵥ
        (amp32Val (st j) • basisState j)) x = 0 := by
    rw [Matrix.mulVec_smul, embed_predCtrlMatrix_mulVec_basisState]
    obtain ⟨hn0, hn1⟩ := setBitIdx_other_ne t j x hjx hjy
    by_cases hcf :
        (((QRegister.pair c t h).compose (QRegister.block 0 1 (by omega))).extractIndex j).val == 1
    · simp only [hcf, ↓reduceIte, ht_last, Pi.smul_apply, Pi.add_apply, basisState,
        Pi.single_eq_of_ne hn0.symm, Pi.single_eq_of_ne hn1.symm, smul_zero, add_zero]
    · simp only [hcf, Bool.false_eq_true, ↓reduceIte, Pi.smul_apply, basisState,
        Pi.single_eq_of_ne hjx.symm, smul_zero]
  rw [(Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm,
    (Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩)).symm,
    Finset.sum_eq_zero (fun j hj ↦ by
      have hj1 := Finset.mem_erase.mp hj
      have hj2 := Finset.mem_erase.mp hj1.2
      exact hother j hj2.1 hj1.1), add_zero]
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul,
    embed_predCtrlMatrix_mulVec_basisState, embed_predCtrlMatrix_mulVec_basisState]
  rw [pair_ctrl_fires c t h x, pair_ctrl_fires c t h y, hcy]
  dsimp only [stepCtrlHAmp]
  cases hc : x.val.testBit c.val
  · simp only [Bool.false_eq_true, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      basisState, Pi.single_eq_same, Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, add_zero]
  · have hex : (st x).1 % 2 = 0 := by
      have hx := List.all_eq_true.mp heven x (List.mem_finRange x)
      simp only [hc, ↓reduceIte, decide_eq_true_eq] at hx
      exact hx
    have hey : (st y).1 % 2 = 0 := by
      have hy := List.all_eq_true.mp heven y (List.mem_finRange y)
      simp only [hcy, hc, ↓reduceIte, decide_eq_true_eq] at hy
      exact hy
    cases ht : x.val.testBit t.val
    · obtain ⟨hbt, hs0, hs1, hyt, hys0, hys1⟩ := hxt0 ht
      simp only [Bool.false_eq_true, ↓reduceIte, ht_last, hbt, hyt, hs0, hs1, hys0, hys1,
        show (1 : ZMod 2) ≠ 0 by decide, qubit_H_entries.1, qubit_H_entries.2.2.1,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisState, Pi.single_eq_same,
        Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, add_zero]
      exact amp32Val_add_pos (st x) (st y) hex hey
    · obtain ⟨hbt, hs0, hs1, hyt, hys0, hys1⟩ := hxt1 ht
      simp only [↓reduceIte, ht_last, hbt, hyt, hs0, hs1, hys0, hys1,
        show (1 : ZMod 2) ≠ 0 by decide, qubit_H_entries.2.2.2, qubit_H_entries.2.1,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisState, Pi.single_eq_same,
        Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, zero_add]
      exact amp32Val_sub_pos (st x) (st y) hex hey

theorem CoinGate4.evalAmp32_2 (g : CoinGate4) (st : Fin (2 ^ 4) → ℤ × ℤ)
    (hv : g.validAmp st = true) :
    g.toCircuit.eval.1 *ᵥ evalAmp32 st = evalAmp32 (g.stepAmp st) := by
  cases g with
  | x w =>
      exact mulVec_permAmp32 (flipBit4_involutive w) (fun j ↦ by
        have hj : basisState j = SelectSwapQROM.ket (basisBits 4 j) :=
          (congrArg basisState (SelectSwapQROM.symm_basisBits j)).symm
        change (Circuit.X w).eval.1.mulVec (basisState j) = _
        rw [hj, SelectSwapQROM.ket_X]; rfl) st
  | cnot c t h =>
      exact mulVec_permAmp32 (cnotFlip4_involutive c t h) (fun j ↦ by
        have hj : basisState j = SelectSwapQROM.ket (basisBits 4 j) :=
          (congrArg basisState (SelectSwapQROM.symm_basisBits j)).symm
        change (Circuit.CNOT c t h).eval.1.mulVec (basisState j) = _
        rw [hj, SelectSwapQROM.ket_CNOT]; rfl) st
  | ch c t h =>
      exact eval_ctrlHAmp32 c t h st hv

theorem eval_coinGatesAmp32 :
    ∀ (gs : List CoinGate4) (st : Fin (2 ^ 4) → ℤ × ℤ),
      validCoinGates gs st = true →
      (Circuit.sequence (gs.map CoinGate4.toCircuit)).eval.1 *ᵥ evalAmp32 st =
        evalAmp32 (stepCoinGates gs st)
  | [], st, _ => by simp [stepCoinGates]
  | g :: gs, st, hv => by
      obtain ⟨hvg, hvgs⟩ := Bool.and_eq_true_iff.mp hv
      rw [List.map_cons, Circuit.sequence_cons, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, g.evalAmp32_2 st hvg]
      exact eval_coinGatesAmp32 gs (g.stepAmp st) hvgs

theorem basis0Amp_eq_basisState : evalAmp32 basis0Amp = basisState 0 := by
  funext x; rw [evalAmp32_apply]
  fin_cases x <;> simp [basis0Amp, amp32Val, basisState]

theorem basis1Amp_eq_basisState : evalAmp32 basis1Amp = basisState 1 := by
  funext x; rw [evalAmp32_apply]
  fin_cases x <;> simp [basis1Amp, amp32Val, basisState]

theorem orthCoin10_mulVec_zero_eq :
    orthCoin10Unitary.1 *ᵥ basisState 0 = evalAmp32 coinCol0Amp := by
  rw [← basis0Amp_eq_basisState]
  exact eval_coinGatesAmp32 orthCoin10Gates basis0Amp validCoinGatesBasis0

theorem orthCoin10_mulVec_one_eq :
    orthCoin10Unitary.1 *ᵥ basisState 1 = basisState 0 := by
  have h1 : orthCoin10Unitary.1 *ᵥ basisState 1 = evalAmp32 coinCol1Amp := by
    rw [← basis1Amp_eq_basisState]
    exact eval_coinGatesAmp32 orthCoin10Gates basis1Amp validCoinGatesBasis1
  have heq : coinCol1Amp = basis0Amp := funext fun c ↦
    of_decide_eq_true (List.all_eq_true.mp coinCol1Amp_eq_basis0_ok c (List.mem_finRange c))
  rw [h1, heq, basis0Amp_eq_basisState]

theorem normSqAmp32Val_of_eq (p : ℤ × ℤ) (w : ℕ)
    (horth : p.1 * p.2 = 0) (hw : p.1 * p.1 + 2 * (p.2 * p.2) = (w : ℤ)) :
    Complex.normSq (amp32Val p) = (w : ℝ) / 1024 := by
  dsimp only [amp32Val]; rw [Complex.normSq_ofReal]
  have hsq : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have ho : (p.1 : ℝ) * (p.2 : ℝ) = 0 := by exact_mod_cast horth
  have hwr : (p.1 : ℝ) * (p.1 : ℝ) + 2 * ((p.2 : ℝ) * (p.2 : ℝ)) = (w : ℝ) := by
    exact_mod_cast hw
  calc (((p.1 : ℝ) + (p.2 : ℝ) * √2) / 32) * (((p.1 : ℝ) + (p.2 : ℝ) * √2) / 32)
      = ((p.1 : ℝ) * (p.1 : ℝ) + (p.2 : ℝ) * (p.2 : ℝ) * (√2 * √2) +
          2 * ((p.1 : ℝ) * (p.2 : ℝ)) * √2) / 1024 := by ring
    _ = (w : ℝ) / 1024 := by rw [hsq, ho]; linarith

theorem orthCoin10Unitary_col_zero_normSq (c : Fin (2 ^ 4)) :
    Complex.normSq (orthCoin10Unitary.1 c 0) = (coin10Weight c : ℝ) / 1024 := by
  have h0 : orthCoin10Unitary.1 c 0 = (orthCoin10Unitary.1 *ᵥ basisState 0) c := by
    simp [basisState]
  have hc := of_decide_eq_true
    (List.all_eq_true.mp coinCol0Amp_weight_ok c (List.mem_finRange c))
  rw [h0, orthCoin10_mulVec_zero_eq, evalAmp32_apply]
  exact normSqAmp32Val_of_eq (coinCol0Amp c) (coin10Weight c) hc.1 hc.2

theorem orthCoin10Unitary_zero_zero : orthCoin10Unitary.1 0 0 = 0 := by
  have h0 : orthCoin10Unitary.1 0 0 = (orthCoin10Unitary.1 *ᵥ basisState 0) 0 := by
    simp [basisState]
  have hz : coinCol0Amp 0 = (0, 0) := of_decide_eq_true coinCol0Amp_zero_ok
  rw [h0, orthCoin10_mulVec_zero_eq, evalAmp32_apply, hz]
  simp [amp32Val]

theorem jAux4_eq_one : StepOuter8Pi145L1.jAux4 = (1 : Fin (2 ^ 4)) := by
  apply (basisBits 4).injective
  rw [StepOuter8Pi145L1.jAux4, Equiv.apply_symm_apply]
  funext j; fin_cases j <;> decide

theorem orthCoin10Unitary_col_jAux4 (c : Fin (2 ^ 4)) :
    orthCoin10Unitary.1 c StepOuter8Pi145L1.jAux4 = if c = 0 then 1 else 0 := by
  rw [jAux4_eq_one]
  have h1 : orthCoin10Unitary.1 c 1 = (orthCoin10Unitary.1 *ᵥ basisState 1) c := by
    simp [basisState]
  rw [h1, orthCoin10_mulVec_one_eq]
  by_cases hc : c = 0 <;> simp [hc, basisState]

attribute [irreducible] orthCoin10Unitary orthCoin10Dyn orthCoin10InvDyn

/-! ### `10`-AND Reversible Packet Multiplexer (`pktMux10Rev2`, `pKeepMux25_2`) -/

private def pktSum16 (k : Fin 10 → ZMod 2) : ℕ :=
  let f (c : Fin 16) : ℕ :=
    if 1 + pktKeepSel10 k (basisBits 4 c) = 0 then coin10Weight c else 0
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +
    (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + f 15))))))))))))))

private lemma pktSum16_eq_val_all :
    (List.finRange 1024).all (fun keep : Fin 1024 ↦
      decide (pktSum16 (basisBits 10 keep) = keep.val)) = true := by decide +kernel

private lemma sum_fin16_eq (f : Fin 16 → ℕ) : (∑ c : Fin 16, f c) =
    f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +
      (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + f 15)))))))))))))) := by
  have huniv : (Finset.univ : Finset (Fin 16)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by decide
  rw [huniv]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

theorem sumCoin10Weight_keep (keep : Fin 1024) :
    (∑ c : Fin 16, if pktSwapBit10 keep c = 0 then coin10Weight c else 0) = keep.val := by
  rw [sum_fin16_eq]
  exact of_decide_eq_true (List.all_eq_true.mp pktSum16_eq_val_all keep (List.mem_finRange keep))

theorem sumCoin10Weight_swap (keep : Fin 1024) :
    (∑ c : Fin 16, if pktSwapBit10 keep c ≠ 0 then coin10Weight c else 0) =
      1024 - keep.val := by
  have htot : (∑ c : Fin 16, if pktSwapBit10 keep c = 0 then coin10Weight c else 0) +
      (∑ c : Fin 16, if pktSwapBit10 keep c ≠ 0 then coin10Weight c else 0) = 1024 := by
    rw [← Finset.sum_add_distrib]
    have hpt (c : Fin 16) :
        (if pktSwapBit10 keep c = 0 then coin10Weight c else 0) +
          (if pktSwapBit10 keep c ≠ 0 then coin10Weight c else 0) = coin10Weight c := by
      by_cases h : pktSwapBit10 keep c = 0 <;> simp [h]
    simp only [hpt]
    exact sumCoin10Weight
  rw [sumCoin10Weight_keep] at htot
  omega

/-- `10`-AND reversible `pktKeepSel10` multiplexer writing `mk` into wire `off + 76`. -/
def pktMux10Rev2 {N : ℕ} (off : ℕ) (h12 : 12 ≤ off) (hN : off + 77 ≤ N) :
    GroupUnary.RevCompute N :=
  let kp (i : Fin 10) : Wire N := ⟨off + 50 + i.val, by omega⟩
  let q (j : Fin 4) : Wire N := ⟨8 + j.val, by omega⟩
  let u (m : Fin 10) : Wire N := ⟨off + 67 + m.val, by omega⟩
  have hkp_ne (i1 i2 : Fin 10) (h : i1 ≠ i2) : kp i1 ≠ kp i2 :=
    fun he ↦ h (Fin.ext (by have hv := congrArg Fin.val he; dsimp [kp] at hv; omega))
  have hq_kp (j : Fin 4) (i : Fin 10) : q j ≠ kp i :=
    fun he ↦ by have hv := congrArg Fin.val he; dsimp [q, kp] at hv; omega
  have hq_u (j : Fin 4) (m : Fin 10) : q j ≠ u m :=
    fun he ↦ by have hv := congrArg Fin.val he; dsimp [q, u] at hv; omega
  have hkp_u (i : Fin 10) (m : Fin 10) : kp i ≠ u m :=
    fun he ↦ by have hv := congrArg Fin.val he; dsimp [kp, u] at hv; omega
  have hu_ne (m1 m2 : Fin 10) (h : m1 ≠ m2) : u m1 ≠ u m2 :=
    fun he ↦ h (Fin.ext (by have hv := congrArg Fin.val he; dsimp [u] at hv; omega))
  .seq (mux2Rev (q 1) (kp 2) (kp 7) (u 0) (hkp_ne 2 7 (by decide)) (hq_kp 1 7) (hq_u 1 0)
        (hkp_u 7 0) (hkp_u 2 0))
    (.seq (mux2Rev (q 1) (kp 6) (kp 3) (u 1) (hkp_ne 6 3 (by decide)) (hq_kp 1 3) (hq_u 1 1)
          (hkp_u 3 1) (hkp_u 6 1))
      (.seq (mux2Rev (q 1) (kp 8) (kp 4) (u 2) (hkp_ne 8 4 (by decide)) (hq_kp 1 4) (hq_u 1 2)
            (hkp_u 4 2) (hkp_u 8 2))
        (.seq (notAndRev (q 1) (kp 0) (u 3) (hq_kp 1 0) (hq_u 1 3) (hkp_u 0 3))
          (.seq (mux2Rev (q 0) (u 1) (u 2) (u 4) (hu_ne 1 2 (by decide)) (hq_u 0 2) (hq_u 0 4)
                (hu_ne 2 4 (by decide)) (hu_ne 1 4 (by decide)))
            (.seq (mux2Rev (q 0) (kp 9) (kp 5) (u 5) (hkp_ne 9 5 (by decide)) (hq_kp 0 5)
                  (hq_u 0 5) (hkp_u 5 5) (hkp_u 9 5))
              (.seq (mux2Rev (q 0) (kp 1) (u 3) (u 6) (hkp_u 1 3) (hq_u 0 3) (hq_u 0 6)
                    (hu_ne 3 6 (by decide)) (hkp_u 1 6))
                (.seq (mux2Rev (q 2) (u 0) (u 4) (u 7) (hu_ne 0 4 (by decide)) (hq_u 2 4)
                      (hq_u 2 7) (hu_ne 4 7 (by decide)) (hu_ne 0 7 (by decide)))
                  (.seq (mux2Rev (q 2) (u 5) (u 6) (u 8) (hu_ne 5 6 (by decide)) (hq_u 2 6)
                        (hq_u 2 8) (hu_ne 6 8 (by decide)) (hu_ne 5 8 (by decide)))
                    (mux2Rev (q 3) (u 7) (u 8) (u 9) (hu_ne 7 8 (by decide)) (hq_u 3 8)
                      (hq_u 3 9) (hu_ne 8 9 (by decide)) (hu_ne 7 9 (by decide)))))))))))

@[simp]
theorem numAndPktMux10Rev {N : ℕ} (off : ℕ) (h12 : 12 ≤ off) (hN : off + 77 ≤ N) :
    (pktMux10Rev2 off h12 hN).numAnd = 10 := rfl

/-- `25`-AND (`100 T`, `0 TOFF`) reversible `keep:10 + pktMux10Rev2` program on `off..off + 76`. -/
def pKeepMux25_2 {N : ℕ} (outerTable : Fin 184 → OuterWeights.AliasEntry 184)
    (off : ℕ) (h12 : 12 ≤ off) (hN : off + 77 ≤ N) : GroupUnary.RevCompute N :=
  have hHotScr : (QRegister.block (n := N) off 46 (by omega)).DisjointWires
      (QRegister.block (n := N) (off + 50) 17 (by omega)) :=
    QRegister.block_disjoint_of_le (n := N) off 46 (off + 50) 17 (by omega) (by omega) (by omega)
  .seq
    (DyadicXMeasPrepOut13.pairedLac4Loop
      (QRegister.block off 46 (by omega)) ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨off + 46, by omega⟩
      (QRegister.block (off + 50) 17 (by omega)) hHotScr
      (fun j h ↦ by have hv := congrArg Fin.val h; simp at hv; omega)
      (fun j h ↦ by have hv := congrArg Fin.val h; simp at hv; omega)
      (fun j h ↦ by have hv := congrArg Fin.val h; simp at hv; omega)
      (DyadicXMeasPrepOut13.keepColBool outerTable) 5 le_rfl)
    (pktMux10Rev2 off h12 hN)

@[simp]
theorem numAndPKeepMux25 {N : ℕ} (outerTable : Fin 184 → OuterWeights.AliasEntry 184)
    (off : ℕ) (h12 : 12 ≤ off) (hN : off + 77 ≤ N) :
    (pKeepMux25_2 outerTable off h12 hN).numAnd = 25 := by
  simp [pKeepMux25_2, GroupUnary.RevCompute.numAnd]

/-! ### `pi145OuterTable` Weight, Sign, Coset-`16` & Affine-`alt` Theorems -/

/-! ### Exact Support-Disjoint Column-`0` `L¹` Identity & `checkOrthGrover184L1Word_sound` -/

/-- Exact column-`0` `L¹` probability deviation `2 * (1 - p) * (1 - 4 * p) ^ 2` for `orthCoin10`
paired with `1`-round Grover-`184` (`p = (23 / 32) * |W_{0,0}|²`). -/
def orthGrover184L1Exact (W : Unitary 2) : ℝ :=
  let p : ℝ := (23 : ℝ) / 32 * Complex.normSq (W.1 0 0)
  2 * (1 - p) * (1 - 4 * p) ^ 2

theorem sum_normSqOrthCoin10_sub_eq (α₀ α₁ β₀ : ℂ) :
    (∑ c : Fin (2 ^ 4),
      |Complex.normSq (α₀ * orthCoin10Unitary.1 c 0 +
          α₁ * orthCoin10Unitary.1 c StepOuter8Pi145L1.jAux4) -
        Complex.normSq (β₀ * orthCoin10Unitary.1 c 0)|) =
      |Complex.normSq α₀ - Complex.normSq β₀| + Complex.normSq α₁ := by
  let C := orthCoin10Unitary
  rw [(Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ 4)))).symm]
  have hc0 : |Complex.normSq (α₀ * C.1 0 0 + α₁ * C.1 0 StepOuter8Pi145L1.jAux4) -
      Complex.normSq (β₀ * C.1 0 0)| = Complex.normSq α₁ := by
    rw [orthCoin10Unitary_zero_zero, orthCoin10Unitary_col_jAux4 0, ite_eq_left rfl,
      mul_zero, zero_add, mul_one, mul_zero, Complex.normSq_zero, sub_zero,
      abs_of_nonneg (Complex.normSq_nonneg α₁)]
  have hrest (c : Fin (2 ^ 4)) (hc : c ∈ Finset.univ.erase 0) :
      |Complex.normSq (α₀ * C.1 c 0 + α₁ * C.1 c StepOuter8Pi145L1.jAux4) -
        Complex.normSq (β₀ * C.1 c 0)| =
      |Complex.normSq α₀ - Complex.normSq β₀| * Complex.normSq (C.1 c 0) := by
    have hne : c ≠ 0 := (Finset.mem_erase.mp hc).1
    rw [orthCoin10Unitary_col_jAux4 c, ite_eq_right hne, mul_zero, add_zero,
      map_mul, map_mul, ← sub_mul, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
  have hsum_erase : (∑ c ∈ Finset.univ.erase (0 : Fin (2 ^ 4)), Complex.normSq (C.1 c 0)) = 1 := by
    have htot := StepOuter8Pi145L1.sum_normSq_unitary_col0 C
    rw [(Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ 4)))).symm,
      orthCoin10Unitary_zero_zero, Complex.normSq_zero, zero_add] at htot
    exact htot
  rw [hc0, Finset.sum_congr rfl hrest, ← Finset.mul_sum, hsum_erase, mul_one, add_comm]

theorem sum_256_grover184OrthCoin10_sub_eq (W W_id : Unitary 2)
    (hWid : Complex.normSq (W_id.1 0 0) = 8 / 23) :
    let u₁ := prepGroverUnitary 3 5 23 W
    let u₂ := prepGroverUnitary 3 5 23 W_id
    (∑ x : Fin 256, ∑ c : Fin (2 ^ 4),
      |Complex.normSq (u₁.1 ⟨x.val, by omega⟩ 0 * orthCoin10Unitary.1 c 0 +
          u₁.1 ⟨x.val + 256, by omega⟩ 0 * orthCoin10Unitary.1 c StepOuter8Pi145L1.jAux4) -
        Complex.normSq (u₂.1 ⟨x.val, by omega⟩ 0 * orthCoin10Unitary.1 c 0 +
          u₂.1 ⟨x.val + 256, by omega⟩ 0 * orthCoin10Unitary.1 c StepOuter8Pi145L1.jAux4)|) =
      orthGrover184L1Exact W := by
  intro u₁ u₂
  have hcol_eq (U : Unitary (2 ^ (3 + 5 + 1))) (j : Fin (2 ^ (3 + 5 + 1))) :
      U.1 j 0 = (U.1 *ᵥ Pi.single 0 1) j := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  have hp_id : ((23 : ℕ) : ℝ) / (2 ^ 5 : ℝ) * Complex.normSq (W_id.1 0 0) = 1 / 4 := by
    rw [hWid]; norm_num
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpow8 : ((1 / √2 : ℝ) ^ (3 + 5) : ℝ) = 1 / 16 := by
    have h8 : (3 + 5 : ℕ) = 2 * 4 := rfl
    rw [h8, pow_mul, div_pow, one_pow, hs2_sq]; norm_num
  have hu2_hi (x : Fin 256) : u₂.1 ⟨x.val + 256, by omega⟩ 0 = 0 := by
    rw [hcol_eq]
    have h := prepGroverUnitary_mulVec_zero_of_ge_two_pow 3 5 23 (by decide) W_id
      ⟨x.val + 256, by omega⟩ (by dsimp; omega)
    dsimp only at h; rw [h, hp_id]; norm_num
  have hu2_good (x : Fin 256) (hx : x.val < 184) :
      Complex.normSq (u₂.1 ⟨x.val, by omega⟩ 0) = 1 / 184 := by
    rw [hcol_eq, prepGroverUnitary_mulVec_zero_of_lt 3 5 23 (by decide) W_id
      ⟨x.val, by omega⟩ (by dsimp; omega)]
    dsimp only [prepGoodAmp]
    rw [hp_id, hpow8, map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, hWid]
    norm_num
  have hu2_bad (x : Fin 256) (hx : ¬ x.val < 184) : u₂.1 ⟨x.val, by omega⟩ 0 = 0 := by
    rw [hcol_eq]
    have h := prepGroverUnitary_mulVec_zero_of_mid 3 5 23 (by decide) W_id
      ⟨x.val, by omega⟩ (by dsimp; omega) (by dsimp; exact x.isLt)
    dsimp only at h; rw [h, hp_id]; norm_num
  let q := Complex.normSq (W.1 0 0)
  let p : ℝ := (23 : ℝ) / 32 * q
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hq1_eq : Complex.normSq (W.1 1 0) = 1 - q := by
    linarith [unitary2_normSq_col0_sum W]
  have hq_le1 : q ≤ 1 := by
    linarith [unitary2_normSq_col0_sum W, Complex.normSq_nonneg (W.1 1 0)]
  have hp_le : p ≤ 23 / 32 := by dsimp [p]; linarith
  have h1p_pos : 0 ≤ 1 - p := by linarith
  have hp_eq : ((23 : ℕ) : ℝ) / (2 ^ 5 : ℝ) * Complex.normSq (W.1 0 0) = p := by
    dsimp [p, q]; norm_num
  have hu1_hi (x : Fin 256) :
      u₁.1 ⟨x.val + 256, by omega⟩ 0 = ((1 - 4 * p) / 16 : ℝ) * W.1 1 0 := by
    rw [hcol_eq]
    have h := prepGroverUnitary_mulVec_zero_of_ge_two_pow 3 5 23 (by decide) W
      ⟨x.val + 256, by omega⟩ (by dsimp; omega)
    dsimp only at h; rw [h, hp_eq, hpow8]; push_cast; ring
  let bGood : ℝ := |Complex.normSq (((3 - 4 * p) / 16 : ℝ) * W.1 0 0) - 1 / 184| +
      Complex.normSq (((1 - 4 * p) / 16 : ℝ) * W.1 1 0)
  let bBad : ℝ := |Complex.normSq (((1 - 4 * p) / 16 : ℝ) * W.1 0 0) - 0| +
      Complex.normSq (((1 - 4 * p) / 16 : ℝ) * W.1 1 0)
  have hx_eq (x : Fin 256) :
      (∑ c : Fin (2 ^ 4),
        |Complex.normSq (u₁.1 ⟨x.val, by omega⟩ 0 * orthCoin10Unitary.1 c 0 +
            u₁.1 ⟨x.val + 256, by omega⟩ 0 * orthCoin10Unitary.1 c StepOuter8Pi145L1.jAux4) -
          Complex.normSq (u₂.1 ⟨x.val, by omega⟩ 0 * orthCoin10Unitary.1 c 0 +
            u₂.1 ⟨x.val + 256, by omega⟩ 0 * orthCoin10Unitary.1 c StepOuter8Pi145L1.jAux4)|) =
      if x.val < 184 then bGood else bBad := by
    simp only [hu2_hi x, zero_mul, add_zero, sum_normSqOrthCoin10_sub_eq, hu1_hi x]
    by_cases hx : x.val < 184
    · rw [ite_eq_left hx, hu2_good x hx]
      have hu1_lo : u₁.1 ⟨x.val, by omega⟩ 0 = ((3 - 4 * p) / 16 : ℝ) * W.1 0 0 := by
        rw [hcol_eq, prepGroverUnitary_mulVec_zero_of_lt 3 5 23 (by decide) W
          ⟨x.val, by omega⟩ (by dsimp; omega)]
        dsimp only [prepGoodAmp]; rw [hp_eq, hpow8]; push_cast; ring
      rw [hu1_lo]
    · rw [ite_eq_right hx, hu2_bad x hx, Complex.normSq_zero]
      have hu1_lo : u₁.1 ⟨x.val, by omega⟩ 0 = ((1 - 4 * p) / 16 : ℝ) * W.1 0 0 := by
        rw [hcol_eq]
        have h := prepGroverUnitary_mulVec_zero_of_mid 3 5 23 (by decide) W
          ⟨x.val, by omega⟩ (by dsimp; omega) (by dsimp; exact x.isLt)
        dsimp only at h; rw [h, hp_eq, hpow8]; push_cast; ring
      rw [hu1_lo]
  simp_rw [hx_eq]
  have hsum_ite : (∑ x : Fin 256, if x.val < 184 then bGood else bBad) =
      184 * bGood + 72 * bBad := by
    let e : Fin (184 + 72) ≃ Fin 256 := finCongr (by decide)
    rw [← e.sum_comp, Fin.sum_univ_add]
    have h1 : (∑ i : Fin 184, if (e (Fin.castAdd 72 i)).val < 184 then bGood else bBad) =
        184 * bGood := by
      have hi : ∀ i : Fin 184, (e (Fin.castAdd 72 i)).val < 184 := fun i ↦ by
        simp [e, Fin.castAdd]
      simp [hi]
    have h2 : (∑ j : Fin 72, if (e (Fin.natAdd 184 j)).val < 184 then bGood else bBad) =
        72 * bBad := by
      have hj : ∀ j : Fin 72, ¬ (e (Fin.natAdd 184 j)).val < 184 := fun j ↦ by
        simp [e, Fin.natAdd]
      simp [hj]
    rw [h1, h2]
  rw [hsum_ite]
  have hn_good : |Complex.normSq (((3 - 4 * p) / 16 : ℝ) * W.1 0 0) - 1 / 184| =
      ((1 - p) * (1 - 4 * p) ^ 2) / 184 := by
    rw [map_mul, Complex.normSq_ofReal, ← sq]
    have hid : ((3 - 4 * p) / 16) ^ 2 * q - 1 / 184 = -(((1 - p) * (1 - 4 * p) ^ 2) / 184) := by
      dsimp [p, q]; ring
    rw [hid, abs_neg, abs_of_nonneg (by positivity)]
  have hn_bad : |Complex.normSq (((1 - 4 * p) / 16 : ℝ) * W.1 0 0) - 0| =
      ((1 - 4 * p) / 16) ^ 2 * q := by
    rw [sub_zero, map_mul, Complex.normSq_ofReal, ← sq, abs_of_nonneg (by positivity)]
  have hn_hi : Complex.normSq (((1 - 4 * p) / 16 : ℝ) * W.1 1 0) =
      ((1 - 4 * p) / 16) ^ 2 * (1 - q) := by
    rw [map_mul, Complex.normSq_ofReal, ← sq, hq1_eq]
  dsimp only [bGood, bBad, orthGrover184L1Exact]
  rw [hn_good, hn_bad, hn_hi]
  dsimp only [p, q]
  ring

theorem sum_abs_normSq_wouter8OrthCoin10_postPerm_eq
    (rG9 : QRegister 9 17) (rK4 : QRegister 4 17) (wSpin17 : Wire 17)
    (hrG9_lo : ∀ i : Fin 8, rG9 ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩)
    (hrG9_8 : rG9 8 = ⟨12, by decide⟩)
    (hrK4 : ∀ j : Fin 4, rK4 j = ⟨12 + j.val, by omega⟩)
    (hwSpin : wSpin17 = ⟨16, by decide⟩)
    (uPost : Unitary (2 ^ 17)) (fPost : BitAssignment 17 → BitAssignment 17)
    (hfPost : Function.Injective fPost)
    (huPost : ∀ γ : BitAssignment 17,
      uPost.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (fPost γ))
    (W W_id : Unitary 2) (hWid : Complex.normSq (W_id.1 0 0) = 8 / 23) :
    let U₁ := uPost * (rK4.embedUnitary orthCoin10Unitary * (Circuit.H wSpin17).eval *
      rG9.embedUnitary (prepGroverUnitary 3 5 23 W))
    let U₂ := uPost * (rK4.embedUnitary orthCoin10Unitary * (Circuit.H wSpin17).eval *
      rG9.embedUnitary (prepGroverUnitary 3 5 23 W_id))
    (∑ o : Fin (2 ^ 17), |Complex.normSq (U₁.1 o 0) - Complex.normSq (U₂.1 o 0)|) =
      orthGrover184L1Exact W := by
  intro U₁ U₂
  let u₁ := prepGroverUnitary 3 5 23 W
  let u₂ := prepGroverUnitary 3 5 23 W_id
  let idx : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → Fin (2 ^ 17) := fun t ↦
    (basisBits 17).symm (fPost (inBits17 t.1 t.2.1 t.2.2))
  have hidx : Function.Injective idx :=
    (basisBits 17).symm.injective.comp (hfPost.comp inBits17_injective)
  let amp₁ : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → ℂ := fun t ↦
    (u₁.1 (lo512 t.1) 0 * orthCoin10Unitary.1 t.2.2 0 +
      u₁.1 (hi512 t.1) 0 * orthCoin10Unitary.1 t.2.2 jAux4) * SelectSwapQROM.sqrtHalf
  let amp₂ : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → ℂ := fun t ↦
    (u₂.1 (lo512 t.1) 0 * orthCoin10Unitary.1 t.2.2 0 +
      u₂.1 (hi512 t.1) 0 * orthCoin10Unitary.1 t.2.2 jAux4) * SelectSwapQROM.sqrtHalf
  have hv₁ := wouter8InitPost_col0 rG9 rK4 wSpin17 hrG9_lo hrG9_8 hrK4 hwSpin orthCoin10Unitary
    uPost fPost huPost u₁
  have hv₂ := wouter8InitPost_col0 rG9 rK4 wSpin17 hrG9_lo hrG9_8 hrK4 hwSpin orthCoin10Unitary
    uPost fPost huPost u₂
  rw [sum_abs_normSq_sub_of_injective idx hidx amp₁ amp₂ _ _ hv₁ hv₂, Fintype.sum_prod_type]
  have hns_half : Complex.normSq SelectSwapQROM.sqrtHalf = 1 / 2 := by
    dsimp [SelectSwapQROM.sqrtHalf]
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  have hspin (x : Fin (2 ^ 8)) :
      (∑ sc : Fin 2 × Fin (2 ^ 4),
          |Complex.normSq (amp₁ (x, sc)) - Complex.normSq (amp₂ (x, sc))|) =
        ∑ c : Fin (2 ^ 4),
          |Complex.normSq (u₁.1 (lo512 x) 0 * orthCoin10Unitary.1 c 0 +
              u₁.1 (hi512 x) 0 * orthCoin10Unitary.1 c jAux4) -
            Complex.normSq (u₂.1 (lo512 x) 0 * orthCoin10Unitary.1 c 0 +
              u₂.1 (hi512 x) 0 * orthCoin10Unitary.1 c jAux4)| := by
    have habs_half : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [amp₁, amp₂]
    rw [map_mul, map_mul, hns_half, ← sub_mul, abs_mul, habs_half]
    ring
  simp_rw [hspin]
  exact sum_256_grover184OrthCoin10_sub_eq W W_id hWid

theorem checkOrthGrover184L1Word_sound {tExpected epsNum epsDen : ℕ} {w : List Gate1}
    (hok : checkOrthGrover184L1Word tExpected epsNum epsDen w = true) :
    (wordToCircuit1 w).count PrimitiveGate.T = tExpected ∧
      orthGrover184L1Exact (wordToCircuit1 w).eval ≤ (epsNum : ℝ) / (epsDen : ℝ) := by
  dsimp only [checkOrthGrover184L1Word] at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  rcases hok with ⟨ht, hepsD, hboundB⟩
  rw [wordCountT_eq] at ht
  refine ⟨ht, ?_⟩
  set M := evalWordCyc w
  set W := (wordToCircuit1 w).eval
  have hW0 : W.1 0 0 = (((1 / √2 : ℝ) ^ M.k : ℝ) : ℂ) * M.a.toComplex := by
    have hm := congrFun (congrFun (evalWordCyc_toMatrix w) 0) 0
    dsimp only [M, W] at hm ⊢
    rw [← hm, CycMat2.toMatrix]
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, smul_eq_mul]
    congr 1; push_cast; rfl
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpow_sq : ((1 / √2 : ℝ) ^ M.k) ^ 2 = 1 / (2 ^ M.k : ℝ) := by
    rw [← pow_mul, mul_comm M.k 2, pow_mul, div_pow, one_pow, hs2_sq, _root_.one_div_pow]
  set D : ℕ := 2 ^ M.k
  have hDR : (D : ℝ) = (2 ^ M.k : ℝ) := by simp [D]
  have hDpos : (0 : ℝ) < (D : ℝ) := by rw [hDR]; positivity
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hnormW : Complex.normSq (W.1 0 0) = M.a.normSqZ2.toReal / (D : ℝ) := by
    rw [hW0, map_mul, Complex.normSq_ofReal, ← sq, hpow_sq, ← Cyc8.normSqZ2_toReal, hDR]; ring
  set qZ2 := M.a.normSqZ2
  have hq_eq : qZ2.toReal = (D : ℝ) * Complex.normSq (W.1 0 0) := by
    rw [hnormW]; field_simp [hDne]
  have hge := Z2.toReal_nonneg_of_geZero hboundB
  simp only [Z2.toReal_sub, Z2.toReal_ofNat, Z2.toReal_scaleNat, Z2.toReal_mul, hq_eq,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hge
  have hepsD_pos : (0 : ℝ) < (epsDen : ℝ) := Nat.cast_pos.mpr hepsD
  have hscale_pos : (0 : ℝ) < (epsDen : ℝ) * (1024 * (D : ℝ) ^ 3) := by positivity
  have hmul_le : orthGrover184L1Exact W * ((epsDen : ℝ) * (1024 * (D : ℝ) ^ 3)) ≤
      ((epsNum : ℝ) / (epsDen : ℝ)) * ((epsDen : ℝ) * (1024 * (D : ℝ) ^ 3)) := by
    have hcel : ((epsNum : ℝ) / (epsDen : ℝ)) * ((epsDen : ℝ) * (1024 * (D : ℝ) ^ 3)) =
        (epsNum : ℝ) * 1024 * (D : ℝ) ^ 3 := by
      field_simp [ne_of_gt hepsD_pos]
    rw [hcel]
    dsimp only [orthGrover184L1Exact] at hge ⊢
    linarith
  exact le_of_mul_le_mul_right hmul_le hscale_pos

attribute [irreducible] orthCoin10Circuit orthCoin10InvCircuit

end

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Pi145Fast2RotCore

end

/-!
# `wOuter = 8` (`kZeroOut = 4`) ANF-Reduced `2`-Rotation Outer `PREP` (`666 / 654 / 618 T/Refl2`)

Constructs an MILP-optimized zero-shear `π145` alias table
`pi145CompactTable` (`keep < 1024`, preserving `pi145Perm` and `pi145WeightNat`) whose
retained `alt` bits `[2, 3, 6, 7]` satisfy four simultaneous `4`-item group ANF constraints across
all `46` groups (`y = 4 * g + r < 184`):
1. `alt` bit `7` is group-constant (`0` ANDs),
2. `alt` bit `3` is group-constant (`0` ANDs),
3. `alt` bit `6` is `x₁`-affine (`1` AND), and
4. `alt` bit `2` has zero quadratic `x₀ * x₁` ANF term (`c₃ = 0`), computable in `1` AND gate using
   the identity `(b₂ + x₀) * (b₁ + x₁) + s₀₁ + (b₀ + b₁ * b₂) = b₀ + x₀ * b₁ + x₁ * b₂` (`ZMod 2`)
   with `s₀₁ = x₀ * x₁` already produced by `wHot46FwdDyn`.

Using forward QROM `preSwap103Dyn` (`210 T`, `87` scratch) and backward X-measurement phase leaf
`leaf94Dyn` (`202 T`, `82` scratch), the outer state-preparation gate counts are:
* Forward `PREP_out`: `(52 + 3 * wordCountT) + 210 + 24 = 286 + 3 * wordCountT` `T`, `0 TOFF`.
* Backward `PREP_out†`: `24 + 202 + (52 + 3 * wordCountT) = 278 + 3 * wordCountT` `T`, `0 TOFF`.
* `Word17`: `337 + 329 = 666 T/Refl2`, `εOut_L1 ≤ 24 / 10 ^ 11` (`δH_out = 0.045 µHa`).
* `Word15`: `331 + 323 = 654 T/Refl2`, `εOut_L1 ≤ 56 / 10 ^ 10` (`δH_out = 1.082 µHa`).
* `Word9`: `313 + 305 = 618 T/Refl2`, `εOut_L1 ≤ 101 / 10 ^ 8` (`δH_out = 196.0 µHa`).

## References
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: 10.22331/q-2018-06-18-74.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, *Quantum* **3**, 208 (2019),
  DOI: 10.22331/q-2019-12-02-208.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024), arXiv:1812.00954.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Compact2RotDyn
open QuantumComputation.Specs QuantumComputation.Specs.P450

/-! ## Section 0: Computable ANF-Reduced `π145` Alias Table & Kernel Certificates -/

section ComputableCerts

open Circuit
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CoherentAlias
open Solution.OptU2Grover184PrepOut13
open Solution.OuterWeights.GroverUniform
open Solution.StepOuter8Pi145Outer

/-- Slice `0` of `pi145CompactPacked` (`62` entries). -/
def pi145CompactPart0 : List ℕ :=
  [261900, 240905, 12558, 261899, 214796, 258573, 27150, 260623, 157772, 261965, 76814, 4367,
    55808, 8193, 261890, 65539, 261968, 59729, 228946, 26963, 645780, 197265, 236182, 784787,
    13328, 46097, 237078, 183063, 80400, 222481, 124434, 161043, 252072, 64429, 665006, 220843,
    112484, 154213, 176482, 65891, 107172, 128417, 164770, 172967, 95840, 112997, 193058, 149799,
    786352, 27569, 2998, 779447, 241020, 5497, 120442, 97151, 627888, 167857, 232118, 677047,
    203312, 3125]

/-- Slice `1` of `pi145CompactPacked` (`62` entries). -/
def pi145CompactPart1 : List ℕ :=
  [23154, 33143, 233220, 233221, 157190, 107271, 129288, 184333, 78606, 169995, 142856, 215053,
    125710, 204811, 16896, 50689, 78914, 100675, 595092, 262033, 228498, 786327, 136784, 128593,
    134674, 68371, 112144, 101397, 173590, 57875, 614040, 611737, 120478, 133791, 33188, 222373,
    207782, 49831, 20768, 100641, 251234, 54627, 79392, 114977, 169058, 114787, 63584, 71009,
    136546, 137315, 42812, 251197, 786302, 54655, 23868, 105021, 175226, 262011, 24624, 112689,
    198962, 122675]

/-- Slice `2` of `pi145CompactPacked` (`60` entries). -/
def pi145CompactPart2 : List ℕ :=
  [108092, 261945, 469310, 199995, 375364, 833, 360774, 312131, 269888, 396609, 411458, 39747,
    265732, 288261, 5890, 355587, 380484, 108613, 366662, 120903, 313104, 111889, 261970, 384851,
    318480, 187153, 251730, 269139, 262160, 470549, 170070, 430419, 456216, 293145, 126494,
    181791, 305952, 47905, 245606, 130919, 231080, 26029, 770478, 164779, 32, 332833, 281186, 99,
    5540, 262049, 524198, 337571, 469368, 218493, 460666, 154495, 162420, 338289, 1394, 272247]

/-- Packed `184`-entry ANF-reduced zero-shear `wOuter = 8` (`kZeroOut = 4`) `π145` alias array. -/
def pi145CompactPacked : Array ℕ :=
  Array.mk (List.append pi145CompactPart0 (List.append pi145CompactPart1 pi145CompactPart2))

/-- ANF-reduced zero-shear `184`-item `10`-bit outer alias table (`keep < 1024`, `alt < 184`)
for `pi145Perm`. -/
def pi145CompactTable (i : Fin 184) : OuterWeights.AliasEntry 184 :=
  OuterWeights.unpackOuterEntry (pi145CompactPacked.getD i.val 0) i

theorem pi145CompactPacked_check :
    checkOuterPackedWeights pi145WeightFast pi145CompactPacked.toList = true := by
  decide +kernel

/-- Kernel check that every `y < 184` and `(pi145CompactTable y).alt` share bits `0, 1, 4, 5`. -/
def checkCompactCoset16 : Bool :=
  (List.finRange 184).all fun y ↦
    let av := (pi145CompactTable y).alt.val
    (av.testBit 0 == y.val.testBit 0) &&
      (av.testBit 1 == y.val.testBit 1) &&
      (av.testBit 4 == y.val.testBit 4) &&
      (av.testBit 5 == y.val.testBit 5)

theorem checkCompactCoset16_eq_true : checkCompactCoset16 = true := by
  decide +kernel

/-- Group-constant bit `7` of `(pi145CompactTable y).alt` on `4`-item group `g : Fin 46`. -/
def alt7Group (g : Fin 46) : Bool :=
  ((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 7

/-- Intercept (`x₁ = 0`) of bit `6` of `(pi145CompactTable y).alt` on group `g : Fin 46`. -/
def alt6Base (g : Fin 46) : Bool :=
  ((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 6

/-- `x₁`-slope (`b₆(4g) ⊕ b₆(4g + 2)`) of bit `6` of `alt` on group `g : Fin 46`. -/
def alt6Slope (g : Fin 46) : Bool :=
  xor (((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 6)
    (((pi145CompactTable ⟨4 * g.val + 2, by omega⟩).alt.val).testBit 6)

/-- Group-constant bit `3` of `(pi145CompactTable y).alt` on `4`-item group `g : Fin 46`. -/
def alt3Group (g : Fin 46) : Bool :=
  ((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 3

/-- Constant ANF term `b₂(4g)` of bit `2` of `(pi145CompactTable y).alt` on group `g : Fin 46`. -/
def alt2B0 (g : Fin 46) : Bool :=
  ((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 2

/-- `x₀`-slope `b₂(4g) ⊕ b₂(4g + 1)` of bit `2` of `alt` on group `g : Fin 46`. -/
def alt2B1 (g : Fin 46) : Bool :=
  xor (((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 2)
    (((pi145CompactTable ⟨4 * g.val + 1, by omega⟩).alt.val).testBit 2)

/-- `x₁`-slope `b₂(4g) ⊕ b₂(4g + 2)` of bit `2` of `alt` on group `g : Fin 46`. -/
def alt2B2 (g : Fin 46) : Bool :=
  xor (((pi145CompactTable ⟨4 * g.val, by omega⟩).alt.val).testBit 2)
    (((pi145CompactTable ⟨4 * g.val + 2, by omega⟩).alt.val).testBit 2)

/-- Kernel check that across all `y = 4 * g + r < 184`, `alt` bits `7, 3` are group-constant,
`alt` bit `6` is `x₁`-affine, and `alt` bit `2` has `c₃ = 0` (`b₀ ⊕ x₀ b₁ ⊕ x₁ b₂`). -/
def checkCompactAltAnf : Bool :=
  (List.finRange 184).all fun y ↦
    let g : Fin 46 := ⟨y.val / 4, by omega⟩
    let av := (pi145CompactTable y).alt.val
    let x0 := y.val.testBit 0
    let x1 := y.val.testBit 1
    (av.testBit 7 == alt7Group g) &&
      (av.testBit 6 == xor (alt6Base g) (x1 && alt6Slope g)) &&
      (av.testBit 3 == alt3Group g) &&
      (av.testBit 2 == xor (xor (alt2B0 g) (x0 && alt2B1 g)) (x1 && alt2B2 g))

theorem checkCompactAltAnf_eq_true : checkCompactAltAnf = true := by
  decide +kernel

end ComputableCerts

noncomputable section

open Operator QProg Matrix Circuit Real
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCore
open Solution.OuterWeights.GroverUniform
open Solution.Comparators hiding ket bit_cases matrix_ext_ket zeroProjOn
open Solution.SelectSwapQROM
open Solution.OptFactoredMag30AndCoin9
open Solution.ReordOuter13Bridge
open Solution.Phase2MidSandwich
open Solution.CompactZeroCmp20OuterParam
open Solution.CompactStepZeroCmp20OuterParam
open Solution.StepOuter8Pi145Outer
open Solution.StepOuter8Pi145L1
open Solution.Pi145Fast2RotCore
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowCompactDyn (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ### `pi145CompactTable` Weight, Sign & `ZMod 2` ANF Theorems -/

theorem pi145CompactTable_keep_lt (i : Fin 184) : (pi145CompactTable i).keep < 1024 :=
  Nat.mod_lt _ (by decide)

theorem pi145CompactTable_isValid :
    CoherentAlias.IsValidAliasTable 184 10 pi145WeightNat
      (fun i ↦ (pi145CompactTable i).alt)
      (fun i ↦ (pi145CompactTable i).keep) :=
  OptU2Grover184PrepOut13.isValidAliasTable_of_checkOuterPacked
    pi145CompactPacked pi145WeightFast pi145WeightNat pi145WeightFast_eq
    pi145CompactPacked_check

theorem pi145CompactTable_weight_eq (z : Fin 184) :
    (pi145CompactTable z).keep +
      (∑ y : Fin 184, if (pi145CompactTable y).alt = z then 1024 - (pi145CompactTable y).keep
        else 0) =
      outerWeightNatPerm pi145Per z := by
  have hv := pi145CompactTable_isValid.2 z
  rw [Finset.sum_add_distrib] at hv
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hv
  exact hv

attribute [irreducible] pi145CompactPacked

/-- Cast `(pi145CompactTable y).alt` from `Fin 184` into `Fin (2 ^ 8)`. -/
abbrev altFin256_2 (y : Fin 184) : Fin (2 ^ 8) :=
  ⟨(pi145CompactTable y).alt.val, by have := (pi145CompactTable y).alt.isLt; omega⟩

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem noC3_zmod2_id (x0 x1 : ZMod 2) (c0 c1 c2 : Bool) :
    ((b2z c2 + x0) * (b2z c1 + x1) + x0 * x1) + b2z (xor c0 (c1 && c2)) =
      b2z c0 + x0 * b2z c1 + x1 * b2z c2 := by
  rcases bit_cases x0 with rfl | rfl <;>
    rcases bit_cases x1 with rfl | rfl <;>
    cases c0 <;> cases c1 <;> cases c2 <;> decide

theorem alt_basisBits_eq (g : Fin 46) (x0 x1 : ZMod 2) :
    let rem := bit01Nat x0 + 2 * bit01Nat x1
    let y : Fin 184 := ⟨4 * g.val + rem, by
      have := g.isLt
      have := bit01Nat_le_one x0
      have := bit01Nat_le_one x1; omega⟩
    basisBits 8 (altFin256_2 y) 7 = b2z (alt7Group g) ∧
      basisBits 8 (altFin256_2 y) 6 = b2z (alt6Base g) + x1 * b2z (alt6Slope g) ∧
      basisBits 8 (altFin256_2 y) 3 = b2z (alt3Group g) ∧
      basisBits 8 (altFin256_2 y) 2 =
        b2z (alt2B0 g) + x0 * b2z (alt2B1 g) + x1 * b2z (alt2B2 g) := by
  intro rem y
  have hanf := List.all_eq_true.mp checkCompactAltAnf_eq_true y (List.mem_finRange y)
  simp only [Bool.and_eq_true, beq_iff_eq] at hanf
  rcases hanf with ⟨⟨⟨h7, h6⟩, h3⟩, h2⟩
  have hg : (⟨y.val / 4, by omega⟩ : Fin 46) = g := by
    ext; dsimp only [y, rem]
    have := bit01Nat_le_one x0; have := bit01Nat_le_one x1; omega
  rw [hg] at h7 h6 h3 h2
  have ht0 : y.val.testBit 0 = (x0 == 1) := by
    clear h7 h6 h3 h2 hg
    dsimp only [y, rem, bit01Nat]
    clear y rem; revert g
    rcases bit_cases x0 with rfl | rfl <;>
      rcases bit_cases x1 with rfl | rfl <;> decide
  have ht1 : y.val.testBit 1 = (x1 == 1) := by
    clear h7 h6 h3 h2 hg ht0
    dsimp only [y, rem, bit01Nat]
    clear y rem; revert g
    rcases bit_cases x0 with rfl | rfl <;>
      rcases bit_cases x1 with rfl | rfl <;> decide
  rw [ht1] at h6 h2
  rw [ht0] at h2
  rw [basisBits_eq_testBit, basisBits_eq_testBit, basisBits_eq_testBit, basisBits_eq_testBit]
  have hv7 : (7 : Fin 8).val = 7 := rfl
  have hv6 : (6 : Fin 8).val = 6 := rfl
  have hv3 : (3 : Fin 8).val = 3 := rfl
  have hv2 : (2 : Fin 8).val = 2 := rfl
  simp only [hv7, hv6, hv3, hv2, h7, h6, h3, h2]
  refine ⟨rfl, ?_, rfl, ?_⟩
  · rcases bit_cases x1 with rfl | rfl <;>
      cases alt6Base g <;> cases alt6Slope g <;> decide
  · rcases bit_cases x0 with rfl | rfl <;>
      rcases bit_cases x1 with rfl | rfl <;>
      cases alt2B0 g <;> cases alt2B1 g <;> cases alt2B2 g <;> decide

/-! ## Section 1: `52 + 3 * wordCountT` Support-Disjoint `13`-Wire Initializer -/

/-- `13`-qubit initial unitary on `nonAlt13Loc`: Grover-`184` on `0..8`, spin `H` on `12`, and
`20-T` support-disjoint `orthCoin10Unitary` on `8..11`. -/
def init13Unitary (uUnif9 : Unitary (2 ^ 9)) : Unitary (2 ^ 13) :=
  nonAltKReg.embedUnitary orthCoin10Unitary *
    (Circuit.H nonAltSpinWire).eval *
    nonAltXoAuxReg.embedUnitary uUnif9

/-- Fixed-width `17`-wire forward initial preparer (`13` active + `4` scratch,
`3 * wordCountT rotWord + 52` `T`, `0 TOFF`). -/
def init17WordLocDyn {Var : Type} (rotWord : List Gate1) (v : Var) : DynamicCircuit Var 17 :=
  let rAct13 : QRegister 13 17 := QRegister.block 0 13 (by decide)
  let rScr4 : QRegister 4 17 := QRegister.block 13 4 (by decide)
  .seq
    (placeWithScratchPrefix (m := 4)
      (OptU2Grover184PrepOut13.prepUnif184WordLocDyn rotWord v)
      (rAct13.compose nonAltXoAuxReg) rScr4)
    (.seq (.circuit (Circuit.H (rAct13 nonAltSpinWire)))
      (orthCoin10Dyn (rAct13.compose nonAltKReg)))

/-- Fixed-width `17`-wire inverse initial unpreparer (`13` active + `4` scratch,
`3 * wordCountT rotWord + 52` `T`, `0 TOFF`). -/
def uninit17WordLocDyn {Var : Type} (rotWord : List Gate1) (v : Var) : DynamicCircuit Var 17 :=
  let rAct13 : QRegister 13 17 := QRegister.block 0 13 (by decide)
  let rScr4 : QRegister 4 17 := QRegister.block 13 4 (by decide)
  .seq
    (orthCoin10InvDyn (rAct13.compose nonAltKReg))
    (.seq (.circuit (Circuit.H (rAct13 nonAltSpinWire)))
      (placeWithScratchPrefix (m := 4)
        (OptU2Grover184PrepOut13.unprepUnif184WordLocDyn rotWord v)
        (rAct13.compose nonAltXoAuxReg) rScr4))

@[simp]
theorem countInit17WordLocDyn_toff {Var : Type} (rotWord : List Gate1) (v : Var) :
    (init17WordLocDyn rotWord v).count .TOFF = 0 := by
  have hL : (OptU2Grover184PrepOut13.prepUnif184WordLocDyn rotWord v).count .TOFF = 0 :=
    count_prepGroverLocDyn_toff 3 5 4
      (count_groverStepFwdLocDyn_toff 5 4 rotWord
        (count_rGood23LocDyn_toff v) (count_sZero6LocDyn_toff v))
  have hH (q : Wire 17) : (Circuit.H q).count .TOFF = 0 := rfl
  dsimp only [init17WordLocDyn, DynamicCircuit.count]
  rw [count_placeWithScratchPrefix_toff (m := 4) hL, hH, countOrthCoin10Dyn_toff]

@[simp]
theorem countInit17WordLocDyn_t {Var : Type} (rotWord : List Gate1) (v : Var) :
    (init17WordLocDyn rotWord v).count .T = 3 * wordCountT rotWord + 52 := by
  have hH (q : Wire 17) : (Circuit.H q).count .T = 0 := rfl
  dsimp only [init17WordLocDyn, DynamicCircuit.count]
  rw [count_placeWithScratchPrefix_t_eq (m := 4) _ _ _ (by decide) (by decide),
    OptU2Grover184PrepOut13.prepUnif184WordLocDyn,
    count_prepGroverLocDyn_t, count_groverStepFwdLocDyn_t,
    ← wordCountT_eq, count_rGood23LocDyn_t, count_sZero6LocDyn_t, hH, countOrthCoin10Dyn_t]

@[simp]
theorem countUninit17WordLocDyn_toff {Var : Type} (rotWord : List Gate1) (v : Var) :
    (uninit17WordLocDyn rotWord v).count .TOFF = 0 := by
  have hL : (OptU2Grover184PrepOut13.unprepUnif184WordLocDyn rotWord v).count .TOFF = 0 :=
    count_unprepGroverLocDyn_toff 3 5 4
      (count_groverStepInvLocDyn_toff 5 4 rotWord
        (count_rGood23LocDyn_toff v) (count_sZero6LocDyn_toff v))
  have hH (q : Wire 17) : (Circuit.H q).count .TOFF = 0 := rfl
  dsimp only [uninit17WordLocDyn, DynamicCircuit.count]
  rw [countOrthCoin10InvDyn_toff, hH, count_placeWithScratchPrefix_toff (m := 4) hL]

@[simp]
theorem countUninit17WordLocDyn_t {Var : Type} (rotWord : List Gate1) (v : Var) :
    (uninit17WordLocDyn rotWord v).count .T = 3 * wordCountT rotWord + 52 := by
  have hH (q : Wire 17) : (Circuit.H q).count .T = 0 := rfl
  dsimp only [uninit17WordLocDyn, DynamicCircuit.count]
  rw [countOrthCoin10InvDyn_t, hH,
    count_placeWithScratchPrefix_t_eq (m := 4) _ _ _ (by decide) (by decide),
    OptU2Grover184PrepOut13.unprepUnif184WordLocDyn,
    count_unprepGroverLocDyn_t, count_groverStepInvLocDyn_t,
    ← wordCountT_eq, count_rGood23LocDyn_t, count_sZero6LocDyn_t]
  omega

theorem cleanRealizesInit17WordLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (rotWord : List Gate1) (v : Var) :
    Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 13 (by decide) : QRegister 13 17)
      (QRegister.block 13 4 (by decide) : QRegister 4 17)
      (init13Unitary (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord))
      (init17WordLocDyn rotWord v) := by
  let rAct13 : QRegister 13 17 := QRegister.block 0 13 (by decide)
  let rScr4 : QRegister 4 17 := QRegister.block 13 4 (by decide)
  have h1 := cr_lift_sub (cleanRealizes_placeWithScratchPrefix (m := 4) v
    (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord)
    (OptU2Grover184PrepOut13.prepUnif184WordLocDyn rotWord v)
    (rAct13.compose nonAltXoAuxReg) rScr4 (by decide) (by decide)
    (cleanRealizes_prepGroverLocDyn v 3 5 23 4 (wordToCircuit1 rotWord).eval _
      (cleanRealizes_groverStepFwdLocDyn v 5 23 4 rotWord _ _
        (cleanRealizes_rGood23LocDyn v) (cleanRealizes_sZero6LocDyn v))))
  have h2 : Solution.CleanDyn.CleanRealizes v rAct13 rScr4
      (Circuit.H nonAltSpinWire).eval (.circuit (Circuit.H (rAct13 nonAltSpinWire))) := by
    rw [show Circuit.H (rAct13 nonAltSpinWire) =
      (Circuit.H nonAltSpinWire).onRegister rAct13 from rfl]
    exact Solution.CleanDyn.CleanRealizes.circuit v rAct13 rScr4 (by decide)
      (Circuit.H nonAltSpinWire) rfl
  have h3 := cr_lift_sub (cleanRealizesOrthCoin10Dyn v
    (rAct13.compose nonAltKReg) rScr4 (by decide))
  refine (h1.seq (h2.seq h3)).congr_unitary ?_
  simp only [init13Unitary, mul_assoc]

theorem cleanRealizesUninit17WordLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (rotWord : List Gate1) (v : Var) :
    Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 13 (by decide) : QRegister 13 17)
      (QRegister.block 13 4 (by decide) : QRegister 4 17)
      (init13Unitary (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord))⁻¹
      (uninit17WordLocDyn rotWord v) := by
  let rAct13 : QRegister 13 17 := QRegister.block 0 13 (by decide)
  let rScr4 : QRegister 4 17 := QRegister.block 13 4 (by decide)
  have h1 := cr_lift_sub (cleanRealizesOrthCoin10InvDyn v
    (rAct13.compose nonAltKReg) rScr4 (by decide))
  have hH_inv : ((Circuit.H nonAltSpinWire).eval)⁻¹ = (Circuit.H nonAltSpinWire).eval := by
    rw [← Circuit.eval_inverse]; rfl
  have h2 : Solution.CleanDyn.CleanRealizes v rAct13 rScr4
      ((Circuit.H nonAltSpinWire).eval)⁻¹ (.circuit (Circuit.H (rAct13 nonAltSpinWire))) := by
    rw [hH_inv, show Circuit.H (rAct13 nonAltSpinWire) =
      (Circuit.H nonAltSpinWire).onRegister rAct13 from rfl]
    exact Solution.CleanDyn.CleanRealizes.circuit v rAct13 rScr4 (by decide)
      (Circuit.H nonAltSpinWire) rfl
  have h3 := cr_lift_sub (cleanRealizes_placeWithScratchPrefix (m := 4) v
    (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord)⁻¹
    (OptU2Grover184PrepOut13.unprepUnif184WordLocDyn rotWord v)
    (rAct13.compose nonAltXoAuxReg) rScr4 (by decide) (by decide)
    (cleanRealizes_unprepGroverLocDyn v 3 5 23 4 (wordToCircuit1 rotWord).eval _
      (cleanRealizes_groverStepInvLocDyn v 5 23 4 rotWord _ _
        (cleanRealizes_rGood23LocDyn v) (cleanRealizes_sZero6LocDyn v))))
  refine (h1.seq (h2.seq h3)).congr_unitary ?_
  simp only [init13Unitary, _root_.mul_inv_rev, QRegister.embedUnitary_inv, mul_assoc]

theorem nonAlt13Loc_embedInit13Unitary (uUnif9 : Unitary (2 ^ 9)) :
    nonAlt13Loc.embedUnitary (init13Unitary uUnif9) =
      kLoc.embedUnitary orthCoin10Unitary *
        (Circuit.H spinWire).eval *
        (nonAlt13Loc.compose nonAltXoAuxReg).embedUnitary uUnif9 := by
  have hH : nonAlt13Loc.embedUnitary (Circuit.H nonAltSpinWire).eval =
      (Circuit.H spinWire).eval := by
    rw [← Circuit.eval_onRegister, ← nonAlt13Loc_spin]; rfl
  dsimp only [init13Unitary]
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
    ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    nonAlt13Loc_compose_kReg, hH]

/-! ## Section 2: Reusable `1`-AND `c₃ = 0` & `x₁`-Affine Gadgets + `210-T` Forward QROM -/

theorem sum_oneHot_cnotMask_eq {N : ℕ} (rHot : QRegister 46 N) (δ : BitAssignment N)
    (g : Fin 46) (mask : Fin 46 → Bool)
    (hHot : ∀ i : Fin 46, δ (rHot i) = if i = g then 1 else 0) :
    (∑ i : Fin 46, if mask i then δ (rHot i) else 0) = b2z (mask g) := by
  have hpt (i : Fin 46) : (if mask i then δ (rHot i) else 0) =
      if i = g then b2z (mask g) else 0 := by
    rw [hHot i]
    by_cases hig : i = g
    · subst hig; cases mask i <;> simp [b2z]
    · simp [hig]
  simp_rw [hpt]; simp

/-- `1`-AND (`4-T`) reversible `c₃ = 0` lookup writing
`b2z (b0 g) + x₀ * b2z (b1 g) + x₁ * b2z (b2 g)` onto wire `off + 77` using clean scratch
`off + 77`, `off + 79`, `off + 80` and `s₀₁ = x₀ * x₁` on `off + 46`. -/
def cnotNoC3AtOffRev {N : ℕ} (off : ℕ) (h12 : 12 ≤ off) (hN : off + 81 ≤ N)
    (b0 b1 b2 : Fin 46 → Bool) : GroupUnary.RevCompute N :=
  let rHot : QRegister 46 N := QRegister.block off 46 (by omega)
  let w0 : Wire N := ⟨0, by omega⟩
  let w1 : Wire N := ⟨1, by omega⟩
  let wS01 : Wire N := ⟨off + 46, by omega⟩
  let wOut : Wire N := ⟨off + 77, by omega⟩
  let t1 : Wire N := ⟨off + 79, by omega⟩
  let t2 : Wire N := ⟨off + 80, by omega⟩
  .seq (cnotMaskRev t1 46 rHot
          (fun i h ↦ by have hv := congrArg Fin.val h; simp [rHot, t1] at hv; omega) b2)
    (.seq (.cnot w0 t1 (fun h ↦ by have hv := congrArg Fin.val h; dsimp [w0, t1] at hv; omega))
      (.seq (cnotMaskRev t2 46 rHot
              (fun i h ↦ by have hv := congrArg Fin.val h; simp [rHot, t2] at hv; omega) b1)
        (.seq (.cnot w1 t2 (fun h ↦ by have hv := congrArg Fin.val h; dsimp [w1, t2] at hv; omega))
          (.seq (.andGate t1 t2 wOut
                  (fun h ↦ by have hv := congrArg Fin.val h; dsimp [t1, t2] at hv; omega)
                  (fun h ↦ by have hv := congrArg Fin.val h; dsimp [t1, wOut] at hv; omega)
                  (fun h ↦ by have hv := congrArg Fin.val h; dsimp [t2, wOut] at hv; omega))
            (.seq (.cnot wS01 wOut
                    (fun h ↦ by have hv := congrArg Fin.val h; dsimp [wS01, wOut] at hv; omega))
              (cnotMaskRev wOut 46 rHot
                (fun i h ↦ by have hv := congrArg Fin.val h; simp [rHot, wOut] at hv; omega)
                (fun i ↦ xor (b0 i) (b1 i && b2 i))))))))

@[simp]
theorem numAnd_cnotNoC3AtOffRev {N : ℕ} (off : ℕ) (h12 : 12 ≤ off) (hN : off + 81 ≤ N)
    (b0 b1 b2 : Fin 46 → Bool) :
    (cnotNoC3AtOffRev off h12 hN b0 b1 b2).numAnd = 1 := by
  simp [cnotNoC3AtOffRev, GroupUnary.RevCompute.numAnd]

theorem revDisjRange_cnotNoC3AtOffRev {N : ℕ} (off : ℕ) (h16 : 16 ≤ off) (hN : off + 81 ≤ N)
    (b0 b1 b2 : Fin 46 → Bool) :
    RevDisjRange 12 16 (cnotNoC3AtOffRev off (by omega) hN b0 b1 b2) := by
  dsimp only [cnotNoC3AtOffRev, RevDisjRange]
  refine ⟨?_, ⟨Or.inl (by omega), Or.inr (by omega)⟩, ?_,
    ⟨Or.inl (by omega), Or.inr (by omega)⟩,
    ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
    ⟨Or.inr (by omega), Or.inr (by omega)⟩, ?_⟩
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by dsimp; omega)) 46 _ _ _
      (fun i ↦ Or.inr (by simp; omega))
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by dsimp; omega)) 46 _ _ _
      (fun i ↦ Or.inr (by simp; omega))
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by dsimp; omega)) 46 _ _ _
      (fun i ↦ Or.inr (by simp; omega))

theorem cnotNoC3AtOffRev_spec {N : ℕ} (off : ℕ) (h12 : 12 ≤ off) (hN : off + 81 ≤ N)
    (b0 b1 b2 : Fin 46 → Bool) (β : BitAssignment N) (g : Fin 46)
    (hHot : ∀ i : Fin 46, β ⟨off + i.val, by omega⟩ = if i = g then 1 else 0)
    (hS01 : β ⟨off + 46, by omega⟩ = β ⟨0, by omega⟩ * β ⟨1, by omega⟩)
    (h77 : β ⟨off + 77, by omega⟩ = 0)
    (h79 : β ⟨off + 79, by omega⟩ = 0)
    (h80 : β ⟨off + 80, by omega⟩ = 0) :
    (cnotNoC3AtOffRev off h12 hN b0 b1 b2).validOn β = true ∧
      (∀ u : Wire N, u ≠ ⟨off + 77, by omega⟩ → u ≠ ⟨off + 79, by omega⟩ →
        u ≠ ⟨off + 80, by omega⟩ → (cnotNoC3AtOffRev off h12 hN b0 b1 b2).fwdBits β u = β u) ∧
      (cnotNoC3AtOffRev off h12 hN b0 b1 b2).fwdBits β ⟨off + 77, by omega⟩ =
        b2z (b0 g) + β ⟨0, by omega⟩ * b2z (b1 g) + β ⟨1, by omega⟩ * b2z (b2 g) := by
  let rHot : QRegister 46 N := QRegister.block off 46 (by omega)
  let w0 : Wire N := ⟨0, by omega⟩
  let w1 : Wire N := ⟨1, by omega⟩
  let wS01 : Wire N := ⟨off + 46, by omega⟩
  let wOut : Wire N := ⟨off + 77, by omega⟩
  let t1 : Wire N := ⟨off + 79, by omega⟩
  let t2 : Wire N := ⟨off + 80, by omega⟩
  have hHotR (i : Fin 46) : β (rHot i) = if i = g then 1 else 0 := by
    simpa only [rHot, qreg_block_apply] using hHot i
  have hr_ne {i : Fin 46} {u : Wire N} (hu : off + 46 ≤ u.val) : rHot i ≠ u :=
    fun h ↦ by have hv := congrArg Fin.val h; simp [rHot] at hv; omega
  have hw_ne {a b : Wire N} (hab : a.val ≠ b.val) : a ≠ b :=
    fun h ↦ hab (congrArg Fin.val h)
  let p1 := cnotMaskRev t1 46 rHot
    (fun i h ↦ by have hv := congrArg Fin.val h; simp [rHot, t1] at hv; omega) b2
  let p2 : GroupUnary.RevCompute N :=
    .cnot w0 t1 (fun h ↦ by have hv := congrArg Fin.val h; dsimp [w0, t1] at hv; omega)
  let p3 := cnotMaskRev t2 46 rHot
    (fun i h ↦ by have hv := congrArg Fin.val h; simp [rHot, t2] at hv; omega) b1
  let p4 : GroupUnary.RevCompute N :=
    .cnot w1 t2 (fun h ↦ by have hv := congrArg Fin.val h; dsimp [w1, t2] at hv; omega)
  let p5 : GroupUnary.RevCompute N := .andGate t1 t2 wOut
    (fun h ↦ by have hv := congrArg Fin.val h; dsimp [t1, t2] at hv; omega)
    (fun h ↦ by have hv := congrArg Fin.val h; dsimp [t1, wOut] at hv; omega)
    (fun h ↦ by have hv := congrArg Fin.val h; dsimp [t2, wOut] at hv; omega)
  let p6 : GroupUnary.RevCompute N :=
    .cnot wS01 wOut (fun h ↦ by have hv := congrArg Fin.val h; dsimp [wS01, wOut] at hv; omega)
  let p7 := cnotMaskRev wOut 46 rHot
    (fun i h ↦ by have hv := congrArg Fin.val h; simp [rHot, wOut] at hv; omega)
    (fun i ↦ xor (b0 i) (b1 i && b2 i))
  obtain ⟨hv1, hf1⟩ := cnotMaskRev_spec t1 rHot _ b2 β
  let β1 := p1.fwdBits β
  have hβ1 : β1 = Function.update β t1 (b2z (b2 g)) := by
    dsimp only [β1, p1]; rw [hf1, h79, zero_add, sum_oneHot_cnotMask_eq rHot β g b2 hHotR]
  have hv2 : p2.validOn β1 = true := rfl
  let β2 := p2.fwdBits β1
  have hβ2 : β2 = Function.update β t1 (b2z (b2 g) + β w0) := by
    dsimp only [β2, p2, GroupUnary.RevCompute.fwdBits]
    rw [hβ1, Function.update_self, Function.update_of_ne (hw_ne (by dsimp [w0, t1]; omega)),
      Function.update_idem]
  have hHot2 (i : Fin 46) : β2 (rHot i) = if i = g then 1 else 0 := by
    rw [hβ2, Function.update_of_ne (hr_ne (by dsimp [t1]; omega))]; exact hHotR i
  have ht2_2 : β2 t2 = 0 := by
    rw [hβ2, Function.update_of_ne (hw_ne (by dsimp [t2, t1]; omega))]; exact h80
  obtain ⟨hv3, hf3⟩ := cnotMaskRev_spec t2 rHot _ b1 β2
  let β3 := p3.fwdBits β2
  have hβ3 : β3 = Function.update β2 t2 (b2z (b1 g)) := by
    dsimp only [β3, p3]; rw [hf3, ht2_2, zero_add, sum_oneHot_cnotMask_eq rHot β2 g b1 hHot2]
  have hv4 : p4.validOn β3 = true := rfl
  let β4 := p4.fwdBits β3
  have hβ4 : β4 = Function.update β2 t2 (b2z (b1 g) + β w1) := by
    dsimp only [β4, p4, GroupUnary.RevCompute.fwdBits]
    have hw1_2 : β2 w1 = β w1 := by
      rw [hβ2, Function.update_of_ne (hw_ne (by dsimp [w1, t1]; omega))]
    rw [hβ3, Function.update_self, Function.update_of_ne (hw_ne (by dsimp [w1, t2]; omega)),
      hw1_2, Function.update_idem]
  have hout_4 : β4 wOut = 0 := by
    rw [hβ4, Function.update_of_ne (hw_ne (by dsimp [wOut, t2]; omega)),
      hβ2, Function.update_of_ne (hw_ne (by dsimp [wOut, t1]; omega))]; exact h77
  have hv5 : p5.validOn β4 = true := by
    simpa [p5, GroupUnary.RevCompute.validOn] using hout_4
  let β5 := p5.fwdBits β4
  have hβ5 : β5 = Function.update β4 wOut ((b2z (b2 g) + β w0) * (b2z (b1 g) + β w1)) := by
    dsimp only [β5, p5, GroupUnary.RevCompute.fwdBits]
    have ht1_4 : β4 t1 = b2z (b2 g) + β w0 := by
      rw [hβ4, Function.update_of_ne (hw_ne (by dsimp [t1, t2]; omega)), hβ2, Function.update_self]
    have ht2_4 : β4 t2 = b2z (b1 g) + β w1 := by rw [hβ4, Function.update_self]
    rw [hout_4, zero_add, ht1_4, ht2_4]
  have hv6 : p6.validOn β5 = true := rfl
  let β6 := p6.fwdBits β5
  have hβ6 : β6 =
      Function.update β4 wOut ((b2z (b2 g) + β w0) * (b2z (b1 g) + β w1) + β w0 * β w1) := by
    dsimp only [β6, p6, GroupUnary.RevCompute.fwdBits]
    have hs01_5 : β5 wS01 = β w0 * β w1 := by
      rw [hβ5, Function.update_of_ne (hw_ne (by dsimp [wS01, wOut]; omega)),
        hβ4, Function.update_of_ne (hw_ne (by dsimp [wS01, t2]; omega)),
        hβ2, Function.update_of_ne (hw_ne (by dsimp [wS01, t1]; omega))]; exact hS01
    rw [hs01_5, hβ5, Function.update_self, Function.update_idem]
  have hHot6 (i : Fin 46) : β6 (rHot i) = if i = g then 1 else 0 := by
    rw [hβ6, Function.update_of_ne (hr_ne (by dsimp [wOut]; omega)),
      hβ4, Function.update_of_ne (hr_ne (by dsimp [t2]; omega)),
      hβ2, Function.update_of_ne (hr_ne (by dsimp [t1]; omega))]; exact hHotR i
  obtain ⟨hv7, hf7⟩ := cnotMaskRev_spec wOut rHot _ (fun i ↦ xor (b0 i) (b1 i && b2 i)) β6
  have hβ7 : (cnotNoC3AtOffRev off h12 hN b0 b1 b2).fwdBits β =
      Function.update β4 wOut (b2z (b0 g) + β w0 * b2z (b1 g) + β w1 * b2z (b2 g)) := by
    change p7.fwdBits β6 = _
    rw [hf7, sum_oneHot_cnotMask_eq rHot β6 g _ hHot6, hβ6, Function.update_self,
      Function.update_idem, noC3_zmod2_id]
  refine ⟨Bool.and_eq_true_iff.mpr ⟨hv1, Bool.and_eq_true_iff.mpr
    ⟨hv2, Bool.and_eq_true_iff.mpr ⟨hv3, Bool.and_eq_true_iff.mpr
      ⟨hv4, Bool.and_eq_true_iff.mpr ⟨hv5, Bool.and_eq_true_iff.mpr ⟨hv6, hv7⟩⟩⟩⟩⟩⟩,
    fun u huOut huT1 huT2 ↦ ?_, ?_⟩
  · rw [hβ7, Function.update_of_ne huOut, hβ4, Function.update_of_ne huT2,
      hβ2, Function.update_of_ne huT1]
  · rw [hβ7, Function.update_self]

/-! ### `210-T` (`87`-Scratch) Forward QROM (`preSwap103Dyn`) -/

/-- `4` bits XOR-loaded into `rAlt4` (`8..11`) for `(y : Fin 184, mk : ZMod 2)` under
`pi145CompactTable`: `[alt₂, alt₃, mk ∨ alt₆, mk ∨ alt₇]`. -/
def loadedAlt4Bits (y : Fin 184) (mk : ZMod 2) (j : Fin 4) : ZMod 2 :=
  let b := basisBits 8 (altFin256_2 y) (ret4Idx j)
  if j.val < 2 then b else mk + (1 + mk) * b

theorem postCswap_route_eq (y : Fin 184) (mkB : Bool) :
    let mk : ZMod 2 := if mkB then 1 else 0
    let xBits : BitAssignment 8 := basisBits 8 ⟨y.val, by omega⟩
    let aBits : BitAssignment 4 := loadedAlt4Bits y mk
    let outIdx : Fin 184 := if mkB then y else (pi145CompactTable y).alt
    postCswapXoBits xBits aBits = basisBits 8 ⟨outIdx.val, by omega⟩ := by
  intro mk xBits aBits outIdx
  have hx67 : xBits 7 * xBits 6 = 0 := top2_basisBits8_mul_zero_of_lt184 y.isLt
  have ha67 : basisBits 8 (altFin256_2 y) 7 * basisBits 8 (altFin256_2 y) 6 = 0 :=
    top2_basisBits8_mul_zero_of_lt184 (pi145CompactTable y).alt.isLt
  have hcoset := List.all_eq_true.mp checkCompactCoset16_eq_true y (List.mem_finRange y)
  simp only [Bool.and_eq_true, beq_iff_eq] at hcoset
  rcases hcoset with ⟨⟨⟨hc0, hc1⟩, hc4⟩, hc5⟩
  cases mkB
  · have hmk : mk = 0 := rfl
    have ha2 : aBits 2 = basisBits 8 (altFin256_2 y) 6 := by
      dsimp only [aBits, loadedAlt4Bits, ret4Idx]; simp [hmk]
    have ha3 : aBits 3 = basisBits 8 (altFin256_2 y) 7 := by
      dsimp only [aBits, loadedAlt4Bits, ret4Idx]; simp [hmk]
    have hgd : cswapGuardBit xBits aBits = 1 := by
      dsimp only [cswapGuardBit]; rw [hx67, ha3, ha2, ha67]; decide
    funext i; dsimp only [postCswapXoBits, outIdx]
    rw [ite_eq_left hgd]
    fin_cases i
    · dsimp only [xBits]; rw [basisBits_eq_testBit, basisBits_eq_testBit]; simp [hc0]
    · dsimp only [xBits]; rw [basisBits_eq_testBit, basisBits_eq_testBit]; simp [hc1]
    · dsimp only [aBits, loadedAlt4Bits, ret4Idx]; simp
    · dsimp only [aBits, loadedAlt4Bits, ret4Idx]; simp
    · dsimp only [xBits]; rw [basisBits_eq_testBit, basisBits_eq_testBit]; simp [hc4]
    · dsimp only [xBits]; rw [basisBits_eq_testBit, basisBits_eq_testBit]; simp [hc5]
    · exact ha2
    · exact ha3
  · have hmk : mk = 1 := rfl
    have ha2 : aBits 2 = 1 := by
      dsimp only [aBits, loadedAlt4Bits, ret4Idx]; simp [hmk]
    have ha3 : aBits 3 = 1 := by
      dsimp only [aBits, loadedAlt4Bits, ret4Idx]; simp [hmk]
    have hgd : cswapGuardBit xBits aBits = 0 := by
      dsimp only [cswapGuardBit]; rw [hx67, ha3, ha2]; decide
    funext i; dsimp only [postCswapXoBits, outIdx]
    rw [ite_eq_right (by rw [hgd]; decide)]; rfl

/-- `4096 × 4` Boolean QROM table loaded by `preSwap103Dyn` on `12`-bit index `(x : 8, c : 4)`. -/
def alt4BoolTable (idx : ℕ) (j : Fin 4) : Bool :=
  let x := idx % 256
  let c := (idx / 256) % 16
  let g := DyadicXMeasPrepOut13.effGroup (x / 4)
  let y : Fin 184 := ⟨4 * g.val + x % 4, by have := g.isLt; omega⟩
  let kv : Fin 1024 := ⟨(pi145CompactTable y).keep % 1024, Nat.mod_lt _ (by decide)⟩
  let mk : ZMod 2 := pktKeepSel10 (basisBits 10 kv) (basisBits 4 ⟨c, by omega⟩)
  loadedAlt4Bits y mk j == 1

/-- `1`-AND (`4-T`) lookup computing `alt₂(y)` (`c₃ = 0`) on `93` and group-constant `alt₃(y)` on
`94` using clean scratch `93..96`. -/
def pCompactAlt23 : GroupUnary.RevCompute 103 :=
  .seq (cnotNoC3AtOffRev 16 (by decide) (by decide) alt2B0 alt2B1 alt2B2)
    (cnotMaskRev ⟨94, by decide⟩ 46 (QRegister.block 16 46 (by decide)) (by decide) alt3Group)

@[simp]
theorem numAnd_pCompactAlt23 : pCompactAlt23.numAnd = 1 := by
  simp [pCompactAlt23, GroupUnary.RevCompute.numAnd]

theorem pCompactAlt23_spec (β : BitAssignment 103) (g : Fin 46)
    (hHot : ∀ i : Fin 46, β ⟨16 + i.val, by omega⟩ = if i = g then 1 else 0)
    (hS01 : β ⟨62, by decide⟩ = β ⟨0, by decide⟩ * β ⟨1, by decide⟩)
    (h93 : β ⟨93, by decide⟩ = 0) (h94 : β ⟨94, by decide⟩ = 0)
    (h95 : β ⟨95, by decide⟩ = 0) (h96 : β ⟨96, by decide⟩ = 0) :
    pCompactAlt23.validOn β = true ∧
      (∀ u : Wire 103, (u.val < 93 ∨ 97 ≤ u.val) → pCompactAlt23.fwdBits β u = β u) ∧
      pCompactAlt23.fwdBits β ⟨93, by decide⟩ =
        b2z (alt2B0 g) + β ⟨0, by decide⟩ * b2z (alt2B1 g) +
          β ⟨1, by decide⟩ * b2z (alt2B2 g) ∧
      pCompactAlt23.fwdBits β ⟨94, by decide⟩ = b2z (alt3Group g) := by
  let rHot : QRegister 46 103 := QRegister.block 16 46 (by decide)
  obtain ⟨hv1, hout1, h93_1⟩ := cnotNoC3AtOffRev_spec 16 (by decide) (by decide)
    alt2B0 alt2B1 alt2B2 β g hHot hS01 h93 h95 h96
  let β1 := (cnotNoC3AtOffRev 16 (by decide) (by decide)
    alt2B0 alt2B1 alt2B2).fwdBits β
  have hHot1 (i : Fin 46) : β1 (rHot i) = if i = g then 1 else 0 := by
    have hne (k : ℕ) (hk : 93 ≤ k) (hk2 : k < 103) : rHot i ≠ ⟨k, hk2⟩ :=
      fun h ↦ by have hv := congrArg Fin.val h; simp [rHot] at hv; omega
    have hw := hout1 (rHot i) (hne 93 (by decide) (by decide))
      (hne 95 (by decide) (by decide)) (hne 96 (by decide) (by decide))
    change β1 (rHot i) = _ at hw
    rw [hw]; simpa only [rHot, qreg_block_apply] using hHot i
  have h94_1 : β1 ⟨94, by decide⟩ = 0 := by
    have hw := hout1 ⟨94, by decide⟩ (Fin.ne_of_val_ne (by decide))
      (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
    change β1 ⟨94, by decide⟩ = _ at hw
    rw [hw]; exact h94
  obtain ⟨hv2, hf2⟩ := cnotMaskRev_spec ⟨94, by decide⟩ rHot (by decide) alt3Group β1
  have hβ2 : pCompactAlt23.fwdBits β = Function.update β1 ⟨94, by decide⟩
      (b2z (alt3Group g)) := by
    change (cnotMaskRev ⟨94, by decide⟩ 46 rHot (by decide) alt3Group).fwdBits β1 = _
    rw [hf2, h94_1, zero_add, sum_oneHot_cnotMask_eq rHot β1 g alt3Group hHot1]
  refine ⟨Bool.and_eq_true_iff.mpr ⟨hv1, hv2⟩, fun u hu ↦ ?_, ?_, ?_⟩
  · have hu94 : u ≠ ⟨94, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    have hu93 : u ≠ ⟨93, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    have hu95 : u ≠ ⟨95, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    have hu96 : u ≠ ⟨96, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    rw [hβ2, Function.update_of_ne hu94]; exact hout1 u hu93 hu95 hu96
  · rw [hβ2, Function.update_of_ne (Fin.ne_of_val_ne (by decide))]; exact h93_1
  · rw [hβ2, Function.update_self]

/-- `1`-AND (`4-T`) affine top-`2` `alt` lookup computing `b₆` on `99` and `b₇` on `100`
using clean scratch `98..100`. -/
def affTop2Rev : GroupUnary.RevCompute 103 :=
  let rHot : QRegister 46 103 := QRegister.block 16 46 (by decide)
  .seq (cnotMaskRev ⟨98, by decide⟩ 46 rHot (by decide) alt6Slope)
    (.seq (.andGate ⟨1, by decide⟩ ⟨98, by decide⟩ ⟨99, by decide⟩
            (by decide) (by decide) (by decide))
      (.seq (cnotMaskRev ⟨99, by decide⟩ 46 rHot (by decide) alt6Base)
        (cnotMaskRev ⟨100, by decide⟩ 46 rHot (by decide) alt7Group)))

@[simp]
theorem numAndAffTop2Rev : affTop2Rev.numAnd = 1 := by
  simp [affTop2Rev, GroupUnary.RevCompute.numAnd]

theorem affTop2Rev_spec (β : BitAssignment 103) (g : Fin 46)
    (hHot : ∀ i : Fin 46, β ⟨16 + i.val, by omega⟩ = if i = g then 1 else 0)
    (h98 : β ⟨98, by decide⟩ = 0) (h99 : β ⟨99, by decide⟩ = 0)
    (h100 : β ⟨100, by decide⟩ = 0) :
    affTop2Rev.validOn β = true ∧
      (∀ u : Wire 103, (u.val < 98 ∨ 101 ≤ u.val) → affTop2Rev.fwdBits β u = β u) ∧
      affTop2Rev.fwdBits β ⟨99, by decide⟩ =
        b2z (alt6Base g) + β ⟨1, by decide⟩ * b2z (alt6Slope g) ∧
      affTop2Rev.fwdBits β ⟨100, by decide⟩ = b2z (alt7Group g) := by
  let rHot : QRegister 46 103 := QRegister.block 16 46 (by decide)
  have hHotR (i : Fin 46) : β (rHot i) = if i = g then 1 else 0 := by
    simpa only [rHot, qreg_block_apply] using hHot i
  obtain ⟨hv1, hf1⟩ := cnotMaskRev_spec ⟨98, by decide⟩ rHot (by decide) alt6Slope β
  let β1 := (cnotMaskRev ⟨98, by decide⟩ 46 rHot (by decide) alt6Slope).fwdBits β
  have hβ1 : β1 = Function.update β ⟨98, by decide⟩ (b2z (alt6Slope g)) := by
    dsimp only [β1]; rw [hf1, h98, zero_add, sum_oneHot_cnotMask_eq rHot β g alt6Slope hHotR]
  have h99_1 : β1 ⟨99, by decide⟩ = 0 := by
    rw [hβ1, Function.update_of_ne (Fin.ne_of_val_ne (by decide))]; exact h99
  let m2 : GroupUnary.RevCompute 103 :=
    .andGate ⟨1, by decide⟩ ⟨98, by decide⟩ ⟨99, by decide⟩ (by decide) (by decide) (by decide)
  have hv2 : m2.validOn β1 = true := by simpa [m2, GroupUnary.RevCompute.validOn] using h99_1
  let β2 := m2.fwdBits β1
  have hβ2 : β2 = Function.update β1 ⟨99, by decide⟩
      (β ⟨1, by decide⟩ * b2z (alt6Slope g)) := by
    dsimp only [β2, m2, GroupUnary.RevCompute.fwdBits]
    rw [h99_1, zero_add, hβ1, Function.update_of_ne (Fin.ne_of_val_ne (by decide)),
      Function.update_self]
  have hHot2 (i : Fin 46) : β2 (rHot i) = if i = g then 1 else 0 := by
    have hne99 : rHot i ≠ ⟨99, by decide⟩ :=
      fun h ↦ by have := congrArg Fin.val h; simp [rHot] at this; omega
    have hne98 : rHot i ≠ ⟨98, by decide⟩ :=
      fun h ↦ by have := congrArg Fin.val h; simp [rHot] at this; omega
    rw [hβ2, Function.update_of_ne hne99, hβ1, Function.update_of_ne hne98]; exact hHotR i
  obtain ⟨hv3, hf3⟩ := cnotMaskRev_spec ⟨99, by decide⟩ rHot (by decide) alt6Base β2
  let β3 := (cnotMaskRev ⟨99, by decide⟩ 46 rHot (by decide) alt6Base).fwdBits β2
  have hβ3 : β3 = Function.update β1 ⟨99, by decide⟩
      (b2z (alt6Base g) + β ⟨1, by decide⟩ * b2z (alt6Slope g)) := by
    dsimp only [β3]
    rw [hf3, sum_oneHot_cnotMask_eq rHot β2 g alt6Base hHot2, hβ2,
      Function.update_self, Function.update_idem, add_comm]
  have hHot3 (i : Fin 46) : β3 (rHot i) = if i = g then 1 else 0 := by
    have hne99 : rHot i ≠ ⟨99, by decide⟩ :=
      fun h ↦ by have := congrArg Fin.val h; simp [rHot] at this; omega
    have hne98 : rHot i ≠ ⟨98, by decide⟩ :=
      fun h ↦ by have := congrArg Fin.val h; simp [rHot] at this; omega
    rw [hβ3, Function.update_of_ne hne99, hβ1, Function.update_of_ne hne98]; exact hHotR i
  have h100_3 : β3 ⟨100, by decide⟩ = 0 := by
    rw [hβ3, Function.update_of_ne (Fin.ne_of_val_ne (by decide)),
      hβ1, Function.update_of_ne (Fin.ne_of_val_ne (by decide))]; exact h100
  obtain ⟨hv4, hf4⟩ := cnotMaskRev_spec ⟨100, by decide⟩ rHot (by decide) alt7Group β3
  have hβ4 : affTop2Rev.fwdBits β = Function.update β3 ⟨100, by decide⟩
      (b2z (alt7Group g)) := by
    change (cnotMaskRev ⟨100, by decide⟩ 46 rHot (by decide) alt7Group).fwdBits β3 = _
    rw [hf4, h100_3, zero_add, sum_oneHot_cnotMask_eq rHot β3 g alt7Group hHot3]
  refine ⟨Bool.and_eq_true_iff.mpr ⟨hv1, Bool.and_eq_true_iff.mpr
    ⟨hv2, Bool.and_eq_true_iff.mpr ⟨hv3, hv4⟩⟩⟩, fun u hu ↦ ?_, ?_, ?_⟩
  · have hu100 : u ≠ ⟨100, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    have hu99 : u ≠ ⟨99, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    have hu98 : u ≠ ⟨98, by decide⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    rw [hβ4, Function.update_of_ne hu100, hβ3, Function.update_of_ne hu99,
      hβ1, Function.update_of_ne hu98]
  · rw [hβ4, Function.update_of_ne (Fin.ne_of_val_ne (by decide)), hβ3, Function.update_self]
  · rw [hβ4, Function.update_self]

/-- `2`-AND (`8-T`) `¬mk ∧ b₆` and `¬mk ∧ b₇` terms on wires `101` and `102` (`mk` on `92`,
`b₆` on `99`, `b₇` on `100`). -/
def mkOr2 : GroupUnary.RevCompute 103 :=
  .seq (notAndRev ⟨92, by decide⟩ ⟨99, by decide⟩ ⟨101, by decide⟩
          (by decide) (by decide) (by decide))
    (notAndRev ⟨92, by decide⟩ ⟨100, by decide⟩ ⟨102, by decide⟩
      (by decide) (by decide) (by decide))

@[simp]
theorem numAndMkOr2 : mkOr2.numAnd = 2 := by
  simp [mkOr2, GroupUnary.RevCompute.numAnd]

theorem mkOr2_spec (β : BitAssignment 103)
    (h101 : β ⟨101, by decide⟩ = 0) (h102 : β ⟨102, by decide⟩ = 0) :
    mkOr2.validOn β = true ∧
      (∀ u : Wire 103, u.val < 101 → mkOr2.fwdBits β u = β u) ∧
      mkOr2.fwdBits β ⟨101, by decide⟩ = (1 + β ⟨92, by decide⟩) * β ⟨99, by decide⟩ ∧
      mkOr2.fwdBits β ⟨102, by decide⟩ = (1 + β ⟨92, by decide⟩) * β ⟨100, by decide⟩ := by
  obtain ⟨hv1, hf1⟩ := notAndRev_spec ⟨92, by decide⟩ ⟨99, by decide⟩ ⟨101, by decide⟩
    (by decide) (by decide) (by decide) β h101
  set β1 := (notAndRev ⟨92, by decide⟩ ⟨99, by decide⟩ ⟨101, by decide⟩
    (by decide) (by decide) (by decide)).fwdBits β
  have h102_1 : β1 ⟨102, by decide⟩ = 0 := by
    rw [hf1, Function.update_of_ne (Fin.ne_of_val_ne (by decide))]; exact h102
  obtain ⟨hv2, hf2⟩ := notAndRev_spec ⟨92, by decide⟩ ⟨100, by decide⟩ ⟨102, by decide⟩
    (by decide) (by decide) (by decide) β1 h102_1
  refine ⟨Bool.and_eq_true_iff.mpr ⟨hv1, hv2⟩, fun u hu ↦ ?_, ?_, ?_⟩
  · change (notAndRev _ _ _ _ _ _).fwdBits β1 u = β u
    have hu102 : u ≠ ⟨102, by decide⟩ :=
      fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    have hu101 : u ≠ ⟨101, by decide⟩ :=
      fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
    rw [hf2, Function.update_of_ne hu102, hf1, Function.update_of_ne hu101]
  · change (notAndRev _ _ _ _ _ _).fwdBits β1 ⟨101, by decide⟩ = _
    rw [hf2, Function.update_of_ne (Fin.ne_of_val_ne (by decide)), hf1, Function.update_self]
  · change (notAndRev _ _ _ _ _ _).fwdBits β1 ⟨102, by decide⟩ = _
    rw [hf2, Function.update_self, hf1,
      Function.update_of_ne (Fin.ne_of_val_ne (by decide)),
      Function.update_of_ne (Fin.ne_of_val_ne (by decide))]

/-- Classical reversible reference for the `210-T` compute half of `preSwap103Dyn`. -/
def preSwapComputeRev2 : GroupUnary.RevCompute 103 :=
  .seq (wHot46Rev 16 (by decide) (by decide))
    (.seq (pKeepMux25_2 pi145CompactTable 16 (by decide) (by decide))
      (.seq pCompactAlt23 (.seq affTop2Rev mkOr2)))

theorem revDisjRangePreSwapComputeRev2 :
    RevDisjRange 12 16 preSwapComputeRev2 := by
  refine ⟨revDisjRangePreSwapComputeRev.1, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact revDisjRange_pairedLac4Loop 12 16 _ _ _ _ _ _ _ _ _ _
      (fun i ↦ Or.inr (by simp))
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr (by decide))
      (fun j ↦ Or.inr (by simp; omega)) 5 le_rfl
  · have hmux {s a b dst : Wire 103} {hab hsb hsd hbd had}
        (hs : s.val < 12 ∨ 16 ≤ s.val) (ha : a.val < 12 ∨ 16 ≤ a.val)
        (hb : b.val < 12 ∨ 16 ≤ b.val) (hd : dst.val < 12 ∨ 16 ≤ dst.val) :
        RevDisjRange 12 16 (mux2Rev s a b dst hab hsb hsd hbd had) :=
      ⟨⟨ha, hb⟩, ⟨hs, hb, hd⟩, ⟨ha, hb⟩, ⟨ha, hd⟩⟩
    have hnand {s a dst : Wire 103} {hsa hsd had}
        (hs : s.val < 12 ∨ 16 ≤ s.val) (ha : a.val < 12 ∨ 16 ≤ a.val)
        (hd : dst.val < 12 ∨ 16 ≤ dst.val) :
        RevDisjRange 12 16 (notAndRev s a dst hsa hsd had) :=
      ⟨hs, ⟨hs, ha, hd⟩, hs⟩
    have hq (j : Fin 4) : 8 + j.val < 12 ∨ 16 ≤ 8 + j.val := Or.inl (by omega)
    have hkp (i : Fin 10) : 16 + 50 + i.val < 12 ∨ 16 ≤ 16 + 50 + i.val := Or.inr (by omega)
    have hu (m : Fin 10) : 16 + 67 + m.val < 12 ∨ 16 ≤ 16 + 67 + m.val := Or.inr (by omega)
    exact ⟨hmux (hq 1) (hkp 2) (hkp 7) (hu 0), hmux (hq 1) (hkp 6) (hkp 3) (hu 1),
      hmux (hq 1) (hkp 8) (hkp 4) (hu 2), hnand (hq 1) (hkp 0) (hu 3),
      hmux (hq 0) (hu 1) (hu 2) (hu 4), hmux (hq 0) (hkp 9) (hkp 5) (hu 5),
      hmux (hq 0) (hkp 1) (hu 3) (hu 6), hmux (hq 2) (hu 0) (hu 4) (hu 7),
      hmux (hq 2) (hu 5) (hu 6) (hu 8), hmux (hq 3) (hu 7) (hu 8) (hu 9)⟩
  · exact revDisjRange_cnotNoC3AtOffRev 16 (by decide) (by decide)
      alt2B0 alt2B1 alt2B2
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by decide)) 46 _ _ _
      (fun i ↦ Or.inr (by simp))
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by decide)) 46 _ _ _
      (fun i ↦ Or.inr (by simp))
  · exact ⟨Or.inl (by decide), Or.inr (by decide), Or.inr (by decide)⟩
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by decide)) 46 _ _ _
      (fun i ↦ Or.inr (by simp))
  · exact revDisjRange_cnotMaskRev 12 16 _ (Or.inr (by decide)) 46 _ _ _
      (fun i ↦ Or.inr (by simp))
  · dsimp [mkOr2, notAndRev, RevDisjRange]; decide

/-! ## Section 3: `202-T` (`82`-Scratch) X-Meas Phase Leaf (`leaf94Dyn`) -/

/-- Group-level constant ANF coefficient of `p₀(y)` for X-measurement outcome `m : Fin (2 ^ 4)`. -/
def leafP0B0 (m : Fin (2 ^ 4)) (g : Fin 46) : Bool :=
  xor (xor ((basisBits 4 m 0 == 1) && alt2B0 g) ((basisBits 4 m 1 == 1) && alt3Group g))
    (xor ((basisBits 4 m 2 == 1) && alt6Base g) ((basisBits 4 m 3 == 1) && alt7Group g))

/-- Group-level `x₀`-slope of `p₀(y)` for X-measurement outcome `m : Fin (2 ^ 4)`. -/
def leafP0B1 (m : Fin (2 ^ 4)) (g : Fin 46) : Bool :=
  (basisBits 4 m 0 == 1) && alt2B1 g

/-- Group-level `x₁`-slope of `p₀(y)` for X-measurement outcome `m : Fin (2 ^ 4)`. -/
def leafP0B2 (m : Fin (2 ^ 4)) (g : Fin 46) : Bool :=
  xor ((basisBits 4 m 0 == 1) && alt2B2 g) ((basisBits 4 m 2 == 1) && alt6Slope g)

/-! ## Section 4: `286 + 3 * wordCountT` Forward & `278 + 3 * wordCountT` Backward `PREP_out` -/

/-- Support-disjoint `17`-qubit outer `PREP` unitary on `mOutUB 8 = 17`:
`cswap ∘ qromXor ∘ init13`. -/
def outer8PrepOutUnit (uUnif9 : Unitary (2 ^ 9)) : Unitary (2 ^ mOutUB 8) :=
  (xoAlt12Loc.embedUnitary cswap12Unitary *
    idxAlt16Loc.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)) *
  nonAlt13Loc.embedUnitary (init13Unitary uUnif9)

/-- Implemented `wOuter = 8` support-disjoint outer `PREP` unitary parameterized by `rotWord`. -/
abbrev outer8PrepOutWordImpl (rotWord : List Gate1) : Unitary (2 ^ mOutUB 8) :=
  outer8PrepOutUnit (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord)

/-- Ideal `wOuter = 8` support-disjoint outer `PREP` unitary parameterized by `W_ideal`. -/
abbrev outer8PrepOutWordIdeal (W_ideal : Unitary (2 ^ 1)) : Unitary (2 ^ mOutUB 8) :=
  outer8PrepOutUnit (prepGroverUnitary 3 5 23 W_ideal)

/-- Stage-2 classical bit involution on `BitAssignment (mOutUB 8)` induced by `alt4BoolTable`. -/
def gromXor17Bits (γ : BitAssignment (mOutUB 8)) : BitAssignment (mOutUB 8) :=
  xorRegBits γ alt4Loc (alt4BoolTable (localIdx idx12Loc γ).val)

theorem gromXor17Bits_invol (γ : BitAssignment (mOutUB 8)) :
    gromXor17Bits (gromXor17Bits γ) = γ := by
  have hIdx : localIdx idx12Loc (gromXor17Bits γ) = localIdx idx12Loc γ := by
    unfold localIdx; congr 1; funext i; dsimp only [gromXor17Bits]
    apply xorRegBits_apply_of_not_mem
    have hDisj : idx12Loc.DisjointWires alt4Loc := by decide
    intro hm; obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
    exact hDisj.ne i j hj.symm
  change xorRegBits (gromXor17Bits γ) alt4Loc
    (alt4BoolTable (localIdx idx12Loc (gromXor17Bits γ)).val) = γ
  rw [hIdx]; dsimp only [gromXor17Bits]; funext w
  by_cases hw : w ∈ alt4Loc.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hw
    rw [xorRegBits_apply_reg, xorRegBits_apply_reg, add_assoc, zmod2_add_self, add_zero]
  · rw [xorRegBits_apply_of_not_mem _ _ _ w hw, xorRegBits_apply_of_not_mem _ _ _ w hw]

theorem gromXor17_mulVec_ket (γ : BitAssignment (mOutUB 8)) :
    (idxAlt16Loc.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)).1.mulVec (ket γ) =
      ket (gromXor17Bits γ) := by
  have hlt : (localIdx idx12Loc γ).val < 4096 := (localIdx idx12Loc γ).isLt
  dsimp only [idxAlt16Loc, gromXor17Bits]
  rw [embed_xorLoadUnitary_mulVec_ket]; congr 2; funext j; simp [localIdx, hlt]

/-- Combined `17`-bit post-init classical permutation `cswap ∘ qromXor` for `alt4BoolTable`. -/
def postPerm17Bits (γ : BitAssignment (mOutUB 8)) : BitAssignment (mOutUB 8) :=
  gromCswap17Bits (gromXor17Bits γ)

theorem postPerm17Bits_injective : Function.Injective postPerm17Bits := by
  have hInv : Function.LeftInverse
      (fun δ ↦ gromXor17Bits (gromCswap17Bits δ)) postPerm17Bits := fun γ ↦ by
    dsimp only [postPerm17Bits]; rw [gromCswap17Bits_invol, gromXor17Bits_invol]
  exact hInv.injective

theorem outerConjPreservesZeroOuter8PrepOutUnit (uUnif9 : Unitary (2 ^ 9)) :
    OuterConjPreservesZero 8 4 (by decide) (outer8PrepOutUnit uUnif9) := by
  rw [outer8PrepOutUnit, mul_assoc]
  exact outerConjPreservesZero_mul_left_invol gromCswap17Bits gromCswap17Bits_invol
    gromCswap17_mulVec_ket
    (outerConjPreservesZero_mul_left_invol gromXor17Bits gromXor17Bits_invol
      gromXor17_mulVec_ket
      (outerConjPreservesZero_of_disjoint (by decide) nonAlt13Loc (by decide)
        (init13Unitary uUnif9)))

theorem outerConjPreservesZeroOuter8PrepOutWordImpl (rotWord : List Gate1) :
    OuterConjPreservesZero 8 4 (by decide) (outer8PrepOutWordImpl rotWord) :=
  outerConjPreservesZeroOuter8PrepOutUnit _

attribute [irreducible] init17WordLocDyn uninit17WordLocDyn

end

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Compact2RotDyn

/-! ## Outer Comb Sandwiches, `PrepOutValidPerm256` & `L¹` Sector Closures -/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Compact2RotOuter
open QuantumComputation.Specs QuantumComputation.Specs.P450

noncomputable section

open Operator QProg Matrix Circuit Real
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCore
open Solution.OuterWeights.GroverUniform
open Solution.Comparators hiding ket bit_cases matrix_ext_ket zeroProjOn
open Solution.SelectSwapQROM
open Solution.OptFactoredMag30AndCoin9
open Solution.ReordOuter13Bridge
open Solution.Phase2MidSandwich
open Solution.MobiusOptSubcube163Walk
open Solution.CompactZeroCmp20OuterParam
open Solution.CompactStepZeroCmp20OuterParam
open Solution.StepOuter8Pi145Outer
open Solution.StepOuter8Pi145L1
open Solution.Pi145Fast2RotCore
open Solution.Outer8Pi145Compact2RotDyn
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowCompactOuter (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 5: Comb Wrappers & Concrete `Word17 / Word15 / Word9` Sandwiches -/

/-! ## Section 6: `PrepOutValidPerm256`, Exact `L¹` Bounds & `fullQuantP450HBlocked` Closures -/

/-- Routed `Fin 184` output index produced on `rXoLoc 8` for `(x, c)` under `pi145CompactTable`. -/
def routedIdx (x : Fin 184) (c : Fin 16) : Fin 184 :=
  let kv : Fin 1024 := ⟨(pi145CompactTable x).keep, pi145CompactTable_keep_lt x⟩
  if pktSwapBit10 kv c = 0 then x else (pi145CompactTable x).alt

theorem postPerm17Bits_extract (x : Fin 184) (s : Fin 2) (c : Fin 16) :
    let x8 : Fin (2 ^ 8) := ⟨x.val, by omega⟩
    let o : Fin (2 ^ mOutUB 8) :=
      (basisBits (mOutUB 8)).symm (postPerm17Bits (inputBits x8 s c))
    ((rXoLoc 8).extractIndex o).val = (routedIdx x c).val ∧
      (rSigOutLoc 8).extractIndex o = s := by
  intro x8 o
  set β₀ := inputBits x8 s c
  have hIdxSplit : (localIdx idx12Loc β₀).val % 256 = x.val ∧
      ((localIdx idx12Loc β₀).val / 256) % 16 = c.val := by
    let idx12Fin := localIdx idx12Loc β₀
    let idx12 := idx12Fin.val
    have hb12 (k : ℕ) (hk : k < 12) : bit01Nat (β₀ (idx12Loc ⟨k, hk⟩)) = idx12 / 2 ^ k % 2 := by
      have hb : basisBits 12 idx12Fin ⟨k, hk⟩ = β₀ (idx12Loc ⟨k, hk⟩) :=
        congrFun (basisBits_basisBitsEquiv_symm (fun i ↦ β₀ (idx12Loc i))) ⟨k, hk⟩
      rw [← hb, basisBits_eq_div_mod]; dsimp only [bit01Nat, idx12]
      rcases Nat.mod_two_eq_zero_or_one (idx12Fin.val / 2 ^ k) with hm | hm <;> simp [hm]
    have hbx (i : ℕ) (hi : i < 8) :
        bit01Nat (β₀ (idx12Loc ⟨i, by omega⟩)) = x.val / 2 ^ i % 2 := by
      have hw : (idx12Loc ⟨i, by omega⟩).val = i := by
        rw [show (⟨i, by omega⟩ : Fin 12) = Fin.castAdd 4 ⟨i, hi⟩ from rfl, idx12Loc,
          QRegister.concat_apply_left]; simp [rXoLoc]
      have hr : β₀ (idx12Loc ⟨i, by omega⟩) = basisBits 8 x8 ⟨i, hi⟩ := by
        dsimp [β₀, inputBits]; simp [hw, hi]
      rw [hr, basisBits_eq_div_mod]; dsimp [bit01Nat, x8]
      rcases Nat.mod_two_eq_zero_or_one (x.val / 2 ^ i) with hm | hm <;> simp [hm]
    have hbc (j : ℕ) (hj : j < 4) :
        bit01Nat (β₀ (idx12Loc ⟨8 + j, by omega⟩)) = c.val / 2 ^ j % 2 := by
      have hw : (idx12Loc ⟨8 + j, by omega⟩).val = 12 + j := by
        rw [show (⟨8 + j, by omega⟩ : Fin 12) = Fin.natAdd 8 ⟨j, hj⟩ from Fin.ext (by simp),
          idx12Loc, QRegister.concat_apply_right, kLoc_apply_val]
      have hr : β₀ (idx12Loc ⟨8 + j, by omega⟩) = basisBits 4 c ⟨j, hj⟩ := by
        dsimp [β₀, inputBits]
        simp [hw, show ¬ 12 + j < 8 by omega, show 12 ≤ 12 + j ∧ 12 + j < 16 by omega]
      rw [hr, basisBits_eq_div_mod]; dsimp [bit01Nat]
      rcases Nat.mod_two_eq_zero_or_one (c.val / 2 ^ j) with hm | hm <;> simp [hm]
    have hx_lt := x.isLt; have hc_lt := c.isLt; have hidx_lt := idx12Fin.isLt
    have hsplit : idx12 = x.val + 256 * c.val :=
      nat_eq_of_div_pow2_mod_eq 12 idx12 (x.val + 256 * c.val) hidx_lt (by omega) fun k hk ↦ by
        by_cases hk8 : k < 8
        · rw [← hb12 k hk, hbx k hk8]; interval_cases k <;> omega
        · rw [← hb12 k hk,
            show (⟨k, hk⟩ : Fin 12) = ⟨8 + (k - 8), by omega⟩ from Fin.ext (by dsimp; omega),
            hbc (k - 8) (by omega)]; interval_cases k <;> omega
    exact ⟨by omega, by omega⟩
  set kv : Fin 1024 := ⟨(pi145CompactTable x).keep, pi145CompactTable_keep_lt x⟩
  set mk : ZMod 2 := pktKeepSel10 (basisBits 10 kv) (basisBits 4 c)
  have hRow (j : Fin 4) :
      alt4BoolTable (localIdx idx12Loc β₀).val j = (loadedAlt4Bits x mk j == 1) := by
    dsimp only [alt4BoolTable]; simp only [hIdxSplit.1, hIdxSplit.2]
    have hg : DyadicXMeasPrepOut13.effGroup (x.val / 4) = ⟨x.val / 4, by omega⟩ := by
      dsimp [DyadicXMeasPrepOut13.effGroup]
      ext; simp [Nat.mod_eq_of_lt (by omega : x.val / 4 < 64), show x.val / 4 < 46 by omega]
    have hy : (⟨4 * (DyadicXMeasPrepOut13.effGroup (x.val / 4)).val + x.val % 4,
        by have := (DyadicXMeasPrepOut13.effGroup (x.val / 4)).isLt; omega⟩ : Fin 184) = x := by
      apply Fin.ext; dsimp only; rw [hg]; dsimp only; omega
    have hkv : (⟨(pi145CompactTable x).keep % 1024, Nat.mod_lt _ (by decide)⟩ : Fin 1024) = kv :=
      Fin.ext (Nat.mod_eq_of_lt kv.isLt)
    simp only [hy, hkv, show (⟨c.val, by omega⟩ : Fin 16) = c from rfl]; rfl
  set β₁ := gromXor17Bits β₀
  have hβ₁_xo (i : Fin 8) : β₁ (rXoLoc 8 i) = basisBits 8 x8 i := by
    dsimp only [β₁, gromXor17Bits]; rw [xorRegBits_apply_of_not_mem]
    · dsimp [β₀, inputBits, rXoLoc]; simp [i.isLt]
    · intro hm; obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
      have := congrArg Fin.val hj
      simp only [alt4Loc_apply_val, rXoLoc] at this; dsimp at this; omega
  have hβ₁_alt (j : Fin 4) : β₁ (alt4Loc j) = loadedAlt4Bits x mk j := by
    dsimp only [β₁, gromXor17Bits]; rw [xorRegBits_apply_reg, hRow j]
    have hj := j.isLt
    have h0 : β₀ (alt4Loc j) = 0 := by
      dsimp only [β₀, inputBits]
      simp only [show ¬ (alt4Loc j).val < 8 by rw [alt4Loc_apply_val]; omega,
        show ¬ (12 ≤ (alt4Loc j).val ∧ (alt4Loc j).val < 16) by rw [alt4Loc_apply_val]; omega,
        show (alt4Loc j).val ≠ 16 by rw [alt4Loc_apply_val]; omega, ↓reduceDIte, ↓reduceIte]
    rw [h0, zero_add]; rcases bit_cases (loadedAlt4Bits x mk j) with hb | hb <;> simp [hb]
  set β₂ := postPerm17Bits β₀
  have hβ₂_xo (i : Fin 8) :
      β₂ (rXoLoc 8 i) = postCswapXoBits (basisBits 8 x8) (loadedAlt4Bits x mk) i := by
    have hr : rXoLoc 8 i = xoAlt12Loc ⟨i.val, by omega⟩ :=
      Fin.ext (by simp [rXoLoc, xoAlt12Loc])
    dsimp only [β₂, postPerm17Bits, gromCswap17Bits]
    rw [hr, writeReg_apply_reg]
    have hγx (p : Fin 8) : β₁ (xoAlt12Loc ⟨p.val, by omega⟩) = basisBits 8 x8 p := by
      rw [show xoAlt12Loc ⟨p.val, by omega⟩ = rXoLoc 8 p from
        Fin.ext (by simp [rXoLoc, xoAlt12Loc])]; exact hβ₁_xo p
    have hγa (j : Fin 4) : β₁ (xoAlt12Loc ⟨8 + j.val, by omega⟩) = loadedAlt4Bits x mk j := by
      rw [show xoAlt12Loc ⟨8 + j.val, by omega⟩ = alt4Loc j from
        Fin.ext (by simp [xoAlt12Loc, alt4Loc_apply_val])]; exact hβ₁_alt j
    have hg7 : β₁ (xoAlt12Loc 7) = basisBits 8 x8 7 := hγx 7
    have hg6 : β₁ (xoAlt12Loc 6) = basisBits 8 x8 6 := hγx 6
    have hg11 : β₁ (xoAlt12Loc 11) = loadedAlt4Bits x mk 3 := hγa 3
    have hg10 : β₁ (xoAlt12Loc 10) = loadedAlt4Bits x mk 2 := hγa 2
    unfold postCswapXoBits cswapGuardBit; dsimp only [cswap12Bits]
    dsimp only [β₁] at hg7 hg6 hg11 hg10 hγx hγa
    rw [hg7, hg6, hg11, hg10]
    by_cases hen : (1 + basisBits 8 x8 7 * basisBits 8 x8 6 +
        loadedAlt4Bits x mk 3 * loadedAlt4Bits x mk 2 : ZMod 2) = 1
    · simp only [hen, ↓reduceIte]
      fin_cases i
      · exact hγx 0
      · exact hγx 1
      · exact hγa 0
      · exact hγa 1
      · exact hγx 4
      · exact hγx 5
      · rfl
      · rfl
    · simp only [hen, ↓reduceIte]; exact hγx i
  have hβ₂_xo_vec : (fun i ↦ β₂ (rXoLoc 8 i)) =
      basisBits 8 ⟨(routedIdx x c).val, by have := (routedIdx x c).isLt; omega⟩ := by
    rw [funext hβ₂_xo]
    rcases bit_cases mk with hmk | hmk
    · have hsw : pktSwapBit10 kv c = 1 := by change 1 + mk = 1; rw [hmk]; decide
      have hrt : routedIdx x c = if false then x else (pi145CompactTable x).alt := by
        unfold routedIdx; dsimp only; rw [hsw, ite_eq_right one_ne_zero]; rfl
      exact ((congrArg (postCswapXoBits (basisBits 8 x8))
        (congrArg (loadedAlt4Bits x) hmk)).trans (postCswap_route_eq x false)).trans
        (congrArg (basisBits 8) (Fin.ext (congrArg (Fin.val (n := 184)) hrt.symm)))
    · have hsw : pktSwapBit10 kv c = 0 := by change 1 + mk = 0; rw [hmk]; decide
      have hrt : routedIdx x c = if true then x else (pi145CompactTable x).alt := by
        unfold routedIdx; dsimp only; rw [hsw, ite_eq_left rfl]; rfl
      exact ((congrArg (postCswapXoBits (basisBits 8 x8))
        (congrArg (loadedAlt4Bits x) hmk)).trans (postCswap_route_eq x true)).trans
        (congrArg (basisBits 8) (Fin.ext (congrArg (Fin.val (n := 184)) hrt.symm)))
  refine ⟨?_, ?_⟩
  · have hxo_eq : (rXoLoc 8).extractIndex o =
        ⟨(routedIdx x c).val, by have := (routedIdx x c).isLt; omega⟩ := by
      apply (basisBits 8).injective; funext i
      rw [QRegister.basisBits_extractIndex]; dsimp only [o]
      rw [basisBits_symm]; exact congrFun hβ₂_xo_vec i
    exact congrArg Fin.val hxo_eq
  · apply (basisBits 1).injective; funext i
    rw [QRegister.basisBits_extractIndex]; dsimp only [o]; rw [basisBits_symm]
    fin_cases i; dsimp only
    change β₂ (rSigOutLoc 8 0) = basisBits 1 s 0
    rw [show rSigOutLoc 8 0 = spinWire by decide]
    have h2 : β₂ spinWire = β₁ spinWire := by
      dsimp only [β₂, postPerm17Bits, gromCswap17Bits]; apply writeReg_apply_of_not_mem
      rintro ⟨p, hp⟩; have := congrArg Fin.val hp
      simp only [xoAlt12Loc, spinWire] at this; dsimp at this; omega
    have h3 : β₁ spinWire = β₀ spinWire := by
      dsimp only [β₁, gromXor17Bits]; apply xorRegBits_apply_of_not_mem
      intro hm; obtain ⟨p, hp⟩ := (QRegister.mem_image _ _).mp hm
      have := congrArg Fin.val hp; simp only [alt4Loc_apply_val, spinWire] at this; omega
    have h4 : β₀ spinWire = (s.val : ZMod 2) := by
      dsimp only [β₀, inputBits, spinWire]; simp
    rw [h2, h3, h4]
    fin_cases s <;> decide

theorem prepOutValidForWeightsOuter8PrepOutWordIdeal (W_ideal : Unitary (2 ^ 1))
    (hW : Complex.normSq (W_ideal.1 0 0) = 8 / 23) :
    CompactBilinearPrep.PrepOutValidForWeights
      (outerWeightNatPerm pi145Per) (outer8PrepOutWordIdeal W_ideal) := by
  let u₂ := prepGroverUnitary 3 5 23 W_ideal
  let uPost : Unitary (2 ^ 17) := xoAlt12Loc.embedUnitary cswap12Unitary *
    idxAlt16Loc.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)
  have huPost (γ : BitAssignment 17) : uPost.1.mulVec (ket γ) = ket (postPerm17Bits γ) := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, gromXor17_mulVec_ket, gromCswap17_mulVec_ket]
    rfl
  have hU : outer8PrepOutWordIdeal W_ideal = uPost * (kLoc.embedUnitary orthCoin10Unitary *
      (Circuit.H spinWire).eval * (nonAlt13Loc.compose nonAltXoAuxReg).embedUnitary u₂) := by
    unfold outer8PrepOutWordIdeal outer8PrepOutUnit; rw [nonAlt13Loc_embedInit13Unitary]
  have hcol_eq (j : Fin (2 ^ (3 + 5 + 1))) : u₂.1 j 0 = (u₂.1 *ᵥ Pi.single 0 1) j := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  have hp_id : ((23 : ℕ) : ℝ) / (2 ^ 5 : ℝ) * Complex.normSq (W_ideal.1 0 0) = 1 / 4 := by
    rw [hW]; norm_num
  have hpow8 : ((1 / √2 : ℝ) ^ (3 + 5) : ℝ) = 1 / 16 := by
    rw [show (3 + 5 : ℕ) = 2 * 4 from rfl, pow_mul, div_pow, one_pow,
      Real.sq_sqrt (by norm_num)]; norm_num
  have hu2_hi (x : Fin (2 ^ 8)) : u₂.1 (hi512 x) 0 = 0 := by
    rw [hcol_eq]
    have h := prepGroverUnitary_mulVec_zero_of_ge_two_pow 3 5 23 (by decide) W_ideal
      (hi512 x) (by dsimp [hi512]; omega)
    dsimp only at h; rw [h, hp_id]; norm_num
  have hu2_bad (x : Fin (2 ^ 8)) (hx : ¬ x.val < 184) : u₂.1 (lo512 x) 0 = 0 := by
    rw [hcol_eq]
    have h := prepGroverUnitary_mulVec_zero_of_mid 3 5 23 (by decide) W_ideal
      (lo512 x) (by dsimp [lo512]; omega) (by dsimp [lo512]; exact x.isLt)
    dsimp only at h; rw [h, hp_id]; norm_num
  have hu2_good (x : Fin (2 ^ 8)) (hx : x.val < 184) :
      Complex.normSq (u₂.1 (lo512 x) 0) = 1 / 184 := by
    rw [hcol_eq, prepGroverUnitary_mulVec_zero_of_lt 3 5 23 (by decide) W_ideal
      (lo512 x) (by dsimp [lo512]; omega)]
    dsimp only [prepGoodAmp]
    rw [hp_id, hpow8, map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, hW]; norm_num
  let idx : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → Fin (2 ^ 17) := fun t ↦
    (basisBits 17).symm (postPerm17Bits (inBits17 t.1 t.2.1 t.2.2))
  have hidx : Function.Injective idx :=
    (basisBits 17).symm.injective.comp (postPerm17Bits_injective.comp inBits17_injective)
  let amp : Fin (2 ^ 8) × Fin 2 × Fin (2 ^ 4) → ℂ := fun t ↦
    (u₂.1 (lo512 t.1) 0 * orthCoin10Unitary.1 t.2.2 0 +
      u₂.1 (hi512 t.1) 0 * orthCoin10Unitary.1 t.2.2 jAux4) * sqrtHalf
  have hCol (o : Fin (2 ^ mOutUB 8)) :
      (outer8PrepOutWordIdeal W_ideal).1 o 0 = ∑ t, if idx t = o then amp t else 0 := by
    rw [hU]
    exact wouter8InitPost_col0 (nonAlt13Loc.compose nonAltXoAuxReg) kLoc spinWire
      (fun i ↦ by fin_cases i <;> decide) (by decide) (fun j ↦ by fin_cases j <;> decide) rfl
      orthCoin10Unitary uPost postPerm17Bits huPost u₂ o
  refine ⟨fun o ho ↦ ?_, fun xo so ↦ ?_⟩
  · rw [hCol o]
    refine Finset.sum_eq_zero fun t _ ↦ ite_eq_right_iff.mpr fun hto ↦ ?_
    by_cases hx : t.1.val < 184
    · have hex := (postPerm17Bits_extract ⟨t.1.val, hx⟩ t.2.1 t.2.2).1
      have hid : idx t = (basisBits (mOutUB 8)).symm
          (postPerm17Bits (inputBits ⟨t.1.val, by omega⟩ t.2.1 t.2.2)) := rfl
      rw [← hid, hto] at hex
      have := (routedIdx ⟨t.1.val, hx⟩ t.2.2).isLt; omega
    · change (u₂.1 (lo512 t.1) 0 * orthCoin10Unitary.1 t.2.2 0 +
        u₂.1 (hi512 t.1) 0 * orthCoin10Unitary.1 t.2.2 jAux4) * sqrtHalf = 0
      rw [hu2_bad t.1 hx, hu2_hi t.1, zero_mul, zero_mul, add_zero, zero_mul]
  · have hns_entry (o : Fin (2 ^ mOutUB 8)) :
        Complex.normSq ((outer8PrepOutWordIdeal W_ideal).1 o 0) =
          ∑ t, if idx t = o then Complex.normSq (amp t) else 0 := by
      rw [hCol o]
      by_cases hex : ∃ t₀, idx t₀ = o
      · obtain ⟨t₀, ht₀⟩ := hex
        have hs1 : (∑ t, if idx t = o then amp t else 0) = amp t₀ := by
          rw [Finset.sum_eq_single t₀]; · simp [ht₀]
          · intro t _ hne; exact ite_eq_right fun h ↦ hne (hidx (h.trans ht₀.symm))
          · intro habs; exact absurd (Finset.mem_univ t₀) habs
        have hs2 : (∑ t, if idx t = o then Complex.normSq (amp t) else 0) =
            Complex.normSq (amp t₀) := by
          rw [Finset.sum_eq_single t₀]; · simp [ht₀]
          · intro t _ hne; exact ite_eq_right fun h ↦ hne (hidx (h.trans ht₀.symm))
          · intro habs; exact absurd (Finset.mem_univ t₀) habs
        rw [hs1, hs2]
      · have hall : ∀ t, idx t ≠ o := fun t h ↦ hex ⟨t, h⟩
        simp [hall]
    let P : Fin (2 ^ mOutUB 8) → Prop := fun o ↦
      ((rXoLoc 8).extractIndex o).val = xo.val ∧ (rSigOutLoc 8).extractIndex o = so
    change (∑ o ∈ Finset.univ.filter P, _) = _
    rw [Finset.sum_filter]; simp_rw [hns_entry]
    have hswap : (∑ o : Fin (2 ^ mOutUB 8),
          if P o then ∑ t, (if idx t = o then Complex.normSq (amp t) else 0) else 0) =
        ∑ t, if P (idx t) then Complex.normSq (amp t) else 0 := by
      have hite (o : Fin (2 ^ mOutUB 8)) :
          (if P o then ∑ t, (if idx t = o then Complex.normSq (amp t) else 0) else 0) =
            ∑ t, if idx t = o then (if P o then Complex.normSq (amp t) else 0) else 0 := by
        by_cases hP : P o <;> simp [hP]
      simp_rw [hite]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun t _ ↦ by simp
    rw [hswap, Fintype.sum_prod_type]
    let e256 : Fin (184 + 72) ≃ Fin (2 ^ 8) := finCongr (by decide)
    rw [← e256.sum_comp, Fin.sum_univ_add]
    have htail : (∑ i : Fin 72, ∑ sc : Fin 2 × Fin (2 ^ 4),
        if P (idx (e256 (Fin.natAdd 184 i), sc)) then
          Complex.normSq (amp (e256 (Fin.natAdd 184 i), sc)) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun sc _ ↦ ?_
      have hx : ¬ (e256 (Fin.natAdd 184 i)).val < 184 := by simp [e256, Fin.natAdd]
      dsimp only [amp]; rw [hu2_bad _ hx, hu2_hi, zero_mul, zero_mul, add_zero, zero_mul,
        Complex.normSq_zero, ite_self]
    rw [htail, add_zero]
    have hsh : Complex.normSq sqrtHalf = 1 / 2 := by
      unfold sqrtHalf; rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    have hamp (x : Fin 184) (s : Fin 2) (c : Fin (2 ^ 4)) :
        Complex.normSq (amp (e256 (Fin.castAdd 72 x), s, c)) =
          (coin10Weight c : ℝ) / (2 * 188416) := by
      have hx : (e256 (Fin.castAdd 72 x)).val < 184 := by simp [e256, Fin.castAdd]
      dsimp only [amp]
      rw [hu2_hi, zero_mul, add_zero, Complex.normSq_mul, Complex.normSq_mul,
        hu2_good _ hx, orthCoin10Unitary_col_zero_normSq c, hsh]
      ring
    have hP_idx (x : Fin 184) (s : Fin 2) (c : Fin (2 ^ 4)) :
        P (idx (e256 (Fin.castAdd 72 x), s, c)) ↔ routedIdx x c = xo ∧ s = so := by
      have heq : e256 (Fin.castAdd 72 x) = ⟨x.val, by omega⟩ := rfl
      rw [heq]
      obtain ⟨hxo, hso⟩ := postPerm17Bits_extract x s c
      have hid : idx (⟨x.val, by omega⟩, s, c) = (basisBits (mOutUB 8)).symm
          (postPerm17Bits (inputBits ⟨x.val, by omega⟩ s c)) := rfl
      dsimp only [P]; rw [hid, hxo, hso]
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨Fin.ext h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨congrArg Fin.val h1, h2⟩⟩
    simp_rw [Fintype.sum_prod_type, hP_idx, hamp]
    have hrow (x : Fin 184) :
        (∑ s : Fin 2, ∑ c : Fin (2 ^ 4),
          if routedIdx x c = xo ∧ s = so then (coin10Weight c : ℝ) / (2 * 188416) else 0) =
        (((if x = xo then (pi145CompactTable x).keep else 0) +
          (if (pi145CompactTable x).alt = xo then 1024 - (pi145CompactTable x).keep else 0) :
            ℕ) : ℝ) / (2 * 188416) := by
      have hs_elim : (∑ s : Fin 2, ∑ c : Fin (2 ^ 4),
            if routedIdx x c = xo ∧ s = so then (coin10Weight c : ℝ) / (2 * 188416) else 0) =
          ∑ c : Fin (2 ^ 4),
            if routedIdx x c = xo then (coin10Weight c : ℝ) / (2 * 188416) else 0 := by
        fin_cases so <;> simp [Fin.sum_univ_two]
      rw [hs_elim]
      set kv : Fin 1024 := ⟨(pi145CompactTable x).keep, pi145CompactTable_keep_lt x⟩
      have hsplit (c : Fin (2 ^ 4)) :
          (if routedIdx x c = xo then (coin10Weight c : ℝ) / (2 * 188416) else 0) =
          (((if x = xo then if pktSwapBit10 kv c = 0 then coin10Weight c else 0 else 0) +
            (if (pi145CompactTable x).alt = xo then
              if pktSwapBit10 kv c ≠ 0 then coin10Weight c else 0 else 0) : ℕ) : ℝ) /
            (2 * 188416) := by
        set m := pktSwapBit10 kv c
        change (if (if m = 0 then x else (pi145CompactTable x).alt) = xo then
            (coin10Weight c : ℝ) / (2 * 188416) else 0) = _
        by_cases hm : m = 0
        · rw [hm]; by_cases hx : x = xo <;>
            simp only [hx, ↓reduceIte, ne_eq, not_true_eq_false, ite_self, add_zero,
              Nat.cast_zero, zero_div]
        · by_cases ha : (pi145CompactTable x).alt = xo <;>
            simp only [hm, ha, ↓reduceIte, ne_eq, not_false_eq_true, ite_self, zero_add,
              Nat.cast_zero, zero_div]
      simp_rw [hsplit, ← Finset.sum_div, ← Nat.cast_sum, Finset.sum_add_distrib]
      have hz : (∑ c : Fin (2 ^ 4),
          if x = xo then if pktSwapBit10 kv c = 0 then coin10Weight c else 0 else 0) =
          if x = xo then (pi145CompactTable x).keep else 0 := by
        by_cases hx : x = xo
        · simp only [ite_eq_left hx]; exact sumCoin10Weight_keep kv
        · simp only [ite_eq_right hx, Finset.sum_const_zero]
      have ho1 : (∑ c : Fin (2 ^ 4),
          if (pi145CompactTable x).alt = xo then
            if pktSwapBit10 kv c ≠ 0 then coin10Weight c else 0 else 0) =
          if (pi145CompactTable x).alt = xo then 1024 - (pi145CompactTable x).keep else 0 := by
        by_cases ha : (pi145CompactTable x).alt = xo
        · simp only [ite_eq_left ha]; exact sumCoin10Weight_swap kv
        · simp only [ite_eq_right ha, Finset.sum_const_zero]
      rw [hz, ho1]
    simp_rw [hrow, ← Finset.sum_div, ← Nat.cast_sum, Finset.sum_add_distrib]
    have hKeepSum : (∑ x : Fin 184, if x = xo then (pi145CompactTable x).keep else 0) =
        (pi145CompactTable xo).keep := by simp
    rw [hKeepSum, pi145CompactTable_weight_eq xo]

theorem prepOutValidPerseOuter8PrepOutWordIdeal (W_ideal : Unitary (2 ^ 1))
    (hW : Complex.normSq (W_ideal.1 0 0) = 8 / 23) :
    PrepOutValidPerm256 pi145Perm (outer8PrepOutWordIdeal W_ideal) :=
  prepOutValidPerm256_extPerm256_of_weights pi145Per
    (prepOutValidForWeightsOuter8PrepOutWordIdeal W_ideal hW)

/-- Canonical ideal `wOuter = 8` support-disjoint outer `PREP` unitary (`|W_{0,0}|² = 8 / 23`). -/
abbrev outer8PrepOutIdeal : Unitary (2 ^ mOutUB 8) :=
  outer8PrepOutWordIdeal FastCleanUnif184.mag8To23IdealUnitary

theorem prepOutValidPerseOuter8PrepOutIdeal :
    PrepOutValidPerm256 pi145Perm outer8PrepOutIdeal :=
  prepOutValidPerseOuter8PrepOutWordIdeal _
    FastCleanUnif184.normSqMag8To23IdealUnitary_zero_zero

theorem sum_abs_normSqOuter8PrepOutWordImpl_sub_eq
    (rotWord : List Gate1) (W_id : Unitary (2 ^ 1))
    (hWid : Complex.normSq (W_id.1 0 0) = 8 / 23) :
    (∑ o' : Fin (2 ^ mOutUB 8),
      |Complex.normSq ((outer8PrepOutWordImpl rotWord).1 o' 0) -
        Complex.normSq ((outer8PrepOutWordIdeal W_id).1 o' 0)|) =
      orthGrover184L1Exact (wordToCircuit1 rotWord).eval := by
  let uPost : Unitary (2 ^ 17) := xoAlt12Loc.embedUnitary cswap12Unitary *
    idxAlt16Loc.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)
  have huPost (γ : BitAssignment 17) : uPost.1.mulVec (ket γ) = ket (postPerm17Bits γ) := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, gromXor17_mulVec_ket, gromCswap17_mulVec_ket]
    rfl
  have hU (u : Unitary (2 ^ 9)) :
      outer8PrepOutUnit u = uPost * (kLoc.embedUnitary orthCoin10Unitary *
        (Circuit.H spinWire).eval * (nonAlt13Loc.compose nonAltXoAuxReg).embedUnitary u) := by
    unfold outer8PrepOutUnit; rw [nonAlt13Loc_embedInit13Unitary]
  change (∑ o' : Fin (2 ^ 17),
    |Complex.normSq ((outer8PrepOutUnit (prepGroverUnitary 3 5 23
        (wordToCircuit1 rotWord).eval)).1 o' 0) -
      Complex.normSq ((outer8PrepOutUnit (prepGroverUnitary 3 5 23 W_id)).1 o' 0)|) = _
  rw [hU, hU]
  exact sum_abs_normSq_wouter8OrthCoin10_postPerm_eq
    (nonAlt13Loc.compose nonAltXoAuxReg) kLoc spinWire
    (fun i ↦ by fin_cases i <;> decide) (by decide) (fun j ↦ by fin_cases j <;> decide) rfl
    uPost postPerm17Bits postPerm17Bits_injective huPost
    (wordToCircuit1 rotWord).eval W_id hWid

end

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Compact2RotOuter

end

/-!
# `rXo7`-Borrowing `252-T` Context-Borrowing Inner `PREP_mid` Engine
Generic `(sliceFn, π128, kScr, qromLoad)` `rXo7`-borrowing inner `PREP_mid` and `252-T`
`withHot128Dyn` turnaround (Babbush et al., PRX 8, 041015, 2018; Gidney, Quantum 2, 74, 2018;
Low, Kliuchnikov, and Schaeffer, Quantum 8, 1375, 2024).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepBound148Borrow
open QuantumComputation.Specs QuantumComputation.Specs.P450
noncomputable section
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open CoherentAlias AliasPrep Phase2MidSandwich OptFactoredMag30AndCoin9
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge MidReflCtxRetain
open GroupUnary (RevCompute predProj restrictPred restrictPred_coe predProj_conjTranspose)
open SelectSwapQROM (zeroProjOn zeroProjOn_conjTranspose zeroProjOn_mulVec_ket
  CleanRealizesSet cleanRealizes_iff_set disjoint_image_of_disjointWires
  basisOutcomeProjector_zero_eq_zeroProjOn)
open StepOuter8Pi145Outer (WSplitValid InvWSplitDet splitRevLoop splitRevLoop_spec
  cswapRangeBits cswapRangeBits_w0 cswapRangeBits_w1 cswapRangeBits_other bit01Nat
  dWExpandDet1 EquivRev TransRealizes predProj_mulVec_ket
  restrictAssertionToZeroAncilla_eq_restrictPred restrictPred_restrictPred
  cleanRealizes_of_transRealizes conjTranspose_eq_self_of_mul_self)
open Lac2Folded184Select (revComputeDyn revUncomputeDyn count_revComputeDyn_toff
  count_revUncomputeDyn_toff count_revUncomputeDyn_t)
open Solution.CircuitModular.UnsignedGivens (maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket
  eval_identity_mulVec)
open QRegister (mem_image disjointWires_concat_right disjointWires_concat_left concat_apply_left
  concat_apply_right slice_apply embedUnitary_one embedUnitary_val embedMatrix_one
  sum_basisOutcomeProjector basisBits_extractIndex image_compose_subset)
open Function (update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-- Wire-relabeling `QRegister k k` induced by `α : Equiv.Perm (Fin k)`. -/
def permLocalReg {k : ℕ} (α : Equiv.Perm (Fin k)) : QRegister k k := ⟨⟨α, α.injective⟩⟩
@[simp] theorem permLocalReg_apply {k : ℕ} (α : Equiv.Perm (Fin k)) (i : Fin k) : permLocalReg α
  i = α i := rfl
/-- `0-T` wire-permuted `128`-qubit one-hot register `c ↦ rHot (π128.symm c)`. -/
abbrev hotPermReg {N : ℕ} (π128 : Equiv.Perm (Fin (2 ^ 7))) (rHot : QRegister 128 N) : QRegister
  128 N := rHot.compose (permLocalReg π128.symm)
/-- Coordinate permutation on `Fin (7 + 128)` fixing `0..6` and permuting `7..134` by `π128.symm`.
-/
def ctrlPer (π128 : Equiv.Perm (Fin (2 ^ 7))) : Equiv.Perm (Fin (7 + 128)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin 7)) π128.symm).trans finSumFinEquiv)
theorem concatHotPermReg_eq_compose {N : ℕ} (π128 : Equiv.Perm (Fin (2 ^ 7))) (rXo7 : QRegister 7
    N) (rHot : QRegister 128 N) (hXoHot : rXo7.DisjointWires rHot) : rXo7.concat (hotPermReg π128
    rHot) (hXoHot.compose_right _) = (rXo7.concat rHot hXoHot).compose (permLocalReg
    (ctrlPer π128)) := by
  apply CoherentAlias.qreg_ext; intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change ((rXo7.concat (hotPermReg π128 rHot) _) (Fin.castAdd 128 i)).val =
      ((rXo7.concat rHot hXoHot) (ctrlPer π128 (finSumFinEquiv (Sum.inl i)))).val
    rw [show ctrlPer π128 (finSumFinEquiv (Sum.inl i)) = Fin.castAdd 128 i by
      simp [ctrlPer]; rfl, concat_apply_left, concat_apply_left]
  · change ((rXo7.concat (hotPermReg π128 rHot) _) (Fin.natAdd 7 j)).val =
      ((rXo7.concat rHot hXoHot) (ctrlPer π128 (finSumFinEquiv (Sum.inr j)))).val
    rw [show ctrlPer π128 (finSumFinEquiv (Sum.inr j)) = Fin.natAdd 7 (π128.symm j) by
      simp [ctrlPer]; rfl, concat_apply_right, concat_apply_right]; rfl
theorem embedUnitary_muxOnAct_permCtrl {n k_t k_c : ℕ} [NeZero (2 ^ n)] (rTgt : QRegister k_t n)
    (rCtrl : QRegister k_c n) (α : Equiv.Perm (Fin k_c)) (hdisj0 : rTgt.DisjointWires rCtrl) (G :
    (Fin k_c → Bool) → Unitary (2 ^ k_t)) : (rTgt.concat (rCtrl.compose (permLocalReg α))
    (hdisj0.compose_right _)).embedUnitary (muxOnAct k_t k_c G) = (rTgt.concat rCtrl
    hdisj0).embedUnitary (muxOnAct k_t k_c (fun z ↦ G (fun j ↦ z (α j)))) := by
  rw [embedUnitary_muxOnAct, embedUnitary_muxOnAct]
  let ePerm : Equiv.Perm (Fin (2 ^ k_c)) :=
    { toFun := fun c ↦ finOfBits k_c (fun i ↦ bitsOfFin k_c c (α.symm i))
      invFun := fun c0 ↦ finOfBits k_c (fun j ↦ bitsOfFin k_c c0 (α j))
      left_inv := fun c ↦ by simp [bitsOfFin_finOfBits, finOfBits_bitsOfFin]
      right_inv := fun c0 ↦ by simp [bitsOfFin_finOfBits, finOfBits_bitsOfFin] }
  have hExPerm (c0 : Fin (2 ^ k_c)) : (permLocalReg α).extractIndex c0 = ePerm.symm c0 := by
    have hbits : bitsOfFin k_c ((permLocalReg α).extractIndex c0) =
        fun j ↦ bitsOfFin k_c c0 (α j) := by
      funext j; dsimp only [bitsOfFin, permLocalReg]; rw [basisBits_extractIndex]; rfl
    rw [← finOfBits_bitsOfFin k_c ((permLocalReg α).extractIndex c0), hbits]; rfl
  have hProj (c : Fin (2 ^ k_c)) : (rCtrl.compose (permLocalReg α)).basisOutcomeProjector c =
      rCtrl.basisOutcomeProjector (ePerm c) := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
    congr 1; funext g; rw [QRegister.extractIndex_compose, hExPerm]
    have hiff : (ePerm.symm (rCtrl.extractIndex g) = c) ↔ rCtrl.extractIndex g = ePerm c :=
      ⟨fun h ↦ by rw [← h, ePerm.apply_symm_apply], fun h ↦ by rw [h, ePerm.symm_apply_apply]⟩
    by_cases hc : rCtrl.extractIndex g = ePerm c
    · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
    · rw [ite_eq_right (mt hiff.mp hc), ite_eq_right hc]
  apply Subtype.ext; dsimp only [muxUnitary]; simp_rw [hProj]
  refine (Equiv.sum_comp ePerm.symm (fun c ↦
    rCtrl.basisOutcomeProjector (ePerm c) * rTgt.embedMatrix (G (bitsOfFin k_c c)).1)).symm.trans ?_
  refine Finset.sum_congr rfl fun c0 _ ↦ ?_
  rw [ePerm.apply_symm_apply]; simp only [ePerm, Equiv.coe_fn_symm_mk, bitsOfFin_finOfBits]
/-- Coupled one-hot predicate on `(rXo, rHot)`: `rHot` holds `|e_{localIdx rXo β}⟩`. -/
def xoOneHotPred {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N) (β : BitAssignment N) : Bool
  :=
    decide (∀ g : Fin 128,
    β (rHot g) = if g = Solution.CircuitModular.UnsignedGivens.localIdx rXo β then 1 else 0)
theorem xoOneHotPred_implies_oneHotPred {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N) (β :
    BitAssignment N) (h : xoOneHotPred rXo rHot β = true) : oneHotPred rHot β = true := by
  unfold xoOneHotPred at h
  unfold oneHotPred
  exact decide_eq_true ⟨Solution.CircuitModular.UnsignedGivens.localIdx rXo β, of_decide_eq_true h⟩
/-- Bit `b` mask on `Fin 128` (`c ↦ c.testBit b`). -/
def xoBitMask128 (b : Fin 7) (c : Fin 128) : Bool := decide (c.val / 2 ^ b.val % 2 = 1)
/-- `0-T`, `0-TOFF` CNOT fan-in circuit clearing `rXo` (`7` wires) from one-hot `rHot` (`128`). -/
def xo7ClearLoop {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
    (hXoHot : rXo.DisjointWires rHot) : (k : ℕ) → k ≤ 7 → Circuit N
  | 0, _ => .identity
  | k + 1, hk =>
      xo7ClearLoop rXo rHot hXoHot k (by omega) ;;ᶜ cnotMaskReg 128 rHot (rXo ⟨k, hk⟩) (xoBitMask128
        ⟨k, hk⟩) (fun c ↦ (hXoHot.ne ⟨k, hk⟩ c).symm)
/-- Public `0-T`, `0-TOFF` circuit clearing/restoring `rXo` (`7` wires) from live `rHot`. -/
def xo7OneHotClearCirc {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N) (hXoHot :
  rXo.DisjointWires rHot) : Circuit N := xo7ClearLoop rXo rHot hXoHot 7 le_rfl
theorem count_xo7ClearLoop_zero {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
    (hXoHot : rXo.DisjointWires rHot) :
    ∀ (k : ℕ) (hk : k ≤ 7), (xo7ClearLoop rXo rHot hXoHot k hk).count .TOFF = 0 ∧ (xo7ClearLoop rXo
      rHot hXoHot k hk).count .T = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      obtain ⟨h1, h2⟩ := count_xo7ClearLoop_zero rXo rHot hXoHot k (by omega); rw [xo7ClearLoop]
      exact ⟨by simp [Circuit.count_seq, h1], by simp [Circuit.count_seq, h2]⟩
@[simp] theorem count_xo7OneHotClearCirc_toff {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
  (hXoHot : rXo.DisjointWires rHot) : (xo7OneHotClearCirc rXo rHot hXoHot).count .TOFF = 0 :=
  (count_xo7ClearLoop_zero rXo rHot hXoHot 7 le_rfl).1
@[simp] theorem count_xo7OneHotClearCirc_t {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
  (hXoHot : rXo.DisjointWires rHot) : (xo7OneHotClearCirc rXo rHot hXoHot).count .T = 0 :=
  (count_xo7ClearLoop_zero rXo rHot hXoHot 7 le_rfl).2
/-- Bit-assignment transformer induced by `xo7ClearLoop rXo rHot hXoHot k hk`. -/
def xo7ClearLoopBits {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N) (k : ℕ) (β :
    BitAssignment N) : BitAssignment N :=
  writeReg β rXo fun b ↦
    if b.val < k then β (rXo b) + maskSumBit rHot (xoBitMask128 b) β else β (rXo b)
theorem ket_xo7ClearLoop {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
    (hXoHot : rXo.DisjointWires rHot) :
    ∀ (k : ℕ) (hk : k ≤ 7) (β : BitAssignment N), (xo7ClearLoop rXo rHot hXoHot k hk).eval.1.mulVec
      (Solution.CircuitModular.UnsignedGivens.ket β) =
        Solution.CircuitModular.UnsignedGivens.ket (xo7ClearLoopBits rXo rHot k β)
  | 0, _, β => by
      simp only [xo7ClearLoop, eval_identity_mulVec]
      apply congrArg Solution.CircuitModular.UnsignedGivens.ket; funext w;
        dsimp only [xo7ClearLoopBits]
      by_cases hw : w ∈ Set.range rXo.wires
      · obtain ⟨b, rfl⟩ := hw; simp [CoherentAlias.writeReg_apply_reg]
      · exact (CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw).symm
  | k + 1, hk, β => by
      rw [xo7ClearLoop, SelectSwapQROM.eval_seq_mulVec, ket_xo7ClearLoop rXo rHot hXoHot k
        (by omega) β, evolve_cnotMaskReg_ket]
      set βk := xo7ClearLoopBits rXo rHot k β
      have hMaskEq : maskSumBit rHot (xoBitMask128 ⟨k, hk⟩) βk = maskSumBit rHot (xoBitMask128 ⟨k,
          hk⟩) β := by
        dsimp only [maskSumBit]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        have hnot : rHot g ∉ Set.range rXo.wires := fun ⟨b, hb⟩ ↦ hXoHot.ne b g hb
        rw [show βk (rHot g) = β (rHot g) from
          CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnot]
      rw [hMaskEq]; apply congrArg Solution.CircuitModular.UnsignedGivens.ket; funext w
      by_cases hw : w ∈ Set.range rXo.wires
      · obtain ⟨b, rfl⟩ := hw
        by_cases hbk : b = ⟨k, hk⟩
        · subst hbk; simp [βk, xo7ClearLoopBits, CoherentAlias.writeReg_apply_reg]
        · have hne_val : b.val ≠ k := fun he ↦ hbk (Fin.ext he)
          dsimp only [βk, xo7ClearLoopBits]
          rw [update_of_ne (rXo.wires.injective.ne hbk), CoherentAlias.writeReg_apply_reg,
            CoherentAlias.writeReg_apply_reg]
          exact if_congr (by omega) rfl rfl
      · simp [update_of_ne (show w ≠ rXo ⟨k, hk⟩ from fun he ↦ hw ⟨⟨k, hk⟩, he.symm⟩),
          βk, xo7ClearLoopBits, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw]
theorem ket_xo7OneHotClearCirc {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N) (hXoHot :
    rXo.DisjointWires rHot) (β : BitAssignment N) : (xo7OneHotClearCirc rXo rHot
    hXoHot).eval.1.mulVec (Solution.CircuitModular.UnsignedGivens.ket β) =
      Solution.CircuitModular.UnsignedGivens.ket (writeReg β rXo fun b ↦
    β (rXo b) + maskSumBit rHot (xoBitMask128 b) β) := by
  simpa only [xo7OneHotClearCirc, xo7ClearLoopBits, Fin.is_lt, ↓reduceIte] using ket_xo7ClearLoop
    rXo rHot hXoHot 7 le_rfl β
theorem xo7OneHotClearCirc_mul_self {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N) (hXoHot :
    rXo.DisjointWires rHot) : (xo7OneHotClearCirc rXo rHot hXoHot).eval * (xo7OneHotClearCirc rXo
    rHot hXoHot).eval = 1 := by
  apply Subtype.ext; refine Solution.CircuitModular.UnsignedGivens.matrix_ext_ket fun γ ↦ ?_
  rw [Submonoid.coe_mul, ← mulVec_mulVec, ket_xo7OneHotClearCirc, ket_xo7OneHotClearCirc,
    Submonoid.coe_one, one_mulVec]
  set γ' := writeReg γ rXo fun b ↦
    γ (rXo b) + maskSumBit rHot (xoBitMask128 b) γ with hγ'
  have hMask (b : Fin 7) : maskSumBit rHot (xoBitMask128 b) γ' = maskSumBit rHot (xoBitMask128 b) γ
    :=
    Finset.sum_congr rfl fun c _ ↦ by
      have hnot : rHot c ∉ Set.range rXo.wires := fun ⟨b', hb'⟩ ↦ hXoHot.ne b' c hb'
      rw [hγ', CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnot]
  apply congrArg Solution.CircuitModular.UnsignedGivens.ket; funext w
  by_cases hw : w ∈ Set.range rXo.wires
  · obtain ⟨b, rfl⟩ := hw
    rw [CoherentAlias.writeReg_apply_reg, hMask b, hγ', CoherentAlias.writeReg_apply_reg, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  · rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw]
    exact CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw
theorem xo7OneHotClearCirc_conjTranspose {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
  (hXoHot : rXo.DisjointWires rHot) : (xo7OneHotClearCirc rXo rHot hXoHot).eval.1ᴴ =
  (xo7OneHotClearCirc rXo rHot hXoHot).eval.1 := conjTranspose_eq_self_of_mul_self _
  (xo7OneHotClearCirc_mul_self rXo rHot hXoHot)
theorem basisBits7_eq_xoBitMask128 (c₀ : Fin (2 ^ 7)) (b : Fin 7) : basisBits 7 c₀ b = if
    xoBitMask128 b c₀ then 1 else 0 := by
  revert c₀ b; decide
theorem maskSumBit_xoBitMask128_oneHot {N : ℕ} (rHot : QRegister 128 N) (b : Fin 7) (c₀ : Fin (2 ^
    7)) {γ : BitAssignment N} (hc : ∀ c : Fin 128, γ (rHot c) = if c = c₀ then 1 else 0) :
    maskSumBit rHot (xoBitMask128 b) γ = basisBits 7 c₀ b := by
  rw [basisBits7_eq_xoBitMask128]; dsimp only [maskSumBit]
  have hite (c : Fin 128) : (if xoBitMask128 b c then γ (rHot c) else 0) =
        if c = c₀ then (if xoBitMask128 b c₀ then (1 : ZMod 2) else 0) else 0 := by
    rw [hc c]
    by_cases hcc : c = c₀
    · subst hcc; simp
    · simp [hcc]
  simp_rw [hite]; simp
theorem predProj_mul_zeroProjOn_eq_cleanPredProj {N : ℕ} (S : Finset (Wire N)) (H : BitAssignment N
    → Bool) : predProj H * zeroProjOn S = Mobius126OneHot.cleanPredProj S H := by
  dsimp only [Mobius126OneHot.cleanPredProj, zeroProjOn, predProj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; exact mul_comm _ _
theorem cleanPredProj_conjTranspose {N : ℕ} (S : Finset (Wire N)) (H : BitAssignment N → Bool) :
    (Mobius126OneHot.cleanPredProj S H)ᴴ = Mobius126OneHot.cleanPredProj S H := by
  dsimp only [Mobius126OneHot.cleanPredProj]
  rw [conjTranspose_mul, predProj_conjTranspose, zeroProjOn_conjTranspose]
  exact predProj_mul_zeroProjOn_eq_cleanPredProj S H
theorem cleanPredProj_mul_of_subset {N : ℕ} {S₁ S₂ : Finset (Wire N)} (hSub : S₁ ⊆ S₂) (H :
    BitAssignment N → Bool) : Mobius126OneHot.cleanPredProj S₁ H * Mobius126OneHot.cleanPredProj
    S₂ H = Mobius126OneHot.cleanPredProj S₂ H := by
  dsimp only [Mobius126OneHot.cleanPredProj, zeroProjOn, predProj]
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  by_cases h2 : ∀ w ∈ S₂, basisBits N i w = 0
  · rw [ite_eq_left h2, ite_eq_left fun w hw ↦ h2 w (hSub hw)]
    by_cases hH : H (basisBits N i) = true <;> simp [hH]
  · rw [ite_eq_right h2]; simp
theorem zeroProjOn_borrow_mul_clear_cleanPredProj {N sTail : ℕ}
    (rXo : QRegister 7 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N)
    (hXoHot : rXo.DisjointWires rHot) (hXoTail : rXo.DisjointWires rTail) :
    let C := xo7OneHotClearCirc rXo rHot hXoHot
    let Q_xo := Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo rHot)
    zeroProjOn (rXo.concat rTail hXoTail).image * (C.eval.1 * Q_xo) =
      C.eval.1 * Q_xo := by
  intro C Q_xo
  have hket (δ : BitAssignment N) : Solution.CircuitModular.UnsignedGivens.ket δ =
    SelectSwapQROM.ket δ := rfl
  refine SelectSwapQROM.matrix_ext_ket fun γ ↦ ?_
  dsimp only [Q_xo, Mobius126OneHot.cleanPredProj]
  simp only [← mulVec_mulVec, predProj_mulVec_ket]
  by_cases hPred : xoOneHotPred rXo rHot γ = true
  · rw [ite_eq_left hPred, zeroProjOn_mulVec_ket]
    by_cases hT : ∀ w ∈ rTail.image, γ w = 0
    · rw [ite_eq_left hT, ← hket γ, ket_xo7OneHotClearCirc, hket,
        zeroProjOn_mulVec_ket]
      refine ite_eq_left fun w hw ↦ ?_
      rw [QRegister.image_concat, Finset.mem_union] at hw
      rcases hw with hwXo | hwTail
      · obtain ⟨b, rfl⟩ := (mem_image rXo w).mp hwXo; rw [CoherentAlias.writeReg_apply_reg]
        have hx : ∀ c : Fin 128, γ (rHot c) =
            if c = Solution.CircuitModular.UnsignedGivens.localIdx rXo γ then 1 else 0 := by
          unfold xoOneHotPred at hPred; exact of_decide_eq_true hPred
        have hb : basisBits 7 (Solution.CircuitModular.UnsignedGivens.localIdx rXo γ) b =
          γ (rXo b) := congrFun
          (basisBits_symm_eq (fun k ↦ γ (rXo k))) b
        rw [maskSumBit_xoBitMask128_oneHot rHot b _ hx, hb, CharTwo.add_self_eq_zero]
      · obtain ⟨j, rfl⟩ := (mem_image rTail w).mp hwTail
        rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦ hXoTail.ne b j hb]
        exact hT _ hwTail
    · rw [ite_eq_right hT, mulVec_zero, mulVec_zero]
  · rw [ite_eq_right hPred, mulVec_zero, mulVec_zero, mulVec_zero]
attribute [irreducible] xo7OneHotClearCirc
/-- Subspace `wp` realization of unitary `U` on Hermitian projector `Q` (`Q * U.1ᴴ = U.1ᴴ * Q`). -/
def CleanPredRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} (v : Var) (Q : Operator
  (2 ^ N)) (U : Unitary (2 ^ N)) (P : DynamicCircuit Var N) : Prop := P.count .TOFF = 0 ∧ Q * U.1ᴴ =
  U.1ᴴ * Q ∧ (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) → ∀ σ val,
  wp P.compile Θ (Function.update σ v val) = wp P.compile Θ σ) ∧ (∀ Θ : QCAssertion Var (2 ^ N), (∀
  σ val, Θ (Function.update σ v val) = Θ σ) → ∀ σ : Store Var, ((wp P.compile Θ σ).1).conj Q =
  ((qcWpQAssign U Θ σ).1).conj Q)
theorem CleanPredRealizes.seq {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} {v : Var} {Q :
    Operator (2 ^ N)} {U₁ U₂ : Unitary (2 ^ N)} {P₁ P₂ : DynamicCircuit Var N} (h₁ :
    CleanPredRealizes v Q U₁ P₁) (h₂ : CleanPredRealizes v Q U₂ P₂) : CleanPredRealizes v Q
    (U₂ * U₁) (P₁.seq P₂) :=
  ⟨by simp [DynamicCircuit.count, h₁.1, h₂.1],
   by change Q * (U₂.1 * U₁.1)ᴴ = (U₂.1 * U₁.1)ᴴ * Q
      rw [conjTranspose_mul, ← Matrix.mul_assoc, h₁.2.1, Matrix.mul_assoc, h₂.2.1, ←
        Matrix.mul_assoc],
   fun Θ hΘ σ val ↦ h₁.2.2.1 (wp P₂.compile Θ) (h₂.2.2.1 Θ hΘ) σ val,
   fun Θ hΘ σ ↦ by
     have h1 := congrArg HermitianMat.mat (h₁.2.2.2 (wp P₂.compile Θ) (h₂.2.2.1 Θ hΘ) σ)
     have h2 := congrArg HermitianMat.mat (h₂.2.2.2 Θ hΘ σ)
     have h1R : U₁.1 * Qᴴ = Qᴴ * U₁.1 := by
       simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
         congrArg (·ᴴ) h₁.2.1
     apply HermitianMat.ext; change Q * (wp P₁.compile (wp P₂.compile Θ) σ).1.mat * Qᴴ = _
     simp only [qcWpQAssign, qcQAssignObsMap, conj_coe, conj_apply_mat, coe_star,
       star_eq_conjTranspose, conjTranspose_conjTranspose, Submonoid.coe_mul, conjTranspose_mul]
       at h1 h2 ⊢
     have hSwap (M : Operator (2 ^ N)) : Q * (U₁.1ᴴ * M * U₁.1) * Qᴴ = U₁.1ᴴ * (Q * M * Qᴴ) * U₁.1
         := by
       calc Q * (U₁.1ᴴ * M * U₁.1) * Qᴴ
           = (Q * U₁.1ᴴ) * M * (U₁.1 * Qᴴ) := by simp only [Matrix.mul_assoc]
         _ = U₁.1ᴴ * (Q * M * Qᴴ) * U₁.1 := by rw [h₁.2.1, h1R]; simp only [Matrix.mul_assoc]
     rw [h1, hSwap, h2, ← hSwap]; simp only [Matrix.mul_assoc]⟩
theorem preservesWires_comm_predProj {N : ℕ} {M : Operator (2 ^ N)} {S : Finset (Wire N)} {P :
    BitAssignment N → Bool} (hPres : PreservesWires M S) (hDep : ∀ α β : BitAssignment N, (∀ w ∈ S,
    α w = β w) → P α = P β) : M * predProj P = predProj P * M := by
  ext i j; simp only [predProj, mul_diagonal, Matrix.diagonal_mul]
  by_cases hM : M i j = 0
  · simp [hM]
  · rw [hDep (basisBits N i) (basisBits N j) fun w hw ↦ by
      by_contra hne; exact hM (hPres i j ⟨w, hw, hne⟩), mul_comm]
theorem preservesWires_comm_predProj_xoOneHot {N : ℕ} {M : Operator (2 ^ N)} {rXo : QRegister 7 N}
    {rHot : QRegister 128 N} (hPres : PreservesWires M (rXo.image ∪ rHot.image)) : M * predProj
    (xoOneHotPred rXo rHot) = predProj (xoOneHotPred rXo rHot) * M :=
  preservesWires_comm_predProj hPres fun α β h ↦ by
    have hIdx : Solution.CircuitModular.UnsignedGivens.localIdx rXo α =
      Solution.CircuitModular.UnsignedGivens.localIdx rXo β :=
      congrArg (basisBits 7).symm (funext fun b ↦
        h _ (Finset.mem_union_left _ ((mem_image rXo _).mpr ⟨b, rfl⟩)))
    have hH (c : Fin 128) := h _ (Finset.mem_union_right _ ((mem_image rHot _).mpr ⟨c, rfl⟩))
    unfold xoOneHotPred; rw [hIdx]
    exact decide_eq_decide.mpr ⟨fun hc c ↦ (hH c).symm.trans (hc c), fun hc c ↦ (hH c).trans (hc c)⟩
theorem CleanPredRealizes.of_cleanRealizes_xoOneHot {Var : Type} [Fintype Var] [DecidableEq Var]
    {k N sTail : ℕ} {v : Var} {rSub : QRegister k N} {rTail : QRegister sTail N} {rXo : QRegister 7
    N} {rHot : QRegister 128 N} (hSubTail : rSub.DisjointWires rTail) (hSubXo : rSub.DisjointWires
    rXo) (hSubHot : rSub.DisjointWires rHot) {V : Unitary (2 ^ k)} {P : DynamicCircuit Var N} (h :
    Solution.CleanDyn.CleanRealizes v rSub rTail V P) : CleanPredRealizes v
    (Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo rHot)) (rSub.embedUnitary V) P :=
  by
  have hSet : CleanRealizesSet v rTail.image (rSub.embedUnitary V) P := (cleanRealizes_iff_set v
    rSub rTail V P).mp ((cleanRealizes_sbx_iff v rSub rTail V P).mpr h)
  have hDisjXH : Disjoint rSub.image (rXo.image ∪ rHot.image) :=
    Finset.disjoint_union_right.mpr ⟨disjoint_image_of_disjointWires hSubXo,
      disjoint_image_of_disjointWires hSubHot⟩
  have hCommT : zeroProjOn rTail.image * (rSub.embedUnitary V).1ᴴ = (rSub.embedUnitary V).1ᴴ *
      zeroProjOn rTail.image := by
    have hc := preservesWires_comm_zeroProjOn (preservesWires_embedMatrix_of_disjoint rSub V.1
      rTail.image (disjoint_image_of_disjointWires hSubTail)) Finset.Subset.rfl
    simpa only [embedUnitary_val, conjTranspose_mul,
      zeroProjOn_conjTranspose] using congrArg (·ᴴ) hc
  have hCommP : predProj (xoOneHotPred rXo rHot) * (rSub.embedUnitary V).1ᴴ = (rSub.embedUnitary
      V).1ᴴ * predProj (xoOneHotPred rXo rHot) := by
    have hc := preservesWires_comm_predProj_xoOneHot (rXo := rXo) (rHot := rHot)
      (preservesWires_embedMatrix_of_disjoint rSub V.1 _ hDisjXH)
    simpa only [embedUnitary_val, conjTranspose_mul,
      predProj_conjTranspose] using congrArg (·ᴴ) hc
  refine ⟨hSet.1, ?_, hSet.2.1, fun Θ hΘ σ ↦ ?_⟩
  · dsimp only [Mobius126OneHot.cleanPredProj]
    rw [Matrix.mul_assoc, hCommP, ← Matrix.mul_assoc, hCommT, Matrix.mul_assoc]
  · apply HermitianMat.ext
    have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦
      (x.1.conj (predProj (xoOneHotPred rXo rHot))).mat)
      (congrFun (hSet.2.2.1 Θ hΘ) σ)
    simp only [SelectSwapQROM.restrictZeroSet_coe, conj_apply_mat, predProj_conjTranspose,
      zeroProjOn_conjTranspose, cleanPredProj_conjTranspose] at hv ⊢
    have hv' : (predProj (xoOneHotPred rXo rHot) * zeroProjOn rTail.image) * (wp P.compile Θ
        σ).1.mat * Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo rHot) = (predProj
        (xoOneHotPred rXo rHot) * zeroProjOn rTail.image) * (qcWpQAssign (rSub.embedUnitary V) Θ
        σ).1.mat * Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo rHot) := by
      dsimp only [Mobius126OneHot.cleanPredProj]; simpa only [Matrix.mul_assoc] using hv
    rwa [predProj_mul_zeroProjOn_eq_cleanPredProj] at hv'
/-- `1`-AND (`4 T`) initial `2 → 4` one-hot decoder on `L.rCtx 0, 1 → L.rHot 0..3`. -/
def init4Rev2 {N : ℕ} (L : StepOneHotLayout N) : RevCompute N :=
  let c0 := L.rCtx 0; let c1 := L.rCtx 1
  let h0 := L.rHot 0; let h1 := L.rHot 1; let h2 := L.rHot 2; let h3 := L.rHot 3
  have hc01 : c0 ≠ c1 := L.rCtx.wires.injective.ne (by decide)
  have hne (i : Fin 7) (g : Fin 128) : L.rCtx i ≠ L.rHot g := L.hCtxHot.ne i g
  have hh (a b : Fin 128) (hab : a ≠ b) : L.rHot a ≠ L.rHot b := L.rHot.wires.injective.ne hab
  .seq (.andGate c0 c1 h3 hc01 (hne 0 3) (hne 1 3)) (.seq (.cnot c1 h2 (hne 1 2)) (.seq (.cnot h3 h2
    (hh 3 2 (by decide))) (.seq (.cnot c0 h1 (hne 0 1)) (.seq (.cnot h3 h1 (hh 3 1 (by decide)))
    (.seq (.x h0) (.seq (.cnot c0 h0 (hne 0 0)) (.cnot h2 h0 (hh 2 0 (by decide)))))))))
/-- Disjointness certificate for binary-tree W-state doubling stage `R` (`2 * R ≤ 128`). -/
theorem hotSplitValid {N : ℕ} (L : StepOneHotLayout N) (bIdx : Fin 7)
    (R : ℕ) (h2R : 2 * R ≤ 128) :
    WSplitValid R (L.rCtx bIdx)
      (fun i : Fin R ↦ L.rHot ⟨i.val, by omega⟩)
      (fun i : Fin R ↦ L.rHot ⟨R + i.val, by omega⟩) L.qEnc where
  w0_inj i j h := Fin.ext (by have := congrArg Fin.val (L.rHot.wires.injective h); exact this)
  w1_inj i j h := Fin.ext (by
    have := congrArg Fin.val (L.rHot.wires.injective h); dsimp at this; omega)
  w01_ne i j h := by have := congrArg Fin.val (L.rHot.wires.injective h); dsimp at this; omega
  ctrl_w0 i := L.hCtxHot.ne bIdx _
  ctrl_w1 i := L.hCtxHot.ne bIdx _
  q_ctrl := (L.hCtxEnc bIdx).symm
  q_w0 i := (L.hHotEnc _).symm
  q_w1 i := (L.hHotEnc _).symm
/-- Classical `R`-way W-splitting reversible stage on `L`. -/
def splitRevPhase {N : ℕ} (L : StepOneHotLayout N) (b : Fin 7) (R : ℕ) (h2R : 2 * R ≤ 128) :
  RevCompute N := splitRevLoop (L.rCtx b) R _ _ (hotSplitValid L b R h2R).toWPairDisj
/-- Classical `125`-AND reversible `7 → 128` binary-tree one-hot model (uncomputed in `0 T`). -/
def hot128Rev {N : ℕ} (L : StepOneHotLayout N) : RevCompute N := .seq (.seq (.seq (.seq (.seq
  (init4Rev2 L) (splitRevPhase L 2 4 (by decide))) (splitRevPhase L 3 8 (by decide)))
  (splitRevPhase L 4 16 (by decide))) (splitRevPhase L 5 32 (by decide))) (splitRevPhase L 6
  64 (by decide))
/-- `252-T`, `0-TOFF` W-state `7 → 128` one-hot encoder (`4 + 8 + 16 + 32 + 64 + 128 = 252 T`). -/
def hot128EncDyn {Var : Type} {N : ℕ} (v : Var) (L : StepOneHotLayout N) : DynamicCircuit Var N
  := .seq (.seq (.seq (.seq (.seq (revComputeDyn (init4Rev2 L)) (dWExpandDet1 v 4 (L.rCtx 2) _ _
  L.qEnc (hotSplitValid L 2 4 (by decide)))) (dWExpandDet1 v 8 (L.rCtx 3) _ _ L.qEnc
  (hotSplitValid L 3 8 (by decide)))) (dWExpandDet1 v 16 (L.rCtx 4) _ _ L.qEnc (hotSplitValid L
  4 16 (by decide)))) (dWExpandDet1 v 32 (L.rCtx 5) _ _ L.qEnc (hotSplitValid L 5 32
  (by decide)))) (dWExpandDet1 v 64 (L.rCtx 6) _ _ L.qEnc (hotSplitValid L 6 64 (by decide)))
/-- `0-T`, `0-TOFF` measurement-based uncompute decoder paired with `hot128EncDyn`. -/
def hot128DecDyn {Var : Type} {N : ℕ} (v : Var) (L : StepOneHotLayout N) : DynamicCircuit Var N
  := revUncomputeDyn v (hot128Rev L)
/-- `252-T` one-hot context wrapper `hot128EncDyn ;; mid ;; hot128DecDyn`. -/
def withHot128Dyn {Var : Type} {N : ℕ} (v : Var) (L : StepOneHotLayout N) (mid : DynamicCircuit
  Var N) : DynamicCircuit Var N := .seq (hot128EncDyn v L) (.seq mid (hot128DecDyn v L))
@[simp] theorem count_withHot128Dyn_toff {Var : Type} {N : ℕ} (v : Var) (L : StepOneHotLayout N)
    {mid : DynamicCircuit Var N} (hm : mid.count .TOFF = 0) : (withHot128Dyn v L mid).count .TOFF
    = 0 := by
  simp [withHot128Dyn, hot128EncDyn, hot128DecDyn, DynamicCircuit.count, hm]
@[simp] theorem count_withHot128Dyn_t {Var : Type} {N : ℕ} (v : Var) (L : StepOneHotLayout N)
    (mid : DynamicCircuit Var N) : (withHot128Dyn v L mid).count .T = 252 + mid.count .T := by
  simp [withHot128Dyn, hot128EncDyn, hot128DecDyn, DynamicCircuit.count, init4Rev2,
    RevCompute.numAnd]
/-- Input validity predicate `(∀ c, β (L.rHot c) = 0) ∧ β L.qEnc = 0` for `hot128EncDyn`. -/
noncomputable def encValidPred {N : ℕ} (L : StepOneHotLayout N) (β : BitAssignment N) : Bool :=
  open Classical in decide ((∀ c : Fin 128, β (L.rHot c) = 0) ∧ β L.qEnc = 0)
theorem init4Bits (x : Fin (2 ^ 7)) :
    let b0 := basisBits 7 x 0; let b1 := basisBits 7 x 1
    let a3 := b0 * b1; let a2 := b1 + a3; let a1 := b0 + a3; let a0 := 1 + b0 + a2
    a0 = (if (0 : ℕ) = x.val % 4 then 1 else 0) ∧
    a1 = (if (1 : ℕ) = x.val % 4 then 1 else 0) ∧
    a2 = (if (2 : ℕ) = x.val % 4 then 1 else 0) ∧
    a3 = (if (3 : ℕ) = x.val % 4 then 1 else 0) := by
  revert x; decide
theorem doubleIdx (x : Fin (2 ^ 7)) (bIdx : Fin 7) (hb : 2 ≤ bIdx.val) : x.val % 2 ^ bIdx.val + 2
    ^ bIdx.val * bit01Nat (basisBits 7 x bIdx) = x.val % 2 ^ (bIdx.val + 1) := by
  revert x bIdx hb; decide
theorem init4Rev_spec {N : ℕ} (L : StepOneHotLayout N) (β : BitAssignment N) (hHot : ∀ c : Fin
    128, β (L.rHot c) = 0) : (init4Rev2 L).validOn β = true ∧ (∀ k : ℕ, (hk : k < 4) → (init4Rev2
    L).fwdBits β (L.rHot ⟨k, by
      omega⟩) = if k = (Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β).val % 4 then
    1 else 0) ∧ (∀ u : Wire N, u ≠ L.rHot 0 ∧ u ≠ L.rHot 1 ∧ u ≠ L.rHot 2 ∧ u ≠ L.rHot 3 →
    (init4Rev2 L).fwdBits β u = β u) := by
  have hc (i : Fin 7) : β (L.rCtx i) =
    basisBits 7 (Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β) i :=
    (congrFun (basisBits_symm_eq (fun j ↦ β (L.rCtx j))) i).symm
  have hb := init4Bits (Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β)
  have hCH (i : Fin 7) (g : Fin 128) : (L.rCtx i = L.rHot g) ↔ False := iff_false_intro
    (L.hCtxHot.ne i g)
  have hHH (a b : Fin 128) : (L.rHot a = L.rHot b) ↔ a = b := L.rHot.wires.injective.eq_iff
  refine ⟨by simp [init4Rev2, RevCompute.validOn, hHot 3], fun k hk ↦ ?_,
    fun u hu ↦ ?_⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change (init4Rev2 L).fwdBits β (L.rHot 0) = _
      simpa only [init4Rev2, RevCompute.fwdBits, update_apply, hCH, hHH, Fin.reduceEq, ↓reduceIte,
        hHot, hc, zero_add] using hb.1
    · change (init4Rev2 L).fwdBits β (L.rHot 1) = _
      simpa only [init4Rev2, RevCompute.fwdBits, update_apply, hCH, hHH, Fin.reduceEq, ↓reduceIte,
        hHot, hc, zero_add] using hb.2.1
    · change (init4Rev2 L).fwdBits β (L.rHot 2) = _
      simpa only [init4Rev2, RevCompute.fwdBits, update_apply, hCH, hHH, Fin.reduceEq, ↓reduceIte,
        hHot, hc, zero_add] using hb.2.2.1
    · change (init4Rev2 L).fwdBits β (L.rHot 3) = _
      simpa only [init4Rev2, RevCompute.fwdBits, update_apply, hCH, hHH, Fin.reduceEq, ↓reduceIte,
        hHot, hc, zero_add] using hb.2.2.2
  · dsimp only [init4Rev2, RevCompute.fwdBits]
    simp only [update_of_ne hu.1, update_of_ne hu.2.1, update_of_ne hu.2.2.1, update_of_ne hu.2.2.2]
theorem cswapHotPhase {N R : ℕ} (L : StepOneHotLayout N) (bIdx : Fin 7) (h2R : 2 * R ≤ 128)
    (β : BitAssignment N) (idx : Fin R)
    (hq : β L.qEnc = 0)
    (hHot : ∀ k : ℕ, (hk : k < 2 * R) → β (L.rHot ⟨k, by omega⟩) = if k = idx.val then 1 else 0) :
    let hv := hotSplitValid L bIdx R h2R
    let w0 : Fin R → Wire N := fun i ↦ L.rHot ⟨i.val, by omega⟩
    let w1 : Fin R → Wire N := fun i ↦ L.rHot ⟨R + i.val, by omega⟩
    let p := splitRevLoop (L.rCtx bIdx) R w0 w1 hv.toWPairDisj
    InvWSplitDet R w0 w1 L.qEnc β ∧ p.validOn β = true ∧
    (∀ k : ℕ, (hk : k < 2 * R) → p.fwdBits β (L.rHot ⟨k, by omega⟩) =
      if k = idx.val + R * bit01Nat (β (L.rCtx bIdx)) then 1 else 0) ∧
    (∀ u : Wire N, (∀ k : ℕ, (hk : k < 2 * R) → u ≠ L.rHot ⟨k, by omega⟩) →
      p.fwdBits β u = β u) := by
  intro hv w0 w1 p; have hIdxLt := idx.isLt
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have hb0 : bit01Nat 0 = 0 := rfl; have hb1 : bit01Nat 1 = 1 := rfl
  have hw1 (i : Fin R) : β (w1 i) = 0 := by
    dsimp only [w1]; rw [hHot (R + i.val) (by omega), ite_eq_right (by omega)]
  have hInv : InvWSplitDet R w0 w1 L.qEnc β :=
    ⟨hq, hw1, idx, by dsimp [w0]; rw [hHot idx.val (by omega), ite_eq_left rfl],
      fun i hne ↦ by dsimp [w0]; rw [hHot i.val (by omega), ite_eq_right (Fin.val_ne_of_ne hne)]⟩
  obtain ⟨hval, hfwd⟩ := splitRevLoop_spec (L.rCtx bIdx) R w0 w1 hv.toWPairDisj β hw1
  refine ⟨hInv, hval, fun k hk ↦ ?_, fun u hu ↦ ?_⟩
  · rw [hfwd]; by_cases hkR : k < R
    · change cswapRangeBits R (L.rCtx bIdx) w0 w1 β (w0 ⟨k, hkR⟩) = _
      rw [cswapRangeBits_w0 hv.toWPairDisj β ⟨k, hkR⟩]
      rcases SelectSwapQROM.bit_cases (β (L.rCtx bIdx)) with hc | hc
      · simp only [hc, h01, ↓reduceIte, hb0, mul_zero, add_zero, hHot k hk]
      · simp only [hc, ↓reduceIte, hb1, mul_one, hHot (R + k) (by omega),
          ite_eq_right (show R + k ≠ idx.val by omega), ite_eq_right (show k ≠ idx.val + R by
            omega)]
    · let j : Fin R := ⟨k - R, by omega⟩
      rw [show L.rHot ⟨k, by omega⟩ = w1 j from congrArg L.rHot (Fin.ext (by dsimp [j]; omega)),
        cswapRangeBits_w1 hv.toWPairDisj β j]
      rcases SelectSwapQROM.bit_cases (β (L.rCtx bIdx)) with hc | hc
      · simp only [hc, h01, ↓reduceIte, hb0, mul_zero, add_zero, hHot (R + j.val) (by omega),
          ite_eq_right (show R + j.val ≠ idx.val by omega), ite_eq_right (show k ≠ idx.val by
            omega)]
      · simp only [hc, ↓reduceIte, hb1, mul_one, hHot j.val (by omega), j]
        exact if_congr (by omega) rfl rfl
  · rw [hfwd]
    exact cswapRangeBits_other β (fun i ↦ hu i.val (by omega)) (fun i ↦ hu (R + i.val) (by omega))
/-- Stage invariant after `R`-way (`R ≤ 128`) binary-tree one-hot expansion on `L`. -/
abbrev PhaseInv {N : ℕ} (L : StepOneHotLayout N) (β : BitAssignment N) (R : ℕ) (hR : R ≤ 128) (γ
    : BitAssignment N) : Prop :=
  let x := Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β
  γ L.qEnc = 0 ∧ (∀ j : Fin 7, γ (L.rCtx j) = basisBits 7 x j) ∧
  (∀ k : ℕ, (hk : k < R) → γ (L.rHot ⟨k, by omega⟩) = if k = x.val % R then 1 else 0) ∧
  (∀ k : ℕ, R ≤ k → (hk2 : k < 128) → γ (L.rHot ⟨k, hk2⟩) = 0) ∧
  (∀ u : Wire N, (∀ c : Fin 128, u ≠ L.rHot c) → γ u = β u)
theorem hot128Rev_equiv {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} (v : Var) (L :
    StepOneHotLayout N) : EquivRev v (encValidPred L) (hot128Rev L) (hot128EncDyn v L) ∧ (∀
    β, encValidPred L β = true → (hot128Rev L).validOn β = true ∧ (hot128Rev L).fwdBits β =
    Function.update β (L.rHot (Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β)) 1) := by
  let w0R (R : ℕ) (h2R : 2 * R ≤ 128) : Fin R → Wire N := fun i ↦ L.rHot ⟨i.val, by omega⟩
  let w1R (R : ℕ) (h2R : 2 * R ≤ 128) : Fin R → Wire N := fun i ↦ L.rHot ⟨R + i.val, by omega⟩
  let p0 := init4Rev2 L; let q1 := p0.seq (splitRevPhase L 2 4 (by decide))
  let q2 := q1.seq (splitRevPhase L 3 8 (by decide))
  let q3 := q2.seq (splitRevPhase L 4 16 (by decide))
  let q4 := q3.seq (splitRevPhase L 5 32 (by decide))
  have hPhase {β : BitAssignment N} {R : ℕ} (b : Fin 7) (hb2 : 2 ≤ b.val) (hR : R = 2 ^ b.val) (h2R
      : 2 * R ≤ 128) {γ : BitAssignment N} (hInv : PhaseInv L β R (by omega) γ) : InvWSplitDet R
      (w0R R h2R) (w1R R h2R) L.qEnc γ ∧ PhaseInv L β (2 * R) h2R ((splitRevPhase L b R
      h2R).fwdBits γ) := by
    dsimp only [splitRevPhase]; let x := Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β
    obtain ⟨hqγ, hcγ, hLo, hHi, hOut⟩ := hInv; have hRpos : 0 < R := hR ▸ Nat.two_pow_pos b.val
    have hHot2R (k : ℕ) (hk : k < 2 * R) :
        γ (L.rHot ⟨k, by omega⟩) = if k = (⟨x.val % R, Nat.mod_lt _ hRpos⟩ : Fin R).val
          then 1 else 0 := by
      by_cases hkR : k < R
      · exact hLo k hkR
      · rw [hHi k (by omega) (by omega),
          ite_eq_right (by dsimp; have := Nat.mod_lt x.val hRpos; omega)]
    obtain ⟨hI, _, hH', hO'⟩ := cswapHotPhase L b h2R γ ⟨x.val % R, Nat.mod_lt _ hRpos⟩ hqγ hHot2R
    have hIdxEq : x.val % R + R * bit01Nat (γ (L.rCtx b)) = x.val % (2 * R) := by
      rw [hcγ b, hR]; simpa only [Nat.pow_succ, Nat.mul_comm 2] using doubleIdx x b hb2
    exact ⟨hI, (hO' _ fun _ _ ↦ (L.hHotEnc _).symm).trans hqγ,
      fun j ↦ (hO' _ fun _ _ ↦ L.hCtxHot.ne j _).trans (hcγ j),
      fun k hk ↦ by simpa only [hIdxEq] using hH' k hk,
      fun k hk hk2 ↦ (hO' _ fun m hm ↦ L.rHot.wires.injective.ne
        (Fin.ne_of_val_ne (by dsimp; omega))).trans (hHi k (by omega) hk2),
      fun u hu ↦ (hO' u fun _ _ ↦ hu _).trans (hOut u hu)⟩
  have hChain (β : BitAssignment N) (hS : encValidPred L β = true) : p0.validOn β = true ∧
      InvWSplitDet 4 (w0R 4 (by decide)) (w1R 4 (by decide)) L.qEnc (p0.fwdBits β) ∧ InvWSplitDet 8
      (w0R 8 (by decide)) (w1R 8 (by decide)) L.qEnc (q1.fwdBits β) ∧ InvWSplitDet 16 (w0R 16
      (by decide)) (w1R 16 (by decide)) L.qEnc (q2.fwdBits β) ∧ InvWSplitDet 32 (w0R 32 (by decide))
      (w1R 32 (by decide)) L.qEnc (q3.fwdBits β) ∧ InvWSplitDet 64 (w0R 64 (by decide)) (w1R 64
      (by decide)) L.qEnc (q4.fwdBits β) ∧ (hot128Rev L).fwdBits β = Function.update β (L.rHot
      (Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β)) 1 := by
    obtain ⟨hHot0, hq0⟩ : (∀ c : Fin 128, β (L.rHot c) = 0) ∧ β L.qEnc = 0 := by
      unfold encValidPred at hS; exact of_decide_eq_true hS
    let x := Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β
    obtain ⟨hv0, hH0, hO0⟩ := init4Rev_spec L β hHot0
    have hne4 (u : Wire N) (h : ∀ c : Fin 128, c.val < 4 → u ≠ L.rHot c) : u ≠ L.rHot 0 ∧ u ≠ L.rHot
      1 ∧ u ≠ L.rHot 2 ∧ u ≠ L.rHot 3 := ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3
      (by decide)⟩
    have s0 : PhaseInv L β 4 (by decide) (p0.fwdBits β) :=
      ⟨(hO0 _ (hne4 _ fun c _ ↦ (L.hHotEnc c).symm)).trans hq0,
       fun b ↦ (hO0 _ (hne4 _ fun c _ ↦ L.hCtxHot.ne b c)).trans
         (congrFun (basisBits_symm_eq (fun j ↦ β (L.rCtx j))) b).symm,
       hH0,
       fun k hk hk2 ↦ (hO0 _ (hne4 _ fun c hc ↦ L.rHot.wires.injective.ne
         (Fin.ne_of_val_ne (by dsimp; omega)))).trans (hHot0 _),
       fun u hu ↦ hO0 u (hne4 u fun c _ ↦ hu c)⟩
    have s1 := hPhase (R := 4) 2 (by decide) (by decide) (by decide) s0
    have s2 := hPhase (R := 8) 3 (by decide) (by decide) (by decide) s1.2
    have s3 := hPhase (R := 16) 4 (by decide) (by decide) (by decide) s2.2
    have s4 := hPhase (R := 32) 5 (by decide) (by decide) (by decide) s3.2
    have s5 := hPhase (R := 64) 6 (by decide) (by decide) (by decide) s4.2
    have hFwd5 : (hot128Rev L).fwdBits β = (splitRevPhase L 6 64 (by decide)).fwdBits
      (q4.fwdBits β) := rfl
    refine ⟨hv0, s1.1, s2.1, s3.1, s4.1, s5.1, funext fun u ↦ ?_⟩
    rw [hFwd5]
    by_cases hu : ∃ c : Fin 128, u = L.rHot c
    · obtain ⟨c, rfl⟩ := hu
      have hc5 : (splitRevPhase L 6 64 (by decide)).fwdBits (q4.fwdBits β) (L.rHot c) =
          if c.val = x.val % 128 then 1 else 0 := s5.2.2.2.1 c.val c.isLt
      rw [Nat.mod_eq_of_lt (show x.val < 128 from x.isLt)] at hc5
      by_cases hcx : c = x
      · subst hcx; rw [hc5, ite_eq_left rfl, update_self]
      · rw [hc5, ite_eq_right (Fin.val_ne_of_ne hcx),
          update_of_ne (L.rHot.wires.injective.ne hcx), hHot0 c]
    · have hnot (c : Fin 128) : u ≠ L.rHot c := fun he ↦ hu ⟨c, he⟩
      exact (s5.2.2.2.2.2 u hnot).trans (update_of_ne (hnot x) 1 β).symm
  have hStep {q : RevCompute N} {Pq : DynamicCircuit Var N} (hq : EquivRev v (encValidPred L) q
      Pq) (b : Fin 7) (R : ℕ) (h2R : 2 * R ≤ 128) (hI : ∀ β, encValidPred L β = true →
      InvWSplitDet R (w0R R h2R) (w1R R h2R) L.qEnc (q.fwdBits β)) : EquivRev v (encValidPred L)
      (q.seq (splitRevPhase L b R h2R)) (Pq.seq (dWExpandDet1 v R (L.rCtx b) _ _ L.qEnc
      (hotSplitValid L b R h2R))) := by
    dsimp only [splitRevPhase]
    exact hq.seq (EquivRev.ofDWExpandDet1 v R (L.rCtx b) _ _ L.qEnc
      (hotSplitValid L b R h2R) _ fun γ hγ ↦ by rw [← q.fwdBits_invBits γ]; exact hI _ hγ)
  have e0 := EquivRev.ofRevCompute v (encValidPred L) p0
    fun β hS ↦ (hChain β hS).1
  have e1 := hStep e0 2 4 (by decide) fun β hS ↦ (hChain β hS).2.1
  have e2 := hStep e1 3 8 (by decide) fun β hS ↦ (hChain β hS).2.2.1
  have e3 := hStep e2 4 16 (by decide) fun β hS ↦ (hChain β hS).2.2.2.1
  have e4 := hStep e3 5 32 (by decide) fun β hS ↦ (hChain β hS).2.2.2.2.1
  have e5 := hStep e4 6 64 (by decide) fun β hS ↦ (hChain β hS).2.2.2.2.2.1
  exact ⟨e5, fun β hS ↦ ⟨e5.1 β hS, (hChain β hS).2.2.2.2.2.2⟩⟩
attribute [irreducible] splitRevPhase
/-- Subspace turnaround `wp` specification on `Q`: conjugates `W_in` into `W_out` on `Q`. -/
def XoTurnaroundWp {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} (v : Var) (Q : Operator (2
  ^ N)) (W_in W_out : Unitary (2 ^ N)) (P : DynamicCircuit Var N) : Prop := P.count .TOFF = 0 ∧ (∀ Θ
  : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) → ∀ σ val, wp P.compile Θ
  (Function.update σ v val) = wp P.compile Θ σ) ∧ (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ
  (Function.update σ v val) = Θ σ) → ∀ σ : Store Var, ((qcWpQAssign W_in (wp P.compile Θ) σ).1).conj
  Q = ((qcWpQAssign W_out Θ σ).1).conj Q)
theorem e_enc_mulVec_ket {N : ℕ} (L : StepOneHotLayout N) (β : BitAssignment N) : ((hot128Rev
    L).toCircuit.eval.1 * predProj (encValidPred L)).mulVec (CoherentAlias.ket β) = if
    encValidPred L β = true then CoherentAlias.ket (Function.update β (L.rHot
    (Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β)) 1) else 0 := by
  have hk (γ : BitAssignment N) : CoherentAlias.ket γ = SelectSwapQROM.ket γ := rfl
  rw [hk, ← mulVec_mulVec, predProj_mulVec_ket]
  by_cases hS : encValidPred L β = true
  · rw [ite_eq_left hS, ite_eq_left hS]
    change (hot128Rev L).toCircuit.eval.1.mulVec (GroupUnary.ket β) = _
    rw [(hot128Rev L).toCircuit_mulVec_ket, ((hot128Rev_equiv () L).2 β hS).2]
  · rw [ite_eq_right hS, ite_eq_right hS, mulVec_zero]
theorem encValid_of_zero {N : ℕ} (L : StepOneHotLayout N) {S_clean : Finset (Wire N)} (hqS :
    L.qEnc ∈ S_clean) {β : BitAssignment N} (h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0) :
    encValidPred L β = true := by
  unfold encValidPred; rw [decide_eq_true_eq]
  exact ⟨fun c ↦ h0 _ (Finset.mem_union_left _ ((mem_image L.rHot _).mpr ⟨c, rfl⟩)),
    h0 _ (Finset.mem_union_right _ hqS)⟩
theorem pEnc_mul_zeroProjOn {N : ℕ} (L : StepOneHotLayout N) (S_clean : Finset (Wire N)) (hqS :
    L.qEnc ∈ S_clean) : predProj (encValidPred L) * zeroProjOn (L.rHot.image ∪ S_clean) =
    zeroProjOn (L.rHot.image ∪ S_clean) := by
  refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  rw [← mulVec_mulVec, zeroProjOn_mulVec_ket]
  by_cases h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0
  · rw [ite_eq_left h0, predProj_mulVec_ket,
      ite_eq_left (encValid_of_zero L hqS h0)]
  · rw [ite_eq_right h0, mulVec_zero]
theorem preserves_comm_pEnc {N : ℕ} (L : StepOneHotLayout N) {M : Operator (2 ^ N)} (hPres :
    PreservesWires M (L.rHot.image ∪ {L.qEnc})) : M * predProj (encValidPred L) = predProj
    (encValidPred L) * M :=
  preservesWires_comm_predProj hPres fun α β h ↦ by
    have hH (c : Fin 128) := h _ (Finset.mem_union_left _ ((mem_image L.rHot _).mpr ⟨c, rfl⟩))
    have hQ := h L.qEnc (by simp)
    unfold encValidPred; exact decide_eq_decide.mpr
      ⟨fun ⟨hc, hq⟩ ↦ ⟨fun c ↦ (hH c).symm.trans (hc c), hQ.symm.trans hq⟩,
       fun ⟨hc, hq⟩ ↦ ⟨fun c ↦ (hH c).trans (hc c), hQ.trans hq⟩⟩
theorem cleanPredXo_mul_eEnc_zeroProjOn {N : ℕ} (L : StepOneHotLayout N)
    (S_clean : Finset (Wire N)) (hDisjHotS : Disjoint L.rHot.image S_clean)
    (hqS : L.qEnc ∈ S_clean) :
    let E_enc := (hot128Rev L).toCircuit.eval.1 * predProj (encValidPred L)
    Mobius126OneHot.cleanPredProj S_clean (xoOneHotPred L.rCtx L.rHot) * (E_enc * zeroProjOn
      (L.rHot.image ∪ S_clean)) =
      E_enc * zeroProjOn (L.rHot.image ∪ S_clean) := by
  intro E_enc; have hk (γ : BitAssignment N) : SelectSwapQROM.ket γ = CoherentAlias.ket γ := rfl
  refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  simp only [← mulVec_mulVec, zeroProjOn_mulVec_ket]
  by_cases h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0
  · rw [ite_eq_left h0, hk, e_enc_mulVec_ket L β, ite_eq_left (encValid_of_zero L hqS h0)]
    let x := Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β;
      let β₁ := Function.update β (L.rHot x) 1
    have hS1 (w : Wire N) (hw : w ∈ S_clean) : β₁ w = 0 := by
      have hne : w ≠ L.rHot x := fun he ↦
        Finset.disjoint_left.mp hDisjHotS ((mem_image L.rHot _).mpr ⟨x, he.symm⟩) hw
      exact (update_of_ne hne 1 β).trans (h0 w (Finset.mem_union_right _ hw))
    have hIdx : Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β₁ = x :=
      congrArg (basisBits 7).symm (funext
      fun b ↦ update_of_ne (L.hCtxHot.ne b x) _ _)
    have hXo : xoOneHotPred L.rCtx L.rHot β₁ = true := by
      unfold xoOneHotPred; rw [hIdx, decide_eq_true_eq]; intro g
      by_cases hgx : g = x
      · subst hgx; simp [β₁]
      · rw [ite_eq_right hgx]; exact (update_of_ne (L.rHot.wires.injective.ne hgx) 1 β).trans
          (h0 _ (Finset.mem_union_left _ ((mem_image L.rHot _).mpr ⟨g, rfl⟩)))
    dsimp only [Mobius126OneHot.cleanPredProj]
    rw [← mulVec_mulVec, ← hk, predProj_mulVec_ket, ite_eq_left hXo, zeroProjOn_mulVec_ket,
      ite_eq_left hS1]
  · rw [ite_eq_right h0, mulVec_zero, mulVec_zero]
theorem eEnc_comm_embedMatrix {N k : ℕ} (L : StepOneHotLayout N) (r : QRegister k N)
    (hrCtx : r.DisjointWires L.rCtx) (hrHot : r.DisjointWires L.rHot)
    (hrEnc : ∀ j, r j ≠ L.qEnc) (M : Operator (2 ^ k)) :
    let E_enc := (hot128Rev L).toCircuit.eval.1 * predProj (encValidPred L)
    (r.embedMatrix M) * E_enc = E_enc * (r.embedMatrix M) := by
  intro E_enc
  have hnC (i : Fin 7) : L.rCtx i ∉ Set.range r.wires := fun ⟨j, hj⟩ ↦ hrCtx.ne j i hj
  have hnH (c : Fin 128) : L.rHot c ∉ Set.range r.wires := fun ⟨j, hj⟩ ↦ hrHot.ne j c hj
  have hnQ : L.qEnc ∉ Set.range r.wires := fun ⟨j, hj⟩ ↦ hrEnc j hj
  refine Solution.CircuitModular.UnsignedGivens.matrix_ext_ket fun β ↦ ?_
  change ((r.embedMatrix M) * E_enc).mulVec (CoherentAlias.ket β) = (E_enc * (r.embedMatrix
    M)).mulVec (CoherentAlias.ket β)
  rw [← mulVec_mulVec (CoherentAlias.ket β) (r.embedMatrix M) E_enc, ← mulVec_mulVec
    (CoherentAlias.ket β) E_enc (r.embedMatrix M), e_enc_mulVec_ket, embedMatrix_mulVec_ket,
    mulVec_sum]
  by_cases hS : encValidPred L β = true
  · obtain ⟨hH0, hQ0⟩ : (∀ c, β (L.rHot c) = 0) ∧ β L.qEnc = 0 := by
      unfold encValidPred at hS; exact of_decide_eq_true hS
    let x := Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β
    have hloc : CoherentAlias.localIdx r (Function.update β (L.rHot x) 1) = CoherentAlias.localIdx r
      β := congrArg (basisBits k).symm (funext fun j ↦ update_of_ne (hrHot.ne j x) _ _)
    rw [ite_eq_left hS, embedMatrix_mulVec_ket, hloc]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    let β' := writeReg β r (basisBits k l)
    have hIdx' : Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β' = x :=
      congrArg (basisBits 7).symm (funext fun i ↦
        CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ (hnC i))
    have hS' : encValidPred L β' = true := by
      unfold encValidPred; rw [decide_eq_true_eq]
      exact ⟨fun c ↦ (CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ (hnH c)).trans (hH0 c),
        (CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnQ).trans hQ0⟩
    have hUpd : Function.update β' (L.rHot x) 1 = writeReg (Function.update β (L.rHot x) 1) r
        (basisBits k l) := by
      funext w; rcases eq_or_ne w (L.rHot x) with rfl | hw
      · simp [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ (hnH x)]
      · by_cases hwr : w ∈ Set.range r.wires
        · obtain ⟨j, rfl⟩ := hwr; simp [β', update_of_ne hw, CoherentAlias.writeReg_apply_reg]
        · simp [β', update_of_ne hw, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hwr]
    rw [mulVec_smul, e_enc_mulVec_ket, ite_eq_left hS', hIdx', hUpd]
  · rw [ite_eq_right hS, mulVec_zero]
    refine (Finset.sum_eq_zero fun l _ ↦ ?_).symm
    let β' := writeReg β r (basisBits k l)
    have hnS' : encValidPred L β' ≠ true := fun hS' ↦ hS (by
      obtain ⟨hH', hQ'⟩ : (∀ c, β' (L.rHot c) = 0) ∧ β' L.qEnc = 0 := by
        unfold encValidPred at hS'; exact of_decide_eq_true hS'
      unfold encValidPred; rw [decide_eq_true_eq]
      exact ⟨fun c ↦ (CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ (hnH c)).symm.trans (hH' c),
        (CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnQ).symm.trans hQ'⟩)
    rw [mulVec_smul, e_enc_mulVec_ket, ite_eq_right hnS', smul_zero]
/-- Embedded `(mAct + (7 + 128))`-wire mux on `rAct` and `L.rCtx ++ L.rHot`. -/
noncomputable abbrev hotMux135 {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
  (hActCtx : rAct.DisjointWires L.rCtx) (hActHot : rAct.DisjointWires L.rHot) (F : (Fin (7 + 128) →
  Bool) → Unitary (2 ^ mAct)) : Unitary (2 ^ N) := (rAct.concat (L.rCtx.concat L.rHot L.hCtxHot)
  (disjointWires_concat_right L.hCtxHot hActCtx hActHot)).embedUnitary (muxOnAct mAct (7 + 128) F)
/-- Embedded `(mAct + 7)`-wire mux on `rAct` and `L.rCtx` via `stepOneHotCtrlBits`. -/
noncomputable abbrev ctxMux7 {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
  (hActCtx : rAct.DisjointWires L.rCtx) (F : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) : Unitary
  (2 ^ N) := (rAct.concat L.rCtx hActCtx).embedUnitary (muxOnAct mAct 7 (fun y ↦ F
  (stepOneHotCtrlBits y)))
theorem mux135_mul_eEnc_eq {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
    (hActCtx : rAct.DisjointWires L.rCtx) (hActHot : rAct.DisjointWires L.rHot)
    (hActEnc : ∀ j, rAct j ≠ L.qEnc) (F : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) :
    let E_enc := (hot128Rev L).toCircuit.eval.1 * predProj (encValidPred L)
    (hotMux135 L rAct hActCtx hActHot F).1 * E_enc =
      E_enc * (ctxMux7 L rAct hActCtx F).1 := by
  intro E_enc; let rCH := L.rCtx.concat L.rHot L.hCtxHot
  have hDisjCH := disjointWires_concat_right L.hCtxHot hActCtx hActHot
  have hBop {m : ℕ} (r : QRegister m N) (c : Fin (2 ^ m)) (γ : BitAssignment N) :
    (r.basisOutcomeProjector c).mulVec (CoherentAlias.ket γ) =
        if r.extractIndex ((basisBits N).symm γ) = c then CoherentAlias.ket γ else 0 := by
    simp [CoherentAlias.ket, basisState, eq_comm]
  have hComm {m : ℕ} (r : QRegister m N) (hr : rAct.DisjointWires r) (A : Operator (2 ^ mAct)) (c :
    Fin (2 ^ m)) : r.basisOutcomeProjector c * rAct.embedMatrix A = rAct.embedMatrix A *
    r.basisOutcomeProjector c := (rAct.embedMatrix_comm_of_disjoint r hr A _).symm
  have hMuxKet {m : ℕ} (r : QRegister m N) (hr : rAct.DisjointWires r) (H : Fin (2 ^ m) → Unitary (2
      ^ mAct)) (γ : BitAssignment N) : (muxUnitary r rAct hr.symm H).1.mulVec (CoherentAlias.ket γ)
      = (rAct.embedMatrix (H (r.extractIndex ((basisBits N).symm γ))).1).mulVec
      (CoherentAlias.ket γ) := by
    dsimp only [muxUnitary]; rw [sum_mulVec, Finset.sum_eq_single (r.extractIndex ((basisBits
      N).symm γ))]
    · rw [hComm r hr, ← mulVec_mulVec, hBop, ite_eq_left rfl]
    · intro c _ hne; rw [hComm r hr, ← mulVec_mulVec, hBop, ite_eq_right hne.symm,
        mulVec_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine Solution.CircuitModular.UnsignedGivens.matrix_ext_ket fun β ↦ ?_
  dsimp only [hotMux135, ctxMux7]
  change (_ * E_enc).mulVec (CoherentAlias.ket β) = (E_enc * _).mulVec (CoherentAlias.ket β)
  rw [← mulVec_mulVec (CoherentAlias.ket β) _ E_enc, ← mulVec_mulVec (CoherentAlias.ket β) E_enc _,
    embedUnitary_muxOnAct, embedUnitary_muxOnAct, hMuxKet L.rCtx hActCtx]
  let c7 := L.rCtx.extractIndex ((basisBits N).symm β)
  have hCommAct : (rAct.embedMatrix (F (stepOneHotCtrlBits (bitsOfFin 7 c7))).1 * E_enc).mulVec
    (CoherentAlias.ket β) = (E_enc * rAct.embedMatrix (F (stepOneHotCtrlBits (bitsOfFin 7
    c7))).1).mulVec (CoherentAlias.ket β) := congrArg (fun M ↦ M.mulVec (CoherentAlias.ket β))
    (eEnc_comm_embedMatrix L rAct hActCtx hActHot hActEnc _)
  rw [mulVec_mulVec (CoherentAlias.ket β) E_enc _, ← hCommAct, ← mulVec_mulVec (CoherentAlias.ket β)
    _ E_enc]
  dsimp only [E_enc]; rw [e_enc_mulVec_ket]
  by_cases hS : encValidPred L β = true
  · obtain ⟨hH0, _⟩ : (∀ c, β (L.rHot c) = 0) ∧ β L.qEnc = 0 := by
      unfold encValidPred at hS; exact of_decide_eq_true hS
    rw [ite_eq_left hS]; let x := Solution.CircuitModular.UnsignedGivens.localIdx L.rCtx β
    let β₁ := Function.update β (L.rHot x) 1
    let c135 := rCH.extractIndex ((basisBits N).symm β₁)
    have hBits : bitsOfFin (7 + 128) c135 = stepOneHotCtrlBits (bitsOfFin 7 c7) := by
      funext idx; dsimp only [bitsOfFin, stepOneHotCtrlBits]
      rw [basisBits_extractIndex, SelectSwapQROM.basisBits_symm]
      by_cases hlt : idx.val < 7
      · have hi : idx = Fin.castAdd 128 ⟨idx.val, hlt⟩ := rfl
        have hrw : rCH idx = L.rCtx ⟨idx.val, hlt⟩ := by
          conv_lhs => rw [hi]; exact concat_apply_left ..
        simp only [hlt, ↓reduceDIte, hrw, β₁, update_of_ne (L.hCtxHot.ne _ x), c7,
          basisBits_extractIndex, SelectSwapQROM.basisBits_symm]
      · simp only [hlt, ↓reduceDIte]
        let g : Fin 128 := ⟨idx.val - 7, by omega⟩
        have hi : idx = Fin.natAdd 7 g := Fin.ext (by dsimp [g]; omega)
        have hrw : rCH idx = L.rHot g := by rw [hi]; exact concat_apply_right ..
        have hc7 : finOfBits 7 (bitsOfFin 7 c7) = x := by
          rw [finOfBits_bitsOfFin]; apply (basisBits 7).injective; funext j
          rw [basisBits_extractIndex, SelectSwapQROM.basisBits_symm]
          exact (congrFun (basisBits_symm_eq (fun k ↦ β (L.rCtx k))) j).symm
        rw [hrw, hc7]
        by_cases hgx : g = x
        · rw [hgx]; simp [β₁, show idx.val - 7 = x.val from congrArg Fin.val hgx]
        · have hv : idx.val - 7 ≠ x.val := fun he ↦ hgx (Fin.ext he)
          simp [β₁, update_of_ne (L.rHot.wires.injective.ne hgx), hH0 g, hv]
    rw [hMuxKet rCH hDisjCH, hBits]
  · rw [ite_eq_right hS, mulVec_zero, mulVec_zero]
theorem wpQAssign_one {Var : Type} [Fintype Var] {N : ℕ} (Ψ : Store Var →
    Observable (Fin (2 ^ N))) :
    qcWpQAssign (1 : Unitary (2 ^ N)) Ψ = Ψ := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext; ext i j; simp [qcWpQAssign, qcQAssignObsMap]
theorem wpQAssign_comp {Var : Type} [Fintype Var] {N : ℕ} (U₁ U₂ : Unitary (2 ^ N)) (Ψ :
    QCAssertion Var (2 ^ N)) : qcWpQAssign U₁ (qcWpQAssign U₂ Ψ) = qcWpQAssign (U₂ * U₁) Ψ := by
  funext σ; apply Subtype.ext; simp [qcWpQAssign, qcQAssignObsMap, conj_coe]
theorem restrictPred_wp_revComputeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} (v :
    Var) (p : RevCompute N) (S : BitAssignment N → Bool) (hval : ∀ β, S β = true → p.validOn β =
    true) (Θ : QCAssertion Var (2 ^ N)) : restrictPred S (wp (revComputeDyn p).compile Θ) =
    restrictPred S (qcWpQAssign p.toCircuit.eval Θ) := by
  induction p generalizing S Θ with
  | id =>
      change restrictPred S Θ = restrictPred S (qcWpQAssign (Circuit.identity : Circuit N).eval Θ)
      rw [Circuit.eval_identity, wpQAssign_one]
  | x q => simp [revComputeDyn, RevCompute.toCircuit]
  | cnot c t h => simp [revComputeDyn, RevCompute.toCircuit]
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      have hS_eq : S = fun β ↦ S β && decide (∀ i : Fin 1, β (QRegister.singleton anc i) = 0) := by
        funext β; by_cases hS : S β = true
        · rw [hS, Bool.true_and, eq_comm, decide_eq_true_iff]
          exact fun _ ↦ beq_iff_eq.mp (hval β hS)
        · rw [Bool.eq_false_iff.mpr hS, Bool.false_and]
      have hR (Φ : QCAssertion Var (2 ^ N)) : restrictPred S Φ = restrictPred S
          (restrictAssertionToZeroAncilla Φ (QRegister.singleton anc)) := by
        rw [restrictAssertionToZeroAncilla_eq_restrictPred, restrictPred_restrictPred, ← hS_eq]
      rw [hR, revComputeDyn, DynamicCircuit.qc_wp_andCompute c₁ c₂ anc
        h₁₂ h₁a h₂a Θ, ← hR]
      rfl
  | seq p₁ p₂ ih₁ ih₂ =>
      have hv₁ : ∀ β, S β = true → p₁.validOn β = true :=
        fun β hS ↦ (Bool.and_eq_true _ _).mp (hval β hS) |>.1
      have hv₂ : ∀ γ, S (p₁.invBits γ) = true → p₂.validOn γ = true := fun γ hγ ↦ by
        have h := (Bool.and_eq_true _ _).mp (hval (p₁.invBits γ) hγ) |>.2
        rwa [p₁.fwdBits_invBits] at h
      have h1 := TransRealizes.computeDyn v p₁ S hv₁
      simp only [revComputeDyn, DynamicCircuit.compile_seq, wp_qSeq]
      rw [← h1.clean_post, ih₂ _ hv₂ Θ, h1.clean_post, ih₁ S hv₁, wpQAssign_comp]; rfl
theorem transRealizes_extract_enc_dec {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ} (v :
    Var) (rScr : QRegister s N) (p : RevCompute N) {S_scr : BitAssignment N → Bool} (hS : S_scr =
    fun β ↦ decide (∀ j : Fin s, β (rScr j) = 0)) (hval : ∀ β, S_scr β = true → p.validOn β = true)
    {P_enc P_dec : DynamicCircuit Var N} (hEnc : TransRealizes v S_scr (fun γ ↦ S_scr (p.invBits γ))
    p.toCircuit.eval P_enc) (hDec : TransRealizes v (fun γ ↦ S_scr (p.invBits γ)) S_scr
    p.toCircuit.eval⁻¹ P_dec) : (∀ Φ : QCAssertion Var (2 ^ N), (∀ σ val, Φ (Function.update σ v
    val) = Φ σ) → restrictPred S_scr (wp P_enc.compile Φ) = restrictPred S_scr (qcWpQAssign
    p.toCircuit.eval Φ)) ∧ (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ
    σ) → restrictPred (fun γ ↦ S_scr (p.invBits γ)) (wp P_dec.compile Θ) = restrictPred (fun γ ↦
    S_scr (p.invBits γ)) (qcWpQAssign p.toCircuit.eval⁻¹ Θ)) := by
  let rEmp : QRegister 0 N := ⟨⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩⟩
  have hDisj : rEmp.DisjointWires rScr := QRegister.disjoint_iff.mpr fun i ↦ Fin.elim0 i
  have hId {Q : DynamicCircuit Var N} (hQ : TransRealizes v S_scr S_scr 1 Q) (Θ : QCAssertion Var (2
      ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) : restrictPred S_scr (wp Q.compile Θ)
      = restrictPred S_scr Θ := by
    subst hS
    have hQ' : TransRealizes v (fun β ↦ decide (∀ j : Fin s, β (rScr j) = 0)) (fun β ↦ decide (∀ j :
      Fin s, β (rScr j) = 0)) (rEmp.embedUnitary 1) Q := rEmp.embedUnitary_one.symm ▸ hQ
    have h := (cleanRealizes_of_transRealizes rEmp rScr hDisj hQ').2.2.1 Θ hΘ
    rwa [restrictAssertionToZeroAncilla_eq_restrictPred,
      restrictAssertionToZeroAncilla_eq_restrictPred, embedUnitary_one, wpQAssign_one] at h
  let U := p.toCircuit.eval
  let S_post := fun γ ↦ S_scr (p.invBits γ)
  have hDecWp (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
      restrictPred S_post (wp P_dec.compile Θ) = restrictPred S_post (qcWpQAssign U⁻¹ Θ) := by
    have hSeq1 : TransRealizes v S_scr S_scr 1 ((revComputeDyn p).seq P_dec) := inv_mul_cancel U ▸
      ((TransRealizes.computeDyn v p S_scr hval).seq hDec)
    have hPD := hId hSeq1 Θ hΘ
    simp only [DynamicCircuit.compile_seq, wp_qSeq, restrictPred_wp_revComputeDyn v p S_scr hval]
      at hPD
    have hProj : p.toCircuit.eval.1 * predProj S_scr * (p.toCircuit.eval.1)ᴴ = predProj S_post := by
      have hm : p.toCircuit.eval.1 * predProj S_scr = predProj S_post * p.toCircuit.eval.1 :=
        hEnc.map_proj
      rw [hm, Matrix.mul_assoc, ← star_eq_conjTranspose, U.prop.2, Matrix.mul_one]
    have hUinv : (U⁻¹ : Unitary (2 ^ N)).1 = (p.toCircuit.eval.1)ᴴ := by
      simp [U, star_eq_conjTranspose]
    funext σ; apply Subtype.ext
    have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦
      x.1.conj p.toCircuit.eval.1) (congrFun hPD σ)
    have hMap : predProj S_post * p.toCircuit.eval.1 = p.toCircuit.eval.1 * predProj S_scr :=
      hEnc.map_proj.symm
    simpa only [restrictPred_coe, qcWpQAssign, qcQAssignObsMap, conj_coe, conj_conj, hUinv,
      coe_star,
      star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.mul_assoc, hProj, hMap] using hv
  refine ⟨fun Φ hΦ ↦ ?_, hDecWp⟩
  let Θ' := qcWpQAssign U Φ
  have hΘ' (σ : Store Var) (val : ℤ) : Θ' (Function.update σ v val) = Θ' σ := by
    dsimp only [Θ', qcWpQAssign, qcQAssignObsMap]; rw [hΦ σ val]
  have hD := hDecWp Θ' hΘ'; rw [wpQAssign_comp, mul_inv_cancel, wpQAssign_one] at hD
  have hSeq2 : TransRealizes v S_scr S_scr 1 (P_enc.seq P_dec) := inv_mul_cancel U ▸ (hEnc.seq hDec)
  have hED := hId hSeq2 Θ' hΘ'; simp only [DynamicCircuit.compile_seq, wp_qSeq] at hED
  rw [← hEnc.clean_post Φ, ← hD, hEnc.clean_post]; exact hED
theorem turnaroundMatrixCalc {m : Type} [Fintype m] (P_out P_enc P_post Q_xo U_enc E G_in G_out
    W_in W_out M_enc M_mid M_dec M_Θ : Matrix m m ℂ) (hPoutH : P_outᴴ = P_out) (hQxoH : Q_xoᴴ =
    Q_xo) (hPencH : P_encᴴ = P_enc) (hPpostH : P_postᴴ = P_post) (hPE : P_post * E = E) (hUinv :
    U_encᴴ * E = P_enc) (hGinP : P_enc * (G_in * P_out) = G_in * P_out) (hGoutP : P_enc * (G_out *
    P_out) = G_out * P_out) (hInterIn : E * (G_in * P_out) = W_in * (Q_xo * (E * P_out))) (hInterOut
    : E * (G_out * P_out) = W_out * (Q_xo * (E * P_out))) (hEncRaw : P_enc * M_enc * P_enc = Eᴴ *
    M_mid * E) (hMidMat : Q_xo * (W_inᴴ * M_mid * W_in) * Q_xo = Q_xo * (W_outᴴ * M_dec * W_out) *
    Q_xo) (hDecRaw : P_post * M_dec * P_post = P_post * (U_enc * M_Θ * U_encᴴ) * P_post) : P_out *
    (G_inᴴ * M_enc * G_in) * P_out = P_out * (G_outᴴ * M_Θ * G_out) * P_out := by
  have hAbs {P X M : Matrix m m ℂ} (hPH : Pᴴ = P) (hPX : P * X = X) : Xᴴ * M * X = Xᴴ * (P * M * P)
      * X := by
    have hXP : Xᴴ * P = Xᴴ := by
      calc Xᴴ * P = (P * X)ᴴ := by rw [conjTranspose_mul, hPH]
        _ = Xᴴ := by rw [hPX]
    calc Xᴴ * M * X = (Xᴴ * P) * M * (P * X) := by rw [hXP, hPX]
      _ = Xᴴ * (P * M * P) * X := by simp only [Matrix.mul_assoc]
  have hOut {G M : Matrix m m ℂ} : P_out * (Gᴴ * M * G) * P_out = (G * P_out)ᴴ * M * (G * P_out) :=
    by
    rw [conjTranspose_mul, hPoutH]; simp only [Matrix.mul_assoc]
  have hR : U_encᴴ * (P_post * (E * (G_out * P_out))) = G_out * P_out := by
    rw [← Matrix.mul_assoc P_post, hPE, ← Matrix.mul_assoc, hUinv, hGoutP]
  have hL : (E * (G_out * P_out))ᴴ * P_post * U_enc = (G_out * P_out)ᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hPpostH,
      ← Matrix.mul_assoc] using congrArg (·ᴴ) hR
  calc P_out * (G_inᴴ * M_enc * G_in) * P_out
      = (E * (G_in * P_out))ᴴ * M_mid * (E * (G_in * P_out)) := by
          rw [hOut, hAbs hPencH hGinP, hEncRaw, conjTranspose_mul E]; simp only [Matrix.mul_assoc]
    _ = (E * P_out)ᴴ * (Q_xo * (W_inᴴ * M_mid * W_in) * Q_xo) * (E * P_out) := by
          rw [hInterIn, conjTranspose_mul W_in, conjTranspose_mul Q_xo, hQxoH]
          simp only [Matrix.mul_assoc]
    _ = (E * (G_out * P_out))ᴴ * M_dec * (E * (G_out * P_out)) := by
          rw [hMidMat, hInterOut, conjTranspose_mul W_out, conjTranspose_mul Q_xo, hQxoH]; simp only
            [Matrix.mul_assoc]
    _ = ((E * (G_out * P_out))ᴴ * P_post * U_enc) * M_Θ *
          (U_encᴴ * (P_post * (E * (G_out * P_out)))) := by
          rw [hAbs hPpostH (by rw [← Matrix.mul_assoc, hPE]), hDecRaw]; simp only [Matrix.mul_assoc]
    _ = P_out * (G_outᴴ * M_Θ * G_out) * P_out := by rw [hL, hR, ← hOut]
theorem cleanTurnaroundWp_withHot128Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {N mAct : ℕ}
    (v : Var) (rAct : QRegister mAct N) (L : StepOneHotLayout N) (hActCtx : rAct.DisjointWires
    L.rCtx) (hActHot : rAct.DisjointWires L.rHot) (hActEnc : ∀ j, rAct j ≠ L.qEnc) (S_clean : Finset
    (Wire N)) (hDisjHotS : Disjoint L.rHot.image S_clean) (hqS : L.qEnc ∈ S_clean) (F_in F_out :
    (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) (mid : DynamicCircuit Var N) (hmid :
    XoTurnaroundWp v (Mobius126OneHot.cleanPredProj S_clean (xoOneHotPred L.rCtx L.rHot))
    (hotMux135 L rAct hActCtx hActHot F_in) (hotMux135 L rAct hActCtx hActHot F_out) mid) :
    CleanTurnaroundWp v (L.rHot.image ∪ S_clean) (ctxMux7 L rAct hActCtx F_in) (ctxMux7 L rAct
    hActCtx F_out) (withHot128Dyn v L mid) := by
  obtain ⟨⟨hval, m, hbij, hfwd⟩, _⟩ := hot128Rev_equiv v L
  have hEnc := hbij.to_transRealizes_revCompute (hot128Rev L) hfwd
  have hDec := TransRealizes.uncomputeDyn v (hot128Rev L) (encValidPred L) hval
  let rScr129 := L.rHot.concat (QRegister.singleton L.qEnc) (QRegister.disjoint_iff.mpr fun g _ ↦
    L.hHotEnc g)
  have hScrPred : encValidPred L = fun β ↦ decide (∀ j : Fin (128 + 1), β (rScr129 j) = 0) := by
    funext β; unfold encValidPred; apply decide_eq_decide.mpr
    refine ⟨fun ⟨h1, h2⟩ j ↦ ?_, fun hR ↦ ⟨fun c ↦ ?_, ?_⟩⟩
    · by_cases hj : j.val < 128
      · rw [show j = Fin.castAdd 1 ⟨j.val, hj⟩ from rfl, concat_apply_left]; exact h1 _
      · rw [show j = Fin.natAdd 128 0 from Fin.ext (by dsimp; omega), concat_apply_right]; exact h2
    · have h := hR (Fin.castAdd 1 c); rwa [concat_apply_left] at h
    · have h := hR (Fin.natAdd 128 0); rwa [concat_apply_right, QRegister.singleton_apply] at h
  obtain ⟨hEncWpFn, hDecWpFn⟩ := transRealizes_extract_enc_dec v rScr129 (hot128Rev L) hScrPred
    hval hEnc hDec
  let rActCtx := rAct.concat L.rCtx hActCtx; let P_out := zeroProjOn (L.rHot.image ∪ S_clean)
  let Q_xo := Mobius126OneHot.cleanPredProj S_clean (xoOneHotPred L.rCtx L.rHot)
  let P_enc := predProj (encValidPred L)
  let P_post := predProj (fun γ ↦ encValidPred L ((hot128Rev L).invBits γ))
  let U_enc := (hot128Rev L).toCircuit.eval; let E_enc := U_enc.1 * P_enc
  let W_in := hotMux135 L rAct hActCtx hActHot F_in
  let W_out := hotMux135 L rAct hActCtx hActHot F_out; let G_in := ctxMux7 L rAct hActCtx F_in
  let G_out := ctxMux7 L rAct hActCtx F_out
  have hDisjACH : Disjoint rActCtx.image (L.rHot.image ∪ {L.qEnc}) := by
    rw [Finset.disjoint_union_right]
    refine ⟨disjoint_image_of_disjointWires
      (disjointWires_concat_left hActCtx hActHot L.hCtxHot),
      Finset.disjoint_singleton_right.mpr fun hm ↦ ?_⟩
    obtain ⟨k, hk⟩ := (mem_image rActCtx _).mp hm
    by_cases hlt : k.val < mAct
    · exact hActEnc ⟨k.val, hlt⟩ ((rAct.concat_apply_left L.rCtx hActCtx ⟨k.val, hlt⟩).symm.trans
        hk)
    · exact L.hCtxEnc ⟨k.val - mAct, by omega⟩ ((by
        rw [show k = Fin.natAdd mAct ⟨k.val - mAct, by omega⟩ from Fin.ext (by dsimp; omega)] at hk
        exact (rAct.concat_apply_right L.rCtx hActCtx _).symm.trans hk))
  have hPredMul (q : BitAssignment N → Bool) : predProj q * predProj q = predProj q := by
    rw [predProj, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    cases q (basisBits N i) <;> simp
  have hPpost2 : P_post * P_post = P_post := hPredMul _
  have hPE : P_post * E_enc = E_enc := by
    dsimp only [E_enc]; rw [hEnc.map_proj, ← Matrix.mul_assoc, hPpost2]
  have hUinvE : U_enc.1ᴴ * E_enc = P_enc := by
    dsimp only [E_enc]; rw [← Matrix.mul_assoc, ← star_eq_conjTranspose, U_enc.prop.1, one_mul]
  have hGP (G : Unitary (2 ^ N)) (hPres : PreservesWires G.1 (L.rHot.image ∪ {L.qEnc})) : P_enc *
      (G.1 * P_out) = G.1 * P_out := by
    rw [← Matrix.mul_assoc, ← preserves_comm_pEnc L hPres, Matrix.mul_assoc, pEnc_mul_zeroProjOn
      L S_clean hqS]
  have hInter (F : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) : E_enc * ((ctxMux7 L rAct hActCtx
      F).1 * P_out) = (hotMux135 L rAct hActCtx hActHot F).1 * (Q_xo * (E_enc * P_out)) := by
    rw [cleanPredXo_mul_eEnc_zeroProjOn L S_clean hDisjHotS hqS, ← Matrix.mul_assoc, ←
      mux135_mul_eEnc_eq L rAct hActCtx hActHot hActEnc F, Matrix.mul_assoc]
  refine ⟨count_withHot128Dyn_toff v L hmid.1, fun Θ hΘ σ val ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · simpa only [withHot128Dyn, hot128DecDyn, DynamicCircuit.compile_seq, wp_qSeq] using
      hEnc.update_self _ (hmid.2.1 _ (hDec.update_self Θ hΘ)) σ val
  · funext σ; apply Subtype.ext; apply HermitianMat.ext
    let Ψ_dec := wp (hot128DecDyn v L).compile Θ
    have hΨ_dec : ∀ σ' val, Ψ_dec (Function.update σ' v val) = Ψ_dec σ' := hDec.update_self Θ hΘ
    have hMidMat : Q_xo * (W_in.1ᴴ * (wp mid.compile Ψ_dec σ).1.mat * W_in.1) * Q_xo = Q_xo *
        (W_out.1ᴴ * (Ψ_dec σ).1.mat * W_out.1) * Q_xo := by
      simpa only [qcWpQAssign, qcQAssignObsMap, conj_coe, conj_apply_mat, coe_star,
        star_eq_conjTranspose, conjTranspose_conjTranspose, cleanPredProj_conjTranspose] using
        congrArg HermitianMat.mat (hmid.2.2 Ψ_dec hΨ_dec σ)
    have hEncRaw : P_enc * (wp (hot128EncDyn v L).compile (wp mid.compile Ψ_dec) σ).1.mat * P_enc
        = E_encᴴ * (wp mid.compile Ψ_dec σ).1.mat * E_enc := by
      have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦
        x.1.mat) (congrFun (hEncWpFn (wp mid.compile
        Ψ_dec) (hmid.2.1 Ψ_dec hΨ_dec)) σ)
      simp only [restrictPred_coe, qcWpQAssign, qcQAssignObsMap, conj_coe, conj_apply_mat, coe_star,
        star_eq_conjTranspose, conjTranspose_conjTranspose, predProj_conjTranspose] at hv
      dsimp only [P_enc, E_enc, U_enc]; rw [hv, conjTranspose_mul, predProj_conjTranspose]
      simp only [Matrix.mul_assoc]
    have hUinv : ((hot128Rev L).toCircuit.eval⁻¹ : Unitary (2 ^ N)).1 = U_enc.1ᴴ := by
      simp [U_enc, star_eq_conjTranspose]
    have hDecRaw : P_post * (Ψ_dec σ).1.mat * P_post = P_post * (U_enc.1 * (Θ σ).1.mat * U_enc.1ᴴ) *
        P_post := by
      simpa only [P_post, Ψ_dec, hot128DecDyn, restrictPred_coe, qcWpQAssign, qcQAssignObsMap,
        conj_coe, conj_apply_mat, hUinv, coe_star, star_eq_conjTranspose,
        conjTranspose_conjTranspose, predProj_conjTranspose] using congrArg (fun x :
          Observable (Fin (2 ^
        N)) ↦ x.1.mat) (congrFun (hDecWpFn Θ hΘ) σ)
    have hSeq : wp (withHot128Dyn v L mid).compile Θ = wp (hot128EncDyn v L).compile (wp
        mid.compile Ψ_dec) := by
      rw [withHot128Dyn, DynamicCircuit.compile_seq, DynamicCircuit.compile_seq, wp_qSeq, wp_qSeq]
    have hRMat (G : Unitary (2 ^ N)) (Φ : QCAssertion Var (2 ^ N)) :
        (SelectSwapQROM.restrictZeroSet (qcWpQAssign G Φ) (L.rHot.image ∪ S_clean) σ).1.mat =
          P_out
        * (G.1ᴴ * (Φ σ).1.mat * G.1) * P_out := by
      simp [P_out, SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, conj_coe,
        conj_apply_mat, coe_star, star_eq_conjTranspose, zeroProjOn_conjTranspose]
    rw [hRMat, hRMat, hSeq]
    exact turnaroundMatrixCalc P_out P_enc P_post Q_xo U_enc.1 E_enc G_in.1 G_out.1 W_in.1 W_out.1
      (wp (hot128EncDyn v L).compile (wp mid.compile Ψ_dec) σ).1.mat (wp mid.compile Ψ_dec
      σ).1.mat (Ψ_dec σ).1.mat (Θ σ).1.mat (zeroProjOn_conjTranspose _)
      (cleanPredProj_conjTranspose _ _) (predProj_conjTranspose _) (predProj_conjTranspose _) hPE
      hUinvE (hGP G_in (preservesWires_embedMatrix_of_disjoint rActCtx _ _ hDisjACH)) (hGP G_out
      (preservesWires_embedMatrix_of_disjoint rActCtx _ _ hDisjACH)) (hInter F_in) (hInter F_out)
      hEncRaw hMidMat hDecRaw
attribute [irreducible] hot128EncDyn hot128DecDyn withHot128Dyn
theorem cleanTurnaroundWp_withHot128Dyn_congr_xoOneHot {Var : Type} [Fintype Var] [DecidableEq
  Var] {N mAct : ℕ} (v : Var) (rAct : QRegister mAct N) (L : StepOneHotLayout N) (hActCtx :
  rAct.DisjointWires L.rCtx) (hActHot : rAct.DisjointWires L.rHot) (hActEnc : ∀ j, rAct j ≠ L.qEnc)
  (S_clean : Finset (Wire N)) (hDisjHotS : Disjoint L.rHot.image S_clean) (hqS : L.qEnc ∈ S_clean)
  (F_in F_out : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) (mid : DynamicCircuit Var N) (hToff :
  mid.count .TOFF = 0) (hUpd : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val)
  = Θ σ) → ∀ σ val, wp mid.compile Θ (Function.update σ v val) = wp mid.compile Θ σ) (hConj : ∀ Θ :
  QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) → ∀ σ : Store Var,
  ((qcWpQAssign (hotMux135 L rAct hActCtx hActHot F_in) (wp mid.compile Θ) σ).1).conj
  (Mobius126OneHot.cleanPredProj S_clean (xoOneHotPred L.rCtx L.rHot)) = ((qcWpQAssign
    (hotMux135
  L rAct hActCtx hActHot F_out) Θ σ).1).conj (Mobius126OneHot.cleanPredProj S_clean (xoOneHotPred
  L.rCtx L.rHot))) : CleanTurnaroundWp v (L.rHot.image ∪ S_clean) (ctxMux7 L rAct hActCtx F_in)
  (ctxMux7 L rAct hActCtx F_out) (withHot128Dyn v L mid) := cleanTurnaroundWp_withHot128Dyn v
  rAct L hActCtx hActHot hActEnc S_clean hDisjHotS hqS F_in F_out mid ⟨hToff, hUpd, hConj⟩
theorem cleanRealizes_withHot128MuxDyn {Var : Type} [Fintype Var] [DecidableEq Var] {N mAct sScr :
    ℕ} (v : Var) (rAct : QRegister mAct N) (rCtx : QRegister 7 N) (rScr : QRegister sScr N) (hScr :
    129 ≤ sScr) (hActCtx : rAct.DisjointWires rCtx) (hActScr : rAct.DisjointWires rScr) (hCtxScr :
    rCtx.DisjointWires rScr) (F_out : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) (mid :
    DynamicCircuit Var N) (hmid : CleanPredRealizes v (Mobius126OneHot.cleanPredProj (rScr.slice
    128 (sScr - 128) (by omega)).image (xoOneHotPred rCtx (rScr.slice 0 128 (by omega))))
    (hotMux135 (stepScrLayout rCtx rScr hScr hCtxScr) rAct hActCtx (hActScr.compose_right _)
    F_out) mid) : Solution.CleanDyn.CleanRealizes v (rAct.concat rCtx hActCtx) rScr (muxOnAct mAct 7
      (fun
    y ↦ F_out (stepOneHotCtrlBits y))) (withHot128Dyn v (stepScrLayout rCtx rScr hScr hCtxScr)
    mid) := by
  let L := stepScrLayout rCtx rScr hScr hCtxScr
  let rTail := rScr.slice 128 (sScr - 128) (by omega)
  have hHotTail := rScr.slice_disjoint_of_le 0 128 128 (sScr - 128) (by omega) (by omega) le_rfl
  have hqMem : L.qEnc ∈ rTail.image := (mem_image rTail _).mpr ⟨⟨0, by omega⟩,
    (slice_apply ..).trans (congrArg rScr (Fin.ext (Nat.add_zero 128)))⟩
  have hActEnc (j : Fin mAct) : rAct j ≠ L.qEnc := hActScr.ne j ⟨128, by omega⟩
  have hMuxOne (k : ℕ) : muxOnAct mAct k (fun _ ↦ (1 : Unitary (2 ^ mAct))) = 1 := by
    apply Subtype.ext; dsimp only [muxOnAct, muxUnitary, embedUnitary_val]
    rw [← Finset.sum_mul, sum_basisOutcomeProjector, Submonoid.coe_one, embedMatrix_one, one_mul];
      rfl
  have hOne : hotMux135 L rAct hActCtx (hActScr.compose_right _) (fun _ ↦ 1) = 1 := by
    dsimp only [hotMux135]; rw [hMuxOne, embedUnitary_one]
  have hCT := cleanTurnaroundWp_withHot128Dyn v rAct L hActCtx (hActScr.compose_right _) hActEnc
    rTail.image (disjoint_image_of_disjointWires hHotTail) hqMem
    (fun _ ↦ 1) F_out mid ⟨hmid.1, hmid.2.2.1, fun Θ hΘ σ ↦ by
      rw [hOne, wpQAssign_one]; exact hmid.2.2.2 Θ hΘ σ⟩
  dsimp only [ctxMux7] at hCT; rw [hMuxOne 7, embedUnitary_one] at hCT
  have hScrEq : L.rHot.image ∪ rTail.image = rScr.image := by
    apply Finset.Subset.antisymm (Finset.union_subset (rScr.image_compose_subset _)
      (rScr.image_compose_subset _))
    intro w hw; obtain ⟨u, rfl⟩ := (mem_image rScr w).mp hw
    by_cases hu : u.val < 128
    · exact Finset.mem_union_left _ ((mem_image L.rHot _).mpr ⟨⟨u.val, hu⟩,
        (slice_apply ..).trans (congrArg rScr (Fin.ext (Nat.zero_add u.val)))⟩)
    · exact Finset.mem_union_right _ ((mem_image rTail _).mpr ⟨⟨u.val - 128, by omega⟩,
        (slice_apply ..).trans (congrArg rScr (Fin.ext (by dsimp; omega)))⟩)
  rw [hScrEq] at hCT
  have hDisjAS : (rAct.concat rCtx hActCtx).DisjointWires rScr := disjointWires_concat_left hActCtx
    hActScr hCtxScr
  refine Solution.CleanDyn.CleanRealizes.mk_of_disjoint v
    (rAct.concat rCtx hActCtx) rScr hDisjAS _ _
    hCT.1 hCT.2.1 fun Θ hΘ ↦ ?_
  have hAnc (Ψ : Store Var → Observable (Fin (2 ^ N))) : restrictAssertionToZeroAncilla Ψ rScr =
      SelectSwapQROM.restrictZeroSet Ψ rScr.image := by
    funext σ; apply Subtype.ext
    rw [restrictAssertionToZeroAncilla_coe, SelectSwapQROM.restrictZeroSet_coe,
      basisOutcomeProjector_zero_eq_zeroProjOn]
  rw [hAnc, hAnc]; dsimp only [L, stepScrLayout] at hCT
  have hCT2 := hCT.2.2 Θ hΘ; rw [wpQAssign_one] at hCT2; exact hCT2
end
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepBound148Borrow
end

@[expose] public section

/-!
# `155`-Toffoli Shared Symplectic `GF(2)` QROM
Rank-`155` shared-Toffoli symplectic `GF(2)` decomposition over `126 × 30` bitplanes (`16` output
planes, `620 T` core, `680 T` `w = 5` loader, `716 T` `w = 4` loader) realizing the
`tuned162SliceTargetFn` slice family (Low, Kliuchnikov, and Schaeffer, Quantum 8, 1375, 2024;
Gidney, Quantum 2, 74, 2018).
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned155Hot128SympQrom20
open QuantumComputation.Specs QuantumComputation.Specs.P450

section DataSection

open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCore
open Solution.Tuned162ScheduledSympQrom21

end DataSection

section CoreSection

open Operator QProg Matrix Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution CoherentAlias Solution.CleanDyn AliasPrep
open CompactBilinearPrep
open RankReducedPrepMid
open Solution.Tuned162ScheduledSympQrom21
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open scoped Matrix BigOperators

local instance (priority := 1000000) instNeZeroTwoPowSharedCore2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

end CoreSection

section MainSection

open Operator QProg Matrix Circuit Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution CoherentAlias Solution.CleanDyn AliasPrep
open CompactBilinearPrep
open MidReflCtxRetain RankReducedPrepMid
open DyadicPacketInnerPrep
open Solution.Tuned162ScheduledSympQrom21
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowSharedMain2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

end MainSection

section WalkClosures

open Operator QProg Matrix Circuit Real HermitianMat
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open BlockEncodingCore BlockEncodingCircuit
open Solution.CoherentAlias
open Solution.AliasPrep
open Solution.Phase2MidSandwich
open Solution.OptFactoredMag30AndCoin9
open Solution.Cat11CompactPhase2Bridge
open Solution.ReordOuter13Bridge
open Solution.ZeroRcHotPrepMid21Fast
open Solution.OptXMeasUnload21
open Solution.Tuned162ScheduledSympQrom21
open Solution.Tuned162StepSympAnfQrom21
open Solution.OptStepSympAnfQrom21
open Solution.TopIntegrationBridge
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam
open Solution.CompactStepZeroCmp20OuterParam
open Solution.StepAnfAndCoin14Core
open Solution.CompactStepCompact2504ZeroCmp20
open Solution.Pi145SOSPermBridge
open Solution.MidReflCtxRetain
open Solution.StepBound148Borrow
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowWalk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

end WalkClosures

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned155Hot128SympQrom20

end
