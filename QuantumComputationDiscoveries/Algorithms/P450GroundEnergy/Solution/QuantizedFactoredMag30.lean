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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FactoredMag30AndCoin9
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20OuterAnfParam

set_option exponentiation.threshold 512

@[expose] public section

/-!
# Exact `SU(2)` Quantized `factoredMag30` Algebra & `T38..T30` Words

Defines the parametric `5`-qubit factored `L = 30 = 2 × 5 × 3` column-`0` support, polarization, and
`L¹_30` probability deviation algebra (`factoredMag30Of`), together with `GateTrace` certificates
for the `38-T`, `34-T`, `32-T`, and `30-T` exact `SU(2)` magnitude splitters, the `28-T`, `24-T`,
`22-T` words, all five `5`-qubit splitters (`Quant86`, `Quant78`, `Quant72`, `Quant66`,
`Quant56`), Markov-kernel `L¹` contraction (`zeroCmpQuantInnerProb`), `AgreesOnElectronSector`,
`PulledSOSBlockEncoding`, and `PerturbedRefl2Cert` (`δIdx = 0`) closures.

## References
- V. Kliuchnikov, D. Maslov, and M. Mosca, *Quantum Inf. Comput.* **13**, 607–630 (2013),
  arXiv:1206.5236.
- N. J. Ross and P. Selinger, *Quantum Inf. Comput.* **16**, 901–953 (2016), arXiv:1403.2975.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit HermitianMat Real QuantumComputation.Specs
open QuantumComputation.Specs.P450 CoherentAlias CleanDyn AliasPrep FastUniform
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptFactoredMag30AndCoin9
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowQuantMag30 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Parametric Factored `30 = 2 × 5 × 3` Algebra & Exact Branch Probabilities -/

/-- Parametric `4`-qubit ancilla-free factored `L = 15 = 5 × 3` splitter from `1`-qubit `c5, c3`. -/
def factoredMag15Of (c5 c3 : Circuit 1) : Circuit 4 :=
  Circuit.sequence [
    c5.onRegister (QRegister.singleton (2 : Wire 4)),
    c3.onRegister (QRegister.singleton (3 : Wire 4)),
    postFactor15Circuit
  ]

/-- Parametric `5`-qubit ancilla-free factored `L = 30` splitter `H_0 ⊗ factoredMag15Of c5 c3`. -/
def factoredMag30Of (c5 c3 : Circuit 1) : Circuit 5 :=
  prepMag30Of (factoredMag15Of c5 c3)

theorem factoredMag15Of_count_toff (c5 c3 : Circuit 1)
    (h5 : c5.count PrimitiveGate.TOFF = 0) (h3 : c3.count PrimitiveGate.TOFF = 0) :
    (factoredMag15Of c5 c3).count PrimitiveGate.TOFF = 0 := by
  simp [factoredMag15Of, h5, h3]

theorem factoredMag15Of_count_t (c5 c3 : Circuit 1) :
    (factoredMag15Of c5 c3).count PrimitiveGate.T =
      c5.count PrimitiveGate.T + c3.count PrimitiveGate.T + 10 := by
  simp [factoredMag15Of]; omega

theorem factoredMag30Of_count_toff (c5 c3 : Circuit 1)
    (h5 : c5.count PrimitiveGate.TOFF = 0) (h3 : c3.count PrimitiveGate.TOFF = 0) :
    (factoredMag30Of c5 c3).count PrimitiveGate.TOFF = 0 := by
  simp [factoredMag30Of, prepMag30Of, factoredMag15Of_count_toff c5 c3 h5 h3]

theorem factoredMag30Of_count_t (c5 c3 : Circuit 1) :
    (factoredMag30Of c5 c3).count PrimitiveGate.T =
      c5.count PrimitiveGate.T + c3.count PrimitiveGate.T + 10 := by
  simp [factoredMag30Of, prepMag30Of, factoredMag15Of_count_t]

theorem factoredMag15Of_eval_eq (c5 c3 : Circuit 1) :
    (factoredMag15Of c5 c3).eval = idealFactoredMag15Of c5.eval c3.eval := by
  ext i j
  simp [factoredMag15Of, idealFactoredMag15Of, idealFactoredMag15Steps, Circuit.sequence,
    Circuit.eval_seq, Circuit.eval_onRegister, Submonoid.coe_mul, Matrix.mul_assoc]

theorem prepMag30Of_eval_eq (c15 : Circuit 4) :
    (prepMag30Of c15).eval = idealMag30Of c15.eval := by
  ext i j
  simp [prepMag30Of, idealMag30Of, Circuit.eval_seq, Circuit.eval_onRegister]

/-- Exact column-`0` `(0, 0)` norm-squared `(u + v * √2) / 2 ^ k` of a verified `GateTrace`. -/
theorem traceCircuit_normSq_zero_zero (tr : CliffordT.GateTrace) (m : CliffordT.CyclotomicMat2)
    (u v : ℤ) (hm : tr.checkFrom .one = some m) (ha_norm : m.a.mul m.a.conj = ⟨u, v, 0, -v⟩) :
    Complex.normSq (tr.toCircuit.eval.1 0 0) = ((u : ℝ) + (v : ℝ) * √2) / (2 : ℝ) ^ m.k := by
  rw [CliffordT.GateTrace.eval_toCircuit_of_checkFrom tr m hm]
  have hm00 : m.toMatrix 0 0 = (((√2 : ℝ)⁻¹ ^ m.k : ℝ) : ℂ) * m.a.toComplex := by
    simp [CliffordT.CyclotomicMat2.toMatrix]
  rw [hm00, map_mul, Complex.normSq_ofReal, normSq_toComplex_of_mul_conj ha_norm, ← sq,
    ← pow_mul, mul_comm m.k 2, pow_mul, inv_pow, Real.sq_sqrt (by positivity), inv_pow]
  ring

private lemma unitary2_normSq_one_zero (U : Unitary 2) :
    Complex.normSq (U.1 1 0) = 1 - Complex.normSq (U.1 0 0) := by
  have hunit : (U.1ᴴ * U.1) 0 0 = 1 := by
    have h1 : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
    rw [h1]; rfl
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    RCLike.star_def, mul_comm (starRingEnd ℂ _) _, Complex.mul_conj] at hunit
  have hre := congrArg Complex.re hunit
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at hre
  linarith

private lemma singleton_replaceIndex_eq_loc {n : ℕ} (w : Wire n) (k k' : Fin (2 ^ n)) (b : Fin 2)
    (h : ∀ q : Wire n, basisBits n k' q = if q = w then basisBits 1 b 0 else basisBits n k q) :
    (QRegister.singleton w).replaceIndex k b = k' := by
  apply (basisBits n).injective; funext q
  rw [h q]
  by_cases hqw : q = w
  · subst hqw; simpa using (QRegister.singleton q).basisBits_replaceIndex_apply k b 0
  · rw [ite_eq_right hqw]
    exact (QRegister.singleton w).basisBits_replaceIndex_of_not_mem k b q
      (by rintro ⟨_, hi⟩; exact hqw hi.symm)

private lemma singleton_embedUnitary_mulVec_of_zero_loc {n : ℕ} (w : Wire n)
    (U : Unitary 2) (k k1 : Fin (2 ^ n))
    (hex : (QRegister.singleton w).extractIndex k = 0)
    (h1 : ∀ q : Wire n, basisBits n k1 q =
      if q = w then basisBits 1 (1 : Fin 2) 0 else basisBits n k q) :
    ((QRegister.singleton w).embedUnitary U).1 *ᵥ (Pi.single k 1) =
      U.1 0 0 • Pi.single k 1 + U.1 1 0 • Pi.single k1 1 := by
  let r := QRegister.singleton w
  have hr0 : r.replaceIndex k 0 = k := by rw [← hex, r.replaceIndex_extractIndex]
  have hr1 : r.replaceIndex k 1 = k1 := singleton_replaceIndex_eq_loc w k k1 1 h1
  have hm2 (A : Matrix (Fin 2) (Fin 2) ℂ) :
      A *ᵥ (Pi.single (0 : Fin 2) 1) = A 0 0 • Pi.single 0 1 + A 1 0 • Pi.single 1 1 := by
    funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors, hex, hm2,
    r.tensorState_add_left, r.tensorState_smul_left, r.tensorState_smul_left,
    r.tensorState_single_replaceIndex, r.tensorState_single_replaceIndex, hr0, hr1]

private lemma idealFactoredMag15Of_mulVec_zero_apply (U5 U3 : Unitary 2) (y : Fin (2 ^ 4)) :
    ((idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0) y =
      (U5.1 0 0 * U3.1 0 0) * postFactor15Circuit.eval.1 y 0 +
      (U5.1 1 0 * U3.1 0 0) * postFactor15Circuit.eval.1 y 4 +
      (U5.1 0 0 * U3.1 1 0) * postFactor15Circuit.eval.1 y 8 +
      (U5.1 1 0 * U3.1 1 0) * postFactor15Circuit.eval.1 y 12 := by
  have hcons {d : ℕ} (u : Unitary d) (us : List (Unitary d)) (v : Fin d → ℂ) :
      (u :: us).reverse.prod.1 *ᵥ v = us.reverse.prod.1 *ᵥ (u.1 *ᵥ v) := by
    rw [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  have hvec : (idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0 =
      (U5.1 0 0 * U3.1 0 0) • (postFactor15Circuit.eval.1 *ᵥ Pi.single 0 1) +
      (U5.1 1 0 * U3.1 0 0) • (postFactor15Circuit.eval.1 *ᵥ Pi.single 4 1) +
      (U5.1 0 0 * U3.1 1 0) • (postFactor15Circuit.eval.1 *ᵥ Pi.single 8 1) +
      (U5.1 1 0 * U3.1 1 0) • (postFactor15Circuit.eval.1 *ᵥ Pi.single 12 1) := by
    rw [idealFactoredMag15Of, idealFactoredMag15Steps, basisState, hcons]
    conv_lhs =>
      enter [2]
      rw [singleton_embedUnitary_mulVec_of_zero_loc 2 U5 0 4 (by decide) (by decide)]
    rw [hcons]
    conv_lhs =>
      enter [2]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        singleton_embedUnitary_mulVec_of_zero_loc 3 U3 0 8 (by decide) (by decide),
        singleton_embedUnitary_mulVec_of_zero_loc 3 U3 4 12 (by decide) (by decide)]
    rw [hcons]
    simp only [List.reverse_nil, List.prod_nil, OneMemClass.coe_one, Matrix.one_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
    abel
  rw [hvec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply]

private lemma orth_two_of_normSq_eq {u v : ℂ}
    (h1 : Complex.normSq (u + v) = Complex.normSq (u - v))
    (hi : Complex.normSq (u + Complex.I * v) = Complex.normSq (u - Complex.I * v)) :
    u = 0 ∨ v = 0 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, zero_add] at h1 hi
  have hr : u.re * v.re + u.im * v.im = 0 := by linear_combination h1 / 4
  have him : u.im * v.re - u.re * v.im = 0 := by linear_combination hi / 4
  have hprod : (u.re * u.re + u.im * u.im) * (v.re * v.re + v.im * v.im) = 0 := by
    calc (u.re * u.re + u.im * u.im) * (v.re * v.re + v.im * v.im)
        = (u.re * v.re + u.im * v.im) ^ 2 + (u.im * v.re - u.re * v.im) ^ 2 := by ring
      _ = 0 := by rw [hr, him]; ring
  rcases mul_eq_zero.mp hprod with hu | hv
  · exact Or.inl (Complex.normSq_eq_zero.mp hu)
  · exact Or.inr (Complex.normSq_eq_zero.mp hv)

private lemma orth_four_of_normSq_const {z0 z4 z8 z12 : ℂ} {C : ℝ}
    (h : ∀ ε5 ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ),
      ∀ ε3 ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ),
        Complex.normSq (z0 + ε5 * z4 + ε3 * (z8 + ε5 * z12)) = C) :
    (z4 = 0 ∧ z8 = 0 ∧ z12 = 0) ∨ (z0 = 0 ∧ z8 = 0 ∧ z12 = 0) ∨
      (z0 = 0 ∧ z4 = 0 ∧ z12 = 0) ∨ (z0 = 0 ∧ z4 = 0 ∧ z8 = 0) := by
  have hm1 : (1 : ℂ) ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ) := by simp
  have hmn1 : (-1 : ℂ) ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ) := by simp
  have hmi : Complex.I ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ) := by simp
  have hmni : -Complex.I ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ) := by simp
  have hpair (ε5 : ℂ) (hε5 : ε5 ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ)) :
      z0 + ε5 * z4 = 0 ∨ z8 + ε5 * z12 = 0 := by
    refine orth_two_of_normSq_eq ?_ ?_
    · have ha := h ε5 hε5 1 hm1; have hb := h ε5 hε5 (-1) hmn1
      simpa [sub_eq_add_neg] using ha.trans hb.symm
    · have ha := h ε5 hε5 Complex.I hmi; have hb := h ε5 hε5 (-Complex.I) hmni
      simpa [sub_eq_add_neg, neg_mul] using ha.trans hb.symm
  have h1i_ne : (1 - Complex.I : ℂ) ≠ 0 := by
    intro hc; have := congrArg Complex.im hc; norm_num at this
  have h1pi_ne : (1 + Complex.I : ℂ) ≠ 0 := by
    intro hc; have := congrArg Complex.im hc; norm_num at this
  have hleft_zero (hz : z0 = 0 ∧ z4 = 0) : z8 = 0 ∨ z12 = 0 := by
    rcases hz with ⟨rfl, rfl⟩
    refine orth_two_of_normSq_eq ?_ ?_
    · have ha := h 1 hm1 1 hm1; have hb := h (-1) hmn1 1 hm1
      simpa [sub_eq_add_neg] using ha.trans hb.symm
    · have ha := h Complex.I hmi 1 hm1; have hb := h (-Complex.I) hmni 1 hm1
      simpa [sub_eq_add_neg, neg_mul] using ha.trans hb.symm
  have hright_zero (hzz : z8 = 0 ∧ z12 = 0) : z0 = 0 ∨ z4 = 0 := by
    rcases hzz with ⟨rfl, rfl⟩
    refine orth_two_of_normSq_eq ?_ ?_
    · have ha := h 1 hm1 1 hm1; have hb := h (-1) hmn1 1 hm1
      simpa [sub_eq_add_neg] using ha.trans hb.symm
    · have ha := h Complex.I hmi 1 hm1; have hb := h (-Complex.I) hmni 1 hm1
      simpa [sub_eq_add_neg, neg_mul] using ha.trans hb.symm
  have hzz : (z0 = 0 ∧ z4 = 0) ∨ (z8 = 0 ∧ z12 = 0) := by
    rcases hpair 1 hm1 with p1 | p1 <;> rcases hpair (-1) hmn1 with pn1 | pn1 <;>
      rcases hpair Complex.I hmi with pi | pi
    · exact Or.inl ⟨by linear_combination (p1 + pn1) / 2, by linear_combination (p1 - pn1) / 2⟩
    · exact Or.inl ⟨by linear_combination (p1 + pn1) / 2, by linear_combination (p1 - pn1) / 2⟩
    · have hb : z4 = 0 := mul_eq_zero.mp (by linear_combination p1 - pi : (1 - Complex.I) * z4 = 0)
        |>.resolve_left h1i_ne
      exact Or.inl ⟨by linear_combination p1 - hb, hb⟩
    · have hb : z12 = 0 :=
        mul_eq_zero.mp (by linear_combination pn1 - pi : (-1 - Complex.I) * z12 = 0)
        |>.resolve_left (by intro hc; have := congrArg Complex.im hc; norm_num at this)
      exact Or.inr ⟨by linear_combination pi - Complex.I * hb, hb⟩
    · have hb : z4 = 0 :=
        mul_eq_zero.mp (by linear_combination pi - pn1 : (1 + Complex.I) * z4 = 0)
        |>.resolve_left h1pi_ne
      exact Or.inl ⟨by linear_combination pn1 + hb, hb⟩
    · have hb : z12 = 0 :=
        mul_eq_zero.mp (by linear_combination p1 - pi : (1 - Complex.I) * z12 = 0)
        |>.resolve_left h1i_ne
      exact Or.inr ⟨by linear_combination p1 - hb, hb⟩
    · exact Or.inr ⟨by linear_combination (p1 + pn1) / 2, by linear_combination (p1 - pn1) / 2⟩
    · exact Or.inr ⟨by linear_combination (p1 + pn1) / 2, by linear_combination (p1 - pn1) / 2⟩
  rcases hzz with hl | hr
  · rcases hleft_zero hl with h8 | h12
    · exact Or.inr (Or.inr (Or.inr ⟨hl.1, hl.2, h8⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hl.1, hl.2, h12⟩))
  · rcases hright_zero hr with h0 | h4
    · exact Or.inr (Or.inl ⟨h0, hr.1, hr.2⟩)
    · exact Or.inl ⟨h4, hr.1, hr.2⟩

private noncomputable def su2PhaseTestUnitary (ε : ℂ) (t : ℝ)
    (hε : Complex.normSq ε = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Unitary 2 :=
  ⟨CliffordT.su2Matrix (√t : ℂ) ((√(1 - t) : ℂ) * ε), by
    apply CliffordT.su2Matrix_mem_unitaryGroup
    rw [map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, hε, mul_one,
      ← sq, ← sq, Real.sq_sqrt ht0, Real.sq_sqrt (by linarith)]
    ring⟩

private lemma postFactor15_fifteen_entries_zero :
    postFactor15Circuit.eval.1 15 0 = 0 ∧ postFactor15Circuit.eval.1 15 4 = 0 ∧
      postFactor15Circuit.eval.1 15 8 = 0 ∧ postFactor15Circuit.eval.1 15 12 = 0 := by
  let P := postFactor15Circuit.eval.1
  let z0 := (√(4 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P 15 0
  let z4 := (√(1 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P 15 4
  let z8 := (√(4 / 5 : ℝ) : ℂ) * (√(1 / 3 : ℝ) : ℂ) * P 15 8
  let z12 := (√(1 / 5 : ℝ) : ℂ) * (√(1 / 3 : ℝ) : ℂ) * P 15 12
  have heq (ε5 ε3 : ℂ) (h5 : Complex.normSq ε5 = 1) (h3 : Complex.normSq ε3 = 1) :
      z0 + ε5 * z4 + ε3 * z8 + ε5 * ε3 * z12 = 0 := by
    let U5 := su2PhaseTestUnitary ε5 (4 / 5) h5 (by norm_num) (by norm_num)
    let U3 := su2PhaseTestUnitary ε3 (2 / 3) h3 (by norm_num) (by norm_num)
    have hns := normSq_idealFactoredMag15Of U5 U3
      (by change Complex.normSq (√(4 / 5 : ℝ) : ℂ) = 4 / 5
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)])
      (by rw [unitary2_normSq_one_zero]
          change 1 - Complex.normSq (√(4 / 5 : ℝ) : ℂ) = 1 / 5
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]; norm_num)
      (by change Complex.normSq (√(2 / 3 : ℝ) : ℂ) = 2 / 3
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)])
      (by rw [unitary2_normSq_one_zero]
          change 1 - Complex.normSq (√(2 / 3 : ℝ) : ℂ) = 1 / 3
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]; norm_num)
      15
    simp only [(by decide : ¬ ((15 : Fin 16).val < 15)), ↓reduceIte] at hns
    have hv := Complex.normSq_eq_zero.mp hns
    rw [idealFactoredMag15Of_mulVec_zero_apply] at hv
    change (√(4 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P 15 0 +
      ((√(1 - 4 / 5 : ℝ) : ℂ) * ε5 * (√(2 / 3 : ℝ) : ℂ)) * P 15 4 +
      ((√(4 / 5 : ℝ) : ℂ) * ((√(1 - 2 / 3 : ℝ) : ℂ) * ε3)) * P 15 8 +
      (((√(1 - 4 / 5 : ℝ) : ℂ) * ε5) * ((√(1 - 2 / 3 : ℝ) : ℂ) * ε3)) * P 15 12 = 0 at hv
    have hr5 : (1 - 4 / 5 : ℝ) = 1 / 5 := by norm_num
    have hr3 : (1 - 2 / 3 : ℝ) = 1 / 3 := by norm_num
    rw [hr5, hr3] at hv
    dsimp only [z0, z4, z8, z12]
    linear_combination hv
  have hpp := heq 1 1 (by simp) (by simp)
  have hmp := heq (-1) 1 (by simp) (by simp)
  have hpm := heq 1 (-1) (by simp) (by simp)
  have hmm := heq (-1) (-1) (by simp) (by simp)
  have hz0 : z0 = 0 := by linear_combination (hpp + hmp + hpm + hmm) / 4
  have hz4 : z4 = 0 := by linear_combination (hpp - hmp + hpm - hmm) / 4
  have hz8 : z8 = 0 := by linear_combination (hpp + hmp - hpm - hmm) / 4
  have hz12 : z12 = 0 := by linear_combination (hpp - hmp - hpm + hmm) / 4
  have hne (r : ℝ) (hr : 0 < r) : (√r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp hz0).resolve_left
      (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
  · exact (mul_eq_zero.mp hz4).resolve_left
      (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
  · exact (mul_eq_zero.mp hz8).resolve_left
      (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
  · exact (mul_eq_zero.mp hz12).resolve_left
      (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))

private lemma postFactor15_lt15_normSq_decomp (y : Fin (2 ^ 4)) (hy : y.val < 15) :
    let P := postFactor15Circuit.eval.1
    ((8 / 15 : ℝ) * Complex.normSq (P y 0) + (2 / 15 : ℝ) * Complex.normSq (P y 4) +
      (4 / 15 : ℝ) * Complex.normSq (P y 8) + (1 / 15 : ℝ) * Complex.normSq (P y 12) = 1 / 15) ∧
    (∀ c0 c4 c8 c12 : ℂ,
      Complex.normSq (c0 * P y 0 + c4 * P y 4 + c8 * P y 8 + c12 * P y 12) =
        Complex.normSq c0 * Complex.normSq (P y 0) +
        Complex.normSq c4 * Complex.normSq (P y 4) +
        Complex.normSq c8 * Complex.normSq (P y 8) +
        Complex.normSq c12 * Complex.normSq (P y 12)) := by
  intro P
  let z0 := (√(4 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P y 0
  let z4 := (√(1 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P y 4
  let z8 := (√(4 / 5 : ℝ) : ℂ) * (√(1 / 3 : ℝ) : ℂ) * P y 8
  let z12 := (√(1 / 5 : ℝ) : ℂ) * (√(1 / 3 : ℝ) : ℂ) * P y 12
  have hns_eps (ε5 ε3 : ℂ) (h5 : Complex.normSq ε5 = 1) (h3 : Complex.normSq ε3 = 1) :
      Complex.normSq (z0 + ε5 * z4 + ε3 * (z8 + ε5 * z12)) = 1 / 15 := by
    let U5 := su2PhaseTestUnitary ε5 (4 / 5) h5 (by norm_num) (by norm_num)
    let U3 := su2PhaseTestUnitary ε3 (2 / 3) h3 (by norm_num) (by norm_num)
    have hns := normSq_idealFactoredMag15Of U5 U3
      (by change Complex.normSq (√(4 / 5 : ℝ) : ℂ) = 4 / 5
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)])
      (by rw [unitary2_normSq_one_zero]
          change 1 - Complex.normSq (√(4 / 5 : ℝ) : ℂ) = 1 / 5
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]; norm_num)
      (by change Complex.normSq (√(2 / 3 : ℝ) : ℂ) = 2 / 3
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)])
      (by rw [unitary2_normSq_one_zero]
          change 1 - Complex.normSq (√(2 / 3 : ℝ) : ℂ) = 1 / 3
          rw [Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]; norm_num)
      y
    simp only [hy, ↓reduceIte, idealFactoredMag15Of_mulVec_zero_apply] at hns
    change Complex.normSq ((√(4 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P y 0 +
      ((√(1 - 4 / 5 : ℝ) : ℂ) * ε5 * (√(2 / 3 : ℝ) : ℂ)) * P y 4 +
      ((√(4 / 5 : ℝ) : ℂ) * ((√(1 - 2 / 3 : ℝ) : ℂ) * ε3)) * P y 8 +
      (((√(1 - 4 / 5 : ℝ) : ℂ) * ε5) * ((√(1 - 2 / 3 : ℝ) : ℂ) * ε3)) * P y 12) = 1 / 15 at hns
    have hr5 : (1 - 4 / 5 : ℝ) = 1 / 5 := by norm_num
    have hr3 : (1 - 2 / 3 : ℝ) = 1 / 3 := by norm_num
    rw [hr5, hr3] at hns
    have hring : z0 + ε5 * z4 + ε3 * (z8 + ε5 * z12) =
        (√(4 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ) * P y 0 +
        ((√(1 / 5 : ℝ) : ℂ) * ε5 * (√(2 / 3 : ℝ) : ℂ)) * P y 4 +
        ((√(4 / 5 : ℝ) : ℂ) * ((√(1 / 3 : ℝ) : ℂ) * ε3)) * P y 8 +
        (((√(1 / 5 : ℝ) : ℂ) * ε5) * ((√(1 / 3 : ℝ) : ℂ) * ε3)) * P y 12 := by
      dsimp only [z0, z4, z8, z12]; ring
    rwa [hring]
  have hmem_ns {ε : ℂ} (hε : ε ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ)) :
      Complex.normSq ε = 1 := by
    rcases hε with rfl | rfl | rfl | rfl <;> simp [Complex.normSq_I]
  have horth := orth_four_of_normSq_const
    (fun ε5 h5 ε3 h3 ↦ hns_eps ε5 ε3 (hmem_ns h5) (hmem_ns h3))
  have hne (r : ℝ) (hr : 0 < r) : (√r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr))
  have hP_orth :
      (P y 4 = 0 ∧ P y 8 = 0 ∧ P y 12 = 0) ∨ (P y 0 = 0 ∧ P y 8 = 0 ∧ P y 12 = 0) ∨
        (P y 0 = 0 ∧ P y 4 = 0 ∧ P y 12 = 0) ∨ (P y 0 = 0 ∧ P y 4 = 0 ∧ P y 8 = 0) := by
    have k0 : z0 = 0 → P y 0 = 0 := fun h ↦
      (mul_eq_zero.mp h).resolve_left (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
    have k4 : z4 = 0 → P y 4 = 0 := fun h ↦
      (mul_eq_zero.mp h).resolve_left (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
    have k8 : z8 = 0 → P y 8 = 0 := fun h ↦
      (mul_eq_zero.mp h).resolve_left (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
    have k12 : z12 = 0 → P y 12 = 0 := fun h ↦
      (mul_eq_zero.mp h).resolve_left (mul_ne_zero (hne _ (by norm_num)) (hne _ (by norm_num)))
    rcases horth with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨k4 a, k8 b, k12 c⟩
    · exact Or.inr (Or.inl ⟨k0 a, k8 b, k12 c⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k0 a, k4 b, k12 c⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k0 a, k4 b, k8 c⟩))
  have hlin (c0 c4 c8 c12 : ℂ) :
      Complex.normSq (c0 * P y 0 + c4 * P y 4 + c8 * P y 8 + c12 * P y 12) =
        Complex.normSq c0 * Complex.normSq (P y 0) +
        Complex.normSq c4 * Complex.normSq (P y 4) +
        Complex.normSq c8 * Complex.normSq (P y 8) +
        Complex.normSq c12 * Complex.normSq (P y 12) := by
    rcases hP_orth with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      simp [h1, h2, h3, map_mul]
  refine ⟨?_, hlin⟩
  have h11 := hns_eps 1 1 (by simp) (by simp)
  have hrew : z0 + 1 * z4 + 1 * (z8 + 1 * z12) =
      ((√(4 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ)) * P y 0 +
      ((√(1 / 5 : ℝ) : ℂ) * (√(2 / 3 : ℝ) : ℂ)) * P y 4 +
      ((√(4 / 5 : ℝ) : ℂ) * (√(1 / 3 : ℝ) : ℂ)) * P y 8 +
      ((√(1 / 5 : ℝ) : ℂ) * (√(1 / 3 : ℝ) : ℂ)) * P y 12 := by
    dsimp only [z0, z4, z8, z12]; ring
  rw [hrew, hlin] at h11
  have hns_r (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Complex.normSq ((√a : ℂ) * (√b : ℂ)) = a * b := by
    rw [map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, ← sq, ← sq,
      Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [hns_r _ _ (by norm_num) (by norm_num), hns_r _ _ (by norm_num) (by norm_num),
    hns_r _ _ (by norm_num) (by norm_num), hns_r _ _ (by norm_num) (by norm_num)] at h11
  linarith

private lemma postFactor15_sum_lt15_normSq {j : Fin (2 ^ 4)}
    (h15 : postFactor15Circuit.eval.1 15 j = 0) :
    (∑ y : Fin 15, Complex.normSq (postFactor15Circuit.eval.1 ⟨y.val, by omega⟩ j)) = 1 := by
  let U := postFactor15Circuit.eval
  have hunit : (U.1ᴴ * U.1) j j = 1 := by
    have h1 : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
    rw [h1]; exact Matrix.one_apply_eq j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    mul_comm (starRingEnd ℂ _) _, Complex.mul_conj] at hunit
  have hre := congrArg Complex.re hunit
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.one_re] at hre
  let emb15 : Fin 15 → Fin (2 ^ 4) := fun y ↦ ⟨y.val, by omega⟩
  have hsub : (∑ y : Fin 15, Complex.normSq (U.1 (emb15 y) j)) =
      ∑ y : Fin (2 ^ 4), Complex.normSq (U.1 y j) := by
    rw [← Finset.sum_subset (s₁ := Finset.univ.image emb15) (Finset.subset_univ _)]
    · exact (Finset.sum_bij (fun y (_ : y ∈ Finset.univ) ↦ emb15 y)
        (fun y _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _))
        (fun y₁ _ y₂ _ h ↦ Fin.ext (congrArg (Fin.val : Fin (2 ^ 4) → ℕ) h))
        (fun z hz ↦ let ⟨y, _, hy⟩ := Finset.mem_image.mp hz; ⟨y, Finset.mem_univ _, hy⟩)
        (fun _ _ ↦ rfl))
    · intro z _ hz
      have hz15 : z = 15 := by
        by_contra hne
        have hlt : z.val < 15 := by
          have := z.isLt; have : z.val ≠ 15 := fun hv ↦ hne (Fin.ext hv); omega
        exact hz (Finset.mem_image.mpr ⟨⟨z.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [hz15, show U.1 15 j = 0 from h15, map_zero]
  exact hsub.trans hre

theorem idealFactoredMag15Of_fifteen_zero (U5 U3 : Unitary 2) :
    ((idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0) 15 = 0 := by
  obtain ⟨h0, h4, h8, h12⟩ := postFactor15_fifteen_entries_zero
  rw [idealFactoredMag15Of_mulVec_zero_apply, h0, h4, h8, h12]
  simp

theorem idealFactoredMag15Of_l1_le (U5 U3 : Unitary 2) :
    let p5 := Complex.normSq (U5.1 0 0)
    let p3 := Complex.normSq (U3.1 0 0)
    (∑ y : Fin 15,
      |Complex.normSq (((idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0) ⟨y.val, by omega⟩) -
        1 / 15|) ≤
      |p5 * p3 - 8 / 15| + |(1 - p5) * p3 - 2 / 15| +
        |p5 * (1 - p3) - 4 / 15| + |(1 - p5) * (1 - p3) - 1 / 15| := by
  intro p5 p3
  let P := postFactor15Circuit.eval.1
  let e0 := |p5 * p3 - 8 / 15|
  let e4 := |(1 - p5) * p3 - 2 / 15|
  let e8 := |p5 * (1 - p3) - 4 / 15|
  let e12 := |(1 - p5) * (1 - p3) - 1 / 15|
  have hterm (y : Fin 15) :
      |Complex.normSq (((idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0) ⟨y.val, by omega⟩) -
        1 / 15| ≤
      e0 * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
      e4 * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
      e8 * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
      e12 * Complex.normSq (P ⟨y.val, by omega⟩ 12) := by
    obtain ⟨h15_eq, hlin⟩ := postFactor15_lt15_normSq_decomp ⟨y.val, by omega⟩ y.isLt
    rw [idealFactoredMag15Of_mulVec_zero_apply, hlin, ← h15_eq,
      map_mul, map_mul, map_mul, map_mul, unitary2_normSq_one_zero U5, unitary2_normSq_one_zero U3]
    change |(p5 * p3) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
        ((1 - p5) * p3) * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
        (p5 * (1 - p3)) * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
        ((1 - p5) * (1 - p3)) * Complex.normSq (P ⟨y.val, by omega⟩ 12) -
      ((8 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
        (2 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
        (4 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
        (1 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 12))| ≤ _
    have hdiff :
        (p5 * p3) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
          ((1 - p5) * p3) * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
          (p5 * (1 - p3)) * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
          ((1 - p5) * (1 - p3)) * Complex.normSq (P ⟨y.val, by omega⟩ 12) -
        ((8 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
          (2 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
          (4 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
          (1 / 15 : ℝ) * Complex.normSq (P ⟨y.val, by omega⟩ 12)) =
        (p5 * p3 - 8 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
          ((1 - p5) * p3 - 2 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
          (p5 * (1 - p3) - 4 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
          ((1 - p5) * (1 - p3) - 1 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 12) := by ring
    rw [hdiff]
    have ha1 := abs_add_le
      ((p5 * p3 - 8 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
        ((1 - p5) * p3 - 2 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
        (p5 * (1 - p3) - 4 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 8))
      (((1 - p5) * (1 - p3) - 1 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 12))
    have ha2 := abs_add_le
      ((p5 * p3 - 8 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
        ((1 - p5) * p3 - 2 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 4))
      ((p5 * (1 - p3) - 4 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 8))
    have ha3 := abs_add_le
      ((p5 * p3 - 8 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 0))
      (((1 - p5) * p3 - 2 / 15) * Complex.normSq (P ⟨y.val, by omega⟩ 4))
    simp only [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)] at ha1 ha2 ha3
    dsimp only [e0, e4, e8, e12]
    linarith
  obtain ⟨h15_0, h15_4, h15_8, h15_12⟩ := postFactor15_fifteen_entries_zero
  calc (∑ y : Fin 15,
        |Complex.normSq (((idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0) ⟨y.val, by omega⟩) -
          1 / 15|)
      ≤ ∑ y : Fin 15, (e0 * Complex.normSq (P ⟨y.val, by omega⟩ 0) +
          e4 * Complex.normSq (P ⟨y.val, by omega⟩ 4) +
          e8 * Complex.normSq (P ⟨y.val, by omega⟩ 8) +
          e12 * Complex.normSq (P ⟨y.val, by omega⟩ 12)) :=
        Finset.sum_le_sum fun y _ ↦ hterm y
    _ = e0 * (∑ y : Fin 15, Complex.normSq (P ⟨y.val, by omega⟩ 0)) +
          e4 * (∑ y : Fin 15, Complex.normSq (P ⟨y.val, by omega⟩ 4)) +
          e8 * (∑ y : Fin 15, Complex.normSq (P ⟨y.val, by omega⟩ 8)) +
          e12 * (∑ y : Fin 15, Complex.normSq (P ⟨y.val, by omega⟩ 12)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = e0 + e4 + e8 + e12 := by
        rw [postFactor15_sum_lt15_normSq h15_0, postFactor15_sum_lt15_normSq h15_4,
          postFactor15_sum_lt15_normSq h15_8, postFactor15_sum_lt15_normSq h15_12]
        ring

private lemma idealMag30Of_mulVec_zero_apply (U15 : Unitary (2 ^ 4)) (x : Fin (2 ^ 5)) :
    ((idealMag30Of U15).1 *ᵥ basisState 0) x =
      ((U15.1 *ᵥ basisState 0) ⟨x.val / 2, by omega⟩) * (√2 : ℂ)⁻¹ := by
  let r4 : QRegister 4 5 := QRegister.block 1 4 (by decide)
  have hH : (Circuit.H (0 : Wire 5)).eval.1 *ᵥ basisState 0 =
      r4.tensorState (basisState 0) (fun _ ↦ (√2 : ℂ)⁻¹) := by
    have hh : (Circuit.H (0 : Wire 5)).eval.1 *ᵥ (Pi.single 0 1) =
        (√2 : ℂ)⁻¹ • (Pi.single 0 1 + Pi.single 1 1) := by
      change ((QRegister.singleton (0 : Wire 5)).embedUnitary Qubit.H).1 *ᵥ (Pi.single 0 1) = _
      have h00 : Qubit.H.1 0 0 = (√2 : ℂ)⁻¹ := by simp [Qubit.H, Complex.real_smul]
      have h10 : Qubit.H.1 1 0 = (√2 : ℂ)⁻¹ := by simp [Qubit.H, Complex.real_smul]
      rw [singleton_embedUnitary_mulVec_of_zero_loc 0 Qubit.H 0 1 (by decide) (by decide),
        h00, h10, ← smul_add]
    rw [show (basisState 0 : Fin (2 ^ 5) → ℂ) = Pi.single 0 1 from rfl, hh]
    funext g
    have hex0 : r4.extractIndex g = 0 ↔ g = 0 ∨ g = 1 := by fin_cases g <;> decide
    simp only [QRegister.tensorState, basisState, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    by_cases hg : g = 0 ∨ g = 1
    · rw [ite_eq_left (hex0.mpr hg)]
      rcases hg with rfl | rfl <;> simp
    · rw [ite_eq_right (mt hex0.mp hg)]
      rw [not_or] at hg
      simp [hg.1, hg.2]
  have hmul : (idealMag30Of U15).1 *ᵥ basisState 0 =
      r4.tensorState (U15.1 *ᵥ basisState 0) (fun _ ↦ (√2 : ℂ)⁻¹) := by
    rw [idealMag30Of, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hH, QRegister.embedUnitary_val,
      r4.embedMatrix_mulVec_tensorState]
  have hex : r4.extractIndex x = ⟨x.val / 2, by omega⟩ := by fin_cases x <;> decide
  rw [hmul, QRegister.tensorState, hex]

theorem factoredMag30Of_mulVec_zero_eq_zero_of_ge (c5 c3 : Circuit 1)
    (x : Fin (2 ^ 5)) (hx : 30 ≤ x.val) :
    ((factoredMag30Of c5 c3).eval.1 *ᵥ basisState 0) x = 0 := by
  rw [factoredMag30Of, prepMag30Of_eval_eq, factoredMag15Of_eval_eq,
    idealMag30Of_mulVec_zero_apply]
  have h15 : (⟨x.val / 2, by omega⟩ : Fin (2 ^ 4)) = 15 :=
    Fin.ext (by have := x.isLt; change x.val / 2 = 15; omega)
  rw [h15, idealFactoredMag15Of_fifteen_zero, zero_mul]

theorem factoredMag30Of_l1_le (c5 c3 : Circuit 1) :
    let p5 := Complex.normSq (c5.eval.1 0 0)
    let p3 := Complex.normSq (c3.eval.1 0 0)
    (∑ x : Fin 30,
      |Complex.normSq (((factoredMag30Of c5 c3).eval.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) -
        1 / 30|) ≤
      |p5 * p3 - 8 / 15| + |(1 - p5) * p3 - 2 / 15| +
        |p5 * (1 - p3) - 4 / 15| + |(1 - p5) * (1 - p3) - 1 / 15| := by
  intro p5 p3
  let U15 := idealFactoredMag15Of c5.eval c3.eval
  have hns_inv2 : Complex.normSq ((√2 : ℂ)⁻¹) = 1 / 2 := by
    rw [map_inv₀, Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]; norm_num
  have hpt (x : Fin 30) :
      |Complex.normSq (((factoredMag30Of c5 c3).eval.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) -
        1 / 30| =
      |Complex.normSq ((U15.1 *ᵥ basisState 0) ⟨x.val / 2, by omega⟩) - 1 / 15| / 2 := by
    rw [factoredMag30Of, prepMag30Of_eval_eq, factoredMag15Of_eval_eq,
      idealMag30Of_mulVec_zero_apply, map_mul, hns_inv2]
    have hdiv : Complex.normSq ((U15.1 *ᵥ basisState 0) ⟨x.val / 2, by omega⟩) * (1 / 2) - 1 / 30 =
        (Complex.normSq ((U15.1 *ᵥ basisState 0) ⟨x.val / 2, by omega⟩) - 1 / 15) / 2 := by ring
    rw [hdiv, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp_rw [hpt]
  let eqv : Fin 15 × Fin 2 ≃ Fin 30 :=
    { toFun := fun yb ↦ ⟨2 * yb.1.val + yb.2.val, by omega⟩
      invFun := fun x ↦ (⟨x.val / 2, by omega⟩, ⟨x.val % 2, by omega⟩)
      left_inv := fun ⟨y, b⟩ ↦ Prod.ext (Fin.ext (by dsimp only; omega))
        (Fin.ext (by dsimp only; omega))
      right_inv := fun x ↦ Fin.ext (by dsimp only; omega) }
  have hpair :
      (∑ x : Fin 30,
        |Complex.normSq ((U15.1 *ᵥ basisState 0) ⟨x.val / 2, by omega⟩) - 1 / 15| / 2) =
      ∑ y : Fin 15, |Complex.normSq ((U15.1 *ᵥ basisState 0) ⟨y.val, by omega⟩) - 1 / 15| := by
    rw [← Equiv.sum_comp eqv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Fin.sum_univ_two]
    have he0 : (⟨(eqv (y, 0)).val / 2, by omega⟩ : Fin (2 ^ 4)) = ⟨y.val, by omega⟩ :=
      Fin.ext (by change (2 * y.val + 0) / 2 = y.val; omega)
    have he1 : (⟨(eqv (y, 1)).val / 2, by omega⟩ : Fin (2 ^ 4)) = ⟨y.val, by omega⟩ :=
      Fin.ext (by change (2 * y.val + 1) / 2 = y.val; omega)
    rw [he0, he1]; ring
  rw [hpair]
  exact idealFactoredMag15Of_l1_le c5.eval c3.eval

theorem factored15_l1_of_linear_bounds {p5 p3 η5 η3 b1 b2 b3 b4 ε : ℝ}
    (h5 : |p5 - 4 / 5| ≤ η5) (h3 : |p3 - 2 / 3| ≤ η3)
    (hl1 : |(2 / 3) * (p5 - 4 / 5) + (4 / 5) * (p3 - 2 / 3)| ≤ b1)
    (hl2 : |-(2 / 3) * (p5 - 4 / 5) + (1 / 5) * (p3 - 2 / 3)| ≤ b2)
    (hl3 : |(1 / 3) * (p5 - 4 / 5) - (4 / 5) * (p3 - 2 / 3)| ≤ b3)
    (hl4 : |-(1 / 3) * (p5 - 4 / 5) - (1 / 5) * (p3 - 2 / 3)| ≤ b4)
    (htot : b1 + b2 + b3 + b4 + 4 * η5 * η3 ≤ ε) :
    |p5 * p3 - 8 / 15| + |(1 - p5) * p3 - 2 / 15| +
      |p5 * (1 - p3) - 4 / 15| + |(1 - p5) * (1 - p3) - 1 / 15| ≤ ε := by
  let d5 := p5 - 4 / 5
  let d3 := p3 - 2 / 3
  have hprod : |d5 * d3| ≤ η5 * η3 := by
    rw [abs_mul]; exact mul_le_mul h5 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h5)
  have e1 : |p5 * p3 - 8 / 15| ≤ b1 + η5 * η3 := by
    have hr : p5 * p3 - 8 / 15 = ((2 / 3) * d5 + (4 / 5) * d3) + d5 * d3 := by
      dsimp only [d5, d3]; ring
    rw [hr]; linarith [abs_add_le ((2 / 3) * d5 + (4 / 5) * d3) (d5 * d3)]
  have e2 : |(1 - p5) * p3 - 2 / 15| ≤ b2 + η5 * η3 := by
    have hr : (1 - p5) * p3 - 2 / 15 = (-(2 / 3) * d5 + (1 / 5) * d3) + -(d5 * d3) := by
      dsimp only [d5, d3]; ring
    rw [hr]; linarith [abs_add_le (-(2 / 3) * d5 + (1 / 5) * d3) (-(d5 * d3)), abs_neg (d5 * d3)]
  have e3 : |p5 * (1 - p3) - 4 / 15| ≤ b3 + η5 * η3 := by
    have hr : p5 * (1 - p3) - 4 / 15 = ((1 / 3) * d5 - (4 / 5) * d3) + -(d5 * d3) := by
      dsimp only [d5, d3]; ring
    rw [hr]; linarith [abs_add_le ((1 / 3) * d5 - (4 / 5) * d3) (-(d5 * d3)), abs_neg (d5 * d3)]
  have e4 : |(1 - p5) * (1 - p3) - 1 / 15| ≤ b4 + η5 * η3 := by
    have hr : (1 - p5) * (1 - p3) - 1 / 15 = (-(1 / 3) * d5 - (1 / 5) * d3) + d5 * d3 := by
      dsimp only [d5, d3]; ring
    rw [hr]; linarith [abs_add_le (-(1 / 3) * d5 - (1 / 5) * d3) (d5 * d3)]
  linarith

/-! ## Section 2: Exact `SU(2)` `GateTrace` Words & `1`-Qubit Certificates -/

/-- Generic `L¹_30` instantiator from column-`0` `(u + v * √2) / 2 ^ k` formulas. -/
theorem factoredMag30Of_l1_of_ns (c5 c3 : Circuit 1) {p5 p3 η5 η3 b1 b2 b3 b4 ε : ℝ}
    (hp5 : Complex.normSq (c5.eval.1 0 0) = p5) (hp3 : Complex.normSq (c3.eval.1 0 0) = p3)
    (h5 : |p5 - 4 / 5| ≤ η5) (h3 : |p3 - 2 / 3| ≤ η3)
    (hl1 : |(2 / 3) * (p5 - 4 / 5) + (4 / 5) * (p3 - 2 / 3)| ≤ b1)
    (hl2 : |-(2 / 3) * (p5 - 4 / 5) + (1 / 5) * (p3 - 2 / 3)| ≤ b2)
    (hl3 : |(1 / 3) * (p5 - 4 / 5) - (4 / 5) * (p3 - 2 / 3)| ≤ b3)
    (hl4 : |-(1 / 3) * (p5 - 4 / 5) - (1 / 5) * (p3 - 2 / 3)| ≤ b4)
    (htot : b1 + b2 + b3 + b4 + 4 * η5 * η3 ≤ ε) :
    (∑ x : Fin 30,
      |Complex.normSq (((factoredMag30Of c5 c3).eval.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) -
        1 / 30|) ≤ ε := by
  refine (factoredMag30Of_l1_le c5 c3).trans ?_
  rw [hp5, hp3]
  exact factored15_l1_of_linear_bounds h5 h3 hl1 hl2 hl3 hl4 htot

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30

/-!
# Quantized `SU(2)` Factored `L = 30` Splitters, Markov-Kernel `L¹`, & `δIdx = 0` Walk Closures

Completes all 5 exact `SU(2)` `GateTrace` `5`-qubit quantized `factoredMag30` operating points
(`Quant86`, `Quant78`, `Quant72`, `Quant66`, `Quant56`; `86 / 78 / 72 / 66 / 56 T`, `0` scratch,
`0 TOFF`), establishes the slice-agnostic Markov-kernel `L¹` contraction for
`zeroCmpQuantInnerProb sliceFn uIdx`, proves direct `BlockEncodingCore` operator-norm and
`AgreesOnElectronSector 58 63` bounds for `quantInnerP450HBlocked` and `quantJointP450HBlocked`
(`c_shift = 0`, `eLB_q = dfthcLowerBound`, `lam_q = 97.3864`), and closes `PulledSOSBlockEncoding`
and `PerturbedRefl2Cert` with `uIdxIdeal := uIdx` (`δIdx = 0`, `δStep = 2 * δOut + δ1 + δ2`) plus
quantized inner cores (`3,012 / 2,980 / 2,956 / 2,932 / 2,892 + sel1 + sel2` `T`).

## References
- N. J. Ross and P. Selinger, *Quantum Inf. Comput.* **16**, 901–953 (2016), arXiv:1403.2975.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CoherentAlias
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptFactoredMag30AndCoin9
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162StepSympAnfQrom21
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastUniform
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepZeroCmp20
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepWalk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactZeroCmp20OuterParam
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepZeroCmp20OuterParam
open scoped Matrix BigOperators Circuit.Notation Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowQMag30 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Lower-`T` `SU(2)` `GateTrace` Words & All 5 `5`-Qubit Splitters -/

/-! ## Section 2: Slice-Agnostic Quantized Inner Probabilities & Markov-Kernel `L¹` Contraction -/

/-- Exact `184`-item normalized outer DFTHC probability distribution (`∑ xo, qOut xo = 1`). -/
noncomputable def p450ExactOuterProb (xo : Fin 184) : ℝ :=
  (outerWeightNat xo : ℝ) / 188416

/-- Exact `30`-item normalized inner DFTHC probability distribution per fragment `rc : Fin 126`. -/
noncomputable def p450ExactInnerProb (rc : Fin 126) (b : Fin 30) : ℝ :=
  ((innerMantissaFlat rc b).natAbs : ℝ) / 15360

/-- Quantized spin-blocked fragment LCU `A^{blocked}_{rc}(pIn)` for fragment `(r, c)`. -/
noncomputable def quantBlockedFragmentLCU (pIn : Fin 126 → Fin 30 → ℝ)
    (r : Fin 9) (c : Fin 14) : Operator (2 ^ (2 * 58)) :=
  let rc : Fin 126 := ⟨14 * r.val + c.val, by omega⟩
  ((pIn rc 29 * (if negIn rc 29 then -1 else 1) : ℝ) : ℂ) • (1 : Operator (2 ^ (2 * 58))) -
    ∑ b : Fin 29, ∑ σ : Fin 2,
      (((pIn rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
        blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ

/-- Jointly quantized `(qOut, pIn)` spin-blocked P450 SOS Hamiltonian (`eLB = dfthcLowerBound`,
`lam = 97.3864`, `c_shift = 0`). -/
noncomputable def quantJointP450HBlocked (qOut : Fin 184 → ℝ) (pIn : Fin 126 → Fin 30 → ℝ) :
    Operator (2 ^ (2 * 58)) :=
  (dfthcLowerBound : ℂ) • (1 : Operator (2 ^ (2 * 58))) +
    ((2 * 97.3864 : ℝ) : ℂ) •
      ((∑ ℓ : Fin 58, ∑ σ : Fin 2,
          ((qOut (outerIndexEquiv (.inl ℓ)) / 2 : ℝ) : ℂ) •
            ((blockedOneBodyProjector ℓ σ)ᴴ * blockedOneBodyProjector ℓ σ)) +
       (∑ r : Fin 9, ∑ c : Fin 14,
          (qOut (outerIndexEquiv (.inr (r, c))) : ℂ) •
            ((quantBlockedFragmentLCU pIn r c)ᴴ * quantBlockedFragmentLCU pIn r c)))

/-- Inner-quantized spin-blocked P450 SOS Hamiltonian at exact outer `p450ExactOuterProb`. -/
noncomputable abbrev quantInnerP450HBlocked (pIn : Fin 126 → Fin 30 → ℝ) :
    Operator (2 ^ (2 * 58)) :=
  quantJointP450HBlocked p450ExactOuterProb pIn

@[simp] theorem quantBlockedFragmentLCU_conjTranspose (pIn : Fin 126 → Fin 30 → ℝ)
    (r : Fin 9) (c : Fin 14) :
    (quantBlockedFragmentLCU pIn r c)ᴴ = quantBlockedFragmentLCU pIn r c := by
  unfold quantBlockedFragmentLCU; dsimp only
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal, Matrix.conjTranspose_sum]
  refine congrArg (_ - ·) (Finset.sum_congr rfl fun b _ ↦ ?_)
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Matrix.conjTranspose_smul, blockedOrbitalReflection_conjTranspose,
    Complex.star_def, Complex.conj_ofReal]

@[simp] theorem quantJointP450HBlocked_conjTranspose (qOut : Fin 184 → ℝ)
    (pIn : Fin 126 → Fin 30 → ℝ) :
    (quantJointP450HBlocked qOut pIn)ᴴ = quantJointP450HBlocked qOut pIn := by
  unfold quantJointP450HBlocked
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_ofReal]

theorem p450ExactOuterProb_nonneg (xo : Fin 184) : 0 ≤ p450ExactOuterProb xo := by
  unfold p450ExactOuterProb; positivity

theorem p450ExactInnerProb_nonneg (rc : Fin 126) (b : Fin 30) : 0 ≤ p450ExactInnerProb rc b := by
  unfold p450ExactInnerProb; positivity

theorem sum_p450ExactInnerProb (rc : Fin 126) : (∑ b : Fin 30, p450ExactInnerProb rc b) = 1 := by
  unfold p450ExactInnerProb
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_innerMantissaFlat_natAbs]; norm_num

theorem quantBlockedFragmentLCU_exact (r : Fin 9) (c : Fin 14) :
    quantBlockedFragmentLCU p450ExactInnerProb r c = blockedFragmentLCU r c := by
  let rc : Fin 126 := ⟨14 * r.val + c.val, by omega⟩
  have hrc (b : Fin 30) : innerMantissaFlat rc b = innerMantissa r c b := by
    unfold innerMantissaFlat
    congr 1 <;> exact Fin.ext (by dsimp [rc]; omega)
  have hsc (b : Fin 30) :
      p450ExactInnerProb rc b * (if negIn rc b then -1 else 1) =
        (innerMantissa r c b : ℝ) / 15360 := by
    unfold p450ExactInnerProb
    rw [div_mul_eq_mul_div, innerMantissaFlat_natAbs_mul_sign, hrc]
  unfold quantBlockedFragmentLCU blockedFragmentLCU; dsimp only
  rw [smul_sub, smul_smul, Finset.smul_sum]
  refine congrArg₂ (· - ·) ?_ (Finset.sum_congr rfl fun b _ ↦ ?_)
  · refine congrArg (· • _) ?_
    have hc := congrArg Complex.ofReal (hsc 29); push_cast at hc ⊢; linear_combination hc
  · rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [smul_smul]; refine congrArg (· • _) ?_
    have hc := congrArg Complex.ofReal (hsc b.castSucc)
    push_cast at hc ⊢; linear_combination hc / 2

theorem quantJointP450HBlocked_exact :
    quantJointP450HBlocked p450ExactOuterProb p450ExactInnerProb =
      BlockEncodingCore.p450HBlocked := by
  have hsos := sub_eq_iff_eq_add'.mp p450HBlocked_sub_lowerBound_eq_sos
  rw [hsos]; unfold quantJointP450HBlocked
  rw [smul_add, Finset.smul_sum]
  refine congrArg (_ + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun ℓ _ ↦ ?_) ?_)
  · rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [smul_smul]; refine congrArg (· • _) ?_
    have h1 : (2 * 97.3864 : ℝ) * (p450ExactOuterProb (outerIndexEquiv (.inl ℓ)) / 2) =
        |P450.oneBodyEigenvalue ℓ| := by
      have heq : outerIndexEquiv (.inl ℓ) = ⟨ℓ.val, by omega⟩ := rfl
      rw [← outerWeightNat_lt_58_mul_unit ℓ, heq]
      unfold p450ExactOuterProb P450.coefficientUnit; ring
    have hc := congrArg Complex.ofReal h1; push_cast at hc ⊢; exact hc
  · rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [quantBlockedFragmentLCU_exact, smul_smul]; refine congrArg (· • _) ?_
    have hnot : ¬ (58 + 14 * r.val + c.val < 58) := by omega
    have hw : outerWeightNat (outerIndexEquiv (.inr (r, c))) = fragmentWeightNat r c := by
      change outerWeightNat ⟨58 + 14 * r.val + c.val, _⟩ = fragmentWeightNat r c
      simp only [outerWeightNat, hnot, ↓reduceDIte]
      congr 1 <;> exact Fin.ext (by dsimp; omega)
    have h2 : (2 * 97.3864 : ℝ) * p450ExactOuterProb (outerIndexEquiv (.inr (r, c))) =
        2 * (fragmentWeightNat r c : ℝ) * P450.coefficientUnit := by
      unfold p450ExactOuterProb P450.coefficientUnit; rw [hw]; ring
    have hc := congrArg Complex.ofReal h2; push_cast at hc ⊢; exact hc

private theorem fragmentWeights_toList_sum_eq_144553 :
    (DataArrays.fragmentWeightsArr.toList.map fun row ↦ row.toList.sum).sum = 144553 := by
  decide +kernel

theorem sum_fragmentWeightNat_eq_144553 :
    (∑ r : Fin 9, ∑ c : Fin 14, fragmentWeightNat r c) = 144553 := by
  obtain ⟨_, _, _, _, hfw, hfw_rows, _⟩ := table_shapes_and_bounds
  unfold fragmentWeightNat
  have hrow (r : Fin 9) :
      (∑ c : Fin 14, (DataArrays.fragmentWeightsArr.getD r.val #[]).getD c.val 0) =
        (DataArrays.fragmentWeightsArr.getD r.val #[]).toList.sum := by
    have hr : r.val < DataArrays.fragmentWeightsArr.size := by omega
    have hrs := hfw_rows _ (array_getD_mem_toList DataArrays.fragmentWeightsArr #[] r.val hr)
    simpa only [id_eq, List.map_id] using array_fin_sum_eq_toList_map_sum _ 0 id hrs
  simp only [hrow]
  exact (array_fin_sum_eq_toList_map_sum DataArrays.fragmentWeightsArr #[]
    (fun row ↦ row.toList.sum) hfw).trans fragmentWeights_toList_sum_eq_144553

section NormAndSectorBounds

open scoped Matrix.Norms.L2Operator

private theorem norm_blockedOrbitalReflection_le_one {u : Fin 58 → ℝ}
    (hu : ∑ p, u p ^ 2 = 1) (σ : Fin 2) : ‖blockedOrbitalReflection u σ‖ ≤ 1 :=
  QubitisedWalk.unitary_opNorm_le_one ⟨blockedOrbitalReflection u σ, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      blockedOrbitalReflection_conjTranspose, blockedOrbitalReflection_mul_self hu]⟩

theorem norm_quantBlockedFragmentLCU_le_one {pIn : Fin 126 → Fin 30 → ℝ}
    (r : Fin 9) (c : Fin 14)
    (hp0 : ∀ b : Fin 30, 0 ≤ pIn ⟨14 * r.val + c.val, by omega⟩ b)
    (hp1 : (∑ b : Fin 30, pIn ⟨14 * r.val + c.val, by omega⟩ b) = 1) :
    ‖quantBlockedFragmentLCU pIn r c‖ ≤ 1 := by
  let rc : Fin 126 := ⟨14 * r.val + c.val, by omega⟩
  have hsgn (b : Fin 30) : |if negIn rc b then (-1 : ℝ) else 1| = 1 := by split_ifs <;> norm_num
  unfold quantBlockedFragmentLCU; dsimp only
  have hI : ‖((pIn rc 29 * (if negIn rc 29 then -1 else 1) : ℝ) : ℂ) •
      (1 : Operator (2 ^ (2 * 58)))‖ ≤ pIn rc 29 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hsgn 29, mul_one,
      abs_of_nonneg (hp0 29)]
    exact mul_le_of_le_one_right (hp0 29) (QubitisedWalk.unitary_opNorm_le_one 1)
  have hS : ‖∑ b : Fin 29, ∑ σ : Fin 2,
      (((pIn rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
        blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ‖ ≤
      ∑ b : Fin 29, pIn rc b.castSucc := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ ↦ ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_two]
    have hterm (σ : Fin 2) :
        ‖(((pIn rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
          blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ‖ ≤
          pIn rc b.castSucc / 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, hsgn b.castSucc,
        mul_one, abs_of_nonneg (hp0 b.castSucc), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_of_le_one_right (div_nonneg (hp0 b.castSucc) (by norm_num))
        (norm_blockedOrbitalReflection_le_one (givensLeaf_sum_sq 15 _) σ)
    linarith [hterm 0, hterm 1]
  have htot : (∑ b : Fin 29, pIn rc b.castSucc) + pIn rc 29 = 1 :=
    (Fin.sum_univ_castSucc (fun b : Fin 30 ↦ pIn rc b)).symm.trans hp1
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_quantBlockedFragmentLCU_sub_le (p₁ p₂ : Fin 126 → Fin 30 → ℝ)
    (r : Fin 9) (c : Fin 14) :
    ‖quantBlockedFragmentLCU p₁ r c - quantBlockedFragmentLCU p₂ r c‖ ≤
      ∑ b : Fin 30, |p₁ ⟨14 * r.val + c.val, by omega⟩ b -
        p₂ ⟨14 * r.val + c.val, by omega⟩ b| := by
  let rc : Fin 126 := ⟨14 * r.val + c.val, by omega⟩
  change ‖quantBlockedFragmentLCU p₁ r c - quantBlockedFragmentLCU p₂ r c‖ ≤
    ∑ b : Fin 30, |p₁ rc b - p₂ rc b|
  have hsgn (b : Fin 30) : |if negIn rc b then (-1 : ℝ) else 1| = 1 := by split_ifs <;> norm_num
  unfold quantBlockedFragmentLCU; dsimp only
  rw [sub_sub_sub_comm, ← sub_smul, ← Finset.sum_sub_distrib]
  have hI : ‖((((p₁ rc 29 * (if negIn rc 29 then -1 else 1) : ℝ) : ℂ) -
      ((p₂ rc 29 * (if negIn rc 29 then -1 else 1) : ℝ) : ℂ)) •
        (1 : Operator (2 ^ (2 * 58))))‖ ≤ |p₁ rc 29 - p₂ rc 29| := by
    rw [← Complex.ofReal_sub, ← sub_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, hsgn 29, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) (QubitisedWalk.unitary_opNorm_le_one 1)
  have hS : ‖∑ b : Fin 29, ((∑ σ : Fin 2,
      (((p₁ rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
        blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ) -
      (∑ σ : Fin 2,
      (((p₂ rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
        blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ))‖ ≤
      ∑ b : Fin 29, |p₁ rc b.castSucc - p₂ rc b.castSucc| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ ↦ ?_)
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_two]
    have hterm (σ : Fin 2) :
        ‖((((p₁ rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
          blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ) -
          ((((p₂ rc b.castSucc * (if negIn rc b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
          blockedOrbitalReflection (P450.leafVector (leafIndex r b)) σ)‖ ≤
          |p₁ rc b.castSucc - p₂ rc b.castSucc| / 2 := by
      rw [← sub_smul, ← Complex.ofReal_sub, ← sub_div, ← sub_mul, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_div, abs_mul, hsgn b.castSucc, mul_one,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_of_le_one_right (div_nonneg (abs_nonneg _) (by norm_num))
        (norm_blockedOrbitalReflection_le_one (givensLeaf_sum_sq 15 _) σ)
    linarith [hterm 0, hterm 1]
  have htot : (∑ b : Fin 29, |p₁ rc b.castSucc - p₂ rc b.castSucc|) + |p₁ rc 29 - p₂ rc 29| =
      ∑ b : Fin 30, |p₁ rc b - p₂ rc b| :=
    (Fin.sum_univ_castSucc (fun b : Fin 30 ↦ |p₁ rc b - p₂ rc b|)).symm
  exact (norm_sub_le _ _).trans (by linarith)

private theorem norm_conjTranspose_mul_self_sub_le {d : ℕ} [NeZero d] {A B : Operator d}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖Aᴴ * A - Bᴴ * B‖ ≤ 2 * ‖A - B‖ := by
  have hsplit : Aᴴ * A - Bᴴ * B = Aᴴ * (A - B) + (A - B)ᴴ * B := by
    simp only [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  have hAh : ‖Aᴴ‖ = ‖A‖ := by rw [← Matrix.star_eq_conjTranspose, norm_star]
  have hDh : ‖(A - B)ᴴ‖ = ‖A - B‖ := by rw [← Matrix.star_eq_conjTranspose, norm_star]
  rw [hsplit]
  calc ‖Aᴴ * (A - B) + (A - B)ᴴ * B‖
      ≤ ‖Aᴴ * (A - B)‖ + ‖(A - B)ᴴ * B‖ := norm_add_le _ _
    _ ≤ ‖Aᴴ‖ * ‖A - B‖ + ‖(A - B)ᴴ‖ * ‖B‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * ‖A - B‖ + ‖A - B‖ * 1 := by
        rw [hAh, hDh]
        exact add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
    _ = 2 * ‖A - B‖ := by ring

theorem norm_quantInnerP450HBlocked_sub_le
    {pIn : Fin 126 → Fin 30 → ℝ} (hp0 : ∀ rc b, 0 ≤ pIn rc b)
    (hp1 : ∀ rc, (∑ b : Fin 30, pIn rc b) = 1)
    {εIn : ℝ} (hl1 : ∀ rc : Fin 126, (∑ b : Fin 30, |pIn rc b - p450ExactInnerProb rc b|) ≤ εIn) :
    ‖quantInnerP450HBlocked pIn - BlockEncodingCore.p450HBlocked‖ ≤
      (4 * 97.3864 * 144553 / 188416) * εIn := by
  rw [← quantJointP450HBlocked_exact]; unfold quantInnerP450HBlocked quantJointP450HBlocked
  rw [add_sub_add_left_eq_sub, ← smul_sub, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 * 97.3864)]
  have hrc_le (r : Fin 9) (c : Fin 14) :
      ‖((p450ExactOuterProb (outerIndexEquiv (.inr (r, c))) : ℂ) •
          ((quantBlockedFragmentLCU pIn r c)ᴴ * quantBlockedFragmentLCU pIn r c)) -
        ((p450ExactOuterProb (outerIndexEquiv (.inr (r, c))) : ℂ) •
          ((quantBlockedFragmentLCU p450ExactInnerProb r c)ᴴ *
            quantBlockedFragmentLCU p450ExactInnerProb r c))‖ ≤
        p450ExactOuterProb (outerIndexEquiv (.inr (r, c))) * (2 * εIn) := by
    let rc : Fin 126 := ⟨14 * r.val + c.val, by omega⟩
    have hq_nn := p450ExactOuterProb_nonneg (outerIndexEquiv (.inr (r, c)))
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nn]
    refine mul_le_mul_of_nonneg_left ?_ hq_nn
    exact (norm_conjTranspose_mul_self_sub_le
      (norm_quantBlockedFragmentLCU_le_one r c (hp0 rc) (hp1 rc))
      (norm_quantBlockedFragmentLCU_le_one r c (p450ExactInnerProb_nonneg rc)
        (sum_p450ExactInnerProb rc))).trans
      (mul_le_mul_of_nonneg_left
        ((norm_quantBlockedFragmentLCU_sub_le pIn p450ExactInnerProb r c).trans (hl1 rc))
        (by norm_num))
  have hsum_le :
      ‖∑ r : Fin 9, ((∑ c : Fin 14, (p450ExactOuterProb (outerIndexEquiv (.inr (r, c))) : ℂ) •
          ((quantBlockedFragmentLCU pIn r c)ᴴ * quantBlockedFragmentLCU pIn r c)) -
        (∑ c : Fin 14, (p450ExactOuterProb (outerIndexEquiv (.inr (r, c))) : ℂ) •
          ((quantBlockedFragmentLCU p450ExactInnerProb r c)ᴴ *
            quantBlockedFragmentLCU p450ExactInnerProb r c)))‖ ≤
        (∑ r : Fin 9, ∑ c : Fin 14, p450ExactOuterProb (outerIndexEquiv (.inr (r, c)))) *
          (2 * εIn) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ hrc_le r c)
  have h2b_eq :
      (∑ r : Fin 9, ∑ c : Fin 14, p450ExactOuterProb (outerIndexEquiv (.inr (r, c)))) =
        (144553 : ℝ) / 188416 := by
    have hw (r : Fin 9) (c : Fin 14) :
        outerWeightNat (outerIndexEquiv (.inr (r, c))) = fragmentWeightNat r c := by
      have hnot : ¬ (58 + 14 * r.val + c.val < 58) := by omega
      change outerWeightNat ⟨58 + 14 * r.val + c.val, _⟩ = fragmentWeightNat r c
      simp only [outerWeightNat, hnot, ↓reduceDIte]
      congr 1 <;> exact Fin.ext (by dsimp; omega)
    unfold p450ExactOuterProb
    simp_rw [hw, ← Finset.sum_div, ← Nat.cast_sum]
    rw [sum_fragmentWeightNat_eq_144553]; norm_num
  calc (2 * 97.3864 : ℝ) * _
      ≤ (2 * 97.3864 : ℝ) * (((144553 : ℝ) / 188416) * (2 * εIn)) := by
        rw [← h2b_eq]; exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    _ = (4 * 97.3864 * 144553 / 188416) * εIn := by ring

end NormAndSectorBounds

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30

/-!
# Quantized `SU(2)` `factoredMag30` `δIdx = 0` SOS Block Encoding & Walk Closures

Establishes spin-blocked sector bounds and SOS block-encoding closures for the quantized `SU(2)`
`factoredMag30` engine:

1. **Spin-Blocked `AgreesOnElectronSector 58 63` & Sector Eigenvalue Bounds (`c_shift = 0`):**
   - Exact outer (`p450ExactOuterProb`): `δ_H ≤ 15e-9 / 272e-9 / 155e-8 / 783e-8 / 444e-7`.
   - Joint outer (`L¹ ≤ εOut`): `δ_H ≤ 2 * 97.3864 * εOut + 20e-9 / 354e-9 / 202e-8 / 1021e-8 /
     578e-7`, plus `quantP450_eigenSector_bounds` (`dfthcLowerBound ≤ E_t ≤ dfthcUpperBound + δ_H`).
2. **Quantized `PulledSOSBlockEncoding` & `δIdx = 0` `PerturbedRefl2Cert`:**
   - Polarization proof of `pulledSOSBlockEncoding_ubDirectXo7Pure_quantJoint` at `(eLB, 97.3864)`
     and outer-sandwich `PerturbedRefl2Cert` transfer (`δIdx = 0`, `δStep = 2 * δOut +
     δ1 + δ2`) across all 5 quantized inner cores (`0 TOFF`, `155 ≤ sUb`) in Forms A & B.

## References
- N. J. Ross and P. Selinger, *Quantum Inf. Comput.* **16**, 901–953 (2016), arXiv:1403.2975.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
- J. J. Goings, A. White, J. Lee, C. S. Tautermann, M. Degroote, C. Gidney, T. Shiozaki,
  R. Babbush, and N. C. Rubin, *Proc. Natl. Acad. Sci. USA* **119**, e2203533119 (2022),
  DOI: 10.1073/pnas.2203533119.
-/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open CoherentAlias AliasPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptFactoredMag30AndCoin9
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162StepSympAnfQrom21
open TopIntegrationBridge ReordOuter13Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepZeroCmp20
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepWalk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2MidSandwich
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactZeroCmp20OuterParam
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepZeroCmp20OuterParam
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowQMag30C (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Sector Commutation, `AgreesOnElectronSector 58 63`, & Eigenvalue Bounds -/

section SectorAndConcreteBounds

private theorem blockedOrbitalReflection_comm_electronSectorProjector
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

theorem quantJointP450HBlocked_comm_electronSectorProjector
    (qOut : Fin 184 → ℝ) (pIn : Fin 126 → Fin 30 → ℝ) (η : ℕ) :
    quantJointP450HBlocked qOut pIn * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * quantJointP450HBlocked qOut pIn := by
  let P := electronSectorProjector (2 * 58) η
  have h1b (ℓ : Fin 58) (σ : Fin 2) :
      blockedOneBodyProjector ℓ σ * P = P * blockedOneBodyProjector ℓ σ := by
    unfold blockedOneBodyProjector; dsimp only [P]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one,
      blockedOrbitalReflection_comm_electronSectorProjector]
  have h2b (r : Fin 9) (c : Fin 14) :
      quantBlockedFragmentLCU pIn r c * P = P * quantBlockedFragmentLCU pIn r c := by
    unfold quantBlockedFragmentLCU; dsimp only [P]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      Finset.sum_mul, Finset.mul_sum, blockedOrbitalReflection_comm_electronSectorProjector]
  have hsq {M : Operator (2 ^ (2 * 58))} (hM : M * P = P * M) (hH : Mᴴ = M) :
      (Mᴴ * M) * P = P * (Mᴴ * M) := by
    rw [hH, Matrix.mul_assoc, hM, ← Matrix.mul_assoc, hM, Matrix.mul_assoc]
  unfold quantJointP450HBlocked
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    Finset.sum_mul, Finset.mul_sum]
  refine congrArg (_ + ((2 * 97.3864 : ℝ) : ℂ) • ·) (congrArg₂ (· + ·) ?_ ?_)
  · exact Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_congr rfl fun σ _ ↦
      congrArg _ (hsq (h1b ℓ σ) (blockedOneBodyProjector_conjTranspose ℓ σ))
  · exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦
      congrArg _ (hsq (h2b r c) (quantBlockedFragmentLCU_conjTranspose pIn r c))

theorem norm_electronSectorProjector_le_one (k η : ℕ) :
    ‖electronSectorProjector k η‖ ≤ 1 :=
  QubitisedWalk.opNorm_le_of_vecNormSq_mulVec (electronSectorProjector k η) zero_le_one fun v ↦ by
    rw [_root_.one_pow, one_mul]; unfold QubitisedWalk.vecNormSq
    exact PerturbedQPEClosure.sum_normSq_electronSectorProjector_mulVec_le k η v

private theorem norm_conj_proj_le_loc {d : ℕ} [NeZero d] {P D : Operator d} {δ : ℝ}
    (hP : ‖P‖ ≤ 1) (hD : ‖D‖ ≤ δ) : ‖P * D * P‖ ≤ δ := by
  calc ‖P * D * P‖
      ≤ ‖P * D‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ ‖P * D‖ * 1 := mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ = ‖P * D‖ := mul_one _
    _ ≤ ‖P‖ * ‖D‖ := norm_mul_le _ _
    _ ≤ 1 * ‖D‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ δ := by rw [one_mul]; exact hD

theorem agreesOnElectronSector_of_comm_and_opNorm {η : ℕ}
    {H_eff B : Operator (2 ^ (2 * 58))} {δ_H : ℝ}
    (hcomm : H_eff * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * H_eff)
    (hop : ‖H_eff - B‖ ≤ δ_H) :
    AgreesOnElectronSector 58 η H_eff B δ_H :=
  ⟨hcomm, norm_conj_proj_le_loc (norm_electronSectorProjector_le_one (2 * 58) η) hop⟩

end SectorAndConcreteBounds

/-! ## Section 2: Quantized `PulledSOSBlockEncoding` (`eLB = dfthcLowerBound`, `lam = 97.3864`) -/

/-- `σ`-permuted `256`-slot outer `PREP_out` validity predicate for a general `184`-item outer
distribution `qOut : Fin 184 → ℝ`. -/
def PrepOutQuantPerm256 (σ : Equiv.Perm (Fin (2 ^ 8))) (qOut : Fin 184 → ℝ) {wOuter : ℕ}
    (prepOutPerm : Unitary (2 ^ mOutUB wOuter)) : Prop :=
  (∀ o' : Fin (2 ^ mOutUB wOuter),
    184 ≤ ((rXoLoc wOuter).extractIndex o').val → prepOutPerm.1 o' 0 = 0) ∧
  (∀ (xo' : Fin 184) (so : Fin 2),
    (∑ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
        ((rXoLoc wOuter).extractIndex o').val = xo'.val ∧ (rSigOutLoc wOuter).extractIndex o' = so),
      Complex.normSq (prepOutPerm.1 o' 0)) =
      if h : (σ ⟨xo'.val, by omega⟩).val < 184 then
        qOut ⟨(σ ⟨xo'.val, by omega⟩).val, h⟩ / 2
      else 0)

theorem prepOutQuantPerm256_of_validPerm256 {σ : Equiv.Perm (Fin (2 ^ 8))} {wOuter : ℕ}
    {prepOutPerm : Unitary (2 ^ mOutUB wOuter)} (h : PrepOutValidPerm256 σ prepOutPerm) :
    PrepOutQuantPerm256 σ p450ExactOuterProb prepOutPerm := by
  refine ⟨h.1, fun xo' so ↦ (h.2 xo' so).trans ?_⟩
  split_ifs with hlt <;> [ (unfold p450ExactOuterProb; ring); rfl ]

/-- Full-`128` inner `PREP_mid` validity predicate for a general `126 × 30` inner distribution
`pIn : Fin 126 → Fin 30 → ℝ`. -/
def PrepMidQuant128 (pIn : Fin 126 → Fin 30 → ℝ) {wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) : Prop :=
  (∀ (rc : Fin 126) (m : Fin (2 ^ mMidUB wInner2)),
    30 ≤ ((rBLoc wInner2).extractIndex m).val → (prepMid ⟨rc.val, by omega⟩).1 m 0 = 0) ∧
  (∀ (rc : Fin 126) (b : Fin 30) (si : Fin 2),
    (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
        ((rBLoc wInner2).extractIndex m).val = b.val ∧ (rSigInLoc wInner2).extractIndex m = si),
      Complex.normSq ((prepMid ⟨rc.val, by omega⟩).1 m 0)) = pIn rc b / 2) ∧
  (∀ (rc : Fin (2 ^ 7)) (si : Fin 2),
    (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦ (rSigInLoc wInner2).extractIndex m
      = si),
      Complex.normSq ((prepMid rc).1 m 0)) = 1 / 2)

/-- Quantized half-step system operator `M(pIn; xo, so)` for `quantJointP450HBlocked`. -/
noncomputable def quantHalfSystemOp (pIn : Fin 126 → Fin 30 → ℝ)
    (xo : Fin (2 ^ 8)) (so : Fin 2) : Operator (2 ^ (2 * 58)) :=
  if h1 : xo.val < 58 then
    blockedOneBodyProjector ⟨xo.val, h1⟩ so
  else if h2 : xo.val < 184 then
    quantBlockedFragmentLCU pIn ⟨(xo.val - 58) / 14, by omega⟩ ⟨(xo.val - 58) % 14, by omega⟩
  else 0

@[simp] theorem quantHalfSystemOp_conjTranspose (pIn : Fin 126 → Fin 30 → ℝ)
    (xo : Fin (2 ^ 8)) (so : Fin 2) :
    (quantHalfSystemOp pIn xo so)ᴴ = quantHalfSystemOp pIn xo so := by
  unfold quantHalfSystemOp
  split_ifs
  · exact blockedOneBodyProjector_conjTranspose _ _
  · exact quantBlockedFragmentLCU_conjTranspose _ _ _
  · exact Matrix.conjTranspose_zero

private theorem prepMidDirectXo7MuxUnitary_mulVec_embedKet_loc {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' m =
      ∑ m' : Fin (2 ^ mMidUB wInner2),
        ((prepMid ((rXo7Loc wOuter).extractIndex o')).1 m' m) • embedKet ψ o' m' := by
  have hxo (g : Fin (2 ^ nUB wOuter wInner2))
      (hne : (rXo7UB wOuter wInner2).extractIndex g ≠ (rXo7Loc wOuter).extractIndex o') :
      embedKet ψ o' m g = 0 := by
    dsimp [embedKet]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g =
        o' ∧ (rMidUB wOuter wInner2).extractIndex g = m
    · exact absurd (by rw [show rXo7UB wOuter wInner2 = (rOutUB wOuter wInner2).compose (rXo7Loc
        wOuter) from rfl,
        QRegister.extractIndex_compose, hc.1]) hne
    · simp [hc]
  unfold prepMidDirectXo7MuxUnitary
  rw [muxUnitary_mulVec_of_proj _ _ _ _ ((rXo7Loc wOuter).extractIndex o') _ hxo,
    embedMatrix_rMidUB_mulVec_embedKet]

private theorem sum_inv_ite_embedKet_loc {wOuter wInner2 : ℕ} (U : Unitary (2 ^ mMidUB wInner2))
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

private theorem finset_sum_partition_by_loc {α β M : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [AddCommMonoid M] (p : α → β) (f : α → M) :
    ∑ a : α, f a = ∑ b : β, ∑ a ∈ Finset.univ.filter (fun a ↦ p a = b), f a :=
  (Finset.sum_fiberwise_of_maps_to (fun _ _ ↦ Finset.mem_univ _) f).symm

private theorem negInPadded_eq_loc (rc126 : Fin 126) (b30 : Fin 30) :
    negInPadded ⟨rc126.val, by omega⟩ ⟨b30.val, by omega⟩ = negIn rc126 b30 := by
  unfold negInPadded; exact dite_eq_left ⟨rc126.isLt, b30.isLt⟩

private theorem projMid_directXo7_selectPure_eq_quantHalfSystemOp {σ : Equiv.Perm (Fin (2 ^ 8))}
    (hσ : IsZeroRcOuterPerm σ) {wOuter wInner2 : ℕ} {pIn : Fin 126 → Fin 30 → ℝ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hMid : PrepMidQuant128 pIn prepMid)
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (hSelAct : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      ((rXoLoc wOuter).extractIndex o').val < 184 →
      (prepMid ((rXo7Loc wOuter).extractIndex o')).1 m 0 ≠ 0 →
      selectPure.1 *ᵥ embedKet ψ o' m =
        embedKet ((selectBranchUnitary (σ ((rXoLoc wOuter).extractIndex o'))
          ((rSigOutLoc wOuter).extractIndex o')
          ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1 *ᵥ ψ) o' m)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
    (hxo' : ((rXoLoc wOuter).extractIndex o').val < 184) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let so := (rSigOutLoc wOuter).extractIndex o'
    (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
        (((prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid)⁻¹ *
          selectPure * prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' 0) =
      embedKet (quantHalfSystemOp pIn (σ xo') so *ᵥ ψ) o' 0 := by
  intro xo' so; let rc7 := (rXo7Loc wOuter).extractIndex o'
  have hSumLhs :
      (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
        (((prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid)⁻¹ * selectPure *
          prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' 0) =
      embedKet ((∑ m : Fin (2 ^ mMidUB wInner2),
        (Complex.normSq ((prepMid rc7).1 m 0) : ℂ) •
          (selectBranchUnitary (σ xo') so
            ((rBLoc wInner2).extractIndex m)
            ((rSigInLoc wInner2).extractIndex m)).1) *ᵥ ψ) o' 0 := by
    have hinv : (prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid)⁻¹ =
        prepMidDirectXo7MuxUnitary wOuter wInner2 (fun r ↦ (prepMid r)⁻¹) := muxUnitary_inv _ _ _ _
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hinv,
      prepMidDirectXo7MuxUnitary_mulVec_embedKet_loc, Matrix.mulVec_sum, Matrix.mulVec_smul]
    have hterm (m : Fin (2 ^ mMidUB wInner2)) :
        ((prepMid rc7).1 m 0) •
          ((rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
            ((prepMidDirectXo7MuxUnitary wOuter wInner2 fun r ↦ (prepMid r)⁻¹).1 *ᵥ
              (selectPure.1 *ᵥ embedKet ψ o' m))) =
        embedKet (((Complex.normSq ((prepMid rc7).1 m 0) : ℂ) •
          (selectBranchUnitary (σ xo') so
            ((rBLoc wInner2).extractIndex m)
            ((rSigInLoc wInner2).extractIndex m)).1) *ᵥ ψ) o' 0 := by
      by_cases hnz : (prepMid rc7).1 m 0 = 0
      · rw [hnz, Complex.normSq_zero, Complex.ofReal_zero, zero_smul, zero_smul, Matrix.zero_mulVec]
        ext g; simp [embedKet]
      · rw [hSelAct ψ o' m hxo' hnz]
        simp only [prepMidDirectXo7MuxUnitary_mulVec_embedKet_loc, Matrix.mulVec_sum,
          Matrix.mulVec_smul, projMid_mulVec_embedKet]
        exact sum_inv_ite_embedKet_loc (prepMid rc7) m _ ψ o'
    refine (Finset.sum_congr rfl fun m _ ↦ hterm m).trans ?_
    rw [← embedKet_sum, Matrix.sum_mulVec]
  rw [hSumLhs]
  have hσlt : (σ xo').val < 184 := (hσ.lt184_iff xo').mpr hxo'
  by_cases h1b : (σ xo').val < 58
  · let ℓ : Fin 58 := ⟨(σ xo').val, h1b⟩
    have his1 : isOneBodyXo (σ xo') = true := decide_eq_true h1b
    have hn1 : neg1bPadded (σ xo') = neg1b ℓ := by simp [neg1bPadded, h1b, ℓ]
    have hbr0 (b : Fin (2 ^ 5)) : (selectBranchUnitary (σ xo') so b 0).1 = 1 := by
      change (if negPhaseOf (σ xo') b 0 then (-1 : ℂ) else 1) •
        (if enROf (σ xo') b 0 then
          (blockedRowReflectionUnitary (rowIdxOf (σ xo') b) (sigSelOf (σ xo') so 0)).1
         else 1) = 1
      simp [enROf, negPhaseOf, his1]
    have hbr1 (b : Fin (2 ^ 5)) : (selectBranchUnitary (σ xo') so b 1).1 =
        (-(oneBodySign ℓ : ℂ)) • blockedOrbitalReflection (P450.oneBodyVector ℓ) so := by
      change (if negPhaseOf (σ xo') b 1 then (-1 : ℂ) else 1) •
        (if enROf (σ xo') b 1 then
          (blockedRowReflectionUnitary (rowIdxOf (σ xo') b) (sigSelOf (σ xo') so 1)).1
         else 1) = _
      have hrow : p450RowVector (rowIdxOf (σ xo') b) = P450.oneBodyVector ℓ := by
        unfold p450RowVector; rw [dite_eq_left (by simp [rowIdxOf, h1b])]
        exact congrArg P450.oneBodyVector (Fin.ext (by simp [rowIdxOf, h1b, ℓ]))
      simp only [enROf, sigSelOf, negPhaseOf, his1, hn1, ↓reduceIte, blockedRowReflectionUnitary,
        hrow]
      refine congrArg (· • _) ?_; rw [oneBodySign_eq_neg1b ℓ]; cases neg1b ℓ <;> simp
    have hbr_indep (b : Fin (2 ^ 5)) (si : Fin 2) :
        (selectBranchUnitary (σ xo') so b si).1 = (selectBranchUnitary (σ xo') so 0 si).1 := by
      fin_cases si
      · exact (hbr0 b).trans (hbr0 0).symm
      · exact (hbr1 b).trans (hbr1 0).symm
    refine congrArg (fun φ ↦ embedKet (w_gi := wInner2) φ o' 0) (congrArg (· *ᵥ ψ) ?_)
    rw [Finset.sum_congr rfl fun m _ ↦
        congrArg _ (hbr_indep ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex
          m)),
      ← Finset.sum_fiberwise_of_maps_to (g := (rSigInLoc wInner2).extractIndex)
        (fun _ _ ↦ Finset.mem_univ _)]
    have hfib (si : Fin 2) :
        (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
            (rSigInLoc wInner2).extractIndex m = si),
          (Complex.normSq ((prepMid rc7).1 m 0) : ℂ) •
            (selectBranchUnitary (σ xo') so 0 ((rSigInLoc wInner2).extractIndex m)).1) =
        ((1 / 2 : ℝ) : ℂ) • (selectBranchUnitary (σ xo') so 0 si).1 := by
      rw [← hMid.2.2 rc7 si, Complex.ofReal_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun m hm ↦ by rw [(Finset.mem_filter.mp hm).2]
    refine (Finset.sum_congr rfl fun si _ ↦ hfib si).trans ?_
    rw [Fin.sum_univ_two, hbr0 0, hbr1 0, ← smul_add, neg_smul, ← sub_eq_add_neg]
    dsimp only [quantHalfSystemOp]; rw [dite_eq_left h1b]
    unfold blockedOneBodyProjector; push_cast; rw [one_div]
  · let xo := σ xo'
    let r : Fin 9 := ⟨(xo.val - 58) / 14, by omega⟩
    let c : Fin 14 := ⟨(xo.val - 58) % 14, by omega⟩
    let rc126 : Fin 126 := ⟨xo.val - 58, by omega⟩
    have his1 : isOneBodyXo xo = false := decide_eq_false h1b
    have hrc_eq : rc7 = rcBitsOfXo xo :=
      ((rXoLoc wOuter).extractIndex_compose (QRegister.block 0 7 (by decide)) o').trans
        (extract_rXo7_eq_rcBitsOfXo_of_isZeroRcOuterPerm hσ xo' hxo' (by omega))
    have hrc_bits : rcBitsOfXo xo = ⟨rc126.val, by omega⟩ :=
      Fin.ext (by dsimp [rcBitsOfXo, rc126]; rw [ite_eq_right h1b]; omega)
    have hrc7 : rc7 = ⟨rc126.val, by omega⟩ := hrc_eq.trans hrc_bits
    have hrdiv : (rDiv14OfRc (rcBitsOfXo xo)).val = r.val := by
      rw [rDiv14OfRc_eq_div (rcBitsOfXo xo) (by rw [hrc_bits]; exact rc126.isLt), hrc_bits]
    refine congrArg (fun φ ↦ embedKet (w_gi := wInner2) φ o' 0) (congrArg (· *ᵥ ψ) ?_)
    rw [finset_sum_partition_by_loc (fun m : Fin (2 ^ mMidUB wInner2) ↦
      ((rBLoc wInner2).extractIndex m, (rSigInLoc wInner2).extractIndex m)), Fintype.sum_prod_type]
    have hgroup (b5 : Fin (2 ^ 5)) (si : Fin (2 ^ 1)) :
        (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
            ((rBLoc wInner2).extractIndex m, (rSigInLoc wInner2).extractIndex m) = (b5, si)),
          (Complex.normSq ((prepMid rc7).1 m 0) : ℂ) •
            (selectBranchUnitary xo so ((rBLoc wInner2).extractIndex m)
              ((rSigInLoc wInner2).extractIndex m)).1) =
        if hb30 : b5.val < 30 then
          ((pIn rc126 ⟨b5.val, hb30⟩ / 2 : ℝ) : ℂ) • (selectBranchUnitary xo so b5 si).1
        else 0 := by
      have hrew :
          (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
              ((rBLoc wInner2).extractIndex m, (rSigInLoc wInner2).extractIndex m) = (b5, si)),
            (Complex.normSq ((prepMid rc7).1 m 0) : ℂ) •
              (selectBranchUnitary xo so ((rBLoc wInner2).extractIndex m)
                ((rSigInLoc wInner2).extractIndex m)).1) =
          ((∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
              ((rBLoc wInner2).extractIndex m).val = b5.val ∧ (rSigInLoc wInner2).extractIndex m =
                si),
            Complex.normSq ((prepMid rc7).1 m 0) : ℝ) : ℂ) •
              (selectBranchUnitary xo so b5 si).1 := by
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr (by ext m; simp [Prod.ext_iff, Fin.ext_iff]) fun m hm ↦ ?_
        rcases Finset.mem_filter.mp hm with ⟨_, h1, h2⟩
        rw [show (rBLoc wInner2).extractIndex m = b5 from Fin.ext h1, h2]
      rw [hrew]
      by_cases hb30 : b5.val < 30
      · simp only [hb30, ↓reduceDIte]; rw [hrc7, hMid.2.1 rc126 ⟨b5.val, hb30⟩ si]
      · simp only [hb30, ↓reduceDIte]
        have hz : ∀ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
            ((rBLoc wInner2).extractIndex m).val = b5.val ∧ (rSigInLoc wInner2).extractIndex m =
              si),
            Complex.normSq ((prepMid rc7).1 m 0) = 0 := by
          intro m hm
          rcases Finset.mem_filter.mp hm with ⟨_, h1, _⟩
          rw [hrc7, hMid.1 rc126 m (by omega), map_zero]
        rw [Finset.sum_eq_zero hz, Complex.ofReal_zero, zero_smul]
    refine (Finset.sum_congr rfl fun b5 _ ↦ Finset.sum_congr rfl fun si _ ↦ hgroup b5 si).trans ?_
    let emb30 : Fin 30 ↪ Fin (2 ^ 5) :=
      ⟨fun b ↦ ⟨b.val, by omega⟩, fun a b h ↦ Fin.ext (Fin.mk.inj h)⟩
    have hsum30 :
        (∑ b5 : Fin (2 ^ 5), ∑ si : Fin (2 ^ 1),
          if hb30 : b5.val < 30 then
            ((pIn rc126 ⟨b5.val, hb30⟩ / 2 : ℝ) : ℂ) • (selectBranchUnitary xo so b5 si).1
          else 0) =
        ∑ b : Fin 30, ∑ si : Fin 2,
          ((pIn rc126 b / 2 : ℝ) : ℂ) • (selectBranchUnitary xo so ⟨b.val, by omega⟩ si).1 := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map emb30)), Finset.sum_map]
      · refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun si _ ↦ ?_
        have hb30 : (emb30 b).val < 30 := b.isLt
        have hb_eq : (⟨(emb30 b).val, hb30⟩ : Fin 30) = b := Fin.ext rfl
        change (if h : (emb30 b).val < 30 then _ else 0) = _
        rw [dite_eq_left hb30, hb_eq]; rfl
      · intro b5 _ hb5
        have hn30 : ¬ (b5.val < 30) := fun hlt ↦
          hb5 (Finset.mem_map.mpr ⟨⟨b5.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [hn30]
    rw [hsum30, Fin.sum_univ_castSucc]
    have hrc_pair : (⟨14 * r.val + c.val, by omega⟩ : Fin 126) = rc126 :=
      Fin.ext (by dsimp [r, c, rc126]; omega)
    have hlast :
        (∑ si : Fin 2, ((pIn rc126 (Fin.last 29) / 2 : ℝ) : ℂ) •
          (selectBranchUnitary xo so ⟨(Fin.last 29).val, by omega⟩ si).1) =
        ((pIn rc126 29 * (if negIn rc126 29 then -1 else 1) : ℝ) : ℂ) •
          (1 : Operator (2 ^ (2 * 58))) := by
      have hbr29 (si : Fin 2) :
          (selectBranchUnitary xo so ⟨(Fin.last 29).val, by omega⟩ si).1 =
            ((if negIn rc126 29 then (-1 : ℝ) else 1 : ℝ) : ℂ) • 1 := by
        let b29 : Fin (2 ^ 5) := ⟨(Fin.last 29).val, by omega⟩
        have hb29_nlt : ¬ (b29.val < 29) := by dsimp [b29]; omega
        have hn29 : negInPadded (rcBitsOfXo xo) b29 = negIn rc126 29 := by
          dsimp [b29]; rw [hrc_bits]; exact negInPadded_eq_loc rc126 (Fin.last 29)
        change (if negPhaseOf xo b29 si then (-1 : ℂ) else 1) •
            (if enROf xo b29 si then
              (blockedRowReflectionUnitary (rowIdxOf xo b29) (sigSelOf xo so si)).1
             else 1) = _
        simp only [enROf, negPhaseOf, his1, hb29_nlt, hn29]
        cases negIn rc126 29 <;> simp
      simp_rw [hbr29, smul_smul]; rw [Fin.sum_univ_two, ← add_smul]
      have hl29 : (Fin.last 29 : Fin 30) = 29 := rfl
      rw [hl29]; refine congrArg (· • _) ?_; push_cast; ring
    have hleaf (b : Fin 29) (si : Fin 2) :
        ((pIn rc126 b.castSucc / 2 : ℝ) : ℂ) •
          (selectBranchUnitary xo so ⟨b.castSucc.val, by omega⟩ si).1 =
        -((((pIn rc126 b.castSucc * (if negIn rc126 b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) •
            blockedOrbitalReflection (P450.leafVector (leafIndex r b)) si) := by
      let b5 : Fin (2 ^ 5) := ⟨b.castSucc.val, by omega⟩
      have hlt29 : b5.val < 29 := b.isLt
      have hnin : negInPadded (rcBitsOfXo xo) b5 = negIn rc126 b.castSucc := by
        dsimp [b5]; rw [hrc_bits]; exact negInPadded_eq_loc rc126 b.castSucc
      have hrow : p450RowVector (rowIdxOf xo b5) = P450.leafVector (leafIndex r b) := by
        have hidx_val : (rowIdxOf xo b5).val = 58 + 29 * r.val + b.val := by
          unfold rowIdxOf; rw [dite_eq_right h1b]; dsimp [b5]; rw [hrdiv]; omega
        unfold p450RowVector; rw [dite_eq_right (by omega)]
        exact congrArg P450.leafVector (Fin.ext (by dsimp [leafIndex]; omega))
      have hbr : (selectBranchUnitary xo so b5 si).1 =
          ((-(if negIn rc126 b.castSucc then (-1 : ℝ) else 1) : ℝ) : ℂ) •
            blockedOrbitalReflection (P450.leafVector (leafIndex r b)) si := by
        have hen : enROf xo b5 si = true := by simp [enROf, his1, hlt29]
        have hsig : sigSelOf xo so si = si := by simp [sigSelOf, his1]
        have hneg : negPhaseOf xo b5 si = !(negIn rc126 b.castSucc) := by
          simp [negPhaseOf, his1, hlt29, hnin]
        have hsc : (if (!(negIn rc126 b.castSucc)) = true then (-1 : ℂ) else 1) =
            ((-(if negIn rc126 b.castSucc then (-1 : ℝ) else 1) : ℝ) : ℂ) := by
          cases negIn rc126 b.castSucc <;> norm_num
        change (if negPhaseOf xo b5 si then (-1 : ℂ) else 1) •
            (if enROf xo b5 si then
              (blockedRowReflectionUnitary (rowIdxOf xo b5) (sigSelOf xo so si)).1
             else 1) = _
        rw [hen, hsig, hneg, ite_eq_left rfl, hsc]
        change _ • blockedOrbitalReflection (p450RowVector (rowIdxOf xo b5)) si = _
        rw [hrow]
      have hsc2 : ((pIn rc126 b.castSucc / 2 : ℝ) : ℂ) *
            ((-(if negIn rc126 b.castSucc then (-1 : ℝ) else 1) : ℝ) : ℂ) =
          -(((pIn rc126 b.castSucc * (if negIn rc126 b.castSucc then -1 else 1)) / 2 : ℝ) : ℂ) :=
        by push_cast; ring
      change _ • (selectBranchUnitary xo so b5 si).1 = _
      rw [hbr, smul_smul, hsc2, neg_smul]
    have hsum_leaf := (Finset.sum_congr (s₁ := Finset.univ) rfl fun b _ ↦
      (Finset.sum_congr (s₁ := Finset.univ) rfl fun si _ ↦ hleaf b si).trans
        (Finset.sum_neg_distrib _)).trans (Finset.sum_neg_distrib _)
    rw [hsum_leaf, hlast]
    dsimp only [quantHalfSystemOp]; rw [dite_eq_right h1b, dite_eq_left hσlt]
    unfold quantBlockedFragmentLCU; dsimp only; rw [hrc_pair, add_comm, ← sub_eq_add_neg]

private theorem dotProduct_star_embedKet_ortho {wOuter wInner2 : ℕ}
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
    by_cases h1 : (rOutUB wOuter wInner2).extractIndex g =
        o₁ ∧ (rMidUB wOuter wInner2).extractIndex g = 0
    · by_cases h2 : (rOutUB wOuter wInner2).extractIndex g =
          o₂ ∧ (rMidUB wOuter wInner2).extractIndex g = 0
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

private theorem dotProduct_star_mulVec_loc {d : ℕ} (A : Operator d) (x y : Fin d → ℂ) :
    dotProduct (star (A *ᵥ x)) y = dotProduct (star x) (Aᴴ *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

private theorem eq_of_projAll_and_dotProduct_embedKet {wOuter wInner2 : ℕ}
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
        (rOutUB wOuter wInner2).extractIndex g = 0 ∧ (rMidUB wOuter wInner2).extractIndex g = 0 :=
          by
      rw [rAllUB_eq_concat, CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
        CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
        CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
      exact ⟨fun h ↦ ⟨fun i ↦ by simpa using h (Fin.castAdd _ i),
          fun j ↦ by simpa using h (Fin.natAdd _ j)⟩,
        fun ⟨ho, hm⟩ idx ↦ by
          obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
          · simpa using ho i
          · simpa using hm j⟩
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g =
        0 ∧ (rMidUB wOuter wInner2).extractIndex g = 0
    · have hsp : (ubSplitEquiv wOuter wInner2).symm ((rSysUB wOuter wInner2).extractIndex g, 0, 0) =
          g := by
        rw [← hc.1, ← hc.2, ← ubSplitEquiv_apply, Equiv.symm_apply_apply]
      dsimp [embedKet, dSys]; rw [ite_eq_left hc, hsp]
    · have hnall : (rAllUB wOuter wInner2).extractIndex g ≠ 0 := fun h ↦ hc (hall0.mp h)
      have hdg := congrFun hd_proj.symm g
      rw [(rAllUB wOuter wInner2).basisOutcomeProjector_mulVec, ite_eq_right hnall] at hdg
      dsimp [embedKet]; rw [hdg, ite_eq_right hc]
  have hd0 : dotProduct (star dSys) dSys = 0 := by
    have h1 : dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) dSys 0 0)) d = 0 := by
      dsimp [d]; rw [dotProduct_sub, sub_eq_zero]; exact hdot dSys
    rw [hd_eq, dotProduct_star_embedKet_ortho, ite_eq_left rfl] at h1; exact h1
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

private theorem quantJoint_sos_sum_eq {σ : Equiv.Perm (Fin (2 ^ 8))} (hσ : IsZeroRcOuterPerm σ)
    {wOuter : ℕ} {qOut : Fin 184 → ℝ} {pIn : Fin 126 → Fin 30 → ℝ}
    {prepOutPerm : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutQuantPerm256 σ qOut prepOutPerm) :
    (∑ o' : Fin (2 ^ mOutUB wOuter),
      (Complex.normSq (prepOutPerm.1 o' 0) : ℂ) •
        ((quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
            ((rSigOutLoc wOuter).extractIndex o'))ᴴ *
          quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
            ((rSigOutLoc wOuter).extractIndex o'))) =
    (2 * 97.3864 : ℂ)⁻¹ • (quantJointP450HBlocked qOut pIn - (dfthcLowerBound : ℂ) • 1) := by
  rw [finset_sum_partition_by_loc (fun o' : Fin (2 ^ mOutUB wOuter) ↦
    ((rXoLoc wOuter).extractIndex o', (rSigOutLoc wOuter).extractIndex o')), Fintype.sum_prod_type]
  have hgroup (xo8 : Fin (2 ^ 8)) (so : Fin 2) :
      (∑ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
          ((rXoLoc wOuter).extractIndex o', (rSigOutLoc wOuter).extractIndex o') = (xo8, so)),
        (Complex.normSq (prepOutPerm.1 o' 0) : ℂ) •
          ((quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
              ((rSigOutLoc wOuter).extractIndex o'))ᴴ *
            quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
              ((rSigOutLoc wOuter).extractIndex o'))) =
      if hlt : xo8.val < 184 then
        ((qOut ⟨(σ xo8).val, (hσ.lt184_iff xo8).mpr hlt⟩ / 2 : ℝ) : ℂ) •
          ((quantHalfSystemOp pIn (σ xo8) so)ᴴ * quantHalfSystemOp pIn (σ xo8) so)
      else 0 := by
    have hs1 :
        (∑ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
            ((rXoLoc wOuter).extractIndex o', (rSigOutLoc wOuter).extractIndex o') = (xo8, so)),
          (Complex.normSq (prepOutPerm.1 o' 0) : ℂ) •
            ((quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
                ((rSigOutLoc wOuter).extractIndex o'))ᴴ *
              quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
                ((rSigOutLoc wOuter).extractIndex o'))) =
        ((∑ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
            ((rXoLoc wOuter).extractIndex o').val = xo8.val ∧ (rSigOutLoc wOuter).extractIndex o' =
              so),
          Complex.normSq (prepOutPerm.1 o' 0) : ℝ) : ℂ) •
            ((quantHalfSystemOp pIn (σ xo8) so)ᴴ * quantHalfSystemOp pIn (σ xo8) so) := by
      rw [Complex.ofReal_sum, Finset.sum_smul]
      refine Finset.sum_congr (by ext o'; simp [Prod.ext_iff, Fin.ext_iff]) fun o' ho' ↦ ?_
      rcases Finset.mem_filter.mp ho' with ⟨_, h1, h2⟩
      rw [show (rXoLoc wOuter).extractIndex o' = xo8 from Fin.ext h1, h2]
    rw [hs1]
    by_cases hlt : xo8.val < 184
    · simp only [hlt, ↓reduceDIte]
      have hpr := hOut.2 ⟨xo8.val, hlt⟩ so
      have hσlt : (σ xo8).val < 184 := (hσ.lt184_iff xo8).mpr hlt
      simp only [Fin.eta, hσlt, ↓reduceDIte] at hpr
      rw [hpr]
    · simp only [hlt, ↓reduceDIte]
      have hz : ∀ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
          ((rXoLoc wOuter).extractIndex o').val = xo8.val ∧ (rSigOutLoc wOuter).extractIndex o' =
            so),
          Complex.normSq (prepOutPerm.1 o' 0) = 0 := by
        intro o' ho'
        rcases Finset.mem_filter.mp ho' with ⟨_, h1, _⟩
        rw [hOut.1 o' (by omega), map_zero]
      rw [Finset.sum_eq_zero hz, Complex.ofReal_zero, zero_smul]
  simp_rw [hgroup]
  let emb184 : Fin 184 ↪ Fin (2 ^ 8) :=
    ⟨fun xo ↦ ⟨xo.val, by omega⟩, fun a b h ↦ Fin.ext (Fin.mk.inj h)⟩
  have hsum184 :
      (∑ xo8 : Fin (2 ^ 8), ∑ so : Fin (2 ^ 1),
        if hlt : xo8.val < 184 then
          ((qOut ⟨(σ xo8).val, (hσ.lt184_iff xo8).mpr hlt⟩ / 2 : ℝ) : ℂ) •
            ((quantHalfSystemOp pIn (σ xo8) so)ᴴ * quantHalfSystemOp pIn (σ xo8) so)
        else 0) =
      ∑ xo : Fin 184, ∑ so : Fin 2,
        ((qOut xo / 2 : ℝ) : ℂ) •
          ((quantHalfSystemOp pIn ⟨xo.val, by omega⟩ so)ᴴ *
            quantHalfSystemOp pIn ⟨xo.val, by omega⟩ so) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map emb184)), Finset.sum_map]
    · refine Finset.sum_bij (fun xo' _ ↦
          ⟨(σ (emb184 xo')).val, (hσ.lt184_iff (emb184 xo')).mpr xo'.isLt⟩)
        (fun _ _ ↦ Finset.mem_univ _)
        (fun a b _ _ h ↦ emb184.injective (σ.injective (Fin.ext (Fin.mk.inj h))))
        (fun xo _ ↦ ⟨⟨(σ.symm (emb184 xo)).val,
            (hσ.lt184_iff _).mp (by rw [σ.apply_symm_apply]; exact xo.isLt)⟩,
          Finset.mem_univ _, Fin.ext (by
            change (σ ⟨(σ.symm (emb184 xo)).val, _⟩).val = xo.val
            rw [Fin.eta, σ.apply_symm_apply]; rfl)⟩)
        fun xo' _ ↦ Finset.sum_congr rfl fun so _ ↦ ?_
      have hlt184 : (emb184 xo').val < 184 := xo'.isLt
      have hfin : (⟨(⟨(σ (emb184 xo')).val,
          (hσ.lt184_iff (emb184 xo')).mpr xo'.isLt⟩ : Fin 184).val, by omega⟩ : Fin (2 ^ 8)) =
          σ (emb184 xo') := Fin.ext rfl
      change (if hlt : (emb184 xo').val < 184 then _ else 0) = _
      rw [dite_eq_left hlt184, hfin]
    · intro xo8 _ hxo8
      have hn184 : ¬ (xo8.val < 184) := fun hlt ↦
        hxo8 (Finset.mem_map.mpr ⟨⟨xo8.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp [hn184]
  rw [hsum184, ← outerIndexEquiv.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1b :
      (∑ ℓ : Fin 58, ∑ so : Fin 2,
        ((qOut (outerIndexEquiv (.inl ℓ)) / 2 : ℝ) : ℂ) •
          ((quantHalfSystemOp pIn ⟨(outerIndexEquiv (.inl ℓ)).val, by omega⟩ so)ᴴ *
            quantHalfSystemOp pIn ⟨(outerIndexEquiv (.inl ℓ)).val, by omega⟩ so)) =
      ∑ ℓ : Fin 58, ∑ so : Fin 2,
        ((qOut (outerIndexEquiv (.inl ℓ)) / 2 : ℝ) : ℂ) •
          ((blockedOneBodyProjector ℓ so)ᴴ * blockedOneBodyProjector ℓ so) := by
    refine Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_congr rfl fun so _ ↦ ?_
    have hop : quantHalfSystemOp pIn ⟨(outerIndexEquiv (.inl ℓ)).val, by omega⟩ so =
        blockedOneBodyProjector ℓ so := by simp [outerIndexEquiv, quantHalfSystemOp, ℓ.isLt]
    rw [hop]
  have h2b :
      (∑ r : Fin 9, ∑ c : Fin 14, ∑ so : Fin 2,
        ((qOut (outerIndexEquiv (.inr (r, c))) / 2 : ℝ) : ℂ) •
          ((quantHalfSystemOp pIn ⟨(outerIndexEquiv (.inr (r, c))).val, by omega⟩ so)ᴴ *
            quantHalfSystemOp pIn ⟨(outerIndexEquiv (.inr (r, c))).val, by omega⟩ so)) =
      ∑ r : Fin 9, ∑ c : Fin 14,
        (qOut (outerIndexEquiv (.inr (r, c))) : ℂ) •
          ((quantBlockedFragmentLCU pIn r c)ᴴ * quantBlockedFragmentLCU pIn r c) := by
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    have hnot : ¬ (58 + 14 * r.val + c.val < 58) := by omega
    have hlt184 : 58 + 14 * r.val + c.val < 184 := by omega
    have hr' : (⟨((58 + 14 * r.val + c.val) - 58) / 14, by omega⟩ : Fin 9) = r :=
      Fin.ext (by dsimp; omega)
    have hc' : (⟨((58 + 14 * r.val + c.val) - 58) % 14, by omega⟩ : Fin 14) = c :=
      Fin.ext (by dsimp; omega)
    have hop (so : Fin 2) :
        quantHalfSystemOp pIn ⟨(outerIndexEquiv (.inr (r, c))).val, by omega⟩ so =
          quantBlockedFragmentLCU pIn r c := by
      change quantHalfSystemOp pIn ⟨58 + 14 * r.val + c.val, _⟩ so = _
      simp only [quantHalfSystemOp, hnot, hlt184, ↓reduceDIte]; rw [hr', hc']
    simp_rw [hop]; rw [Fin.sum_univ_two, ← add_smul]
    refine congrArg (· • _) ?_; push_cast; ring
  rw [h1b, h2b]
  unfold quantJointP450HBlocked
  rw [add_sub_cancel_left, smul_smul]
  have hinv : (2 * 97.3864 : ℂ)⁻¹ * ((2 * 97.3864 : ℝ) : ℂ) = 1 := by
    push_cast; exact inv_mul_cancel₀ (by norm_num)
  rw [hinv, one_smul]

/-- Active-support `PulledSOSBlockEncoding` for `quantJointP450HBlocked qOut pIn` at
`(eLB, lam) = (dfthcLowerBound, 97.3864)` under `PrepOutQuantPerm256` and `PrepMidQuant128`. -/
theorem pulledSOSBlockEncoding_ubDirectXo7Pure_quantJoint {σ : Equiv.Perm (Fin (2 ^ 8))}
    (hσ : IsZeroRcOuterPerm σ) {wOuter wInner2 : ℕ}
    {qOut : Fin 184 → ℝ} {pIn : Fin 126 → Fin 30 → ℝ}
    {prepOutPerm : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutQuantPerm256 σ qOut prepOutPerm)
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hMid : PrepMidQuant128 pIn prepMid)
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (hSelAct : ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (m : Fin (2 ^ mMidUB wInner2)),
      ((rXoLoc wOuter).extractIndex o').val < 184 →
      (prepMid ((rXo7Loc wOuter).extractIndex o')).1 m 0 ≠ 0 →
      selectPure.1 *ᵥ embedKet ψ o' m =
        embedKet ((selectBranchUnitary (σ ((rXoLoc wOuter).extractIndex o'))
          ((rSigOutLoc wOuter).extractIndex o')
          ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1 *ᵥ ψ) o' m) :
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) (quantJointP450HBlocked qOut pIn)
      dfthcLowerBound 97.3864 (ubDirectXo7PureUnitary prepOutPerm prepMid selectPure) := by
  let U_B := ubDirectXo7PureUnitary prepOutPerm prepMid selectPure
  let P_mid := (rMidUB wOuter wInner2).basisOutcomeProjector 0
  let P_in := (rAllUB wOuter wInner2).basisOutcomeProjector 0
  have hfwd (χ : Fin (2 ^ (2 * 58)) → ℂ) :
      P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0) =
        ∑ o' : Fin (2 ^ mOutUB wOuter), (prepOutPerm.1 o' 0) •
          embedKet (w_gi := wInner2) (quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o'))
            ((rSigOutLoc wOuter).extractIndex o') *ᵥ χ) o' 0 := by
    dsimp only [P_mid, U_B, ubDirectXo7PureUnitary]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val,
      embedMatrix_rOutUB_mulVec_embedKet, Matrix.mulVec_sum, Matrix.mulVec_smul]
    refine Finset.sum_congr rfl fun o' _ ↦ ?_
    by_cases hlt : ((rXoLoc wOuter).extractIndex o').val < 184
    · have h := projMid_directXo7_selectPure_eq_quantHalfSystemOp hσ hMid selectPure hSelAct
        χ o' hlt
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at h
      rw [h]
    · rw [hOut.1 o' (Nat.le_of_not_lt hlt), zero_smul, zero_smul]
  have hdot_mid (φ χ : Fin (2 ^ (2 * 58)) → ℂ) :
      dotProduct (star (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)))
        (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) χ 0 0)) =
      dotProduct (star φ)
        (((2 * 97.3864 : ℂ)⁻¹ • (quantJointP450HBlocked qOut pIn - (dfthcLowerBound : ℂ) • 1)) *ᵥ
          χ) := by
    rw [hfwd φ, hfwd χ, star_sum, sum_dotProduct]
    have hrow (o₁ : Fin (2 ^ mOutUB wOuter)) :
        dotProduct (star ((prepOutPerm.1 o₁ 0) • embedKet (w_gi := wInner2)
            (quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o₁))
              ((rSigOutLoc wOuter).extractIndex o₁) *ᵥ φ) o₁ 0))
          (∑ o₂ : Fin (2 ^ mOutUB wOuter), (prepOutPerm.1 o₂ 0) • embedKet (w_gi := wInner2)
            (quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o₂))
              ((rSigOutLoc wOuter).extractIndex o₂) *ᵥ χ) o₂ 0) =
        dotProduct (star φ)
          (((Complex.normSq (prepOutPerm.1 o₁ 0) : ℂ) •
            ((quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o₁))
                ((rSigOutLoc wOuter).extractIndex o₁))ᴴ *
              quantHalfSystemOp pIn (σ ((rXoLoc wOuter).extractIndex o₁))
                ((rSigOutLoc wOuter).extractIndex o₁))) *ᵥ χ) := by
      rw [dotProduct_sum, Finset.sum_eq_single o₁]
      · rw [star_smul, smul_dotProduct, dotProduct_smul, dotProduct_star_embedKet_ortho,
          ite_eq_left rfl, dotProduct_star_mulVec_loc, Matrix.mulVec_mulVec,
          Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc, Complex.star_def,
          mul_comm (starRingEnd ℂ (prepOutPerm.1 o₁ 0)) (prepOutPerm.1 o₁ 0),
          Complex.mul_conj]
      · intro o₂ _ ho₂
        rw [star_smul, smul_dotProduct, dotProduct_smul, dotProduct_star_embedKet_ortho,
          ite_eq_right ho₂.symm, smul_zero, smul_zero]
      · simp
    simp_rw [hrow, ← dotProduct_sum, ← Matrix.sum_mulVec, quantJoint_sos_sum_eq hσ hOut]
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
      ((hdot_norm e₁).trans (by rw [he₁, dotProduct_star_embedKet_ortho, ite_eq_left rfl,
        ← hdot_norm ψ, hnorm]))
  have hvec : (((2 * 97.3864 : ℂ)⁻¹ •
        (quantJointP450HBlocked qOut pIn - (dfthcLowerBound : ℂ) • 1)) *ᵥ ψ) =
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
      rw [hdot_norm _, hdot_norm e₁, dotProduct_star_mulVec_loc, Matrix.mulVec_mulVec, hU,
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
  refine eq_of_projAll_and_dotProduct_embedKet ?_ ?_ fun φ ↦ ?_
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
          rw [dotProduct_star_mulVec_loc,
            (rAllUB wOuter wInner2).basisOutcomeProjector_conjTranspose]
      _ = dotProduct (star (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0))
            ((P_mid * P_mid) *ᵥ (U_B.1 *ᵥ e₁)) := by
          rw [hPinφ, ← dotProduct_star_mulVec_loc U_B.1]
          dsimp only [P_mid]
          rw [(rMidUB wOuter wInner2).basisOutcomeProjector_mul_self]
      _ = dotProduct (star (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0)))
            (P_mid *ᵥ (U_B.1 *ᵥ embedKet (w_go := wOuter) (w_gi := wInner2) ψ 0 0)) := by
          rw [← Matrix.mulVec_mulVec, ← he₁]; dsimp only [P_mid]
          conv_rhs =>
            rw [dotProduct_star_mulVec_loc ((rMidUB wOuter wInner2).basisOutcomeProjector 0),
            (rMidUB wOuter wInner2).basisOutcomeProjector_conjTranspose]
      _ = dotProduct (star (embedKet (w_go := wOuter) (w_gi := wInner2) φ 0 0))
            ((((E - dfthcLowerBound) / (2 * 97.3864) : ℝ) : ℂ) • e₁) := by
          rw [hdot_mid φ ψ, hvec, he₁, ← embedKet_smul, dotProduct_star_embedKet_ortho,
            ite_eq_left rfl]

section StepQuantizedCounts

variable {Var : Type} (wOuter kZeroOut mLow sUb : ℕ) (hUb : 155 ≤ sUb) (v : Var)

end StepQuantizedCounts

section StepQuantizedClosures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 155 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))} {qOut : Fin 184 → ℝ}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)} {δOut δSelFwd δSelBwd δStep : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {outerWrap : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb) →
    DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}
  {pOutFwd pOutBwd pSelFwd pSelBwd :
    DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end StepQuantizedClosures

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30
