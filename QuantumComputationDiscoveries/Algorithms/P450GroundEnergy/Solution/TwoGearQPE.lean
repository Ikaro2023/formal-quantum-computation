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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE46687
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SineWindowPrep

/-!
# Two-Gear Schmidt-Factored Sine-Window Quantum Phase Estimation

Implements zero-extra-walk-step Two-Gear Phase Estimation (`StageA + StageB`) for `P450GroundEnergy`
when `2 ^ mLow ∣ M + 1`. By factoring the `16`-qubit Luis–Peřina half-shift sine window across the
`(16 - mLow) | mLow` cut via its exact rank-`2` trigonometric addition identity
`sin(α(x_hi) + β(x_lo)) = sin α(x_hi) cos β(x_lo) + cos α(x_hi) sin β(x_lo)`, `pWinHi` prepares only
the top `(16 - mLow) + 1` QPE wires (`rHi` plus bond wire `mLow - 1`), leaving all low `mLow - 1`
QPE wires in exact `|0⟩` throughout the `(D - 1) * 2 ^ mLow` steps of `StageA` (`99.7%` of `M` at
`mLow = 7`). Deferred low-register expansion `pWinLo` then prepares `rLo` in `0` ancillas before the
remaining `2 ^ mLow - 1` steps of `StageB`, saving `mLow - 1` persistent qubits (`6` qubits at
`mLow = 7`, `7` qubits at `mLow = 8`) with zero measurement-induced decoherence.

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen, J. J. Vartiainen, V. Bergholm, and M. M. Salomaa, *Phys. Rev. Lett.* **93**, 130502
  (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

set_option exponentiation.threshold 256

@[expose] public section

/-! ## Section 1: Pure Rational Two-Gear Error-Budget Boxes (Outside `NeZero (2 ^ k)` Scope) -/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox
open QuantumComputation.Specs QuantumComputation.Specs.P450

/-- Pure rational single-gear QPE error-budget box outside `NeZero (2 ^ k)` scope. -/
def BaseRayQuantBox (M : ℕ) (ci wUb dStep δH eUb gUb effUb kp : ℝ) : Prop :=
  46368 ≤ M ∧ M ≤ 47488 ∧ 440 / 100 ≤ gUb ∧ gUb ≤ 496 / 100 ∧
    ((M ≤ 46752 ∧ gUb ≤ 4715 / 1000 ∧ 99475 / 10 ^ 5 ≤ kp) ∨
      (M ≤ 47008 ∧ gUb ≤ 475 / 100 ∧ 99478 / 10 ^ 5 ≤ kp) ∨
      99487 / 10 ^ 5 ≤ kp) ∧
    0 ≤ δH ∧ 0 ≤ gUb ∧ 0 ≤ kp ∧ 0 ≤ effUb ∧
    eUb + 134987442 / 10 ^ 6 ≤ gUb ∧
    gUb + δH ≤ 11 ∧
    gUb * (2 * (973864 / 10000) - gUb) ≤ effUb ^ 2 ∧
    kp * (effUb / 2) * ((314159265358979323847 / 10 ^ 20) / ((M : ℝ) + 1)) + δH +
      gUb * ((ci + wUb) + (M : ℝ) * dStep) ≤ 1 / 1000

/-- Static `(M, eRef)` slice of `BaseRayQuantBox` factored across `(mode, δH)` grid points. -/
def RefStaticBox (M : ℕ) (eUb gUb effUb kp qpeUb : ℝ) : Prop :=
  46368 ≤ M ∧ M ≤ 47488 ∧ 440 / 100 ≤ gUb ∧ gUb ≤ 496 / 100 ∧
    ((M ≤ 46752 ∧ gUb ≤ 4715 / 1000 ∧ 99475 / 10 ^ 5 ≤ kp) ∨
      (M ≤ 47008 ∧ gUb ≤ 475 / 100 ∧ 99478 / 10 ^ 5 ≤ kp) ∨
      99487 / 10 ^ 5 ≤ kp) ∧
    0 ≤ gUb ∧ 0 ≤ kp ∧ 0 ≤ effUb ∧
    eUb + 134987442 / 10 ^ 6 ≤ gUb ∧
    gUb + 2 / 1000 ≤ 11 ∧
    gUb * (2 * (973864 / 10000) - gUb) ≤ effUb ^ 2 ∧
    kp * (effUb / 2) * ((314159265358979323847 / 10 ^ 20) / ((M : ℝ) + 1)) = qpeUb

theorem baseRayQuantBox_of_refStatic {M : ℕ}
    {ci wUb dStep δH eUb gUb effUb kp qpeUb : ℝ}
    (href : RefStaticBox M eUb gUb effUb kp qpeUb)
    (hdh : 0 ≤ δH ∧ δH ≤ 2 / 1000)
    (htot : qpeUb + δH + gUb * ((ci + wUb) + (M : ℝ) * dStep) ≤ 1 / 1000) :
    BaseRayQuantBox M ci wUb dStep δH eUb gUb effUb kp := by
  obtain ⟨h1, h2, h3, h4, h5, hg0, hkp0, heff0, heGap, hg11, heffSq, hqpe⟩ := href
  refine ⟨h1, h2, h3, h4, h5, hdh.1, hg0, hkp0, heff0, heGap, by linarith [hdh.2], heffSq, ?_⟩
  rw [hqpe]
  exact htot

/-- Rational CI error bound `4458 / 10 ^ 11` (`p450Fast`). -/
noncomputable abbrev cFa : ℝ := 4458 / 10 ^ 11
/-- Default rational window error bound `5 / 10 ^ 9`. -/
noncomputable abbrev w5 : ℝ := 5 / 10 ^ 9
/-- Rational step-error scale `n / 10 ^ 15`. -/
noncomputable abbrev d15 (n : ℝ) : ℝ := n / 10 ^ 15
/-- Namespace shadow stub `m0` for `hiding` compatibility. -/
abbrev m0 : ℕ := 0
/-- Namespace shadow stub `m1` for `hiding` compatibility. -/
abbrev m1 : ℕ := 0
/-- Namespace shadow stub `m2` for `hiding` compatibility. -/
abbrev m2 : ℕ := 0
/-- Namespace shadow stub `m3` for `hiding` compatibility. -/
abbrev m3 : ℕ := 0
/-- Namespace shadow stub `m4` for `hiding` compatibility. -/
abbrev m4 : ℕ := 0
/-- Namespace shadow stub `m5` for `hiding` compatibility. -/
abbrev m5 : ℕ := 0
/-- Namespace shadow stub `m6` for `hiding` compatibility. -/
abbrev m6 : ℕ := 0
/-- Namespace shadow stub `m7` for `hiding` compatibility. -/
abbrev m7 : ℕ := 0
/-- Namespace shadow stub `m8` for `hiding` compatibility. -/
abbrev m8 : ℕ := 0
/-- Namespace shadow stub `m9` for `hiding` compatibility. -/
abbrev m9 : ℕ := 0
/-- Namespace shadow stub `m10` for `hiding` compatibility. -/
abbrev m10 : ℕ := 0
/-- Namespace shadow stub `m11` for `hiding` compatibility. -/
abbrev m11 : ℕ := 0
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Swar192
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open OuterWeights.SineWindowPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.PhaseSwar
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNe2_192 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Primitive eighth root of unity `ω₈ = (1 + i) / √2`. -/
noncomputable def omega8_192 : ℂ :=
  (⟨.ofNat 0, .ofNat 1, .ofNat 0, .ofNat 0⟩ : OuterWeights.SineWindowPrep.Cyc8).toComplex

/-- Complex `2 × 2` matrix semantics of `FastSU2`. -/
noncomputable def toMatrix192 (st : FastSU2) : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := (1 / (√2 : ℂ)) ^ st.k
  let α : ℂ := s * st.a.toComplex
  let γ : ℂ := s * st.c.toComplex
  let φ : ℂ := omega8_192 ^ st.p
  !![α, -φ * star γ; γ, φ * star α]

theorem omega8_192_re : omega8_192.re = 1 / √2 := by
  simp [omega8_192, Cyc8.toComplex, SInt.toReal_ofNat]

theorem omega8_192_im : omega8_192.im = 1 / √2 := by
  simp [omega8_192, Cyc8.toComplex, SInt.toReal_ofNat]

theorem star_inv_sqrt2_192 : star (1 / (√2 : ℂ)) = 1 / (√2 : ℂ) := by
  simp only [one_div, star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem cyc8_mulI_toComplex_192 (c : OuterWeights.SineWindowPrep.Cyc8) :
    c.mulI.toComplex = Complex.I * c.toComplex := by
  apply Complex.ext <;> simp [Cyc8.mulI, Cyc8.toComplex,
    OuterWeights.SineWindowPrep.SInt.toReal_opp] <;> ring

theorem cyc8_mulOmega_toComplex_192 (c : OuterWeights.SineWindowPrep.Cyc8) :
    c.mulOmega.toComplex = omega8_192 * c.toComplex := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp only [Cyc8.mulOmega, Cyc8.toComplex,
      OuterWeights.SineWindowPrep.SInt.toReal_opp, Complex.mul_re, omega8_192_re, omega8_192_im]
    field_simp [hs2_ne]; ring_nf; rw [hs2_sq]; ring
  · simp only [Cyc8.mulOmega, Cyc8.toComplex,
      OuterWeights.SineWindowPrep.SInt.toReal_opp, Complex.mul_im, omega8_192_re, omega8_192_im]
    field_simp [hs2_ne]; ring_nf; rw [hs2_sq]; ring

theorem omega8_192_sq : omega8_192 ^ 2 = Complex.I := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [sq]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.I_re, omega8_192_re, omega8_192_im]
    ring
  · simp only [Complex.mul_im, Complex.I_im, omega8_192_re, omega8_192_im]
    field_simp [hs2_ne]; ring_nf; rw [hs2_sq]

theorem omega8_192_pow_four : omega8_192 ^ 4 = -1 := by
  calc omega8_192 ^ 4 = (omega8_192 ^ 2) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [omega8_192_sq]
    _ = -1 := Complex.I_sq

theorem omega8_192_pow_eight : omega8_192 ^ 8 = 1 := by
  calc omega8_192 ^ 8 = (omega8_192 ^ 4) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [omega8_192_pow_four]
    _ = 1 := by ring

theorem omega8_192_pow_mod (n : ℕ) : omega8_192 ^ (n % 8) = omega8_192 ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 8]
  rw [pow_add, pow_mul, omega8_192_pow_eight, one_pow, mul_one]

theorem omega8_192_mul_star : omega8_192 * star omega8_192 = 1 := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.one_re,
      omega8_192_re, omega8_192_im]
    field_simp [hs2_ne]; ring_nf; rw [hs2_sq]
  · simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.one_im,
      omega8_192_re, omega8_192_im]
    ring

theorem smul_mat2_mul_192 (s : ℂ) (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : ℂ) :
    (s • !![a₁₁, a₁₂; a₂₁, a₂₂] : Matrix (Fin 2) (Fin 2) ℂ) * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![s * (a₁₁ * b₁₁ + a₁₂ * b₂₁), s * (a₁₁ * b₁₂ + a₁₂ * b₂₂);
         s * (a₂₁ * b₁₁ + a₂₂ * b₂₁), s * (a₂₁ * b₁₂ + a₂₂ * b₂₂)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;> ring

theorem mat2_eq_192 {a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : ℂ}
    (h₁₁ : a₁₁ = b₁₁) (h₁₂ : a₁₂ = b₁₂) (h₂₁ : a₂₁ = b₂₁) (h₂₂ : a₂₂ = b₂₂) :
    (!![a₁₁, a₁₂; a₂₁, a₂₂] : Matrix (Fin 2) (Fin 2) ℂ) = !![b₁₁, b₁₂; b₂₁, b₂₂] := by
  subst h₁₁ h₁₂ h₂₁ h₂₂; rfl

theorem stepGateSU2_X_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepGateSU2 .X ⟨k, p, a, c, t⟩ = ⟨k, (p + 4) % 8, c, a, t⟩ := by
  dsimp only [stepGateSU2]; rw [OuterWeights.SineWindowPrep.withForcedNat_eq]; rfl

theorem stepGateSU2_Z_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepGateSU2 .Z ⟨k, p, a, c, t⟩ = ⟨k, (p + 4) % 8, a, c.opp, t⟩ := by
  dsimp only [stepGateSU2]
  rcases h : c.oppStrict with ⟨c0, c1, c2, c3⟩
  rw [OuterWeights.SineWindowPrep.withForcedNat_eq]
  have ho : (⟨c0, c1, c2, c3⟩ : Cyc8) = c.opp := h.symm.trans c.oppStrict_eq
  rw [ho]; rfl

theorem stepGateSU2_S_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepGateSU2 .S ⟨k, p, a, c, t⟩ = ⟨k, (p + 2) % 8, a, c.mulI, t⟩ := by
  dsimp only [stepGateSU2]
  rcases h : c.mulIStrict with ⟨c0, c1, c2, c3⟩
  rw [OuterWeights.SineWindowPrep.withForcedNat_eq]
  have ho : (⟨c0, c1, c2, c3⟩ : Cyc8) = c.mulI := h.symm.trans c.mulIStrict_eq
  rw [ho]; rfl

theorem stepGateSU2_T_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepGateSU2 .T ⟨k, p, a, c, t⟩ = ⟨k, (p + 1) % 8, a, c.mulOmega, t + 1⟩ := by
  dsimp only [stepGateSU2]
  rcases h : c.mulOmegaStrict with ⟨c0, c1, c2, c3⟩
  simp only [OuterWeights.SineWindowPrep.withForcedNat_eq]
  have ho : (⟨c0, c1, c2, c3⟩ : OuterWeights.SineWindowPrep.Cyc8) = c.mulOmega :=
    h.symm.trans c.mulOmegaStrict_eq
  rw [ho]; rfl

theorem stepGateSU2_H_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepGateSU2 .H ⟨k, p, a, c, t⟩ = ⟨k + 1, (p + 4) % 8, a.add c, a.sub c, t⟩ := by
  dsimp only [stepGateSU2]
  rcases ha : a.addStrict c with ⟨a0, a1, a2, a3⟩
  rcases hc : a.subStrict c with ⟨c0, c1, c2, c3⟩
  simp only [OuterWeights.SineWindowPrep.withForcedNat_eq]
  have hoa : (⟨a0, a1, a2, a3⟩ : OuterWeights.SineWindowPrep.Cyc8) = a.add c :=
    ha.symm.trans (a.addStrict_eq c)
  have hoc : (⟨c0, c1, c2, c3⟩ : OuterWeights.SineWindowPrep.Cyc8) = a.sub c :=
    hc.symm.trans (a.subStrict_eq c)
  rw [hoa, hoc]; rfl

theorem stepGateSU2_spec_192 (g : OuterWeights.SineWindowPrep.Gate1) (st : FastSU2) :
    toMatrix192 (stepGateSU2 g st) = g.toCircuit1.eval.1 * toMatrix192 st ∧
      (stepGateSU2 g st).tCnt = st.tCnt + g.toCircuit1.count .T := by
  rcases st with ⟨k, p, a, c, t⟩
  rw [← g.toCycMat2_toMatrix]
  cases g with
  | X =>
    have htc : OuterWeights.SineWindowPrep.Gate1.X.toCircuit1.count .T = 0 := by decide
    rw [stepGateSU2_X_192, htc, Nat.add_zero]
    refine ⟨?_, rfl⟩
    dsimp only [toMatrix192, OuterWeights.SineWindowPrep.Gate1.toCycMat2,
      OuterWeights.SineWindowPrep.CycMat2.toMatrix]
    rw [smul_mat2_mul_192, omega8_192_pow_mod, pow_add, omega8_192_pow_four,
      Cyc8.toComplex_zero, Cyc8.toComplex_one, pow_zero]
    exact mat2_eq_192 (by ring) (by ring) (by ring) (by ring)
  | Z =>
    have htc : OuterWeights.SineWindowPrep.Gate1.Z.toCircuit1.count .T = 0 := by decide
    rw [stepGateSU2_Z_192, htc, Nat.add_zero]
    refine ⟨?_, rfl⟩
    dsimp only [toMatrix192, OuterWeights.SineWindowPrep.Gate1.toCycMat2,
      OuterWeights.SineWindowPrep.CycMat2.toMatrix]
    rw [smul_mat2_mul_192, omega8_192_pow_mod, pow_add, omega8_192_pow_four,
      Cyc8.toComplex_opp, Cyc8.toComplex_zero,
      Cyc8.toComplex_one, Cyc8.toComplex_negOne, pow_zero]
    simp only [mul_neg, star_neg]
    exact mat2_eq_192 (by ring) (by ring) (by ring) (by ring)
  | S =>
    have hi : (⟨.ofNat 0, .ofNat 0, .ofNat 1, .ofNat 0⟩ : Cyc8).toComplex =
        Complex.I := by
      apply Complex.ext <;> simp [OuterWeights.SineWindowPrep.Cyc8.toComplex,
        OuterWeights.SineWindowPrep.SInt.toReal_ofNat]
    have htc : OuterWeights.SineWindowPrep.Gate1.S.toCircuit1.count .T = 0 := by decide
    rw [stepGateSU2_S_192, htc, Nat.add_zero]
    refine ⟨?_, rfl⟩
    dsimp only [toMatrix192, OuterWeights.SineWindowPrep.Gate1.toCycMat2,
      OuterWeights.SineWindowPrep.CycMat2.toMatrix]
    rw [smul_mat2_mul_192, omega8_192_pow_mod, pow_add, omega8_192_sq, cyc8_mulI_toComplex_192, hi,
      Cyc8.toComplex_zero, Cyc8.toComplex_one, pow_zero]
    refine mat2_eq_192 (by ring) ?_ (by ring) (by ring)
    simp only [star_mul', Complex.star_def, Complex.conj_I]
    ring_nf; rw [Complex.I_sq]; ring
  | T =>
    have htc : OuterWeights.SineWindowPrep.Gate1.T.toCircuit1.count .T = 1 := by decide
    rw [stepGateSU2_T_192, htc]
    refine ⟨?_, rfl⟩
    dsimp only [toMatrix192, OuterWeights.SineWindowPrep.Gate1.toCycMat2,
      OuterWeights.SineWindowPrep.CycMat2.toMatrix]
    have hom : (⟨.ofNat 0, .ofNat 1, .ofNat 0, .ofNat 0⟩ : Cyc8).toComplex =
        omega8_192 := rfl
    rw [smul_mat2_mul_192, omega8_192_pow_mod, pow_add, pow_one, cyc8_mulOmega_toComplex_192, hom,
      Cyc8.toComplex_zero, Cyc8.toComplex_one, pow_zero]
    refine mat2_eq_192 (by ring) ?_ (by ring) (by ring)
    simp only [star_mul']
    linear_combination (-(omega8_192 ^ p) * star ((1 / (√2 : ℂ)) ^ k) * star c.toComplex) *
      omega8_192_mul_star
  | H =>
    have htc : OuterWeights.SineWindowPrep.Gate1.H.toCircuit1.count .T = 0 := by decide
    rw [stepGateSU2_H_192, htc, Nat.add_zero]
    refine ⟨?_, rfl⟩
    dsimp only [toMatrix192, OuterWeights.SineWindowPrep.Gate1.toCycMat2,
      OuterWeights.SineWindowPrep.CycMat2.toMatrix]
    rw [smul_mat2_mul_192, omega8_192_pow_mod, pow_add omega8_192 p 4, omega8_192_pow_four,
      pow_succ, pow_one, OuterWeights.SineWindowPrep.Cyc8.toComplex_add,
      Cyc8.toComplex_sub, Cyc8.toComplex_one,
      OuterWeights.SineWindowPrep.Cyc8.toComplex_negOne]
    refine mat2_eq_192 (by ring) ?_ (by ring) ?_ <;>
      (simp only [star_mul', star_add, star_sub, star_inv_sqrt2_192]; ring)

theorem foldl_stepGateSU2_spec_192 (w : List OuterWeights.SineWindowPrep.Gate1) (st : FastSU2) :
    toMatrix192 (w.foldl (fun acc g ↦ stepGateSU2 g acc) st) =
      (OuterWeights.SineWindowPrep.wordToCircuit1 w).eval.1 * toMatrix192 st ∧
    (w.foldl (fun acc g ↦ stepGateSU2 g acc) st).tCnt =
      st.tCnt + (OuterWeights.SineWindowPrep.wordToCircuit1 w).count .T := by
  induction w generalizing st with
  | nil => simp [OuterWeights.SineWindowPrep.wordToCircuit1]
  | cons g gs ih =>
    simp only [List.foldl_cons, OuterWeights.SineWindowPrep.wordToCircuit1, Circuit.eval_seq,
      Submonoid.coe_mul, Circuit.count_seq]
    obtain ⟨hm, ht⟩ := stepGateSU2_spec_192 g st
    obtain ⟨ihm, iht⟩ := ih (stepGateSU2 g st)
    exact ⟨by rw [ihm, hm, Matrix.mul_assoc], by omega⟩

theorem fastSU2_toMatrix_congr_192 {k p₁ p₂ : ℕ} {a₁ a₂ c₁ c₂ : OuterWeights.SineWindowPrep.Cyc8}
    {t₁ t₂ : ℕ} (hp : p₁ = p₂) (ha : a₁.toComplex = a₂.toComplex)
    (hc : c₁.toComplex = c₂.toComplex) :
    toMatrix192 ⟨k, p₁, a₁, c₁, t₁⟩ = toMatrix192 ⟨k, p₂, a₂, c₂, t₂⟩ := by
  dsimp only [toMatrix192]
  rw [hp, ha, hc]

theorem stepZSTZH_unfold_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepZSTZH ⟨k, p, a, c, t⟩ =
      ⟨k + 1, (p + 7) % 8, a.add c.mulOmega.mulI, a.sub c.mulOmega.mulI, t + 1⟩ := by
  dsimp only [stepZSTZH]
  rcases hw : c.mulOmegaStrict with ⟨w0, w1, w2, w3⟩
  dsimp only
  rcases hm : (OuterWeights.SineWindowPrep.Cyc8.mk w0 w1 w2 w3).mulIStrict with ⟨m0, m1, m2, m3⟩
  dsimp only
  rcases ha : a.addStrict ⟨m0, m1, m2, m3⟩ with ⟨a0, a1, a2, a3⟩
  rcases hc : a.subStrict ⟨m0, m1, m2, m3⟩ with ⟨c0, c1, c2, c3⟩
  dsimp only
  simp only [OuterWeights.SineWindowPrep.withForcedNat_eq]
  have hwo : (⟨w0, w1, w2, w3⟩ : OuterWeights.SineWindowPrep.Cyc8) = c.mulOmega :=
    hw.symm.trans c.mulOmegaStrict_eq
  have hmo : (⟨m0, m1, m2, m3⟩ : OuterWeights.SineWindowPrep.Cyc8) = c.mulOmega.mulI := by
    have h1 := hm.symm.trans (OuterWeights.SineWindowPrep.Cyc8.mk w0 w1 w2 w3).mulIStrict_eq
    rw [hwo] at h1
    exact h1
  have hoa : (⟨a0, a1, a2, a3⟩ : OuterWeights.SineWindowPrep.Cyc8) = a.add c.mulOmega.mulI := by
    have h1 := ha.symm.trans (a.addStrict_eq ⟨m0, m1, m2, m3⟩)
    rw [hmo] at h1
    exact h1
  have hoc : (⟨c0, c1, c2, c3⟩ : OuterWeights.SineWindowPrep.Cyc8) = a.sub c.mulOmega.mulI := by
    have h1 := hc.symm.trans (a.subStrict_eq ⟨m0, m1, m2, m3⟩)
    rw [hmo] at h1
    exact h1
  rw [hoa, hoc]; rfl

theorem stepZSTSH_unfold_192 (k p : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    stepZSTSH ⟨k, p, a, c, t⟩ =
      ⟨k + 1, (p + 5) % 8, a.add c.mulOmega, a.sub c.mulOmega, t + 1⟩ := by
  dsimp only [stepZSTSH]
  rcases hm : c.mulOmegaStrict with ⟨m0, m1, m2, m3⟩
  dsimp only
  rcases ha : a.addStrict ⟨m0, m1, m2, m3⟩ with ⟨a0, a1, a2, a3⟩
  rcases hc : a.subStrict ⟨m0, m1, m2, m3⟩ with ⟨c0, c1, c2, c3⟩
  dsimp only
  simp only [OuterWeights.SineWindowPrep.withForcedNat_eq]
  have hmo : (⟨m0, m1, m2, m3⟩ : OuterWeights.SineWindowPrep.Cyc8) = c.mulOmega :=
    hm.symm.trans c.mulOmegaStrict_eq
  have hoa : (⟨a0, a1, a2, a3⟩ : OuterWeights.SineWindowPrep.Cyc8) = a.add c.mulOmega := by
    have h1 := ha.symm.trans (a.addStrict_eq ⟨m0, m1, m2, m3⟩)
    rw [hmo] at h1
    exact h1
  have hoc : (⟨c0, c1, c2, c3⟩ : OuterWeights.SineWindowPrep.Cyc8) = a.sub c.mulOmega := by
    have h1 := hc.symm.trans (a.subStrict_eq ⟨m0, m1, m2, m3⟩)
    rw [hmo] at h1
    exact h1
  rw [hoa, hoc]; rfl

theorem stepZSTZH_equiv_192 (st : FastSU2) :
    toMatrix192 (stepZSTZH st) =
      toMatrix192 (([.Z, .S, .T, .Z, .H] : List OuterWeights.SineWindowPrep.Gate1).foldl
        (fun acc g ↦ stepGateSU2 g acc) st) ∧
    (stepZSTZH st).tCnt =
      (([.Z, .S, .T, .Z, .H] : List OuterWeights.SineWindowPrep.Gate1).foldl
        (fun acc g ↦ stepGateSU2 g acc) st).tCnt := by
  rcases st with ⟨k, p, a, c, t⟩
  dsimp only [List.foldl]
  simp only [stepZSTZH_unfold_192, stepGateSU2_Z_192, stepGateSU2_S_192, stepGateSU2_T_192,
    stepGateSU2_H_192]
  have hcw : c.mulOmega.mulI.toComplex = c.opp.mulI.mulOmega.opp.toComplex := by
    rw [cyc8_mulI_toComplex_192, cyc8_mulOmega_toComplex_192, Cyc8.toComplex_opp,
      cyc8_mulOmega_toComplex_192, cyc8_mulI_toComplex_192, Cyc8.toComplex_opp]
    ring
  refine ⟨fastSU2_toMatrix_congr_192 (by omega) ?_ ?_, trivial⟩
  · rw [Cyc8.toComplex_add, Cyc8.toComplex_add, hcw]
  · rw [Cyc8.toComplex_sub, Cyc8.toComplex_sub, hcw]

theorem stepZSTSH_equiv_192 (st : FastSU2) :
    toMatrix192 (stepZSTSH st) =
      toMatrix192 (([.Z, .S, .T, .S, .H] : List OuterWeights.SineWindowPrep.Gate1).foldl
        (fun acc g ↦ stepGateSU2 g acc) st) ∧
    (stepZSTSH st).tCnt =
      (([.Z, .S, .T, .S, .H] : List OuterWeights.SineWindowPrep.Gate1).foldl
        (fun acc g ↦ stepGateSU2 g acc) st).tCnt := by
  rcases st with ⟨k, p, a, c, t⟩
  dsimp only [List.foldl]
  simp only [stepZSTSH_unfold_192, stepGateSU2_Z_192, stepGateSU2_S_192, stepGateSU2_T_192,
    stepGateSU2_H_192]
  have hcw : c.mulOmega.toComplex = c.opp.mulI.mulOmega.mulI.toComplex := by
    rw [cyc8_mulOmega_toComplex_192, cyc8_mulI_toComplex_192, cyc8_mulOmega_toComplex_192,
      cyc8_mulI_toComplex_192, OuterWeights.SineWindowPrep.Cyc8.toComplex_opp]
    calc omega8_192 * c.toComplex
        = -(Complex.I ^ 2) * (omega8_192 * c.toComplex) := by rw [Complex.I_sq]; ring
      _ = Complex.I * (omega8_192 * (Complex.I * -c.toComplex)) := by ring
  refine ⟨fastSU2_toMatrix_congr_192 (by omega) ?_ ?_, trivial⟩
  · rw [Cyc8.toComplex_add, Cyc8.toComplex_add, hcw]
  · rw [Cyc8.toComplex_sub, Cyc8.toComplex_sub, hcw]

theorem stepCodeSU2_equiv_192 (d : ℕ) (st : FastSU2) :
    toMatrix192 (stepCodeSU2 d st) =
      toMatrix192 ((decodeSyl1 d).foldl (fun acc g ↦ stepGateSU2 g acc) st) ∧
    (stepCodeSU2 d st).tCnt =
      ((decodeSyl1 d).foldl (fun acc g ↦ stepGateSU2 g acc) st).tCnt := by
  match d with
  | 0 => exact ⟨rfl, rfl⟩
  | 1 => exact stepZSTZH_equiv_192 st
  | 2 => exact stepZSTSH_equiv_192 st
  | 3 => exact ⟨rfl, rfl⟩
  | 4 => exact ⟨rfl, rfl⟩
  | 5 => exact ⟨rfl, rfl⟩
  | 6 => exact ⟨rfl, rfl⟩
  | 7 => exact ⟨rfl, rfl⟩
  | _ + 8 => exact ⟨rfl, rfl⟩

theorem foldl_stepGateSU2_congr_192 (w : List OuterWeights.SineWindowPrep.Gate1) {st₁ st₂ : FastSU2}
    (h : toMatrix192 st₁ = toMatrix192 st₂ ∧ st₁.tCnt = st₂.tCnt) :
    toMatrix192 (w.foldl (fun acc g ↦ stepGateSU2 g acc) st₁) =
      toMatrix192 (w.foldl (fun acc g ↦ stepGateSU2 g acc) st₂) ∧
    (w.foldl (fun acc g ↦ stepGateSU2 g acc) st₁).tCnt =
      (w.foldl (fun acc g ↦ stepGateSU2 g acc) st₂).tCnt := by
  obtain ⟨hm₁, ht₁⟩ := foldl_stepGateSU2_spec_192 w st₁
  obtain ⟨hm₂, ht₂⟩ := foldl_stepGateSU2_spec_192 w st₂
  exact ⟨by rw [hm₁, hm₂, h.1], by rw [ht₁, ht₂, h.2]⟩

theorem evalChunkAux_equiv_192 (n code : ℕ) (st : FastSU2) :
    toMatrix192 (evalChunkAux n code st) =
      toMatrix192 ((decodeChunkAux n code).foldl (fun acc g ↦ stepGateSU2 g acc) st) ∧
    (evalChunkAux n code st).tCnt =
      ((decodeChunkAux n code).foldl (fun acc g ↦ stepGateSU2 g acc) st).tCnt := by
  induction n generalizing code st with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    unfold evalChunkAux decodeChunkAux
    dsimp only
    split_ifs with h0
    · exact ⟨rfl, rfl⟩
    · rw [List.foldl_append]
      obtain ⟨hm1, ht1⟩ := ih (Nat.div code 8) (stepCodeSU2 (Nat.mod code 8) st)
      obtain ⟨hm2, ht2⟩ := foldl_stepGateSU2_congr_192 (decodeChunkAux m (Nat.div code 8))
        (stepCodeSU2_equiv_192 (Nat.mod code 8) st)
      exact ⟨hm1.trans hm2, ht1.trans ht2⟩

theorem evalChunksSU2_equiv_192 (chs : List ℕ) (st : FastSU2) :
    toMatrix192 (evalChunksSU2 chs st) =
      toMatrix192 ((decodeChunks chs).foldl (fun acc g ↦ stepGateSU2 g acc) st) ∧
    (evalChunksSU2 chs st).tCnt =
      ((decodeChunks chs).foldl (fun acc g ↦ stepGateSU2 g acc) st).tCnt := by
  induction chs generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons ch rest ih =>
    dsimp only [evalChunksSU2, decodeChunks]
    rw [List.foldl_append]
    obtain ⟨hm1, ht1⟩ := ih (evalChunkAux (4 * 5) ch st)
    obtain ⟨hm2, ht2⟩ :=
      foldl_stepGateSU2_congr_192 (decodeChunks rest) (evalChunkAux_equiv_192 (4 * 5) ch st)
    exact ⟨hm1.trans hm2, ht1.trans ht2⟩

theorem fastSU2_init_toMatrix_192 : toMatrix192 FastSU2.init = 1 := by
  have h01 : ((0 : Fin 2) = 1) = False := by decide
  have h10 : ((1 : Fin 2) = 0) = False := by decide
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [toMatrix192, FastSU2.init, OuterWeights.SineWindowPrep.Cyc8.toComplex_one,
      Cyc8.toComplex_zero, pow_zero, one_mul, mul_zero, star_zero, star_one,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.one_apply, Fin.zero_eta, Fin.mk_one, h01, h10, ite_true, ite_false]

theorem fastSU2_p0_eq_su2Matrix_192 (k : ℕ) (a c : OuterWeights.SineWindowPrep.Cyc8) (t : ℕ) :
    toMatrix192 ⟨k, 0, a, c, t⟩ =
      SineQPE.su2Matrix ((1 / (√2 : ℂ)) ^ k * a.toComplex)
        ((1 / (√2 : ℂ)) ^ k * c.toComplex) := by
  dsimp only [toMatrix192, SineQPE.su2Matrix]
  exact mat2_eq_192 rfl (by rw [pow_zero]; ring) rfl (by rw [pow_zero, one_mul])

/-- `192`-bit limb radix `2 ^ 192` (`3` GMP 64-bit limbs). -/
def swarW192 : ℕ := 0x1000000000000000000000000000000000000000000000000

/-- Two-lane radix `2 ^ 384` (`6` GMP 64-bit limbs). -/
def swarW192_2 : ℕ :=
 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/-- Three-lane radix `2 ^ 576` (`9` GMP 64-bit limbs). -/
def swarW192_3 : ℕ := Nat.mul swarW192 swarW192_2

/-- Four-lane unit bias mask `1 + W + W ^ 2 + W ^ 3` for `192`-bit lanes. -/
def swarOnes192 : ℕ :=
  Nat.add 1 (Nat.add swarW192 (Nat.add swarW192_2 swarW192_3))

/-- Packed `4 × 192`-bit limb-aligned SWAR state for `SU(2)` Clifford+`T` words (`k ≤ 180`). -/
structure SWARState192 where
  /-- Denominator exponent `(1 / √2) ^ k`. -/
  k : ℕ
  /-- Unreduced determinant phase accumulator `p` (`det = ω₈ ^ (p % 8)`). -/
  p : ℕ
  /-- Packed bias `2 ^ k * swarOnes192`. -/
  bPack : ℕ
  /-- Biased packed `(0, 0)` cyclotomic coordinate. -/
  aPack : ℕ
  /-- Biased packed `(1, 0)` cyclotomic coordinate. -/
  cPack : ℕ
  /-- Accumulated `.T` gate count. -/
  t : ℕ

/-- Multiply `192`-bit packed cyclotomic lane word by `ω₈` (`1`-lane rotate). -/
@[inline] def rot1SWAR192 (B2 X : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub B2 X) swarW192_3) (Nat.mul (Nat.mod X swarW192_3) swarW192)

/-- Multiply `192`-bit packed cyclotomic lane word by `i = ω₈ ^ 2` (`2`-lane rotate). -/
@[inline] def rot2SWAR192 (B2 X : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub B2 X) swarW192_2) (Nat.mul (Nat.mod X swarW192_2) swarW192_2)

/-- Multiply `192`-bit packed cyclotomic lane word by `i * ω₈ = ω₈ ^ 3` (`3`-lane rotate). -/
@[inline] def rot3SWAR192 (B2 X : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub B2 X) swarW192) (Nat.mul (Nat.mod X swarW192) swarW192_3)

/-- Select `rot3SWAR192` (`d = 1`, `ZSTZH`) or `rot1SWAR192` (`d = 2`, `ZSTSH`). -/
@[inline] def rot12SWAR192 (d B2 X : ℕ) : ℕ :=
  Bool.casesOn (Nat.beq d 1) (rot1SWAR192 B2 X) (rot3SWAR192 B2 X)

/-- Fused 64-bit limb-aligned `192`-bit SWAR step for `d ∈ {1, 2}` (`ZSTZH` / `ZSTSH`). -/
def stepFast12SWAR192 (d : ℕ) (st : SWARState192) : SWARState192 :=
  SWARState192.casesOn st fun k p B A C t =>
  withForcedNat (Nat.add k 1) fun k1 =>
  withForcedNat (Nat.add p (Bool.casesOn (Nat.beq d 1) 5 7)) fun p1 =>
  withForcedNat (Nat.add B B) fun B2 =>
  withForcedNat (rot12SWAR192 d B2 C) fun cw =>
  withForcedNat (Nat.add A cw) fun nA =>
  withForcedNat (Nat.add A (Nat.sub B2 cw)) fun nC =>
  withForcedNat (Nat.add t 1) fun t1 =>
  ⟨k1, p1, B2, nA, nC, t1⟩

/-- Single base-`8` syllable step on `SWARState192`. -/
def step1SWAR192 (d : ℕ) (st : SWARState192) : SWARState192 :=
  SWARState192.casesOn st fun k p B A C t =>
  Bool.casesOn (Nat.ble d 2)
    (Bool.casesOn (Nat.ble d 4)
      (Bool.casesOn (Nat.beq d 5)
        (Bool.casesOn (Nat.beq d 6)
          (Bool.casesOn (Nat.beq d 7)
            ⟨k, p, B, A, C, t⟩
            (withForcedNat (Nat.sub (Nat.add B B) C) fun nC => ⟨k, Nat.add p 4, B, A, nC, t⟩))
          ⟨k, Nat.add p 4, B, C, A, t⟩)
        (let B2 := Nat.add B B
         withForcedNat (rot1SWAR192 B2 C) fun nC => ⟨k, Nat.add p 1, B, A, nC, Nat.add t 1⟩))
      (Bool.casesOn (Nat.beq d 3)
        (let B2 := Nat.add B B
         withForcedNat (rot2SWAR192 B2 C) fun nC => ⟨k, Nat.add p 2, B, A, nC, t⟩)
        (withForcedNat (Nat.add B B) fun B2 =>
         withForcedNat (Nat.add A C) fun nA =>
         withForcedNat (Nat.add A (Nat.sub B2 C)) fun nC =>
         ⟨Nat.add k 1, Nat.add p 4, B2, nA, nC, t⟩)))
    (Bool.casesOn (Nat.beq d 0)
      (stepFast12SWAR192 d ⟨k, p, B, A, C, t⟩)
      ⟨k, p, B, A, C, t⟩)

/-- Fallback 4-syllable `192`-bit SWAR evaluator handling stop digits (`0`) and Cliffords. -/
def evalSlow4SWAR192 (d0 d1 d2 d3 : ℕ) (st : SWARState192) : Bool × SWARState192 :=
  Bool.casesOn (Nat.beq d0 0)
    (let s1 := step1SWAR192 d0 st
     Bool.casesOn (Nat.beq d1 0)
       (let s2 := step1SWAR192 d1 s1
        Bool.casesOn (Nat.beq d2 0)
          (let s3 := step1SWAR192 d2 s2
           Bool.casesOn (Nat.beq d3 0)
             (true, step1SWAR192 d3 s3)
             (false, s3))
          (false, s2))
       (false, s1))
    (false, st)

/-- Unrolled `4`-syllable-per-step `192`-bit SWAR chunk evaluator (`5` steps = `20` syllables). -/
def evalChunk4SWAR192 : ℕ → ℕ → SWARState192 → SWARState192
  | 0, _, st => st
  | m + 1, code, st =>
    let d0 := Nat.mod code 8; let q0 := Nat.div code 8
    let d1 := Nat.mod q0 8;   let q1 := Nat.div q0 8
    let d2 := Nat.mod q1 8;   let q2 := Nat.div q1 8
    let d3 := Nat.mod q2 8;   let q3 := Nat.div q2 8
    Bool.casesOn (is12SWAR d0 && is12SWAR d1 && is12SWAR d2 && is12SWAR d3)
      (Prod.casesOn (evalSlow4SWAR192 d0 d1 d2 d3 st) fun cont st' =>
        Bool.casesOn cont st' (evalChunk4SWAR192 m q3 st'))
      (evalChunk4SWAR192 m q3
        (stepFast12SWAR192 d3 (stepFast12SWAR192 d2
          (stepFast12SWAR192 d1 (stepFast12SWAR192 d0 st)))))

/-- Evaluate a list of `20`-syllable base-`8` chunks on `SWARState192`. -/
def evalChunksSWAR192 : List ℕ → SWARState192 → SWARState192
  | [], st => st
  | ch :: chs, st => evalChunksSWAR192 chs (evalChunk4SWAR192 5 ch st)

/-- Identity `SU(2)` state in `SWARState192`. -/
def swarInit192 : SWARState192 := ⟨0, 0, swarOnes192, Nat.add swarOnes192 1, swarOnes192, 0⟩

/-- Unpack four `192`-bit lanes of `X` in CPS with forced `Nat` evaluation. -/
def withUnpack4SWAR192 {α : Type} (X : ℕ) (f : ℕ → ℕ → ℕ → ℕ → α) : α :=
  withForcedNat (Nat.mod X swarW192) fun x0 =>
  withForcedNat (Nat.div X swarW192) fun q1 =>
  withForcedNat (Nat.mod q1 swarW192) fun x1 =>
  withForcedNat (Nat.div q1 swarW192) fun q2 =>
  withForcedNat (Nat.mod q2 swarW192) fun x2 =>
  withForcedNat (Nat.div q2 swarW192) fun x3 =>
    f x0 x1 x2 x3

/-- Unpack four `192`-bit lanes using pre-forced radix `w1`. -/
def withUnpack4Fast {α : Type} (w1 X : ℕ) (f : ℕ → ℕ → ℕ → ℕ → α) : α :=
  withForcedNat (Nat.mod X w1) fun x0 =>
  withForcedNat (Nat.div X w1) fun q1 =>
  withForcedNat (Nat.mod q1 w1) fun x1 =>
  withForcedNat (Nat.div q1 w1) fun q2 =>
  withForcedNat (Nat.mod q2 w1) fun x2 =>
  withForcedNat (Nat.div q2 w1) fun x3 =>
    f x0 x1 x2 x3

/-- `1`-lane SWAR rotate with pre-forced radices `w1, w3`. -/
@[inline] def rot1Fast (w1 w3 B2 X : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub B2 X) w3) (Nat.mul (Nat.mod X w3) w1)

/-- `2`-lane SWAR rotate with pre-forced radix `w2`. -/
@[inline] def rot2Fast (w2 B2 X : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub B2 X) w2) (Nat.mul (Nat.mod X w2) w2)

/-- `3`-lane SWAR rotate with pre-forced radices `w1, w3`. -/
@[inline] def rot3Fast (w1 w3 B2 X : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub B2 X) w1) (Nat.mul (Nat.mod X w1) w3)

/-- Select `rot3Fast` (`d = 1`) or `rot1Fast` (`d = 2`) with pre-forced radices `w1, w3`. -/
@[inline] def rot12Fast (w1 w3 d B2 X : ℕ) : ℕ :=
  Bool.casesOn (Nat.beq d 1) (rot1Fast w1 w3 B2 X) (rot3Fast w1 w3 B2 X)

/-- Fused SWAR step for `d ∈ {1, 2}` with pre-forced radices `w1, w3`. -/
def stepFast12Fast (w1 w3 d : ℕ) (st : SWARState192) : SWARState192 :=
  SWARState192.casesOn st fun k p B A C t =>
  withForcedNat (Nat.add k 1) fun k1 =>
  withForcedNat (Nat.add p (Bool.casesOn (Nat.beq d 1) 5 7)) fun p1 =>
  withForcedNat (Nat.add B B) fun B2 =>
  withForcedNat (rot12Fast w1 w3 d B2 C) fun cw =>
  withForcedNat (Nat.add A cw) fun nA =>
  withForcedNat (Nat.add A (Nat.sub B2 cw)) fun nC =>
  withForcedNat (Nat.add t 1) fun t1 =>
  ⟨k1, p1, B2, nA, nC, t1⟩

/-- Single-syllable SWAR step with pre-forced radices `w1, w2, w3`. -/
def step1Fast (w1 w2 w3 d : ℕ) (st : SWARState192) : SWARState192 :=
  SWARState192.casesOn st fun k p B A C t =>
  Bool.casesOn (Nat.ble d 2)
    (Bool.casesOn (Nat.ble d 4)
      (Bool.casesOn (Nat.beq d 5)
        (Bool.casesOn (Nat.beq d 6)
          (Bool.casesOn (Nat.beq d 7)
            ⟨k, p, B, A, C, t⟩
            (withForcedNat (Nat.sub (Nat.add B B) C) fun nC => ⟨k, Nat.add p 4, B, A, nC, t⟩))
          ⟨k, Nat.add p 4, B, C, A, t⟩)
        (let B2 := Nat.add B B
         withForcedNat (rot1Fast w1 w3 B2 C) fun nC => ⟨k, Nat.add p 1, B, A, nC, Nat.add t 1⟩))
      (Bool.casesOn (Nat.beq d 3)
        (let B2 := Nat.add B B
         withForcedNat (rot2Fast w2 B2 C) fun nC => ⟨k, Nat.add p 2, B, A, nC, t⟩)
        (withForcedNat (Nat.add B B) fun B2 =>
         withForcedNat (Nat.add A C) fun nA =>
         withForcedNat (Nat.add A (Nat.sub B2 C)) fun nC =>
         ⟨Nat.add k 1, Nat.add p 4, B2, nA, nC, t⟩)))
    (Bool.casesOn (Nat.beq d 0)
      (stepFast12Fast w1 w3 d ⟨k, p, B, A, C, t⟩)
      ⟨k, p, B, A, C, t⟩)

/-- Fallback 4-syllable SWAR evaluator with pre-forced radices `w1, w2, w3`. -/
def evalSlow4Fast (w1 w2 w3 d0 d1 d2 d3 : ℕ) (st : SWARState192) : Bool × SWARState192 :=
  Bool.casesOn (Nat.beq d0 0)
    (let s1 := step1Fast w1 w2 w3 d0 st
     Bool.casesOn (Nat.beq d1 0)
       (let s2 := step1Fast w1 w2 w3 d1 s1
        Bool.casesOn (Nat.beq d2 0)
          (let s3 := step1Fast w1 w2 w3 d2 s2
           Bool.casesOn (Nat.beq d3 0)
             (true, step1Fast w1 w2 w3 d3 s3)
             (false, s3))
          (false, s2))
       (false, s1))
    (false, st)

/-- Kernel-forced 4-syllable chunk evaluator avoiding unshared `Nat.div` growth. -/
def evalChunk4Fast (w1 w2 w3 : ℕ) : ℕ → ℕ → SWARState192 → SWARState192
  | 0, _, st => st
  | m + 1, code, st =>
    withForcedNat (Nat.mod code 8) fun d0 =>
    withForcedNat (Nat.div code 8) fun q0 =>
    withForcedNat (Nat.mod q0 8) fun d1 =>
    withForcedNat (Nat.div q0 8) fun q1 =>
    withForcedNat (Nat.mod q1 8) fun d2 =>
    withForcedNat (Nat.div q1 8) fun q2 =>
    withForcedNat (Nat.mod q2 8) fun d3 =>
    withForcedNat (Nat.div q2 8) fun q3 =>
    Bool.casesOn (is12SWAR d0 && is12SWAR d1 && is12SWAR d2 && is12SWAR d3)
      (Prod.casesOn (evalSlow4Fast w1 w2 w3 d0 d1 d2 d3 st) fun cont st' =>
        Bool.casesOn cont st' (evalChunk4Fast w1 w2 w3 m q3 st'))
      (evalChunk4Fast w1 w2 w3 m q3
        (stepFast12Fast w1 w3 d3 (stepFast12Fast w1 w3 d2
          (stepFast12Fast w1 w3 d1 (stepFast12Fast w1 w3 d0 st)))))

/-- Evaluate base-`8` chunks using pre-forced limb radices `w1, w2, w3`. -/
def evalChunksFast (w1 w2 w3 : ℕ) : List ℕ → SWARState192 → SWARState192
  | [], st => st
  | ch :: chs, st => evalChunksFast w1 w2 w3 chs (evalChunk4Fast w1 w2 w3 5 ch st)

theorem evalSlow4Fast_eq (d0 d1 d2 d3 : ℕ) (st : SWARState192) :
    evalSlow4Fast swarW192 swarW192_2 swarW192_3 d0 d1 d2 d3 st =
      evalSlow4SWAR192 d0 d1 d2 d3 st := rfl

theorem withUnpack4Fast_eq {α : Type} (X : ℕ) (f : ℕ → ℕ → ℕ → ℕ → α) :
    withUnpack4Fast swarW192 X f = withUnpack4SWAR192 X f := rfl

theorem evalChunk4Fast_eq :
    ∀ (m code : ℕ) (st : SWARState192),
      evalChunk4Fast swarW192 swarW192_2 swarW192_3 m code st = evalChunk4SWAR192 m code st
  | 0, _, _ => rfl
  | m + 1, code, st => by
    unfold evalChunk4Fast evalChunk4SWAR192
    simp only [withForcedNat_eq]
    cases (is12SWAR (Nat.mod code 8) && is12SWAR (Nat.mod (Nat.div code 8) 8) &&
      is12SWAR (Nat.mod (Nat.div (Nat.div code 8) 8) 8) &&
      is12SWAR (Nat.mod (Nat.div (Nat.div (Nat.div code 8) 8) 8) 8))
    · dsimp only
      rw [evalSlow4Fast_eq]
      rcases evalSlow4SWAR192 (Nat.mod code 8) (Nat.mod (Nat.div code 8) 8)
        (Nat.mod (Nat.div (Nat.div code 8) 8) 8)
        (Nat.mod (Nat.div (Nat.div (Nat.div code 8) 8) 8) 8) st with ⟨cont, st'⟩
      cases cont
      · rfl
      · exact evalChunk4Fast_eq m _ st'
    · exact evalChunk4Fast_eq m _ _

theorem evalChunksFast_eq :
    ∀ (chs : List ℕ) (st : SWARState192),
      evalChunksFast swarW192 swarW192_2 swarW192_3 chs st = evalChunksSWAR192 chs st
  | [], _ => rfl
  | ch :: chs, st => by
    dsimp only [evalChunksFast, evalChunksSWAR192]
    rw [evalChunk4Fast_eq]
    exact evalChunksFast_eq chs _

/-- Limb-aligned `4 × 192`-bit SWAR `Rz(θ)` single-word verifier (`k ≤ 180`). -/
def checkRzSWAR192Word (dRzNum : ℕ) (chs : List ℕ) (cMid sMid : SInt) (eUlps : ℕ) : Bool × ℕ :=
  withForcedNat swarW192 fun w1 =>
  withForcedNat swarW192_2 fun w2 =>
  withForcedNat swarW192_3 fun w3 =>
  withForcedNat swarOnes192 fun ones =>
  withForcedNat (Nat.add ones 1) fun initA =>
  SWARState192.casesOn (evalChunksFast w1 w2 w3 chs ⟨0, 0, ones, initA, ones, 0⟩)
    fun k p B A C tCnt =>
    let ok := Nat.ble k 180 && Nat.beq (Nat.mod p 8) 0 &&
      withForcedNat (Nat.mod B w1) fun b =>
      withForcedNat (Nat.add b b) fun b2 =>
      withUnpack4Fast w1 A fun a0 a1 a2 a3 =>
      withUnpack4Fast w1 C fun c0 c1 c2 c3 =>
      withForcedNat (Nat.add (Nat.div k 2) 1) fun q =>
      withForcedNat (Nat.pow 2 q) fun pow2q =>
      withForcedNat (Nat.mul dRzNum pow2q) fun rhs =>
      withForcedNat (Nat.mul rhs rhs) fun rhs2 =>
      let cPos := sintPos cMid; let cNeg := sintNeg cMid
      let msPos := sintNeg sMid; let msNeg := sintPos sMid
      Bool.casesOn (Nat.beq (Nat.mod k 2) 0)
        (withForcedNat (coordBoundPosNeg pow2q a1 a3 a0 b cPos cNeg eUlps) fun n1 =>
         withForcedNat (coordBoundPosNeg pow2q (Nat.add a1 a3) b2 a2 b msPos msNeg eUlps)
           fun n2 =>
         withForcedNat (coordBoundPosNeg pow2q c1 c3 c0 b 0 0 0) fun n3 =>
         withForcedNat (coordBoundPosNeg pow2q (Nat.add c1 c3) b2 c2 b 0 0 0) fun n4 =>
           Nat.ble (Nat.add (Nat.add (Nat.mul n1 n1) (Nat.mul n2 n2))
             (Nat.add (Nat.mul n3 n3) (Nat.mul n4 n4))) rhs2)
        (withForcedNat (coordBoundPosNeg pow2q (Nat.add a0 a0) b2 a1 a3 cPos cNeg eUlps)
           fun n1 =>
         withForcedNat
             (coordBoundPosNeg pow2q (Nat.add a2 a2) b2 (Nat.add a1 a3) b2 msPos msNeg eUlps)
             fun n2 =>
         withForcedNat (coordBoundPosNeg pow2q (Nat.add c0 c0) b2 c1 c3 0 0 0) fun n3 =>
         withForcedNat (coordBoundPosNeg pow2q (Nat.add c2 c2) b2 (Nat.add c1 c3) b2 0 0 0)
             fun n4 =>
           Nat.ble (Nat.add (Nat.add (Nat.mul n1 n1) (Nat.mul n2 n2))
             (Nat.add (Nat.mul n3 n3) (Nat.mul n4 n4))) rhs2)
    (ok, tCnt)

/-- Pack four `192`-bit lane coordinates into a single natural number. -/
def pack4_192 (x0 x1 x2 x3 : ℕ) : ℕ :=
  x0 + swarW192 * (x1 + swarW192 * (x2 + swarW192 * x3))

theorem swarW192_pos : 0 < swarW192 := by decide
theorem swarW192_2_eq : swarW192_2 = swarW192 * swarW192 := by decide
theorem swarW192_3_eq : swarW192_3 = swarW192 * (swarW192 * swarW192) := by decide
theorem swarOnes192_eq : swarOnes192 = pack4_192 1 1 1 1 := by decide
theorem swarInitA192_eq : Nat.add swarOnes192 1 = pack4_192 2 1 1 1 := by decide
theorem pow181_lt_swarW192 : 2 * 2 ^ 180 < swarW192 := by decide

section SWAR192Proofs
attribute [local irreducible] swarW192 swarW192_2 swarW192_3 swarOnes192

theorem nat_mod_def_192 (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem pack4_192_add (x0 x1 x2 x3 y0 y1 y2 y3 : ℕ) :
    Nat.add (pack4_192 x0 x1 x2 x3) (pack4_192 y0 y1 y2 y3) =
      pack4_192 (x0 + y0) (x1 + y1) (x2 + y2) (x3 + y3) := by
  unfold pack4_192; rw [Nat.add_eq]; ring

theorem pack4_192_sub {x0 x1 x2 x3 y0 y1 y2 y3 : ℕ}
    (h0 : x0 ≤ y0) (h1 : x1 ≤ y1) (h2 : x2 ≤ y2) (h3 : x3 ≤ y3) :
    Nat.sub (pack4_192 y0 y1 y2 y3) (pack4_192 x0 x1 x2 x3) =
      pack4_192 (y0 - x0) (y1 - x1) (y2 - x2) (y3 - x3) := by
  change pack4_192 y0 y1 y2 y3 - pack4_192 x0 x1 x2 x3 = _
  apply Nat.sub_eq_of_eq_add
  unfold pack4_192
  conv_lhs =>
    rw [← Nat.sub_add_cancel h0, ← Nat.sub_add_cancel h1,
        ← Nat.sub_add_cancel h2, ← Nat.sub_add_cancel h3]
  ring

theorem div_mod_base_192 {r q m : ℕ} (hm : 0 < m) (hr : r < m) :
    (r + m * q) / m = q ∧ (r + m * q) % m = r :=
  ⟨by rw [Nat.add_mul_div_left r q hm, Nat.div_eq_zero_iff.mpr (Or.inr hr), zero_add],
   by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]⟩

theorem lt_mul2_192 {x0 x1 m : ℕ} (h0 : x0 < m) (h1 : x1 < m) : x0 + m * x1 < m * m :=
  calc x0 + m * x1 < m + m * x1 := Nat.add_lt_add_right h0 _
    _ = m * (x1 + 1) := by ring
    _ ≤ m * m := Nat.mul_le_mul_left m h1

theorem lt_mul3_192 {x0 x1 x2 m : ℕ} (h0 : x0 < m) (h1 : x1 < m) (h2 : x2 < m) :
    x0 + m * (x1 + m * x2) < m * (m * m) := by
  have h12 := lt_mul2_192 h1 h2
  calc x0 + m * (x1 + m * x2) < m + m * (x1 + m * x2) := Nat.add_lt_add_right h0 _
    _ = m * (x1 + m * x2 + 1) := by ring
    _ ≤ m * (m * m) := Nat.mul_le_mul_left m h12

theorem unpack4_192_eq {x0 x1 x2 x3 : ℕ}
    (h0 : x0 < swarW192) (h1 : x1 < swarW192) (h2 : x2 < swarW192) :
    let X := pack4_192 x0 x1 x2 x3
    X % swarW192 = x0 ∧ (X / swarW192) % swarW192 = x1 ∧
      (X / swarW192 / swarW192) % swarW192 = x2 ∧
      X / swarW192 / swarW192 / swarW192 = x3 := by
  dsimp only [pack4_192]
  have s0 := div_mod_base_192 swarW192_pos h0 (q := x1 + swarW192 * (x2 + swarW192 * x3))
  have s1 := div_mod_base_192 swarW192_pos h1 (q := x2 + swarW192 * x3)
  have s2 := div_mod_base_192 swarW192_pos h2 (q := x3)
  exact ⟨s0.2, by rw [s0.1, s1.2], by rw [s0.1, s1.1, s2.2], by rw [s0.1, s1.1, s2.1]⟩

theorem withUnpack4SWAR192_pack4 {α : Type} {x0 x1 x2 x3 : ℕ}
    (h0 : x0 < swarW192) (h1 : x1 < swarW192) (h2 : x2 < swarW192)
    (f : ℕ → ℕ → ℕ → ℕ → α) :
    withUnpack4SWAR192 (pack4_192 x0 x1 x2 x3) f = f x0 x1 x2 x3 := by
  obtain ⟨u0, u1, u2, u3⟩ := unpack4_192_eq (x3 := x3) h0 h1 h2
  have ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
  simp only [withUnpack4SWAR192, withForcedNat_eq, nat_mod_def_192, ndiv, u0, u1, u2, u3]

attribute [local irreducible] withUnpack4SWAR192

theorem rot1SWAR192_pack4 {b x0 x1 x2 x3 : ℕ} (hb : 2 * b < swarW192)
    (h0 : x0 ≤ 2 * b) (h1 : x1 ≤ 2 * b) (h2 : x2 ≤ 2 * b) (h3 : x3 ≤ 2 * b) :
    rot1SWAR192 (pack4_192 (2 * b) (2 * b) (2 * b) (2 * b)) (pack4_192 x0 x1 x2 x3) =
      pack4_192 (2 * b - x3) x0 x1 x2 := by
  unfold rot1SWAR192
  rw [pack4_192_sub h0 h1 h2 h3]
  change pack4_192 (2 * b - x0) (2 * b - x1) (2 * b - x2) (2 * b - x3) / swarW192_3 +
    (pack4_192 x0 x1 x2 x3 % swarW192_3) * swarW192 = _
  have split3 (u0 u1 u2 u3 : ℕ) :
      pack4_192 u0 u1 u2 u3 = (u0 + swarW192 * (u1 + swarW192 * u2)) + swarW192_3 * u3 := by
    unfold pack4_192; rw [swarW192_3_eq]; ring
  have hw3 : 0 < swarW192_3 := by
    rw [swarW192_3_eq]; exact Nat.mul_pos swarW192_pos (Nat.mul_pos swarW192_pos swarW192_pos)
  have hd := (div_mod_base_192 hw3
    (r := (2 * b - x0) + swarW192 * ((2 * b - x1) + swarW192 * (2 * b - x2)))
    (q := 2 * b - x3) (by rw [swarW192_3_eq]; exact lt_mul3_192 (by omega) (by omega) (by omega))).1
  have hm := (div_mod_base_192 hw3 (r := x0 + swarW192 * (x1 + swarW192 * x2))
    (q := x3) (by rw [swarW192_3_eq]; exact lt_mul3_192 (by omega) (by omega) (by omega))).2
  rw [split3 (2 * b - x0), hd, split3 x0, hm]
  unfold pack4_192; ring

theorem rot2SWAR192_pack4 {b x0 x1 x2 x3 : ℕ} (hb : 2 * b < swarW192)
    (h0 : x0 ≤ 2 * b) (h1 : x1 ≤ 2 * b) (h2 : x2 ≤ 2 * b) (h3 : x3 ≤ 2 * b) :
    rot2SWAR192 (pack4_192 (2 * b) (2 * b) (2 * b) (2 * b)) (pack4_192 x0 x1 x2 x3) =
      pack4_192 (2 * b - x2) (2 * b - x3) x0 x1 := by
  unfold rot2SWAR192
  rw [pack4_192_sub h0 h1 h2 h3]
  change pack4_192 (2 * b - x0) (2 * b - x1) (2 * b - x2) (2 * b - x3) / swarW192_2 +
    (pack4_192 x0 x1 x2 x3 % swarW192_2) * swarW192_2 = _
  have split2 (u0 u1 u2 u3 : ℕ) :
      pack4_192 u0 u1 u2 u3 = (u0 + swarW192 * u1) + swarW192_2 * (u2 + swarW192 * u3) := by
    unfold pack4_192; rw [swarW192_2_eq]; ring
  have hw2 : 0 < swarW192_2 := by rw [swarW192_2_eq]; exact Nat.mul_pos swarW192_pos swarW192_pos
  have hd := (div_mod_base_192 hw2 (r := (2 * b - x0) + swarW192 * (2 * b - x1))
    (q := (2 * b - x2) + swarW192 * (2 * b - x3))
    (by rw [swarW192_2_eq]; exact lt_mul2_192 (by omega) (by omega))).1
  have hm := (div_mod_base_192 hw2 (r := x0 + swarW192 * x1)
    (q := x2 + swarW192 * x3) (by rw [swarW192_2_eq]; exact lt_mul2_192 (by omega) (by omega))).2
  rw [split2 (2 * b - x0), hd, split2 x0, hm]
  unfold pack4_192; rw [swarW192_2_eq]; ring

theorem rot3SWAR192_pack4 {b x0 x1 x2 x3 : ℕ} (hb : 2 * b < swarW192)
    (h0 : x0 ≤ 2 * b) (h1 : x1 ≤ 2 * b) (h2 : x2 ≤ 2 * b) (h3 : x3 ≤ 2 * b) :
    rot3SWAR192 (pack4_192 (2 * b) (2 * b) (2 * b) (2 * b)) (pack4_192 x0 x1 x2 x3) =
      pack4_192 (2 * b - x1) (2 * b - x2) (2 * b - x3) x0 := by
  unfold rot3SWAR192
  rw [pack4_192_sub h0 h1 h2 h3]
  change pack4_192 (2 * b - x0) (2 * b - x1) (2 * b - x2) (2 * b - x3) / swarW192 +
    (pack4_192 x0 x1 x2 x3 % swarW192) * swarW192_3 = _
  have hd := (div_mod_base_192 swarW192_pos (r := 2 * b - x0)
    (q := (2 * b - x1) + swarW192 * ((2 * b - x2) + swarW192 * (2 * b - x3))) (by omega)).1
  have hm := (div_mod_base_192 swarW192_pos (r := x0)
    (q := x1 + swarW192 * (x2 + swarW192 * x3)) (by omega)).2
  dsimp only [pack4_192]
  rw [hd, hm, swarW192_3_eq]; ring

/-- Biased 4-lane cyclotomic representation invariant `xᵢ - b = z.cᵢ`. -/
def Cyc8Biased192 (b x0 x1 x2 x3 : ℕ) (z : Cyc8) : Prop :=
  x0 ≤ 2 * b ∧ x1 ≤ 2 * b ∧ x2 ≤ 2 * b ∧ x3 ≤ 2 * b ∧
  (x0 : ℝ) - (b : ℝ) = z.c0.toReal ∧ (x1 : ℝ) - (b : ℝ) = z.c1.toReal ∧
  (x2 : ℝ) - (b : ℝ) = z.c2.toReal ∧ (x3 : ℝ) - (b : ℝ) = z.c3.toReal

theorem biased192_opp {b x0 x1 x2 x3 : ℕ} {z : Cyc8} (h : Cyc8Biased192 b x0 x1 x2 x3 z) :
    Cyc8Biased192 b (2 * b - x0) (2 * b - x1) (2 * b - x2) (2 * b - x3) z.opp := by
  obtain ⟨h0, h1, h2, h3, e0, e1, e2, e3⟩ := h
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Cyc8.opp, SInt.toReal_opp, Nat.cast_sub h0, Nat.cast_sub h1, Nat.cast_sub h2,
      Nat.cast_sub h3, Nat.cast_mul, Nat.cast_ofNat] <;> linarith

theorem biased192_mulOmega {b x0 x1 x2 x3 : ℕ} {z : Cyc8} (h : Cyc8Biased192 b x0 x1 x2 x3 z) :
    Cyc8Biased192 b (2 * b - x3) x0 x1 x2 z.mulOmega := by
  obtain ⟨h0, h1, h2, h3, e0, e1, e2, e3⟩ := h
  refine ⟨by omega, h0, h1, h2, ?_, e0, e1, e2⟩
  simp only [Cyc8.mulOmega, SInt.toReal_opp, Nat.cast_sub h3, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem biased192_mulI {b x0 x1 x2 x3 : ℕ} {z : Cyc8} (h : Cyc8Biased192 b x0 x1 x2 x3 z) :
    Cyc8Biased192 b (2 * b - x2) (2 * b - x3) x0 x1 z.mulI := by
  obtain ⟨h0, h1, h2, h3, e0, e1, e2, e3⟩ := h
  refine ⟨by omega, by omega, h0, h1, ?_, ?_, e0, e1⟩ <;>
    simp only [Cyc8.mulI, SInt.toReal_opp, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_mul,
      Nat.cast_ofNat] <;> linarith

theorem biased192_add {b a0 a1 a2 a3 w0 w1 w2 w3 : ℕ} {a w : Cyc8}
    (ha : Cyc8Biased192 b a0 a1 a2 a3 a) (hw : Cyc8Biased192 b w0 w1 w2 w3 w) :
    Cyc8Biased192 (2 * b) (a0 + w0) (a1 + w1) (a2 + w2) (a3 + w3) (a.add w) := by
  obtain ⟨ha0, ha1, ha2, ha3, ea0, ea1, ea2, ea3⟩ := ha
  obtain ⟨hw0, hw1, hw2, hw3, ew0, ew1, ew2, ew3⟩ := hw
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Cyc8.add, SInt.toReal_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> linarith

theorem biased192_sub {b a0 a1 a2 a3 w0 w1 w2 w3 : ℕ} {a w : Cyc8}
    (ha : Cyc8Biased192 b a0 a1 a2 a3 a) (hw : Cyc8Biased192 b w0 w1 w2 w3 w) :
    Cyc8Biased192 (2 * b) (a0 + (2 * b - w0)) (a1 + (2 * b - w1))
      (a2 + (2 * b - w2)) (a3 + (2 * b - w3)) (a.sub w) := by
  obtain ⟨ha0, ha1, ha2, ha3, ea0, ea1, ea2, ea3⟩ := ha
  obtain ⟨hw0, hw1, hw2, hw3, ew0, ew1, ew2, ew3⟩ := hw
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Cyc8.sub, SInt.toReal_sub, Nat.cast_add, Nat.cast_sub hw0, Nat.cast_sub hw1,
      Nat.cast_sub hw2, Nat.cast_sub hw3, Nat.cast_mul, Nat.cast_ofNat] <;> linarith

theorem absDiffNat_toReal_192 (x y : ℕ) : (absDiffNat x y : ℝ) = |(x : ℝ) - (y : ℝ)| := by
  unfold absDiffNat
  cases h : Nat.ble y x
  · have hlt : x < y := not_le.mp (fun hle => by rw [Nat.ble_eq.mpr hle] at h; cases h)
    have hle : x ≤ y := hlt.le
    simp only [Nat.sub_eq, Nat.cast_sub hle, abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hle))]
    ring
  · have hle : y ≤ x := Nat.ble_eq.mp h
    simp only [Nat.sub_eq, Nat.cast_sub hle, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hle))]

theorem sintPos_sub_sintNeg_192 (x : SInt) :
    (sintPos x : ℝ) - (sintNeg x : ℝ) = x.toReal := by
  rcases x with ⟨neg, mag⟩
  cases neg <;> simp [sintPos, sintNeg, SInt.toReal]

theorem coordBoundPosNeg_eq_coordNumBound_192
    (pow2q p1 n1 p2 n2 tPos tNeg eUlps : ℕ) (ab : SInt × SInt) (tMid : SInt)
    (h1 : (p1 : ℝ) - (n1 : ℝ) = ab.1.toReal)
    (h2 : (p2 : ℝ) - (n2 : ℝ) = ab.2.toReal)
    (ht : (tPos : ℝ) - (tNeg : ℝ) = tMid.toReal) :
    coordBoundPosNeg pow2q p1 n1 p2 n2 tPos tNeg eUlps =
      coordNumBound pow2q ab tMid eUlps := by
  suffices hR : (coordBoundPosNeg pow2q p1 n1 p2 n2 tPos tNeg eUlps : ℝ) =
      (coordNumBound pow2q ab tMid eUlps : ℝ) from by exact_mod_cast hR
  unfold coordBoundPosNeg coordNumBound
  simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, absDiffNat_toReal_192]
  have hmag1 : |(((p1 : ℝ) * scale24 + (p2 : ℝ) * s2Nat + (tNeg : ℝ) * pow2q) -
      ((n1 : ℝ) * scale24 + (n2 : ℝ) * s2Nat + (tPos : ℝ) * pow2q))| =
      ((((ab.1.mul (.ofNat scale24)).add (ab.2.mul (.ofNat s2Nat))).sub
        (tMid.mul (.ofNat pow2q))).mag : ℝ) := by
    rw [← SInt.abs_toReal]
    simp only [SInt.toReal_sub, SInt.toReal_add, SInt.toReal_mul, SInt.toReal_ofNat]
    congr 1; linear_combination scale24 * h1 + s2Nat * h2 - pow2q * ht
  have hmag2 : |(p2 : ℝ) - (n2 : ℝ)| = (ab.2.mag : ℝ) := by
    rw [h2, SInt.abs_toReal]
  linarith

/-- Reference single-syllable-per-step `192`-bit SWAR chunk evaluator. -/
def evalChunk1SWAR192 : ℕ → ℕ → SWARState192 → SWARState192
  | 0, _, st => st
  | n + 1, code, st =>
    let d := Nat.mod code 8
    if Nat.beq d 0 then st
    else evalChunk1SWAR192 n (Nat.div code 8) (step1SWAR192 d st)

theorem step1SWAR192_d12 (d : ℕ) (hd : is12SWAR d = true) (st : SWARState192) :
    step1SWAR192 d st = stepFast12SWAR192 d st := by
  unfold is12SWAR at hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hd
  have hd_cases : d = 1 ∨ d = 2 := by omega
  rcases st with ⟨k, p, B, A, C, t⟩
  rcases hd_cases with rfl | rfl <;> rfl

theorem evalChunk1SWAR192_step (n code : ℕ) (st : SWARState192) :
    evalChunk1SWAR192 (n + 1) code st =
      if Nat.beq (Nat.mod code 8) 0 then st
      else evalChunk1SWAR192 n (Nat.div code 8) (step1SWAR192 (Nat.mod code 8) st) := rfl

theorem evalChunk4SWAR192_eq :
    ∀ (m code : ℕ) (st : SWARState192),
      evalChunk4SWAR192 m code st = evalChunk1SWAR192 (4 * m) code st
  | 0, _, _ => rfl
  | m + 1, code, st => by
    have h4 : 4 * (m + 1) = (((4 * m + 1) + 1) + 1) + 1 := by omega
    rw [h4, evalChunk1SWAR192_step]
    unfold evalChunk4SWAR192; dsimp only
    cases his : (is12SWAR (Nat.mod code 8) && is12SWAR (Nat.mod (Nat.div code 8) 8) &&
      is12SWAR (Nat.mod (Nat.div (Nat.div code 8) 8) 8) &&
      is12SWAR (Nat.mod (Nat.div (Nat.div (Nat.div code 8) 8) 8) 8))
    · dsimp only [evalSlow4SWAR192]
      cases hb0 : Nat.beq (Nat.mod code 8) 0
      · dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, evalChunk1SWAR192_step]
        cases hb1 : Nat.beq (Nat.mod (Nat.div code 8) 8) 0
        · dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]
          cases hb2 : Nat.beq (Nat.div (Nat.div code 8) 8 |>.mod 8) 0
          · dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]
            cases hb3 : Nat.beq (Nat.mod (Nat.div (Nat.div (Nat.div code 8) 8) 8) 8) 0
            · dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]
              exact evalChunk4SWAR192_eq m _ _
            · dsimp only; simp only [↓reduceIte]
          · dsimp only; simp only [↓reduceIte]
        · dsimp only; simp only [↓reduceIte]
      · dsimp only; simp only [↓reduceIte]
    · dsimp only
      simp only [Bool.and_eq_true] at his
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := his
      have nz (d : ℕ) (hd : is12SWAR d = true) : Nat.beq d 0 = false := by
        unfold is12SWAR at hd; simp only [Bool.and_eq_true, Nat.ble_eq] at hd
        cases h : Nat.beq d 0
        · rfl
        · exfalso; have := Nat.beq_eq.mp h; omega
      simp only [nz _ h0, nz _ h1, nz _ h2, nz _ h3, Bool.false_eq_true, ↓reduceIte,
        evalChunk1SWAR192_step, step1SWAR192_d12 _ h0, step1SWAR192_d12 _ h1,
        step1SWAR192_d12 _ h2, step1SWAR192_d12 _ h3]
      exact evalChunk4SWAR192_eq m _ _

attribute [local irreducible] rot1SWAR192 rot2SWAR192 rot3SWAR192

/-- Unfolded output specification of `step1SWAR192`. -/
def step1SWAR192Out (d k p B A C t : ℕ) : SWARState192 :=
  match d with
  | 1 => ⟨k + 1, p + 7, Nat.add B B, Nat.add A (rot3SWAR192 (Nat.add B B) C),
           Nat.add A (Nat.sub (Nat.add B B) (rot3SWAR192 (Nat.add B B) C)), t + 1⟩
  | 2 => ⟨k + 1, p + 5, Nat.add B B, Nat.add A (rot1SWAR192 (Nat.add B B) C),
           Nat.add A (Nat.sub (Nat.add B B) (rot1SWAR192 (Nat.add B B) C)), t + 1⟩
  | 3 => ⟨k + 1, p + 4, Nat.add B B, Nat.add A C, Nat.add A (Nat.sub (Nat.add B B) C), t⟩
  | 4 => ⟨k, p + 2, B, A, rot2SWAR192 (Nat.add B B) C, t⟩
  | 5 => ⟨k, p + 1, B, A, rot1SWAR192 (Nat.add B B) C, t + 1⟩
  | 6 => ⟨k, p + 4, B, C, A, t⟩
  | 7 => ⟨k, p + 4, B, A, Nat.sub (Nat.add B B) C, t⟩
  | _ => ⟨k, p, B, A, C, t⟩

theorem step1SWAR192_clean (d k p B A C t : ℕ) :
    step1SWAR192 d ⟨k, p, B, A, C, t⟩ = step1SWAR192Out d k p B A C t := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    unfold step1SWAR192 stepFast12SWAR192 rot12SWAR192 step1SWAR192Out
    simp only [withForcedNat_eq, Nat.add_eq]; rfl
  | n + 8 =>
    have b1 : Nat.ble (n + 8) 2 = false :=
      Bool.eq_false_iff.mpr fun h => by have := Nat.ble_eq.mp h; omega
    have b2 : Nat.ble (n + 8) 4 = false :=
      Bool.eq_false_iff.mpr fun h => by have := Nat.ble_eq.mp h; omega
    have b5 : Nat.beq (n + 8) 5 = false :=
      Bool.eq_false_iff.mpr fun h => by have := Nat.beq_eq.mp h; omega
    have b6 : Nat.beq (n + 8) 6 = false :=
      Bool.eq_false_iff.mpr fun h => by have := Nat.beq_eq.mp h; omega
    have b7 : Nat.beq (n + 8) 7 = false :=
      Bool.eq_false_iff.mpr fun h => by have := Nat.beq_eq.mp h; omega
    unfold step1SWAR192 step1SWAR192Out; simp only [b1, b2, b5, b6, b7]

theorem step1SWAR192_k_bounds (d : ℕ) (sw : SWARState192) :
    sw.k ≤ (step1SWAR192 d sw).k ∧ (step1SWAR192 d sw).k ≤ sw.k + 1 := by
  rcases sw with ⟨k, p, B, A, C, t⟩
  rw [step1SWAR192_clean]
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _ + 8 =>
    simp only [step1SWAR192Out]; exact ⟨by omega, by omega⟩

theorem evalChunk1SWAR192_k_le :
    ∀ (n code : ℕ) (sw : SWARState192), sw.k ≤ (evalChunk1SWAR192 n code sw).k
  | 0, _, _ => le_rfl
  | n + 1, code, sw => by
    unfold evalChunk1SWAR192; dsimp only
    split_ifs
    · exact le_rfl
    · exact (step1SWAR192_k_bounds _ sw).1.trans (evalChunk1SWAR192_k_le n _ _)

theorem evalChunksSWAR192_k_le :
    ∀ (chs : List ℕ) (sw : SWARState192), sw.k ≤ (evalChunksSWAR192 chs sw).k
  | [], _ => le_rfl
  | ch :: chs, sw => by
    dsimp only [evalChunksSWAR192]
    rw [evalChunk4SWAR192_eq]
    exact (evalChunk1SWAR192_k_le (4 * 5) ch sw).trans (evalChunksSWAR192_k_le chs _)

/-- Refinement relation between `SWARState192` and `FastSU2`. -/
def SWARRel192 (sw : SWARState192) (st : FastSU2) : Prop :=
  ∃ a0 a1 a2 a3 c0 c1 c2 c3 : ℕ,
    sw.k = st.k ∧ sw.p % 8 = st.p ∧ sw.t = st.tCnt ∧
    sw.bPack = pack4_192 (2 ^ st.k) (2 ^ st.k) (2 ^ st.k) (2 ^ st.k) ∧
    sw.aPack = pack4_192 a0 a1 a2 a3 ∧
    sw.cPack = pack4_192 c0 c1 c2 c3 ∧
    Cyc8Biased192 (2 ^ st.k) a0 a1 a2 a3 st.a ∧
    Cyc8Biased192 (2 ^ st.k) c0 c1 c2 c3 st.c

theorem swarInit192_rel : SWARRel192 swarInit192 FastSU2.init := by
  refine ⟨2, 1, 1, 1, 1, 1, 1, 1, rfl, rfl, rfl, swarOnes192_eq, swarInitA192_eq,
    swarOnes192_eq, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
      (dsimp only [FastSU2.init, Cyc8.one]; rw [SInt.toReal_ofNat]; norm_num)
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
      (dsimp only [FastSU2.init, Cyc8.zero]; rw [SInt.toReal_ofNat]; norm_num)

theorem two_mul_pow_lt_swarW192 {k : ℕ} (hk : k ≤ 180) : 2 * 2 ^ k < swarW192 :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hk)) pow181_lt_swarW192

/-- Unfolded output specification of `stepCodeSU2`. -/
def stepCodeSU2Out192 (d : ℕ) (st : FastSU2) : FastSU2 :=
  match d with
  | 1 => ⟨st.k + 1, (st.p + 7) % 8, st.a.add st.c.mulOmega.mulI,
           st.a.sub st.c.mulOmega.mulI, st.tCnt + 1⟩
  | 2 => ⟨st.k + 1, (st.p + 5) % 8, st.a.add st.c.mulOmega,
           st.a.sub st.c.mulOmega, st.tCnt + 1⟩
  | 3 => ⟨st.k + 1, (st.p + 4) % 8, st.a.add st.c, st.a.sub st.c, st.tCnt⟩
  | 4 => ⟨st.k, (st.p + 2) % 8, st.a, st.c.mulI, st.tCnt⟩
  | 5 => ⟨st.k, (st.p + 1) % 8, st.a, st.c.mulOmega, st.tCnt + 1⟩
  | 6 => ⟨st.k, (st.p + 4) % 8, st.c, st.a, st.tCnt⟩
  | 7 => ⟨st.k, (st.p + 4) % 8, st.a, st.c.opp, st.tCnt⟩
  | _ => st

theorem stepCodeSU2_clean_192 (d : ℕ) (st : FastSU2) :
    stepCodeSU2 d st = stepCodeSU2Out192 d st := by
  rcases st with ⟨k, p, a, c, t⟩
  have mk_eq (z : Cyc8) : (⟨z.1, z.2, z.3, z.4⟩ : Cyc8) = z := by cases z; rfl
  match d with
  | 0 | _ + 8 => rfl
  | 1 =>
    simp only [stepCodeSU2, stepZSTZH, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192, mk_eq, Cyc8.addStrict_eq, Cyc8.subStrict_eq, Cyc8.mulIStrict_eq,
      Cyc8.mulOmegaStrict_eq]
  | 2 =>
    simp only [stepCodeSU2, stepZSTSH, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192, mk_eq, Cyc8.addStrict_eq, Cyc8.subStrict_eq, Cyc8.mulOmegaStrict_eq]
  | 3 =>
    simp only [stepCodeSU2, stepGateSU2, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192, mk_eq, Cyc8.addStrict_eq, Cyc8.subStrict_eq]
  | 4 =>
    simp only [stepCodeSU2, stepGateSU2, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192, mk_eq, Cyc8.mulIStrict_eq]
  | 5 =>
    simp only [stepCodeSU2, stepGateSU2, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192, mk_eq, Cyc8.mulOmegaStrict_eq]
  | 6 =>
    simp only [stepCodeSU2, stepGateSU2, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192]
  | 7 =>
    simp only [stepCodeSU2, stepGateSU2, stepCodeSU2Out192, withForcedNat_eq, Nat.add_eq,
      nat_mod_def_192, mk_eq, Cyc8.oppStrict_eq]

theorem pack4_192_double (b : ℕ) :
    Nat.add (pack4_192 b b b b) (pack4_192 b b b b) =
      pack4_192 (2 * b) (2 * b) (2 * b) (2 * b) := by
  rw [pack4_192_add, two_mul]

attribute [local irreducible] pack4_192

theorem step1SWAR192_rel (d : ℕ) {sw : SWARState192} {st : FastSU2}
    (hrel : SWARRel192 sw st) (hk : sw.k ≤ 180) :
    SWARRel192 (step1SWAR192 d sw) (stepCodeSU2 d st) := by
  rcases sw with ⟨k, p, B, A, C, t⟩
  rw [step1SWAR192_clean, stepCodeSU2_clean_192]
  obtain ⟨a0, a1, a2, a3, c0, c1, c2, c3, hk_eq, hp_eq, ht_eq, hB, hA, hC, ha, hc⟩ := hrel
  change k ≤ 180 at hk; change k = st.k at hk_eq; change p % 8 = st.p at hp_eq
  change t = st.tCnt at ht_eq; change B = _ at hB; change A = _ at hA; change C = _ at hC
  subst hk_eq ht_eq
  have hb : 2 * 2 ^ st.k < swarW192 := two_mul_pow_lt_swarW192 hk
  have hpow : 2 ^ (st.k + 1) = 2 * 2 ^ st.k := by rw [Nat.pow_succ]; ring
  have hB2 : Nat.add B B =
      pack4_192 (2 * 2 ^ st.k) (2 * 2 ^ st.k) (2 * 2 ^ st.k) (2 * 2 ^ st.k) := by
    rw [hB]; exact pack4_192_double _
  match d with
  | 0 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨a0, a1, a2, a3, c0, c1, c2, c3, rfl, hp_eq, rfl, hB, hA, hC, ha, hc⟩
  | 1 =>
    have hw := biased192_mulI (biased192_mulOmega hc)
    have hrot : rot3SWAR192 (Nat.add B B) C =
        pack4_192 (2 * 2 ^ st.k - c1) (2 * 2 ^ st.k - c2) (2 * 2 ^ st.k - c3) c0 := by
      rw [hB2, hC]; exact rot3SWAR192_pack4 hb hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, by rw [hB2, hpow],
      by rw [hA, hrot, pack4_192_add, ← hpow],
      by rw [hA, hrot, hB2, pack4_192_sub hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1, pack4_192_add,
        ← hpow],
      hpow ▸ biased192_add ha hw, hpow ▸ biased192_sub ha hw⟩
  | 2 =>
    have hw := biased192_mulOmega hc
    have hrot : rot1SWAR192 (Nat.add B B) C =
        pack4_192 (2 * 2 ^ st.k - c3) c0 c1 c2 := by
      rw [hB2, hC]; exact rot1SWAR192_pack4 hb hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, by rw [hB2, hpow],
      by rw [hA, hrot, pack4_192_add, ← hpow],
      by rw [hA, hrot, hB2, pack4_192_sub hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1, pack4_192_add,
        ← hpow],
      hpow ▸ biased192_add ha hw, hpow ▸ biased192_sub ha hw⟩
  | 3 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, by rw [hB2, hpow],
      by rw [hA, hC, pack4_192_add],
      by rw [hA, hB2, hC, pack4_192_sub hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1, pack4_192_add, ← hpow],
      hpow ▸ biased192_add ha hc, hpow ▸ biased192_sub ha hc⟩
  | 4 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, hB, hA,
      by rw [hB2, hC]; exact rot2SWAR192_pack4 hb hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1,
      ha, biased192_mulI hc⟩
  | 5 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, hB, hA,
      by rw [hB2, hC]; exact rot1SWAR192_pack4 hb hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1,
      ha, biased192_mulOmega hc⟩
  | 6 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, hB, hC, hA, hc, ha⟩
  | 7 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨_, _, _, _, _, _, _, _, rfl, by omega, rfl, hB, hA,
      by rw [hB2, hC]; exact pack4_192_sub hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1,
      ha, biased192_opp hc⟩
  | _ + 8 =>
    simp only [step1SWAR192Out, stepCodeSU2Out192]; dsimp only [SWARRel192]
    exact ⟨a0, a1, a2, a3, c0, c1, c2, c3, rfl, hp_eq, rfl, hB, hA, hC, ha, hc⟩

theorem evalChunk1SWAR192_rel :
    ∀ (n code : ℕ) {sw : SWARState192} {st : FastSU2},
      SWARRel192 sw st → (evalChunk1SWAR192 n code sw).k ≤ 180 →
      SWARRel192 (evalChunk1SWAR192 n code sw) (evalChunkAux n code st)
  | 0, _, _, _, hrel, _ => hrel
  | n + 1, code, sw, st, hrel, hk => by
    unfold evalChunk1SWAR192 evalChunkAux; dsimp only
    split_ifs with h0
    · exact hrel
    · simp only [evalChunk1SWAR192, h0] at hk
      have hk_sw : sw.k ≤ 180 :=
        ((step1SWAR192_k_bounds _ sw).1.trans (evalChunk1SWAR192_k_le n _ _)).trans hk
      exact evalChunk1SWAR192_rel n _ (step1SWAR192_rel _ hrel hk_sw) hk

theorem evalChunksSWAR192_rel :
    ∀ (chs : List ℕ) {sw : SWARState192} {st : FastSU2},
      SWARRel192 sw st → (evalChunksSWAR192 chs sw).k ≤ 180 →
      SWARRel192 (evalChunksSWAR192 chs sw) (evalChunksSU2 chs st)
  | [], _, _, hrel, _ => hrel
  | ch :: chs, sw, st, hrel, hk => by
    dsimp only [evalChunksSWAR192, evalChunksSU2] at hk ⊢
    rw [evalChunk4SWAR192_eq] at hk ⊢
    have hk1 : (evalChunk1SWAR192 (4 * 5) ch sw).k ≤ 180 :=
      (evalChunksSWAR192_k_le chs _).trans hk
    exact evalChunksSWAR192_rel chs (evalChunk1SWAR192_rel (4 * 5) ch hrel hk1) hk

theorem coordRe192_false {k b z0 z1 z2 z3 pow2q tPos tNeg eUlps : ℕ} {z : Cyc8} {tMid : SInt}
    (hk : Nat.beq (Nat.mod k 2) 0 = false) (hz : Cyc8Biased192 b z0 z1 z2 z3 z)
    (ht : (tPos : ℝ) - (tNeg : ℝ) = tMid.toReal) :
    coordBoundPosNeg pow2q z1 z3 z0 b tPos tNeg eUlps =
      coordNumBound pow2q (cycReAB k z) tMid eUlps := by
  have hmod : (k % 2 == 0) = false := by
    cases h : (k % 2 == 0); · rfl
    · rw [beq_iff_eq] at h; rw [nat_mod_def_192, h] at hk; cases hk
  obtain ⟨_, _, _, _, e0, e1, _, e3⟩ := hz
  unfold cycReAB; simp only [hmod, Bool.false_eq_true, ↓reduceIte]
  exact coordBoundPosNeg_eq_coordNumBound_192 pow2q z1 z3 z0 b tPos tNeg eUlps _ tMid
    (by simp only [SInt.toReal_sub]; linarith) e0 ht

theorem coordRe192_true {k b z0 z1 z2 z3 pow2q tPos tNeg eUlps : ℕ} {z : Cyc8} {tMid : SInt}
    (hk : Nat.beq (Nat.mod k 2) 0 = true) (hz : Cyc8Biased192 b z0 z1 z2 z3 z)
    (ht : (tPos : ℝ) - (tNeg : ℝ) = tMid.toReal) :
    coordBoundPosNeg pow2q (z0 + z0) (b + b) z1 z3 tPos tNeg eUlps =
      coordNumBound pow2q (cycReAB k z) tMid eUlps := by
  have hmod : (k % 2 == 0) = true := by rw [beq_iff_eq]; exact Nat.beq_eq.mp hk
  obtain ⟨_, _, _, _, e0, e1, _, e3⟩ := hz
  unfold cycReAB; simp only [hmod, ↓reduceIte]
  exact coordBoundPosNeg_eq_coordNumBound_192 pow2q (z0 + z0) (b + b) z1 z3 tPos tNeg
    eUlps _ tMid (by simp only [Nat.cast_add, SInt.toReal_mul, SInt.toReal_ofNat,
      Nat.cast_ofNat]; linarith) (by simp only [SInt.toReal_sub]; linarith) ht

theorem coordIm192_false {k b z0 z1 z2 z3 pow2q tPos tNeg eUlps : ℕ} {z : Cyc8} {tMid : SInt}
    (hk : Nat.beq (Nat.mod k 2) 0 = false) (hz : Cyc8Biased192 b z0 z1 z2 z3 z)
    (ht : (tPos : ℝ) - (tNeg : ℝ) = tMid.toReal) :
    coordBoundPosNeg pow2q (z1 + z3) (b + b) z2 b tPos tNeg eUlps =
      coordNumBound pow2q (cycImAB k z) tMid eUlps := by
  have hmod : (k % 2 == 0) = false := by
    cases h : (k % 2 == 0); · rfl
    · rw [beq_iff_eq] at h; rw [nat_mod_def_192, h] at hk; cases hk
  obtain ⟨_, _, _, _, _, e1, e2, e3⟩ := hz
  unfold cycImAB; simp only [hmod, Bool.false_eq_true, ↓reduceIte]
  exact coordBoundPosNeg_eq_coordNumBound_192 pow2q (z1 + z3) (b + b) z2 b tPos tNeg
    eUlps _ tMid (by simp only [Nat.cast_add, SInt.toReal_add]; linarith) e2 ht

theorem coordIm192_true {k b z0 z1 z2 z3 pow2q tPos tNeg eUlps : ℕ} {z : Cyc8} {tMid : SInt}
    (hk : Nat.beq (Nat.mod k 2) 0 = true) (hz : Cyc8Biased192 b z0 z1 z2 z3 z)
    (ht : (tPos : ℝ) - (tNeg : ℝ) = tMid.toReal) :
    coordBoundPosNeg pow2q (z2 + z2) (b + b) (z1 + z3) (b + b)
      tPos tNeg eUlps = coordNumBound pow2q (cycImAB k z) tMid eUlps := by
  have hmod : (k % 2 == 0) = true := by rw [beq_iff_eq]; exact Nat.beq_eq.mp hk
  obtain ⟨_, _, _, _, _, e1, e2, e3⟩ := hz
  unfold cycImAB; simp only [hmod, ↓reduceIte]
  exact coordBoundPosNeg_eq_coordNumBound_192 pow2q (z2 + z2) (b + b) (z1 + z3)
    (b + b) tPos tNeg eUlps _ tMid
    (by simp only [Nat.cast_add, SInt.toReal_mul, SInt.toReal_ofNat,
      Nat.cast_ofNat]; linarith)
    (by simp only [Nat.cast_add, SInt.toReal_add]; linarith) ht

theorem checkRzSWAR192Word_extract (dRzNum : ℕ) (chs : List ℕ) (cMid sMid : SInt) (eUlps : ℕ)
    (hok : (checkRzSWAR192Word dRzNum chs cMid sMid eUlps).1 = true) :
    ∃ ks a c,
      evalChunksSU2 chs FastSU2.init =
        ⟨ks, 0, a, c, (checkRzSWAR192Word dRzNum chs cMid sMid eUlps).2⟩ ∧
      let pow2q := 2 ^ (ks / 2 + 1)
      (coordNumBound pow2q (cycReAB ks a) cMid eUlps) ^ 2 +
        (coordNumBound pow2q (cycImAB ks a) sMid.opp eUlps) ^ 2 +
        (coordNumBound pow2q (cycReAB ks c) (.ofNat 0) 0) ^ 2 +
        (coordNumBound pow2q (cycImAB ks c) (.ofNat 0) 0) ^ 2 ≤ (dRzNum * pow2q) ^ 2 := by
  have ht2 : (checkRzSWAR192Word dRzNum chs cMid sMid eUlps).2 =
      (evalChunksSWAR192 chs swarInit192).t := by
    unfold checkRzSWAR192Word
    simp only [withForcedNat_eq]
    rw [evalChunksFast_eq]
    change _ = (evalChunksSWAR192 chs ⟨0, 0, swarOnes192, Nat.add swarOnes192 1, swarOnes192, 0⟩).t
    rcases evalChunksSWAR192 chs ⟨0, 0, swarOnes192, Nat.add swarOnes192 1, swarOnes192, 0⟩ with
      ⟨_, _, _, _, _, _⟩
    rfl
  rw [ht2]
  unfold checkRzSWAR192Word at hok
  rw [withForcedNat_eq, withForcedNat_eq, withForcedNat_eq, withForcedNat_eq, withForcedNat_eq]
    at hok
  rw [evalChunksFast_eq, show (⟨0, 0, swarOnes192, Nat.add swarOnes192 1, swarOnes192, 0⟩ :
    SWARState192) = swarInit192 from rfl] at hok
  generalize hsw : evalChunksSWAR192 chs swarInit192 = sw at hok ⊢
  rcases sw with ⟨k, p, B, A, C, tCnt⟩
  dsimp only at hok
  rcases hst : evalChunksSU2 chs FastSU2.init with ⟨ks, ps, a, c, ts⟩
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hk_ble, hp_beq⟩, hbound⟩ := hok
  have hk180 : (evalChunksSWAR192 chs swarInit192).k ≤ 180 := by
    rw [hsw]; exact Nat.ble_eq.mp hk_ble
  obtain ⟨a0, a1, a2, a3, c0, c1, c2, c3, hk_eq, hp_eq, ht_eq, hB, hA, hC, ha, hc⟩ :=
    evalChunksSWAR192_rel chs swarInit192_rel hk180
  rw [hsw] at hk_eq hp_eq ht_eq hB hA hC
  rw [hst] at hk_eq hp_eq ht_eq hB ha hc
  dsimp only at hk_eq hp_eq ht_eq hB hA hC ha hc
  cases hk_eq; cases ht_eq; subst hB hA hC
  have hp0 : ps = 0 := by
    rw [← hp_eq]; exact Nat.beq_eq.mp (by simpa [nat_mod_def_192] using hp_beq)
  subst hp0
  refine ⟨k, a, c, rfl, ?_⟩
  have hbW : 2 * 2 ^ k < swarW192 := two_mul_pow_lt_swarW192 (Nat.ble_eq.mp hk_ble)
  have hb1 : 2 ^ k < swarW192 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)) hbW
  have uB := (unpack4_192_eq (x0 := 2 ^ k) (x1 := 2 ^ k) (x2 := 2 ^ k) (x3 := 2 ^ k)
    hb1 hb1 hb1).1
  have uA := withUnpack4SWAR192_pack4 (α := Bool) (x3 := a3)
    (lt_of_le_of_lt ha.1 hbW) (lt_of_le_of_lt ha.2.1 hbW) (lt_of_le_of_lt ha.2.2.1 hbW)
  have uC := withUnpack4SWAR192_pack4 (α := Bool) (x3 := c3)
    (lt_of_le_of_lt hc.1 hbW) (lt_of_le_of_lt hc.2.1 hbW) (lt_of_le_of_lt hc.2.2.1 hbW)
  have ndiv2 (x : ℕ) : Nat.div x 2 = x / 2 := rfl
  rw [withForcedNat_eq, nat_mod_def_192, uB, withForcedNat_eq, withUnpack4Fast_eq, uA,
      withUnpack4Fast_eq, uC,
      withForcedNat_eq, ndiv2, Nat.add_eq, withForcedNat_eq, Nat.pow_eq,
      withForcedNat_eq, withForcedNat_eq, Nat.mul_eq, nat_mod_def_192] at hbound
  have hms : (sintNeg sMid : ℝ) - (sintPos sMid : ℝ) = sMid.opp.toReal := by
    rw [SInt.toReal_opp, ← sintPos_sub_sintNeg_192]; ring
  have hz0 : ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) = (SInt.ofNat 0).toReal := by simp [SInt.toReal_ofNat]
  cases hpar : Nat.beq (k % 2) 0 <;> rw [hpar] at hbound
  · simp only [withForcedNat_eq, Nat.mul_eq, Nat.add_eq, ← add_assoc] at hbound
    rw [coordRe192_false hpar ha (sintPos_sub_sintNeg_192 cMid), coordIm192_false hpar ha hms,
        coordRe192_false hpar hc hz0, coordIm192_false hpar hc hz0] at hbound
    simpa only [sq] using Nat.ble_eq.mp hbound
  · simp only [withForcedNat_eq, Nat.mul_eq, Nat.add_eq, ← add_assoc] at hbound
    rw [coordRe192_true hpar ha (sintPos_sub_sintNeg_192 cMid), coordIm192_true hpar ha hms,
        coordRe192_true hpar hc hz0, coordIm192_true hpar hc hz0] at hbound
    simpa only [sq] using Nat.ble_eq.mp hbound
end SWAR192Proofs

theorem checkRzSWAR192Word_sound {dRzNum : ℕ} {ch : List ℕ}
    {t : OuterWeights.SineWindowPrep.TrigCert} {θ : ℝ}
    (ht : t.Valid (θ / 2))
    (hok : (checkRzSWAR192Word dRzNum ch t.cMid t.sMid t.eUlps).1 = true) :
    ‖(OuterWeights.SineWindowPrep.wordToCircuit1 (decodeChunks ch)).eval.1 - SineQPE.rzMatrix θ‖ ≤
        (dRzNum : ℝ) / 10 ^ 24 ∧
      (checkRzSWAR192Word dRzNum ch t.cMid t.sMid t.eUlps).2 =
        OuterWeights.SineWindowPrep.wordCountT (decodeChunks ch) := by
  let w := decodeChunks ch
  obtain ⟨k, a, c, hst, hsum_nat⟩ :=
    checkRzSWAR192Word_extract dRzNum ch t.cMid t.sMid t.eUlps hok
  obtain ⟨hst_mat, hst_t⟩ := evalChunksSU2_equiv_192 ch FastSU2.init
  obtain ⟨hmat0, ht0⟩ := foldl_stepGateSU2_spec_192 (decodeChunks ch) FastSU2.init
  rw [← hst_mat, hst, fastSU2_init_toMatrix_192, Matrix.mul_one] at hmat0
  rw [← hst_t, hst, show FastSU2.init.tCnt = 0 from rfl, zero_add,
    OuterWeights.SineWindowPrep.count_wordToCircuit1_t] at ht0
  dsimp only at ht0
  refine ⟨?_, ht0⟩
  let U := (OuterWeights.SineWindowPrep.wordToCircuit1 w).eval
  have hUM : U.1 = toMatrix192 ⟨k, 0, a, c, _⟩ := hmat0.symm
  have hU00 : U.1 0 0 = (1 / (√2 : ℂ)) ^ k * a.toComplex := by rw [hUM]; rfl
  have hU10 : U.1 1 0 = (1 / (√2 : ℂ)) ^ k * c.toComplex := by rw [hUM]; rfl
  have hU_su2 : U.1 = SineQPE.su2Matrix (U.1 0 0) (U.1 1 0) := by
    rw [hU00, hU10, hUM]; exact fastSU2_p0_eq_su2Matrix_192 k a c _
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  let pow2q := 2 ^ (k / 2 + 1)
  let SP : ℝ := S * (pow2q : ℝ)
  have hSP_pos : 0 < SP := by dsimp only [SP, S, pow2q, scale24]; positivity
  have hcos : |Real.cos (θ / 2) - t.cMid.toReal / S| ≤ (t.eUlps : ℝ) / S := ht.1
  have hsin : |-Real.sin (θ / 2) - t.sMid.opp.toReal / S| ≤ (t.eUlps : ℝ) / S := by
    rw [OuterWeights.SineWindowPrep.SInt.toReal_opp,
      show -Real.sin (θ / 2) - -t.sMid.toReal / S = -(Real.sin (θ / 2) - t.sMid.toReal / S) by
        ring, abs_neg]
    exact ht.2
  have h0_bound :
      |(0 : ℝ) - (OuterWeights.SineWindowPrep.SInt.ofNat 0).toReal / S| ≤ ((0 : ℕ) : ℝ) / S := by
    simp only [SInt.toReal_ofNat, Nat.cast_zero, zero_div, sub_zero, abs_zero,
      le_refl]
  have hb1 := coordNumBound_spec (cycReAB_spec k a) hcos
  have hb2 := coordNumBound_spec (cycImAB_spec k a) hsin
  have hb3 := coordNumBound_spec (cycReAB_spec k c) h0_bound
  have hb4 := coordNumBound_spec (cycImAB_spec k c) h0_bound
  let n1 := coordNumBound pow2q (cycReAB k a) t.cMid t.eUlps
  let n2 := OuterWeights.SineWindowPrep.coordNumBound pow2q
    (OuterWeights.SineWindowPrep.cycImAB k a) t.sMid.opp t.eUlps
  let n3 := coordNumBound pow2q (cycReAB k c) (.ofNat 0) 0
  let n4 := coordNumBound pow2q (cycImAB k c) (.ofNat 0) 0
  have hsq1 : SP ^ 2 * ((U.1 0 0).re - Real.cos (θ / 2)) ^ 2 ≤ (n1 : ℝ) ^ 2 := by
    rw [← mul_pow, hU00, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
  have hsq2 : SP ^ 2 * ((U.1 0 0).im - (-Real.sin (θ / 2))) ^ 2 ≤ (n2 : ℝ) ^ 2 := by
    rw [← mul_pow, hU00, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb2 2
  have hsq3 : SP ^ 2 * ((U.1 1 0).re - 0) ^ 2 ≤ (n3 : ℝ) ^ 2 := by
    rw [← mul_pow, hU10, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb3 2
  have hsq4 : SP ^ 2 * ((U.1 1 0).im - 0) ^ 2 ≤ (n4 : ℝ) ^ 2 := by
    rw [← mul_pow, hU10, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb4 2
  dsimp only at hsum_nat
  have hsumR : (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 + (n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2 ≤
      ((dRzNum : ℝ) * (pow2q : ℝ)) ^ 2 := by
    exact_mod_cast hsum_nat
  have hdel : (dRzNum : ℝ) * (pow2q : ℝ) = SP * ((dRzNum : ℝ) / 10 ^ 24) := by
    dsimp only [SP, S, OuterWeights.SineWindowPrep.scale24]; ring
  rw [hdel, mul_pow] at hsumR
  have hscaled :
      SP ^ 2 * (((U.1 0 0).re - Real.cos (θ / 2)) ^ 2 +
        ((U.1 0 0).im - (-Real.sin (θ / 2))) ^ 2 +
        ((U.1 1 0).re - 0) ^ 2 + ((U.1 1 0).im - 0) ^ 2) ≤
      SP ^ 2 * ((dRzNum : ℝ) / 10 ^ 24) ^ 2 := by
    rw [mul_add, mul_add, mul_add]
    exact (add_le_add (add_le_add (add_le_add hsq1 hsq2) hsq3) hsq4).trans hsumR
  have hsum_err := le_of_mul_le_mul_left hscaled (sq_pos_of_pos hSP_pos)
  rw [hU_su2, SineQPE.rzMatrix_eq_su2Matrix]
  apply SineQPE.norm_su2Matrix_sub_le (by positivity)
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im, zero_mul,
    one_mul, zero_add, sub_zero]
  linarith only [hsum_err]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Swar192

/-! ## Section 2: Zero-Ancilla Two-Gear Sine-Window Synthesis & Scale-24 `L²` Verifier -/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearQPEPhase5
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastUniform
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.UpperBound
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.BlockReflection
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.ApproxIqft16
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.PhaseSwar
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16
  CleanWalkRefl2 WalkRefl2ErrLe P450RefVarBound ReordSosHyp RealizesP450GroundQPE
  tensorWalkCat_smul_right
  approxPhaseGrad11Ray exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar
  exactPhaseGrad11RayUnitary_mulVec_zero approxPhaseGrad11Ray_count_toff
  approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le
)
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CoherentAlias
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox
open OuterWeights.SineWindowPrep (
  SInt TrigCert VecApprox addTrig addTrig_valid count_wordToCircuit1_t count_wordToCircuit1_toff
  evolve_CNOT_ket evolve_H_ket evolve_X_ket evolve_Z_ket iterDoubleTrig iterDoubleTrig_valid
  ket_basisBits mkStrictSInt mkStrictSInt_eq qubitX_mul_ryUnitary_mul_qubitX ryUnitary
  ryUnitary_mul scale24 su2RealUnitary withForcedBool withForcedBool_eq withForcedNat
  withForcedNat_eq withForcedTrigRes withForcedTrigRes_eq wordToCircuit1)
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowInlineTG (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-- Rational Weierstrass denominator scale `10 ^ 15` (`tan(θ / 4) = p / 10 ^ 15`). -/
def weierQ : ℕ := 1000000000000000

/-- Per-leaf `Rz`/`Ry` synthesis spectral-norm tolerance numerator `8 * 10 ^ 11` (`8e-13`). -/
def dRzLeafNum : ℕ := 800000000000

/-- Exact rational-Weierstrass `Ry` rotation angle `θ = 4 * arctan(p / 10 ^ 15)` whose half-angle
has exact rational `(cos(θ / 2), sin(θ / 2)) = ((Q^2 - p^2)/(Q^2 + p^2), 2 p Q / (Q^2 + p^2))`. -/
noncomputable def weierAngle (p : OuterWeights.SineWindowPrep.SInt) : ℝ :=
  4 * Real.arctan (p.toReal / (weierQ : ℝ))

theorem sInt_toReal_sq (p : OuterWeights.SineWindowPrep.SInt) :
    p.toReal ^ 2 = ((p.mag * p.mag : ℕ) : ℝ) := by
  cases h : p.neg <;> simp [OuterWeights.SineWindowPrep.SInt.toReal, h, sq, Nat.cast_mul]

theorem cos_sin_half_weierAngle (p : OuterWeights.SineWindowPrep.SInt) :
    let den : ℝ := ((weierQ * weierQ + p.mag * p.mag : ℕ) : ℝ)
    Real.cos (weierAngle p / 2) =
        (((weierQ * weierQ : ℕ) : ℝ) - ((p.mag * p.mag : ℕ) : ℝ)) / den ∧
      Real.sin (weierAngle p / 2) = (2 * p.toReal * (weierQ : ℝ)) / den := by
  intro den
  let Q : ℝ := (weierQ : ℝ)
  have hQ_pos : 0 < Q := by dsimp [Q, weierQ]; positivity
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
  let x : ℝ := p.toReal / Q
  let φ : ℝ := Real.arctan x
  have hhalf : weierAngle p / 2 = 2 * φ := by dsimp [weierAngle, φ, x]; ring
  have h1x_pos : 0 < 1 + x ^ 2 := by positivity
  have h1x_ne : 1 + x ^ 2 ≠ 0 := ne_of_gt h1x_pos
  have hsq : √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt h1x_pos.le
  have hsqrt_ne : √(1 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1x_pos)
  have hpsq : p.toReal ^ 2 = ((p.mag * p.mag : ℕ) : ℝ) := sInt_toReal_sq p
  have hden_eq : den = Q ^ 2 + p.toReal ^ 2 := by
    dsimp [den, Q]; rw [hpsq]; push_cast; ring
  have hden_pos : 0 < den := by rw [hden_eq]; positivity
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  rw [hhalf]
  constructor
  · rw [Real.cos_two_mul, Real.cos_arctan, div_pow, _root_.one_pow, hsq]
    have hcalc : 2 * (1 / (1 + x ^ 2)) - 1 = (1 - x ^ 2) / (1 + x ^ 2) := by
      field_simp [h1x_ne]; ring
    rw [hcalc]
    dsimp only [x]
    rw [hden_eq, ← hpsq]
    have hQ2 : ((weierQ * weierQ : ℕ) : ℝ) = Q ^ 2 := by dsimp [Q]; push_cast; ring
    rw [hQ2]
    field_simp [hQ_ne, h1x_ne, hden_ne]
  · rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hmul : 2 * (x / √(1 + x ^ 2)) * (1 / √(1 + x ^ 2)) =
        (2 * x) / (√(1 + x ^ 2) ^ 2) := by ring
    rw [hmul, hsq]
    dsimp only [x]
    rw [hden_eq]
    field_simp [hQ_ne, h1x_ne, hden_ne]
    dsimp only [Q]

/-- Precomputed `weierQ ^ 2 = 10 ^ 30` literal for fast kernel arithmetic. -/
def weierQ2 : ℕ := 1000000000000000000000000000000

theorem weierQ2_eq : weierQ2 = weierQ * weierQ := by decide

/-- Precomputed `2 * weierQ = 2 * 10 ^ 15` literal for fast kernel arithmetic. -/
def twoWeierQ : ℕ := 2000000000000000

theorem twoWeierQ_eq : twoWeierQ = 2 * weierQ := by decide

/-- Strict multiplication on `SInt` avoiding `HMul` typeclass unfolding in `decide +kernel`. -/
def mulStrictSInt (x y : OuterWeights.SineWindowPrep.SInt) : OuterWeights.SineWindowPrep.SInt :=
  OuterWeights.SineWindowPrep.SInt.casesOn x fun nx mx ↦
  OuterWeights.SineWindowPrep.SInt.casesOn y fun ny my ↦
  OuterWeights.SineWindowPrep.withForcedBool (bne nx ny) fun n ↦
  OuterWeights.SineWindowPrep.mkStrictSInt n (Nat.mul mx my)

@[simp]
theorem mulStrictSInt_eq (x y : SInt) : mulStrictSInt x y = x.mul y := by
  rcases x with ⟨nx, mx⟩; rcases y with ⟨ny, my⟩
  simp only [mulStrictSInt, SInt.mul, withForcedBool_eq,
    OuterWeights.SineWindowPrep.mkStrictSInt_eq, Nat.mul_eq]

/-- Pure-`ℕ` `1`-ulp Weierstrass midpoint check for `(p, cMid, sMid)` at `scale24 = 10 ^ 24`. -/
def checkWeierLeaf (p cMid sMid : OuterWeights.SineWindowPrep.SInt) : Bool :=
  OuterWeights.SineWindowPrep.withForcedNat (Nat.mul p.mag p.mag) fun p2 ↦
  OuterWeights.SineWindowPrep.withForcedNat (Nat.add weierQ2 p2) fun den ↦
  OuterWeights.SineWindowPrep.withForcedNat OuterWeights.SineWindowPrep.scale24 fun s24 ↦
  let numC := (OuterWeights.SineWindowPrep.SInt.ofNat weierQ2).subStrict
    (OuterWeights.SineWindowPrep.SInt.ofNat p2)
  let numS := mulStrictSInt p (OuterWeights.SineWindowPrep.SInt.ofNat twoWeierQ)
  let diffC := (mulStrictSInt numC (OuterWeights.SineWindowPrep.SInt.ofNat s24)).subStrict
    (mulStrictSInt cMid (OuterWeights.SineWindowPrep.SInt.ofNat den))
  let diffS := (mulStrictSInt numS (OuterWeights.SineWindowPrep.SInt.ofNat s24)).subStrict
    (mulStrictSInt sMid (OuterWeights.SineWindowPrep.SInt.ofNat den))
  Nat.ble diffC.mag den && Nat.ble diffS.mag den

theorem checkWeierLeaf_valid {p cMid sMid : OuterWeights.SineWindowPrep.SInt}
    (hok : checkWeierLeaf p cMid sMid = true) :
    (⟨cMid, sMid, 1⟩ : OuterWeights.SineWindowPrep.TrigCert).Valid (weierAngle p / 2) := by
  dsimp only [checkWeierLeaf] at hok
  simp only [OuterWeights.SineWindowPrep.withForcedNat_eq, mulStrictSInt_eq,
    OuterWeights.SineWindowPrep.SInt.subStrict_eq, weierQ2_eq, twoWeierQ_eq,
    Nat.mul_eq, Nat.add_eq, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hc_nat, hs_nat⟩ := hok
  obtain ⟨hcos_eq, hsin_eq⟩ := cos_sin_half_weierAngle p
  let denNat := weierQ * weierQ + p.mag * p.mag
  let den : ℝ := (denNat : ℝ)
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  have hden_pos : 0 < den := by dsimp [den, denNat, weierQ]; positivity
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hdenS_pos : 0 < den * S := mul_pos hden_pos hS_pos
  dsimp only [OuterWeights.SineWindowPrep.TrigCert.Valid]
  rw [hcos_eq, hsin_eq]
  constructor
  · let diffC := ((OuterWeights.SineWindowPrep.SInt.ofNat (weierQ * weierQ)).sub
      (OuterWeights.SineWindowPrep.SInt.ofNat (p.mag * p.mag))).mul
        (OuterWeights.SineWindowPrep.SInt.ofNat OuterWeights.SineWindowPrep.scale24) |>.sub
          (cMid.mul (OuterWeights.SineWindowPrep.SInt.ofNat denNat))
    have habs : |diffC.toReal| ≤ den := by
      rw [OuterWeights.SineWindowPrep.SInt.abs_toReal]
      dsimp only [diffC, den, denNat]
      exact Nat.cast_le.mpr hc_nat
    have hval : diffC.toReal =
        (((weierQ * weierQ : ℕ) : ℝ) - ((p.mag * p.mag : ℕ) : ℝ)) * S - cMid.toReal * den := by
      dsimp only [diffC, S, den]
      simp only [SInt.toReal_sub, SInt.toReal_mul,
        OuterWeights.SineWindowPrep.SInt.toReal_ofNat]
    have hquot :
        (((weierQ * weierQ : ℕ) : ℝ) - ((p.mag * p.mag : ℕ) : ℝ)) / den - cMid.toReal / S =
          diffC.toReal / (den * S) := by
      rw [hval]; field_simp [hden_ne, hS_ne]
    rw [hquot, abs_div, abs_of_pos hdenS_pos, Nat.cast_one]
    rw [div_le_div_iff₀ hdenS_pos hS_pos]
    calc |diffC.toReal| * S ≤ den * S := mul_le_mul_of_nonneg_right habs hS_pos.le
      _ = 1 * (den * S) := by ring
  · let diffS := (p.mul (OuterWeights.SineWindowPrep.SInt.ofNat (2 * weierQ))).mul
        (OuterWeights.SineWindowPrep.SInt.ofNat OuterWeights.SineWindowPrep.scale24) |>.sub
          (sMid.mul (OuterWeights.SineWindowPrep.SInt.ofNat denNat))
    have habs : |diffS.toReal| ≤ den := by
      rw [OuterWeights.SineWindowPrep.SInt.abs_toReal]
      dsimp only [diffS, den, denNat]
      exact Nat.cast_le.mpr hs_nat
    have hval : diffS.toReal = (2 * p.toReal * (weierQ : ℝ)) * S - sMid.toReal * den := by
      dsimp only [diffS, S, den]
      simp only [SInt.toReal_sub, SInt.toReal_mul,
        OuterWeights.SineWindowPrep.SInt.toReal_ofNat, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hquot : (2 * p.toReal * (weierQ : ℝ)) / den - sMid.toReal / S =
        diffS.toReal / (den * S) := by
      rw [hval]; field_simp [hden_ne, hS_ne]
    rw [hquot, abs_div, abs_of_pos hdenS_pos, Nat.cast_one]
    rw [div_le_div_iff₀ hdenS_pos hS_pos]
    calc |diffS.toReal| * S ≤ den * S := mul_le_mul_of_nonneg_right habs hS_pos.le
      _ = 1 * (den * S) := by ring

/-- Non-dependent Walsh-multiplexed `Ry` synthesis tree (`0` implicit depth indices for fast
kernel reduction). -/
inductive WordPairTree : Type where
  /-- Pruned zero-angle subtree (`0` gates). -/
  | skip : WordPairTree
  /-- Single-qubit `Ry` leaf encoded as SWAR `Rz` chunks + Weierstrass midpoint certificate. -/
  | leaf (ch : List ℕ) (p cMid sMid : OuterWeights.SineWindowPrep.SInt) : WordPairTree
  /-- Binary Walsh split applying `tP`, `CNOT`, `tM`, `CNOT`. -/
  | branch (tP tM : WordPairTree) : WordPairTree

/-- Negate the sine midpoint of a `TrigCert` (`cos(-α) = cos α`, `sin(-α) = -sin α`). -/
def negSinTrig (t : OuterWeights.SineWindowPrep.TrigCert) : OuterWeights.SineWindowPrep.TrigCert :=
  ⟨t.cMid, t.sMid.oppStrict, t.eUlps⟩

theorem negSinTrig_valid {t : OuterWeights.SineWindowPrep.TrigCert} {α : ℝ} (h : t.Valid α) :
    (negSinTrig t).Valid (-α) := by
  dsimp only [negSinTrig, OuterWeights.SineWindowPrep.TrigCert.Valid]
  rw [OuterWeights.SineWindowPrep.SInt.oppStrict_eq, Real.cos_neg, Real.sin_neg,
    OuterWeights.SineWindowPrep.SInt.toReal_opp]
  refine ⟨h.1, ?_⟩
  have heq : -Real.sin α - -t.sMid.toReal / (OuterWeights.SineWindowPrep.scale24 : ℝ) =
      -(Real.sin α - t.sMid.toReal / (OuterWeights.SineWindowPrep.scale24 : ℝ)) := by ring
  rw [heq, abs_neg]
  exact h.2

/-- Pointwise angle-addition `TrigCert` combiner with CPS forcing for `decide +kernel`. -/
def zipAddTrig :
    List OuterWeights.SineWindowPrep.TrigCert → List OuterWeights.SineWindowPrep.TrigCert →
      Bool × List OuterWeights.SineWindowPrep.TrigCert
  | [], [] => (true, [])
  | a :: as, b :: bs =>
      withForcedTrigRes (addTrig a b) fun t1 ok1 ↦
      Prod.casesOn (zipAddTrig as bs) fun okR tsR ↦
      OuterWeights.SineWindowPrep.withForcedBool (ok1 && okR) fun ok ↦
        (ok, t1 :: tsR)
  | _, _ => (false, [])

/-- Pointwise angle-subtraction `TrigCert` combiner with CPS forcing for `decide +kernel`. -/
def zipSubTrig :
    List OuterWeights.SineWindowPrep.TrigCert → List OuterWeights.SineWindowPrep.TrigCert →
      Bool × List OuterWeights.SineWindowPrep.TrigCert
  | [], [] => (true, [])
  | a :: as, b :: bs =>
      withForcedTrigRes (addTrig a (negSinTrig b))
        fun t1 ok1 ↦
      Prod.casesOn (zipSubTrig as bs) fun okR tsR ↦
      OuterWeights.SineWindowPrep.withForcedBool (ok1 && okR) fun ok ↦
        (ok, t1 :: tsR)
  | _, _ => (false, [])

/-- Force the head cons cell of `l : List α` to WHNF for `decide +kernel`. -/
def withForcedList {α β : Type} (l : List α) (f : List α → β) : β :=
  (List.casesOn (motive := fun _ ↦ (List α → β) → β) l
    (fun k ↦ k []) (fun x xs k ↦ k (x :: xs))) f

@[simp]
theorem withForcedList_eq {α β : Type} (l : List α) (f : List α → β) :
    withForcedList l f = f l := by
  cases l <;> rfl

/-- Pure-`ℕ` evaluator for `WordPairTree` at control depth `k`, returning
`(ok, trigs_of_half_angles, leafCount, tCount)`. -/
def evalWordPairTree : ℕ → WordPairTree → Bool × List OuterWeights.SineWindowPrep.TrigCert × ℕ × ℕ
  | k, .skip =>
      OuterWeights.SineWindowPrep.withForcedNat (2 ^ k) fun len ↦
        (true, List.replicate len ⟨.ofNat OuterWeights.SineWindowPrep.scale24, .ofNat 0, 0⟩, 0, 0)
  | 0, .leaf ch p cMid sMid =>
      Prod.casesOn (Swar192.checkRzSWAR192Word dRzLeafNum ch cMid sMid 1) fun okSw tSw ↦
      OuterWeights.SineWindowPrep.withForcedBool (checkWeierLeaf p cMid sMid && okSw) fun ok ↦
        (ok, [⟨cMid, sMid, 1⟩], 1, tSw)
  | _ + 1, .leaf _ _ _ _ => (false, [], 0, 0)
  | 0, .branch _ _ => (false, [], 0, 0)
  | k + 1, .branch tP tM =>
      Prod.casesOn (evalWordPairTree k tP) fun okP rP1 ↦
      Prod.casesOn rP1 fun trP rP2 ↦
      Prod.casesOn rP2 fun nlP tcP ↦
      Prod.casesOn (evalWordPairTree k tM) fun okM rM1 ↦
      Prod.casesOn rM1 fun trM rM2 ↦
      Prod.casesOn rM2 fun nlM tcM ↦
      Prod.casesOn (zipAddTrig trP trM) fun okL trL ↦
      Prod.casesOn (zipSubTrig trP trM) fun okR trR ↦
      OuterWeights.SineWindowPrep.withForcedBool (okP && okM && okL && okR) fun ok ↦
      OuterWeights.SineWindowPrep.withForcedNat (nlP + nlM) fun nl ↦
      OuterWeights.SineWindowPrep.withForcedNat (tcP + tcM) fun tc ↦
      withForcedList (trL ++ trR) fun trLR ↦
        (ok, trLR, nl, tc)

/-- Ideal angle vector `Fin (2 ^ k) → ℝ` realized by `t : WordPairTree` at depth `k`. -/
noncomputable def wordPairTreeIdeal : (k : ℕ) → WordPairTree → Fin (2 ^ k) → ℝ
  | _, .skip => fun _ ↦ 0
  | 0, .leaf _ p _ _ => fun _ ↦ weierAngle p
  | _ + 1, .leaf _ _ _ _ => fun _ ↦ 0
  | 0, .branch _ _ => fun _ ↦ 0
  | k + 1, .branch tP tM => fun c ↦
      let cLo : Fin (2 ^ k) := ⟨c.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
      if c.val < 2 ^ k then wordPairTreeIdeal k tP cLo + wordPairTreeIdeal k tM cLo
      else wordPairTreeIdeal k tP cLo - wordPairTreeIdeal k tM cLo

/-- Ancilla-free `Circuit n` implementing `t : WordPairTree` on `tgt` controlled by `rCtrl`. -/
def wordPairTreeCircuit {n : ℕ} :
    (k : ℕ) → (rCtrl : QRegister k n) → (tgt : Wire n) →
      (rCtrl.DisjointWires (QRegister.singleton tgt)) → WordPairTree → Circuit n
  | _, _, _, _, .skip => Circuit.identity
  | 0, _, tgt, _, .leaf ch _ _ _ =>
      (SineQPE.rzToRyCircuit (wordToCircuit1 (decodeChunks ch))).onRegister
        (QRegister.singleton tgt)
  | _ + 1, _, _, _, .leaf _ _ _ _ => Circuit.identity
  | 0, _, _, _, .branch _ _ => Circuit.identity
  | k + 1, rCtrl, tgt, hdisj, .branch tP tM =>
      let rLo := rCtrl.slice 0 k (by omega)
      let wTop := rCtrl ⟨k, by omega⟩
      have hLo : rLo.DisjointWires (QRegister.singleton tgt) := by
        rw [QRegister.disjoint_iff] at hdisj ⊢
        intro i j hij
        exact hdisj ⟨i.val, by omega⟩ j (by simpa [rLo] using hij)
      have hwTop : wTop ≠ tgt := by
        rw [QRegister.disjoint_iff] at hdisj
        intro heq
        exact hdisj ⟨k, by omega⟩ 0 (by simpa [wTop] using heq)
      Circuit.sequence [
        wordPairTreeCircuit k rLo tgt hLo tP,
        Circuit.CNOT wTop tgt hwTop,
        wordPairTreeCircuit k rLo tgt hLo tM,
        Circuit.CNOT wTop tgt hwTop]

theorem zipAddTrig_spec :
    ∀ (as bs : List OuterWeights.SineWindowPrep.TrigCert) (f g : ℕ → ℝ),
      as.length = bs.length →
      (∀ i (hi : i < as.length), (as[i]'hi).Valid (f i)) →
      (∀ i (hi : i < bs.length), (bs[i]'hi).Valid (g i)) →
      (zipAddTrig as bs).1 = true →
      (zipAddTrig as bs).2.length = as.length ∧
        ∀ i (hi : i < (zipAddTrig as bs).2.length),
          ((zipAddTrig as bs).2[i]'hi).Valid (f i + g i)
  | [], [], _, _, _, _, _, _ => ⟨rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | a :: as, b :: bs, f, g, hlen, ha, hb, hok => by
      dsimp only [zipAddTrig] at hok ⊢
      simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq,
        OuterWeights.SineWindowPrep.withForcedBool_eq, Bool.and_eq_true] at hok ⊢
      have hlen' : as.length = bs.length := Nat.succ.inj hlen
      obtain ⟨ih_len, ih_val⟩ := zipAddTrig_spec as bs (fun i ↦ f (i + 1)) (fun i ↦ g (i + 1))
        hlen' (fun i hi ↦ ha (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi ↦ hb (i + 1) (Nat.succ_lt_succ hi)) hok.2
      refine ⟨congrArg Nat.succ ih_len, fun i hi ↦ ?_⟩
      cases i with
      | zero =>
          dsimp only [List.getElem_cons_zero]
          exact OuterWeights.SineWindowPrep.addTrig_valid (ha 0 (Nat.zero_lt_succ _))
            (hb 0 (Nat.zero_lt_succ _)) hok.1
      | succ j => exact ih_val j (Nat.lt_of_succ_lt_succ hi)
  | _ :: _, [], _, _, hlen, _, _, _ => absurd hlen (Nat.succ_ne_zero _)
  | [], _ :: _, _, _, hlen, _, _, _ => absurd hlen.symm (Nat.succ_ne_zero _)

theorem zipSubTrig_spec :
    ∀ (as bs : List OuterWeights.SineWindowPrep.TrigCert) (f g : ℕ → ℝ),
      as.length = bs.length →
      (∀ i (hi : i < as.length), (as[i]'hi).Valid (f i)) →
      (∀ i (hi : i < bs.length), (bs[i]'hi).Valid (g i)) →
      (zipSubTrig as bs).1 = true →
      (zipSubTrig as bs).2.length = as.length ∧
        ∀ i (hi : i < (zipSubTrig as bs).2.length),
          ((zipSubTrig as bs).2[i]'hi).Valid (f i - g i)
  | [], [], _, _, _, _, _, _ => ⟨rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | a :: as, b :: bs, f, g, hlen, ha, hb, hok => by
      dsimp only [zipSubTrig] at hok ⊢
      simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq,
        OuterWeights.SineWindowPrep.withForcedBool_eq, Bool.and_eq_true] at hok ⊢
      have hlen' : as.length = bs.length := Nat.succ.inj hlen
      obtain ⟨ih_len, ih_val⟩ := zipSubTrig_spec as bs (fun i ↦ f (i + 1)) (fun i ↦ g (i + 1))
        hlen' (fun i hi ↦ ha (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi ↦ hb (i + 1) (Nat.succ_lt_succ hi)) hok.2
      refine ⟨congrArg Nat.succ ih_len, fun i hi ↦ ?_⟩
      cases i with
      | zero =>
          dsimp only [List.getElem_cons_zero]
          rw [sub_eq_add_neg]
          exact OuterWeights.SineWindowPrep.addTrig_valid (ha 0 (Nat.zero_lt_succ _))
            (negSinTrig_valid (hb 0 (Nat.zero_lt_succ _))) hok.1
      | succ j => exact ih_val j (Nat.lt_of_succ_lt_succ hi)
  | _ :: _, [], _, _, hlen, _, _, _ => absurd hlen (Nat.succ_ne_zero _)
  | [], _ :: _, _, _, hlen, _, _, _ => absurd hlen.symm (Nat.succ_ne_zero _)

theorem evalWordPairTree_trigs :
    ∀ (k : ℕ) (t : WordPairTree),
      (evalWordPairTree k t).1 = true →
      ∃ (hlen : (evalWordPairTree k t).2.1.length = 2 ^ k),
        ∀ (c : Fin (2 ^ k)),
          ((evalWordPairTree k t).2.1[c.val]'(c.isLt.trans_eq hlen.symm)).Valid
            (wordPairTreeIdeal k t c / 2)
  | k, .skip, _ => by
      simp only [evalWordPairTree, wordPairTreeIdeal, OuterWeights.SineWindowPrep.withForcedNat_eq]
      refine ⟨List.length_replicate, fun c ↦ ?_⟩
      simp only [List.getElem_replicate, zero_div, Real.cos_zero, Real.sin_zero,
        TrigCert.Valid, SInt.toReal_ofNat, Nat.cast_zero,
        zero_div, sub_zero, abs_zero]
      have hS_ne : (OuterWeights.SineWindowPrep.scale24 : ℝ) ≠ 0 := by
        norm_num [OuterWeights.SineWindowPrep.scale24]
      rw [div_self hS_ne, sub_self, abs_zero]
      exact ⟨le_rfl, le_rfl⟩
  | 0, .leaf ch p cMid sMid, hok => by
      simp only [evalWordPairTree, wordPairTreeIdeal,
        OuterWeights.SineWindowPrep.withForcedBool_eq, Bool.and_eq_true] at hok ⊢
      refine ⟨rfl, fun c ↦ ?_⟩
      have hc0 : c.val = 0 := by omega
      simp only [hc0, List.getElem_cons_zero]
      exact checkWeierLeaf_valid hok.1
  | _ + 1, .leaf _ _ _ _, hok => by simp [evalWordPairTree] at hok
  | 0, .branch _ _, hok => by simp [evalWordPairTree] at hok
  | k + 1, .branch tP tM, hok => by
      simp only [evalWordPairTree, OuterWeights.SineWindowPrep.withForcedBool_eq,
        OuterWeights.SineWindowPrep.withForcedNat_eq, withForcedList_eq, Bool.and_eq_true] at hok ⊢
      obtain ⟨⟨⟨hokP, hokM⟩, hokL⟩, hokR⟩ := hok
      obtain ⟨hlenP, hvalP⟩ := evalWordPairTree_trigs k tP hokP
      obtain ⟨hlenM, hvalM⟩ := evalWordPairTree_trigs k tM hokM
      set rP := (evalWordPairTree k tP).2.1
      set rM := (evalWordPairTree k tM).2.1
      let fP : ℕ → ℝ := fun i ↦
        if hi : i < 2 ^ k then wordPairTreeIdeal k tP ⟨i, hi⟩ / 2 else 0
      let fM : ℕ → ℝ := fun i ↦
        if hi : i < 2 ^ k then wordPairTreeIdeal k tM ⟨i, hi⟩ / 2 else 0
      obtain ⟨hlenL, hvalL⟩ := zipAddTrig_spec rP rM fP fM (hlenP.trans hlenM.symm)
        (fun i hi ↦ by
          have hi' : i < 2 ^ k := hi.trans_eq hlenP
          simpa [fP, hi'] using hvalP ⟨i, hi'⟩)
        (fun i hi ↦ by
          have hi' : i < 2 ^ k := hi.trans_eq hlenM
          simpa [fM, hi'] using hvalM ⟨i, hi'⟩) hokL
      obtain ⟨hlenR, hvalR⟩ := zipSubTrig_spec rP rM fP fM (hlenP.trans hlenM.symm)
        (fun i hi ↦ by
          have hi' : i < 2 ^ k := hi.trans_eq hlenP
          simpa [fP, hi'] using hvalP ⟨i, hi'⟩)
        (fun i hi ↦ by
          have hi' : i < 2 ^ k := hi.trans_eq hlenM
          simpa [fM, hi'] using hvalM ⟨i, hi'⟩) hokR
      have htot : ((zipAddTrig rP rM).2 ++ (zipSubTrig rP rM).2).length = 2 ^ (k + 1) := by
        rw [List.length_append, hlenL, hlenR, hlenP, pow_succ]; omega
      refine ⟨htot, fun c ↦ ?_⟩
      by_cases hc : c.val < 2 ^ k
      · have hltL : c.val < (zipAddTrig rP rM).2.length := by rw [hlenL, hlenP]; exact hc
        rw [List.getElem_append_left hltL]
        have hv := hvalL c.val hltL
        have hmod : c.val % 2 ^ k = c.val := Nat.mod_eq_of_lt hc
        have hcLo : (⟨c.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) =
            ⟨c.val, hc⟩ := Fin.ext hmod
        simp only [wordPairTreeIdeal, hc, ↓reduceIte, hcLo]
        rw [show (wordPairTreeIdeal k tP ⟨c.val, hc⟩ + wordPairTreeIdeal k tM ⟨c.val, hc⟩) / 2 =
          fP c.val + fM c.val by dsimp [fP, fM]; simp [hc]; ring]
        exact hv
      · have hge : 2 ^ k ≤ c.val := Nat.le_of_not_lt hc
        have hgeL : (zipAddTrig rP rM).2.length ≤ c.val := by rw [hlenL, hlenP]; exact hge
        have hsub_lt : c.val - 2 ^ k < 2 ^ k := by
          have hc_lt : c.val < 2 ^ k * 2 := c.isLt.trans_eq (pow_succ 2 k)
          omega
        have hltR : c.val - (zipAddTrig rP rM).2.length < (zipSubTrig rP rM).2.length := by
          rw [hlenL, hlenR, hlenP]; exact hsub_lt
        rw [List.getElem_append_right hgeL]
        have hidx : c.val - (zipAddTrig rP rM).2.length = c.val - 2 ^ k := by rw [hlenL, hlenP]
        have hv := hvalR (c.val - (zipAddTrig rP rM).2.length) hltR
        have hmod : c.val % 2 ^ k = c.val - 2 ^ k := by
          have heq : c.val = (c.val - 2 ^ k) + 2 ^ k * 1 := by omega
          conv_lhs => rw [heq]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub_lt]
        have hcLo : (⟨c.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) =
            ⟨c.val - 2 ^ k, hsub_lt⟩ := Fin.ext hmod
        simp only [wordPairTreeIdeal, hc, ↓reduceIte, hcLo]
        rw [show (wordPairTreeIdeal k tP ⟨c.val - 2 ^ k, hsub_lt⟩ -
            wordPairTreeIdeal k tM ⟨c.val - 2 ^ k, hsub_lt⟩) / 2 =
          fP (c.val - (zipAddTrig rP rM).2.length) -
            fM (c.val - (zipAddTrig rP rM).2.length) by
          rw [hidx]; dsimp [fP, fM]; simp [hsub_lt]; ring]
        exact hv

theorem vecApprox_of_opNorm_le {d : ℕ} {U V : Unitary d} {ε : ℝ}
    (h : ‖U.1 - V.1‖ ≤ ε) : OuterWeights.SineWindowPrep.VecApprox U V ε := by
  intro ψ
  let v : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 ψ
  have heq : WithLp.toLp 2 (U.1 *ᵥ ψ - V.1 *ᵥ ψ) = WithLp.toLp 2 ((U.1 - V.1) *ᵥ ψ) := by
    rw [Matrix.sub_mulVec]
  rw [heq]
  exact (Matrix.l2_opNorm_mulVec (U.1 - V.1) v).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg v))

theorem ryUnitary_coe_eq_ryMatrix (θ : ℝ) :
    (OuterWeights.SineWindowPrep.ryUnitary θ).1 = SineQPE.ryMatrix θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryUnitary, su2RealUnitary, SineQPE.ryMatrix]

/-- Ideal `n`-qubit unitary realized by `WordPairTree` at control depth `k`. -/
noncomputable def wordPairTreeIdealU {n : ℕ} :
    (k : ℕ) → (rCtrl : QRegister k n) → (tgt : Wire n) →
      rCtrl.DisjointWires (QRegister.singleton tgt) → WordPairTree → Unitary (2 ^ n)
  | _, _, _, _, .skip => 1
  | 0, _, tgt, _, .leaf _ p _ _ =>
      (QRegister.singleton tgt).embedUnitary (OuterWeights.SineWindowPrep.ryUnitary (weierAngle p))
  | k + 1, rCtrl, tgt, hdisj, .branch tP tM =>
      let rLo := rCtrl.slice 0 k (by omega)
      let wTop := rCtrl ⟨k, by omega⟩
      have hLo : rLo.DisjointWires (QRegister.singleton tgt) := by
        rw [QRegister.disjoint_iff] at hdisj ⊢
        intro i j hij
        exact hdisj ⟨i.val, by omega⟩ j (by simpa [rLo] using hij)
      have hwTop : wTop ≠ tgt := by
        rw [QRegister.disjoint_iff] at hdisj
        intro heq
        exact hdisj ⟨k, by omega⟩ 0 (by simpa [wTop] using heq)
      (Circuit.CNOT wTop tgt hwTop).eval *
        (wordPairTreeIdealU k rLo tgt hLo tM *
          ((Circuit.CNOT wTop tgt hwTop).eval * wordPairTreeIdealU k rLo tgt hLo tP))
  | _ + 1, _, _, _, .leaf _ _ _ _ => 1
  | 0, _, _, _, .branch _ _ => 1

theorem wordPairTreeCircuit_spec {n : ℕ} :
    ∀ (k : ℕ) (rCtrl : QRegister k n) (tgt : Wire n)
      (hdisj : rCtrl.DisjointWires (QRegister.singleton tgt)) (t : WordPairTree),
      (evalWordPairTree k t).1 = true →
      (wordPairTreeCircuit k rCtrl tgt hdisj t).count .TOFF = 0 ∧
        (wordPairTreeCircuit k rCtrl tgt hdisj t).count .T = (evalWordPairTree k t).2.2.2 ∧
        OuterWeights.SineWindowPrep.VecApprox (wordPairTreeCircuit k rCtrl tgt hdisj t).eval
          (wordPairTreeIdealU k rCtrl tgt hdisj t)
          (((evalWordPairTree k t).2.2.1 : ℝ) * ((dRzLeafNum : ℝ) / 10 ^ 24))
  | k, rCtrl, tgt, hdisj, .skip, _ => by
      simp only [wordPairTreeCircuit, wordPairTreeIdealU, evalWordPairTree,
        OuterWeights.SineWindowPrep.withForcedNat_eq]
      refine ⟨by simp, by simp, ?_⟩
      simpa [Circuit.eval] using OuterWeights.SineWindowPrep.VecApprox.refl (1 : Unitary (2 ^ n))
  | 0, rCtrl, tgt, hdisj, .leaf ch p cMid sMid, hok => by
      simp only [wordPairTreeCircuit, wordPairTreeIdealU, evalWordPairTree,
        OuterWeights.SineWindowPrep.withForcedBool_eq, Bool.and_eq_true] at hok ⊢
      have hvalid := checkWeierLeaf_valid hok.1
      obtain ⟨hnorm_rz, hcnt⟩ := Swar192.checkRzSWAR192Word_sound hvalid hok.2
      have hnorm_ry :
          ‖(SineQPE.rzToRyCircuit
              (OuterWeights.SineWindowPrep.wordToCircuit1 (decodeChunks ch))).eval.1 -
              (OuterWeights.SineWindowPrep.ryUnitary (weierAngle p)).1‖ ≤
            (dRzLeafNum : ℝ) / 10 ^ 24 := by
        rw [ryUnitary_coe_eq_ryMatrix]
        exact (SineQPE.norm_rzToRyCircuit_sub_le _ _).trans hnorm_rz
      refine ⟨?_, ?_, ?_⟩
      · simp [OuterWeights.SineWindowPrep.count_wordToCircuit1_toff]
      · simp [hcnt, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      · rw [Circuit.eval_onRegister, Nat.cast_one, one_mul]
        exact OuterWeights.SineWindowPrep.VecApprox.embed (QRegister.singleton tgt)
          (by dsimp [dRzLeafNum]; positivity) (vecApprox_of_opNorm_le hnorm_ry)
  | _ + 1, _, _, _, .leaf _ _ _ _, hok => by simp [evalWordPairTree] at hok
  | 0, _, _, _, .branch _ _, hok => by simp [evalWordPairTree] at hok
  | k + 1, rCtrl, tgt, hdisj, .branch tP tM, hok => by
      simp only [evalWordPairTree, OuterWeights.SineWindowPrep.withForcedBool_eq,
        OuterWeights.SineWindowPrep.withForcedNat_eq, withForcedList_eq, Bool.and_eq_true] at hok ⊢
      obtain ⟨⟨⟨hokP, hokM⟩, _⟩, _⟩ := hok
      let rLo := rCtrl.slice 0 k (by omega)
      let wTop := rCtrl ⟨k, by omega⟩
      have hLo : rLo.DisjointWires (QRegister.singleton tgt) := by
        rw [QRegister.disjoint_iff] at hdisj ⊢
        intro i j hij
        exact hdisj ⟨i.val, by omega⟩ j (by simpa [rLo] using hij)
      have hwTop : wTop ≠ tgt := by
        rw [QRegister.disjoint_iff] at hdisj
        intro heq
        exact hdisj ⟨k, by omega⟩ 0 (by simpa [wTop] using heq)
      obtain ⟨htoffP, htP, hapP⟩ := wordPairTreeCircuit_spec k rLo tgt hLo tP hokP
      obtain ⟨htoffM, htM, hapM⟩ := wordPairTreeCircuit_spec k rLo tgt hLo tM hokM
      dsimp only [rLo, wTop] at htoffP htP hapP htoffM htM hapM
      simp only [wordPairTreeCircuit, wordPairTreeIdealU]
      refine ⟨?_, ?_, ?_⟩
      · simp [Circuit.sequence, htoffP, htoffM]
      · simp [Circuit.sequence, htP, htM]
      · have heval :
            (Circuit.sequence [wordPairTreeCircuit k rLo tgt hLo tP,
              Circuit.CNOT wTop tgt hwTop,
              wordPairTreeCircuit k rLo tgt hLo tM,
              Circuit.CNOT wTop tgt hwTop]).eval =
            (Circuit.CNOT wTop tgt hwTop).eval *
              ((wordPairTreeCircuit k rLo tgt hLo tM).eval *
                ((Circuit.CNOT wTop tgt hwTop).eval *
                  (wordPairTreeCircuit k rLo tgt hLo tP).eval)) := by
          simp only [Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity, one_mul,
            mul_assoc]
        dsimp only [rLo, wTop] at heval
        rw [heval]
        have hcnot :=
          VecApprox.refl (Circuit.CNOT (rCtrl ⟨k, by omega⟩) tgt hwTop).eval
        have hstep1 := OuterWeights.SineWindowPrep.VecApprox.mul hcnot hapP
        have hstep2 := OuterWeights.SineWindowPrep.VecApprox.mul hapM hstep1
        have hstep3 := OuterWeights.SineWindowPrep.VecApprox.mul hcnot hstep2
        refine hstep3.mono (le_of_eq ?_)
        push_cast; ring

/-- Little-endian control index extracted along `rCtrl` from a bit assignment `β`. -/
noncomputable def ctrlIdx {k n : ℕ} (rCtrl : QRegister k n) (β : BitAssignment n) :
    Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (rCtrl i))

theorem ctrlIdx_val_eq_sum {k n : ℕ} (rCtrl : QRegister k n) (β : BitAssignment n) :
    (ctrlIdx rCtrl β).val = ∑ i : Fin k, (β (rCtrl i)).val * 2 ^ i.val := by
  let c := ctrlIdx rCtrl β
  have hb : basisBits k c = fun i ↦ β (rCtrl i) := (basisBits k).apply_symm_apply _
  have hsum : ∀ (m : ℕ) (x : Fin (2 ^ m)),
      (∑ i : Fin m, (basisBits m x i).val * 2 ^ i.val) = x.val := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k' ih =>
        intro x
        let cDiv : Fin (2 ^ k') := ⟨x.val / 2,
          Nat.div_lt_of_lt_mul (x.isLt.trans_eq (pow_succ' 2 k'))⟩
        rw [Fin.sum_univ_succ]
        have h0 : (basisBits (k' + 1) x 0).val = x.val % 2 := by
          rw [basisBits_eq_div_mod, Fin.val_zero, _root_.pow_zero, Nat.div_one, ZMod.val_natCast,
            Nat.mod_mod_of_dvd _ (by decide)]
        have hs (r : Fin k') :
            (basisBits (k' + 1) x r.succ).val = (basisBits k' cDiv r).val := by
          rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
          simp only [Fin.val_succ, cDiv, pow_succ', Nat.div_div_eq_div_mul, mul_comm 2]
        have htail : (∑ i : Fin k', (basisBits (k' + 1) x i.succ).val * 2 ^ (i.succ).val) =
            2 * ∑ i : Fin k', (basisBits k' cDiv i).val * 2 ^ i.val := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hs i, Fin.val_succ, pow_succ']; ring
        simp only [Fin.val_zero, _root_.pow_zero, mul_one]
        rw [h0, htail, ih cDiv]; dsimp [cDiv]; omega
  simpa only [hb] using (hsum k c).symm

theorem ctrlIdx_update_not_mem {k n : ℕ} (rCtrl : QRegister k n) (tgt : Wire n)
    (hdisj : rCtrl.DisjointWires (QRegister.singleton tgt)) (β : BitAssignment n) (b : ZMod 2) :
    ctrlIdx rCtrl (Function.update β tgt b) = ctrlIdx rCtrl β := by
  dsimp only [ctrlIdx]
  congr 1; funext i
  have hne : rCtrl i ≠ tgt := by
    rw [QRegister.disjoint_iff] at hdisj
    exact fun heq ↦ hdisj i 0 (by simpa using heq)
  exact Function.update_of_ne hne b β

theorem singleton_embedUnitary_mulVec_ket {n : ℕ} (tgt : Wire n) (U : Unitary 2)
    (β : BitAssignment n) :
    ((QRegister.singleton tgt).embedUnitary U).1 *ᵥ OuterWeights.SineWindowPrep.ket n β =
      U.1 0 (if β tgt = 0 then 0 else 1) •
          OuterWeights.SineWindowPrep.ket n (Function.update β tgt 0) +
        U.1 1 (if β tgt = 0 then 0 else 1) •
          OuterWeights.SineWindowPrep.ket n (Function.update β tgt 1) := by
  have hk : ∀ γ : BitAssignment n, OuterWeights.SineWindowPrep.ket n γ = XMeasCircuit.ket γ :=
    fun γ ↦ by
      simp [OuterWeights.SineWindowPrep.ket, XMeasCircuit.ket, basisState]
  let A : Matrix (Fin 2) (Fin 2) ℂ := U.1
  change ((QRegister.singleton tgt).embedMatrix A).mulVec (OuterWeights.SineWindowPrep.ket n β) = _
  rw [hk β, XMeasCircuit.singleton_embedMatrix_mulVec_ket, ← hk, ← hk]

theorem singleton_qubitX_mulVec_ket {n : ℕ} (tgt : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton tgt).embedUnitary Qubit.X).1 *ᵥ OuterWeights.SineWindowPrep.ket n β =
      OuterWeights.SineWindowPrep.ket n (Function.update β tgt (β tgt + 1)) := by
  have hev : (Circuit.X tgt).eval = (QRegister.singleton tgt).embedUnitary Qubit.X := rfl
  rw [← hev]
  exact OuterWeights.SineWindowPrep.evolve_X_ket tgt β

theorem cnot_mulVec_singleton_ry_ket {n : ℕ} (wTop tgt : Wire n) (hwTop : wTop ≠ tgt)
    (θ : ℝ) (β : BitAssignment n) :
    (Circuit.CNOT wTop tgt hwTop).eval.1 *ᵥ
        (((QRegister.singleton tgt).embedUnitary (OuterWeights.SineWindowPrep.ryUnitary θ)).1 *ᵥ
          OuterWeights.SineWindowPrep.ket n β) =
      (if β wTop = 1 then
          ((QRegister.singleton tgt).embedUnitary
            (Qubit.X * ryUnitary θ)).1 *ᵥ OuterWeights.SineWindowPrep.ket n β
        else
          ((QRegister.singleton tgt).embedUnitary (OuterWeights.SineWindowPrep.ryUnitary θ)).1 *ᵥ
            OuterWeights.SineWindowPrep.ket n β) := by
  rw [singleton_embedUnitary_mulVec_ket, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  change _ • (Circuit.CNOT wTop tgt hwTop).evolve _ +
      _ • (Circuit.CNOT wTop tgt hwTop).evolve _ = _
  rw [OuterWeights.SineWindowPrep.evolve_CNOT_ket, OuterWeights.SineWindowPrep.evolve_CNOT_ket,
    Function.update_of_ne hwTop, Function.update_of_ne hwTop]
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (β wTop) with hb0 | hb1
  · simp only [hb0, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte, add_zero, Function.update_idem,
      Function.update_self]
  · simp only [hb1, ↓reduceIte, Function.update_idem, Function.update_self]
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      singleton_embedUnitary_mulVec_ket, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      singleton_qubitX_mulVec_ket, singleton_qubitX_mulVec_ket]
    simp only [Function.update_idem, Function.update_self]

theorem tree_and_cnot_on_singleton_ket {n k : ℕ}
    (rLo : QRegister k n) (wTop tgt : Wire n)
    (hLo : rLo.DisjointWires (QRegister.singleton tgt)) (hwTop : wTop ≠ tgt)
    (tM : WordPairTree) (θM : ℝ) (U₁ : Unitary 2) (β : BitAssignment n)
    (ihM : ∀ γ : BitAssignment n, ctrlIdx rLo γ = ctrlIdx rLo β →
      (wordPairTreeIdealU k rLo tgt hLo tM).1 *ᵥ OuterWeights.SineWindowPrep.ket n γ =
        ((QRegister.singleton tgt).embedUnitary (OuterWeights.SineWindowPrep.ryUnitary θM)).1 *ᵥ
          OuterWeights.SineWindowPrep.ket n γ) :
    (Circuit.CNOT wTop tgt hwTop).eval.1 *ᵥ
        ((wordPairTreeIdealU k rLo tgt hLo tM).1 *ᵥ
          (((QRegister.singleton tgt).embedUnitary U₁).1 *ᵥ OuterWeights.SineWindowPrep.ket n β)) =
      ((QRegister.singleton tgt).embedUnitary
        ((if β wTop = 1 then Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θM
          else OuterWeights.SineWindowPrep.ryUnitary θM) * U₁)).1 *ᵥ
        OuterWeights.SineWindowPrep.ket n β := by
  obtain ⟨a0, a1, hexp⟩ : ∃ a0 a1 : ℂ,
      ((QRegister.singleton tgt).embedUnitary U₁).1 *ᵥ OuterWeights.SineWindowPrep.ket n β =
        a0 • OuterWeights.SineWindowPrep.ket n (Function.update β tgt 0) +
          a1 • OuterWeights.SineWindowPrep.ket n (Function.update β tgt 1) :=
    ⟨_, _, singleton_embedUnitary_mulVec_ket tgt U₁ β⟩
  rw [hexp, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    ihM _ (ctrlIdx_update_not_mem rLo tgt hLo β 0),
    ihM _ (ctrlIdx_update_not_mem rLo tgt hLo β 1),
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    cnot_mulVec_singleton_ry_ket, cnot_mulVec_singleton_ry_ket]
  simp only [Function.update_of_ne hwTop]
  by_cases hb : β wTop = 1 <;> simp only [hb, ↓reduceIte] <;>
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← hexp,
      Matrix.mulVec_mulVec, ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul]

theorem wordPairTreeIdealU_mulVec_ket {n : ℕ} :
    ∀ (k : ℕ) (rCtrl : QRegister k n) (tgt : Wire n)
      (hdisj : rCtrl.DisjointWires (QRegister.singleton tgt))
      (t : WordPairTree) (β : BitAssignment n),
      (wordPairTreeIdealU k rCtrl tgt hdisj t).1 *ᵥ OuterWeights.SineWindowPrep.ket n β =
        ((QRegister.singleton tgt).embedUnitary
          (OuterWeights.SineWindowPrep.ryUnitary (wordPairTreeIdeal k t (ctrlIdx rCtrl β)))).1 *ᵥ
          OuterWeights.SineWindowPrep.ket n β
  | k, rCtrl, tgt, _, .skip, β => by
      simp only [wordPairTreeIdealU, wordPairTreeIdeal]
      have hry0 : OuterWeights.SineWindowPrep.ryUnitary 0 = 1 := by
        apply Subtype.ext
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [OuterWeights.SineWindowPrep.ryUnitary, OuterWeights.SineWindowPrep.su2RealUnitary]
      rw [hry0, QRegister.embedUnitary_one]
  | 0, _, _, _, .leaf _ _ _ _, _ => rfl
  | k + 1, _, _, _, .leaf _ _ _ _, β => by
      simp only [wordPairTreeIdealU, wordPairTreeIdeal]
      have hry0 : OuterWeights.SineWindowPrep.ryUnitary 0 = 1 := by
        apply Subtype.ext
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [OuterWeights.SineWindowPrep.ryUnitary, OuterWeights.SineWindowPrep.su2RealUnitary]
      rw [hry0, QRegister.embedUnitary_one]
  | 0, _, _, _, .branch _ _, β => by
      simp only [wordPairTreeIdealU, wordPairTreeIdeal]
      have hry0 : OuterWeights.SineWindowPrep.ryUnitary 0 = 1 := by
        apply Subtype.ext
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [OuterWeights.SineWindowPrep.ryUnitary, OuterWeights.SineWindowPrep.su2RealUnitary]
      rw [hry0, QRegister.embedUnitary_one]
  | k + 1, rCtrl, tgt, hdisj, .branch tP tM, β => by
      let rLo := rCtrl.slice 0 k (by omega)
      let wTop := rCtrl ⟨k, by omega⟩
      have hLo : rLo.DisjointWires (QRegister.singleton tgt) := by
        rw [QRegister.disjoint_iff] at hdisj ⊢
        intro i j hij
        exact hdisj ⟨i.val, by omega⟩ j (by simpa [rLo] using hij)
      have hwTop : wTop ≠ tgt := by
        rw [QRegister.disjoint_iff] at hdisj
        intro heq
        exact hdisj ⟨k, by omega⟩ 0 (by simpa [wTop] using heq)
      have hc_decomp : (ctrlIdx rCtrl β).val =
          (ctrlIdx rLo β).val + (β wTop).val * 2 ^ k := by
        rw [ctrlIdx_val_eq_sum, ctrlIdx_val_eq_sum, Fin.sum_univ_castSucc]
        refine congrArg₂ (· + ·) ?_ rfl
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hr : rCtrl i.castSucc = rLo i := by
          dsimp only [rLo]; rw [QRegister.slice_apply]; congr 1; ext; simp
        rw [hr, Fin.val_castSucc]
      have hlo_lt : (ctrlIdx rLo β).val < 2 ^ k := (ctrlIdx rLo β).isLt
      have hcLo_eq : (⟨(ctrlIdx rCtrl β).val % 2 ^ k,
          Nat.mod_lt _ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) = ctrlIdx rLo β := by
        apply Fin.ext; dsimp only
        rw [hc_decomp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo_lt]
      let θP := wordPairTreeIdeal k tP (ctrlIdx rLo β)
      let θM := wordPairTreeIdeal k tM (ctrlIdx rLo β)
      have ihM_ket : ∀ γ : BitAssignment n, ctrlIdx rLo γ = ctrlIdx rLo β →
          (wordPairTreeIdealU k (rCtrl.slice 0 k (by omega)) tgt hLo tM).1 *ᵥ
              OuterWeights.SineWindowPrep.ket n γ =
            ((QRegister.singleton tgt).embedUnitary (OuterWeights.SineWindowPrep.ryUnitary θM)).1 *ᵥ
              OuterWeights.SineWindowPrep.ket n γ := by
        intro γ hγ
        change (wordPairTreeIdealU k rLo tgt hLo tM).1 *ᵥ _ = _
        rw [wordPairTreeIdealU_mulVec_ket, hγ]
      simp only [wordPairTreeIdealU, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      have ihP_ket :
          (wordPairTreeIdealU k (rCtrl.slice 0 k (by omega)) tgt hLo tP).1 *ᵥ
              OuterWeights.SineWindowPrep.ket n β =
            ((QRegister.singleton tgt).embedUnitary (OuterWeights.SineWindowPrep.ryUnitary θP)).1 *ᵥ
              OuterWeights.SineWindowPrep.ket n β :=
        wordPairTreeIdealU_mulVec_ket k rLo tgt hLo tP β
      rw [ihP_ket, cnot_mulVec_singleton_ry_ket (rCtrl ⟨k, by omega⟩) tgt hwTop θP β]
      dsimp only [wTop] at hc_decomp
      have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h01 (β (rCtrl ⟨k, by omega⟩)) with hb0 | hb1
      · have hlt : (ctrlIdx rCtrl β).val < 2 ^ k := by
          rw [hc_decomp, hb0, ZMod.val_zero, zero_mul, add_zero]; exact hlo_lt
        simp only [hb0, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
        rw [tree_and_cnot_on_singleton_ket (rCtrl.slice 0 k (by omega)) (rCtrl ⟨k, by omega⟩)
          tgt hLo hwTop tM θM (OuterWeights.SineWindowPrep.ryUnitary θP) β ihM_ket]
        simp only [hb0, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte,
          OuterWeights.SineWindowPrep.ryUnitary_mul, wordPairTreeIdeal, hlt, hcLo_eq, θP, θM]
      · have hnotlt : ¬ (ctrlIdx rCtrl β).val < 2 ^ k := by
          rw [hc_decomp, hb1, ZMod.val_one, one_mul]; omega
        simp only [hb1, ↓reduceIte]
        rw [tree_and_cnot_on_singleton_ket (rCtrl.slice 0 k (by omega)) (rCtrl ⟨k, by omega⟩)
          tgt hLo hwTop tM θM (Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θP) β ihM_ket]
        simp only [hb1, ↓reduceIte]
        have hconj : (Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θM) *
            (Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θP) =
            OuterWeights.SineWindowPrep.ryUnitary (θP - θM) := by
          calc (Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θM) *
                (Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θP)
              = (Qubit.X * OuterWeights.SineWindowPrep.ryUnitary θM * Qubit.X) *
                  OuterWeights.SineWindowPrep.ryUnitary θP := by group
            _ = ryUnitary (-θM) * ryUnitary θP := by
                  rw [OuterWeights.SineWindowPrep.qubitX_mul_ryUnitary_mul_qubitX]
            _ = OuterWeights.SineWindowPrep.ryUnitary (θP - θM) := by
                  rw [OuterWeights.SineWindowPrep.ryUnitary_mul, sub_eq_add_neg]
        rw [hconj]
        simp only [wordPairTreeIdeal, hnotlt, ↓reduceIte, hcLo_eq, θP, θM]

/-- Unified top-down Möttönen cascade on `q` wires from target bit `s - 1` down to `0`. -/
def mottonenCascade (q : ℕ) : (s : ℕ) → s ≤ q → List WordPairTree → Circuit q
  | 0, _, _ => Circuit.identity
  | _ + 1, _, [] => Circuit.identity
  | s' + 1, hs, tr :: trs =>
      let k := q - (s' + 1)
      let rCtrl : QRegister k q := QRegister.block (s' + 1) k (by omega)
      let tgt : Wire q := ⟨s', by omega⟩
      have hdisj : rCtrl.DisjointWires (QRegister.singleton tgt) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hv := congrArg Fin.val hij
        simp [rCtrl, tgt] at hv; omega
      (wordPairTreeCircuit k rCtrl tgt hdisj tr).seq (mottonenCascade q s' (by omega) trs)

/-- Ideal `q`-qubit unitary of `mottonenCascade`. -/
noncomputable def mottonenCascadeIdealU (q : ℕ) :
    (s : ℕ) → s ≤ q → List WordPairTree → Unitary (2 ^ q)
  | 0, _, _ => 1
  | _ + 1, _, [] => 1
  | s' + 1, hs, tr :: trs =>
      let k := q - (s' + 1)
      let rCtrl : QRegister k q := QRegister.block (s' + 1) k (by omega)
      let tgt : Wire q := ⟨s', by omega⟩
      have hdisj : rCtrl.DisjointWires (QRegister.singleton tgt) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hv := congrArg Fin.val hij
        simp [rCtrl, tgt] at hv; omega
      mottonenCascadeIdealU q s' (by omega) trs * wordPairTreeIdealU k rCtrl tgt hdisj tr

/-- Real coarse state on `q` qubits supported on multiples of `2 ^ s`. -/
noncomputable def coarseVec (q s : ℕ) (hs : s ≤ q) (v : Fin (2 ^ (q - s)) → ℝ) :
    Fin (2 ^ q) → ℂ :=
  ∑ c : Fin (2 ^ (q - s)),
    (v c : ℂ) • OuterWeights.SineWindowPrep.ket q (basisBits q ⟨c.val * 2 ^ s, by
      have hc := c.isLt
      have hp : 2 ^ (q - s) * 2 ^ s = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hs]
      nlinarith [Nat.two_pow_pos s]⟩)

theorem coarseVec_zero (q : ℕ) (v : Fin (2 ^ (q - 0)) → ℝ) (x : Fin (2 ^ q)) :
    coarseVec q 0 (Nat.zero_le q) v x = (v x : ℂ) := by
  dsimp only [coarseVec]
  simp only [_root_.pow_zero, mul_one, OuterWeights.SineWindowPrep.ket_basisBits, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  let x0 : Fin (2 ^ (q - 0)) := ⟨x.val, x.isLt⟩
  rw [Fintype.sum_eq_single x0 (fun c hc ↦ by
    have hne : x.val ≠ c.val := fun h ↦ hc (Fin.ext h.symm)
    simp [Fin.ext_iff, hne])]
  simp [x0]

theorem update_basisBits_mul_two_pow {q s' : ℕ} (hs : s' + 1 ≤ q)
    (c : Fin (2 ^ (q - (s' + 1)))) (b : ZMod 2) :
    Function.update
        (basisBits q ⟨c.val * 2 ^ (s' + 1), by
          have hc := c.isLt
          have hp : 2 ^ (q - (s' + 1)) * 2 ^ (s' + 1) = 2 ^ q := by
            rw [← pow_add, Nat.sub_add_cancel hs]
          nlinarith [Nat.two_pow_pos (s' + 1)]⟩)
        ⟨s', by omega⟩ b =
      basisBits q ⟨(2 * c.val + b.val) * 2 ^ s', by
        have hc := c.isLt
        have hb : b.val < 2 := ZMod.val_lt b
        have hp : 2 ^ (q - (s' + 1)) * 2 ^ (s' + 1) = 2 ^ q := by
          rw [← pow_add, Nat.sub_add_cancel hs]
        have hp2 : 2 ^ (s' + 1) = 2 * 2 ^ s' := pow_succ' 2 s'
        nlinarith [Nat.two_pow_pos s']⟩ := by
  funext w
  by_cases hw : w = ⟨s', by omega⟩
  · subst hw
    rw [Function.update_self, basisBits_eq_div_mod]
    simp only [Nat.mul_div_cancel _ (Nat.two_pow_pos s')]
    have hb : b.val < 2 := ZMod.val_lt b
    have hmod : (2 * c.val + b.val) % 2 = b.val := by omega
    rw [hmod, ZMod.natCast_zmod_val]
  · have hw_ne : w.val ≠ s' := fun h ↦ hw (Fin.ext h)
    rw [Function.update_of_ne hw, basisBits_eq_div_mod, basisBits_eq_div_mod]
    congr 1
    dsimp only
    by_cases hlt : w.val < s'
    · have hd1 : 2 ^ (w.val + 1) ∣ c.val * 2 ^ (s' + 1) :=
         dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
      have hd2 : 2 ^ (w.val + 1) ∣ (2 * c.val + b.val) * 2 ^ s' :=
        dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
      obtain ⟨m1, hm1⟩ := hd1
      obtain ⟨m2, hm2⟩ := hd2
      have hp : 2 ^ (w.val + 1) = 2 ^ w.val * 2 := pow_succ 2 w.val
      rw [hm1, hm2, hp, mul_assoc, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos w.val),
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos w.val),
        Nat.mul_mod_right, Nat.mul_mod_right]
    · have hgt : s' + 1 ≤ w.val := by omega
      have h1 : (c.val * 2 ^ (s' + 1)) / 2 ^ w.val = c.val / 2 ^ (w.val - (s' + 1)) := by
        have hw_eq : 2 ^ w.val = 2 ^ (s' + 1) * 2 ^ (w.val - (s' + 1)) := by
          rw [← pow_add, Nat.add_sub_of_le hgt]
        rw [hw_eq, ← Nat.div_div_eq_div_mul,
          Nat.mul_div_cancel _ (Nat.two_pow_pos (s' + 1))]
      have h2 : ((2 * c.val + b.val) * 2 ^ s') / 2 ^ w.val =
          c.val / 2 ^ (w.val - (s' + 1)) := by
        have hw_eq : 2 ^ w.val = 2 ^ s' * (2 * 2 ^ (w.val - (s' + 1))) := by
          have : s' + (1 + (w.val - (s' + 1))) = w.val := by omega
          calc 2 ^ w.val = 2 ^ (s' + (1 + (w.val - (s' + 1)))) := by rw [this]
            _ = 2 ^ s' * (2 * 2 ^ (w.val - (s' + 1))) := by rw [pow_add, pow_add, pow_one]
        have hb : b.val < 2 := ZMod.val_lt b
        have hdiv2 : (2 * c.val + b.val) / 2 = c.val := by omega
        rw [hw_eq, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos s'),
          ← Nat.div_div_eq_div_mul, hdiv2]
      rw [h1, h2]

theorem mottonenCascade_step_mulVec (q s' : ℕ) (hs : s' + 1 ≤ q)
    (tr : WordPairTree) (v : Fin (2 ^ (q - (s' + 1))) → ℝ) :
    let k := q - (s' + 1)
    let rCtrl : QRegister k q := QRegister.block (s' + 1) k (by omega)
    let tgt : Wire q := ⟨s', by omega⟩
    have hdisj : rCtrl.DisjointWires (QRegister.singleton tgt) := by
      rw [QRegister.disjoint_iff]
      intro i j hij; have hv := congrArg Fin.val hij; simp [rCtrl, tgt] at hv; omega
    (wordPairTreeIdealU k rCtrl tgt hdisj tr).1 *ᵥ coarseVec q (s' + 1) hs v =
      coarseVec q s' (by omega) (fun c' ↦
        let c : Fin (2 ^ k) := ⟨c'.val / 2, Nat.div_lt_of_lt_mul
          (c'.isLt.trans_eq (by rw [show q - s' = k + 1 by omega, pow_succ']))⟩
        if c'.val % 2 = 0 then v c * Real.cos (wordPairTreeIdeal k tr c / 2)
        else v c * Real.sin (wordPairTreeIdeal k tr c / 2)) := by
  intro k rCtrl tgt hdisj
  dsimp only [coarseVec]
  rw [Matrix.mulVec_sum]
  have hterm (c : Fin (2 ^ k)) :
      (wordPairTreeIdealU k rCtrl tgt hdisj tr).1 *ᵥ
          ((v c : ℂ) • OuterWeights.SineWindowPrep.ket q (basisBits q ⟨c.val * 2 ^ (s' + 1), by
            have hc := c.isLt
            have hp : 2 ^ k * 2 ^ (s' + 1) = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hs]
            nlinarith [Nat.two_pow_pos (s' + 1)]⟩)) =
        ((v c * Real.cos (wordPairTreeIdeal k tr c / 2) : ℝ) : ℂ) •
            OuterWeights.SineWindowPrep.ket q (basisBits q ⟨(2 * c.val + 0) * 2 ^ s', by
              have hc := c.isLt
              have hp : 2 ^ k * 2 ^ (s' + 1) = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hs]
              have hp2 : 2 ^ (s' + 1) = 2 * 2 ^ s' := pow_succ' 2 s'
              nlinarith [Nat.two_pow_pos s']⟩) +
          ((v c * Real.sin (wordPairTreeIdeal k tr c / 2) : ℝ) : ℂ) •
            OuterWeights.SineWindowPrep.ket q (basisBits q ⟨(2 * c.val + 1) * 2 ^ s', by
              have hc := c.isLt
              have hp : 2 ^ k * 2 ^ (s' + 1) = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hs]
              have hp2 : 2 ^ (s' + 1) = 2 * 2 ^ s' := pow_succ' 2 s'
              nlinarith [Nat.two_pow_pos s']⟩) := by
    let idx : Fin (2 ^ q) := ⟨c.val * 2 ^ (s' + 1), by
      have hc := c.isLt
      have hp : 2 ^ k * 2 ^ (s' + 1) = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hs]
      nlinarith [Nat.two_pow_pos (s' + 1)]⟩
    let β := basisBits q idx
    have hctrl : ctrlIdx rCtrl β = c := by
      apply (basisBits k).injective
      dsimp only [ctrlIdx]
      rw [(basisBits k).apply_symm_apply]
      funext i
      change basisBits q idx (rCtrl i) = basisBits k c i
      rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
      congr 1
      dsimp only [idx, rCtrl]
      rw [QRegister.block_apply_val]
      have hp : 2 ^ (s' + 1 + i.val) = 2 ^ (s' + 1) * 2 ^ i.val := pow_add 2 (s' + 1) i.val
      rw [hp, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos (s' + 1))]
    have htgt0 : β tgt = 0 := by
      dsimp only [β, idx, tgt]
      rw [basisBits_eq_div_mod]
      have hp : 2 ^ (s' + 1) = 2 ^ s' * 2 := pow_succ 2 s'
      have hd : (c.val * 2 ^ (s' + 1)) / 2 ^ s' = c.val * 2 := by
        rw [hp, ← mul_assoc, mul_comm (c.val), mul_assoc,
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos s'), mul_comm]
      rw [hd, Nat.mul_mod_left]; rfl
    dsimp only [β, idx] at htgt0
    rw [Matrix.mulVec_smul, wordPairTreeIdealU_mulVec_ket, hctrl,
      singleton_embedUnitary_mulVec_ket]
    simp only [htgt0, ↓reduceIte, ryUnitary_coe_eq_ryMatrix, SineQPE.ryMatrix,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [smul_add, smul_smul, smul_smul,
      update_basisBits_mul_two_pow hs c 0, update_basisBits_mul_two_pow hs c 1]
    simp [ZMod.val_zero, show (1 : ZMod 2).val = 1 from rfl, Complex.ofReal_mul]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  -- Biject `Fin (2 ^ (q - s'))` with `(Fin (2 ^ k) ⊕ Fin (2 ^ k))` via `2 * c + 0` and `2 * c + 1`
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c' : Fin (2 ^ (q - s')) ↦ c'.val % 2 = 0)]
  congr 1
  · refine (Finset.sum_bij (fun c (_ : c ∈ Finset.univ) ↦ (⟨2 * c.val, by
        have hc : c.val < 2 ^ k := c.isLt
        calc 2 * c.val < 2 * 2 ^ k := by omega
          _ = 2 ^ (q - s') := by rw [← pow_succ', show k + 1 = q - s' by omega]⟩ :
          Fin (2 ^ (q - s'))))
      (fun c _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩)
      (fun c₁ _ c₂ _ h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
      (fun c' hc' ↦ ⟨⟨c'.val / 2, Nat.div_lt_of_lt_mul
        (c'.isLt.trans_eq (by rw [show q - s' = k + 1 by omega, pow_succ']))⟩,
        Finset.mem_univ _,
        Fin.ext (by have hm := (Finset.mem_filter.mp hc').2; dsimp; omega)⟩)
      (fun c _ ↦ ?_)).symm
    dsimp only
    have hm : (2 * c.val) % 2 = 0 := by omega
    have hd : (2 * c.val) / 2 = c.val := by omega
    simp only [hm, ↓reduceIte, hd, Fin.eta, add_zero]
  · refine (Finset.sum_bij (fun c (_ : c ∈ Finset.univ) ↦ (⟨2 * c.val + 1, by
        have hc : c.val < 2 ^ k := c.isLt
        calc 2 * c.val + 1 < 2 * 2 ^ k := by omega
          _ = 2 ^ (q - s') := by rw [← pow_succ', show k + 1 = q - s' by omega]⟩ :
          Fin (2 ^ (q - s'))))
      (fun c _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩)
      (fun c₁ _ c₂ _ h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
      (fun c' hc' ↦ ⟨⟨c'.val / 2, Nat.div_lt_of_lt_mul
        (c'.isLt.trans_eq (by rw [show q - s' = k + 1 by omega, pow_succ']))⟩,
        Finset.mem_univ _,
        Fin.ext (by have hm := (Finset.mem_filter.mp hc').2; dsimp; omega)⟩)
      (fun c _ ↦ ?_)).symm
    dsimp only
    have hm : ¬ (2 * c.val + 1) % 2 = 0 := by omega
    have hd : (2 * c.val + 1) / 2 = c.val := by omega
    simp only [hm, ↓reduceIte, hd, Fin.eta]

/-- `CNOT` fan-out from `mLow - 1` onto bits `0 .. j - 1`. -/
def cnotFan (mLow : ℕ) (hm1 : 1 ≤ mLow) : (j : ℕ) → j ≤ mLow - 1 → Circuit mLow
  | 0, _ => Circuit.identity
  | j' + 1, hj =>
      (cnotFan mLow hm1 j' (by omega)).seq
        (Circuit.CNOT ⟨mLow - 1, by omega⟩ ⟨j', by omega⟩ (by
          intro h; have hv := congrArg Fin.val h; dsimp at hv; omega))

/-- Zero-`T` Clifford tail `Z(q_lo) ;; H(q_lo) ;; CNOT(q_lo -> 0..q_lo-1)` for `pWinLo`. -/
def loCliffordTail (mLow : ℕ) (hm1 : 1 ≤ mLow) : Circuit mLow :=
  let qLo : Wire mLow := ⟨mLow - 1, by omega⟩
  (Circuit.Z qLo).seq ((Circuit.H qLo).seq (cnotFan mLow hm1 (mLow - 1) le_rfl))

theorem cnotFan_counts (mLow : ℕ) (hm1 : 1 ≤ mLow) :
    ∀ (j : ℕ) (hj : j ≤ mLow - 1),
      (cnotFan mLow hm1 j hj).count .TOFF = 0 ∧ (cnotFan mLow hm1 j hj).count .T = 0
  | 0, _ => ⟨by simp [cnotFan], by simp [cnotFan]⟩
  | j' + 1, hj => by
      obtain ⟨h0, h1⟩ := cnotFan_counts mLow hm1 j' (by omega)
      exact ⟨by simp [cnotFan, h0], by simp [cnotFan, h1]⟩

theorem loCliffordTail_counts (mLow : ℕ) (hm1 : 1 ≤ mLow) :
    (loCliffordTail mLow hm1).count .TOFF = 0 ∧ (loCliffordTail mLow hm1).count .T = 0 := by
  obtain ⟨h0, h1⟩ := cnotFan_counts mLow hm1 (mLow - 1) le_rfl
  exact ⟨by simp [loCliffordTail, h0], by simp [loCliffordTail, h1]⟩

theorem cnotFan_evolve_ket (mLow : ℕ) (hm1 : 1 ≤ mLow) :
    ∀ (j : ℕ) (hj : j ≤ mLow - 1) (β : BitAssignment mLow),
      (cnotFan mLow hm1 j hj).evolve (OuterWeights.SineWindowPrep.ket mLow β) =
        OuterWeights.SineWindowPrep.ket mLow
          (fun w ↦ if w.val < j then β w + β ⟨mLow - 1, by omega⟩ else β w)
  | 0, _, β => by simp [cnotFan, Circuit.evolve]
  | j' + 1, hj, β => by
      dsimp only [cnotFan]
      rw [Circuit.evolve_seq, cnotFan_evolve_ket mLow hm1 j' (by omega) β,
        OuterWeights.SineWindowPrep.evolve_CNOT_ket]
      congr 1; funext w
      by_cases hw : w = ⟨j', by omega⟩
      · subst hw
        have h1 : ¬ (mLow - 1 < j') := by omega
        simp [h1]
      · have hw_ne : w.val ≠ j' := fun h ↦ hw (Fin.ext h)
        rw [Function.update_of_ne hw]
        by_cases hlt : w.val < j'
        · have hlt' : w.val < j' + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ w.val < j' + 1 := by omega
          simp [hlt, hlt']

theorem basisBits_lo_comp (mLow : ℕ) (hm1 : 1 ≤ mLow) (z : Fin (2 ^ (mLow - 1))) :
    let qLo : Wire mLow := ⟨mLow - 1, by omega⟩
    let β0 := basisBits mLow ⟨z.val, by
      have hz := z.isLt
      exact lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (by omega))⟩
    Function.update β0 qLo 0 = β0 ∧
      (fun w : Wire mLow ↦
        if w.val < mLow - 1 then Function.update β0 qLo 1 w + Function.update β0 qLo 1 qLo
        else Function.update β0 qLo 1 w) =
      basisBits mLow ⟨2 ^ mLow - 1 - z.val,
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos mLow) Nat.one_pos)⟩ := by
  intro qLo β0
  have htop0 : β0 qLo = 0 := by
    dsimp only [β0, qLo]
    rw [basisBits_eq_div_mod, Nat.div_eq_of_lt z.isLt, Nat.zero_mod]; rfl
  refine ⟨by funext w; by_cases hw : w = qLo <;> simp [hw, htop0], ?_⟩
  funext w
  by_cases hw : w = qLo
  · subst hw
    have hnot : ¬ (mLow - 1 < mLow - 1) := Nat.lt_irrefl _
    simp only [qLo, hnot, ↓reduceIte, Function.update_self]
    rw [basisBits_eq_div_mod]
    have hdiv : (2 ^ mLow - 1 - z.val) / 2 ^ (mLow - 1) = 1 := by
      have hz := z.isLt
      have hp : 2 ^ mLow = 2 * 2 ^ (mLow - 1) := by
        conv_lhs => rw [show mLow = (mLow - 1) + 1 by omega, pow_succ']
      have hsplit : 2 ^ mLow - 1 - z.val =
          2 ^ (mLow - 1) * 1 + (2 ^ (mLow - 1) - 1 - z.val) := by omega
      rw [hsplit, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega)]
    rw [hdiv]; rfl
  · have hlt : w.val < mLow - 1 := by
      have := w.isLt
      have hv : w.val ≠ mLow - 1 := fun h ↦ hw (Fin.ext h)
      omega
    simp only [hlt, ↓reduceIte, Function.update_of_ne hw, Function.update_self]
    dsimp only [β0]
    rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
    -- Complement identity: `((2^mLow - 1 - z) / 2^w) % 2 = 1 - (z / 2^w) % 2`
    let P := 2 ^ w.val
    let K := 2 ^ (mLow - w.val)
    have hP_pos : 0 < P := Nat.two_pow_pos w.val
    have hK_pos : 0 < K := Nat.two_pow_pos (mLow - w.val)
    have hPK_pos : 0 < P * K := Nat.mul_pos hP_pos hK_pos
    have hpow_split : 2 ^ mLow = P * K := by
      dsimp only [P, K]; rw [← pow_add, Nat.add_sub_of_le (by omega)]
    have hsum_div : z.val / P + (2 ^ mLow - 1 - z.val) / P = K - 1 := by
      have h1 := Nat.div_add_mod z.val P
      have h2 := Nat.div_add_mod (2 ^ mLow - 1 - z.val) P
      have hm1 := Nat.mod_lt z.val hP_pos
      have hm2 := Nat.mod_lt (2 ^ mLow - 1 - z.val) hP_pos
      set q1 := z.val / P
      set r1 := z.val % P
      set q2 := (2 ^ mLow - 1 - z.val) / P
      set r2 := (2 ^ mLow - 1 - z.val) % P
      rw [hpow_split] at h2
      have htot : P * (q1 + q2) + (r1 + r2) = P * K - 1 := by
        have hz_lt : z.val < P * K := hpow_split ▸
          lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by decide) (by omega))
        have hlin : (P * q1 + r1) + (P * q2 + r2) = P * K - 1 := by omega
        calc P * (q1 + q2) + (r1 + r2) = (P * q1 + r1) + (P * q2 + r2) := by ring
          _ = P * K - 1 := hlin
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt_q | hgt_q
      · have hle_q : q1 + q2 + 2 ≤ K := by omega
        have hm := Nat.mul_le_mul_left P hle_q
        have hexp : P * (q1 + q2 + 2) = P * (q1 + q2) + P + P := by ring
        omega
      · have hge_q : K ≤ q1 + q2 := by omega
        have hm := Nat.mul_le_mul_left P hge_q
        omega
    have heven : 2 ∣ K := by
      dsimp only [K]
      refine ⟨2 ^ (mLow - w.val - 1), ?_⟩
      conv_lhs => rw [show mLow - w.val = (mLow - w.val - 1) + 1 by omega, pow_succ']
    obtain ⟨m, hm⟩ := heven
    have hm_pos : 1 ≤ m := by
      by_contra hc; have hm0 : m = 0 := by omega
      rw [hm0, mul_zero] at hm; exact absurd hm hK_pos.ne'
    have hmod_sum : (z.val / P) % 2 + ((2 ^ mLow - 1 - z.val) / P) % 2 = 1 := by
      omega
    dsimp only [P] at hmod_sum
    rcases Nat.mod_two_eq_zero_or_one (z.val / 2 ^ w.val) with h0 | h1
    · have hc1 : ((2 ^ mLow - 1 - z.val) / 2 ^ w.val) % 2 = 1 := by omega
      rw [h0, hc1]; rfl
    · have hc0 : ((2 ^ mLow - 1 - z.val) / 2 ^ w.val) % 2 = 0 := by omega
      rw [h1, hc0]; decide

theorem loCliffordTail_evolve_ket0 (mLow : ℕ) (hm1 : 1 ≤ mLow)
    (z : Fin (2 ^ (mLow - 1))) :
    let idx0 : Fin (2 ^ mLow) := ⟨z.val,
      lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by decide) (by omega))⟩
    let idx1 : Fin (2 ^ mLow) := ⟨2 ^ mLow - 1 - z.val,
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos mLow) Nat.one_pos)⟩
    (loCliffordTail mLow hm1).eval.1 *ᵥ Pi.single idx0 (1 : ℂ) =
      (√(1 / 2 : ℝ) : ℂ) • Pi.single idx0 1 + (√(1 / 2 : ℝ) : ℂ) • Pi.single idx1 1 := by
  intro idx0 idx1
  let qLo : Wire mLow := ⟨mLow - 1, by omega⟩
  rw [← OuterWeights.SineWindowPrep.ket_basisBits idx0]
  change (loCliffordTail mLow hm1).evolve
    (OuterWeights.SineWindowPrep.ket mLow (basisBits mLow idx0)) = _
  dsimp only [loCliffordTail]
  rw [Circuit.evolve_seq, OuterWeights.SineWindowPrep.evolve_Z_ket]
  have htop0 : basisBits mLow idx0 qLo = 0 := by
    dsimp only [idx0, qLo]
    rw [basisBits_eq_div_mod, Nat.div_eq_of_lt z.isLt, Nat.zero_mod]; rfl
  dsimp only [qLo] at htop0
  simp only [htop0, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte, one_smul]
  rw [Circuit.evolve_seq, OuterWeights.SineWindowPrep.evolve_H_ket]
  simp only [htop0, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
  change (cnotFan mLow hm1 (mLow - 1) le_rfl).eval.1 *ᵥ _ = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  change _ • (cnotFan mLow hm1 (mLow - 1) le_rfl).evolve _ +
      _ • (cnotFan mLow hm1 (mLow - 1) le_rfl).evolve _ = _
  rw [cnotFan_evolve_ket, cnotFan_evolve_ket]
  obtain ⟨hu0, hu1⟩ := basisBits_lo_comp mLow hm1 z
  have h0_id :
      (fun w : Wire mLow ↦
        if w.val < mLow - 1 then
          Function.update (basisBits mLow idx0) qLo 0 w +
            Function.update (basisBits mLow idx0) qLo 0 qLo
        else Function.update (basisBits mLow idx0) qLo 0 w) = basisBits mLow idx0 := by
    dsimp only [idx0, qLo] at htop0 ⊢
    rw [hu0]; funext w
    by_cases hw : w.val < mLow - 1
    · simp [hw, htop0]
    · simp [hw]
  rw [h0_id, hu1, ket_basisBits, ket_basisBits]

theorem loCliffordTail_evolve_ket1 (mLow : ℕ) (hm1 : 1 ≤ mLow)
    (z : Fin (2 ^ (mLow - 1))) :
    let idx0 : Fin (2 ^ mLow) := ⟨z.val,
      lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by decide) (by omega))⟩
    let idxHi : Fin (2 ^ mLow) := ⟨2 ^ (mLow - 1) + z.val, by
      have hz := z.isLt
      have hp : 2 ^ mLow = 2 * 2 ^ (mLow - 1) := by
        conv_lhs => rw [show mLow = (mLow - 1) + 1 by omega, pow_succ']
      omega⟩
    let idx1 : Fin (2 ^ mLow) := ⟨2 ^ mLow - 1 - z.val,
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos mLow) Nat.one_pos)⟩
    (loCliffordTail mLow hm1).eval.1 *ᵥ Pi.single idxHi (1 : ℂ) =
      (-(√(1 / 2 : ℝ) : ℂ)) • Pi.single idx0 1 + (√(1 / 2 : ℝ) : ℂ) • Pi.single idx1 1 := by
  intro idx0 idxHi idx1
  let qLo : Wire mLow := ⟨mLow - 1, by omega⟩
  rw [← OuterWeights.SineWindowPrep.ket_basisBits idxHi]
  change (loCliffordTail mLow hm1).evolve
    (OuterWeights.SineWindowPrep.ket mLow (basisBits mLow idxHi)) = _
  dsimp only [loCliffordTail]
  rw [Circuit.evolve_seq, OuterWeights.SineWindowPrep.evolve_Z_ket]
  have htop1 : basisBits mLow idxHi qLo = 1 := by
    dsimp only [idxHi, qLo]
    rw [basisBits_eq_div_mod]
    have hd : (2 ^ (mLow - 1) + z.val) / 2 ^ (mLow - 1) = 1 := by
      have hs : 2 ^ (mLow - 1) + z.val = 2 ^ (mLow - 1) * 1 + z.val := by ring
      rw [hs, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt z.isLt]
    rw [hd]; rfl
  have hupd_eq : ∀ b : ZMod 2,
      Function.update (basisBits mLow idxHi) qLo b =
        Function.update (basisBits mLow idx0) qLo b := by
    intro b; funext w
    by_cases hw : w = qLo
    · subst hw; simp
    · rw [Function.update_of_ne hw, Function.update_of_ne hw]
      dsimp only [idxHi, idx0]
      rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
      congr 1
      have hlt : w.val < mLow - 1 := by
        have := w.isLt; have hv : w.val ≠ mLow - 1 := fun h ↦ hw (Fin.ext h); omega
      have hd : 2 ^ (w.val + 1) ∣ 2 ^ (mLow - 1) := Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨m, hm⟩ := hd
      have hp : 2 ^ (w.val + 1) = 2 ^ w.val * 2 := pow_succ 2 w.val
      let zv := z.val
      have hdiv : (2 ^ (mLow - 1) + zv) / 2 ^ w.val = 2 * m + zv / 2 ^ w.val := by
        have h1 : 2 ^ (mLow - 1) = 2 ^ w.val * (2 * m) := by rw [hm, hp]; ring
        rw [h1, Nat.mul_add_div (Nat.two_pow_pos w.val)]
      dsimp only
      rw [hdiv, Nat.mul_add_mod_self_left]
  dsimp only [qLo] at htop1 hupd_eq
  simp only [htop1, ↓reduceIte]
  change (Circuit.seq (Circuit.H qLo) (cnotFan mLow hm1 (mLow - 1) le_rfl)).eval.1 *ᵥ _ = _
  rw [Matrix.mulVec_smul]
  change (-1 : ℂ) • ((Circuit.H qLo).seq (cnotFan mLow hm1 (mLow - 1) le_rfl)).evolve _ = _
  rw [Circuit.evolve_seq, OuterWeights.SineWindowPrep.evolve_H_ket]
  dsimp only [qLo]
  simp only [htop1, ↓reduceIte, hupd_eq 0, hupd_eq 1]
  change (-1 : ℂ) • ((cnotFan mLow hm1 (mLow - 1) le_rfl).eval.1 *ᵥ _) = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  change (-1 : ℂ) • (_ • (cnotFan mLow hm1 (mLow - 1) le_rfl).evolve _ +
      _ • (cnotFan mLow hm1 (mLow - 1) le_rfl).evolve _) = _
  rw [cnotFan_evolve_ket, cnotFan_evolve_ket]
  obtain ⟨hu0, hu1⟩ := basisBits_lo_comp mLow hm1 z
  have htop0 : basisBits mLow idx0 qLo = 0 := by
    dsimp only [idx0, qLo]
    rw [basisBits_eq_div_mod, Nat.div_eq_of_lt z.isLt, Nat.zero_mod]; rfl
  have h0_id :
      (fun w : Wire mLow ↦
        if w.val < mLow - 1 then
          Function.update (basisBits mLow idx0) qLo 0 w +
            Function.update (basisBits mLow idx0) qLo 0 qLo
        else Function.update (basisBits mLow idx0) qLo 0 w) = basisBits mLow idx0 := by
    dsimp only [idx0, qLo] at htop0 ⊢
    rw [hu0]; funext w
    by_cases hw : w.val < mLow - 1
    · simp [hw, htop0]
    · simp [hw]
  rw [h0_id, hu1, ket_basisBits, ket_basisBits]
  ext x; simp [Pi.add_apply, Pi.smul_apply]; ring

/-- Scaled real amplitude interval certificate `(mid, eUlps)` at `scale24 = 10 ^ 24`. -/
structure AmpCert where
  /-- Scaled midpoint at `10 ^ 24`. -/
  mid : OuterWeights.SineWindowPrep.SInt
  /-- Error bound in `10 ^ -24` ulps. -/
  eUlps : ℕ

/-- Semantic validity of `a : AmpCert` for real amplitude `v : ℝ`. -/
def AmpCert.Valid (a : AmpCert) (v : ℝ) : Prop :=
  |v - a.mid.toReal / (OuterWeights.SineWindowPrep.scale24 : ℝ)| ≤
    (a.eUlps : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ)

/-- Force all fields of `a : AmpCert` to WHNF so `decide +kernel` avoids thunk buildup. -/
def withForcedAmpCert {α : Type} (a : AmpCert) (f : AmpCert → α) : α :=
  (AmpCert.casesOn (motive := fun _ ↦ (AmpCert → α) → α) a fun mid eUlps k ↦
    OuterWeights.SineWindowPrep.SInt.casesOn
      (OuterWeights.SineWindowPrep.mkStrictSInt mid.neg mid.mag) fun n m ↦
      OuterWeights.SineWindowPrep.withForcedBool n fun n' ↦
      OuterWeights.SineWindowPrep.withForcedNat eUlps fun e' ↦
        k ⟨⟨n', m⟩, e'⟩) f

theorem withForcedAmpCert_eq {α : Type} (a : AmpCert) (f : AmpCert → α) :
    withForcedAmpCert a f = f a := by
  rcases a with ⟨⟨n, m⟩, e⟩
  dsimp only [withForcedAmpCert]
  rw [OuterWeights.SineWindowPrep.mkStrictSInt_eq]
  simp only [withForcedBool_eq, withForcedNat_eq]

/-- Guard-free interval multiplication `(a.mid, a.eUlps) * (tMid, tErr)` at `scale24 = 10 ^ 24`. -/
def mulAmpScalar (a : AmpCert) (tMid : OuterWeights.SineWindowPrep.SInt) (tErr : ℕ) : AmpCert :=
  let S := OuterWeights.SineWindowPrep.scale24
  let prodMid := (a.mid.mul tMid).divScale24
  let num := a.mid.mag * tErr + tMid.mag * a.eUlps + a.eUlps * tErr
  let prodErr := (num + S - 1) / S + 1
  withForcedAmpCert ⟨prodMid, prodErr⟩ id

theorem mulAmpScalar_valid {a : AmpCert} {tMid : OuterWeights.SineWindowPrep.SInt} {tErr : ℕ}
    {v w : ℝ} (ha : a.Valid v)
    (ht : |w - tMid.toReal / (OuterWeights.SineWindowPrep.scale24 : ℝ)| ≤
      (tErr : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ)) :
    (mulAmpScalar a tMid tErr).Valid (v * w) := by
  dsimp only [mulAmpScalar]
  rw [withForcedAmpCert_eq]
  dsimp only [id, AmpCert.Valid]
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hS2_pos : 0 < S ^ 2 := sq_pos_of_pos hS_pos
  let da := v - a.mid.toReal / S
  let dt := w - tMid.toReal / S
  have hda : |da| ≤ (a.eUlps : ℝ) / S := ha
  have hdt : |dt| ≤ (tErr : ℝ) / S := ht
  let raw := a.mid.mul tMid
  have hraw : raw.toReal = a.mid.toReal * tMid.toReal := SInt.toReal_mul _ _
  have htrunc : |raw.toReal / S ^ 2 - raw.divScale24.toReal / S| ≤ 1 / S := by
    have h1 := OuterWeights.SineWindowPrep.SInt.abs_sub_divScale24_mul_le raw
    have heq : raw.toReal / S ^ 2 - raw.divScale24.toReal / S =
        (raw.toReal - raw.divScale24.toReal * S) / S ^ 2 := by field_simp [hS_ne]
    rw [heq, abs_div, abs_of_pos hS2_pos]
    calc |raw.toReal - raw.divScale24.toReal * S| / S ^ 2
        ≤ S / S ^ 2 := div_le_div_of_nonneg_right h1 hS2_pos.le
      _ = 1 / S := by field_simp [hS_ne]
  have hdecomp : v * w - raw.divScale24.toReal / S =
      (a.mid.toReal / S * dt + tMid.toReal / S * da + da * dt) +
        (raw.toReal / S ^ 2 - raw.divScale24.toReal / S) := by
    rw [hraw]; dsimp [da, dt]; field_simp [hS_ne]; ring
  let num := a.mid.mag * tErr + tMid.mag * a.eUlps + a.eUlps * tErr
  have hceil_nat : num ≤ ((num + scale24 - 1) / scale24) *
      OuterWeights.SineWindowPrep.scale24 := by
    have hpos : 0 < scale24 := by norm_num [scale24]
    have hdiv := Nat.div_add_mod (num + scale24 - 1) scale24
    have hmod := Nat.mod_lt (num + OuterWeights.SineWindowPrep.scale24 - 1) hpos
    rw [Nat.mul_comm] at hdiv; omega
  have hceilR : (num : ℝ) / S ≤
      (((num + scale24 - 1) / scale24 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hS_pos]; dsimp only [S]; exact_mod_cast hceil_nat
  have ht1 : |a.mid.toReal / S * dt| ≤ (a.mid.mag : ℝ) / S * ((tErr : ℝ) / S) := by
    rw [abs_mul, abs_div, abs_of_pos hS_pos, OuterWeights.SineWindowPrep.SInt.abs_toReal]
    exact mul_le_mul_of_nonneg_left hdt (by positivity)
  have ht2 : |tMid.toReal / S * da| ≤ (tMid.mag : ℝ) / S * ((a.eUlps : ℝ) / S) := by
    rw [abs_mul, abs_div, abs_of_pos hS_pos, OuterWeights.SineWindowPrep.SInt.abs_toReal]
    exact mul_le_mul_of_nonneg_left hda (by positivity)
  have ht3 : |da * dt| ≤ (a.eUlps : ℝ) / S * ((tErr : ℝ) / S) := by
    rw [abs_mul]; exact mul_le_mul hda hdt (abs_nonneg _) (by positivity)
  have hlin : |a.mid.toReal / S * dt + tMid.toReal / S * da + da * dt| ≤
      (((num + scale24 - 1) / scale24 : ℕ) : ℝ) / S := by
    have htri1 := abs_add_le (a.mid.toReal / S * dt + tMid.toReal / S * da) (da * dt)
    have htri2 := abs_add_le (a.mid.toReal / S * dt) (tMid.toReal / S * da)
    have hnum_eq :
        (a.mid.mag : ℝ) / S * ((tErr : ℝ) / S) +
          (tMid.mag : ℝ) / S * ((a.eUlps : ℝ) / S) +
          (a.eUlps : ℝ) / S * ((tErr : ℝ) / S) = ((num : ℝ) / S) / S := by
      dsimp [num]; push_cast; field_simp [hS_ne]
    have hle := div_le_div_of_nonneg_right hceilR hS_pos.le
    linarith only [ht1, ht2, ht3, htri1, htri2, hnum_eq, hle]
  rw [hdecomp]
  have htri := abs_add_le (a.mid.toReal / S * dt + tMid.toReal / S * da + da * dt)
    (raw.toReal / S ^ 2 - raw.divScale24.toReal / S)
  have hrhs : ((((num + OuterWeights.SineWindowPrep.scale24 - 1) /
      OuterWeights.SineWindowPrep.scale24 + 1 : ℕ) : ℝ)) / S =
      (((num + scale24 - 1) / scale24 : ℕ) : ℝ) / S +
        1 / S := by
    push_cast; ring
  change |_ + _| ≤ ((((num + OuterWeights.SineWindowPrep.scale24 - 1) /
    OuterWeights.SineWindowPrep.scale24 + 1 : ℕ) : ℝ)) / S
  linarith only [hlin, htrunc, htri, hrhs]

/-- Integer numerator bound on `|v - w| * 10 ^ 24` given `a.Valid v` and `b.Valid w`. -/
def ampDiffBound (a b : AmpCert) : ℕ :=
  Nat.add (Nat.add (a.mid.subStrict b.mid).mag a.eUlps) b.eUlps

theorem ampDiffBound_spec {a b : AmpCert} {v w : ℝ} (ha : a.Valid v) (hb : b.Valid w) :
    |v - w| ≤ (ampDiffBound a b : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ) := by
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hdecomp : v - w = (v - a.mid.toReal / S) - (w - b.mid.toReal / S) +
      (a.mid.sub b.mid).toReal / S := by
    rw [OuterWeights.SineWindowPrep.SInt.toReal_sub]; field_simp [hS_ne]; ring
  have hmid : |(a.mid.sub b.mid).toReal / S| = ((a.mid.sub b.mid).mag : ℝ) / S := by
    rw [abs_div, abs_of_pos hS_pos, OuterWeights.SineWindowPrep.SInt.abs_toReal]
  have htri1 := abs_add_le ((v - a.mid.toReal / S) - (w - b.mid.toReal / S))
    ((a.mid.sub b.mid).toReal / S)
  have htri2 := abs_sub_le (v - a.mid.toReal / S) 0 (w - b.mid.toReal / S)
  simp only [sub_zero, zero_sub, abs_neg] at htri2
  rw [hdecomp]
  dsimp only [ampDiffBound, AmpCert.Valid] at ha hb ⊢
  simp only [OuterWeights.SineWindowPrep.SInt.subStrict_eq, Nat.add_eq]
  have hrhs : (((a.mid.sub b.mid).mag + a.eUlps + b.eUlps : ℕ) : ℝ) / S =
      ((a.mid.sub b.mid).mag : ℝ) / S + (a.eUlps : ℝ) / S + (b.eUlps : ℝ) / S := by
    push_cast; ring
  change |_ + _| ≤ (((a.mid.sub b.mid).mag + a.eUlps + b.eUlps : ℕ) : ℝ) / S
  linarith

/-- Integer numerator bound on `|v| * 10 ^ 24` given `a.Valid v`. -/
def ampZeroBound (a : AmpCert) : ℕ :=
  Nat.add a.mid.mag a.eUlps

theorem ampZeroBound_spec {a : AmpCert} {v : ℝ} (ha : a.Valid v) :
    |v| ≤ (ampZeroBound a : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ) := by
  have hz : (⟨.ofNat 0, 0⟩ : AmpCert).Valid 0 := by
    simp [AmpCert.Valid, OuterWeights.SineWindowPrep.SInt.toReal_ofNat]
  have hd := ampDiffBound_spec ha hz
  have hmag : (a.mid.sub (.ofNat 0)).mag = a.mid.mag := by
    have h1 := OuterWeights.SineWindowPrep.SInt.abs_toReal (a.mid.sub (.ofNat 0))
    have h2 := OuterWeights.SineWindowPrep.SInt.abs_toReal a.mid
    rw [OuterWeights.SineWindowPrep.SInt.toReal_sub, OuterWeights.SineWindowPrep.SInt.toReal_ofNat,
      Nat.cast_zero, sub_zero] at h1
    exact_mod_cast h1.symm.trans h2
  simpa [ampZeroBound, ampDiffBound, SInt.subStrict_eq, Nat.add_eq, hmag]
    using hd

/-- Expand one Möttönen `Ry` cascade level `(a, (cMid, sMid, e)) ↦ [a * cos, a * sin]`. -/
def expandAmpStep : List AmpCert → List OuterWeights.SineWindowPrep.TrigCert → List AmpCert
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, t :: ts =>
      withForcedAmpCert (mulAmpScalar a t.cMid t.eUlps) fun c0 ↦
      withForcedAmpCert (mulAmpScalar a t.sMid t.eUlps) fun c1 ↦
        c0 :: c1 :: expandAmpStep as ts

theorem expandAmpStep_spec :
    ∀ (amps : List AmpCert) (trigs : List OuterWeights.SineWindowPrep.TrigCert) (f θ : ℕ → ℝ),
      amps.length = trigs.length →
      (∀ i (hi : i < amps.length), (amps[i]'hi).Valid (f i)) →
      (∀ i (hi : i < trigs.length), (trigs[i]'hi).Valid (θ i)) →
      (expandAmpStep amps trigs).length = 2 * amps.length ∧
        ∀ j (hj : j < (expandAmpStep amps trigs).length),
          ((expandAmpStep amps trigs)[j]'hj).Valid
            (if j % 2 = 0 then f (j / 2) * Real.cos (θ (j / 2))
             else f (j / 2) * Real.sin (θ (j / 2)))
  | [], [], _, _, _, _, _ => ⟨rfl, fun _ hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  | _ :: _, [], _, _, hlen, _, _ => absurd hlen (Nat.succ_ne_zero _)
  | [], _ :: _, _, _, hlen, _, _ => absurd hlen.symm (Nat.succ_ne_zero _)
  | a :: as, t :: ts, f, θ, hlen, ha, ht => by
      have hlen' : as.length = ts.length := Nat.succ.inj hlen
      obtain ⟨ih_len, ih_val⟩ := expandAmpStep_spec as ts (fun i ↦ f (i + 1)) (fun i ↦ θ (i + 1))
        hlen' (fun i hi ↦ ha (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi ↦ ht (i + 1) (Nat.succ_lt_succ hi))
      have hexp_cons :
          expandAmpStep (a :: as) (t :: ts) =
            mulAmpScalar a t.cMid t.eUlps :: mulAmpScalar a t.sMid t.eUlps ::
              expandAmpStep as ts := by
        dsimp only [expandAmpStep]
        simp only [withForcedAmpCert_eq]
      refine ⟨by rw [hexp_cons]; dsimp; omega, fun j hj ↦ ?_⟩
      match j with
      | 0 =>
          simp only [hexp_cons, List.getElem_cons_zero, Nat.zero_mod, ↓reduceIte, Nat.zero_div]
          exact mulAmpScalar_valid (ha 0 (Nat.zero_lt_succ _)) (ht 0 (Nat.zero_lt_succ _)).1
      | 1 =>
          simp only [hexp_cons, List.getElem_cons_succ, List.getElem_cons_zero,
            show 1 % 2 = 1 from rfl, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte,
            show 1 / 2 = 0 from rfl]
          exact mulAmpScalar_valid (ha 0 (Nat.zero_lt_succ _)) (ht 0 (Nat.zero_lt_succ _)).2
      | j' + 2 =>
          rw [hexp_cons] at hj
          have hj' : j' < (expandAmpStep as ts).length := by simp at hj; omega
          simp only [hexp_cons, List.getElem_cons_succ]
          have hv := ih_val j' hj'
          have hmod : (j' + 2) % 2 = j' % 2 := Nat.add_mod_right j' 2
          have hdiv : (j' + 2) / 2 = j' / 2 + 1 := Nat.add_div_right j' (by decide)
          rwa [hmod, hdiv]

/-- Auxiliary top-down interval evaluator for `mottonenCascade q s`. -/
def evalMottonenAux (q : ℕ) :
    ℕ → List WordPairTree → List AmpCert → ℕ → ℕ → Bool × List AmpCert × ℕ × ℕ
  | 0, [], amps, nl, tc => (true, amps, nl, tc)
  | 0, _ :: _, _, _, _ => (false, [], 0, 0)
  | _ + 1, [], _, _, _ => (false, [], 0, 0)
  | s' + 1, tr :: trs, amps, nl, tc =>
      OuterWeights.SineWindowPrep.withForcedNat (q - (s' + 1)) fun k ↦
      Prod.casesOn (evalWordPairTree k tr) fun okTr r1 ↦
      Prod.casesOn r1 fun trigs r2 ↦
      Prod.casesOn r2 fun nl1 tc1 ↦
      if !okTr then (false, [], 0, 0)
      else
        withForcedList (expandAmpStep amps trigs) fun amps' ↦
        OuterWeights.SineWindowPrep.withForcedNat (nl + nl1) fun nl' ↦
        OuterWeights.SineWindowPrep.withForcedNat (tc + tc1) fun tc' ↦
          evalMottonenAux q s' trs amps' nl' tc'

/-- Full `q`-level Möttönen cascade evaluator starting from `|0⟩` (`[(1, 0)]`). -/
def evalMottonenAmps (q : ℕ) (trs : List WordPairTree) : Bool × List AmpCert × ℕ × ℕ :=
  evalMottonenAux q q trs [⟨.ofNat OuterWeights.SineWindowPrep.scale24, 0⟩] 0 0

theorem evalMottonenAux_spec (q : ℕ) :
    ∀ (s : ℕ) (hs : s ≤ q) (trs : List WordPairTree) (amps : List AmpCert) (nl tc : ℕ)
      (v : Fin (2 ^ (q - s)) → ℝ)
      (hlenA : amps.length = 2 ^ (q - s)),
      (∀ c : Fin (2 ^ (q - s)), (amps[c.val]'(c.isLt.trans_eq hlenA.symm)).Valid (v c)) →
      (evalMottonenAux q s trs amps nl tc).1 = true →
      ∃ (vOut : Fin (2 ^ q) → ℝ) (hlen : (evalMottonenAux q s trs amps nl tc).2.1.length = 2 ^ q),
        (mottonenCascade q s hs trs).count .TOFF = 0 ∧
        tc + (mottonenCascade q s hs trs).count .T =
          (evalMottonenAux q s trs amps nl tc).2.2.2 ∧
        nl ≤ (evalMottonenAux q s trs amps nl tc).2.2.1 ∧
        OuterWeights.SineWindowPrep.VecApprox (mottonenCascade q s hs trs).eval
          (mottonenCascadeIdealU q s hs trs)
          ((((evalMottonenAux q s trs amps nl tc).2.2.1 - nl : ℕ) : ℝ) *
            ((dRzLeafNum : ℝ) / 10 ^ 24)) ∧
        (mottonenCascadeIdealU q s hs trs).1 *ᵥ coarseVec q s hs v =
          (fun x : Fin (2 ^ q) ↦ (vOut x : ℂ)) ∧
        ∀ x : Fin (2 ^ q),
          ((evalMottonenAux q s trs amps nl tc).2.1[x.val]'(x.isLt.trans_eq hlen.symm)).Valid
            (vOut x) := by
  intro s
  induction s with
  | zero =>
      intro hs trs amps nl tc v hlenA hval hok
      cases trs with
      | cons _ _ => simp [evalMottonenAux] at hok
      | nil =>
          dsimp only [evalMottonenAux, mottonenCascade, mottonenCascadeIdealU] at hok ⊢
          let vOut : Fin (2 ^ q) → ℝ := v
          have hlen' : amps.length = 2 ^ q := hlenA
          refine ⟨vOut, hlen', ?_, ?_, le_rfl, ?_, ?_, ?_⟩
          · simp
          · simp
          · simpa [Circuit.identity] using VecApprox.refl (1 : Unitary (2 ^ q))
          · ext x; rw [Submonoid.coe_one, Matrix.one_mulVec, coarseVec_zero]
          · intro x; exact hval x
  | succ s' ih =>
      intro hs trs amps nl tc v hlenA hval hok
      cases trs with
      | nil => simp [evalMottonenAux] at hok
      | cons tr trs' =>
          let k := q - (s' + 1)
          have heval_step :
              evalMottonenAux q (s' + 1) (tr :: trs') amps nl tc =
                if !(evalWordPairTree k tr).1 then (false, [], 0, 0)
                else evalMottonenAux q s' trs'
                  (expandAmpStep amps (evalWordPairTree k tr).2.1)
                  (nl + (evalWordPairTree k tr).2.2.1)
                  (tc + (evalWordPairTree k tr).2.2.2) := by
            dsimp only [evalMottonenAux, k]
            simp only [OuterWeights.SineWindowPrep.withForcedNat_eq, withForcedList_eq]
          have hr1' : (evalWordPairTree k tr).1 = true := by
            rw [heval_step] at hok
            by_contra hf
            simp [Bool.eq_false_iff.mpr hf] at hok
          have heval_eq :
              evalMottonenAux q (s' + 1) (tr :: trs') amps nl tc =
                evalMottonenAux q s' trs'
                  (expandAmpStep amps (evalWordPairTree k tr).2.1)
                  (nl + (evalWordPairTree k tr).2.2.1)
                  (tc + (evalWordPairTree k tr).2.2.2) := by
            rw [heval_step]; simp [hr1']
          rw [heval_eq] at hok ⊢
          obtain ⟨hlenT, hvalT⟩ := evalWordPairTree_trigs k tr hr1'
          let rCtrl : QRegister k q := QRegister.block (s' + 1) k (by omega)
          let tgt : Wire q := ⟨s', by omega⟩
          have hdisj : rCtrl.DisjointWires (QRegister.singleton tgt) := by
            rw [QRegister.disjoint_iff]
            intro i j hij; have hv := congrArg Fin.val hij; simp [rCtrl, tgt] at hv; omega
          obtain ⟨htoffT, htT, hapT⟩ := wordPairTreeCircuit_spec k rCtrl tgt hdisj tr hr1'
          let f : ℕ → ℝ := fun i ↦ if hi : i < 2 ^ k then v ⟨i, hi⟩ else 0
          let θ : ℕ → ℝ := fun i ↦
            if hi : i < 2 ^ k then wordPairTreeIdeal k tr ⟨i, hi⟩ / 2 else 0
          obtain ⟨hlenE, hvalE⟩ := expandAmpStep_spec amps (evalWordPairTree k tr).2.1 f θ
            (hlenA.trans hlenT.symm)
            (fun i hi ↦ by have hi' : i < 2 ^ k := hlenA ▸ hi; simpa [f, hi'] using hval ⟨i, hi'⟩)
            (fun i hi ↦ by
              have hi' : i < 2 ^ k := hlenT ▸ hi; simpa [θ, hi'] using hvalT ⟨i, hi'⟩)
          have hsub_eq : q - s' = k + 1 := by omega
          have hlenE' :
              (expandAmpStep amps (evalWordPairTree k tr).2.1).length = 2 ^ (q - s') := by
            rw [hlenE, hlenA, hsub_eq, pow_succ']
          let vNext : Fin (2 ^ (q - s')) → ℝ := fun c' ↦
            let c : Fin (2 ^ k) := ⟨c'.val / 2,
              Nat.div_lt_of_lt_mul (c'.isLt.trans_eq (by rw [hsub_eq, pow_succ']))⟩
            if c'.val % 2 = 0 then v c * Real.cos (wordPairTreeIdeal k tr c / 2)
            else v c * Real.sin (wordPairTreeIdeal k tr c / 2)
          have hvalNext : ∀ c' : Fin (2 ^ (q - s')),
              ((expandAmpStep amps (evalWordPairTree k tr).2.1)[c'.val]'(c'.isLt.trans_eq
                hlenE'.symm)).Valid (vNext c') := by
            intro c'
            have hj : c'.val < (expandAmpStep amps (evalWordPairTree k tr).2.1).length :=
              c'.isLt.trans_eq hlenE'.symm
            have hv := hvalE c'.val hj
            have hdiv_lt : c'.val / 2 < 2 ^ k :=
              Nat.div_lt_of_lt_mul (c'.isLt.trans_eq (by rw [hsub_eq, pow_succ']))
            simpa [vNext, f, θ, hdiv_lt] using hv
          obtain ⟨vOut, hlenOut, htoffR, htR, hnlR, hapR, hvecR, hvalidOut⟩ :=
            ih (by omega) trs' (expandAmpStep amps (evalWordPairTree k tr).2.1)
              (nl + (evalWordPairTree k tr).2.2.1) (tc + (evalWordPairTree k tr).2.2.2)
              vNext hlenE' hvalNext hok
          dsimp only [mottonenCascade, mottonenCascadeIdealU]
          refine ⟨vOut, hlenOut, ?_, ?_, by omega, ?_, ?_, hvalidOut⟩
          · rw [Circuit.count_seq, htoffT, htoffR]
          · rw [Circuit.count_seq, htT]; omega
          · rw [Circuit.eval_seq]
            have hmul := OuterWeights.SineWindowPrep.VecApprox.mul hapR hapT
            refine hmul.mono (le_of_eq ?_)
            have hsub_nl : (evalMottonenAux q s' trs'
                (expandAmpStep amps (evalWordPairTree k tr).2.1)
                (nl + (evalWordPairTree k tr).2.2.1)
                (tc + (evalWordPairTree k tr).2.2.2)).2.2.1 - nl =
              ((evalMottonenAux q s' trs'
                (expandAmpStep amps (evalWordPairTree k tr).2.1)
                (nl + (evalWordPairTree k tr).2.2.1)
                (tc + (evalWordPairTree k tr).2.2.2)).2.2.1 -
                (nl + (evalWordPairTree k tr).2.2.1)) +
                (evalWordPairTree k tr).2.2.1 := by omega
            rw [hsub_nl]; push_cast; ring
          · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
              mottonenCascade_step_mulVec q s' hs tr v]
            exact hvecR

/-- Auxiliary builder for `k + 1` odd-multiple `TrigCert`s `[tCur, tCur + tStep, ...]`. -/
def buildOddTrigGridAux (tStep : OuterWeights.SineWindowPrep.TrigCert) :
    ℕ → OuterWeights.SineWindowPrep.TrigCert → List OuterWeights.SineWindowPrep.TrigCert × Bool
  | 0, tCur => ([tCur], true)
  | k + 1, tCur =>
      withForcedTrigRes (addTrig tCur tStep) fun tNext ok1 ↦
      Prod.casesOn (buildOddTrigGridAux tStep k tNext) fun tsR okR ↦
      OuterWeights.SineWindowPrep.withForcedBool (ok1 && okR) fun ok ↦
        (tCur :: tsR, ok)

/-- Build `n` odd-multiple `TrigCert`s `[(2 * i + 1) * θ₀]` (`i = 0 .. n - 1`) from `tHalf`. -/
def buildOddTrigGrid (n : ℕ) (tHalf : OuterWeights.SineWindowPrep.TrigCert) :
    List OuterWeights.SineWindowPrep.TrigCert × Bool :=
  match n with
  | 0 => ([], true)
  | k + 1 =>
      withForcedTrigRes (addTrig tHalf tHalf) fun tStep ok0 ↦
      Prod.casesOn (buildOddTrigGridAux tStep k tHalf) fun tsR okR ↦
      OuterWeights.SineWindowPrep.withForcedBool (ok0 && okR) fun ok ↦
        (tsR, ok)

theorem buildOddTrigGridAux_spec {tStep : OuterWeights.SineWindowPrep.TrigCert} {δ : ℝ}
    (hStep : tStep.Valid δ) :
    ∀ (k : ℕ) (tCur : OuterWeights.SineWindowPrep.TrigCert) (α : ℝ),
      tCur.Valid α →
      (buildOddTrigGridAux tStep k tCur).2 = true →
      (buildOddTrigGridAux tStep k tCur).1.length = k + 1 ∧
        ∀ i (hi : i < (buildOddTrigGridAux tStep k tCur).1.length),
          ((buildOddTrigGridAux tStep k tCur).1[i]'hi).Valid (α + (i : ℝ) * δ)
  | 0, tCur, α, hCur, _ => by
      refine ⟨rfl, fun i hi ↦ ?_⟩
      have hi0 : i = 0 := by dsimp [buildOddTrigGridAux] at hi; omega
      subst hi0; simpa [buildOddTrigGridAux] using hCur
  | k + 1, tCur, α, hCur, hok => by
      dsimp only [buildOddTrigGridAux] at hok ⊢
      simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq,
        OuterWeights.SineWindowPrep.withForcedBool_eq, Bool.and_eq_true] at hok ⊢
      have hNext := OuterWeights.SineWindowPrep.addTrig_valid hCur hStep hok.1
      obtain ⟨ih_len, ih_val⟩ :=
        buildOddTrigGridAux_spec hStep k (OuterWeights.SineWindowPrep.addTrig tCur tStep).1
          (α + δ) hNext hok.2
      refine ⟨congrArg Nat.succ ih_len, fun i hi ↦ ?_⟩
      cases i with
      | zero => simpa using hCur
      | succ j =>
          have hv := ih_val j (Nat.lt_of_succ_lt_succ hi)
          have heq : α + δ + (j : ℝ) * δ = α + ((j + 1 : ℕ) : ℝ) * δ := by push_cast; ring
          rwa [heq] at hv

theorem buildOddTrigGrid_spec (n : ℕ) {tHalf : OuterWeights.SineWindowPrep.TrigCert} {θ₀ : ℝ}
    (hHalf : tHalf.Valid θ₀) (hok : (buildOddTrigGrid n tHalf).2 = true) :
    (buildOddTrigGrid n tHalf).1.length = n ∧
      ∀ i (hi : i < (buildOddTrigGrid n tHalf).1.length),
        ((buildOddTrigGrid n tHalf).1[i]'hi).Valid ((2 * (i : ℝ) + 1) * θ₀) := by
  cases n with
  | zero => exact ⟨rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | succ k =>
      dsimp only [buildOddTrigGrid] at hok ⊢
      simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq,
        OuterWeights.SineWindowPrep.withForcedBool_eq, Bool.and_eq_true] at hok ⊢
      have hStep := OuterWeights.SineWindowPrep.addTrig_valid hHalf hHalf hok.1
      obtain ⟨hlen, hval⟩ := buildOddTrigGridAux_spec hStep k tHalf θ₀ hHalf hok.2
      refine ⟨hlen, fun i hi ↦ ?_⟩
      have hv := hval i hi
      have heq : θ₀ + (i : ℝ) * (θ₀ + θ₀) = (2 * (i : ℝ) + 1) * θ₀ := by ring
      rwa [heq] at hv

/-- Default zero `AmpCert`. -/
def zeroAmpCert : AmpCert := ⟨.ofNat 0, 0⟩

/-- Default identity `TrigCert`. -/
def zeroTrigCert : OuterWeights.SineWindowPrep.TrigCert := ⟨.ofNat 0, .ofNat 0, 0⟩

/-- Sum of squared ulp bounds for `ampsHi` (`2 * nHi` entries) against `(a0 * sin, a1 * cos)` on
`xh < D` and `0` on `D ≤ xh < nHi`. -/
def sumHiErrSq (D : ℕ) (a0 a1 : AmpCert) (ampsHi : List AmpCert)
    (hiTrigs : List OuterWeights.SineWindowPrep.TrigCert) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc =>
      let aEv := ampsHi.getD (2 * k) zeroAmpCert
      let aOd := ampsHi.getD (2 * k + 1) zeroAmpCert
      let term :=
        if k < D then
          let tr := hiTrigs.getD k zeroTrigCert
          let d0 := ampDiffBound aEv (mulAmpScalar a0 tr.sMid tr.eUlps)
          let d1 := ampDiffBound aOd (mulAmpScalar a1 tr.cMid tr.eUlps)
          d0 * d0 + d1 * d1
        else
          let d0 := ampZeroBound aEv
          let d1 := ampZeroBound aOd
          d0 * d0 + d1 * d1
      OuterWeights.SineWindowPrep.withForcedNat (acc + term) fun acc' ↦
        sumHiErrSq D a0 a1 ampsHi hiTrigs k acc'

/-- Sum of squared ulp bounds for one half-branch of `ampsLo` (`offset + z`, `z < halfLo`). -/
def sumLoErrSq (offset : ℕ) (bCert : AmpCert) (useSin : Bool) (ampsLo : List AmpCert)
    (loTrigs : List OuterWeights.SineWindowPrep.TrigCert) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc =>
      let a := ampsLo.getD (offset + k) zeroAmpCert
      let tr := loTrigs.getD k zeroTrigCert
      let tgt := if useSin then mulAmpScalar bCert tr.sMid tr.eUlps
                 else mulAmpScalar bCert tr.cMid tr.eUlps
      let d := ampDiffBound a tgt
      OuterWeights.SineWindowPrep.withForcedNat (acc + d * d) fun acc' ↦
        sumLoErrSq offset bCert useSin ampsLo loTrigs k acc'

/-- Certificate record for a zero-ancilla Two-Gear sine-window regime `(M, mLow)`. -/
structure TwoGearRegimeData where
  /-- Window cap `M` (`L = M + 1 = D * 2 ^ mLow`). -/
  M : ℕ
  /-- Low-gear QPE bit count `mLow`. -/
  mLow : ℕ
  /-- Coarse period `D = (M + 1) / 2 ^ mLow`. -/
  D : ℕ
  /-- High-gear QPE bit count `mHi = 16 - mLow`. -/
  mHi : ℕ
  /-- Scaled `cos(π / (2 * (M + 1)))` midpoint at `10 ^ 24`. -/
  c0Mid : ℕ
  /-- Scaled `sin(π / (2 * (M + 1)))` midpoint at `10 ^ 24`. -/
  s0Mid : ℕ
  /-- Scaled rank-2 high-branch `r = 0` factor `a₀` at `10 ^ 24`. -/
  a0Nat : ℕ
  /-- Scaled rank-2 high-branch `r = 1` factor `a₁` at `10 ^ 24`. -/
  a1Nat : ℕ
  /-- Scaled rank-2 low-branch `r = 0` factor `b₀` at `10 ^ 24`. -/
  b0Nat : ℕ
  /-- Scaled rank-2 low-branch `r = 1` factor `b₁` at `10 ^ 24`. -/
  b1Nat : ℕ
  /-- Upper bound on `√errSqHi` in `10 ^ -24` ulps. -/
  eHiNum : ℕ
  /-- Upper bound on `√errSqLo0` in `10 ^ -24` ulps. -/
  eLo0Num : ℕ
  /-- Upper bound on `√errSqLo1` in `10 ^ -24` ulps. -/
  eLo1Num : ℕ
  /-- Exact total `T`-gate count `tcHi + tcLo`. -/
  tWin : ℕ
  /-- `(mHi + 1)`-level Walsh `Ry` trees on `QRegister.block (mLow - 1) (mHi + 1)`. -/
  hiTrees : List WordPairTree
  /-- `(mLow - 1)`-level Walsh `Ry` trees preparing `ampsLo` on `QRegister.block 0 mLow`. -/
  loTrees : List WordPairTree

/-- Fast pure-`ℕ` rank-2 factored verifier (`< 50 ms` in `decide +kernel`) certifying `T`-count
`d.tWin` and `L²` synthesis accuracy `≤ 5 / 10 ^ 9` against `windowVec 16 d.M`. -/
def checkTwoGearRegime (d : TwoGearRegimeData) : Bool :=
  let S := OuterWeights.SineWindowPrep.scale24
  let L := d.M + 1
  decide (2 ≤ d.mLow ∧ d.mLow ≤ 14 ∧ d.mHi = 16 - d.mLow ∧
    1 ≤ d.D ∧ d.D ≤ 2 ^ d.mHi ∧ L = d.D * 2 ^ d.mLow ∧
    2 * S ≤ d.a0Nat * d.b0Nat ∧ 2 * S ≤ d.a1Nat * d.b1Nat ∧
    (d.a0Nat * d.b0Nat - 2 * S) ^ 2 * L ≤ (2 * S * S) ^ 2 ∧
    (2 * S * S) ^ 2 ≤ (d.a0Nat * d.b0Nat + 2 * S) ^ 2 * L ∧
    (d.a1Nat * d.b1Nat - 2 * S) ^ 2 * L ≤ (2 * S * S) ^ 2 ∧
    (2 * S * S) ^ 2 ≤ (d.a1Nat * d.b1Nat + 2 * S) ^ 2 * L ∧
    d.D * (d.a0Nat * d.a0Nat) ≤ 2 * (S * S) ∧
    d.D * (d.a1Nat * d.a1Nat) ≤ 2 * (S * S) ∧
    d.hiTrees.length = d.mHi + 1 ∧ d.loTrees.length = d.mLow - 1) &&
  checkBaseTrigNatSC L d.c0Mid d.s0Mid &&
  let t0 : OuterWeights.SineWindowPrep.TrigCert := ⟨.ofNat d.c0Mid, .ofNat d.s0Mid, e0SC⟩
  withForcedTrigRes (iterDoubleTrig d.mLow t0)
    fun tHi0 okDbl ↦
    okDbl &&
    Prod.casesOn (buildOddTrigGrid d.D tHi0) fun hiTrigsRaw okGHi ↦
    OuterWeights.SineWindowPrep.withForcedNat (2 ^ (d.mLow - 1)) fun halfLo ↦
    Prod.casesOn (buildOddTrigGrid halfLo t0) fun loTrigsRaw okGLo ↦
    okGHi && okGLo &&
    withForcedList hiTrigsRaw fun hiTrigs ↦
    withForcedList loTrigsRaw.reverse fun loTrigs ↦
    Prod.casesOn (evalMottonenAmps (d.mHi + 1) d.hiTrees) fun okRHi rHi1 ↦
    Prod.casesOn rHi1 fun ampsHi rHi2 ↦
    Prod.casesOn rHi2 fun nlHi tcHi ↦
    Prod.casesOn
      (evalMottonenAux d.mLow (d.mLow - 1) d.loTrees [⟨.ofNat S, 0⟩, ⟨.ofNat S, 0⟩] 0 0)
      fun okRLo rLo1 ↦
    Prod.casesOn rLo1 fun ampsLo rLo2 ↦
    Prod.casesOn rLo2 fun nlLo tcLo ↦
    okRHi && okRLo &&
    let a0 : AmpCert := ⟨.ofNat d.a0Nat, 0⟩
    let a1 : AmpCert := ⟨.ofNat d.a1Nat, 0⟩
    let b0 : AmpCert := ⟨.ofNat d.b0Nat, 0⟩
    let b1 : AmpCert := ⟨.ofNat d.b1Nat, 0⟩
    OuterWeights.SineWindowPrep.withForcedNat (sumHiErrSq d.D a0 a1 ampsHi hiTrigs (2 ^ d.mHi) 0)
      fun errSqHi ↦
    OuterWeights.SineWindowPrep.withForcedNat (sumLoErrSq 0 b0 false ampsLo loTrigs halfLo 0)
      fun errSqLo0 ↦
    OuterWeights.SineWindowPrep.withForcedNat (sumLoErrSq halfLo b1 true ampsLo loTrigs halfLo 0)
      fun errSqLo1 ↦
    let nlTot := nlHi + nlLo
    let tcTot := tcHi + tcLo
    decide (errSqHi ≤ d.eHiNum * d.eHiNum ∧
      errSqLo0 ≤ d.eLo0Num * d.eLo0Num ∧
      errSqLo1 ≤ d.eLo1Num * d.eLo1Num ∧
      tcTot = d.tWin ∧
      nlTot * dRzLeafNum + d.eHiNum + 2 * (d.eLo0Num + d.eLo1Num) + 1024 ≤ 5 * 10 ^ 15)

/-- Reflection-based real unitary mapping `basisState 0` to a real unit vector `u` (`0 ≤ u 0`). -/
noncomputable def realHouseholderWindowUnitary {d : ℕ} [NeZero d]
    (u : Fin d → ℝ) (hu0 : 0 ≤ u 0) (hu : ∑ i : Fin d, u i * u i = 1) : Unitary d := by
  let w : Fin d → ℝ := fun i ↦ u i + if i = 0 then 1 else 0
  let c : ℝ := 1 + u 0
  have hc_pos : 0 < c := by dsimp [c]; linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hw_sum : ∑ k : Fin d, w k * w k = 2 * c := by
    have hpt (k : Fin d) : w k * w k = u k * u k + if k = 0 then 2 * u 0 + 1 else 0 := by
      rcases eq_or_ne k 0 with rfl | hk
      · dsimp only [w]; simp only [↓reduceIte]; ring
      · dsimp only [w]; simp only [hk, ↓reduceIte, add_zero]
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, hu, Finset.sum_ite_eq' Finset.univ (0 : Fin d)]
    simp only [Finset.mem_univ, ↓reduceIte]; dsimp [c]; ring
  let H : Matrix (Fin d) (Fin d) ℂ :=
    fun i j ↦ (((w i * w j) / c - if i = j then 1 else 0 : ℝ) : ℂ)
  have hHerm : Hᴴ = H := by
    ext i j
    rw [Matrix.conjTranspose_apply]
    dsimp only [H]
    rw [Complex.star_def, Complex.conj_ofReal]
    congr 1
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, hji, ↓reduceIte]; ring
  have hSq : H * H = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hreal :
        (∑ k : Fin d, H i k * H k j) =
          ((∑ k : Fin d,
            (w i * w k / c - if i = k then (1 : ℝ) else 0) *
              (w k * w j / c - if k = j then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      dsimp only [H]
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ (Complex.ofReal_mul _ _).symm
    rw [hreal]
    have hsum_r :
        (∑ k : Fin d,
          (w i * w k / c - if i = k then (1 : ℝ) else 0) *
            (w k * w j / c - if k = j then (1 : ℝ) else 0)) =
          if i = j then 1 else 0 := by
      have hexp (k : Fin d) :
          (w i * w k / c - if i = k then (1 : ℝ) else 0) *
              (w k * w j / c - if k = j then (1 : ℝ) else 0) =
            ((w i * w j / (c * c)) * (w k * w k) -
              (if i = k then w k * w j / c else 0)) -
              (if k = j then w i * w k / c else 0) +
              (if i = k then (if k = j then (1 : ℝ) else 0) else 0) := by
        split_ifs <;> (field_simp [hc_ne]; ring)
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hw_sum, Finset.sum_ite_eq Finset.univ i,
        Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq Finset.univ i]
      simp only [Finset.mem_univ, ↓reduceIte]
      rcases eq_or_ne i j with rfl | hij
      · simp only [↓reduceIte]; field_simp [hc_ne]; ring
      · simp only [hij, ↓reduceIte]; field_simp [hc_ne]; ring
    rw [hsum_r]
    by_cases hij : i = j <;> simp [hij]
  refine ⟨H, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, hHerm]
  exact hSq

theorem realHouseholderWindowUnitary_mulVec_zero {d : ℕ} [NeZero d]
    (u : Fin d → ℝ) (hu0 : 0 ≤ u 0) (hu : ∑ i : Fin d, u i * u i = 1) :
    (realHouseholderWindowUnitary u hu0 hu).1 *ᵥ basisState 0 = fun i ↦ (u i : ℂ) := by
  ext i
  let w : Fin d → ℝ := fun k ↦ u k + if k = 0 then 1 else 0
  let c : ℝ := 1 + u 0
  have hc_pos : 0 < c := by dsimp [c]; linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hw0 : w 0 = c := by dsimp only [w, c]; simp only [↓reduceIte]; ring
  change (∑ k : Fin d,
    (((w i * w k) / c - if i = k then 1 else 0 : ℝ) : ℂ) * basisState 0 k) = (u i : ℂ)
  rw [Fintype.sum_eq_single 0 (fun k hk ↦ by simp [basisState, hk])]
  simp only [basisState, Pi.single_eq_same, mul_one, hw0]
  congr 1
  rcases eq_or_ne i 0 with rfl | hi0
  · dsimp only [w, c]; simp only [↓reduceIte]; field_simp [hc_ne]; ring
  · dsimp only [w]; simp only [hi0, ↓reduceIte, add_zero]; field_simp [hc_ne]; ring

/-- Ideal `16`-qubit unitary mapping `|0⟩` to `windowVec 16 M (sineWindowCoeff (M + 1))`. -/
noncomputable def idealSineWindowUnitary16 (M : ℕ) (hM1 : 1 ≤ M) (hMlt : M < 2 ^ 16) :
    Unitary (2 ^ 16) := by
  let u : Fin (2 ^ 16) → ℝ := fun x ↦ if x.val ≤ M then sineWindowCoeff (M + 1) x.val else 0
  have hu0 : 0 ≤ u 0 := by
    dsimp only [u, sineWindowCoeff]
    simp only [Fin.val_zero]
    rw [ite_eq_left (Nat.zero_le M), ite_eq_left (Nat.succ_pos M)]
    simp only [Nat.cast_zero, zero_add]
    refine mul_nonneg (Real.sqrt_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
    have hM0 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M + 1)
    have hle : π * (1 / 2) / ((M + 1 : ℕ) : ℝ) ≤ π * 1 / 1 := by
      have hp := Real.pi_pos
      exact div_le_div₀ (by positivity) (by linarith) zero_lt_one hM0
    linarith
  have hu_sum : ∑ x : Fin (2 ^ 16), u x * u x = 1 := by
    have h1 := sum_normSq_windowPhaseVec 16 M hMlt (sineWindowCoeff (M + 1)) 0
    have h2 : ∑ x : Fin (2 ^ 16), u x * u x =
        ∑ x : Fin (2 ^ 16),
          Complex.normSq (windowPhaseVec 16 M (sineWindowCoeff (M + 1)) 0 x) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      dsimp only [u, windowPhaseVec]
      by_cases hx : x.val ≤ M
      · simp [hx, Complex.normSq_ofReal]
      · simp [hx]
    rw [h2, h1]
    exact sum_sq_sineWindowCoeff (by omega)
  exact realHouseholderWindowUnitary u hu0 hu_sum

theorem idealSineWindowUnitary16_mulVec_zero (M : ℕ) (hM1 : 1 ≤ M) (hMlt : M < 2 ^ 16) :
    (idealSineWindowUnitary16 M hM1 hMlt).1 *ᵥ basisState 0 =
      windowVec 16 M (sineWindowCoeff (M + 1)) := by
  dsimp [idealSineWindowUnitary16]
  rw [realHouseholderWindowUnitary_mulVec_zero]
  ext x; dsimp [windowVec]; split_ifs <;> simp

/-- Pure-real vector recurrence for `mottonenCascadeIdealU q s hs trs *ᵥ coarseVec q s hs v`. -/
noncomputable def mottonenIdealVec (q : ℕ) :
    ∀ (s : ℕ), s ≤ q → List WordPairTree → (Fin (2 ^ (q - s)) → ℝ) → Fin (2 ^ q) → ℝ
  | 0, _, _, v => fun x ↦ v x
  | _ + 1, _, [], _ => fun _ ↦ 0
  | s' + 1, hs, tr :: trs, v =>
      let k := q - (s' + 1)
      let vNext : Fin (2 ^ (q - s')) → ℝ := fun c' ↦
        let c : Fin (2 ^ k) := ⟨c'.val / 2, Nat.div_lt_of_lt_mul
          (c'.isLt.trans_eq (by rw [show q - s' = k + 1 by omega, pow_succ']))⟩
        if c'.val % 2 = 0 then v c * Real.cos (wordPairTreeIdeal k tr c / 2)
        else v c * Real.sin (wordPairTreeIdeal k tr c / 2)
      mottonenIdealVec q s' (by omega) trs vNext

theorem mottonenCascadeIdealU_eq_idealVec (q : ℕ) :
    ∀ (s : ℕ) (hs : s ≤ q) (trs : List WordPairTree) (v : Fin (2 ^ (q - s)) → ℝ),
      trs.length = s →
      (mottonenCascadeIdealU q s hs trs).1 *ᵥ coarseVec q s hs v =
        fun x : Fin (2 ^ q) ↦ (mottonenIdealVec q s hs trs v x : ℂ)
  | 0, hs, trs, v, hlen => by
      cases trs with
      | nil =>
          ext x
          dsimp only [mottonenCascadeIdealU, mottonenIdealVec]
          rw [Submonoid.coe_one, Matrix.one_mulVec, coarseVec_zero]
      | cons _ _ => simp at hlen
  | s' + 1, hs, trs, v, hlen => by
      cases trs with
      | nil => simp at hlen
      | cons tr trs' =>
          dsimp only [mottonenCascadeIdealU, mottonenIdealVec]
          rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
            mottonenCascade_step_mulVec q s' hs tr v]
          exact mottonenCascadeIdealU_eq_idealVec q s' (by omega) trs' _ (Nat.succ.inj hlen)

theorem mottonenIdealVec_congr_sector (q : ℕ) :
    ∀ (s : ℕ) (hs : s ≤ q) (trs : List WordPairTree) (v₁ v₂ : Fin (2 ^ (q - s)) → ℝ)
      (x : Fin (2 ^ q)),
      trs.length = s →
      v₁ ⟨x.val / 2 ^ s, Nat.div_lt_of_lt_mul (by
        rw [← pow_add, Nat.add_sub_of_le hs]; exact x.isLt)⟩ =
      v₂ ⟨x.val / 2 ^ s, Nat.div_lt_of_lt_mul (by
        rw [← pow_add, Nat.add_sub_of_le hs]; exact x.isLt)⟩ →
      mottonenIdealVec q s hs trs v₁ x = mottonenIdealVec q s hs trs v₂ x
  | 0, hs, _, v₁, v₂, x, _, heq => by
      dsimp only [mottonenIdealVec]
      simpa [_root_.pow_zero, Nat.div_one] using heq
  | s' + 1, hs, [], _, _, _, hlen, _ => by simp at hlen
  | s' + 1, hs, tr :: trs', v₁, v₂, x, hlen, heq => by
      dsimp only [mottonenIdealVec]
      refine mottonenIdealVec_congr_sector q s' (by omega) trs' _ _ x (Nat.succ.inj hlen) ?_
      have hdiv : (x.val / 2 ^ s') / 2 = x.val / 2 ^ (s' + 1) := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      have harg : (⟨(x.val / 2 ^ s') / 2, by
          rw [hdiv]; exact Nat.div_lt_of_lt_mul (by
            rw [← pow_add, Nat.add_sub_of_le hs]; exact x.isLt)⟩ :
          Fin (2 ^ (q - (s' + 1)))) =
        ⟨x.val / 2 ^ (s' + 1), Nat.div_lt_of_lt_mul (by
          rw [← pow_add, Nat.add_sub_of_le hs]; exact x.isLt)⟩ := by
        ext; exact hdiv
      dsimp only
      rw [harg, heq]

theorem mottonenIdealVec_zero (q : ℕ) :
    ∀ (s : ℕ) (hs : s ≤ q) (trs : List WordPairTree) (x : Fin (2 ^ q)),
      mottonenIdealVec q s hs trs (fun _ ↦ 0) x = 0
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | s' + 1, hs, tr :: trs', x => by
      dsimp only [mottonenIdealVec]
      have hz : (fun c' : Fin (2 ^ (q - s')) ↦
          let c : Fin (2 ^ (q - (s' + 1))) := ⟨c'.val / 2, Nat.div_lt_of_lt_mul
            (c'.isLt.trans_eq (by rw [show q - s' = (q - (s' + 1)) + 1 by omega, pow_succ']))⟩
          if c'.val % 2 = 0 then (0 : ℝ) * Real.cos (wordPairTreeIdeal (q - (s' + 1)) tr c / 2)
          else (0 : ℝ) * Real.sin (wordPairTreeIdeal (q - (s' + 1)) tr c / 2)) = fun _ ↦ 0 := by
        funext c'; split_ifs <;> ring
      rw [hz]
      exact mottonenIdealVec_zero q s' (by omega) trs' x

theorem sumHiErrSq_add_acc (D : ℕ) (a0 a1 : AmpCert) (ampsHi : List AmpCert)
    (hiTrigs : List OuterWeights.SineWindowPrep.TrigCert) :
    ∀ (k acc : ℕ),
      sumHiErrSq D a0 a1 ampsHi hiTrigs k acc =
        acc + sumHiErrSq D a0 a1 ampsHi hiTrigs k 0
  | 0, acc => by simp [sumHiErrSq]
  | k + 1, acc => by
      let aEv := ampsHi.getD (2 * k) zeroAmpCert
      let aOd := ampsHi.getD (2 * k + 1) zeroAmpCert
      let term :=
        if k < D then
          let tr := hiTrigs.getD k zeroTrigCert
          let d0 := ampDiffBound aEv (mulAmpScalar a0 tr.sMid tr.eUlps)
          let d1 := ampDiffBound aOd (mulAmpScalar a1 tr.cMid tr.eUlps)
          d0 * d0 + d1 * d1
        else
          let d0 := ampZeroBound aEv
          let d1 := ampZeroBound aOd
          d0 * d0 + d1 * d1
      dsimp only [sumHiErrSq]
      simp only [OuterWeights.SineWindowPrep.withForcedNat_eq, zero_add]
      rw [sumHiErrSq_add_acc D a0 a1 ampsHi hiTrigs k (acc + term),
        sumHiErrSq_add_acc D a0 a1 ampsHi hiTrigs k term]
      omega

theorem sumHiErrSq_spec (D : ℕ) (a0 a1 : AmpCert) (ampsHi : List AmpCert)
    (hiTrigs : List OuterWeights.SineWindowPrep.TrigCert)
    (vHi : ℕ → ℝ) (θHi : ℕ → ℝ) (va0 va1 : ℝ)
    (ha0 : a0.Valid va0) (ha1 : a1.Valid va1)
    (hTrigs : ∀ j (_hj : j < D), ∃ hlt : j < hiTrigs.length, (hiTrigs[j]'hlt).Valid (θHi j)) :
    ∀ (k : ℕ), 2 * k ≤ ampsHi.length →
      (∀ i (_hi : i < 2 * k), ∃ hlt : i < ampsHi.length, (ampsHi[i]'hlt).Valid (vHi i)) →
      (∑ j ∈ Finset.range k,
        ((vHi (2 * j) - if j < D then va0 * Real.sin (θHi j) else 0) ^ 2 +
          (vHi (2 * j + 1) - if j < D then va1 * Real.cos (θHi j) else 0) ^ 2)) ≤
        (sumHiErrSq D a0 a1 ampsHi hiTrigs k 0 : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ) ^ 2
  | 0, _, _ => by simp [sumHiErrSq]
  | k + 1, hlen, hAmps => by
      let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
      have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
      have hS_ne : S ≠ 0 := ne_of_gt hS_pos
      have ih := sumHiErrSq_spec D a0 a1 ampsHi hiTrigs vHi θHi va0 va1 ha0 ha1 hTrigs k
        (by omega) (fun i hi ↦ hAmps i (by omega))
      rw [Finset.sum_range_succ]
      dsimp only [sumHiErrSq]
      simp only [OuterWeights.SineWindowPrep.withForcedNat_eq, zero_add]
      rw [sumHiErrSq_add_acc]
      obtain ⟨hltEv, hvEv⟩ := hAmps (2 * k) (by omega)
      obtain ⟨hltOd, hvOd⟩ := hAmps (2 * k + 1) (by omega)
      have hgetEv : ampsHi.getD (2 * k) zeroAmpCert = ampsHi[2 * k]'hltEv := by
        simp [List.getD, hltEv]
      have hgetOd : ampsHi.getD (2 * k + 1) zeroAmpCert = ampsHi[2 * k + 1]'hltOd := by
        simp [List.getD, hltOd]
      rw [hgetEv, hgetOd]
      by_cases hkD : k < D
      · simp only [hkD, ↓reduceIte]
        obtain ⟨hltTr, hvTr⟩ := hTrigs k hkD
        have hgetTr : hiTrigs.getD k zeroTrigCert = hiTrigs[k]'hltTr := by
          simp [List.getD, hltTr]
        rw [hgetTr]
        have hd0 := ampDiffBound_spec hvEv (mulAmpScalar_valid ha0 hvTr.2)
        have hd1 := ampDiffBound_spec hvOd (mulAmpScalar_valid ha1 hvTr.1)
        have hsq0 : (vHi (2 * k) - va0 * Real.sin (θHi k)) ^ 2 ≤
            ((ampDiffBound (ampsHi[2 * k]'hltEv)
              (mulAmpScalar a0 (hiTrigs[k]'hltTr).sMid (hiTrigs[k]'hltTr).eUlps) : ℝ) / S) ^ 2 := by
          rw [← sq_abs (vHi (2 * k) - _)]
          exact pow_le_pow_left₀ (abs_nonneg _) hd0 2
        have hsq1 : (vHi (2 * k + 1) - va1 * Real.cos (θHi k)) ^ 2 ≤
            ((ampDiffBound (ampsHi[2 * k + 1]'hltOd)
              (mulAmpScalar a1 (hiTrigs[k]'hltTr).cMid (hiTrigs[k]'hltTr).eUlps) : ℝ) / S) ^ 2 := by
          rw [← sq_abs (vHi (2 * k + 1) - _)]
          exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
        set d0N := ampDiffBound (ampsHi[2 * k]'hltEv)
          (mulAmpScalar a0 (hiTrigs[k]'hltTr).sMid (hiTrigs[k]'hltTr).eUlps)
        set d1N := ampDiffBound (ampsHi[2 * k + 1]'hltOd)
          (mulAmpScalar a1 (hiTrigs[k]'hltTr).cMid (hiTrigs[k]'hltTr).eUlps)
        set restN := sumHiErrSq D a0 a1 ampsHi hiTrigs k 0
        have hrhs : (((d0N * d0N + d1N * d1N + restN : ℕ) : ℝ)) / S ^ 2 =
            (restN : ℝ) / S ^ 2 + (((d0N : ℝ) / S) ^ 2 + ((d1N : ℝ) / S) ^ 2) := by
          push_cast; field_simp [hS_ne]; ring
        change _ ≤ (((d0N * d0N + d1N * d1N + restN : ℕ) : ℝ)) / S ^ 2
        linarith
      · simp only [hkD, ↓reduceIte, sub_zero]
        have hd0 := ampZeroBound_spec hvEv
        have hd1 := ampZeroBound_spec hvOd
        have hsq0 : vHi (2 * k) ^ 2 ≤
            ((ampZeroBound (ampsHi[2 * k]'hltEv) : ℝ) / S) ^ 2 := by
          rw [← sq_abs (vHi (2 * k))]
          exact pow_le_pow_left₀ (abs_nonneg _) hd0 2
        have hsq1 : vHi (2 * k + 1) ^ 2 ≤
            ((ampZeroBound (ampsHi[2 * k + 1]'hltOd) : ℝ) / S) ^ 2 := by
          rw [← sq_abs (vHi (2 * k + 1))]
          exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
        set d0N := ampZeroBound (ampsHi[2 * k]'hltEv)
        set d1N := ampZeroBound (ampsHi[2 * k + 1]'hltOd)
        set restN := sumHiErrSq D a0 a1 ampsHi hiTrigs k 0
        have hrhs : (((d0N * d0N + d1N * d1N + restN : ℕ) : ℝ)) / S ^ 2 =
            (restN : ℝ) / S ^ 2 + (((d0N : ℝ) / S) ^ 2 + ((d1N : ℝ) / S) ^ 2) := by
          push_cast; field_simp [hS_ne]; ring
        change _ ≤ (((d0N * d0N + d1N * d1N + restN : ℕ) : ℝ)) / S ^ 2
        linarith

theorem sumLoErrSq_add_acc (offset : ℕ) (bCert : AmpCert) (useSin : Bool)
    (ampsLo : List AmpCert) (loTrigs : List OuterWeights.SineWindowPrep.TrigCert) :
    ∀ (k acc : ℕ),
      sumLoErrSq offset bCert useSin ampsLo loTrigs k acc =
        acc + sumLoErrSq offset bCert useSin ampsLo loTrigs k 0
  | 0, acc => by simp [sumLoErrSq]
  | k + 1, acc => by
      let a := ampsLo.getD (offset + k) zeroAmpCert
      let tr := loTrigs.getD k zeroTrigCert
      let tgt := if useSin then mulAmpScalar bCert tr.sMid tr.eUlps
                 else mulAmpScalar bCert tr.cMid tr.eUlps
      let d := ampDiffBound a tgt
      dsimp only [sumLoErrSq]
      simp only [OuterWeights.SineWindowPrep.withForcedNat_eq, zero_add]
      rw [sumLoErrSq_add_acc offset bCert useSin ampsLo loTrigs k (acc + d * d),
        sumLoErrSq_add_acc offset bCert useSin ampsLo loTrigs k (d * d)]
      omega

theorem sumLoErrSq_spec (offset : ℕ) (bCert : AmpCert) (useSin : Bool)
    (ampsLo : List AmpCert) (loTrigs : List OuterWeights.SineWindowPrep.TrigCert)
    (vLo : ℕ → ℝ) (θLo : ℕ → ℝ) (vb : ℝ) (hb : bCert.Valid vb) :
    ∀ (k : ℕ) (hlenA : offset + k ≤ ampsLo.length) (hlenT : k ≤ loTrigs.length),
      (∀ z (hz : z < k), (ampsLo[offset + z]'(by omega)).Valid (vLo (offset + z))) →
      (∀ z (hz : z < k), (loTrigs[z]'(by omega)).Valid (θLo z)) →
      (∑ z ∈ Finset.range k,
        (vLo (offset + z) -
          (if useSin then vb * Real.sin (θLo z) else vb * Real.cos (θLo z))) ^ 2) ≤
        (sumLoErrSq offset bCert useSin ampsLo loTrigs k 0 : ℝ) /
          (OuterWeights.SineWindowPrep.scale24 : ℝ) ^ 2
  | 0, _, _, _, _ => by simp [sumLoErrSq]
  | k + 1, hlenA, hlenT, hAmps, hTrigs => by
      let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
      have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
      have hS_ne : S ≠ 0 := ne_of_gt hS_pos
      have ih := sumLoErrSq_spec offset bCert useSin ampsLo loTrigs vLo θLo vb hb k
        (by omega) (by omega) (fun z hz ↦ hAmps z (by omega)) (fun z hz ↦ hTrigs z (by omega))
      rw [Finset.sum_range_succ]
      dsimp only [sumLoErrSq]
      simp only [OuterWeights.SineWindowPrep.withForcedNat_eq, zero_add]
      rw [sumLoErrSq_add_acc]
      have hltA : offset + k < ampsLo.length := by omega
      have hltT : k < loTrigs.length := by omega
      have hgetA : ampsLo.getD (offset + k) zeroAmpCert = ampsLo[offset + k]'hltA := by
        simp [List.getD, hltA]
      have hgetT : loTrigs.getD k zeroTrigCert = loTrigs[k]'hltT := by
        simp [List.getD, hltT]
      rw [hgetA, hgetT]
      have hvA := hAmps k (Nat.lt_succ_self k)
      have hvT := hTrigs k (Nat.lt_succ_self k)
      have hTgt :
          (if useSin then mulAmpScalar bCert (loTrigs[k]'hltT).sMid (loTrigs[k]'hltT).eUlps
           else mulAmpScalar bCert (loTrigs[k]'hltT).cMid (loTrigs[k]'hltT).eUlps).Valid
          (if useSin then vb * Real.sin (θLo k) else vb * Real.cos (θLo k)) := by
        cases useSin
        · exact mulAmpScalar_valid hb hvT.1
        · exact mulAmpScalar_valid hb hvT.2
      have hd := ampDiffBound_spec hvA hTgt
      set dN := ampDiffBound (ampsLo[offset + k]'hltA)
        (if useSin then mulAmpScalar bCert (loTrigs[k]'hltT).sMid (loTrigs[k]'hltT).eUlps
         else mulAmpScalar bCert (loTrigs[k]'hltT).cMid (loTrigs[k]'hltT).eUlps)
      set restN := sumLoErrSq offset bCert useSin ampsLo loTrigs k 0
      have hsq : (vLo (offset + k) -
          (if useSin then vb * Real.sin (θLo k) else vb * Real.cos (θLo k))) ^ 2 ≤
          ((dN : ℝ) / S) ^ 2 := by
        rw [← sq_abs (vLo (offset + k) - _)]
        exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      have hrhs : (((dN * dN + restN : ℕ) : ℝ)) / S ^ 2 =
          (restN : ℝ) / S ^ 2 + ((dN : ℝ) / S) ^ 2 := by
        push_cast; field_simp [hS_ne]; ring
      change _ ≤ (((dN * dN + restN : ℕ) : ℝ)) / S ^ 2
      linarith

/-- Active `16`-wire sub-register `(0 .. nDirtyLo - 1) ++ (mLow - 1 .. 15)` touched by `pWinHi`. -/
def rWinHiInQPE (mLow nDirtyLo : ℕ) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15)
    (hDirty : nDirtyLo ≤ mLow - 1) : QRegister (nDirtyLo + (16 - mLow + 1)) 16 :=
  (QRegister.block 0 nDirtyLo (by omega)).concat
    (QRegister.block (mLow - 1) (16 - mLow + 1) (by omega))
    (by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hv := congrArg Fin.val hij
      simp only [QRegister.block_apply_val, zero_add] at hv
      have := i.isLt; omega)

/-- Packaged Two-Gear (`pWinHi`, `pWinLo`) sine-window specification on `16` QPE wires. -/
structure TwoGearWindowSpec (M mLow nDirtyLo : ℕ) where
  /-- Exact divisibility `2 ^ mLow ∣ M + 1`. -/
  hdiv : 2 ^ mLow ∣ M + 1
  /-- Active high-gear schedule lower bound `2 ^ (16 - mLow - 1) ≤ (M + 1) / 2 ^ mLow - 1`. -/
  hDlo : 2 ^ (16 - mLow - 1) ≤ (M + 1) / 2 ^ mLow - 1
  /-- Positive walk cap `1 ≤ M`. -/
  hM1 : 1 ≤ M
  /-- `16`-bit QPE fit `M < 2 ^ 16`. -/
  hMlt : M < 2 ^ 16
  /-- Low-gear bit floor `2 ≤ mLow`. -/
  hmLow2 : 2 ≤ mLow
  /-- Low-gear bit ceiling `mLow ≤ 14`. -/
  hmLow14 : mLow ≤ 14
  /-- Dirty low-bit count bound `nDirtyLo ≤ mLow - 1`. -/
  hDirty : nDirtyLo ≤ mLow - 1
  /-- Total `T`-gate count `cWinHi.count .T + cWinLo.count .T`. -/
  tWin : ℕ
  /-- Certified `L²` synthesis accuracy against `windowVec 16 M (sineWindowCoeff (M + 1))`. -/
  δWin : ℝ
  /-- Nonnegativity of `δWin`. -/
  hδ_nonneg : 0 ≤ δWin
  /-- High-gear + bond-wire preparation circuit (leaves `nDirtyLo .. mLow - 2` in `|0⟩`). -/
  cWinHi : Circuit (nDirtyLo + (16 - mLow + 1))
  /-- Deferred low-gear expansion circuit on `0 .. mLow - 1`. -/
  cWinLo : Circuit mLow
  /-- Ideal `16`-qubit window unitary preparing `windowVec 16 M (sineWindowCoeff (M + 1))`. -/
  uIdeal : Unitary (2 ^ 16)
  /-- Zero `.TOFF` count on `cWinHi`. -/
  count_hi_toff : cWinHi.count .TOFF = 0
  /-- Zero `.TOFF` count on `cWinLo`. -/
  count_lo_toff : cWinLo.count .TOFF = 0
  /-- Exact total `T`-gate count `cWinHi.count .T + cWinLo.count .T = tWin`. -/
  count_t : cWinHi.count .T + cWinLo.count .T = tWin
  /-- Exact ideal action on `|0⟩`. -/
  ideal_mulVec_zero : uIdeal.1 *ᵥ basisState 0 = windowVec 16 M (sineWindowCoeff (M + 1))
  /-- Vector `L²` accuracy bound on `|0⟩`. -/
  vec_err_le :
    ‖WithLp.toLp 2
      ((((QRegister.block 0 mLow (by omega) : QRegister mLow 16).embedUnitary cWinLo.eval) *
        ((rWinHiInQPE mLow nDirtyLo (by omega) (by omega) hDirty).embedUnitary
          cWinHi.eval)).1 *ᵥ basisState 0 -
        uIdeal.1 *ᵥ basisState 0)‖ ≤ δWin

theorem block_extractIndex_val_tg {a m n : ℕ} (ha : a + m ≤ n) (g : Fin (2 ^ n)) :
    ((QRegister.block a m ha).extractIndex g).val = (g.val / 2 ^ a) % 2 ^ m := by
  suffices h : (QRegister.block a m ha).extractIndex g =
      ⟨(g.val / 2 ^ a) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩ from congrArg Fin.val h
  apply (basisBits m).injective; funext i
  rw [QRegister.basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
  have hw : (QRegister.block a m ha i).val = a + i.val := by simp
  rw [hw]; dsimp only
  rw [Nat.testBit_mod_two_pow]
  simp only [i.isLt, decide_true, Bool.true_and, ← Nat.shiftRight_eq_div_pow,
    Nat.testBit_shiftRight]

theorem hiBlock_basisSplit_snd_eq_zero_iff (mLow mHi : ℕ) (_hm1 : 1 ≤ mLow)
    (h16 : (mLow - 1) + (mHi + 1) = 16) (g : Fin (2 ^ 16)) :
    let rHi : QRegister (mHi + 1) 16 := QRegister.block (mLow - 1) (mHi + 1) (by omega)
    (rHi.basisSplitEquiv g).2 = (rHi.basisSplitEquiv 0).2 ↔ g.val % 2 ^ (mLow - 1) = 0 := by
  intro rHi
  constructor
  · intro heq
    let y := rHi.extractIndex g
    let g0 : Fin (2 ^ 16) := ⟨y.val * 2 ^ (mLow - 1), by
      have hy := y.isLt
      have hp : 2 ^ 16 = 2 ^ (mHi + 1) * 2 ^ (mLow - 1) := by
        rw [← pow_add, show (mHi + 1) + (mLow - 1) = 16 by omega]
      nlinarith⟩
    have hg0_ex : rHi.extractIndex g0 = y := by
      apply Fin.ext
      rw [block_extractIndex_val_tg, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
        Nat.mod_eq_of_lt y.isLt]
    have hg0_snd : (rHi.basisSplitEquiv g0).2 = (rHi.basisSplitEquiv 0).2 := by
      funext ⟨u, hu⟩
      change basisBits 16 g0 u = basisBits 16 0 u
      have hu_lt : u.val < mLow - 1 := by
        by_contra hge
        exact hu ⟨⟨u.val - (mLow - 1), by have := u.isLt; omega⟩,
          by ext; simp [rHi]; omega⟩
      rw [basisBits_eq_testBit, basisBits_eq_testBit]
      have h0 : (0 : ℕ).testBit u.val = false := Nat.zero_testBit u.val
      have hdvd : 2 ^ (u.val + 1) ∣ y.val * 2 ^ (mLow - 1) :=
        dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
      obtain ⟨q, hq⟩ := hdvd
      have hg0b : g0.val.testBit u.val = false := by
        dsimp [g0]
        rw [Nat.testBit_eq_decide_div_mod_eq, hq, pow_succ, mul_assoc,
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos u.val), Nat.mul_mod_right]
        decide
      simp [hg0b, h0]
    have hsplit : rHi.basisSplitEquiv g = rHi.basisSplitEquiv g0 :=
      Prod.ext hg0_ex.symm (heq.trans hg0_snd.symm)
    have hgg0 : g = g0 := rHi.basisSplitEquiv.injective hsplit
    rw [hgg0]; exact Nat.mul_mod_left _ _
  · intro hmod
    funext ⟨u, hu⟩
    change basisBits 16 g u = basisBits 16 0 u
    have hu_lt : u.val < mLow - 1 := by
      by_contra hge
      exact hu ⟨⟨u.val - (mLow - 1), by have := u.isLt; omega⟩,
        by ext; simp [rHi]; omega⟩
    rw [basisBits_eq_testBit, basisBits_eq_testBit]
    have hdiv : 2 ^ (mLow - 1) ∣ g.val := Nat.dvd_of_mod_eq_zero hmod
    have hdvd : 2 ^ (u.val + 1) ∣ g.val :=
      dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdiv
    obtain ⟨q, hq⟩ := hdvd
    have hgb : g.val.testBit u.val = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hq, pow_succ, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos u.val), Nat.mul_mod_right]
      decide
    simp [hgb, Nat.zero_testBit]

theorem loBlock_basisSplit_snd_eq_iff (mLow : ℕ) (hm16 : mLow ≤ 16)
    (g h : Fin (2 ^ 16)) :
    let rLo : QRegister mLow 16 := QRegister.block 0 mLow (by omega)
    (rLo.basisSplitEquiv g).2 = (rLo.basisSplitEquiv h).2 ↔
      g.val / 2 ^ mLow = h.val / 2 ^ mLow := by
  intro rLo
  constructor
  · intro heq
    let g' : Fin (2 ^ 16) := ⟨(h.val / 2 ^ mLow) * 2 ^ mLow + g.val % 2 ^ mLow, by
      have hdiv : h.val / 2 ^ mLow < 2 ^ (16 - mLow) := Nat.div_lt_of_lt_mul
        (h.isLt.trans_eq (by rw [← pow_add, show mLow + (16 - mLow) = 16 by omega]))
      calc (h.val / 2 ^ mLow) * 2 ^ mLow + g.val % 2 ^ mLow
          < (h.val / 2 ^ mLow) * 2 ^ mLow + 2 ^ mLow :=
            Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos mLow)) _
        _ = (h.val / 2 ^ mLow + 1) * 2 ^ mLow := by ring
        _ ≤ 2 ^ (16 - mLow) * 2 ^ mLow := Nat.mul_le_mul_right _ hdiv
        _ = 2 ^ 16 := by rw [← pow_add, show (16 - mLow) + mLow = 16 by omega]⟩
    have hg'_ex : rLo.extractIndex g' = rLo.extractIndex g := by
      apply Fin.ext
      rw [block_extractIndex_val_tg, block_extractIndex_val_tg]
      simp only [_root_.pow_zero, Nat.div_one]
      dsimp [g']
      rw [Nat.mul_add_mod_self_right, Nat.mod_mod]
    have hg'_snd : (rLo.basisSplitEquiv g').2 = (rLo.basisSplitEquiv h).2 := by
      funext ⟨u, hu⟩
      change basisBits 16 g' u = basisBits 16 h u
      have hu_ge : mLow ≤ u.val := by
        by_contra hlt; exact hu ⟨⟨u.val, Nat.lt_of_not_ge hlt⟩, by ext; simp [rLo]⟩
      rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
      have hpow : 2 ^ u.val = 2 ^ mLow * 2 ^ (u.val - mLow) := by
        rw [← pow_add, show mLow + (u.val - mLow) = u.val by omega]
      have hd1 : g'.val / 2 ^ u.val = (h.val / 2 ^ mLow) / 2 ^ (u.val - mLow) := by
        rw [hpow, ← Nat.div_div_eq_div_mul]
        congr 1
        dsimp [g']
        rw [mul_comm _ (2 ^ mLow), Nat.mul_add_div (Nat.two_pow_pos mLow),
          Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos mLow)), add_zero]
      have hd2 : h.val / 2 ^ u.val = (h.val / 2 ^ mLow) / 2 ^ (u.val - mLow) := by
        rw [hpow, ← Nat.div_div_eq_div_mul]
      rw [hd1, hd2]
    have hsplit : rLo.basisSplitEquiv g = rLo.basisSplitEquiv g' :=
      Prod.ext hg'_ex.symm (heq.trans hg'_snd.symm)
    have hgg' : g = g' := rLo.basisSplitEquiv.injective hsplit
    rw [hgg']
    dsimp [g']
    rw [mul_comm _ (2 ^ mLow), Nat.mul_add_div (Nat.two_pow_pos mLow),
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos mLow)), add_zero]
  · intro hdiv
    funext ⟨u, hu⟩
    change basisBits 16 g u = basisBits 16 h u
    have hu_ge : mLow ≤ u.val := by
      by_contra hlt; exact hu ⟨⟨u.val, Nat.lt_of_not_ge hlt⟩, by ext; simp [rLo]⟩
    rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
    have hpow : 2 ^ u.val = 2 ^ mLow * 2 ^ (u.val - mLow) := by
      rw [← pow_add, show mLow + (u.val - mLow) = u.val by omega]
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]

theorem sum_16_split_hi_lo (mLow mHi : ℕ) (h16 : mLow + mHi = 16)
    (f : Fin (2 ^ 16) → ℝ) :
    (∑ g : Fin (2 ^ 16), f g) =
      ∑ xh : Fin (2 ^ mHi), ∑ xl : Fin (2 ^ mLow),
        f ⟨xh.val * 2 ^ mLow + xl.val, by
          have hxh := xh.isLt; have hxl := xl.isLt
          have hp : 2 ^ 16 = 2 ^ mHi * 2 ^ mLow := by
            rw [← pow_add, show mHi + mLow = 16 by omega]
          nlinarith⟩ := by
  let e : Fin (2 ^ mHi) × Fin (2 ^ mLow) ≃ Fin (2 ^ 16) :=
    { toFun := fun p ↦ ⟨p.1.val * 2 ^ mLow + p.2.val, by
        have hxh := p.1.isLt; have hxl := p.2.isLt
        have hp : 2 ^ 16 = 2 ^ mHi * 2 ^ mLow := by
          rw [← pow_add, show mHi + mLow = 16 by omega]
        nlinarith⟩
      invFun := fun g ↦
        (⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
            rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)⟩,
         ⟨g.val % 2 ^ mLow, Nat.mod_lt _ (Nat.two_pow_pos mLow)⟩)
      left_inv := fun ⟨xh, xl⟩ ↦ by
        ext
        · dsimp
          rw [mul_comm xh.val, Nat.mul_add_div (Nat.two_pow_pos mLow),
            Nat.div_eq_of_lt xl.isLt, add_zero]
        · dsimp
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt xl.isLt]
      right_inv := fun g ↦ by
        ext; dsimp; rw [mul_comm _ (2 ^ mLow)]; exact Nat.div_add_mod g.val (2 ^ mLow) }
  rw [← Equiv.sum_comp e f, Fintype.sum_prod_type]
  rfl

theorem norm_toLp_ofReal_le {d : ℕ} (v : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hsq : ∑ i : Fin d, v i ^ 2 ≤ B ^ 2) :
    ‖WithLp.toLp 2 (fun i : Fin d ↦ (v i : ℂ))‖ ≤ B := by
  have hn : ‖WithLp.toLp 2 (fun i : Fin d ↦ (v i : ℂ))‖ ^ 2 ≤ B ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Complex.norm_real, sq_abs] using hsq
  exact (sq_le_sq₀ (norm_nonneg _) hB).mp hn

theorem scale_ab_bound {aNat bNat L : ℕ} (hL : 1 ≤ L)
    (hge : 2 * OuterWeights.SineWindowPrep.scale24 ≤ aNat * bNat)
    (hlo : (aNat * bNat - 2 * OuterWeights.SineWindowPrep.scale24) ^ 2 * L ≤
      (2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24) ^ 2)
    (hhi : (2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24) ^ 2 ≤
      (aNat * bNat + 2 * OuterWeights.SineWindowPrep.scale24) ^ 2 * L) :
    let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
    |((aNat : ℝ) / S) * ((bNat : ℝ) / S) - 2 / √(L : ℝ)| ≤ 2 / S := by
  intro S
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hsqL_pos : 0 < √(L : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hsqL_ne : √(L : ℝ) ≠ 0 := ne_of_gt hsqL_pos
  have hsqL_sq : √(L : ℝ) ^ 2 = (L : ℝ) := Real.sq_sqrt hL_pos.le
  have hloR : (((aNat * bNat - 2 * OuterWeights.SineWindowPrep.scale24 : ℕ) : ℝ) * √(L : ℝ)) ^ 2 ≤
      (2 * S * S) ^ 2 := by
    rw [mul_pow, hsqL_sq]
    dsimp only [S]
    exact_mod_cast hlo
  have hhiR : (2 * S * S) ^ 2 ≤
      (((aNat * bNat + 2 * OuterWeights.SineWindowPrep.scale24 : ℕ) : ℝ) * √(L : ℝ)) ^ 2 := by
    conv_rhs => rw [mul_pow, hsqL_sq]
    dsimp only [S]
    exact_mod_cast hhi
  have h2SS_nn : 0 ≤ 2 * S * S :=
    mul_nonneg (mul_nonneg zero_le_two hS_pos.le) hS_pos.le
  have hlo1 : ((aNat * bNat - 2 * scale24 : ℕ) : ℝ) * √(L : ℝ) ≤ 2 * S * S :=
    (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) hsqL_pos.le) h2SS_nn).mp hloR
  have hhi1 : 2 * S * S ≤ ((aNat * bNat + 2 * scale24 : ℕ) : ℝ) * √(L : ℝ) :=
    (sq_le_sq₀ h2SS_nn (mul_nonneg (Nat.cast_nonneg _) hsqL_pos.le)).mp hhiR
  have hsub_cast : ((aNat * bNat - 2 * OuterWeights.SineWindowPrep.scale24 : ℕ) : ℝ) =
      (aNat : ℝ) * (bNat : ℝ) - 2 * S := by
    rw [Nat.cast_sub hge]; dsimp [S]; push_cast; ring
  have hadd_cast : ((aNat * bNat + 2 * OuterWeights.SineWindowPrep.scale24 : ℕ) : ℝ) =
      (aNat : ℝ) * (bNat : ℝ) + 2 * S := by
    dsimp [S]; push_cast; ring
  rw [hsub_cast] at hlo1
  rw [hadd_cast] at hhi1
  rw [abs_le]
  have hdenom : 0 < S * S * √(L : ℝ) := mul_pos (mul_pos hS_pos hS_pos) hsqL_pos
  constructor
  · have h1 : -2 * S * √(L : ℝ) ≤ ((aNat : ℝ) * (bNat : ℝ)) * √(L : ℝ) - 2 * S * S := by
      linarith only [hhi1]
    have h2 := div_le_div_of_nonneg_right h1 hdenom.le
    have hl : (-2 * S * √(L : ℝ)) / (S * S * √(L : ℝ)) = -(2 / S) := by
      field_simp [hS_ne, hsqL_ne]
    have hr : (((aNat : ℝ) * (bNat : ℝ)) * √(L : ℝ) - 2 * S * S) / (S * S * √(L : ℝ)) =
        ((aNat : ℝ) / S) * ((bNat : ℝ) / S) - 2 / √(L : ℝ) := by
      field_simp [hS_ne, hsqL_ne]
    linarith only [h2, hl, hr]
  · have h1 : ((aNat : ℝ) * (bNat : ℝ)) * √(L : ℝ) - 2 * S * S ≤ 2 * S * √(L : ℝ) := by
      linarith only [hlo1]
    have h2 := div_le_div_of_nonneg_right h1 hdenom.le
    have hr : (2 * S * √(L : ℝ)) / (S * S * √(L : ℝ)) = 2 / S := by
      field_simp [hS_ne, hsqL_ne]
    have hl : (((aNat : ℝ) * (bNat : ℝ)) * √(L : ℝ) - 2 * S * S) / (S * S * √(L : ℝ)) =
        ((aNat : ℝ) / S) * ((bNat : ℝ) / S) - 2 / √(L : ℝ) := by
      field_simp [hS_ne, hsqL_ne]
    linarith only [h2, hl, hr]

theorem checkTwoGearRegime_meta (d : TwoGearRegimeData) (hok : checkTwoGearRegime d = true) :
    2 ^ d.mLow ∣ d.M + 1 ∧ 1 ≤ d.M ∧ d.M < 2 ^ 16 ∧ 2 ≤ d.mLow ∧ d.mLow ≤ 14 := by
  rcases d with ⟨M, mLow, D, mHi, c0Mid, s0Mid, a0Nat, a1Nat, b0Nat, b1Nat,
    eHiNum, eLo0Num, eLo1Num, tWin, hiTrees, loTrees⟩
  dsimp only [checkTwoGearRegime] at hok ⊢
  simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq,
    OuterWeights.SineWindowPrep.withForcedNat_eq,
    withForcedList_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
  rcases hok with ⟨hm2, hm14, hmHi_eq, hD1, hD_le, hL_eq, _⟩
  subst hmHi_eq
  have hdiv : 2 ^ mLow ∣ M + 1 := ⟨D, by rw [hL_eq, mul_comm]⟩
  have hL_le_16 : M + 1 ≤ 2 ^ 16 := by
    calc M + 1 = D * 2 ^ mLow := hL_eq
      _ ≤ 2 ^ (16 - mLow) * 2 ^ mLow := Nat.mul_le_mul_right _ hD_le
      _ = 2 ^ 16 := by rw [← pow_add, show (16 - mLow) + mLow = 16 by omega]
  have hp : 4 ≤ 2 ^ mLow :=
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ mLow := Nat.pow_le_pow_right (by decide) hm2
  have hL4 : 4 ≤ M + 1 := by
    rw [hL_eq]; exact le_trans hp (Nat.le_mul_of_pos_left _ hD1)
  exact ⟨hdiv, by omega, by omega, hm2, hm14⟩

/-- High-gear + bond-wire circuit constructed from `d.hiTrees`. -/
def twoGearZeroAncHi (d : TwoGearRegimeData) : Circuit (0 + (16 - d.mLow + 1)) :=
  (mottonenCascade (16 - d.mLow + 1) (16 - d.mLow + 1) le_rfl d.hiTrees).onRegister
    (QRegister.block 0 (16 - d.mLow + 1) le_rfl)

/-- Deferred low-gear circuit constructed from `d.loTrees` and `loCliffordTail`. -/
def twoGearZeroAncLo (d : TwoGearRegimeData) (hm1 : 1 ≤ d.mLow) : Circuit d.mLow :=
  (mottonenCascade d.mLow (d.mLow - 1) (Nat.sub_le _ _) d.loTrees).seq
    (loCliffordTail d.mLow hm1)

theorem twoGear_lo_err_sq
    (M mLow c0Mid s0Mid b0Nat b1Nat eLo0Num eLo1Num : ℕ)
    (hm2 : 2 ≤ mLow)
    (loAmps : List AmpCert) (hlenAmpsLo : loAmps.length = 2 ^ mLow)
    (vLo : Fin (2 ^ mLow) → ℝ)
    (hvalLo : ∀ x : Fin (2 ^ mLow),
      (loAmps[x.val]'(x.isLt.trans_eq hlenAmpsLo.symm)).Valid (vLo x))
    (hlenGLo : (buildOddTrigGrid (2 ^ (mLow - 1))
      ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.length = 2 ^ (mLow - 1))
    (hvalGLo : ∀ (i : ℕ)
      (hi : i < (buildOddTrigGrid (2 ^ (mLow - 1))
        ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.length),
      ((buildOddTrigGrid (2 ^ (mLow - 1)) ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1[i]'hi).Valid
        ((2 * (i : ℝ) + 1) * (π / (2 * ((M + 1 : ℕ) : ℝ)))))
    (herrLo0 : sumLoErrSq 0 ⟨.ofNat b0Nat, 0⟩ false loAmps
      (buildOddTrigGrid (2 ^ (mLow - 1)) ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.reverse
      (2 ^ (mLow - 1)) 0 ≤ eLo0Num * eLo0Num)
    (herrLo1 : sumLoErrSq (2 ^ (mLow - 1)) ⟨.ofNat b1Nat, 0⟩ true loAmps
      (buildOddTrigGrid (2 ^ (mLow - 1)) ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.reverse
      (2 ^ (mLow - 1)) 0 ≤ eLo1Num * eLo1Num) :
    let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
    let halfLo := 2 ^ (mLow - 1)
    let hp_lo : 2 ^ mLow = 2 * halfLo := by
      have hm1 : mLow = (mLow - 1) + 1 := by omega
      conv_lhs => rw [hm1, pow_succ']
    let vb0 : ℝ := (b0Nat : ℝ) / S
    let vb1 : ℝ := (b1Nat : ℝ) / S
    let θLoRev : ℕ → ℝ := fun z ↦
      ((2 * (halfLo - 1 - z) + 1 : ℕ) : ℝ) * (π / (2 * ((M + 1 : ℕ) : ℝ)))
    let wLo0 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if _hlt : xl.val < halfLo then √(1 / 2 : ℝ) * vLo xl
      else √(1 / 2 : ℝ) * vLo ⟨2 ^ mLow - 1 - xl.val, by have := xl.isLt; omega⟩
    let wLo1 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if _hlt : xl.val < halfLo then -√(1 / 2 : ℝ) * vLo ⟨halfLo + xl.val, by omega⟩
      else √(1 / 2 : ℝ) * vLo ⟨halfLo + (2 ^ mLow - 1 - xl.val), by have := xl.isLt; omega⟩
    let tLo0 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if xl.val < halfLo then √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev xl.val))
      else √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev (2 ^ mLow - 1 - xl.val)))
    let tLo1 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if xl.val < halfLo then -√(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev xl.val))
      else √(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev (2 ^ mLow - 1 - xl.val)))
    (∑ xl : Fin (2 ^ mLow), (wLo0 xl - tLo0 xl) ^ 2 ≤ ((eLo0Num : ℝ) / S) ^ 2) ∧
      (∑ xl : Fin (2 ^ mLow), (wLo1 xl - tLo1 xl) ^ 2 ≤ ((eLo1Num : ℝ) / S) ^ 2) := by
  intro S halfLo hp_lo vb0 vb1 θLoRev wLo0 wLo1 tLo0 tLo1
  have hhalf_pos : 0 < halfLo := Nat.two_pow_pos _
  have hb0_val : (⟨.ofNat b0Nat, 0⟩ : AmpCert).Valid vb0 := by
    simp [AmpCert.Valid, OuterWeights.SineWindowPrep.SInt.toReal_ofNat, vb0, S]
  have hb1_val : (⟨.ofNat b1Nat, 0⟩ : AmpCert).Valid vb1 := by
    simp [AmpCert.Valid, OuterWeights.SineWindowPrep.SInt.toReal_ofNat, vb1, S]
  let loTrigs := (buildOddTrigGrid halfLo ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.reverse
  have hlenLoTrigs : loTrigs.length = halfLo := by
    dsimp [loTrigs]; rw [List.length_reverse, hlenGLo]
  have hvalLoTrigs : ∀ z (hz : z < halfLo),
      (loTrigs[z]'(by omega)).Valid (θLoRev z) := by
    intro z hz
    dsimp only [loTrigs]
    rw [List.getElem_reverse]
    have hidx : (buildOddTrigGrid halfLo ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.length - 1 - z =
        halfLo - 1 - z := by rw [hlenGLo]
    have hv := hvalGLo (halfLo - 1 - z) (by omega)
    simpa [hidx, θLoRev] using hv
  let vLoNat : ℕ → ℝ := fun i ↦ if hi : i < 2 ^ mLow then vLo ⟨i, hi⟩ else 0
  have hwLo0_err_sq :
      ∑ xl : Fin (2 ^ mLow), (wLo0 xl - tLo0 xl) ^ 2 ≤ ((eLo0Num : ℝ) / S) ^ 2 := by
    have hsplit_lo :
        (∑ xl : Fin (2 ^ mLow), (wLo0 xl - tLo0 xl) ^ 2) =
          ∑ z ∈ Finset.range halfLo, (vLoNat z - vb0 * Real.cos (θLoRev z)) ^ 2 := by
      let f0 : ℕ → ℝ := fun z ↦
        if hz : z < 2 ^ mLow then (wLo0 ⟨z, hz⟩ - tLo0 ⟨z, hz⟩) ^ 2 else 0
      have hf0 : (∑ xl : Fin (2 ^ mLow), (wLo0 xl - tLo0 xl) ^ 2) =
          ∑ xl : Fin (2 ^ mLow), f0 xl.val :=
        Finset.sum_congr rfl fun xl _ ↦ by dsimp only [f0]; simp only [xl.isLt, ↓reduceDIte]
      rw [hf0, Fin.sum_univ_eq_sum_range, show 2 ^ mLow = halfLo + halfLo by omega,
        Finset.sum_range_add]
      have hsq_half : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
      have hl : (∑ z ∈ Finset.range halfLo, f0 z) =
          (1 / 2 : ℝ) * ∑ z ∈ Finset.range halfLo, (vLoNat z - vb0 * Real.cos (θLoRev z)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z hz ↦ ?_
        have hlt : z < halfLo := Finset.mem_range.mp hz
        have hlt2 : z < 2 ^ mLow := by omega
        dsimp only [f0, wLo0, tLo0, vLoNat]
        simp only [hlt2, hlt, ↓reduceDIte, ↓reduceIte]
        calc (√(1 / 2 : ℝ) * vLo ⟨z, hlt2⟩ - √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev z))) ^ 2
            = √(1 / 2 : ℝ) ^ 2 * (vLo ⟨z, hlt2⟩ - vb0 * Real.cos (θLoRev z)) ^ 2 := by ring
          _ = (1 / 2 : ℝ) * (vLo ⟨z, hlt2⟩ - vb0 * Real.cos (θLoRev z)) ^ 2 := by rw [hsq_half]
      have hr : (∑ z ∈ Finset.range halfLo, f0 (halfLo + z)) =
          (1 / 2 : ℝ) * ∑ z ∈ Finset.range halfLo, (vLoNat z - vb0 * Real.cos (θLoRev z)) ^ 2 := by
        have hr1 : (∑ z ∈ Finset.range halfLo, f0 (halfLo + z)) =
            ∑ z ∈ Finset.range halfLo,
              (1 / 2 : ℝ) * (vLoNat (halfLo - 1 - z) -
                vb0 * Real.cos (θLoRev (halfLo - 1 - z))) ^ 2 := by
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          have hlt : z < halfLo := Finset.mem_range.mp hz
          have hadd_lt : halfLo + z < 2 ^ mLow := by omega
          have hge : ¬ halfLo + z < halfLo := by omega
          have hsub : 2 ^ mLow - 1 - (halfLo + z) = halfLo - 1 - z := by omega
          have hlt2 : halfLo - 1 - z < 2 ^ mLow := by omega
          dsimp only [f0, wLo0, tLo0, vLoNat]
          simp only [hadd_lt, hge, ↓reduceDIte, ↓reduceIte, hsub, hlt2]
          calc (√(1 / 2 : ℝ) * vLo ⟨halfLo - 1 - z, hlt2⟩ -
                √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev (halfLo - 1 - z)))) ^ 2
              = √(1 / 2 : ℝ) ^ 2 *
                  (vLo ⟨halfLo - 1 - z, hlt2⟩ - vb0 * Real.cos (θLoRev (halfLo - 1 - z))) ^ 2 := by
                ring
            _ = (1 / 2 : ℝ) *
                  (vLo ⟨halfLo - 1 - z, hlt2⟩ - vb0 * Real.cos (θLoRev (halfLo - 1 - z))) ^ 2 := by
                rw [hsq_half]
        rw [hr1, ← Finset.mul_sum,
          Finset.sum_range_reflect (fun x ↦ (vLoNat x - vb0 * Real.cos (θLoRev x)) ^ 2) halfLo]
      rw [hl, hr]; ring
    rw [hsplit_lo]
    have hspec := sumLoErrSq_spec 0 ⟨.ofNat b0Nat, 0⟩ false loAmps
      loTrigs vLoNat θLoRev vb0 hb0_val halfLo
      (by rw [hlenAmpsLo]; omega) (by omega)
      (fun z hz ↦ by
        have hz2 : z < 2 ^ mLow := by omega
        dsimp [vLoNat]; simp only [zero_add, hz2, ↓reduceDIte]
        simpa using hvalLo ⟨z, hz2⟩)
      hvalLoTrigs
    simp only [zero_add, Bool.false_eq_true, ↓reduceIte] at hspec
    refine hspec.trans ?_
    rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg S)
    exact_mod_cast herrLo0.trans_eq (sq eLo0Num).symm
  have hwLo1_err_sq :
      ∑ xl : Fin (2 ^ mLow), (wLo1 xl - tLo1 xl) ^ 2 ≤ ((eLo1Num : ℝ) / S) ^ 2 := by
    have hsplit_lo :
        (∑ xl : Fin (2 ^ mLow), (wLo1 xl - tLo1 xl) ^ 2) =
          ∑ z ∈ Finset.range halfLo, (vLoNat (halfLo + z) - vb1 * Real.sin (θLoRev z)) ^ 2 := by
      let f1 : ℕ → ℝ := fun z ↦
        if hz : z < 2 ^ mLow then (wLo1 ⟨z, hz⟩ - tLo1 ⟨z, hz⟩) ^ 2 else 0
      have hf1 : (∑ xl : Fin (2 ^ mLow), (wLo1 xl - tLo1 xl) ^ 2) =
          ∑ xl : Fin (2 ^ mLow), f1 xl.val :=
        Finset.sum_congr rfl fun xl _ ↦ by dsimp only [f1]; simp only [xl.isLt, ↓reduceDIte]
      rw [hf1, Fin.sum_univ_eq_sum_range, show 2 ^ mLow = halfLo + halfLo by omega,
        Finset.sum_range_add]
      have hsq_half : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
      have hl : (∑ z ∈ Finset.range halfLo, f1 z) =
          (1 / 2 : ℝ) * ∑ z ∈ Finset.range halfLo,
            (vLoNat (halfLo + z) - vb1 * Real.sin (θLoRev z)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z hz ↦ ?_
        have hlt : z < halfLo := Finset.mem_range.mp hz
        have hlt2 : z < 2 ^ mLow := by omega
        have hlt3 : halfLo + z < 2 ^ mLow := by omega
        dsimp only [f1, wLo1, tLo1, vLoNat]
        simp only [hlt2, hlt, hlt3, ↓reduceDIte, ↓reduceIte]
        calc (-√(1 / 2 : ℝ) * vLo ⟨halfLo + z, hlt3⟩ -
              -√(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev z))) ^ 2
            = √(1 / 2 : ℝ) ^ 2 *
                (vLo ⟨halfLo + z, hlt3⟩ - vb1 * Real.sin (θLoRev z)) ^ 2 := by ring
          _ = (1 / 2 : ℝ) *
                (vLo ⟨halfLo + z, hlt3⟩ - vb1 * Real.sin (θLoRev z)) ^ 2 := by rw [hsq_half]
      have hr : (∑ z ∈ Finset.range halfLo, f1 (halfLo + z)) =
          (1 / 2 : ℝ) * ∑ z ∈ Finset.range halfLo,
            (vLoNat (halfLo + z) - vb1 * Real.sin (θLoRev z)) ^ 2 := by
        have hr1 : (∑ z ∈ Finset.range halfLo, f1 (halfLo + z)) =
            ∑ z ∈ Finset.range halfLo,
              (1 / 2 : ℝ) * (vLoNat (halfLo + (halfLo - 1 - z)) -
                vb1 * Real.sin (θLoRev (halfLo - 1 - z))) ^ 2 := by
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          have hlt : z < halfLo := Finset.mem_range.mp hz
          have hadd_lt : halfLo + z < 2 ^ mLow := by omega
          have hge : ¬ halfLo + z < halfLo := by omega
          have hsub : 2 ^ mLow - 1 - (halfLo + z) = halfLo - 1 - z := by omega
          have hlt2 : halfLo + (halfLo - 1 - z) < 2 ^ mLow := by omega
          dsimp only [f1, wLo1, tLo1, vLoNat]
          simp only [hadd_lt, hge, ↓reduceDIte, ↓reduceIte, hsub, hlt2]
          calc (√(1 / 2 : ℝ) * vLo ⟨halfLo + (halfLo - 1 - z), hlt2⟩ -
                √(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev (halfLo - 1 - z)))) ^ 2
              = √(1 / 2 : ℝ) ^ 2 *
                  (vLo ⟨halfLo + (halfLo - 1 - z), hlt2⟩ -
                    vb1 * Real.sin (θLoRev (halfLo - 1 - z))) ^ 2 := by ring
            _ = (1 / 2 : ℝ) *
                  (vLo ⟨halfLo + (halfLo - 1 - z), hlt2⟩ -
                    vb1 * Real.sin (θLoRev (halfLo - 1 - z))) ^ 2 := by rw [hsq_half]
        rw [hr1, ← Finset.mul_sum,
          Finset.sum_range_reflect (fun x ↦ (vLoNat (halfLo + x) - vb1 * Real.sin (θLoRev x)) ^ 2)
            halfLo]
      rw [hl, hr]; ring
    rw [hsplit_lo]
    have hspec := sumLoErrSq_spec halfLo ⟨.ofNat b1Nat, 0⟩ true loAmps
      loTrigs vLoNat θLoRev vb1 hb1_val halfLo
      (by rw [hlenAmpsLo]; omega) (by omega)
      (fun z hz ↦ by
        have hz2 : halfLo + z < 2 ^ mLow := by omega
        dsimp [vLoNat]; simp only [hz2, ↓reduceDIte]
        simpa using hvalLo ⟨halfLo + z, hz2⟩)
      hvalLoTrigs
    simp only [↓reduceIte] at hspec
    refine hspec.trans ?_
    rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg S)
    exact_mod_cast herrLo1.trans_eq (sq eLo1Num).symm
  exact ⟨hwLo0_err_sq, hwLo1_err_sq⟩

theorem twoGear_piece3_l2_bound
    (mLow D a0Nat a1Nat eLo0Num eLo1Num : ℕ)
    (hm14 : mLow ≤ 14) (hD_le : D ≤ 2 ^ (16 - mLow))
    (hDa0 : D * (a0Nat * a0Nat) ≤ 2 * (scale24 * scale24))
    (hDa1 : D * (a1Nat * a1Nat) ≤ 2 * (scale24 * scale24))
    (wLo0 wLo1 tLo0 tLo1 : Fin (2 ^ mLow) → ℝ)
    (hwLo0_err_sq :
      ∑ xl : Fin (2 ^ mLow), (wLo0 xl - tLo0 xl) ^ 2 ≤
        ((eLo0Num : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ)) ^ 2)
    (hwLo1_err_sq :
      ∑ xl : Fin (2 ^ mLow), (wLo1 xl - tLo1 xl) ^ 2 ≤
        ((eLo1Num : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ)) ^ 2) :
    let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
    let mHi := 16 - mLow
    let rLo16 : QRegister mLow 16 := QRegister.block 0 mLow (by omega)
    let va0 : ℝ := (a0Nat : ℝ) / S
    let va1 : ℝ := (a1Nat : ℝ) / S
    let θHi : ℕ → ℝ := fun j ↦ ((2 * j + 1 : ℕ) : ℝ) * (π / (2 * (D : ℝ)))
    let tHi0 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va0 * Real.sin (θHi xh.val) else 0
    let tHi1 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va1 * Real.cos (θHi xh.val) else 0
    let v3R : Fin (2 ^ 16) → ℝ := fun g ↦
      let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
        rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)⟩
      tHi0 xh * wLo0 (rLo16.extractIndex g) + tHi1 xh * wLo1 (rLo16.extractIndex g)
    let v4R : Fin (2 ^ 16) → ℝ := fun g ↦
      let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
        rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)⟩
      tHi0 xh * tLo0 (rLo16.extractIndex g) + tHi1 xh * tLo1 (rLo16.extractIndex g)
    ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v3R g - v4R g : ℝ) : ℂ))‖ ≤
      (2 * ((eLo0Num + eLo1Num : ℕ) : ℝ)) / S := by
  intro S mHi rLo16 va0 va1 θHi tHi0 tHi1 v3R v4R
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have h16 : mLow + mHi = 16 := by omega
  have h16_rev : mHi + mLow = 16 := by omega
  have hidx16 (xh : Fin (2 ^ mHi)) (xl : Fin (2 ^ mLow)) :
      xh.val * 2 ^ mLow + xl.val < 2 ^ 16 :=
    calc xh.val * 2 ^ mLow + xl.val
        < xh.val * 2 ^ mLow + 2 ^ mLow := Nat.add_lt_add_left xl.isLt _
      _ = (xh.val + 1) * 2 ^ mLow := by ring
      _ ≤ 2 ^ mHi * 2 ^ mLow := Nat.mul_le_mul_right _ xh.isLt
      _ = 2 ^ 16 := by rw [← pow_add, h16_rev]
  have htHi0_sq : ∑ xh : Fin (2 ^ mHi), tHi0 xh ^ 2 ≤ 2 := by
    have hpt : ∀ xh : Fin (2 ^ mHi), tHi0 xh ^ 2 ≤ if xh.val < D then va0 ^ 2 else 0 := by
      intro xh; dsimp [tHi0]
      split_ifs with hlt
      · have hs : Real.sin (θHi xh.val) ^ 2 ≤ 1 := Real.sin_sq_le_one _
        rw [mul_pow]; exact mul_le_of_le_one_right (sq_nonneg va0) hs
      · norm_num
    have hsum_le : (∑ xh : Fin (2 ^ mHi), tHi0 xh ^ 2) ≤
        ∑ j ∈ Finset.range (2 ^ mHi), (if j < D then va0 ^ 2 else 0) :=
      (Finset.sum_le_sum fun xh _ ↦ hpt xh).trans_eq
        (Fin.sum_univ_eq_sum_range (fun j ↦ if j < D then va0 ^ 2 else 0) (2 ^ mHi))
    have hfilt : (∑ j ∈ Finset.range (2 ^ mHi), (if j < D then va0 ^ 2 else 0)) =
        (D : ℝ) * va0 ^ 2 := by
      rw [← Finset.sum_filter, show (Finset.range (2 ^ mHi)).filter (· < D) = Finset.range D by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; dsimp only [mHi]; omega]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hDa0R : (D : ℝ) * (a0Nat : ℝ) ^ 2 ≤ 2 * S ^ 2 := by
      dsimp [S]
      exact_mod_cast (by simpa [sq] using hDa0 : D * a0Nat ^ 2 ≤ 2 * scale24 ^ 2)
    have hva0 : (D : ℝ) * va0 ^ 2 ≤ 2 := by
      dsimp [va0]; rw [div_pow, ← mul_div_assoc]
      exact (div_le_iff₀ (pow_pos hS_pos 2)).mpr hDa0R
    linarith
  have htHi1_sq : ∑ xh : Fin (2 ^ mHi), tHi1 xh ^ 2 ≤ 2 := by
    have hpt : ∀ xh : Fin (2 ^ mHi), tHi1 xh ^ 2 ≤ if xh.val < D then va1 ^ 2 else 0 := by
      intro xh; dsimp [tHi1]
      split_ifs with hlt
      · have hc : Real.cos (θHi xh.val) ^ 2 ≤ 1 := Real.cos_sq_le_one _
        rw [mul_pow]; exact mul_le_of_le_one_right (sq_nonneg va1) hc
      · norm_num
    have hsum_le : (∑ xh : Fin (2 ^ mHi), tHi1 xh ^ 2) ≤
        ∑ j ∈ Finset.range (2 ^ mHi), (if j < D then va1 ^ 2 else 0) :=
      (Finset.sum_le_sum fun xh _ ↦ hpt xh).trans_eq
        (Fin.sum_univ_eq_sum_range (fun j ↦ if j < D then va1 ^ 2 else 0) (2 ^ mHi))
    have hfilt : (∑ j ∈ Finset.range (2 ^ mHi), (if j < D then va1 ^ 2 else 0)) =
        (D : ℝ) * va1 ^ 2 := by
      rw [← Finset.sum_filter, show (Finset.range (2 ^ mHi)).filter (· < D) = Finset.range D by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; dsimp only [mHi]; omega]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hDa1R : (D : ℝ) * (a1Nat : ℝ) ^ 2 ≤ 2 * S ^ 2 := by
      dsimp [S]
      exact_mod_cast (by simpa [sq] using hDa1 : D * a1Nat ^ 2 ≤ 2 * scale24 ^ 2)
    have hva1 : (D : ℝ) * va1 ^ 2 ≤ 2 := by
      dsimp [va1]; rw [div_pow, ← mul_div_assoc]
      exact (div_le_iff₀ (pow_pos hS_pos 2)).mpr hDa1R
    linarith
  let v3a : Fin (2 ^ 16) → ℝ := fun g ↦
    let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
      rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)⟩
    tHi0 xh * (wLo0 (rLo16.extractIndex g) - tLo0 (rLo16.extractIndex g))
  let v3b : Fin (2 ^ 16) → ℝ := fun g ↦
    let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
      rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)⟩
    tHi1 xh * (wLo1 (rLo16.extractIndex g) - tLo1 (rLo16.extractIndex g))
  have hsplit : WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v3R g - v4R g : ℝ) : ℂ)) =
      WithLp.toLp 2 (fun g ↦ (v3a g : ℂ)) + WithLp.toLp 2 (fun g ↦ (v3b g : ℂ)) := by
    ext g; dsimp [v3R, v4R, v3a, v3b]; push_cast; ring
  have ha_le : ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ (v3a g : ℂ))‖ ≤
      2 * (eLo0Num : ℝ) / S := by
    refine norm_toLp_ofReal_le v3a
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hS_pos.le) ?_
    rw [sum_16_split_hi_lo mLow mHi h16]
    have hfac : (∑ xh : Fin (2 ^ mHi), ∑ xl : Fin (2 ^ mLow),
        v3a ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ ^ 2) =
        (∑ xh : Fin (2 ^ mHi), tHi0 xh ^ 2) *
          (∑ xl : Fin (2 ^ mLow), (wLo0 xl - tLo0 xl) ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun xh _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun xl _ ↦ ?_
      have hdiv : (xh.val * 2 ^ mLow + xl.val) / 2 ^ mLow = xh.val := by
        rw [mul_comm xh.val, Nat.mul_add_div (Nat.two_pow_pos mLow),
          Nat.div_eq_of_lt xl.isLt, add_zero]
      have hex : rLo16.extractIndex ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ = xl := by
        apply Fin.ext
        rw [block_extractIndex_val_tg, _root_.pow_zero, Nat.div_one]
        dsimp
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt xl.isLt]
      dsimp only [v3a]; simp only [hdiv, hex]; ring
    rw [hfac]
    have hp := mul_le_mul htHi0_sq hwLo0_err_sq
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by norm_num)
    exact hp.trans (by
      rw [show (2 * (eLo0Num : ℝ) / S) ^ 2 = 4 * ((eLo0Num : ℝ) / S) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _))
  have hb_le : ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ (v3b g : ℂ))‖ ≤
      2 * (eLo1Num : ℝ) / S := by
    refine norm_toLp_ofReal_le v3b
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hS_pos.le) ?_
    rw [sum_16_split_hi_lo mLow mHi h16]
    have hfac : (∑ xh : Fin (2 ^ mHi), ∑ xl : Fin (2 ^ mLow),
        v3b ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ ^ 2) =
        (∑ xh : Fin (2 ^ mHi), tHi1 xh ^ 2) *
          (∑ xl : Fin (2 ^ mLow), (wLo1 xl - tLo1 xl) ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun xh _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun xl _ ↦ ?_
      have hdiv : (xh.val * 2 ^ mLow + xl.val) / 2 ^ mLow = xh.val := by
        rw [mul_comm xh.val, Nat.mul_add_div (Nat.two_pow_pos mLow),
          Nat.div_eq_of_lt xl.isLt, add_zero]
      have hex : rLo16.extractIndex ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ = xl := by
        apply Fin.ext
        rw [block_extractIndex_val_tg, _root_.pow_zero, Nat.div_one]
        dsimp
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt xl.isLt]
      dsimp only [v3b]; simp only [hdiv, hex]; ring
    rw [hfac]
    have hp := mul_le_mul htHi1_sq hwLo1_err_sq
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by norm_num)
    exact hp.trans (by
      rw [show (2 * (eLo1Num : ℝ) / S) ^ 2 = 4 * ((eLo1Num : ℝ) / S) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _))
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add ha_le hb_le).trans_eq ?_)
  push_cast; ring

theorem twoGear_piece4_l2_bound
    (M mLow D a0Nat a1Nat b0Nat b1Nat : ℕ)
    (hm2 : 2 ≤ mLow) (hm14 : mLow ≤ 14) (hD1 : 1 ≤ D)
    (hL_eq : M + 1 = D * 2 ^ mLow)
    (hge0 : 2 * OuterWeights.SineWindowPrep.scale24 ≤ a0Nat * b0Nat)
    (hge1 : 2 * OuterWeights.SineWindowPrep.scale24 ≤ a1Nat * b1Nat)
    (hab0_lo : (a0Nat * b0Nat - 2 * OuterWeights.SineWindowPrep.scale24) ^ 2 * (M + 1) ≤
      (2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24) ^ 2)
    (hab0_hi : (2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24) ^ 2 ≤
      (a0Nat * b0Nat + 2 * OuterWeights.SineWindowPrep.scale24) ^ 2 * (M + 1))
    (hab1_lo : (a1Nat * b1Nat - 2 * OuterWeights.SineWindowPrep.scale24) ^ 2 * (M + 1) ≤
      (2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24) ^ 2)
    (hab1_hi : (2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24) ^ 2 ≤
      (a1Nat * b1Nat + 2 * OuterWeights.SineWindowPrep.scale24) ^ 2 * (M + 1)) :
    let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
    let mHi := 16 - mLow
    let halfLo := 2 ^ (mLow - 1)
    let rLo16 : QRegister mLow 16 := QRegister.block 0 mLow (by omega)
    let va0 : ℝ := (a0Nat : ℝ) / S
    let va1 : ℝ := (a1Nat : ℝ) / S
    let vb0 : ℝ := (b0Nat : ℝ) / S
    let vb1 : ℝ := (b1Nat : ℝ) / S
    let θHi : ℕ → ℝ := fun j ↦ ((2 * j + 1 : ℕ) : ℝ) * (π / (2 * (D : ℝ)))
    let θLoRev : ℕ → ℝ := fun z ↦
      ((2 * (halfLo - 1 - z) + 1 : ℕ) : ℝ) * (π / (2 * ((M + 1 : ℕ) : ℝ)))
    let tHi0 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va0 * Real.sin (θHi xh.val) else 0
    let tHi1 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va1 * Real.cos (θHi xh.val) else 0
    let tLo0 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if xl.val < halfLo then √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev xl.val))
      else √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev (2 ^ mLow - 1 - xl.val)))
    let tLo1 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if xl.val < halfLo then -√(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev xl.val))
      else √(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev (2 ^ mLow - 1 - xl.val)))
    let v4R : Fin (2 ^ 16) → ℝ := fun g ↦
      let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
        rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)⟩
      tHi0 xh * tLo0 (rLo16.extractIndex g) + tHi1 xh * tLo1 (rLo16.extractIndex g)
    let wTgtR : Fin (2 ^ 16) → ℝ := fun g ↦
      if g.val ≤ M then sineWindowCoeff (M + 1) g.val else 0
    ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v4R g - wTgtR g : ℝ) : ℂ))‖ ≤
      (1024 : ℝ) / S := by
  intro S mHi halfLo rLo16 va0 va1 vb0 vb1 θHi θLoRev tHi0 tHi1 tLo0 tLo1 v4R wTgtR
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hp_lo : 2 ^ mLow = 2 * halfLo := by
    have hm1 : mLow = (mLow - 1) + 1 := by omega
    conv_lhs => rw [hm1, pow_succ']
  have hhalf_pos : 0 < halfLo := Nat.two_pow_pos _
  have h16_rev : mHi + mLow = 16 := by omega
  let LR : ℝ := ((M + 1 : ℕ) : ℝ)
  have hLR_pos : 0 < LR := by dsimp [LR]; positivity
  have hLR_ne : LR ≠ 0 := ne_of_gt hLR_pos
  have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hLR_eq : LR = (D : ℝ) * (2 * (halfLo : ℝ)) := by
    dsimp [LR]
    have h1 : ((M + 1 : ℕ) : ℝ) = (D : ℝ) * ((2 ^ mLow : ℕ) : ℝ) := by exact_mod_cast hL_eq
    have h2 : ((2 ^ mLow : ℕ) : ℝ) = 2 * (halfLo : ℝ) := by exact_mod_cast hp_lo
    rw [h1, h2]
  have hab0 := scale_ab_bound (L := M + 1) (by omega) hge0 hab0_lo hab0_hi
  have hab1 := scale_ab_bound (L := M + 1) (by omega) hge1 hab1_lo hab1_hi
  dsimp only [S] at hab0 hab1
  let αLo : Fin (2 ^ mLow) → ℝ := fun xl ↦
    ((xl.val : ℝ) - (halfLo : ℝ) + 1 / 2) * (π / LR)
  have htLo0_eq : ∀ xl : Fin (2 ^ mLow),
      tLo0 xl = √(1 / 2 : ℝ) * (vb0 * Real.cos (αLo xl)) := by
    intro xl; dsimp only [tLo0]
    by_cases hlt : xl.val < halfLo
    · simp only [hlt, ↓reduceIte]
      have hang : θLoRev xl.val = -αLo xl := by
        dsimp [θLoRev, αLo, LR]
        have hsub : ((halfLo - 1 - xl.val : ℕ) : ℝ) = (halfLo : ℝ) - 1 - (xl.val : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
        push_cast; rw [hsub]; field_simp [hLR_ne]; ring
      rw [hang, Real.cos_neg]
    · simp only [hlt, ↓reduceIte]
      have hang : θLoRev (2 ^ mLow - 1 - xl.val) = αLo xl := by
        dsimp [θLoRev, αLo, LR]
        have hidx : halfLo - 1 - (2 ^ mLow - 1 - xl.val) = xl.val - halfLo := by
          have := xl.isLt; omega
        have hsub : ((xl.val - halfLo : ℕ) : ℝ) = (xl.val : ℝ) - (halfLo : ℝ) :=
          Nat.cast_sub (by omega)
        rw [hidx]; push_cast; rw [hsub]; field_simp [hLR_ne]
      rw [hang]
  have htLo1_eq : ∀ xl : Fin (2 ^ mLow),
      tLo1 xl = √(1 / 2 : ℝ) * (vb1 * Real.sin (αLo xl)) := by
    intro xl; dsimp only [tLo1]
    by_cases hlt : xl.val < halfLo
    · simp only [hlt, ↓reduceIte]
      have hang : θLoRev xl.val = -αLo xl := by
        dsimp [θLoRev, αLo, LR]
        have hsub : ((halfLo - 1 - xl.val : ℕ) : ℝ) = (halfLo : ℝ) - 1 - (xl.val : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
        push_cast; rw [hsub]; field_simp [hLR_ne]; ring
      rw [hang, Real.sin_neg]; ring
    · simp only [hlt, ↓reduceIte]
      have hang : θLoRev (2 ^ mLow - 1 - xl.val) = αLo xl := by
        dsimp [θLoRev, αLo, LR]
        have hidx : halfLo - 1 - (2 ^ mLow - 1 - xl.val) = xl.val - halfLo := by
          have := xl.isLt; omega
        have hsub : ((xl.val - halfLo : ℕ) : ℝ) = (xl.val : ℝ) - (halfLo : ℝ) :=
          Nat.cast_sub (by omega)
        rw [hidx]; push_cast; rw [hsub]; field_simp [hLR_ne]
      rw [hang]
  have hsqrt_rel : √(1 / 2 : ℝ) * (2 / √LR) = √(2 / LR) := by
    refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hLR_pos.le,
      Real.sq_sqrt (by positivity)]
    field_simp [hLR_ne]
  have hsq_half_le1 : √(1 / 2 : ℝ) ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  have hpt : ∀ g : Fin (2 ^ 16), |v4R g - wTgtR g| ≤ 4 / S := by
    intro g
    let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
      rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)⟩
    let xl : Fin (2 ^ mLow) := rLo16.extractIndex g
    have hxl_val : xl.val = g.val % 2 ^ mLow := by
      dsimp [xl]; rw [block_extractIndex_val_tg, _root_.pow_zero, Nat.div_one]
    have hg_decomp : g.val = xh.val * 2 ^ mLow + xl.val := by
      dsimp [xh]; rw [hxl_val, mul_comm _ (2 ^ mLow), Nat.div_add_mod]
    by_cases hltD : xh.val < D
    · have hg_le : g.val ≤ M := by
        have hxl_lt := xl.isLt
        have h1 : (xh.val + 1) * 2 ^ mLow ≤ D * 2 ^ mLow := Nat.mul_le_mul_right _ hltD
        have h2 : xh.val * 2 ^ mLow + 2 ^ mLow = (xh.val + 1) * 2 ^ mLow := by ring
        omega
      have hg_ltL : g.val < M + 1 := by omega
      have hang_sum : θHi xh.val + αLo xl = π * ((g.val : ℝ) + 1 / 2) / LR := by
        dsimp [θHi, αLo]
        have hgR : (g.val : ℝ) = (xh.val : ℝ) * (2 * (halfLo : ℝ)) + (xl.val : ℝ) := by
          have h1 : (g.val : ℝ) = (xh.val : ℝ) * ((2 ^ mLow : ℕ) : ℝ) + (xl.val : ℝ) := by
            exact_mod_cast hg_decomp
          have h2 : ((2 ^ mLow : ℕ) : ℝ) = 2 * (halfLo : ℝ) := by exact_mod_cast hp_lo
          rw [h1, h2]
        rw [hgR, hLR_eq]
        have h2h_ne : (2 : ℝ) * (halfLo : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (halfLo : ℝ) := by exact_mod_cast hhalf_pos
          linarith
        push_cast
        field_simp [hD_ne, h2h_ne]
        ring
      have hv4_eq : v4R g =
          √(1 / 2 : ℝ) * (va0 * vb0) * (Real.sin (θHi xh.val) * Real.cos (αLo xl)) +
            √(1 / 2 : ℝ) * (va1 * vb1) * (Real.cos (θHi xh.val) * Real.sin (αLo xl)) := by
        dsimp [v4R, xh, xl, tHi0, tHi1]
        rw [ite_eq_left hltD, ite_eq_left hltD, htLo0_eq, htLo1_eq]; ring
      have hw_eq : wTgtR g =
          √(1 / 2 : ℝ) * (2 / √LR) * (Real.sin (θHi xh.val) * Real.cos (αLo xl)) +
            √(1 / 2 : ℝ) * (2 / √LR) * (Real.cos (θHi xh.val) * Real.sin (αLo xl)) := by
        dsimp [wTgtR, sineWindowCoeff]
        rw [ite_eq_left hg_le, ite_eq_left hg_ltL]
        change √(2 / LR) * Real.sin (π * ((g.val : ℝ) + 1 / 2) / LR) = _
        rw [← hsqrt_rel, ← hang_sum, Real.sin_add]; ring
      rw [hv4_eq, hw_eq, show
        (√(1 / 2 : ℝ) * (va0 * vb0) * (Real.sin (θHi xh.val) * Real.cos (αLo xl)) +
          √(1 / 2 : ℝ) * (va1 * vb1) * (Real.cos (θHi xh.val) * Real.sin (αLo xl))) -
        (√(1 / 2 : ℝ) * (2 / √LR) * (Real.sin (θHi xh.val) * Real.cos (αLo xl)) +
          √(1 / 2 : ℝ) * (2 / √LR) * (Real.cos (θHi xh.val) * Real.sin (αLo xl))) =
        √(1 / 2 : ℝ) * (va0 * vb0 - 2 / √LR) * (Real.sin (θHi xh.val) * Real.cos (αLo xl)) +
          √(1 / 2 : ℝ) * (va1 * vb1 - 2 / √LR) * (Real.cos (θHi xh.val) * Real.sin (αLo xl))
        by ring]
      have hsc0 : |Real.sin (θHi xh.val) * Real.cos (αLo xl)| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
          (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
      have hsc1 : |Real.cos (θHi xh.val) * Real.sin (αLo xl)| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
          (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
      have ht0 : |√(1 / 2 : ℝ) * (va0 * vb0 - 2 / √LR) *
          (Real.sin (θHi xh.val) * Real.cos (αLo xl))| ≤ 2 / S := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc √(1 / 2 : ℝ) * |va0 * vb0 - 2 / √LR| *
              |Real.sin (θHi xh.val) * Real.cos (αLo xl)|
            ≤ 1 * (2 / S) * 1 :=
              mul_le_mul (mul_le_mul hsq_half_le1 hab0 (abs_nonneg _) zero_le_one)
                hsc0 (abs_nonneg _) (mul_nonneg zero_le_one (div_nonneg zero_le_two hS_pos.le))
          _ = 2 / S := by ring
      have ht1 : |√(1 / 2 : ℝ) * (va1 * vb1 - 2 / √LR) *
          (Real.cos (θHi xh.val) * Real.sin (αLo xl))| ≤ 2 / S := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc √(1 / 2 : ℝ) * |va1 * vb1 - 2 / √LR| *
              |Real.cos (θHi xh.val) * Real.sin (αLo xl)|
            ≤ 1 * (2 / S) * 1 :=
              mul_le_mul (mul_le_mul hsq_half_le1 hab1 (abs_nonneg _) zero_le_one)
                hsc1 (abs_nonneg _) (mul_nonneg zero_le_one (div_nonneg zero_le_two hS_pos.le))
          _ = 2 / S := by ring
      exact (abs_add_le _ _).trans ((add_le_add ht0 ht1).trans_eq (by ring))
    · have hg_gt : ¬ g.val ≤ M := by
        intro hle
        have hgeD : D ≤ xh.val := by omega
        have h1 : D * 2 ^ mLow ≤ g.val := by
          rw [hg_decomp]; exact le_trans (Nat.mul_le_mul_right _ hgeD) (Nat.le_add_right _ _)
        omega
      have hv4_0 : v4R g = 0 := by
        dsimp only [xh] at hltD
        dsimp only [v4R, tHi0, tHi1]
        simp only [hltD, ↓reduceIte, zero_mul, add_zero]
      have hw_0 : wTgtR g = 0 := by
        dsimp only [wTgtR]; simp only [hg_gt, ↓reduceIte]
      rw [hv4_0, hw_0, sub_zero, abs_zero]
      exact div_nonneg (by norm_num) hS_pos.le
  refine norm_toLp_ofReal_le (fun g ↦ v4R g - wTgtR g)
    (div_nonneg (by norm_num) hS_pos.le) ?_
  have hsum : (∑ g : Fin (2 ^ 16), (v4R g - wTgtR g) ^ 2) ≤
      ∑ _g : Fin (2 ^ 16), (4 / S) ^ 2 := by
    refine Finset.sum_le_sum fun g _ ↦ ?_
    rw [← sq_abs (v4R g - wTgtR g)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hpt g) 2
  refine hsum.trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hS_ne]; ring

theorem twoGear_norm4_add_le {E : Type*} [SeminormedAddCommGroup E] (d1 d2 d3 d4 : E) :
    ‖(d1 + d2) + (d3 + d4)‖ ≤ ‖d1‖ + ‖d2‖ + ‖d3‖ + ‖d4‖ := by
  calc ‖(d1 + d2) + (d3 + d4)‖
      ≤ ‖d1 + d2‖ + ‖d3 + d4‖ := norm_add_le _ _
    _ ≤ (‖d1‖ + ‖d2‖) + (‖d3‖ + ‖d4‖) := add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ = ‖d1‖ + ‖d2‖ + ‖d3‖ + ‖d4‖ := by ring

theorem twoGear_budR_div_le {B : ℕ} (hbud : B ≤ 5 * 10 ^ 15) :
    (B : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ) ≤ 5 / 10 ^ 9 := by
  have hb : (B : ℝ) ≤ (5 * 10 ^ 15 : ℝ) := by exact_mod_cast hbud
  calc (B : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ)
      ≤ (5 * 10 ^ 15 : ℝ) / (OuterWeights.SineWindowPrep.scale24 : ℝ) :=
        div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = 5 / 10 ^ 9 := by dsimp [OuterWeights.SineWindowPrep.scale24]; norm_num

theorem twoGear_halfLo_add_lt {mLow x : ℕ} (hm2 : 2 ≤ mLow)
    (hx : x < 2 ^ (mLow - 1)) : 2 ^ (mLow - 1) + x < 2 ^ mLow := by
  have hp : 2 ^ mLow = 2 * 2 ^ (mLow - 1) := by
    conv_lhs => rw [show mLow = (mLow - 1) + 1 by omega, pow_succ']
  omega

theorem twoGear_halfLo_sub_lt {mLow x : ℕ} (hx_lt : x < 2 ^ mLow)
    (hx_ge : ¬ x < 2 ^ (mLow - 1)) :
    2 ^ (mLow - 1) + (2 ^ mLow - 1 - x) < 2 ^ mLow := by
  omega

theorem twoGear_lo_ket0_ket1_orth (mLow : ℕ) (hm2 : 2 ≤ mLow)
    (loTrees : List WordPairTree) (hlenLoT : loTrees.length = mLow - 1)
    (vLo : Fin (2 ^ mLow) → ℝ)
    (hvecLo11 :
      (mottonenCascadeIdealU mLow (mLow - 1) (Nat.sub_le _ _) loTrees).1 *ᵥ
          coarseVec mLow (mLow - 1) (Nat.sub_le _ _) (fun _ ↦ 1) =
        fun x : Fin (2 ^ mLow) ↦ (vLo x : ℂ)) :
    let halfLo := 2 ^ (mLow - 1)
    let hhalf_lt : halfLo < 2 ^ mLow := Nat.pow_lt_pow_right (by decide) (by omega)
    let uLoCasId : Unitary (2 ^ mLow) :=
      mottonenCascadeIdealU mLow (mLow - 1) (by omega) loTrees
    let uLoId : Unitary (2 ^ mLow) := (loCliffordTail mLow (by omega)).eval * uLoCasId
    let wLo0 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if _hlt : xl.val < halfLo then √(1 / 2 : ℝ) * vLo xl
      else √(1 / 2 : ℝ) * vLo ⟨2 ^ mLow - 1 - xl.val, by have := xl.isLt; omega⟩
    let wLo1 : Fin (2 ^ mLow) → ℝ := fun xl ↦
      if _hlt : xl.val < halfLo then
        -√(1 / 2 : ℝ) * vLo ⟨halfLo + xl.val, twoGear_halfLo_add_lt hm2 _hlt⟩
      else
        √(1 / 2 : ℝ) * vLo ⟨halfLo + (2 ^ mLow - 1 - xl.val), twoGear_halfLo_sub_lt xl.isLt _hlt⟩
    (uLoId.1 *ᵥ Pi.single 0 (1 : ℂ) = fun xl ↦ (wLo0 xl : ℂ)) ∧
      (uLoId.1 *ᵥ Pi.single ⟨halfLo, hhalf_lt⟩ (1 : ℂ) = fun xl ↦ (wLo1 xl : ℂ)) ∧
      (∀ Δ0 Δ1 : ℝ,
        ∑ xl : Fin (2 ^ mLow), (Δ0 * wLo0 xl + Δ1 * wLo1 xl) ^ 2 = Δ0 ^ 2 + Δ1 ^ 2) := by
  intro halfLo hhalf_lt uLoCasId uLoId wLo0 wLo1
  have hqLo_sub : mLow - (mLow - 1) = 1 := by omega
  have hp_lo : 2 ^ mLow = 2 * halfLo := by
    dsimp [halfLo]; conv_lhs => rw [show mLow = (mLow - 1) + 1 by omega, pow_succ']
  have hhalf_pos : 0 < halfLo := Nat.two_pow_pos _
  have hvLo_eq_ideal : vLo =
      mottonenIdealVec mLow (mLow - 1) (by omega) loTrees (fun _ ↦ 1) := by
    funext x
    have h1 := congrFun hvecLo11 x
    have h2 := congrFun (mottonenCascadeIdealU_eq_idealVec mLow (mLow - 1) (by omega)
      loTrees (fun _ ↦ 1) hlenLoT) x
    exact Complex.ofReal_injective (h1.symm.trans h2)
  have hdiv1_of_ge : ∀ x : Fin (2 ^ mLow), ¬ x.val < halfLo → x.val / halfLo = 1 := by
    intro x hge
    have h1 : 1 ≤ x.val / halfLo := (Nat.le_div_iff_mul_le hhalf_pos).mpr (by omega)
    have h2 : x.val / halfLo < 2 :=
      Nat.div_lt_of_lt_mul (x.isLt.trans_eq (by rw [hp_lo]; ring))
    omega
  have huLoCas_ket0 :
      uLoCasId.1 *ᵥ Pi.single 0 (1 : ℂ) =
        ∑ z : Fin halfLo,
          (vLo ⟨z.val, lt_of_lt_of_le z.isLt
            (Nat.pow_le_pow_right (by decide) (by omega))⟩ : ℂ) •
            Pi.single ⟨z.val, lt_of_lt_of_le z.isLt
              (Nat.pow_le_pow_right (by decide) (by omega))⟩ 1 := by
    let v10 : Fin (2 ^ (mLow - (mLow - 1))) → ℝ := fun c ↦ if c.val = 0 then 1 else 0
    have hc10 : coarseVec mLow (mLow - 1) (by omega) v10 = Pi.single 0 1 := by
      ext x
      dsimp only [coarseVec]
      rw [Finset.sum_apply, Fintype.sum_eq_single 0 (fun c hc ↦ by
        have hc0 : c.val ≠ 0 := fun h ↦ hc (Fin.ext h)
        dsimp only [v10]; rw [ite_eq_right hc0]
        simp only [Pi.smul_apply, Complex.ofReal_zero, zero_smul])]
      dsimp only [v10]
      simp only [Fin.val_zero, ↓reduceIte, Pi.smul_apply, Complex.ofReal_one, one_smul,
        zero_mul, OuterWeights.SineWindowPrep.ket_basisBits, Pi.single_apply, Fin.ext_iff]
    rw [← hc10, mottonenCascadeIdealU_eq_idealVec mLow (mLow - 1) (by omega) loTrees
      v10 hlenLoT]
    ext x
    by_cases hlt : x.val < halfLo
    · have hdiv0 : x.val / halfLo = 0 := Nat.div_eq_of_lt hlt
      have hsec := mottonenIdealVec_congr_sector mLow (mLow - 1) (by omega) loTrees
        v10 (fun _ ↦ 1) x hlenLoT (by dsimp [v10]; simp [halfLo, hdiv0])
      rw [hsec, ← hvLo_eq_ideal, Finset.sum_apply,
        Finset.sum_eq_single ⟨x.val, hlt⟩
          (fun z _ hz ↦ by
            have hne : x.val ≠ z.val := fun h ↦ hz (Fin.ext h.symm)
            simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, hne, ↓reduceIte, smul_zero])
          (fun h ↦ absurd (Finset.mem_univ _) h)]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have hdiv1 : x.val / halfLo = 1 := hdiv1_of_ge x hlt
      have hsec := mottonenIdealVec_congr_sector mLow (mLow - 1) (by omega) loTrees
        v10 (fun _ ↦ 0) x hlenLoT (by dsimp [v10]; simp [halfLo, hdiv1])
      rw [hsec, mottonenIdealVec_zero, Complex.ofReal_zero, Finset.sum_apply,
        Finset.sum_eq_zero (fun z _ ↦ by
          have hne : x.val ≠ z.val := by have := z.isLt; omega
          simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, hne, ↓reduceIte, smul_zero])]
  have huLoCas_ket1 :
      uLoCasId.1 *ᵥ Pi.single ⟨halfLo, hhalf_lt⟩ (1 : ℂ) =
        ∑ z : Fin halfLo,
          (vLo ⟨halfLo + z.val, by have := z.isLt; omega⟩ : ℂ) •
            Pi.single ⟨halfLo + z.val, by have := z.isLt; omega⟩ 1 := by
    let v01 : Fin (2 ^ (mLow - (mLow - 1))) → ℝ := fun c ↦ if c.val = 1 then 1 else 0
    let cOne : Fin (2 ^ (mLow - (mLow - 1))) := ⟨1, by rw [hqLo_sub]; decide⟩
    have hc01 : coarseVec mLow (mLow - 1) (by omega) v01 =
        Pi.single ⟨halfLo, hhalf_lt⟩ 1 := by
      ext x
      dsimp only [coarseVec]
      rw [Finset.sum_apply, Fintype.sum_eq_single cOne (fun c hc ↦ by
        have hc1 : c.val ≠ 1 := fun h ↦ hc (Fin.ext h)
        dsimp only [v01]; rw [ite_eq_right hc1]
        simp only [Pi.smul_apply, Complex.ofReal_zero, zero_smul])]
      dsimp only [v01, cOne, halfLo]
      simp only [↓reduceIte, one_mul, Pi.smul_apply, Complex.ofReal_one, one_smul,
        OuterWeights.SineWindowPrep.ket_basisBits, Pi.single_apply, Fin.ext_iff]
    rw [← hc01, mottonenCascadeIdealU_eq_idealVec mLow (mLow - 1) (by omega) loTrees
      v01 hlenLoT]
    ext x
    by_cases hlt : x.val < halfLo
    · have hdiv0 : x.val / halfLo = 0 := Nat.div_eq_of_lt hlt
      have hsec := mottonenIdealVec_congr_sector mLow (mLow - 1) (by omega) loTrees
        v01 (fun _ ↦ 0) x hlenLoT (by dsimp [v01]; simp [halfLo, hdiv0])
      rw [hsec, mottonenIdealVec_zero, Complex.ofReal_zero, Finset.sum_apply,
        Finset.sum_eq_zero (fun z _ ↦ by
          have hne : x.val ≠ halfLo + z.val := by omega
          simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, hne, ↓reduceIte, smul_zero])]
    · have hdiv1 : x.val / halfLo = 1 := hdiv1_of_ge x hlt
      have hsec := mottonenIdealVec_congr_sector mLow (mLow - 1) (by omega) loTrees
        v01 (fun _ ↦ 1) x hlenLoT (by dsimp [v01]; simp [halfLo, hdiv1])
      have hsub_lt : x.val - halfLo < halfLo := by have := x.isLt; omega
      rw [hsec, ← hvLo_eq_ideal, Finset.sum_apply,
        Finset.sum_eq_single ⟨x.val - halfLo, hsub_lt⟩
          (fun z _ hz ↦ by
            have hne : x.val ≠ halfLo + z.val := fun h ↦ hz (by ext; dsimp; omega)
            simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, hne, ↓reduceIte, smul_zero])
          (fun h ↦ absurd (Finset.mem_univ _) h)]
      have hfin : (⟨halfLo + (x.val - halfLo), by omega⟩ : Fin (2 ^ mLow)) = x := by
        ext; dsimp; omega
      simp only [hfin, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  have huLoId_ket0 : uLoId.1 *ᵥ Pi.single 0 (1 : ℂ) = fun xl ↦ (wLo0 xl : ℂ) := by
    dsimp only [uLoId]
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, huLoCas_ket0, Matrix.mulVec_sum]
    ext xl
    rw [Finset.sum_apply]
    simp_rw [Matrix.mulVec_smul, loCliffordTail_evolve_ket0 mLow (by omega)]
    by_cases hlt : xl.val < halfLo
    · rw [Finset.sum_eq_single ⟨xl.val, hlt⟩
        (fun z _ hz ↦ by
          have hne0 : xl.val ≠ z.val := fun h ↦ hz (Fin.ext h.symm)
          have hne1 : xl.val ≠ 2 ^ mLow - 1 - z.val := by omega
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
            hne0, hne1, ↓reduceIte, smul_zero, add_zero])
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      have hne1 : xl.val ≠ 2 ^ mLow - 1 - xl.val := by omega
      dsimp only [wLo0]
      simp only [hlt, ↓reduceDIte, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        Fin.ext_iff, hne1, ↓reduceIte, smul_eq_mul, mul_one, mul_zero, add_zero]
      push_cast; ring
    · have hsub_lt : 2 ^ mLow - 1 - xl.val < halfLo := by have := xl.isLt; omega
      rw [Finset.sum_eq_single ⟨2 ^ mLow - 1 - xl.val, hsub_lt⟩
        (fun z _ hz ↦ by
          have hne0 : xl.val ≠ z.val := by have := z.isLt; omega
          have hne1 : xl.val ≠ 2 ^ mLow - 1 - z.val := fun h ↦ hz (by
            ext; dsimp; have := xl.isLt; have := z.isLt; omega)
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
            hne0, hne1, ↓reduceIte, smul_zero, add_zero])
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      have hne0 : xl.val ≠ 2 ^ mLow - 1 - xl.val := by omega
      have h1 : 2 ^ mLow - 1 - (2 ^ mLow - 1 - xl.val) = xl.val := by
        have := xl.isLt; omega
      dsimp only [wLo0]
      simp only [hlt, ↓reduceDIte, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        Fin.ext_iff, hne0, h1, ↓reduceIte, smul_eq_mul, mul_one, mul_zero, zero_add]
      push_cast; ring
  have huLoId_ket1 :
      uLoId.1 *ᵥ Pi.single ⟨halfLo, hhalf_lt⟩ (1 : ℂ) = fun xl ↦ (wLo1 xl : ℂ) := by
    dsimp only [uLoId]
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, huLoCas_ket1, Matrix.mulVec_sum]
    ext xl
    rw [Finset.sum_apply]
    dsimp only [halfLo]
    simp_rw [Matrix.mulVec_smul, loCliffordTail_evolve_ket1 mLow (by omega)]
    change (∑ z : Fin halfLo, _) = _
    by_cases hlt : xl.val < halfLo
    · rw [Finset.sum_eq_single ⟨xl.val, hlt⟩
        (fun z _ hz ↦ by
          have hne0 : xl.val ≠ z.val := fun h ↦ hz (Fin.ext h.symm)
          have hne1 : xl.val ≠ 2 ^ mLow - 1 - z.val := by omega
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
            hne0, hne1, ↓reduceIte, smul_zero, add_zero])
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      have hne1 : xl.val ≠ 2 ^ mLow - 1 - xl.val := by omega
      dsimp only [wLo1]
      simp only [hlt, ↓reduceDIte, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        Fin.ext_iff, hne1, ↓reduceIte, smul_eq_mul, mul_one, mul_zero, add_zero]
      dsimp only [halfLo]
      push_cast; ring
    · have hsub_lt : 2 ^ mLow - 1 - xl.val < halfLo := by have := xl.isLt; omega
      rw [Finset.sum_eq_single ⟨2 ^ mLow - 1 - xl.val, hsub_lt⟩
        (fun z _ hz ↦ by
          have hne0 : xl.val ≠ z.val := by have := z.isLt; omega
          have hne1 : xl.val ≠ 2 ^ mLow - 1 - z.val := fun h ↦ hz (by
            ext; dsimp; have := xl.isLt; have := z.isLt; omega)
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
            hne0, hne1, ↓reduceIte, smul_zero, add_zero])
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      have hne0 : xl.val ≠ 2 ^ mLow - 1 - xl.val := by omega
      have h1 : 2 ^ mLow - 1 - (2 ^ mLow - 1 - xl.val) = xl.val := by
        have := xl.isLt; omega
      dsimp only [wLo1]
      simp only [hlt, ↓reduceDIte, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        Fin.ext_iff, hne0, h1, ↓reduceIte, smul_eq_mul, mul_one, mul_zero, zero_add]
      dsimp only [halfLo]
      push_cast; ring
  have hwLo0_sq : ∑ xl : Fin (2 ^ mLow), wLo0 xl ^ 2 = 1 := by
    have h1 := sum_normSq_unitary_mulVec uLoId (Pi.single 0 (1 : ℂ))
    have hrhs : (∑ j : Fin (2 ^ mLow),
        Complex.normSq ((Pi.single 0 (1 : ℂ) : Fin (2 ^ mLow) → ℂ) j)) = 1 := by
      rw [Fintype.sum_eq_single 0 (fun j hj ↦ by rw [Pi.single_eq_of_ne hj, Complex.normSq_zero]),
        Pi.single_eq_same, Complex.normSq_one]
    rw [huLoId_ket0, hrhs] at h1
    simpa only [Complex.normSq_ofReal, sq] using h1
  have hwLo1_sq : ∑ xl : Fin (2 ^ mLow), wLo1 xl ^ 2 = 1 := by
    have h1 := sum_normSq_unitary_mulVec uLoId (Pi.single ⟨halfLo, hhalf_lt⟩ (1 : ℂ))
    have hrhs : (∑ j : Fin (2 ^ mLow),
        Complex.normSq ((Pi.single ⟨halfLo, hhalf_lt⟩ (1 : ℂ) : Fin (2 ^ mLow) → ℂ) j)) = 1 := by
      rw [Fintype.sum_eq_single ⟨halfLo, hhalf_lt⟩
        (fun j hj ↦ by rw [Pi.single_eq_of_ne hj, Complex.normSq_zero]),
        Pi.single_eq_same, Complex.normSq_one]
    rw [huLoId_ket1, hrhs] at h1
    simpa only [Complex.normSq_ofReal, sq] using h1
  let revLo : Equiv.Perm (Fin (2 ^ mLow)) :=
    { toFun := fun xl ↦ ⟨2 ^ mLow - 1 - xl.val, by have := xl.isLt; omega⟩
      invFun := fun xl ↦ ⟨2 ^ mLow - 1 - xl.val, by have := xl.isLt; omega⟩
      left_inv := fun xl ↦ by ext; dsimp; have := xl.isLt; omega
      right_inv := fun xl ↦ by ext; dsimp; have := xl.isLt; omega }
  have hwLo0_rev : ∀ xl : Fin (2 ^ mLow), wLo0 (revLo xl) = wLo0 xl := by
    intro xl
    dsimp [wLo0, revLo]
    by_cases hlt : xl.val < halfLo
    · have hge : ¬ 2 ^ mLow - 1 - xl.val < halfLo := by omega
      have hback : (⟨2 ^ mLow - 1 - (2 ^ mLow - 1 - xl.val), by omega⟩ : Fin (2 ^ mLow)) = xl := by
        ext; dsimp; omega
      simp [hlt, hge, hback]
    · have hlt' : 2 ^ mLow - 1 - xl.val < halfLo := by have := xl.isLt; omega
      simp [hlt, hlt']
  have hwLo1_rev : ∀ xl : Fin (2 ^ mLow), wLo1 (revLo xl) = -wLo1 xl := by
    intro xl
    dsimp [wLo1, revLo]
    by_cases hlt : xl.val < halfLo
    · have hge : ¬ 2 ^ mLow - 1 - xl.val < halfLo := by omega
      have hback : halfLo + (2 ^ mLow - 1 - (2 ^ mLow - 1 - xl.val)) = halfLo + xl.val := by omega
      simp [hlt, hge, hback]
    · have hlt' : 2 ^ mLow - 1 - xl.val < halfLo := by have := xl.isLt; omega
      simp [hlt, hlt']
  have hwLo_orth : ∑ xl : Fin (2 ^ mLow), wLo0 xl * wLo1 xl = 0 := by
    have hcomp := Equiv.sum_comp revLo (fun xl ↦ wLo0 xl * wLo1 xl)
    have hneg : (∑ xl : Fin (2 ^ mLow), wLo0 (revLo xl) * wLo1 (revLo xl)) =
        -(∑ xl : Fin (2 ^ mLow), wLo0 xl * wLo1 xl) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun xl _ ↦ ?_
      rw [hwLo0_rev, hwLo1_rev]; ring
    linarith
  have hwLo_comb_sq : ∀ Δ0 Δ1 : ℝ,
      ∑ xl : Fin (2 ^ mLow), (Δ0 * wLo0 xl + Δ1 * wLo1 xl) ^ 2 = Δ0 ^ 2 + Δ1 ^ 2 := by
    intro Δ0 Δ1
    have hexp : (∑ xl : Fin (2 ^ mLow), (Δ0 * wLo0 xl + Δ1 * wLo1 xl) ^ 2) =
        Δ0 ^ 2 * (∑ xl, wLo0 xl ^ 2) + Δ1 ^ 2 * (∑ xl, wLo1 xl ^ 2) +
          (2 * Δ0 * Δ1) * (∑ xl, wLo0 xl * wLo1 xl) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun xl _ ↦ by ring
    rw [hexp, hwLo0_sq, hwLo1_sq, hwLo_orth]; ring
  exact ⟨huLoId_ket0, huLoId_ket1, hwLo_comb_sq⟩

theorem twoGear_psi2_eval (mLow : ℕ) (hm2 : 2 ≤ mLow) (hm14 : mLow ≤ 14)
    (uHiId : Unitary (2 ^ (16 - mLow + 1))) (uLoId : Unitary (2 ^ mLow))
    (vHi : Fin (2 ^ (16 - mLow + 1)) → ℝ) (wLo0 wLo1 : Fin (2 ^ mLow) → ℝ)
    (huHi_zero : uHiId.1 *ᵥ basisState 0 = fun y : Fin (2 ^ (16 - mLow + 1)) ↦ (vHi y : ℂ))
    (huLoId_ket0 : uLoId.1 *ᵥ Pi.single 0 (1 : ℂ) = fun xl ↦ (wLo0 xl : ℂ))
    (huLoId_ket1 :
      uLoId.1 *ᵥ Pi.single ⟨2 ^ (mLow - 1), Nat.pow_lt_pow_right (by decide) (by omega)⟩ (1 : ℂ) =
        fun xl ↦ (wLo1 xl : ℂ)) :
    let mHi := 16 - mLow
    let rHi16 : QRegister (mHi + 1) 16 := QRegister.block (mLow - 1) (mHi + 1) (by omega)
    let rLo16 : QRegister mLow 16 := QRegister.block 0 mLow (by omega)
    let v2R : Fin (2 ^ 16) → ℝ := fun g ↦
      let xh := g.val / 2 ^ mLow
      have hxh : xh < 2 ^ mHi := Nat.div_lt_of_lt_mul (by
        rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)
      have h0 : 2 * xh < 2 ^ (mHi + 1) := by rw [pow_succ']; omega
      have h1 : 2 * xh + 1 < 2 ^ (mHi + 1) := by rw [pow_succ']; omega
      vHi ⟨2 * xh, h0⟩ * wLo0 (rLo16.extractIndex g) +
        vHi ⟨2 * xh + 1, h1⟩ * wLo1 (rLo16.extractIndex g)
    (rLo16.embedUnitary uLoId * rHi16.embedUnitary uHiId).1 *ᵥ basisState 0 =
      fun g : Fin (2 ^ 16) ↦ (v2R g : ℂ) := by
  intro mHi rHi16 rLo16 v2R
  let halfLo := 2 ^ (mLow - 1)
  have h16_rev : mHi + mLow = 16 := by omega
  have hp_lo : 2 ^ mLow = 2 * halfLo := by
    dsimp [halfLo]; conv_lhs => rw [show mLow = (mLow - 1) + 1 by omega, pow_succ']
  have hhalf_pos : 0 < halfLo := Nat.two_pow_pos _
  have hhalf_lt : halfLo < 2 ^ mLow := Nat.pow_lt_pow_right (by decide) (by omega)
  have huHi_col0 : ∀ y : Fin (2 ^ (mHi + 1)), uHiId.1 y 0 = (vHi y : ℂ) := by
    intro y
    have h : (uHiId.1 *ᵥ basisState 0) y = (vHi y : ℂ) := congrFun huHi_zero y
    rw [Matrix.mulVec, dotProduct,
      Fintype.sum_eq_single 0 (fun j hj ↦ by
        simp only [basisState, Pi.single_apply, hj, ↓reduceIte, mul_zero])] at h
    simpa only [basisState, Pi.single_eq_same, mul_one] using h
  have hψ₁ : ∀ h : Fin (2 ^ 16),
      ((rHi16.embedUnitary uHiId).1 *ᵥ basisState 0) h =
        if h.val % halfLo = 0 then (vHi (rHi16.extractIndex h) : ℂ) else 0 := by
    intro h
    rw [QRegister.embedUnitary_val, QRegister.embedMatrix_mulVec_apply]
    have hex0 : rHi16.extractIndex 0 = 0 := by
      apply Fin.ext
      rw [block_extractIndex_val_tg]
      simp only [Fin.val_zero, Nat.zero_div, Nat.zero_mod]
    by_cases hmod : h.val % halfLo = 0
    · have hsnd : (rHi16.basisSplitEquiv h).2 = (rHi16.basisSplitEquiv 0).2 :=
        (hiBlock_basisSplit_snd_eq_zero_iff mLow mHi (by omega) (by omega) h).mpr hmod
      rw [ite_eq_left hmod, hsnd,
        Fintype.sum_eq_single (0 : Fin (2 ^ (mHi + 1))) (fun y hy ↦ by
          have hne : rHi16.basisSplitEquiv.symm (y, (rHi16.basisSplitEquiv 0).2) ≠ 0 := by
            intro hc
            have h1 := congrArg (Prod.fst ∘ rHi16.basisSplitEquiv) hc
            simp only [Function.comp_apply, Equiv.apply_symm_apply,
              QRegister.basisSplitEquiv_apply_fst, hex0] at h1
            exact hy h1
          simp [basisState, hne])]
      have heq0 : rHi16.basisSplitEquiv.symm (0, (rHi16.basisSplitEquiv 0).2) = 0 := by
        apply rHi16.basisSplitEquiv.injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext hex0.symm rfl
      rw [heq0]; simp [basisState, huHi_col0]
    · rw [ite_eq_right hmod]
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      have hne : rHi16.basisSplitEquiv.symm (y, (rHi16.basisSplitEquiv h).2) ≠ 0 := by
        intro hc
        have h1 := congrArg (Prod.snd ∘ rHi16.basisSplitEquiv) hc
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at h1
        exact hmod ((hiBlock_basisSplit_snd_eq_zero_iff mLow mHi (by omega) (by omega) h).mp h1)
      simp [basisState, hne]
  have huLo_col0 : ∀ xl : Fin (2 ^ mLow), uLoId.1 xl 0 = (wLo0 xl : ℂ) := by
    intro xl
    have h : (uLoId.1 *ᵥ Pi.single 0 (1 : ℂ)) xl = (wLo0 xl : ℂ) := congrFun huLoId_ket0 xl
    rw [Matrix.mulVec, dotProduct,
      Fintype.sum_eq_single 0 (fun j hj ↦ by
        simp only [Pi.single_apply, hj, ↓reduceIte, mul_zero])] at h
    simpa only [Pi.single_eq_same, mul_one] using h
  have huLo_col1 : ∀ xl : Fin (2 ^ mLow), uLoId.1 xl ⟨halfLo, hhalf_lt⟩ = (wLo1 xl : ℂ) := by
    intro xl
    have h : (uLoId.1 *ᵥ Pi.single ⟨halfLo, hhalf_lt⟩ (1 : ℂ)) xl = (wLo1 xl : ℂ) :=
      congrFun huLoId_ket1 xl
    rw [Matrix.mulVec, dotProduct,
      Fintype.sum_eq_single ⟨halfLo, hhalf_lt⟩
        (fun j hj ↦ by simp only [Pi.single_apply, hj, ↓reduceIte, mul_zero])] at h
    simpa only [Pi.single_eq_same, mul_one] using h
  ext g
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val,
    QRegister.embedMatrix_mulVec_apply]
  let xh := g.val / 2 ^ mLow
  have hxh : xh < 2 ^ mHi := Nat.div_lt_of_lt_mul (by
    rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)
  let hOf : Fin (2 ^ mLow) → Fin (2 ^ 16) := fun u ↦ ⟨xh * 2 ^ mLow + u.val, by
    have hu := u.isLt
    have h1 : (xh + 1) * 2 ^ mLow ≤ 2 ^ mHi * 2 ^ mLow := Nat.mul_le_mul_right _ hxh
    have hp16 : 2 ^ mHi * 2 ^ mLow = 2 ^ 16 := by rw [← pow_add, h16_rev]
    have h2 : xh * 2 ^ mLow + 2 ^ mLow = (xh + 1) * 2 ^ mLow := by ring
    omega⟩
  have hOf_val : ∀ u : Fin (2 ^ mLow), (hOf u).val = xh * 2 ^ mLow + u.val := fun _ ↦ rfl
  have hsymm : ∀ u : Fin (2 ^ mLow),
      rLo16.basisSplitEquiv.symm (u, (rLo16.basisSplitEquiv g).2) = hOf u := by
    intro u
    apply rLo16.basisSplitEquiv.injective
    rw [Equiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · apply Fin.ext
      rw [QRegister.basisSplitEquiv_apply_fst, block_extractIndex_val_tg,
        _root_.pow_zero, Nat.div_one, hOf_val,
        Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt u.isLt]
    · refine ((loBlock_basisSplit_snd_eq_iff mLow (by omega) (hOf u) g).mpr ?_).symm
      rw [hOf_val, mul_comm xh, Nat.mul_add_div (Nat.two_pow_pos mLow),
        Nat.div_eq_of_lt u.isLt, add_zero]
  simp_rw [hsymm, hψ₁]
  let u1 : Fin (2 ^ mLow) := ⟨halfLo, hhalf_lt⟩
  have hu1_val : u1.val = halfLo := rfl
  have hu1_ne0 : u1 ≠ 0 := fun hc ↦ by
    have hv := congrArg Fin.val hc; simp only [hu1_val, Fin.val_zero] at hv; omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ mLow))),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hu1_ne0, Finset.mem_univ u1⟩),
    Finset.sum_eq_zero (fun u hu ↦ by
      rcases Finset.mem_erase.mp hu with ⟨hne1, hu0⟩
      rcases Finset.mem_erase.mp hu0 with ⟨hne0, _⟩
      have hmod : (hOf u).val % halfLo ≠ 0 := by
        have hxh2 : xh * 2 ^ mLow = halfLo * (2 * xh) := by rw [hp_lo]; ring
        have hval : (hOf u).val = u.val + halfLo * (2 * xh) := by
          rw [hOf_val, hxh2, add_comm]
        rw [hval, Nat.add_mul_mod_self_left]
        intro hm0
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hm0
        have hq2 : q < 2 := Nat.lt_of_mul_lt_mul_left (a := halfLo)
          (hq ▸ u.isLt.trans_eq (by rw [hp_lo]; ring))
        rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
        · exact hne0 (Fin.ext (by simp only [Fin.val_zero]; omega))
        · exact hne1 (Fin.ext (by simp only [hu1_val]; omega))
      simp only [hmod, ↓reduceIte, mul_zero]),
    add_zero]
  have hm0 : (hOf 0).val % halfLo = 0 := by
    rw [hOf_val, Fin.val_zero, add_zero, hp_lo,
      show xh * (2 * halfLo) = halfLo * (2 * xh) by ring, Nat.mul_mod_right]
  have hm1 : (hOf u1).val % halfLo = 0 := by
    rw [hOf_val, hu1_val, hp_lo,
      show xh * (2 * halfLo) + halfLo = halfLo * (2 * xh + 1) by ring, Nat.mul_mod_right]
  have hex_h0 : rHi16.extractIndex (hOf 0) =
      ⟨2 * xh, by rw [pow_succ']; omega⟩ := by
    apply Fin.ext
    rw [block_extractIndex_val_tg, hOf_val, Fin.val_zero]
    change (xh * 2 ^ mLow + 0) / halfLo % 2 ^ (mHi + 1) = 2 * xh
    rw [add_zero, hp_lo, show xh * (2 * halfLo) = (2 * xh) * halfLo by ring,
      Nat.mul_div_cancel _ hhalf_pos, Nat.mod_eq_of_lt (by rw [pow_succ']; omega)]
  have hex_h1 : rHi16.extractIndex (hOf u1) =
      ⟨2 * xh + 1, by rw [pow_succ']; omega⟩ := by
    apply Fin.ext
    rw [block_extractIndex_val_tg, hOf_val, hu1_val]
    change (xh * 2 ^ mLow + halfLo) / halfLo % 2 ^ (mHi + 1) = 2 * xh + 1
    rw [hp_lo, show xh * (2 * halfLo) + halfLo = (2 * xh + 1) * halfLo by ring,
      Nat.mul_div_cancel _ hhalf_pos, Nat.mod_eq_of_lt (by rw [pow_succ']; omega)]
  rw [ite_eq_left hm0, ite_eq_left hm1, hex_h0, hex_h1, huLo_col0, huLo_col1]
  dsimp [v2R, xh]
  push_cast; ring

theorem twoGear_piece2_l2_bound
    (mLow D a0Nat a1Nat eHiNum : ℕ) (hm14 : mLow ≤ 14)
    (hiAmps : List AmpCert) (hlenAmpsHi : hiAmps.length = 2 ^ (16 - mLow + 1))
    (vHi : Fin (2 ^ (16 - mLow + 1)) → ℝ)
    (hvalHi : ∀ y : Fin (2 ^ (16 - mLow + 1)),
      (hiAmps[y.val]'(y.isLt.trans_eq hlenAmpsHi.symm)).Valid (vHi y))
    (hiTrigs : List OuterWeights.SineWindowPrep.TrigCert) (hlenGHi : hiTrigs.length = D)
    (hvalGHi : ∀ (j : ℕ) (hj : j < hiTrigs.length),
      (hiTrigs[j]'hj).Valid ((2 * (j : ℝ) + 1) * (π / (2 * (D : ℝ)))))
    (herrHi : sumHiErrSq D ⟨.ofNat a0Nat, 0⟩ ⟨.ofNat a1Nat, 0⟩ hiAmps hiTrigs
      (2 ^ (16 - mLow)) 0 ≤ eHiNum * eHiNum)
    (wLo0 wLo1 : Fin (2 ^ mLow) → ℝ)
    (hwLo_comb_sq : ∀ Δ0 Δ1 : ℝ,
      ∑ xl : Fin (2 ^ mLow), (Δ0 * wLo0 xl + Δ1 * wLo1 xl) ^ 2 = Δ0 ^ 2 + Δ1 ^ 2) :
    let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
    let mHi := 16 - mLow
    let rLo16 : QRegister mLow 16 := QRegister.block 0 mLow (by omega)
    let va0 : ℝ := (a0Nat : ℝ) / S
    let va1 : ℝ := (a1Nat : ℝ) / S
    let θHi : ℕ → ℝ := fun j ↦ ((2 * j + 1 : ℕ) : ℝ) * (π / (2 * (D : ℝ)))
    let tHi0 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va0 * Real.sin (θHi xh.val) else 0
    let tHi1 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va1 * Real.cos (θHi xh.val) else 0
    let v2R : Fin (2 ^ 16) → ℝ := fun g ↦
      let xh := g.val / 2 ^ mLow
      have hxh : xh < 2 ^ mHi := Nat.div_lt_of_lt_mul (by
        rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)
      have h0 : 2 * xh < 2 ^ (mHi + 1) := by rw [pow_succ']; omega
      have h1 : 2 * xh + 1 < 2 ^ (mHi + 1) := by rw [pow_succ']; omega
      vHi ⟨2 * xh, h0⟩ * wLo0 (rLo16.extractIndex g) +
        vHi ⟨2 * xh + 1, h1⟩ * wLo1 (rLo16.extractIndex g)
    let v3R : Fin (2 ^ 16) → ℝ := fun g ↦
      let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
        rw [mul_comm, ← pow_add, show mHi + mLow = 16 by omega]; exact g.isLt)⟩
      tHi0 xh * wLo0 (rLo16.extractIndex g) + tHi1 xh * wLo1 (rLo16.extractIndex g)
    ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v2R g - v3R g : ℝ) : ℂ))‖ ≤
      (eHiNum : ℝ) / S := by
  intro S mHi rLo16 va0 va1 θHi tHi0 tHi1 v2R v3R
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have h16 : mLow + mHi = 16 := by omega
  have h16_rev : mHi + mLow = 16 := by omega
  have ha0_val : (⟨.ofNat a0Nat, 0⟩ : AmpCert).Valid va0 := by
    simp [AmpCert.Valid, OuterWeights.SineWindowPrep.SInt.toReal_ofNat, va0, S]
  have ha1_val : (⟨.ofNat a1Nat, 0⟩ : AmpCert).Valid va1 := by
    simp [AmpCert.Valid, OuterWeights.SineWindowPrep.SInt.toReal_ofNat, va1, S]
  have hidx16 (xh : Fin (2 ^ mHi)) (xl : Fin (2 ^ mLow)) :
      xh.val * 2 ^ mLow + xl.val < 2 ^ 16 :=
    calc xh.val * 2 ^ mLow + xl.val
        < xh.val * 2 ^ mLow + 2 ^ mLow := Nat.add_lt_add_left xl.isLt _
      _ = (xh.val + 1) * 2 ^ mLow := by ring
      _ ≤ 2 ^ mHi * 2 ^ mLow := Nat.mul_le_mul_right _ xh.isLt
      _ = 2 ^ 16 := by rw [← pow_add, h16_rev]
  refine norm_toLp_ofReal_le (fun g ↦ v2R g - v3R g)
    (div_nonneg (Nat.cast_nonneg _) hS_pos.le) ?_
  rw [sum_16_split_hi_lo mLow mHi h16]
  have h2xh0 (xh : Fin (2 ^ mHi)) : 2 * xh.val < 2 ^ (16 - mLow + 1) := by
    have hlt : xh.val < 2 ^ (16 - mLow) := xh.isLt
    rw [pow_succ']; omega
  have h2xh1 (xh : Fin (2 ^ mHi)) : 2 * xh.val + 1 < 2 ^ (16 - mLow + 1) := by
    have hlt : xh.val < 2 ^ (16 - mLow) := xh.isLt
    rw [pow_succ']; omega
  have hrow : ∀ xh : Fin (2 ^ mHi),
      (∑ xl : Fin (2 ^ mLow),
        (v2R ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ -
          v3R ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩) ^ 2) =
        (vHi ⟨2 * xh.val, h2xh0 xh⟩ - tHi0 xh) ^ 2 +
          (vHi ⟨2 * xh.val + 1, h2xh1 xh⟩ - tHi1 xh) ^ 2 := by
    intro xh
    have hcongr : ∀ xl : Fin (2 ^ mLow),
        v2R ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ -
            v3R ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ =
          (vHi ⟨2 * xh.val, h2xh0 xh⟩ - tHi0 xh) * wLo0 xl +
            (vHi ⟨2 * xh.val + 1, h2xh1 xh⟩ - tHi1 xh) * wLo1 xl := by
      intro xl
      have hdiv : (xh.val * 2 ^ mLow + xl.val) / 2 ^ mLow = xh.val := by
        rw [mul_comm xh.val, Nat.mul_add_div (Nat.two_pow_pos mLow),
          Nat.div_eq_of_lt xl.isLt, add_zero]
      have hex : rLo16.extractIndex ⟨xh.val * 2 ^ mLow + xl.val, hidx16 xh xl⟩ = xl := by
        apply Fin.ext
        rw [block_extractIndex_val_tg, _root_.pow_zero, Nat.div_one]
        dsimp
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt xl.isLt]
      dsimp only [v2R, v3R]
      simp only [hdiv, hex]
      ring
    simp_rw [hcongr]
    exact hwLo_comb_sq _ _
  simp_rw [hrow]
  let vHiNat : ℕ → ℝ := fun i ↦ if hi : i < 2 ^ (mHi + 1) then vHi ⟨i, hi⟩ else 0
  have hsum_eq :
      (∑ xh : Fin (2 ^ mHi),
        ((vHi ⟨2 * xh.val, h2xh0 xh⟩ - tHi0 xh) ^ 2 +
          (vHi ⟨2 * xh.val + 1, h2xh1 xh⟩ - tHi1 xh) ^ 2)) =
      ∑ j ∈ Finset.range (2 ^ mHi),
        ((vHiNat (2 * j) - if j < D then va0 * Real.sin (θHi j) else 0) ^ 2 +
          (vHiNat (2 * j + 1) - if j < D then va1 * Real.cos (θHi j) else 0) ^ 2) := by
    let fHi : ℕ → ℝ := fun j ↦
      (vHiNat (2 * j) - if j < D then va0 * Real.sin (θHi j) else 0) ^ 2 +
        (vHiNat (2 * j + 1) - if j < D then va1 * Real.cos (θHi j) else 0) ^ 2
    have hfHi :
        (∑ xh : Fin (2 ^ mHi),
          ((vHi ⟨2 * xh.val, h2xh0 xh⟩ - tHi0 xh) ^ 2 +
            (vHi ⟨2 * xh.val + 1, h2xh1 xh⟩ - tHi1 xh) ^ 2)) =
        ∑ xh : Fin (2 ^ mHi), fHi xh.val := by
      refine Finset.sum_congr rfl fun xh _ ↦ ?_
      have h0 : 2 * xh.val < 2 ^ (mHi + 1) := h2xh0 xh
      have h1 : 2 * xh.val + 1 < 2 ^ (mHi + 1) := h2xh1 xh
      dsimp only [fHi, vHiNat, tHi0, tHi1]
      simp only [h0, h1, ↓reduceDIte]
    exact hfHi.trans (Fin.sum_univ_eq_sum_range fHi (2 ^ mHi))
  rw [hsum_eq]
  have hspec := sumHiErrSq_spec D ⟨.ofNat a0Nat, 0⟩ ⟨.ofNat a1Nat, 0⟩
    hiAmps hiTrigs vHiNat θHi va0 va1 ha0_val ha1_val
    (fun j hj ↦ ⟨by omega, by simpa [θHi] using hvalGHi j (by rw [hlenGHi]; exact hj)⟩)
    (2 ^ mHi) (by dsimp only [mHi]; rw [hlenAmpsHi, pow_succ'])
    (fun i hi ↦ by
      have hi_lt : i < 2 ^ (mHi + 1) := by dsimp only [mHi] at hi ⊢; rw [pow_succ']; omega
      refine ⟨hi_lt.trans_eq hlenAmpsHi.symm, ?_⟩
      dsimp [vHiNat]; simp only [hi_lt, ↓reduceDIte]
      exact hvalHi ⟨i, hi_lt⟩)
  refine hspec.trans ?_
  rw [div_pow]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg S)
  exact_mod_cast herrHi.trans_eq (sq eHiNum).symm

theorem checkTwoGearRegime_sound (d : TwoGearRegimeData)
    (hok : checkTwoGearRegime d = true) :
    let hm := checkTwoGearRegime_meta d hok
    let cWinHi := twoGearZeroAncHi d
    let cWinLo := twoGearZeroAncLo d (by have := hm.2.2.2.1; omega)
    cWinHi.count .TOFF = 0 ∧
      cWinLo.count .TOFF = 0 ∧
      cWinHi.count .T + cWinLo.count .T = d.tWin ∧
      ‖WithLp.toLp 2
        ((((QRegister.block 0 d.mLow (by have := hm.2.2.2.2; omega) :
              QRegister d.mLow 16).embedUnitary cWinLo.eval) *
          ((rWinHiInQPE d.mLow 0 (by have := hm.2.2.2.1; omega)
              (by have := hm.2.2.2.2; omega) (Nat.zero_le _)).embedUnitary
            cWinHi.eval)).1 *ᵥ basisState 0 -
          windowVec 16 d.M (sineWindowCoeff (d.M + 1)))‖ ≤ 5 / 10 ^ 9 := by
  intro hm
  dsimp only [twoGearZeroAncHi, twoGearZeroAncLo]
  rcases d with ⟨M, mLow, D, mHi, c0Mid, s0Mid, a0Nat, a1Nat, b0Nat, b1Nat,
    eHiNum, eLo0Num, eLo1Num, tWin, hiTrees, loTrees⟩
  dsimp only at hok hm ⊢
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  have hS_pos : 0 < S := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  dsimp only [checkTwoGearRegime] at hok
  simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq,
    OuterWeights.SineWindowPrep.withForcedNat_eq,
    withForcedList_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
  rcases hok with ⟨hm2, hm14, hmHi_eq, hD1, hD_le, hL_eq, hge0, hge1,
    hab0_lo, hab0_hi, hab1_lo, hab1_hi, hDa0, hDa1, hlenHiT, hlenLoT,
    hBase, hokDbl, hokGHi, hokGLo, hokRHi, hokRLo,
    herrHi, herrLo0, herrLo1, htcTot, hbudTot⟩
  subst hmHi_eq
  let mHi := 16 - mLow
  have h16_rev : mHi + mLow = 16 := by omega
  let rDrop0 : QRegister (16 - mLow + 1) (0 + (16 - mLow + 1)) :=
    QRegister.block 0 (16 - mLow + 1) le_rfl
  let cHiRaw : Circuit (mHi + 1) := mottonenCascade (mHi + 1) (mHi + 1) le_rfl hiTrees
  let cWinHi : Circuit (0 + (16 - mLow + 1)) := cHiRaw.onRegister rDrop0
  let cLoCas : Circuit mLow := mottonenCascade mLow (mLow - 1) (Nat.sub_le _ _) loTrees
  let cWinLo : Circuit mLow := cLoCas.seq (loCliffordTail mLow (by omega))
  change cWinHi.count .TOFF = 0 ∧ cWinLo.count .TOFF = 0 ∧
    cWinHi.count .T + cWinLo.count .T = tWin ∧
    ‖WithLp.toLp 2
      ((((QRegister.block 0 mLow (by omega) : QRegister mLow 16).embedUnitary cWinLo.eval) *
        ((rWinHiInQPE mLow 0 (by omega) (by omega) (Nat.zero_le _)).embedUnitary
          cWinHi.eval)).1 *ᵥ basisState 0 -
        windowVec 16 M (sineWindowCoeff (M + 1)))‖ ≤ 5 / 10 ^ 9
  have hAmp1 : (⟨.ofNat OuterWeights.SineWindowPrep.scale24, 0⟩ : AmpCert).Valid 1 := by
    dsimp [AmpCert.Valid]
    rw [OuterWeights.SineWindowPrep.SInt.toReal_ofNat, div_self hS_ne, sub_self, abs_zero]
    simp
  obtain ⟨vHi, hlenAmpsHi, htoffHi, htcHi, _, hapHi, hvecHi, hvalHi⟩ :=
    evalMottonenAux_spec (mHi + 1) (mHi + 1) le_rfl hiTrees
      [⟨.ofNat OuterWeights.SineWindowPrep.scale24, 0⟩] 0 0 (fun _ ↦ 1) (by simp)
      (fun c ↦ by
        have hc1 : c.val < 1 := by simpa using c.isLt
        have hc0 : c.val = 0 := by omega
        simp [hc0, hAmp1]) hokRHi
  have hqLo_sub : mLow - (mLow - 1) = 1 := by omega
  obtain ⟨vLo, hlenAmpsLo, htoffLoCas, htcLoCas, _, hapLoCas, hvecLo11, hvalLo⟩ :=
    evalMottonenAux_spec mLow (mLow - 1) (Nat.sub_le _ _) loTrees
      [⟨.ofNat scale24, 0⟩, ⟨.ofNat scale24, 0⟩] 0 0
      (fun _ ↦ 1) (by rw [hqLo_sub]; rfl)
      (fun c ↦ by
        have hc2 : c.val < 2 := c.isLt.trans_eq (by rw [hqLo_sub]; rfl)
        rcases (by omega : c.val = 0 ∨ c.val = 1) with h0 | h1
        · simp [h0, hAmp1]
        · simp [h1, hAmp1])
      hokRLo
  obtain ⟨htoffTail, htcTail⟩ := loCliffordTail_counts mLow (by omega)
  have htoffWinHi : cWinHi.count .TOFF = 0 := by
    dsimp [cWinHi, cHiRaw]; simp [htoffHi]
  have htoffWinLo : cWinLo.count .TOFF = 0 := by
    dsimp [cWinLo]; simp [cLoCas, htoffLoCas, htoffTail]
  have htcWinHi : cWinHi.count .T = (evalMottonenAmps (mHi + 1) hiTrees).2.2.2 := by
    dsimp [cWinHi, cHiRaw, evalMottonenAmps]
    rw [Circuit.count_onRegister]; omega
  have htcWinLo : cWinLo.count .T =
      (evalMottonenAux mLow (mLow - 1) loTrees
        [⟨.ofNat scale24, 0⟩, ⟨.ofNat scale24, 0⟩]
        0 0).2.2.2 := by
    dsimp only [cWinLo, cLoCas]; rw [Circuit.count_seq, htcTail]; omega
  refine ⟨htoffWinHi, htoffWinLo, by rw [htcWinHi, htcWinLo]; exact htcTot, ?_⟩
  have hreg_eq :
      (rWinHiInQPE mLow 0 (by omega) (by omega) (Nat.zero_le _)).compose rDrop0 =
        (QRegister.block (mLow - 1) (mHi + 1) (by omega) : QRegister (mHi + 1) 16) := by
    ext i
    obtain ⟨a | b, hab⟩ := finSumFinEquiv.surjective (rDrop0 i)
    · exact Fin.elim0 a
    · have hb_val : b.val = i.val := by
        have hv := congrArg Fin.val hab
        simp only [rDrop0, QRegister.block_apply_val, finSumFinEquiv_apply_right,
          Fin.val_natAdd, zero_add] at hv
        exact hv
      rw [QRegister.compose_apply, ← hab, rWinHiInQPE, finSumFinEquiv_apply_right,
        QRegister.concat_apply_right]
      simp only [QRegister.block_apply_val, hb_val]
  have hcWinHi_embed :
      (rWinHiInQPE mLow 0 (by omega) (by omega) (Nat.zero_le _)).embedUnitary cWinHi.eval =
        (QRegister.block (mLow - 1) (mHi + 1) (by omega) :
          QRegister (mHi + 1) 16).embedUnitary cHiRaw.eval := by
    dsimp only [cWinHi]
    rw [Circuit.eval_onRegister, ← QRegister.embedUnitary_compose, hreg_eq]
  rw [hcWinHi_embed]
  let rHi16 : QRegister (mHi + 1) 16 := QRegister.block (mLow - 1) (mHi + 1) (by omega)
  let rLo16 : QRegister mLow 16 := QRegister.block 0 mLow (by omega)
  let uHiId : Unitary (2 ^ (mHi + 1)) := mottonenCascadeIdealU (mHi + 1) (mHi + 1) le_rfl hiTrees
  let uLoCasId : Unitary (2 ^ mLow) :=
    mottonenCascadeIdealU mLow (mLow - 1) (by omega) loTrees
  let uLoId : Unitary (2 ^ mLow) := (loCliffordTail mLow (by omega)).eval * uLoCasId
  let nlHi := (evalMottonenAmps (mHi + 1) hiTrees).2.2.1
  let nlLo := (evalMottonenAux mLow (mLow - 1) loTrees
    [⟨.ofNat scale24, 0⟩, ⟨.ofNat scale24, 0⟩] 0 0).2.2.1
  have hS_pow : S = 10 ^ 24 := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; norm_num
  have hleaf_nn : ∀ n : ℕ, 0 ≤ (n : ℝ) * ((dRzLeafNum : ℝ) / 10 ^ 24) := fun n ↦
    mul_nonneg (Nat.cast_nonneg n) (by dsimp [dRzLeafNum]; positivity)
  have hapHi16 : OuterWeights.SineWindowPrep.VecApprox (rHi16.embedUnitary cHiRaw.eval)
      (rHi16.embedUnitary uHiId) (((nlHi : ℝ) * (dRzLeafNum : ℝ)) / S) := by
    have h0 : OuterWeights.SineWindowPrep.VecApprox cHiRaw.eval uHiId
        ((nlHi : ℝ) * ((dRzLeafNum : ℝ) / 10 ^ 24)) := by
      dsimp only [nlHi, evalMottonenAmps]
      simpa only [Nat.sub_zero] using hapHi
    have h1 := OuterWeights.SineWindowPrep.VecApprox.embed rHi16 (hleaf_nn nlHi) h0
    exact h1.mono (le_of_eq (by rw [hS_pow]; ring))
  have hapLo16 : OuterWeights.SineWindowPrep.VecApprox (rLo16.embedUnitary cWinLo.eval)
      (rLo16.embedUnitary uLoId) (((nlLo : ℝ) * (dRzLeafNum : ℝ)) / S) := by
    have h0 : OuterWeights.SineWindowPrep.VecApprox cLoCas.eval uLoCasId
        ((nlLo : ℝ) * ((dRzLeafNum : ℝ) / 10 ^ 24)) := by
      simpa only [Nat.sub_zero] using hapLoCas
    have hlo1 : OuterWeights.SineWindowPrep.VecApprox cWinLo.eval uLoId
        ((nlLo : ℝ) * ((dRzLeafNum : ℝ) / 10 ^ 24)) := by
      dsimp only [cWinLo, uLoId]
      rw [Circuit.eval_seq]
      exact (OuterWeights.SineWindowPrep.VecApprox.mul
        (OuterWeights.SineWindowPrep.VecApprox.refl (loCliffordTail mLow (by omega)).eval)
        h0).mono (le_of_eq (by ring))
    exact (OuterWeights.SineWindowPrep.VecApprox.embed rLo16 (hleaf_nn nlLo) hlo1).mono
      (le_of_eq (by rw [hS_pow]; ring))
  have hapComb := OuterWeights.SineWindowPrep.VecApprox.mul hapLo16 hapHi16
  have hnorm_zero16 : ‖WithLp.toLp 2 (basisState (0 : Fin (2 ^ 16)))‖ = 1 := by
    have hsq : ‖WithLp.toLp 2 (basisState (0 : Fin (2 ^ 16)))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_eq_single 0 (fun i hi ↦ by simp [basisState, hi])]
      simp [basisState]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [hsq, _root_.one_pow])
  have hPiece1 :
      ‖WithLp.toLp 2
        ((rLo16.embedUnitary cWinLo.eval * rHi16.embedUnitary cHiRaw.eval).1 *ᵥ basisState 0 -
          (rLo16.embedUnitary uLoId * rHi16.embedUnitary uHiId).1 *ᵥ basisState 0)‖ ≤
        (((nlHi + nlLo) * dRzLeafNum : ℕ) : ℝ) / S := by
    have hb := hapComb (basisState 0)
    rw [hnorm_zero16, mul_one] at hb
    exact hb.trans_eq (by push_cast; ring)
  have ht0_val : (⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩ : OuterWeights.SineWindowPrep.TrigCert).Valid
      (π / (2 * ((M + 1 : ℕ) : ℝ))) :=
    (checkBaseTrigNatSC_valid hBase).2
  have htHi0_val :
      (OuterWeights.SineWindowPrep.iterDoubleTrig mLow
        ⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩).1.Valid
      (π / (2 * (D : ℝ))) := by
    have hdbl := OuterWeights.SineWindowPrep.iterDoubleTrig_valid mLow ht0_val hokDbl
    have hang : (2 : ℝ) ^ mLow * (π / (2 * ((M + 1 : ℕ) : ℝ))) = π / (2 * (D : ℝ)) := by
      have hL_cast : ((M + 1 : ℕ) : ℝ) = (D : ℝ) * (2 : ℝ) ^ mLow := by
        exact_mod_cast hL_eq
      have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
      have hp_ne : (2 : ℝ) ^ mLow ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [hL_cast]; field_simp [hD_ne, hp_ne]
    rwa [hang] at hdbl
  obtain ⟨hlenGHi, hvalGHi⟩ := buildOddTrigGrid_spec D htHi0_val hokGHi
  let halfLo := 2 ^ (mLow - 1)
  obtain ⟨hlenGLo, hvalGLo⟩ := buildOddTrigGrid_spec halfLo ht0_val hokGLo
  have hcoarseHi :
      coarseVec (mHi + 1) (mHi + 1) le_rfl
        (fun _ : Fin (2 ^ ((mHi + 1) - (mHi + 1))) ↦ (1 : ℝ)) =
      basisState 0 := by
    ext y
    dsimp only [coarseVec]
    rw [Finset.sum_apply, Fintype.sum_eq_single 0 (fun c hc ↦ by
      have hc1 : c.val < 1 := by simpa [Nat.sub_self] using c.isLt
      exact absurd (Fin.ext (by omega : c.val = 0)) hc)]
    simp only [Pi.smul_apply, Complex.ofReal_one, one_smul, Fin.val_zero, zero_mul,
      OuterWeights.SineWindowPrep.ket_basisBits, basisState, Pi.single_apply, Fin.ext_iff]
  have huHi_zero : uHiId.1 *ᵥ basisState 0 = fun y : Fin (2 ^ (mHi + 1)) ↦ (vHi y : ℂ) := by
    rw [← hcoarseHi]; exact hvecHi
  let wLo0 : Fin (2 ^ mLow) → ℝ := fun xl ↦
    if _hlt : xl.val < halfLo then √(1 / 2 : ℝ) * vLo xl
    else √(1 / 2 : ℝ) * vLo ⟨2 ^ mLow - 1 - xl.val, by have := xl.isLt; omega⟩
  let wLo1 : Fin (2 ^ mLow) → ℝ := fun xl ↦
    if _hlt : xl.val < halfLo then
      -√(1 / 2 : ℝ) * vLo ⟨halfLo + xl.val, twoGear_halfLo_add_lt hm2 _hlt⟩
    else
      √(1 / 2 : ℝ) * vLo ⟨halfLo + (2 ^ mLow - 1 - xl.val), twoGear_halfLo_sub_lt xl.isLt _hlt⟩
  obtain ⟨huLoId_ket0, huLoId_ket1, hwLo_comb_sq⟩ :=
    twoGear_lo_ket0_ket1_orth mLow hm2 loTrees hlenLoT vLo hvecLo11
  let v2R : Fin (2 ^ 16) → ℝ := fun g ↦
    let xh := g.val / 2 ^ mLow
    have hxh : xh < 2 ^ mHi := Nat.div_lt_of_lt_mul (by
      rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)
    have h0 : 2 * xh < 2 ^ (mHi + 1) := by rw [pow_succ']; omega
    have h1 : 2 * xh + 1 < 2 ^ (mHi + 1) := by rw [pow_succ']; omega
    vHi ⟨2 * xh, h0⟩ * wLo0 (rLo16.extractIndex g) +
      vHi ⟨2 * xh + 1, h1⟩ * wLo1 (rLo16.extractIndex g)
  have hψ₂ :
      (rLo16.embedUnitary uLoId * rHi16.embedUnitary uHiId).1 *ᵥ basisState 0 =
        fun g : Fin (2 ^ 16) ↦ (v2R g : ℂ) :=
    twoGear_psi2_eval mLow hm2 hm14 uHiId uLoId vHi wLo0 wLo1
      huHi_zero huLoId_ket0 huLoId_ket1
  let va0 : ℝ := (a0Nat : ℝ) / S
  let va1 : ℝ := (a1Nat : ℝ) / S
  let vb0 : ℝ := (b0Nat : ℝ) / S
  let vb1 : ℝ := (b1Nat : ℝ) / S
  let θHi : ℕ → ℝ := fun j ↦ ((2 * j + 1 : ℕ) : ℝ) * (π / (2 * (D : ℝ)))
  let θLoRev : ℕ → ℝ := fun z ↦
    ((2 * (halfLo - 1 - z) + 1 : ℕ) : ℝ) * (π / (2 * ((M + 1 : ℕ) : ℝ)))
  let tHi0 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va0 * Real.sin (θHi xh.val) else 0
  let tHi1 : Fin (2 ^ mHi) → ℝ := fun xh ↦ if xh.val < D then va1 * Real.cos (θHi xh.val) else 0
  let tLo0 : Fin (2 ^ mLow) → ℝ := fun xl ↦
    if xl.val < halfLo then √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev xl.val))
    else √(1 / 2 : ℝ) * (vb0 * Real.cos (θLoRev (2 ^ mLow - 1 - xl.val)))
  let tLo1 : Fin (2 ^ mLow) → ℝ := fun xl ↦
    if xl.val < halfLo then -√(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev xl.val))
    else √(1 / 2 : ℝ) * (vb1 * Real.sin (θLoRev (2 ^ mLow - 1 - xl.val)))
  let v3R : Fin (2 ^ 16) → ℝ := fun g ↦
    let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
      rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)⟩
    tHi0 xh * wLo0 (rLo16.extractIndex g) + tHi1 xh * wLo1 (rLo16.extractIndex g)
  let v4R : Fin (2 ^ 16) → ℝ := fun g ↦
    let xh : Fin (2 ^ mHi) := ⟨g.val / 2 ^ mLow, Nat.div_lt_of_lt_mul (by
      rw [mul_comm, ← pow_add, h16_rev]; exact g.isLt)⟩
    tHi0 xh * tLo0 (rLo16.extractIndex g) + tHi1 xh * tLo1 (rLo16.extractIndex g)
  let wTgtR : Fin (2 ^ 16) → ℝ := fun g ↦
    if g.val ≤ M then sineWindowCoeff (M + 1) g.val else 0
  have hwTgt_coe : (fun g : Fin (2 ^ 16) ↦ (wTgtR g : ℂ)) =
      windowVec 16 M (sineWindowCoeff (M + 1)) := by
    ext g; dsimp [wTgtR, windowVec]; split_ifs <;> simp
  have hPiece2 :
      ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v2R g - v3R g : ℝ) : ℂ))‖ ≤
        (eHiNum : ℝ) / S :=
    twoGear_piece2_l2_bound mLow D a0Nat a1Nat eHiNum hm14
      _ hlenAmpsHi vHi hvalHi _ hlenGHi hvalGHi herrHi wLo0 wLo1 hwLo_comb_sq
  obtain ⟨hwLo0_err_sq, hwLo1_err_sq⟩ := twoGear_lo_err_sq M mLow c0Mid s0Mid b0Nat b1Nat
    eLo0Num eLo1Num hm2 _ hlenAmpsLo vLo hvalLo hlenGLo hvalGLo herrLo0 herrLo1
  have hPiece3 :
      ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v3R g - v4R g : ℝ) : ℂ))‖ ≤
        (2 * ((eLo0Num + eLo1Num : ℕ) : ℝ)) / S :=
    twoGear_piece3_l2_bound mLow D a0Nat a1Nat eLo0Num eLo1Num hm14 hD_le hDa0 hDa1
      wLo0 wLo1 tLo0 tLo1 hwLo0_err_sq hwLo1_err_sq
  have hPiece4 :
      ‖WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v4R g - wTgtR g : ℝ) : ℂ))‖ ≤
        (1024 : ℝ) / S :=
    twoGear_piece4_l2_bound M mLow D a0Nat a1Nat b0Nat b1Nat hm2 hm14 hD1 hL_eq
      hge0 hge1 hab0_lo hab0_hi hab1_lo hab1_hi
  let d1 := WithLp.toLp 2
    ((rLo16.embedUnitary cWinLo.eval * rHi16.embedUnitary cHiRaw.eval).1 *ᵥ basisState 0 -
      (rLo16.embedUnitary uLoId * rHi16.embedUnitary uHiId).1 *ᵥ basisState 0)
  let d2 := WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v2R g - v3R g : ℝ) : ℂ))
  let d3 := WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v3R g - v4R g : ℝ) : ℂ))
  let d4 := WithLp.toLp 2 (fun g : Fin (2 ^ 16) ↦ ((v4R g - wTgtR g : ℝ) : ℂ))
  have hdecomp :
      WithLp.toLp 2
        ((rLo16.embedUnitary cWinLo.eval * rHi16.embedUnitary cHiRaw.eval).1 *ᵥ basisState 0 -
          windowVec 16 M (sineWindowCoeff (M + 1))) =
        (d1 + d2) + (d3 + d4) := by
    rw [← hwTgt_coe]
    ext g
    have h2g := congrFun hψ₂ g
    change ((rLo16.embedUnitary cWinLo.eval * rHi16.embedUnitary cHiRaw.eval).1 *ᵥ
        basisState 0) g - (wTgtR g : ℂ) =
      (((rLo16.embedUnitary cWinLo.eval * rHi16.embedUnitary cHiRaw.eval).1 *ᵥ basisState 0) g -
        ((rLo16.embedUnitary uLoId * rHi16.embedUnitary uHiId).1 *ᵥ basisState 0) g +
        ((v2R g - v3R g : ℝ) : ℂ)) +
      (((v3R g - v4R g : ℝ) : ℂ) + ((v4R g - wTgtR g : ℝ) : ℂ))
    rw [h2g]; push_cast; ring
  rw [hdecomp]
  refine (twoGear_norm4_add_le d1 d2 d3 d4).trans (le_trans ?_ (twoGear_budR_div_le hbudTot))
  dsimp only [d1, d2, d3, d4]
  have heq :
      (((nlHi + nlLo) * dRzLeafNum : ℕ) : ℝ) / S + (eHiNum : ℝ) / S +
        (2 * ((eLo0Num + eLo1Num : ℕ) : ℝ)) / S + (1024 : ℝ) / S =
      (((nlHi + nlLo) * dRzLeafNum + eHiNum + 2 * (eLo0Num + eLo1Num) + 1024 : ℕ) : ℝ) / S := by
    push_cast; ring
  exact (add_le_add (add_le_add (add_le_add hPiece1 hPiece2) hPiece3) hPiece4).trans_eq heq

/-- Construct a zero-ancilla `TwoGearWindowSpec d.M d.mLow 0` from a verified
`TwoGearRegimeData` record without dependent `subst`, keeping `.tWin = d.tWin` and
`.δWin = 5 / 10 ^ 9` definitional (`rfl`). -/
noncomputable def mkTwoGearWindowSpec_zeroAnc (d : TwoGearRegimeData)
    (hok : checkTwoGearRegime d = true)
    (hDlo : 2 ^ (16 - d.mLow - 1) ≤ (d.M + 1) / 2 ^ d.mLow - 1) :
    TwoGearWindowSpec d.M d.mLow 0 :=
  let hm := checkTwoGearRegime_meta d hok
  let hs := checkTwoGearRegime_sound d hok
  { hdiv := hm.1
    hDlo := hDlo
    hM1 := hm.2.1
    hMlt := hm.2.2.1
    hmLow2 := hm.2.2.2.1
    hmLow14 := hm.2.2.2.2
    hDirty := Nat.zero_le _
    tWin := d.tWin
    δWin := 5 / 10 ^ 9
    hδ_nonneg := by positivity
    cWinHi := twoGearZeroAncHi d
    cWinLo := twoGearZeroAncLo d (by have := hm.2.2.2.1; omega)
    uIdeal := idealSineWindowUnitary16 d.M hm.2.1 hm.2.2.1
    count_hi_toff := hs.1
    count_lo_toff := hs.2.1
    count_t := hs.2.2.1
    ideal_mulVec_zero := idealSineWindowUnitary16_mulVec_zero d.M hm.2.1 hm.2.2.1
    vec_err_le := by
      rw [idealSineWindowUnitary16_mulVec_zero d.M hm.2.1 hm.2.2.1]
      exact hs.2.2.2 }

/-- Computable circuit-only projection of `TwoGearWindowSpec` (`0` `Unitary` / `ℝ` fields). -/
structure TwoGearWindowCirc (mLow nDirtyLo : ℕ) where
  /-- High-gear + bond-wire preparation circuit on `nDirtyLo + (16 - mLow + 1)` wires. -/
  cWinHi : Circuit (nDirtyLo + (16 - mLow + 1))
  /-- Low-gear window preparation circuit on `mLow` wires. -/
  cWinLo : Circuit mLow

/-- Projects `w : TwoGearWindowSpec M mLow nDirtyLo` to `TwoGearWindowCirc`. -/
def TwoGearWindowSpec.toCirc {M mLow nDirtyLo : ℕ}
    (w : TwoGearWindowSpec M mLow nDirtyLo) : TwoGearWindowCirc mLow nDirtyLo :=
  ⟨w.cWinHi, w.cWinLo⟩

/-! ### Section 2b: Certified Zero-Ancilla Two-Gear Sine Windows (`δWin = 5 / 10 ^ 9`) -/

/-- Empty Walsh-tree node constructor (`WordPairTree.skip`). -/
@[noinline] def wSk : WordPairTree := .skip

/-- Binary Walsh-tree branch constructor (`WordPairTree.branch`). -/
@[noinline] def wBr : WordPairTree → WordPairTree → WordPairTree := .branch

/-- Expand `cnt` reverse-ordered `TH`/`TSH` bits onto octal stream `acc` in strict WHNF. -/
def expandTH : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | k + 1, m, acc =>
      OuterWeights.SineWindowPrep.withForcedNat (Nat.div m 2) fun m' ↦
      Bool.casesOn (Nat.beq (Nat.mod m 2) 0)
        (OuterWeights.SineWindowPrep.withForcedNat (Nat.add (Nat.mul acc 512) 229) fun acc' ↦
          expandTH k m' acc')
        (OuterWeights.SineWindowPrep.withForcedNat (Nat.add (Nat.mul acc 64) 29) fun acc' ↦
          expandTH k m' acc')

/-- Prepend up to `fuel` reverse-ordered octal digits from `pre` onto `acc` in WHNF. -/
def prependOct : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | k + 1, pre, acc =>
      Bool.casesOn (Nat.beq pre 0)
        (OuterWeights.SineWindowPrep.withForcedNat (Nat.div pre 8) fun pre' ↦
          withForcedNat (Nat.add (Nat.mod pre 8) (Nat.mul acc 8)) fun acc' ↦
            prependOct k pre' acc')
        acc

/-- Slice `big` into `60`-bit SWAR words (`< 2 ^ 60`) in CPS WHNF. -/
def sliceChunks60CPS : ℕ → ℕ → (List ℕ → WordPairTree) → WordPairTree
  | 0, _, k => k []
  | fuel + 1, big, k =>
      Bool.casesOn (Nat.beq big 0)
        (OuterWeights.SineWindowPrep.withForcedNat (Nat.mod big 0x1000000000000000) fun w ↦
          OuterWeights.SineWindowPrep.withForcedNat (Nat.div big 0x1000000000000000) fun big' ↦
            sliceChunks60CPS fuel big' fun ws ↦ k (w :: ws))
        (k [])

/-- Reconstruct a Walsh-tree leaf from `(pn, pm)` and `TH`/`TSH` syllable stream in WHNF. -/
def rPk (pn : Bool) (pm revPre cnt revMask sufCode : ℕ) : WordPairTree :=
  OuterWeights.SineWindowPrep.withForcedNat (Nat.mul pm pm) fun p2 ↦
  OuterWeights.SineWindowPrep.withForcedNat (Nat.add weierQ2 p2) fun den ↦
  OuterWeights.SineWindowPrep.withForcedNat (Nat.mul 2 den) fun den2 ↦
  OuterWeights.SineWindowPrep.withForcedNat
    (Nat.div (Nat.add (Nat.mul (Nat.mul 2 (Nat.sub weierQ2 p2))
      OuterWeights.SineWindowPrep.scale24) den) den2) fun cm ↦
  OuterWeights.SineWindowPrep.withForcedNat
    (Nat.div (Nat.add (Nat.mul (Nat.mul 2 (Nat.mul pm twoWeierQ))
      OuterWeights.SineWindowPrep.scale24) den) den2) fun sm ↦
  OuterWeights.SineWindowPrep.withForcedNat (expandTH cnt revMask sufCode) fun big1 ↦
  OuterWeights.SineWindowPrep.withForcedNat (prependOct 20 revPre big1) fun big2 ↦
  sliceChunks60CPS 20 big2 fun ch ↦
    .leaf ch ⟨pn, pm⟩ ⟨false, cm⟩ ⟨pn, sm⟩

/-- Zero-angle Walsh-tree leaf (`p = 0`, `cMid = 10 ^ 24`, `sMid = 0`). -/
@[noinline] def wP0 : WordPairTree := rPk false 0 0 0 0 0

/-- Nonnegative `TH`/`TSH` Walsh-tree leaf constructor. -/
@[noinline] def rP (pm pre cnt m suf : ℕ) : WordPairTree := rPk false pm pre cnt m suf

/-- Negative `TH`/`TSH` Walsh-tree leaf constructor. -/
@[noinline] def rN (pm pre cnt m suf : ℕ) : WordPairTree := rPk true pm pre cnt m suf

attribute [irreducible] Swar192.swarW192 Swar192.swarW192_2 Swar192.swarW192_3
  Swar192.swarOnes192 Swar192.withUnpack4SWAR192 Swar192.rot1SWAR192 Swar192.rot2SWAR192
  Swar192.rot3SWAR192 Swar192.pack4_192 expandTH prependOct sliceChunks60CPS rPk wP0 rP rN

/-! ## Section 3: Two-Gear QPE Program, Stage-A Wire Relocation & Top-Level QHL Bridge -/

/-- Persistent ancilla count of the two-gear QPE program (`StageB` peak width). -/
abbrev combAncillasB (wOuter wInner2 ko km sRem : ℕ) : ℕ :=
  combAncillas wOuter wInner2 ko km 0 sRem

/-- Persistent total local qubit count of the two-gear QPE program (`StageB` peak width). -/
abbrev combQubitsB (wOuter wInner2 ko km sRem : ℕ) : ℕ :=
  combQubits wOuter wInner2 ko km 0 sRem

/-- Parametric `bQPE` local qubit count for `StageA` (`bQPE = 16 - mLow`) and `StageB`
(`bQPE = 16`). -/
abbrev combQubitsAt (bQPE wOuter wInner2 ko km mLow s : ℕ) : ℕ :=
  cat11TotalQubits bQPE (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) s

/-- Parametric `bQPE` `(walk, cat)` register inside `combQubitsAt`. -/
abbrev combWalkCatRegAt (bQPE wOuter wInner2 ko km mLow s : ℕ) :
    QRegister (nUB wOuter wInner2 + 11) (combQubitsAt bQPE wOuter wInner2 ko km mLow s) :=
  rWalkCatLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) s

/-- Parametric `bQPE` `s`-wire scratch register inside `combQubitsAt`. -/
abbrev combScrUbRegAt (bQPE wOuter wInner2 ko km mLow s : ℕ) :
    QRegister s (combQubitsAt bQPE wOuter wInner2 ko km mLow s) :=
  rScrUbLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) s

/-- Parametric `bQPE` clean two-reflection realization contract on
`(combWalkCatRegAt, rFullZeroLoc)`. -/
abbrev CleanWalkRefl2At {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE wOuter wInner2 kZeroOut kZeroMid mLow sUb : ℕ) (hkOut : kZeroOut ≤ wOuter)
    (hkMid : kZeroMid ≤ wInner2)
    (v : Var) (uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2)))
    (pRefl2 : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 kZeroOut kZeroMid mLow sUb)) :
    Prop :=
  QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.CleanRealizes v
    (combWalkCatRegAt bQPE wOuter wInner2 kZeroOut kZeroMid mLow sUb)
    (rFullZeroLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
      (combARem wOuter wInner2 kZeroOut kZeroMid) (midRemWidth wInner2 kZeroMid) sUb
      (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
        (outZeroPrefixReg wOuter kZeroOut hkOut) (midZeroPrefixReg wInner2 kZeroMid hkMid)))
    uRefl2 pRefl2

/-- Invariant-subspace catalytic `L²` double-reflection error bound along any walk-state predicate
`P_inv` containing `(rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)` and closed under ideal
`R₁ = reflInUnitary` and ideal `R₂ = reflPulledUnitary`. -/
noncomputable def WalkRefl2InvErrLe (wOuter wInner2 : ℕ) (uB : Unitary (2 ^ nUB wOuter wInner2))
    (uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))) (δStep : ℝ) : Prop :=
  ∃ P_inv : (Fin (2 ^ nUB wOuter wInner2) → ℂ) → Prop,
    (∀ ψ : Fin (2 ^ (2 * 58)) → ℂ,
      P_inv ((rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1))) ∧
    (∀ v, P_inv v →
      P_inv ((QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))).1 *ᵥ v)) ∧
    (∀ v, P_inv v →
      P_inv ((QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB).1 *ᵥ
        v)) ∧
    (∀ v, P_inv v →
      ‖WithLp.toLp 2
          (uRefl2.1 *ᵥ tensorWalkCat v (CircuitModular.phaseGradientLowFactor 11 3) -
            tensorWalkCat
              ((QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB).1
                *ᵥ v)
              (CircuitModular.phaseGradientLowFactor 11 3))‖ ≤
        δStep * ‖WithLp.toLp 2 (tensorWalkCat v (CircuitModular.phaseGradientLowFactor 11 3))‖)

theorem walkCtrlTCount_mono (bAct M aRem : ℕ) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    walkCtrlTCount bAct M aRem t₁ ≤ walkCtrlTCount bAct M aRem t₂ := by
  dsimp only [walkCtrlTCount]
  have hm : M * t₁ ≤ M * t₂ := Nat.mul_le_mul_left M ht
  omega

theorem combAncillasB_eq (wOuter wInner2 ko km sRem : ℕ) (hs : wOuter + wInner2 + 30 ≤ sRem) :
    combAncillasB wOuter wInner2 ko km sRem = 42 + wOuter + wInner2 + sRem := by
  have hscr : scrAncillas 16 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem =
      sRem := by
    refine Nat.max_eq_left (max_le ?_ ?_)
    · dsimp [midRemWidth, blockRemWidth, mMidUB]; omega
    · dsimp [chunkedCtrlScrNeed, combARem, outRemWidth, midRemWidth, blockRemWidth,
        mOutUB, mMidUB]; omega
  dsimp [combAncillasB, combAncillas, cat11TotalAncillas, totalAncillas, actAncillas,
    walkAncillas, mOutUB, mMidUB]
  omega

@[simp] theorem combARem_9_10_5_6 : combARem 9 10 5 6 = 23 := rfl
@[simp] theorem combARem_8_10_4_6 : combARem 8 10 4 6 = 23 := rfl

@[simp]
theorem combAncillasB_9_10_eq (ko km sRem : ℕ) (hs : 49 ≤ sRem := by decide) :
    combAncillasB 9 10 ko km sRem = 61 + sRem := by
  simpa using combAncillasB_eq 9 10 ko km sRem (by omega)

@[simp]
theorem combAncillasB_8_10_eq (ko km sRem : ℕ) (hs : 48 ≤ sRem := by decide) :
    combAncillasB 8 10 ko km sRem = 60 + sRem := by
  simpa using combAncillasB_eq 8 10 ko km sRem (by omega)

@[simp] theorem combARem_8_20_8_16 : combARem 8 20 8 16 = 19 := rfl
@[simp] theorem combARem_1_20_1_16 : combARem 1 20 1 16 = 19 := rfl
@[simp] theorem combARem_1_20_0_16 : combARem 1 20 0 16 = 20 := rfl

@[simp]
theorem combAncillasB_8_20_eq (ko km sRem : ℕ) (hs : 58 ≤ sRem := by decide) :
    combAncillasB 8 20 ko km sRem = 70 + sRem := by
  simpa using combAncillasB_eq 8 20 ko km sRem (by omega)

@[simp]
theorem combAncillasB_1_20_eq (ko km sRem : ℕ) (hs : 51 ≤ sRem := by decide) :
    combAncillasB 1 20 ko km sRem = 63 + sRem := by
  simpa using combAncillasB_eq 1 20 ko km sRem (by omega)

theorem two_pow_15_add_le_of_dvd {M mLow : ℕ} (hmLow15 : mLow ≤ 15)
    (hMlo : 2 ^ 15 ≤ M) (hdvd : 2 ^ mLow ∣ M + 1) :
    2 ^ 15 + 2 ^ mLow ≤ M + 1 := by
  obtain ⟨k, hk⟩ := hdvd
  have h15 : 2 ^ 15 = 2 ^ mLow * 2 ^ (15 - mLow) := by
    rw [← pow_add]; congr 1; omega
  have hlt : 2 ^ mLow * 2 ^ (15 - mLow) < 2 ^ mLow * k := by
    rw [← h15, ← hk]; omega
  have hk_gt : 2 ^ (15 - mLow) < k :=
    (Nat.mul_lt_mul_left (Nat.two_pow_pos mLow)).mp hlt
  calc 2 ^ 15 + 2 ^ mLow
      = 2 ^ mLow * (2 ^ (15 - mLow) + 1) := by rw [h15]; ring
    _ ≤ 2 ^ mLow * k := Nat.mul_le_mul_left _ (by omega)
    _ = M + 1 := hk.symm

/-! ### Stage-A Wire Embedding `rStageAInB` & Clean-Workspace Absorption -/

theorem hbScr_phaseB (wOuter wInner2 ko km mLow sRem : ℕ) (hmLow16 : mLow ≤ 16) :
    mLow - 2 ≤ scrAncillas 16 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem := by
  have h3 : chunkedCtrlScrNeed 16 0 (combARem wOuter wInner2 ko km) ≤
      scrAncillas 16 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine le_trans ?_ h3
  dsimp [chunkedCtrlScrNeed, combARem, outRemWidth, midRemWidth, blockRemWidth, mOutUB, mMidUB]
  omega

/-- High `(16 - mLow)`-bit QPE subregister `mLow .. 15` inside `16`-bit QPE. -/
abbrev rHiInQPE16 (mLow : ℕ) (hmLow16 : mLow ≤ 16) : QRegister (16 - mLow) 16 :=
  .block mLow (16 - mLow) (by omega)

/-- Low `mLow`-bit QPE subregister `0 .. mLow - 1` inside `16`-bit QPE. -/
abbrev rLoInQPE16 (mLow : ℕ) (hmLow16 : mLow ≤ 16) : QRegister mLow 16 :=
  .block 0 mLow (by omega)

/-- Borrowed `(mLow - 1 - nDirtyLo)`-wire QPE subregister `nDirtyLo .. mLow - 2` inside `16`-bit
QPE, which stays in exact `|0⟩` throughout `pPart1`. -/
abbrev rBorrowInQPE16 (mLow nDirtyLo : ℕ)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1) :
    QRegister (mLow - 1 - nDirtyLo) 16 :=
  .block nDirtyLo (mLow - 1 - nDirtyLo) (by omega)

theorem rHiInAct_disjoint_rWalkCatInAct (mOut mMid mLow : ℕ) (hmLow16 : mLow ≤ 16) :
    ((rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 mLow hmLow16)).DisjointWires
      (rWalkCatInAct 16 11 mOut mMid) :=
  QubitisedWalk.disjointWires_compose_left (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)

/-- Active `(rHi, rWalkCat)` register of `StageA` inside `actWidth 16 11 mOut mMid`. -/
abbrev rCombHiInAct (mOut mMid mLow : ℕ) (hmLow16 : mLow ≤ 16) :
    QRegister ((16 - mLow) + walkCatWidth 11 mOut mMid) (actWidth 16 11 mOut mMid) :=
  ((rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 mLow hmLow16)).concat
    (rWalkCatInAct 16 11 mOut mMid) (rHiInAct_disjoint_rWalkCatInAct mOut mMid mLow hmLow16)

/-- Borrowed clean QPE register inside `combQubitsB`. -/
abbrev rBorrowLocB (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1) :
    QRegister (mLow - 1 - nDirtyLo) (combQubitsB wOuter wInner2 ko km sRem) :=
  (rQPELoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem).compose
    (rBorrowInQPE16 mLow nDirtyLo hmLow1 hmLow15 hDirty)

/-- Full zero-ancilla register of `StageB` inside `combQubitsB`. -/
abbrev rFullZeroLocB (wOuter wInner2 ko km sRem : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) :
    QRegister (scrAncillas 16 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem +
      (ko + km)) (combQubitsB wOuter wInner2 ko km sRem) :=
  rFullZeroLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem
    (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
      (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid))

theorem rFullZeroLocB_disjoint_rBorrowLocB (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1) :
    (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid).DisjointWires
      (rBorrowLocB wOuter wInner2 ko km mLow nDirtyLo sRem hmLow1 hmLow15 hDirty) := by
  let mOut := mOutUB wOuter; let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km; let mRem := midRemWidth wInner2 km
  let rAncZ := liftOutMidZeroToAnc mOut mMid
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hi : (rFullZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ i) ∈
      (rFullZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ).image :=
    (QRegister.mem_image _ _).mpr ⟨i, rfl⟩
  rw [image_rFullZeroLoc, Finset.mem_union] at hi
  rcases hi with hscr | hanc
  · obtain ⟨is, his⟩ := (QRegister.mem_image _ _).mp hscr
    exact (QubitisedWalk.disjointWires_compose_left
      (rQPELoc_disjoint_rScrLoc 16 11 mOut mMid 0 aRem mRem sRem)).ne j is
      (hij.symm.trans his.symm)
  · obtain ⟨ia, hia⟩ := (QRegister.mem_image _ _).mp hanc
    exact (QubitisedWalk.disjointWires_compose_left
      (QubitisedWalk.disjointWires_compose_right
        (QubitisedWalk.disjointWires_compose_right
          (rQPELoc_disjoint_rWalkCatLoc 16 11 mOut mMid 0 aRem mRem sRem)))).ne j ia
      (hij.symm.trans hia.symm)

/-- Extended clean-zero register for `pPart1`: `rFullZeroLocB ++ rBorrowLocB`. -/
abbrev rExtZeroLocB (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1) :
    QRegister ((scrAncillas 16 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem +
      (ko + km)) + (mLow - 1 - nDirtyLo)) (combQubitsB wOuter wInner2 ko km sRem) :=
  (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid).concat
    (rBorrowLocB wOuter wInner2 ko km mLow nDirtyLo sRem hmLow1 hmLow15 hDirty)
    (rFullZeroLocB_disjoint_rBorrowLocB wOuter wInner2 ko km mLow nDirtyLo sRem
      hkOut hkMid hmLow1 hmLow15 hDirty)

theorem wp_compile_zero {Var : Type} [Finite Var] [DecidableEq Var] {N : ℕ}
    (P : DynamicCircuit Var N) :
    wp P.compile (0 : QCAssertion Var (2 ^ N)) = 0 := by
  have := Fintype.ofFinite Var
  induction P using DynamicCircuit.qcInd with
  | circuit c =>
      funext σ; apply Subtype.ext
      simp [qcWpQAssign, qcQAssignObsMap]
  | measure v r =>
      funext σ; apply Subtype.ext
      simp [DynamicCircuit.compile_measure, QProg.measureRegister,
        qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe, qc_qMeasure_outcome_herm_eq_conj,
        QCAssertion.subst_apply]
  | qIf cond t f iht ihf =>
      funext σ
      simp only [DynamicCircuit.compile_qcRawQIf, wp_qcRawQIf]
      by_cases hc : cond.holds σ <;> simp [hc, iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.compile_seq, wp_qSeq, ih₂, ih₁]

theorem cleanRealizes_preserves_zeroProj {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : XMeasCircuit.CleanRealizes v rAct rScr U P) :
    rScr.basisOutcomeProjector 0 * ((rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0) =
      (rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0 := by
  let P₀ : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ := rScr.basisOutcomeProjector 0
  let W : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ := (rAct.embedUnitary U).1
  let Θ : QCAssertion Var (2 ^ N) := fun _ ↦ XMeasCircuit.CleanRealizes.dirtyObservable rScr
  have hP₀_herm : P₀ᴴ = P₀ := rScr.basisOutcomeProjector_conjTranspose 0
  have hP₀_idem : P₀ * P₀ = P₀ := rScr.basisOutcomeProjector_mul_self 0
  have heq : restrictAssertionToZeroAncilla
      (qcWpQAssign (rAct.embedUnitary U) (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr := by
    rw [← h.wp_clean (restrictAssertionToZeroAncilla Θ rScr) (fun _ _ ↦ rfl), h.wp_clean_post Θ,
      h.wp_clean Θ (fun _ _ ↦ rfl)]
  have hmat := congrArg (fun A : QCAssertion Var (2 ^ N) ↦ (A (fun _ ↦ 0)).1.mat) heq
  simp only [Θ, restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    HermitianMat.conj_apply_mat, XMeasCircuit.CleanRealizes.dirtyObservable_mat] at hmat
  change P₀ * (Wᴴ * (P₀ * (1 - P₀) * P₀ᴴ) * Wᴴᴴ) * P₀ᴴ =
    P₀ * (Wᴴ * (1 - P₀) * Wᴴᴴ) * P₀ᴴ at hmat
  rw [hP₀_herm, Matrix.conjTranspose_conjTranspose] at hmat
  have hmid0 : P₀ * (1 - P₀) * P₀ = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP₀_idem, sub_self, Matrix.zero_mul]
  rw [hmid0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul] at hmat
  have hmat0 : P₀ * (Wᴴ * (1 - P₀) * W) * P₀ = 0 := hmat.symm
  let B : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ := (1 - P₀) * W * P₀
  have hBsq : Bᴴ * B = 0 := by
    dsimp only [B]
    calc ((1 - P₀) * W * P₀)ᴴ * ((1 - P₀) * W * P₀)
        = P₀ * (Wᴴ * ((1 - P₀) * (1 - P₀)) * W) * P₀ := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
              Matrix.conjTranspose_one, hP₀_herm, Matrix.mul_assoc]
      _ = P₀ * (Wᴴ * (1 - P₀) * W) * P₀ := by
            have hid : (1 - P₀) * (1 - P₀) = 1 - P₀ := by
              simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
                hP₀_idem, sub_self, sub_zero]
            rw [hid]
      _ = 0 := hmat0
  have hB0 : B = 0 := by
    ext i j
    have hdiag : (Bᴴ * B) j j = 0 := by rw [hBsq]; rfl
    have hre : ∑ l : Fin (2 ^ N), Complex.normSq (B l j) = 0 := by
      have hs : (∑ l : Fin (2 ^ N), (Complex.normSq (B l j) : ℂ)) = 0 := by
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
          Complex.normSq_eq_conj_mul_self] using hdiag
      exact_mod_cast hs
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun l _ ↦ Complex.normSq_nonneg _).mp hre i
        (Finset.mem_univ i))
  have hsub : W * P₀ - P₀ * (W * P₀) = 0 := by
    simpa only [B, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc] using hB0
  exact (sub_eq_zero.mp hsub).symm

/-! ### Stage-A Super-Step, Local Two-Part Program & Top-Level QHL Realization -/

/-- Local `StageB` affine-folded dihedral walk on `combQubitsB`. -/
def twoGearPhaseBDyn {Var : Type}
    (wOuter wInner2 ko km mLow sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (v : Var)
    (pRefl2B : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  affineDihedralRefl2Dyn 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 sRem v
    (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid)
    mLow (2 ^ mLow - 1) hmLow1 (by omega)
    (hbScr_phaseB wOuter wInner2 ko km mLow sRem (by omega)) pRefl2B

/-- Blocked-basis Part 2 (`cWinLo ; StageB ; cIqft`), keeping `rFullZeroLocB` clean. -/
def twoGearBlockedPart2Prog {Var : Type}
    (wOuter wInner2 ko km M mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15)
    (v : Var) (cIqft : Circuit 16) (w : TwoGearWindowSpec M mLow nDirtyLo)
    (pRefl2B : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  let mOut := mOutUB wOuter; let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km; let mRem := midRemWidth wInner2 km
  let rQPE := rQPELoc 16 11 mOut mMid 0 aRem mRem sRem
  let rWinLo := rQPE.compose (rLoInQPE16 mLow (by omega))
  .seq (.circuit (w.cWinLo.onRegister rWinLo))
    (.seq (twoGearPhaseBDyn wOuter wInner2 ko km mLow sRem hkOut hkMid hmLow1 hmLow15 v pRefl2B)
      (.circuit (cIqft.onRegister rQPE)))

/-- Computable blocked-basis Part 2 (`wc.cWinLo, StageB, cIqft`) from `TwoGearWindowCirc`. -/
def twoGearBlockedPart2CircProg {Var : Type}
    (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15)
    (v : Var) (cIqft : Circuit 16) (wc : TwoGearWindowCirc mLow nDirtyLo)
    (pRefl2B : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  let rQPE := rQPELoc 16 11 mOut mMid 0 aRem mRem sRem
  let rWinLo := rQPE.compose (rLoInQPE16 mLow (by omega))
  .seq (.circuit (wc.cWinLo.onRegister rWinLo))
    (.seq (twoGearPhaseBDyn wOuter wInner2 ko km mLow sRem hkOut hkMid hmLow1 hmLow15 v pRefl2B)
      (.circuit (cIqft.onRegister rQPE)))

/-! ### Clean-Realization of `Part1` (`rExtZeroLocB`), `Part2` (`rFullZeroLocB`), and Top QHL -/

theorem tgAbsorbCleanActive_of_comm {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₁ s₂ : ℕ} {v : Var} {rAct : QRegister k N}
    {rScr : QRegister s₁ N} {rFull : QRegister s₂ N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hbase : CleanDyn.CleanRealizes v rAct rScr U P)
    (hsub : rScr.image ⊆ rFull.image)
    (hcomm : (rAct.embedUnitary U).1 * rFull.basisOutcomeProjector 0 =
      rFull.basisOutcomeProjector 0 * (rAct.embedUnitary U).1) :
    XMeasCircuit.CleanRealizes v rAct rFull U P := by
  refine XMeasCircuit.CleanRealizes.absorbCleanActive hbase hsub rfl ?_
  change rFull.basisOutcomeProjector 0 *
      ((rAct.embedUnitary U).1 * rFull.basisOutcomeProjector 0) = _
  rw [hcomm, ← Matrix.mul_assoc, rFull.basisOutcomeProjector_mul_self 0]

theorem tgSubAct_disjoint_rFullZeroLoc
    (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero k : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid))
    (sub : QRegister k (actWidth bQPE bCat mOut mMid))
    (hsub_wires : ∀ j : Fin k, (sub j).val < systemQubits_local ∨
      walkWidth mOut mMid ≤ (sub j).val) :
    ((rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose sub).DisjointWires
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) := by
  rw [QRegister.disjoint_iff]
  intro j q heq
  rcases Comparators.fin_eq_castAdd_or_natAdd q with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [QRegister.concat_apply_left] at heq
    exact (QubitisedWalk.disjointWires_compose_left
      (rActLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)).ne j p heq
  · rw [QRegister.concat_apply_right] at heq
    have hb := rAncZeroLoc_val_bounds bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero p
    have hv : (sub j).val =
        (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero p).val := by
      simpa only [rActLoc, QRegister.compose_apply, QRegister.block_apply_val, zero_add]
        using congrArg Fin.val heq
    rcases hsub_wires j with hlt | hge <;> omega

theorem tgCleanRealizes_subcircuit {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) (v : Var) {kZero k : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid))
    (sub : QRegister k (actWidth bQPE bCat mOut mMid))
    (hsub_wires : ∀ j : Fin k, (sub j).val < systemQubits_local ∨
      walkWidth mOut mMid ≤ (sub j).val)
    (c : Circuit k) (hc : c.count .TOFF = 0) :
    XMeasCircuit.CleanRealizes v (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) (sub.embedUnitary c.eval)
      (.circuit
        (c.onRegister ((rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose sub))) := by
  have hbase := CoherentAlias.cleanRealizes_subcircuit v
    (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb) sub
    (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    (rActLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb) c hc
  refine tgAbsorbCleanActive_of_comm hbase
    (by rw [image_rFullZeroLoc]; exact Finset.subset_union_left) ?_
  rw [← QRegister.embedUnitary_compose]
  exact (QubitisedWalk.basisOutcomeProjector_comm_embedMatrix _ _
    (QRegister.disjoint_comm.mp
      (tgSubAct_disjoint_rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb
        rAncZero sub hsub_wires)) 0 c.eval.1).symm

theorem cleanRealizes_subcircuit_rExtZeroB {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1)
    (v : Var) {k : ℕ} (sub : QRegister k (actWidth 16 11 (mOutUB wOuter) (mMidUB wInner2)))
    (hsub : ∀ j : Fin k,
      let q := (sub j).val
      q < systemQubits_local ∨
      (walkWidth (mOutUB wOuter) (mMidUB wInner2) ≤ q ∧
        (q < walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2) + nDirtyLo ∨
          walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2) + (mLow - 1) ≤ q)))
    (c : Circuit k) (hc0 : c.count .TOFF = 0) :
    let rAct := rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
      (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.CleanRealizes v rAct
      (rExtZeroLocB wOuter wInner2 ko km mLow nDirtyLo sRem hkOut hkMid hmLow1 hmLow15 hDirty)
      (sub.embedUnitary c.eval) (.circuit (c.onRegister (rAct.compose sub))) := by
  intro rAct
  let mOut := mOutUB wOuter; let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km; let mRem := midRemWidth wInner2 km
  let rAncZ := liftOutMidZeroToAnc mOut mMid
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  let rScr := rScrLoc 16 11 mOut mMid 0 aRem mRem sRem
  let rExt := rExtZeroLocB wOuter wInner2 ko km mLow nDirtyLo sRem hkOut hkMid hmLow1 hmLow15 hDirty
  have hbase := CoherentAlias.cleanRealizes_subcircuit v rAct sub rScr
    (rActLoc_disjoint_rScrLoc 16 11 mOut mMid 0 aRem mRem sRem) c hc0
  have hscr_sub : rScr.image ⊆ rExt.image := by
    intro q hq
    have hmem : q ∈ (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid).image := by
      rw [rFullZeroLocB, image_rFullZeroLoc, Finset.mem_union]
      exact Or.inl hq
    obtain ⟨ifull, rfl⟩ := (QRegister.mem_image _ _).mp hmem
    exact (QRegister.mem_image rExt _).mpr ⟨Fin.castAdd _ ifull,
      QRegister.concat_apply_left _ _ _ ifull⟩
  have hdisj : (rAct.compose sub).DisjointWires rExt := by
    rw [QRegister.disjoint_iff]
    intro j iext hext
    have hj := hsub j
    have hq_lt : (sub j).val < actWidth 16 11 mOut mMid := (sub j).isLt
    have hq_val : (rAct.compose sub j).val = (sub j).val := by
      simp only [rAct, rActLoc, QRegister.compose_apply, QRegister.block_apply_val, zero_add]
    rcases finSumFinEquiv.surjective iext with ⟨ifull | ibor, rfl⟩
    · simp only [finSumFinEquiv_apply_left, rExt, rExtZeroLocB, QRegister.concat_apply_left] at hext
      have hmem : rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid ifull ∈
          (rFullZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ).image :=
        (QRegister.mem_image _ _).mpr ⟨ifull, rfl⟩
      rw [image_rFullZeroLoc, Finset.mem_union] at hmem
      rcases hmem with hscr | hanc
      · obtain ⟨is, his⟩ := (QRegister.mem_image _ _).mp hscr
        have hv := congrArg Fin.val (hext.trans his.symm)
        simp only [hq_val, rScrLoc, QRegister.block_apply_val] at hv
        omega
      · obtain ⟨ia, hia⟩ := (QRegister.mem_image _ _).mp hanc
        have hbnd := rAncZeroLoc_val_bounds 16 11 mOut mMid 0 aRem mRem sRem rAncZ ia
        have hv := congrArg Fin.val (hext.trans hia.symm)
        rw [hq_val] at hv
        dsimp only [mOut, mMid, aRem, mRem, walkCatWidth, walkWidth] at hbnd hj hv
        omega
    · have := ibor.isLt
      simp only [finSumFinEquiv_apply_right, rExt, rExtZeroLocB, QRegister.concat_apply_right]
        at hext
      have hv := congrArg Fin.val hext
      rw [hq_val] at hv
      simp only [rBorrowLocB, rQPELoc, rActLoc, rQPEInAct, rBorrowInQPE16,
        QRegister.compose_apply, QRegister.block_apply_val, zero_add] at hv
      dsimp only [mOut, mMid, walkCatWidth, walkWidth] at hj hv
      omega
  refine tgAbsorbCleanActive_of_comm hbase hscr_sub ?_
  rw [← QRegister.embedUnitary_compose]
  exact (QubitisedWalk.basisOutcomeProjector_comm_embedMatrix _ _
    (QRegister.disjoint_comm.mp hdisj) 0 c.eval.1).symm

theorem twoGearBlockedPart2Prog_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 ko km M mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15)
    (v : Var) (cIqft : Circuit 16) (hIqftToff : cIqft.count .TOFF = 0)
    (w : TwoGearWindowSpec M mLow nDirtyLo)
    {uRefl2B : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    {pRefl2B : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)}
    (hCleanB : CleanWalkRefl2 wOuter wInner2 ko km 0 sRem hkOut hkMid v uRefl2B pRefl2B) :
    let mOut := mOutUB wOuter; let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km; let mRem := midRemWidth wInner2 km
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
    let uMuxB := QubitisedWalk.qpeMuxUnitary
      (affineScheduleFiber mLow (2 ^ mLow - 1) (R₁c * uRefl2B) R₁c)
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rCombFull := rQPE.concat (rWalkCatInAct 16 11 mOut mMid)
      (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.CleanRealizes v
      (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid)
      (rQPE.embedUnitary cIqft.eval *
        rCombFull.embedUnitary uMuxB *
        (rQPE.compose (rLoInQPE16 mLow (by omega))).embedUnitary w.cWinLo.eval)
      (twoGearBlockedPart2Prog wOuter wInner2 ko km M mLow nDirtyLo sRem hkOut hkMid
        hmLow1 hmLow15 v cIqft w pRefl2B) := by
  intro mOut mMid aRem mRem R₁c uMuxB rQPE rCombFull
  let rAncZ := liftOutMidZeroToAnc mOut mMid
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  have hWinLo_raw := tgCleanRealizes_subcircuit 16 11 mOut mMid 0 aRem mRem sRem v rAncZ
    (rQPE.compose (rLoInQPE16 mLow (by omega)))
    (fun j ↦ Or.inr (by
      simp only [rQPE, rQPEInAct, rLoInQPE16, QRegister.compose_apply, QRegister.block_apply_val]
      dsimp only [walkCatWidth]; omega))
    w.cWinLo w.count_lo_toff
  have hWinLo : XMeasCircuit.CleanRealizes v
      (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid)
      ((rQPE.compose (rLoInQPE16 mLow (by omega))).embedUnitary w.cWinLo.eval)
      (.circuit (w.cWinLo.onRegister
        ((rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose (rLoInQPE16 mLow (by omega))))) := by
    have hr : (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
        (rQPE.compose (rLoInQPE16 mLow (by omega))) =
      (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose (rLoInQPE16 mLow (by omega)) := by
      ext i; rfl
    exact hr ▸ hWinLo_raw
  have hMB_lo : 2 ^ (mLow - 1) ≤ 2 ^ mLow - 1 := by
    have hm1 : mLow = (mLow - 1) + 1 := by omega
    have hpos : 1 ≤ 2 ^ (mLow - 1) := Nat.one_le_two_pow
    conv_rhs => rw [hm1, pow_succ]
    omega
  have hCovB := combWalkReflCovers 16 11 wOuter wInner2 0 sRem ko km hkOut hkMid
  have hPhaseB_sub := affineDihedralRefl2Dyn_cleanRealizes 16 11 mOut mMid 0 sRem v hCovB
    mLow (2 ^ mLow - 1) hmLow1 (by omega) hMB_lo
    (hbScr_phaseB wOuter wInner2 ko km mLow sRem (by omega)) hCleanB
  have hComb_eq : ((rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).concat
      (rWalkCatLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rQPELoc_disjoint_rWalkCatLoc 16 11 mOut mMid 0 aRem mRem sRem)) =
    (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose rCombFull := by
    ext idx
    dsimp only [rCombFull, rQPE]
    rcases finSumFinEquiv.surjective idx with ⟨iq | iw, rfl⟩ <;>
      simp only [rQPELoc, rWalkCatLoc, QRegister.compose_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hPhaseB := XMeasCircuit.CleanRealizes.liftActiveOfEq hComb_eq hPhaseB_sub
  have hIqft := tgCleanRealizes_subcircuit 16 11 mOut mMid 0 aRem mRem sRem v rAncZ rQPE
    (fun j ↦ Or.inr (by
      simp only [rQPE, rQPEInAct, QRegister.block_apply_val]
      dsimp only [walkCatWidth]; omega))
    cIqft hIqftToff
  unfold twoGearBlockedPart2Prog twoGearPhaseBDyn
  exact (hWinLo.seq (hPhaseB.seq hIqft)).congrUnitary
    (congrArg (fun U ↦ ((rActLoc 16 11 mOut mMid 0 aRem mRem sRem).embedUnitary U).1 * _)
      (by dsimp only [uMuxB, R₁c, rCombFull, rQPE, mOut, mMid]))

theorem tgRestrictZero_basisUniv_absorb {Var : Type}
    {n ks ka ke : ℕ} [NeZero (2 ^ n)]
    {rSys : QRegister ks n} {rAnc : QRegister ka n} {rExt : QRegister ke n}
    (hsub : rExt.image ⊆ rAnc.image) (A : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla (restrictAssertionToBasisOutcomes A rSys Finset.univ) rAnc =
      restrictAssertionToZeroAncilla
        (restrictAssertionToBasisOutcomes
          (restrictAssertionToZeroAncilla A rExt) rSys Finset.univ) rAnc := by
  funext σ; apply Subtype.ext
  have huniv : rSys.basisOutcomesProjector Finset.univ = 1 := by
    simp [QRegister.basisOutcomesProjector]
  have hcomm : rSys.basisOutcomesProjector Finset.univ * rExt.basisOutcomeProjector 0 =
      rExt.basisOutcomeProjector 0 * rSys.basisOutcomesProjector Finset.univ := by
    rw [huniv, Matrix.one_mul, Matrix.mul_one]
  have hmul : rAnc.basisOutcomeProjector 0 * rExt.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 := by
    have h := congrArg conjTranspose
      (CleanDyn.basisOutcomeProjector_zero_mul_of_image_subset hsub)
    simpa only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
  have hprod : rAnc.basisOutcomeProjector 0 * rSys.basisOutcomesProjector Finset.univ *
        rExt.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 * rSys.basisOutcomesProjector Finset.univ := by
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hmul]
  simp only [restrictAssertionToZeroAncilla_coe, restrictAssertionToBasisOutcomes,
    CQAssertion.restrictToBasisOutcomes, CQAssertion.conj_apply, Observable.conj_coe,
    HermitianMat.conj_conj]
  rw [← Matrix.mul_assoc, hprod]

theorem rExtZeroLocB_emb_subset_rAnc {n : ℕ}
    (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1)
    (rSys : QRegister systemQubits_local n)
    (rAnc : QRegister (combAncillasB wOuter wInner2 ko km sRem) n)
    (hdisj : rSys.DisjointWires rAnc) :
    ((rSys.concat rAnc hdisj).compose
      (rExtZeroLocB wOuter wInner2 ko km mLow nDirtyLo sRem hkOut hkMid hmLow1 hmLow15
        hDirty)).image ⊆
      rAnc.image := by
  let rFull := rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid
  let rExt := rExtZeroLocB wOuter wInner2 ko km mLow nDirtyLo sRem hkOut hkMid hmLow1 hmLow15 hDirty
  let rExt_emb := (rSys.concat rAnc hdisj).compose rExt
  intro q hq
  obtain ⟨i, rfl⟩ := (QRegister.mem_image rExt_emb q).mp hq
  let wLoc := rExt i
  have hw_ge : systemQubits_local ≤ wLoc.val := by
    rcases finSumFinEquiv.surjective i with ⟨ifull | ibor, rfl⟩
    · have hmem : rFull ifull ∈ rFull.image := (QRegister.mem_image _ _).mpr ⟨ifull, rfl⟩
      dsimp only [rFull, rFullZeroLocB] at hmem
      rw [image_rFullZeroLoc, Finset.mem_union] at hmem
      dsimp only [wLoc, rExt]
      simp only [rExtZeroLocB, finSumFinEquiv_apply_left, QRegister.concat_apply_left]
      rcases hmem with hscr | hanc
      · obtain ⟨js, hjs⟩ := (QRegister.mem_image _ _).mp hscr
        dsimp only [rFullZeroLocB]
        rw [← hjs]
        simp only [rScrLoc, QRegister.block_apply_val]
        dsimp only [actWidth, systemQubits_local]; omega
      · obtain ⟨ja, hja⟩ := (QRegister.mem_image _ _).mp hanc
        rw [← hja]
        exact (rAncZeroLoc_val_bounds 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
          (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem _ ja).1
    · dsimp only [wLoc, rExt]
      simp only [rExtZeroLocB, finSumFinEquiv_apply_right, QRegister.concat_apply_right,
        rBorrowLocB, rQPELoc, rActLoc, rQPEInAct, rBorrowInQPE16, QRegister.compose_apply,
        QRegister.block_apply_val, zero_add]
      dsimp only [walkCatWidth, walkWidth]
      omega
  have hw_lt : wLoc.val < systemQubits_local + combAncillasB wOuter wInner2 ko km sRem := wLoc.isLt
  let idxAnc : Fin (combAncillasB wOuter wInner2 ko km sRem) :=
    ⟨wLoc.val - systemQubits_local, by omega⟩
  exact (QRegister.mem_image rAnc _).mpr ⟨idxAnc, by
    change rAnc idxAnc = (rSys.concat rAnc hdisj) (rExt i)
    have hw_eq : rExt i = Fin.natAdd systemQubits_local idxAnc := by
      ext; simp only [Fin.val_natAdd, idxAnc, wLoc]; omega
    rw [hw_eq, QRegister.concat_apply_right]⟩

/-! ## Section 4: Two-Gear Schedule Algebra, `L²` Perturbation & End-to-End Closure -/

theorem tgL2_norm_unitary_mulVec {d : ℕ} (U : Unitary d) (x : Fin d → ℂ) :
    ‖WithLp.toLp 2 (U.1 *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  have hsq : ‖WithLp.toLp 2 (U.1 *ᵥ x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa only [Complex.normSq_eq_norm_sq] using sum_normSq_unitary_mulVec U x
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem tgL2_norm_tensorWalkCat_unitary {bCat mOut mMid : ℕ}
    (U : Unitary (2 ^ walkWidth mOut mMid))
    (u : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    ‖WithLp.toLp 2 (tensorWalkCat (U.1 *ᵥ u) cat)‖ =
      ‖WithLp.toLp 2 (tensorWalkCat u cat)‖ := by
  rw [← embedMatrix_rWalkInWalkCat_mulVec]
  exact tgL2_norm_unitary_mulVec ((rWalkInWalkCat bCat mOut mMid).embedUnitary U) _

/-- Bundled invariant-subspace catalytic approximation relation: `aId` preserves `P_inv` and `aImpl`
approximates `aId ⊗ I_cat` within `L²` relative error `cA` on `P_inv ⊗ |cat⟩`. -/
noncomputable def InvCatRel {bCat mOut mMid : ℕ}
    (P_inv : (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop)
    (cat : Fin (2 ^ bCat) → ℂ)
    (aImpl : Unitary (2 ^ walkCatWidth bCat mOut mMid))
    (aId : Unitary (2 ^ walkWidth mOut mMid)) (cA : ℝ) : Prop :=
  (∀ v, P_inv v → P_inv (aId.1 *ᵥ v)) ∧
    ∀ v, P_inv v →
      ‖WithLp.toLp 2 (aImpl.1 *ᵥ tensorWalkCat v cat - tensorWalkCat (aId.1 *ᵥ v) cat)‖ ≤
        cA * ‖WithLp.toLp 2 (tensorWalkCat v cat)‖

theorem invCatRel_one {bCat mOut mMid : ℕ}
    (P_inv : (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop) (cat : Fin (2 ^ bCat) → ℂ) :
    InvCatRel P_inv cat 1 1 0 := by
  refine ⟨fun v hv ↦ ?_, fun v _ ↦ ?_⟩
  · simpa using hv
  · simp

theorem invCatRel_mul {bCat mOut mMid : ℕ}
    {P_inv : (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop} {cat : Fin (2 ^ bCat) → ℂ}
    {aImpl bImpl : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {aId bId : Unitary (2 ^ walkWidth mOut mMid)} {cA cB : ℝ}
    (hA : InvCatRel P_inv cat aImpl aId cA) (hB : InvCatRel P_inv cat bImpl bId cB) :
    InvCatRel P_inv cat (aImpl * bImpl) (aId * bId) (cA + cB) := by
  refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · change P_inv ((aId.1 * bId.1) *ᵥ v)
    rw [← Matrix.mulVec_mulVec]
    exact hA.1 _ (hB.1 v hv)
  · have hsplit :
        WithLp.toLp 2 ((aImpl * bImpl).1 *ᵥ tensorWalkCat v cat -
            tensorWalkCat ((aId * bId).1 *ᵥ v) cat) =
          WithLp.toLp 2 (aImpl.1 *ᵥ (bImpl.1 *ᵥ tensorWalkCat v cat -
            tensorWalkCat (bId.1 *ᵥ v) cat)) +
          WithLp.toLp 2 (aImpl.1 *ᵥ tensorWalkCat (bId.1 *ᵥ v) cat -
            tensorWalkCat (aId.1 *ᵥ (bId.1 *ᵥ v)) cat) := by
      ext g
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
        WithLp.ofLp_add, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hsplit]
    have hb1 : ‖WithLp.toLp 2 (aImpl.1 *ᵥ (bImpl.1 *ᵥ tensorWalkCat v cat -
        tensorWalkCat (bId.1 *ᵥ v) cat))‖ ≤ cB * ‖WithLp.toLp 2 (tensorWalkCat v cat)‖ := by
      rw [tgL2_norm_unitary_mulVec aImpl]; exact hB.2 v hv
    have hb2 : ‖WithLp.toLp 2 (aImpl.1 *ᵥ tensorWalkCat (bId.1 *ᵥ v) cat -
        tensorWalkCat (aId.1 *ᵥ (bId.1 *ᵥ v)) cat)‖ ≤
        cA * ‖WithLp.toLp 2 (tensorWalkCat v cat)‖ := by
      refine (hA.2 (bId.1 *ᵥ v) (hB.1 v hv)).trans ?_
      rw [tgL2_norm_tensorWalkCat_unitary bId]
    exact (norm_add_le _ _).trans ((add_le_add hb1 hb2).trans_eq (by ring))

theorem invCatRel_pow {bCat mOut mMid : ℕ}
    {P_inv : (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop} {cat : Fin (2 ^ bCat) → ℂ}
    {wImpl : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {wId : Unitary (2 ^ walkWidth mOut mMid)} {δ : ℝ}
    (hW : InvCatRel P_inv cat wImpl wId δ) (L : ℕ) :
    InvCatRel P_inv cat (wImpl ^ L) (wId ^ L) ((L : ℝ) * δ) := by
  induction L with
  | zero => simpa using invCatRel_one P_inv cat
  | succ L' ih =>
    rw [pow_succ, pow_succ]
    obtain ⟨hCl, hBd⟩ := invCatRel_mul ih hW
    exact ⟨hCl, fun v hv ↦ (hBd v hv).trans_eq (by push_cast; ring)⟩

theorem invCatRelChunksFiber {bQPE bCat mOut mMid : ℕ}
    {P_inv : (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop} {cat : Fin (2 ^ bCat) → ℂ}
    {wImpl rImpl : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {wId rId : Unitary (2 ^ walkWidth mOut mMid)} {δ : ℝ}
    (hR : InvCatRel P_inv cat rImpl rId 0)
    (hW : InvCatRel P_inv cat wImpl wId δ)
    (w M n : ℕ) (y : Fin (2 ^ bQPE)) :
    InvCatRel P_inv cat (chunksFiber w M wImpl rImpl n y)
      (chunksFiber w M wId rId n y)
      (((∑ j ∈ Finset.range n, chunkSize2 w M j : ℕ) : ℝ) * δ) := by
  have hChunk (pred : Fin (2 ^ bQPE) → Bool) (L : ℕ) :
      InvCatRel P_inv cat (chunkFiberStep pred L wImpl rImpl y)
        (chunkFiberStep pred L wId rId y) ((L : ℝ) * δ) := by
    dsimp only [chunkFiberStep]
    split_ifs
    · obtain ⟨hCl, hBd⟩ := invCatRel_mul (invCatRel_mul hR (invCatRel_pow hW L)) hR
      exact ⟨hCl, fun v hv ↦ (hBd v hv).trans_eq (by ring)⟩
    · exact invCatRel_pow hW L
  induction n with
  | zero => simpa [chunksFiber] using invCatRel_one P_inv cat
  | succ k ih =>
    rw [chunksFiber, chunksFiber, Finset.sum_range_succ]
    obtain ⟨hCl, hBd⟩ := invCatRel_mul (hChunk _ _) ih
    exact ⟨hCl, fun v hv ↦ (hBd v hv).trans_eq (by push_cast; ring)⟩

theorem tgEmbedUnitary_rWalkInWalkCat_reflIn (bCat mOut mMid : ℕ) :
    QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)) := by
  apply Subtype.ext
  change (2 : ℂ) • (inAllWalkCat bCat mOut mMid).basisOutcomeProjector 0 - 1 =
    (rWalkInWalkCat bCat mOut mMid).embedMatrix
      ((2 : ℂ) • (rAllInWalk mOut mMid).basisOutcomeProjector 0 - 1)
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    inAllWalkCat, CleanDyn.compose_basisOutcomeProjector]

theorem tgEmbedUnitary_rWalkInWalkCat_reflMid (bCat mOut mMid : ℕ) :
    QubitisedWalk.reflMidUnitary (inMidWalkCat bCat mOut mMid) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflMidUnitary (rMidInWalk mOut mMid)) := by
  apply Subtype.ext
  change 1 - (2 : ℂ) • (inMidWalkCat bCat mOut mMid).basisOutcomeProjector 0 =
    (rWalkInWalkCat bCat mOut mMid).embedMatrix
      (1 - (2 : ℂ) • (rMidInWalk mOut mMid).basisOutcomeProjector 0)
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    inMidWalkCat, CleanDyn.compose_basisOutcomeProjector]

theorem tgEmbedUnitary_rWalkInWalkCat_reflPulled (bCat mOut mMid : ℕ)
    (uB : Unitary (2 ^ walkWidth mOut mMid)) :
    QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid)
        ((rWalkInWalkCat bCat mOut mMid).embedUnitary uB) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB) := by
  dsimp [QubitisedWalk.reflPulledUnitary, QubitisedWalk.reflPulledPair]
  rw [tgEmbedUnitary_rWalkInWalkCat_reflMid, ← QRegister.embedUnitary_inv,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]

/-- Disjoint registers commute under `embedUnitary`. -/
theorem embedUnitary_comm_of_disjoint_tg {k m n : ℕ}
    (left : QRegister k n) (right : QRegister m n) (hdisj : left.DisjointWires right)
    (U₁ : Unitary (2 ^ k)) (U₂ : Unitary (2 ^ m)) :
    left.embedUnitary U₁ * right.embedUnitary U₂ =
      right.embedUnitary U₂ * left.embedUnitary U₁ :=
  Subtype.ext (left.embedMatrix_comm_of_disjoint right hdisj U₁.1 U₂.1)

theorem rLoInAct_disjoint_rCombHiInAct (mOut mMid mLow : ℕ) (hmLow16 : mLow ≤ 16) :
    ((rQPEInAct 16 11 mOut mMid).compose (rLoInQPE16 mLow hmLow16)).DisjointWires
      (rCombHiInAct mOut mMid mLow hmLow16) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hi := i.isLt
  rcases finSumFinEquiv.surjective j with ⟨jh | jw, rfl⟩
  · have hv := congrArg Fin.val hij
    simp only [QRegister.compose_apply, finSumFinEquiv_apply_left, rCombHiInAct,
      QRegister.concat_apply_left, rQPEInAct, rLoInQPE16, rHiInQPE16,
      QRegister.block_apply_val, actWidth, walkCatWidth] at hv
    omega
  · have hjw := jw.isLt
    have hv := congrArg Fin.val hij
    simp only [QRegister.compose_apply, finSumFinEquiv_apply_right, rCombHiInAct,
      QRegister.concat_apply_right, rQPEInAct, rLoInQPE16, rWalkCatInAct,
      QRegister.block_apply_val] at hv
    omega

/-! ### Stage-B Clock Reduction & Super-Step Dihedral Exponent Fusion -/

theorem chunksFiber_congr_bits {b₁ b₂ d : ℕ} (w M : ℕ) (W R : Unitary d)
    (y₁ : Fin (2 ^ b₁)) (y₂ : Fin (2 ^ b₂))
    (hbits : ∀ j < w + 1, y₁.val.testBit j = y₂.val.testBit j) :
    ∀ n ≤ w + 1, chunksFiber w M W R n y₁ = chunksFiber w M W R n y₂
  | 0, _ => rfl
  | k + 1, hle => by
      have hpred : chunkPred w k y₁ = chunkPred w k y₂ := by
        dsimp [chunkPred]
        split_ifs with hkw
        · exact hbits k (by omega)
        · rw [hbits w (by omega)]
      simp only [chunksFiber, chunkFiberStep, hpred,
        chunksFiber_congr_bits w M W R y₁ y₂ hbits k (by omega)]

theorem affineFoldVal_testBit_mod (w C x : ℕ) :
    ∀ j < w + 1,
      (affineFoldVal w C x).testBit j = (affineFoldVal w C (x % 2 ^ (w + 1))).testBit j := by
  intro j hj
  let xm := x % 2 ^ (w + 1)
  have hpow : 2 ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
  have hx_decomp : x = xm + 2 ^ (w + 1) * (x / 2 ^ (w + 1)) := (Nat.mod_add_div x _).symm
  have hlo : x % 2 ^ w = xm % 2 ^ w := by
    conv_lhs => rw [hx_decomp, hpow, mul_assoc, Nat.add_mul_mod_self_left]
  have hhi : (x / 2 ^ w) % 2 = (xm / 2 ^ w) % 2 := by
    have hd : x / 2 ^ w = xm / 2 ^ w + 2 * (x / 2 ^ (w + 1)) := by
      conv_lhs =>
        rw [hx_decomp, hpow, mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), ← hpow]
    rw [hd, mul_comm 2, Nat.add_mul_mod_self_right]
  have hxm_top : xm / 2 ^ (w + 1) = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr (Nat.mod_lt x (Nat.two_pow_pos (w + 1))))
  have hfold_eq : affineFoldVal w C x =
      affineFoldVal w C xm + (x / 2 ^ (w + 1)) * 2 ^ (w + 1) := by
    dsimp only [affineFoldVal]
    rw [hlo, hhi, hxm_top]
    ring
  have hfold_lt : affineFoldVal w C xm < 2 ^ (w + 1) := by
    have hylo : (if (xm / 2 ^ w) % 2 = 0 then 2 ^ w - 1 - xm % 2 ^ w
        else ((2 ^ w - 1 - xm % 2 ^ w) + C) % 2 ^ w) < 2 ^ w := by
      have h1 := Nat.mod_lt xm (Nat.two_pow_pos w)
      have h2 := Nat.mod_lt ((2 ^ w - 1 - xm % 2 ^ w) + C) (Nat.two_pow_pos w)
      split_ifs <;> omega
    dsimp only [affineFoldVal]
    rw [hxm_top, mul_zero, add_zero, hpow]
    rcases (by omega : (xm / 2 ^ w) % 2 = 0 ∨ (xm / 2 ^ w) % 2 = 1) with h0 | h1
    · rw [h0] at hylo ⊢; omega
    · rw [h1] at hylo ⊢; omega
  have hmod : affineFoldVal w C x % 2 ^ (w + 1) = affineFoldVal w C xm := by
    rw [hfold_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfold_lt]
  have ht := Nat.testBit_mod_two_pow (affineFoldVal w C x) (w + 1) j
  rw [hmod] at ht
  simpa [hj] using ht.symm

/-- Reduces the `16`-bit Stage-B affine schedule fiber at `m` to the `mLow`-bit fiber at
`m.val % 2 ^ mLow`. -/
theorem affineScheduleFiber_phaseB_eq_mod {d : ℕ} {mLow : ℕ}
    (hmLow1 : 1 ≤ mLow) (hmLow16 : mLow ≤ 16)
    (W R : Unitary d) (m : Fin (2 ^ 16)) :
    let xl : Fin (2 ^ mLow) := ⟨m.val % 2 ^ mLow, Nat.mod_lt _ (Nat.two_pow_pos mLow)⟩
    affineScheduleFiber (bQPE := 16) mLow (2 ^ mLow - 1) W R m =
      affineScheduleFiber (bQPE := mLow) mLow (2 ^ mLow - 1) W R xl := by
  intro xl
  unfold affineScheduleFiber
  have hw1 : mLow - 1 + 1 = mLow := by omega
  refine chunksFiber_congr_bits (mLow - 1) (2 ^ mLow - 1) W R _ _ (fun j hj ↦ ?_) mLow (by omega)
  have h1 : (qpeAffinePerm mLow 16 (2 ^ mLow - 1) m).val =
      affineFoldVal (mLow - 1) ((2 ^ mLow - 1) + 1 - 2 ^ (mLow - 1)) m.val := by
    dsimp [qpeAffinePerm]
    rw [dite_eq_left ⟨hmLow1, hmLow16⟩]; rfl
  have h2 : (qpeAffinePerm mLow mLow (2 ^ mLow - 1) xl).val =
      affineFoldVal (mLow - 1) ((2 ^ mLow - 1) + 1 - 2 ^ (mLow - 1)) xl.val := by
    dsimp [qpeAffinePerm]
    rw [dite_eq_left ⟨hmLow1, le_rfl⟩]; rfl
  rw [h1, h2]
  simpa only [hw1, xl] using
    affineFoldVal_testBit_mod (mLow - 1) ((2 ^ mLow - 1) + 1 - 2 ^ (mLow - 1)) m.val j hj

theorem superRefl_involutive {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (k : ℕ) :
    (R₁ * (R₁ * R₂) ^ k) * (R₁ * (R₁ * R₂) ^ k) = 1 := by
  induction k with
  | zero => simp [hR₁]
  | succ k' ih =>
    have hmid : (R₁ * R₂) * R₁ * (R₁ * R₂) = R₁ := by
      calc (R₁ * R₂) * R₁ * (R₁ * R₂)
          = R₁ * R₂ * (R₁ * R₁) * R₂ := by simp only [mul_assoc]
        _ = R₁ * (R₂ * R₂) := by rw [hR₁, mul_one, mul_assoc]
        _ = R₁ := by rw [hR₂, mul_one]
    calc (R₁ * (R₁ * R₂) ^ (k' + 1)) * (R₁ * (R₁ * R₂) ^ (k' + 1))
        = R₁ * ((R₁ * R₂) ^ k' * (R₁ * R₂)) * (R₁ * ((R₁ * R₂) * (R₁ * R₂) ^ k')) :=
            congrArg₂ (· * ·) (congrArg (R₁ * ·) (pow_succ _ k'))
              (congrArg (R₁ * ·) (pow_succ' _ k'))
      _ = R₁ * (R₁ * R₂) ^ k' * ((R₁ * R₂) * R₁ * (R₁ * R₂)) * (R₁ * R₂) ^ k' := by
            simp only [mul_assoc]
      _ = (R₁ * (R₁ * R₂) ^ k') * (R₁ * (R₁ * R₂) ^ k') := by
            rw [hmid]; simp only [mul_assoc]
      _ = 1 := ih

/-! ### Active-Space Split Equivalence & Statewise Two-Gear `L²` Perturbation Bound -/

/-- Equivalence splitting `actWidth bQPE bCat mOut mMid` into `(walkCat, qpe)` indices. -/
def tgActSplitEquiv (bQPE bCat mOut mMid : ℕ) :
    Fin (2 ^ actWidth bQPE bCat mOut mMid) ≃
      Fin (2 ^ walkCatWidth bCat mOut mMid) × Fin (2 ^ bQPE) :=
  (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid))).trans
    (BlockEncodingCore.splitBlockEquiv (walkCatWidth bCat mOut mMid) bQPE)

theorem tgActSplitEquiv_fst (bQPE bCat mOut mMid : ℕ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    (tgActSplitEquiv bQPE bCat mOut mMid g).1 =
      (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g := by
  apply (basisBits (walkCatWidth bCat mOut mMid)).injective
  funext i
  have h1 := congrFun (congrArg (basisBits (walkCatWidth bCat mOut mMid))
    (BlockEncodingCore.splitBlockEquiv_fst (walkCatWidth bCat mOut mMid) bQPE
      (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid)) g))) i
  dsimp only [tgActSplitEquiv, Equiv.trans_apply]
  rw [h1]
  change basisBits _ _ i = basisBits _ _ i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]
  simp [finCongr, TopIntegrationBridge.rWalkCatInAct]

theorem tgActSplitEquiv_snd (bQPE bCat mOut mMid : ℕ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    (tgActSplitEquiv bQPE bCat mOut mMid g).2 =
      (rQPEInAct bQPE bCat mOut mMid).extractIndex g := by
  apply (basisBits bQPE).injective
  funext j
  have h2 := congrFun (congrArg (basisBits bQPE)
    (BlockEncodingCore.splitBlockEquiv_snd (walkCatWidth bCat mOut mMid) bQPE
      (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid)) g))) j
  dsimp only [tgActSplitEquiv, Equiv.trans_apply]
  rw [h2]
  change basisBits _ _ j = basisBits _ _ j
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]
  simp only [TopIntegrationBridge.rQPEInAct, QRegister.block_apply_val]
  by_cases hb : g.val.testBit (walkCatWidth bCat mOut mMid + j.val) <;> simp [finCongr, hb]

/-- Tensor product of a `(walk + catalyst)` state `wc` with a QPE clock state `q`. -/
noncomputable def tgTensorWCQPE {bQPE bCat mOut mMid : ℕ}
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    Fin (2 ^ actWidth bQPE bCat mOut mMid) → ℂ :=
  fun g ↦ wc ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
    q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)

theorem tgEmbedMatrix_rWalkCatInAct_mulVec {bQPE bCat mOut mMid : ℕ}
    (A : Operator (2 ^ walkCatWidth bCat mOut mMid))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ((rWalkCatInAct bQPE bCat mOut mMid).embedMatrix A) *ᵥ tgTensorWCQPE wc q =
      tgTensorWCQPE (A *ᵥ wc) q := by
  funext g
  rw [QRegister.embedMatrix_mulVec_apply]
  have hstep :
      (∑ u : Fin (2 ^ walkCatWidth bCat mOut mMid),
        A ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) u *
          tgTensorWCQPE wc q ((rWalkCatInAct bQPE bCat mOut mMid).replaceIndex g u)) =
      ∑ u : Fin (2 ^ walkCatWidth bCat mOut mMid),
        (A ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) u * wc u) *
          q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tgTensorWCQPE]
    have hq :
        (rQPEInAct bQPE bCat mOut mMid).extractIndex
            ((rWalkCatInAct bQPE bCat mOut mMid).replaceIndex g u) =
          (rQPEInAct bQPE bCat mOut mMid).extractIndex g :=
      (rQPEInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
        (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid) g u
    rw [hq, QRegister.extractIndex_replaceIndex, mul_assoc]
  exact hstep.trans (by rw [← Finset.sum_mul]; rfl)

theorem tgEmbedMatrix_rQPEInAct_mulVec {bQPE bCat mOut mMid : ℕ}
    (B : Operator (2 ^ bQPE))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ((rQPEInAct bQPE bCat mOut mMid).embedMatrix B) *ᵥ tgTensorWCQPE wc q =
      tgTensorWCQPE wc (B *ᵥ q) := by
  funext g
  rw [QRegister.embedMatrix_mulVec_apply]
  have hstep :
      (∑ u : Fin (2 ^ bQPE),
        B ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) u *
          tgTensorWCQPE wc q ((rQPEInAct bQPE bCat mOut mMid).replaceIndex g u)) =
      ∑ u : Fin (2 ^ bQPE),
        wc ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
          (B ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) u * q u) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tgTensorWCQPE]
    have hwc :
        (rWalkCatInAct bQPE bCat mOut mMid).extractIndex
            ((rQPEInAct bQPE bCat mOut mMid).replaceIndex g u) =
          (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g :=
      (rWalkCatInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
        (QRegister.disjoint_comm.mp (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)) g u
    rw [hwc, QRegister.extractIndex_replaceIndex]
    ring
  exact hstep.trans (by rw [← Finset.mul_sum]; rfl)

theorem tgEmbed_qpeMuxUnitary_mulVec {bQPE bCat mOut mMid : ℕ}
    (F : Fin (2 ^ bQPE) → Unitary (2 ^ walkCatWidth bCat mOut mMid))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    ((((rQPEInAct bQPE bCat mOut mMid).concat (rWalkCatInAct bQPE bCat mOut mMid)
        (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)).embedUnitary
          (QubitisedWalk.qpeMuxUnitary F)).1 *ᵥ tgTensorWCQPE wc q) g =
      ((F ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)).1 *ᵥ wc)
          ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
        q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) := by
  rw [QubitisedWalk.embed_qpeMuxUnitary_mulVec, Finset.sum_apply,
    Finset.sum_eq_single ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)]
  · rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_left rfl, QRegister.embedUnitary_val,
      tgEmbedMatrix_rWalkCatInAct_mulVec]
    rfl
  · intro m _ hm
    rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_right (Ne.symm hm)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Pointwise action of `StageB * StageA` on `tgTensorWCQPE wc q`: on QPE clock branch `m`,
applies `FB m * FA (rHiInQPE16.extractIndex m)` to `wc`! -/
theorem tgEmbed_phaseB_phaseA_mulVec {mOut mMid mLow : ℕ} (hmLow16 : mLow ≤ 16)
    (FA : Fin (2 ^ (16 - mLow)) → Unitary (2 ^ walkCatWidth 11 mOut mMid))
    (FB : Fin (2 ^ 16) → Unitary (2 ^ walkCatWidth 11 mOut mMid))
    (wc : Fin (2 ^ walkCatWidth 11 mOut mMid) → ℂ) (q : Fin (2 ^ 16) → ℂ)
    (g : Fin (2 ^ actWidth 16 11 mOut mMid)) :
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rWC := rWalkCatInAct 16 11 mOut mMid
    let rCombFull := rQPE.concat rWC (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    let m := rQPE.extractIndex g
    let xh := (rHiInQPE16 mLow hmLow16).extractIndex m
    (((rCombFull.embedUnitary (QubitisedWalk.qpeMuxUnitary FB) *
        (rCombHiInAct mOut mMid mLow hmLow16).embedUnitary (QubitisedWalk.qpeMuxUnitary FA)).1) *ᵥ
      tgTensorWCQPE wc q) g =
      (((FB m * FA xh).1) *ᵥ wc) (rWC.extractIndex g) * q m := by
  intro rQPE rWC rCombFull m xh
  let ψA := ((rCombHiInAct mOut mMid mLow hmLow16).embedUnitary
    (QubitisedWalk.qpeMuxUnitary FA)).1 *ᵥ tgTensorWCQPE wc q
  have hψA (h : Fin (2 ^ actWidth 16 11 mOut mMid)) :
      ψA h =
        ((FA ((rHiInQPE16 mLow hmLow16).extractIndex (rQPE.extractIndex h))).1 *ᵥ wc)
          (rWC.extractIndex h) * q (rQPE.extractIndex h) := by
    dsimp only [ψA, rCombHiInAct]
    rw [QubitisedWalk.embed_qpeMuxUnitary_mulVec, Finset.sum_apply,
      Finset.sum_eq_single ((rQPE.compose (rHiInQPE16 mLow hmLow16)).extractIndex h)]
    · rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_left rfl,
        QRegister.extractIndex_compose, QRegister.embedUnitary_val,
        tgEmbedMatrix_rWalkCatInAct_mulVec]
      rfl
    · intro k _ hk
      rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_right (Ne.symm hk)]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  have hψA_branch : ∀ u : Fin (2 ^ walkCatWidth 11 mOut mMid),
      ψA (rWC.replaceIndex g u) =
        ((FA xh).1 *ᵥ wc) u * q m := by
    intro u
    rw [hψA]
    have hq : rQPE.extractIndex (rWC.replaceIndex g u) = m :=
      rQPE.extractIndex_replaceIndex_of_disjoint rWC
        (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid) g u
    rw [hq, QRegister.extractIndex_replaceIndex]
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  change ((rCombFull.embedUnitary (QubitisedWalk.qpeMuxUnitary FB)).1 *ᵥ ψA) g = _
  rw [QubitisedWalk.embed_qpeMuxUnitary_mulVec, Finset.sum_apply, Finset.sum_eq_single m]
  · rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_left rfl, QRegister.embedUnitary_val,
      QRegister.embedMatrix_mulVec_apply]
    have hrep (u : Fin (2 ^ walkCatWidth 11 mOut mMid)) :
        rWC.basisSplitEquiv.symm (u, (rWC.basisSplitEquiv g).2) = rWC.replaceIndex g u := rfl
    simp_rw [hrep, hψA_branch, ← mul_assoc]
    rw [← Finset.sum_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rfl
  · intro m' _ hm'
    rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_right (Ne.symm hm')]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

theorem tgSysAct_tensorState_zero_eq {bQPE bCat mOut mMid : ℕ}
    (ψ : Fin (2 ^ systemQubits_local) → ℂ) :
    let sys : QRegister systemQubits_local (actWidth bQPE bCat mOut mMid) :=
      .block 0 systemQubits_local (by dsimp [actWidth]; omega)
    let e₁ := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
    sys.tensorState ψ (Pi.single 0 1) =
      tgTensorWCQPE (tensorWalkCat e₁ (basisState (0 : Fin (2 ^ bCat))))
        (basisState 0) := by
  intro sys e₁
  funext g
  let xwc := (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g
  let xw := (rWalkInWalkCat bCat mOut mMid).extractIndex xwc
  have hsys_eq : sys.extractIndex g = (rSysInWalk mOut mMid).extractIndex xw := by
    dsimp only [xw, xwc]
    rw [← QRegister.extractIndex_compose, ← QRegister.extractIndex_compose]
    congr 1; ext i; simp [sys, TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat, rSysInWalk]
  have hbits_iff :
      ((sys.basisSplitEquiv g).2 = 0) ↔
        (((rSysInWalk mOut mMid).basisSplitEquiv xw).2 = 0 ∧
          (rCatInWalkCat bCat mOut mMid).extractIndex xwc = 0 ∧
          (rQPEInAct bQPE bCat mOut mMid).extractIndex g = 0) := by
    rw [CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
      CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
    constructor
    · intro h
      have hzero (w : Wire (actWidth bQPE bCat mOut mMid)) (hw : systemQubits_local ≤ w.val) :
          basisBits (actWidth bQPE bCat mOut mMid) g w = 0 := by
        have hnot : w ∉ Set.range sys.wires := by
          rintro ⟨i, rfl⟩; simp [sys] at hw; omega
        exact congrFun h ⟨w, hnot⟩
      refine ⟨?_, fun i ↦ ?_, fun j ↦ hzero _ (by
        simp [TopIntegrationBridge.rQPEInAct, walkCatWidth, walkWidth, systemQubits_local]; omega)⟩
      · funext ⟨w, hw⟩
        have hge : systemQubits_local ≤ w.val := by
          by_contra hlt; push Not at hlt
          exact hw ⟨⟨w.val, hlt⟩, by ext; simp [rSysInWalk]⟩
        simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply, xw, xwc,
          QRegister.basisBits_extractIndex]
        exact hzero _ (by simp [TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat]; omega)
      · simp only [xwc, QRegister.basisBits_extractIndex]
        exact hzero _ (by
          simp [TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat, walkWidth]; omega)
    · rintro ⟨h1, h2, h3⟩
      funext ⟨w, hw⟩
      have hge : systemQubits_local ≤ w.val := by
        by_contra hlt; push Not at hlt
        exact hw ⟨⟨w.val, hlt⟩, by ext; simp [sys]⟩
      simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply]
      by_cases h_w : w.val < walkWidth mOut mMid
      · let w' : Wire (walkWidth mOut mMid) := ⟨w.val, h_w⟩
        have hw' : w' ∉ Set.range (rSysInWalk mOut mMid).wires := by
          rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi
          simp [rSysInWalk, w', systemQubits_local] at hv hge; omega
        have hb := congrFun h1 ⟨w', hw'⟩
        simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply, xw, xwc,
          QRegister.basisBits_extractIndex] at hb
        rw [← hb]; refine congrArg (basisBits _ _) ?_
        ext; simp [TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat, w']
      · by_cases h_wc : w.val < walkCatWidth bCat mOut mMid
        · let i : Fin bCat := ⟨w.val - walkWidth mOut mMid, by
            dsimp [walkCatWidth] at h_wc; omega⟩
          have hb := h2 i
          simp only [xwc, QRegister.basisBits_extractIndex] at hb
          rw [← hb]; refine congrArg (basisBits _ _) ?_
          ext; simp [TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat, i]; omega
        · let j : Fin bQPE := ⟨w.val - walkCatWidth bCat mOut mMid, by
            have hw_lt : w.val < walkCatWidth bCat mOut mMid + bQPE :=
              actWidth_eq bQPE bCat mOut mMid ▸ w.isLt
            omega⟩
          have hb := h3 j
          rw [← hb]; refine congrArg (basisBits _ _) ?_
          ext; simp [TopIntegrationBridge.rQPEInAct, j]; omega
  dsimp only [QRegister.tensorState, tgTensorWCQPE, tensorWalkCat, basisState]
  change _ =
    (e₁ xw *
      (Pi.single 0 (1 : ℂ) : Fin (2 ^ bCat) → ℂ)
        ((rCatInWalkCat bCat mOut mMid).extractIndex xwc)) *
    (Pi.single 0 (1 : ℂ) : Fin (2 ^ bQPE) → ℂ) ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)
  dsimp only [e₁, QRegister.tensorState]
  rw [hsys_eq]
  by_cases h : (sys.basisSplitEquiv g).2 = 0
  · obtain ⟨h1, h2, h3⟩ := hbits_iff.mp h
    simp [h, h1, h2, h3]
  · have hnot := mt hbits_iff.mpr h
    by_cases h1 : ((rSysInWalk mOut mMid).basisSplitEquiv xw).2 = 0
    · by_cases h2 : (rCatInWalkCat bCat mOut mMid).extractIndex xwc = 0
      · have h3 : (rQPEInAct bQPE bCat mOut mMid).extractIndex g ≠ 0 :=
          fun hc ↦ hnot ⟨h1, h2, hc⟩
        simp [Pi.single_apply, h, h3]
      · simp [Pi.single_apply, h, h2]
    · simp [Pi.single_apply, h, h1]

theorem tgRCatInAct_eq_compose (bQPE bCat mOut mMid : ℕ) :
    rCatInAct bQPE bCat mOut mMid =
      (rWalkCatInAct bQPE bCat mOut mMid).compose (rCatInWalkCat bCat mOut mMid) := by
  ext i; simp [TopIntegrationBridge.rCatInAct, TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat]

theorem tgNorm_tensorWCQPE {bQPE bCat mOut mMid : ℕ}
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ‖WithLp.toLp 2 (tgTensorWCQPE wc q)‖ =
      ‖WithLp.toLp 2 wc‖ * ‖WithLp.toLp 2 q‖ := by
  have hsq : ‖WithLp.toLp 2 (tgTensorWCQPE wc q)‖ ^ 2 =
      (‖WithLp.toLp 2 wc‖ * ‖WithLp.toLp 2 q‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    let f : Fin (2 ^ actWidth bQPE bCat mOut mMid) → ℝ :=
      fun g ↦ ‖tgTensorWCQPE wc q g‖ ^ 2
    rw [show (∑ g, ‖tgTensorWCQPE wc q g‖ ^ 2) = ∑ g, f g from rfl,
      ← (tgActSplitEquiv bQPE bCat mOut mMid).symm.sum_comp f, Fintype.sum_prod_type,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    let g := (tgActSplitEquiv bQPE bCat mOut mMid).symm (x, m)
    have hfst : (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g = x := by
      rw [← tgActSplitEquiv_fst, Equiv.apply_symm_apply]
    have hsnd : (rQPEInAct bQPE bCat mOut mMid).extractIndex g = m := by
      rw [← tgActSplitEquiv_snd, Equiv.apply_symm_apply]
    dsimp only [f, tgTensorWCQPE]
    rw [hfst, hsnd, norm_mul, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

/-! ### Sector Eigenbasis Parseval & Turnkey Two-Gear End-to-End Closures -/

/-- Basis-index subtype for the `η`-electron Hamming-weight sector on `k` spin-orbitals. -/
abbrev SectorIndexTG (k η : ℕ) : Type :=
  { i : Fin (2 ^ k) // ∑ q : Fin k, (basisBits k i q).val = η }

/-- Restriction of a `2 ^ k` state vector to `SectorIndexTG k η`. -/
def sectorRestrictTG {k : ℕ} (η : ℕ) (ψ : Fin (2 ^ k) → ℂ) : SectorIndexTG k η → ℂ :=
  fun s ↦ ψ s.1

/-- Zero-padded extension from `SectorIndexTG k η` to `Fin (2 ^ k) → ℂ`. -/
def sectorExtendTG {k : ℕ} (η : ℕ) (v : SectorIndexTG k η → ℂ) : Fin (2 ^ k) → ℂ :=
  fun i ↦ if h : ∑ q : Fin k, (basisBits k i q).val = η then v ⟨i, h⟩ else 0

theorem sum_over_sectorIndex_tg {k : ℕ} (η : ℕ) (f : Fin (2 ^ k) → ℂ)
    (hf : ∀ i : Fin (2 ^ k), (∑ q : Fin k, (basisBits k i q).val) ≠ η → f i = 0) :
    (∑ i : Fin (2 ^ k), f i) = ∑ s : SectorIndexTG k η, f s.1 := by
  have hsub : (∑ i : Fin (2 ^ k), f i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ k) ↦ ∑ q, (basisBits k i q).val = η), f i :=
    (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦
      hf i fun heq ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩)).symm
  rw [hsub]
  exact Finset.sum_bij (fun i hi ↦ ⟨i, (Finset.mem_filter.mp hi).2⟩)
    (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ congrArg Subtype.val h)
    (fun s _ ↦ ⟨s.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.2⟩, rfl⟩) (fun _ _ ↦ rfl)

theorem electronSectorProjector_mulVec_eq_self_iff_tg {k η : ℕ} (ψ : Fin (2 ^ k) → ℂ) :
    electronSectorProjector k η *ᵥ ψ = ψ ↔
      ∀ i : Fin (2 ^ k), (∑ q : Fin k, (basisBits k i q).val) ≠ η → ψ i = 0 := by
  constructor
  · intro h i hi
    have hi' := congrFun h i
    simp only [electronSectorProjector, Matrix.mulVec_diagonal, hi, ↓reduceIte, zero_mul] at hi'
    exact hi'.symm
  · intro h; ext i; simp only [electronSectorProjector, Matrix.mulVec_diagonal]
    split_ifs with hi
    · exact one_mul (ψ i)
    · exact (zero_mul (ψ i)).trans (h i hi).symm

theorem electronSectorProjector_mulVec_sectorExtend_tg {k η : ℕ}
    (v : SectorIndexTG k η → ℂ) :
    electronSectorProjector k η *ᵥ sectorExtendTG η v = sectorExtendTG η v := by
  rw [electronSectorProjector_mulVec_eq_self_iff_tg]
  intro i hi; simp only [sectorExtendTG, hi, ↓reduceDIte]

theorem sectorExtend_sectorRestrict_tg {k η : ℕ} {ψ : Fin (2 ^ k) → ℂ}
    (hψ : electronSectorProjector k η *ᵥ ψ = ψ) :
    sectorExtendTG η (sectorRestrictTG η ψ) = ψ := by
  have hzero := (electronSectorProjector_mulVec_eq_self_iff_tg ψ).mp hψ
  ext i
  by_cases hi : ∑ q : Fin k, (basisBits k i q).val = η
  · simp only [sectorExtendTG, sectorRestrictTG, hi, ↓reduceDIte]
  · rw [hzero i hi]; simp only [sectorExtendTG, hi, ↓reduceDIte]

theorem dotProduct_star_self_re_tg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (dotProduct (star v) v).re = ∑ i : ι, Complex.normSq (v i) := by
  have hc : dotProduct (star v) v = ((∑ i : ι, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_sum]
  rw [hc, Complex.ofReal_re]

theorem star_sectorExtend_dotProduct_tg {k η : ℕ} (u w : SectorIndexTG k η → ℂ) :
    dotProduct (star (sectorExtendTG η u)) (sectorExtendTG η w) = dotProduct (star u) w := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_over_sectorIndex_tg η _ fun i hi ↦
    by simp only [sectorExtendTG, hi, ↓reduceDIte, mul_zero]]
  exact Finset.sum_congr rfl fun s _ ↦ by simp only [sectorExtendTG, s.2, ↓reduceDIte]

theorem sum_normSq_sectorExtend_tg {k η : ℕ} (v : SectorIndexTG k η → ℂ) :
    ∑ i : Fin (2 ^ k), Complex.normSq (sectorExtendTG η v i) =
      ∑ s : SectorIndexTG k η, Complex.normSq (v s) := by
  have h := congrArg Complex.re (star_sectorExtend_dotProduct_tg v v)
  rwa [dotProduct_star_self_re_tg, dotProduct_star_self_re_tg] at h

theorem mulVec_sectorExtend_of_comm_tg {k η : ℕ} {A : Operator (2 ^ k)}
    (hcomm : A * electronSectorProjector k η = electronSectorProjector k η * A)
    (v : SectorIndexTG k η → ℂ) :
    A *ᵥ sectorExtendTG η v =
      sectorExtendTG η
        ((A.submatrix (Subtype.val : SectorIndexTG k η → Fin (2 ^ k)) Subtype.val) *ᵥ v) := by
  have hsec :
      electronSectorProjector k η *ᵥ (A *ᵥ sectorExtendTG η v) = A *ᵥ sectorExtendTG η v := by
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec,
      electronSectorProjector_mulVec_sectorExtend_tg]
  have hzero := (electronSectorProjector_mulVec_eq_self_iff_tg _).mp hsec
  ext i
  by_cases hi : ∑ q : Fin k, (basisBits k i q).val = η
  · simp only [sectorExtendTG, hi, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [sum_over_sectorIndex_tg η _ fun j hj ↦ by simp only [hj, ↓reduceDIte, mul_zero]]
    exact Finset.sum_congr rfl fun s _ ↦ by simp only [s.2, ↓reduceDIte]
  · rw [hzero i hi]; simp only [sectorExtendTG, hi, ↓reduceDIte]

theorem unitaryGroup_mul_conjTranspose_mulVec_tg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    (V : Matrix ι ι ℂ) *ᵥ ((V : Matrix ι ι ℂ)ᴴ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
    Unitary.coe_mul_star_self, Matrix.one_mulVec]

theorem sum_normSq_unitaryGroup_conjTranspose_mulVec_tg {ι : Type*} [Fintype ι]
    [DecidableEq ι] (V : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ s : ι, Complex.normSq (((V : Matrix ι ι ℂ)ᴴ *ᵥ v) s) = ∑ s : ι, Complex.normSq (v s) := by
  have h : dotProduct (star ((V : Matrix ι ι ℂ)ᴴ *ᵥ v)) ((V : Matrix ι ι ℂ)ᴴ *ᵥ v) =
      dotProduct (star v) v := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec, unitaryGroup_mul_conjTranspose_mulVec_tg]
  have hre := congrArg Complex.re h
  rwa [dotProduct_star_self_re_tg, dotProduct_star_self_re_tg] at hre

theorem sum_normSq_orthogonal_family_tg {I : Type*} [Fintype I]
    {n : ℕ} (v : I → Fin n → ℂ)
    (horth : ∀ j j' : I, j ≠ j' → dotProduct (star (v j)) (v j') = 0) :
    ∑ g : Fin n, Complex.normSq ((∑ j : I, v j) g) =
      ∑ j : I, ∑ g : Fin n, Complex.normSq (v j g) := by
  have h1 := (dotProduct_star_self_re_tg (∑ j : I, v j)).symm
  have h2 : dotProduct (star (∑ j : I, v j)) (∑ j' : I, v j') =
      ∑ j : I, dotProduct (star (v j)) (v j) := by
    simp only [star_sum, dotProduct, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single j]
    · intro j' _ hne; exact horth j j' hne.symm
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  rw [h1, h2, Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ ↦ dotProduct_star_self_re_tg (v j)

theorem sector_eigenbasis_parseval_tg {k η : ℕ} {H_eff H : Operator (2 ^ k)} {E δ_H : ℝ}
    {ψ : Fin (2 ^ k) → ℂ} (hHeff : H_eff.IsHermitian)
    (hcomm_eff : H_eff * electronSectorProjector k η = electronSectorProjector k η * H_eff)
    (hEigen : IsEigenSector H η E ψ) (hψ_norm : ∑ i, Complex.normSq (ψ i) = 1)
    (hdiff : ∑ i, Complex.normSq
      (((electronSectorProjector k η * (H_eff - H) * electronSectorProjector k η) *ᵥ ψ) i) ≤
        δ_H ^ 2) :
    ∃ (E_tilde : SectorIndexTG k η → ℝ) (φ_tilde : SectorIndexTG k η → Fin (2 ^ k) → ℂ)
      (c : SectorIndexTG k η → ℂ),
      (∀ j, IsEigenSector H_eff η (E_tilde j) (φ_tilde j)) ∧
      (∀ j, ∑ i, Complex.normSq (φ_tilde j i) = 1) ∧
      (∀ j j', dotProduct (star (φ_tilde j)) (φ_tilde j') = if j = j' then 1 else 0) ∧
      (∑ j, c j • φ_tilde j = ψ) ∧ (∑ j, Complex.normSq (c j) = 1) ∧
      (∑ j, Complex.normSq (c j) * (E_tilde j - E) ^ 2 ≤ δ_H ^ 2) := by
  rcases hEigen with ⟨hHψ, hPψ, _⟩
  let P := electronSectorProjector k η
  let Heff_sub : Matrix (SectorIndexTG k η) (SectorIndexTG k η) ℂ :=
    H_eff.submatrix Subtype.val Subtype.val
  have hHeff_sub : Heff_sub.IsHermitian := hHeff.submatrix Subtype.val
  let U := hHeff_sub.eigenvectorUnitary
  let E_tilde : SectorIndexTG k η → ℝ := hHeff_sub.eigenvalues
  let φ_tilde : SectorIndexTG k η → Fin (2 ^ k) → ℂ :=
    fun j ↦ sectorExtendTG η ⇑(hHeff_sub.eigenvectorBasis j)
  have hφ_sec (j : SectorIndexTG k η) : P *ᵥ φ_tilde j = φ_tilde j :=
    electronSectorProjector_mulVec_sectorExtend_tg _
  have hφ_eig (j : SectorIndexTG k η) : H_eff *ᵥ φ_tilde j = (E_tilde j : ℂ) • φ_tilde j := by
    dsimp only [φ_tilde, E_tilde]
    rw [mulVec_sectorExtend_of_comm_tg hcomm_eff, hHeff_sub.mulVec_eigenvectorBasis]
    ext i; by_cases hi : ∑ q_1, (basisBits k i q_1).val = η <;> simp [sectorExtendTG, hi]
  have hφ_orthonormal (j j' : SectorIndexTG k η) :
      dotProduct (star (φ_tilde j)) (φ_tilde j') = if j = j' then 1 else 0 := by
    dsimp only [φ_tilde]
    rw [star_sectorExtend_dotProduct_tg, dotProduct_comm,
      ← EuclideanSpace.inner_eq_star_dotProduct]
    by_cases hjj : j = j'
    · subst hjj; simp [inner_self_eq_norm_sq_to_K, hHeff_sub.eigenvectorBasis.orthonormal.1 j]
    · simp [hjj]
  have hφ_norm (j : SectorIndexTG k η) : ∑ i, Complex.normSq (φ_tilde j i) = 1 := by
    have h := congrArg Complex.re (hφ_orthonormal j j)
    simpa only [↓reduceIte, Complex.one_re, dotProduct_star_self_re_tg] using h
  have hφ_ne (j : SectorIndexTG k η) : φ_tilde j ≠ 0 := by
    intro hzero; have h1 := hφ_norm j; simp [hzero] at h1
  let c : SectorIndexTG k η → ℂ :=
    (U : Matrix (SectorIndexTG k η) (SectorIndexTG k η) ℂ)ᴴ *ᵥ sectorRestrictTG η ψ
  have hU_recon : ∑ j : SectorIndexTG k η, c j • φ_tilde j = ψ := by
    have hcol : (U : Matrix _ _ ℂ) *ᵥ c = sectorRestrictTG η ψ :=
      unitaryGroup_mul_conjTranspose_mulVec_tg U (sectorRestrictTG η ψ)
    have hsum_sub : ∑ j : SectorIndexTG k η, c j • ⇑(hHeff_sub.eigenvectorBasis j) =
        sectorRestrictTG η ψ := by
      rw [← hcol]; ext s; simp [U, Matrix.mulVec, dotProduct, mul_comm]
    calc ∑ j : SectorIndexTG k η, c j • φ_tilde j
        = sectorExtendTG η (∑ j : SectorIndexTG k η, c j • ⇑(hHeff_sub.eigenvectorBasis j)) := by
            ext i
            by_cases hi : ∑ q_1, (basisBits k i q_1).val = η <;>
              simp [φ_tilde, sectorExtendTG, hi, Finset.sum_apply]
      _ = sectorExtendTG η (sectorRestrictTG η ψ) := by rw [hsum_sub]
      _ = ψ := sectorExtend_sectorRestrict_tg hPψ
  have hc_sum : ∑ j : SectorIndexTG k η, Complex.normSq (c j) = 1 := by
    have hsec_norm := sum_normSq_sectorExtend_tg (sectorRestrictTG η ψ)
    rw [sectorExtend_sectorRestrict_tg hPψ, hψ_norm] at hsec_norm
    exact (sum_normSq_unitaryGroup_conjTranspose_mulVec_tg U
      (sectorRestrictTG η ψ)).trans hsec_norm.symm
  refine ⟨E_tilde, φ_tilde, c, fun j ↦ ⟨hφ_eig j, hφ_sec j, hφ_ne j⟩,
    hφ_norm, hφ_orthonormal, hU_recon, hc_sum, ?_⟩
  have hproj_vec : (P * (H_eff - H) * P) *ᵥ ψ = H_eff *ᵥ ψ - (E : ℂ) • ψ := by
    calc (P * (H_eff - H) * P) *ᵥ ψ
        = P *ᵥ ((H_eff - H) *ᵥ (P *ᵥ ψ)) := by
            rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = P *ᵥ (H_eff *ᵥ ψ - (E : ℂ) • ψ) := by rw [hPψ, Matrix.sub_mulVec, hHψ]
      _ = P *ᵥ (H_eff *ᵥ ψ) - P *ᵥ ((E : ℂ) • ψ) := Matrix.mulVec_sub _ _ _
      _ = H_eff *ᵥ ψ - (E : ℂ) • ψ := by
            have hPHeff : P *ᵥ (H_eff *ᵥ ψ) = H_eff *ᵥ ψ := by
              rw [Matrix.mulVec_mulVec, ← hcomm_eff, ← Matrix.mulVec_mulVec, hPψ]
            rw [hPHeff, Matrix.mulVec_smul, hPψ]
  have hvec : (P * (H_eff - H) * P) *ᵥ ψ =
      ∑ j : SectorIndexTG k η, (c j * ((E_tilde j - E : ℝ) : ℂ)) • φ_tilde j := by
    rw [hproj_vec]; conv_lhs => rw [← hU_recon]
    rw [Matrix.mulVec_sum_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hφ_eig j, smul_smul, smul_smul, ← sub_smul]; push_cast; ring_nf
  have hnorm_eq : ∑ i, Complex.normSq (((P * (H_eff - H) * P) *ᵥ ψ) i) =
      ∑ j : SectorIndexTG k η, Complex.normSq (c j) * (E_tilde j - E) ^ 2 := by
    rw [hvec, sum_normSq_orthogonal_family_tg]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum, hφ_norm j, mul_one,
        Complex.normSq_ofReal]
      ring
    · intro j j' hne
      have ho := hφ_orthonormal j j'
      simp only [hne, ↓reduceIte, dotProduct, Pi.star_apply] at ho
      simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
      have hfactor : (∑ x, star (c j * ↑(E_tilde j - E) * φ_tilde j x) *
          (c j' * ↑(E_tilde j' - E) * φ_tilde j' x)) =
          (star (c j * ↑(E_tilde j - E)) * (c j' * ↑(E_tilde j' - E))) *
            ∑ x, star (φ_tilde j x) * φ_tilde j' x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by rw [star_mul']; ring
      rw [hfactor, ho, mul_zero]
  rwa [← hnorm_eq]

theorem weighted_sum_add_sq_le_tg {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) {ε₁ ε₂ : ℝ} (hw : ∀ i, 0 ≤ w i) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (ha : ∑ i, w i * a i ^ 2 ≤ ε₁ ^ 2) (hb : ∑ i, w i * b i ^ 2 ≤ ε₂ ^ 2) :
    ∑ i, w i * (a i + b i) ^ 2 ≤ (ε₁ + ε₂) ^ 2 := by
  have hexp : ∑ i, w i * (a i + b i) ^ 2 =
      (∑ i, w i * a i ^ 2) + (∑ i, w i * b i ^ 2) + 2 * ∑ i, w i * (a i * b i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hzero {u v : ι → ℝ} (hu : ∑ i, w i * u i ^ 2 ≤ 0) (i : ι) : w i * (u i * v i) = 0 := by
    have hi := (Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw j) (sq_nonneg _))
      (Finset.mem_univ i)).trans hu
    rcases mul_eq_zero.mp (le_antisymm hi (mul_nonneg (hw i) (sq_nonneg _))) with hwi | hui
    · simp [hwi]
    · simp [sq_eq_zero_iff.mp hui]
  have hcross : 2 * ∑ i, w i * (a i * b i) ≤ 2 * ε₁ * ε₂ := by
    by_cases h1 : ε₁ = 0
    · subst h1; simp [hzero (by simpa only [sq, zero_mul] using ha)]
    · by_cases h2 : ε₂ = 0
      · subst h2
        have hz (i : ι) : w i * (a i * b i) = 0 := by
          rw [mul_comm (a i)]; exact hzero (by simpa only [sq, zero_mul] using hb) i
        simp [hz]
      · have hp1 : 0 < ε₁ := lt_of_le_of_ne hε₁ (Ne.symm h1)
        have hp2 : 0 < ε₂ := lt_of_le_of_ne hε₂ (Ne.symm h2)
        have hpt (i : ι) : 2 * ε₁ * ε₂ * (w i * (a i * b i)) ≤
            ε₂ ^ 2 * (w i * a i ^ 2) + ε₁ ^ 2 * (w i * b i ^ 2) := by
          nlinarith [mul_nonneg (hw i) (sq_nonneg (ε₂ * a i - ε₁ * b i))]
        have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hpt i
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
        nlinarith [mul_pos hp1 hp2]
  nlinarith

theorem sq_min_sub_min_le_tg (x y T : ℝ) : (min x T - min y T) ^ 2 ≤ (x - y) ^ 2 := by
  have habs : |min x T - min y T| ≤ |x - y| := by
    rcases le_total x T with hx | hx <;> rcases le_total y T with hy | hy
    · simp only [min_eq_left hx, min_eq_left hy, le_refl]
    · rw [min_eq_left hx, min_eq_right hy, abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]; linarith
    · rw [min_eq_right hx, min_eq_left hy, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]; linarith
    · simp only [min_eq_right hx, min_eq_right hy, sub_self, abs_zero, abs_nonneg]
  rw [← sq_abs (min x T - min y T), ← sq_abs (x - y)]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- Modular negation permutation `y ↦ -y mod 2 ^ 16` on `16`-bit QPE outcomes. -/
def negMod16TG : Equiv.Perm (Fin (2 ^ 16)) where
  toFun y := ⟨(2 ^ 16 - y.val) % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩
  invFun y := ⟨(2 ^ 16 - y.val) % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩
  left_inv y := by apply Fin.ext; dsimp; have hyLt : y.val < 65536 := y.isLt; omega
  right_inv y := by apply Fin.ext; dsimp; have hyLt : y.val < 65536 := y.isLt; omega

theorem exp_two_pi_I_nat_tg (q : ℕ) :
    Complex.exp (2 * π * Complex.I * (q : ℂ)) = 1 := by
  rw [show (2 : ℂ) * π * Complex.I * (q : ℂ) = (q : ℂ) * (π * Complex.I + π * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring_nf

theorem iqft16_apply_tg (y m : Fin (2 ^ 16)) : (QFT.qftMatrix 16)ᴴ y m =
    (1 / 256 : ℂ) * Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ)) := by
  change star (QFT.qftMatrix 16 m y) = _
  simp only [QFT.qftMatrix, qpeAngle, star_mul', Complex.star_def, ← Complex.exp_conj]
  rw [show √(2 ^ 16 : ℝ) = 256 by
      rw [show (2 ^ 16 : ℝ) = (256 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    show (starRingEnd ℂ) (1 / (256 : ℝ) : ℂ) = (1 / 256 : ℂ) by simp [map_ofNat]]
  congr 2; simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_div₀]
  push_cast; ring

theorem qpeDecodeEnergy_negMod16_tg (eLB lam : ℝ) (y : Fin (2 ^ 16)) :
    qpeDecodeEnergy eLB lam 16 (negMod16TG y) = qpeDecodeEnergy eLB lam 16 y := by
  unfold qpeDecodeEnergy qpeHalfPhase
  rw [cos_foldAngle_div_two (qpeAngle_nonneg 16 (negMod16TG y))
      (qpeAngle_le_two_pi 16 (negMod16TG y)),
    cos_foldAngle_div_two (qpeAngle_nonneg 16 y) (qpeAngle_le_two_pi 16 y)]
  suffices h : |Real.cos (qpeAngle 16 (negMod16TG y) / 2)| = |Real.cos (qpeAngle 16 y / 2)| by
    rw [h]
  by_cases hy : y.val = 0
  · have heq : negMod16TG y = y := by apply Fin.ext; simp [negMod16TG, hy]
    rw [heq]
  · have hval : (negMod16TG y).val = 2 ^ 16 - y.val :=
      Nat.mod_eq_of_lt (by have := y.isLt; omega)
    have hang : qpeAngle 16 (negMod16TG y) / 2 = π - qpeAngle 16 y / 2 := by
      dsimp [qpeAngle]; rw [hval, Nat.cast_sub (le_of_lt y.isLt)]; push_cast; field_simp; ring
    rw [hang, Real.cos_pi_sub, abs_neg]

theorem normSq_iqft16_windowPhaseVec_neg_tg (M : ℕ) (c : ℕ → ℝ) (θ : ℝ)
    (y : Fin (2 ^ 16)) :
    Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) (negMod16TG y)) =
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c θ) y) := by
  suffices h : ((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) (negMod16TG y) =
      star (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c θ) y) by
    rw [h, Complex.star_def, Complex.normSq_conj]
  simp only [Matrix.mulVec, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [iqft16_apply_tg, iqft16_apply_tg, star_mul', star_mul']
  have h1 : star (1 / 256 : ℂ) = (1 / 256 : ℂ) := by simp
  have hexp_y : Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 (negMod16TG y) : ℂ)) =
      star (Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ)) =
        Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ) := by
      simp [Complex.conj_ofReal, Complex.conj_I]
    rw [hconj]
    by_cases hy : y.val = 0
    · have h0 : (negMod16TG y).val = 0 := by simp [negMod16TG, hy]
      simp [qpeAngle, hy, h0]
    · have hval : (negMod16TG y).val = 2 ^ 16 - y.val :=
        Nat.mod_eq_of_lt (by have := y.isLt; omega)
      have hang : (qpeAngle 16 (negMod16TG y) : ℂ) = 2 * π - (qpeAngle 16 y : ℂ) := by
        dsimp [qpeAngle]; rw [hval, Nat.cast_sub (le_of_lt y.isLt)]; push_cast; field_simp; ring
      have hsplit : -Complex.I * (m.val : ℂ) * (2 * π - (qpeAngle 16 y : ℂ)) =
          -(2 * π * Complex.I * (m.val : ℂ)) +
            Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ) := by ring
      rw [hang, hsplit, Complex.exp_add, Complex.exp_neg, exp_two_pi_I_nat_tg, inv_one, one_mul]
  have hw : windowPhaseVec 16 M c (-θ) m = star (windowPhaseVec 16 M c θ m) := by
    unfold windowPhaseVec; split_ifs with hm
    · rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2; simp [Complex.conj_ofReal, Complex.conj_I]
    · simp
  rw [h1, hexp_y, hw]

theorem sum_normSq_iqft16_windowPhaseVec_neg_mse_tg (M : ℕ) (c : ℕ → ℝ)
    (eLB lam T E θ : ℝ) :
    (∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) y) *
        (min (qpeDecodeEnergy eLB lam 16 y) T - min E T) ^ 2) =
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c θ) y) *
        (min (qpeDecodeEnergy eLB lam 16 y) T - min E T) ^ 2 := by
  let f : Fin (2 ^ 16) → ℝ := fun z ↦
    Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) z) *
      (min (qpeDecodeEnergy eLB lam 16 z) T - min E T) ^ 2
  rw [show (∑ y, Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) y) *
      (min (qpeDecodeEnergy eLB lam 16 y) T - min E T) ^ 2) = ∑ z, f z from rfl,
    ← Equiv.sum_comp negMod16TG f]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  dsimp [f]; rw [normSq_iqft16_windowPhaseVec_neg_tg, qpeDecodeEnergy_negMod16_tg]

theorem sum_normSq_unitary_mulVec_tg {d : ℕ} (U : Unitary d) (v : Fin d → ℂ) :
    ∑ g : Fin d, Complex.normSq ((U.1 *ᵥ v) g) = ∑ g : Fin d, Complex.normSq (v g) := by
  have h1 : dotProduct (star (U.1 *ᵥ v)) (U.1 *ᵥ v) = dotProduct (star v) v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.vecMul_one]
  have hre := congrArg Complex.re h1
  rwa [dotProduct_star_self_re_tg, dotProduct_star_self_re_tg] at hre

theorem sum_filter_basisOutcomeProbability_eq_tg {n m_anc b_qpe : ℕ}
    (anc : QRegister m_anc n) (rQPE : QRegister b_qpe m_anc)
    (u : Fin (2 ^ n) → ℂ) (y : Fin (2 ^ b_qpe)) :
    ∑ a ∈ Finset.univ.filter (fun a ↦ rQPE.extractIndex a = y),
        anc.basisOutcomeProbability a u =
      (anc.compose rQPE).basisOutcomeProbability y u := by
  calc ∑ a ∈ Finset.univ.filter (fun a ↦ rQPE.extractIndex a = y),
        anc.basisOutcomeProbability a u
      = ∑ a, anc.basisOutcomeProbability a u * (if rQPE.extractIndex a = y then 1 else 0) := by
        rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> ring
    _ = ∑ y', (anc.compose rQPE).basisOutcomeProbability y' u * (if y' = y then 1 else 0) :=
        sum_basisOutcomeProbability_mul_comp anc rQPE u (fun y' ↦ if y' = y then 1 else 0)
    _ = (anc.compose rQPE).basisOutcomeProbability y u := by
        rw [Fintype.sum_eq_single y (fun y' hy' ↦ by simp [hy'])]; simp

theorem p450HBlocked_quadForm_re_le_tg (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    (star ψ ⬝ᵥ (BlockEncodingCore.p450HBlocked *ᵥ ψ)).re ≤
      dfthcUpperBound * ∑ i, Complex.normSq (ψ i) := by
  let U := p450FswapUninterleave.eval
  have hU2 : U.1 * U.1ᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.2
  have hconj : star ψ ⬝ᵥ ((U.1 * thcHamiltonian P450.dfthc * U.1ᴴ) *ᵥ ψ) =
      star (U.1ᴴ *ᵥ ψ) ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ (U.1ᴴ *ᵥ ψ)) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hnorm : ∑ i, Complex.normSq ((U.1ᴴ *ᵥ ψ) i) = ∑ i, Complex.normSq (ψ i) := by
    rw [← dotProduct_star_self_re_tg, ← dotProduct_star_self_re_tg, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hU2, Matrix.one_mulVec]
  change (star ψ ⬝ᵥ ((U.1 * thcHamiltonian P450.dfthc * U.1ᴴ) *ᵥ ψ)).re ≤ _
  rw [hconj, ← hnorm]; exact thcHamiltonian_dfthc_quadForm_re_le _

theorem quantP450_eigenSector_bounds_tg {mOut mMid : ℕ}
    {H_tilde_blk : Operator (2 ^ (2 * 58))} {uB : Unitary (2 ^ walkWidth mOut mMid)}
    (hSOS : PulledSOSBlockEncoding mOut mMid H_tilde_blk dfthcLowerBound 97.3864 uB)
    {δ_H : ℝ} (hδH0 : 0 ≤ δ_H)
    (hAgree : AgreesOnElectronSector 58 63 H_tilde_blk BlockEncodingCore.p450HBlocked δ_H)
    {E_t : ℝ} {φ_t : Fin (2 ^ (2 * 58)) → ℂ}
    (hEig : IsEigenSector H_tilde_blk 63 E_t φ_t)
    (hnorm : (∑ i, Complex.normSq (φ_t i)) = 1) :
    dfthcLowerBound ≤ E_t ∧ E_t ≤ dfthcUpperBound + δ_H :=
  ⟨(hSOS.jordanRelation φ_t E_t hEig.1 hnorm).2.2.1,
    PerturbedQPEClosure.sector_eigen_ub_of_agreesOnElectronSector hδH0 hAgree
      (fun ψ _ ↦ p450HBlocked_quadForm_re_le_tg ψ) hEig⟩

/-- Explicit-estimator `MeasuresLowEnergies` matching `Specs.MeasuresLowEnergies`. -/
def MeasuresLowEnergiesAt {k m : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (estimate : Fin (2 ^ m) → ℝ) (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let IsEigen (E : ℝ) (ψ : Fin (2 ^ k) → ℂ) :=
    H *ᵥ ψ = (E : ℂ) • ψ ∧ electronSectorProjector k η *ᵥ ψ = ψ ∧ ψ ≠ 0
  ∀ T : ℝ, (∀ E' φ, IsEigen E' φ → T ≤ E' + Δ) →
    ∀ E ψ, IsEigen E ψ → ∑ i, Complex.normSq (ψ i) = 1 →
    let out := W.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
    ∑ a, anc.basisOutcomeProbability a out * (min (estimate a) T - min E T) ^ 2 ≤ ε ^ 2

/-- Explicit Two-Gear QPE energy estimator on `actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)`.
-/
noncomputable abbrev p450TwoGearEst (wOuter wInner2 : ℕ) :
    Fin (2 ^ actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)) → ℝ :=
  qpeEstimate dfthcLowerBound 97.3864 16 (rQPEInAnc 16 11 (mOutUB wOuter) (mMidUB
    wInner2)).extractIndex

/-- Explicit-estimator `ValidClampedBox` doubled-phase QPE closure proving `MeasuresLowEnergiesAt`
with `p450TwoGearEst wOuter wInner2` on `BlockEncodingCore.p450HBlocked` (`63`-electron sector). -/
theorem capped_perturbed_measuresLowEnergiesAt_box_tg (wOuter wInner2 M : ℕ)
    (H_eff : Operator (2 ^ (2 * 58)))
    (uCatIdeal : Unitary (2 ^ 11)) (uWinIdeal : Unitary (2 ^ 16))
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (uB : Unitary (2 ^ nUB wOuter wInner2))
    (wImplBlk :
      Unitary (2 ^ (2 * 58 + actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2))))
    {δH δWUb eRef eGapUb κ : ℝ} (hbox : MultiGearQPE.ValidClampedBox M eGapUb κ)
    (hHeff : H_eff.IsHermitian) (hδH0 : 0 ≤ δH)
    (hAgree : AgreesOnElectronSector 58 63 H_eff BlockEncodingCore.p450HBlocked δH)
    (hSOS : PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) H_eff dfthcLowerBound 97.3864
      uB)
    (hWZero : uWinIdeal.1 *ᵥ basisState 0 =
      windowVec 16 M (sineWindowCoeff (M + 1)))
    (hPert : MultiGearQPE.ImplQPEPertHyp wOuter wInner2 M uCatIdeal uB uWinIdeal
      (phasedIqftUnitary 16 ζ hζ) wImplBlk δWUb)
    (hRefVar : DihedralWalkQPE.P450RefVarBound eRef) (hδWUb0 : 0 ≤ δWUb)
    (hGap : eRef + 0.1 - dfthcLowerBound ≤ eGapUb)
    (heGapH11 : eGapUb + δH ≤ 11)
    (hBud : κ * (spectralAmpEffNorm 97.3864 eGapUb / 2) * (π / ((M : ℝ) + 1)) + δH +
      eGapUb * δWUb ≤ 0.001) :
    MeasuresLowEnergiesAt BlockEncodingCore.p450HBlocked 63 0.1 0.001
      (p450TwoGearEst wOuter wInner2) wImplBlk := by
  let mOut := mOutUB wOuter; let mMid := mMidUB wInner2
  let uIqftIdeal := phasedIqftUnitary 16 ζ hζ
  let wIdBlk := BlockReflection.blockedIdealUnitary 16 11 mOut mMid 16 M
    uCatIdeal uB uWinIdeal uIqftIdeal
  have hMlo15 : 2 ^ 15 ≤ M := (by decide : 2 ^ 15 ≤ 46368).trans hbox.1
  have hMlt16 : M < 2 ^ 16 := Nat.lt_of_le_of_lt hbox.2.1 (by decide)
  have heGap0 : 0 ≤ eGapUb := le_trans (by norm_num) hbox.2.2.1
  have hkap0 : 0 ≤ κ := le_trans (by norm_num) (MultiGearQPE.validClampedBox_kap_ge hbox)
  let ε_qpe := κ * (spectralAmpEffNorm 97.3864 eGapUb / 2) * (π / ((M : ℝ) + 1))
  have hε_qpe0 : 0 ≤ ε_qpe :=
    mul_nonneg (mul_nonneg hkap0 (div_nonneg (sqrt_nonneg _) (by norm_num)))
      (div_nonneg pi_pos.le (Nat.cast_add_one_pos M).le)
  have hζ2 : Complex.normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ, _root_.one_pow]
  have hq_normSq (θ : ℝ) (y : Fin (2 ^ 16)) :
      Complex.normSq ((uIqftIdeal.1 *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) θ) y) =
        Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
          windowPhaseVec 16 M (sineWindowCoeff (M + 1)) θ) y) := by
    rw [show uIqftIdeal.1 = ζ • (QFT.qftMatrix 16)ᴴ from
        phasedIqftUnitary_coe 16 ζ hζ,
      Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hζ2, one_mul]
  let mAnc := actAncillas 16 11 mOut mMid
  let sys : QRegister (2 * 58) (2 * 58 + mAnc) := .block 0 (2 * 58) (by omega)
  let anc : QRegister mAnc (2 * 58 + mAnc) := .block (2 * 58) mAnc le_rfl
  let rQPE := rQPEInAnc 16 11 mOut mMid
  let rQPE_glob : QRegister 16 (2 * 58 + mAnc) := anc.compose rQPE
  obtain ⟨hcomm_eff, hproj_err⟩ :=
    PerturbedQPEClosure.projected_sector_err_of_agreesOnElectronSector hAgree
  intro T hT E ψ hEigen hψ_norm
  have hT_gap : T ≤ dfthcLowerBound + eGapUb := by
    linarith only [threshold_le_p450HBlocked_of_dfthc hRefVar T hT, hGap]
  have hE_lb : dfthcLowerBound ≤ E := (p450HBlocked_eigenvalue_bounds E ψ hEigen hψ_norm).1
  obtain ⟨E_tilde, φ_tilde, c, hφ_isEigen, hφ_norm, hφ_orthonormal, hU_recon, hc_sum, hparseval⟩ :=
    sector_eigenbasis_parseval_tg hHeff hcomm_eff hEigen hψ_norm
      (by simpa only [hψ_norm, mul_one] using hproj_err ψ)
  let u_ideal := wIdBlk.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
  let out_j : SectorIndexTG (2 * 58) 63 → Fin (2 ^ (2 * 58 + mAnc)) → ℂ :=
    fun j ↦ wIdBlk.1 *ᵥ sys.tensorState (φ_tilde j) (Pi.single 0 1)
  have hmse_j (j : SectorIndexTG (2 * 58) 63) :
      ∑ y : Fin (2 ^ 16), rQPE_glob.basisOutcomeProbability y (out_j j) *
        (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 y) T - min (E_tilde j) T) ^ 2 ≤
        ε_qpe ^ 2 := by
    obtain ⟨hEt_lb, _⟩ :=
      quantP450_eigenSector_bounds_tg hSOS hδH0 hAgree (hφ_isEigen j) (hφ_norm j)
    have hEt_ub : E_tilde j ≤ dfthcLowerBound + 2 * 97.3864 - eGapUb := by
      have hna := dfthcUpperBound_le_nonAliasing heGapH11; unfold p450Lambda at hna; linarith
    obtain ⟨w_pos, w_neg, hw_pos, hw_neg, hw_sum, hp_eq⟩ :=
      MultiGearQPE.blocked_ideal_qpe_exact 16 11 mOut mMid 16 M (by decide) le_rfl hMlo15 hMlt16
        hSOS uCatIdeal uWinIdeal uIqftIdeal (sineWindowCoeff (M + 1)) hWZero
        63 (E_tilde j) (φ_tilde j) (hφ_isEigen j) (hφ_norm j)
    let φ := QubitisedWalk.spectralPhase dfthcLowerBound 97.3864 (E_tilde j)
    have hpy (y : Fin (2 ^ 16)) : rQPE_glob.basisOutcomeProbability y (out_j j) =
        w_pos * Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
            windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ)) y) +
          w_neg * Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
            windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (-(2 * φ))) y) := by
      rw [← sum_filter_basisOutcomeProbability_eq_tg anc rQPE (out_j j) y]
      exact (hp_eq y).trans (congr
        (congrArg (· + ·) (congrArg (w_pos * ·) (hq_normSq (2 * φ) y)))
        (congrArg (w_neg * ·) (hq_normSq (-(2 * φ)) y)))
    simp_rw [hpy]
    have hsplit : ∑ y : Fin (2 ^ 16),
          (w_pos * Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
              windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ)) y) +
            w_neg * Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
              windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (-(2 * φ))) y)) *
            (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 y) T - min (E_tilde j) T) ^ 2 =
        (w_pos + w_neg) * ∑ y : Fin (2 ^ 16),
          Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
            windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ)) y) *
            (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 y) T - min (E_tilde j) T) ^ 2 := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_normSq_iqft16_windowPhaseVec_neg_mse_tg]
    rw [hsplit]
    have hbranch := MultiGearQPE.clamped_sineWindow_energy_mse_le_box hbox hT_gap hEt_lb hEt_ub
    exact (mul_le_mul_of_nonneg_left hbranch (add_nonneg hw_pos hw_neg)).trans
      ((mul_le_mul_of_nonneg_right hw_sum (sq_nonneg _)).trans_eq (one_mul _))
  have hprob_decomp (y : Fin (2 ^ 16)) :
      rQPE_glob.basisOutcomeProbability y u_ideal =
        ∑ j : SectorIndexTG (2 * 58) 63,
          Complex.normSq (c j) * rQPE_glob.basisOutcomeProbability y (out_j j) := by
    let Py := rQPE_glob.basisOutcomeProjector y
    have hout_sum : Py *ᵥ u_ideal = ∑ j : SectorIndexTG (2 * 58) 63, c j • (Py *ᵥ out_j j) := by
      dsimp only [u_ideal, out_j]
      rw [← hU_recon, sys.tensorState_sum_left]; simp_rw [sys.tensorState_smul_left]
      rw [Matrix.mulVec_sum_smul, Matrix.mulVec_sum_smul]
    unfold QRegister.basisOutcomeProbability
    change ∑ g, Complex.normSq ((Py *ᵥ u_ideal) g) = _
    rw [hout_sum, sum_normSq_orthogonal_family_tg]
    · exact Finset.sum_congr rfl fun j _ ↦ by simp [Pi.smul_apply, ← Finset.mul_sum, Py]
    · intro j j' hne
      have ho_φ : dotProduct (star (φ_tilde j)) (φ_tilde j') = 0 := by
        simpa only [hne, ↓reduceIte] using hφ_orthonormal j j'
      have ho_br := BlockReflection.blocked_ideal_qpe_horth 16 11 mOut mMid 16 M hSOS
        uCatIdeal uWinIdeal uIqftIdeal 63 (E_tilde j) (φ_tilde j) (E_tilde j') (φ_tilde j')
        (hφ_isEigen j) (hφ_norm j) (hφ_isEigen j') (hφ_norm j') ho_φ y
      have hpull : dotProduct (star (c j • (Py *ᵥ out_j j))) (c j' • (Py *ᵥ out_j j')) =
          star (c j) * c j' * dotProduct (star (Py *ᵥ out_j j)) (Py *ᵥ out_j j') := by
        simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hpull, ho_br, mul_zero]
  have hprob_sum_j (j : SectorIndexTG (2 * 58) 63) :
      ∑ y : Fin (2 ^ 16), rQPE_glob.basisOutcomeProbability y (out_j j) = 1 := by
    have h1 := sum_basisOutcomeProbability_mul rQPE_glob (out_j j) (fun _ ↦ 1)
    simp only [mul_one] at h1
    rw [h1, sum_normSq_unitary_mulVec_tg, sum_normSq_sys_tensorState_zero, hφ_norm j]
  have hideal_H :
      ∑ a, anc.basisOutcomeProbability a u_ideal *
        (min (qpeEstimate dfthcLowerBound 97.3864 16 rQPE.extractIndex a) T - min E T) ^ 2 ≤
        (ε_qpe + δH) ^ 2 := by
    have hcomp := sum_basisOutcomeProbability_mul_comp anc rQPE u_ideal
      (fun y ↦ (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 y) T - min E T) ^ 2)
    change ∑ a, anc.basisOutcomeProbability a u_ideal *
        (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 (rQPE.extractIndex a)) T - min E T) ^ 2 ≤ _
    rw [hcomp]
    change ∑ y : Fin (2 ^ 16), rQPE_glob.basisOutcomeProbability y u_ideal *
        (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 y) T - min E T) ^ 2 ≤ _
    simp_rw [hprob_decomp, Finset.sum_mul]; rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    let w : SectorIndexTG (2 * 58) 63 × Fin (2 ^ 16) → ℝ :=
      fun p ↦ Complex.normSq (c p.1) * rQPE_glob.basisOutcomeProbability p.2 (out_j p.1)
    let a_fn : SectorIndexTG (2 * 58) 63 × Fin (2 ^ 16) → ℝ :=
      fun p ↦ min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 p.2) T - min (E_tilde p.1) T
    let b_fn : SectorIndexTG (2 * 58) 63 × Fin (2 ^ 16) → ℝ :=
      fun p ↦ min (E_tilde p.1) T - min E T
    have hrew : (∑ p : SectorIndexTG (2 * 58) 63 × Fin (2 ^ 16),
        Complex.normSq (c p.1) * rQPE_glob.basisOutcomeProbability p.2 (out_j p.1) *
          (min (qpeDecodeEnergy dfthcLowerBound 97.3864 16 p.2) T - min E T) ^ 2) =
        ∑ p, w p * (a_fn p + b_fn p) ^ 2 :=
      Finset.sum_congr rfl fun p _ ↦ by dsimp only [w, a_fn, b_fn]; ring
    rw [hrew]
    refine weighted_sum_add_sq_le_tg w a_fn b_fn
      (fun p ↦ mul_nonneg (Complex.normSq_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _)) hε_qpe0 hδH0 ?_ ?_
    · rw [Fintype.sum_prod_type]
      calc ∑ j : SectorIndexTG (2 * 58) 63, ∑ y : Fin (2 ^ 16), w (j, y) * a_fn (j, y) ^ 2
          = ∑ j, Complex.normSq (c j) *
              (∑ y, rQPE_glob.basisOutcomeProbability y (out_j j) * a_fn (j, y) ^ 2) :=
            Finset.sum_congr rfl fun j _ ↦ by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by dsimp only [w]; ring
        _ ≤ ∑ j, Complex.normSq (c j) * ε_qpe ^ 2 :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (hmse_j j) (Complex.normSq_nonneg _)
        _ = ε_qpe ^ 2 := by rw [← Finset.sum_mul, hc_sum, one_mul]
    · rw [Fintype.sum_prod_type]
      calc ∑ j : SectorIndexTG (2 * 58) 63, ∑ y : Fin (2 ^ 16), w (j, y) * b_fn (j, y) ^ 2
          = ∑ j, Complex.normSq (c j) * (min (E_tilde j) T - min E T) ^ 2 :=
            Finset.sum_congr rfl fun j _ ↦ by
              have hp : ∑ y, w (j, y) * b_fn (j, y) ^ 2 =
                  (Complex.normSq (c j) * (min (E_tilde j) T - min E T) ^ 2) *
                    ∑ y, rQPE_glob.basisOutcomeProbability y (out_j j) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun _ _ ↦ by dsimp only [w, b_fn]; ring
              rw [hp, hprob_sum_j j, mul_one]
        _ ≤ ∑ j, Complex.normSq (c j) * (E_tilde j - E) ^ 2 :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (sq_min_sub_min_le_tg _ _ _) (Complex.normSq_nonneg _)
        _ ≤ δH ^ 2 := hparseval
  have himpl := mse_impl_le_of_ideal_and_perturbation anc
    (qpeEstimate dfthcLowerBound 97.3864 16 rQPE.extractIndex) heGap0 (add_nonneg hε_qpe0 hδH0)
    (fun a ↦ le_qpeDecodeEnergy (by norm_num) 16 (rQPE.extractIndex a)) hE_lb hT_gap hideal_H
    (hPert E ψ hEigen hψ_norm)
  exact himpl.trans
    (pow_le_pow_left₀ (add_nonneg (add_nonneg hε_qpe0 hδH0) (mul_nonneg heGap0 hδWUb0)) hBud 2)

/-! ### Turnkey `Ray1036 + Hi14247` & `Ray1036 + Fast12603` Two-Gear End-to-End Wrappers -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearQPEPhase5

end
