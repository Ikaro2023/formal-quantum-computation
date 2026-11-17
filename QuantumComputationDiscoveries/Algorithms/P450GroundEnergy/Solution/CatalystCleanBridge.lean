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

public import QuantumComputation.Circuits.Toffoli
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanAncillaToffoli
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradRaySliceBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SeamAdapters

/-!
# Clean-Workspace Catalytic Subroutine & Catalyst Sub-Slice Factorization

Provides block-split product-state calculus, LSB-first phase-gradient sub-slice factorization, and
compositional combinators for clean-workspace catalytic subroutines:
1. `blockSplitEquiv`, `prodState`, and `phaseGradientState_eq_prodState_top`;
2. `RealizesCleanCatalyticSubroutineWith` (`φ_cat`-parametric) together with `.identity`,
   `.congrUnitary`, and `.seq`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open scoped Matrix ComplexOrder MatrixOrder BigOperators

/-- Left `k`-wire block `.block 0 k` inside a register of `total` wires (`k + b = total`). -/
def locLeftOf (k b total : ℕ) (h : k + b = total) : QRegister k total :=
  .block 0 k (by omega)

/-- Right `b`-wire block `.block k b` inside a register of `total` wires (`k + b = total`). -/
def locRightOf (k b total : ℕ) (h : k + b = total) : QRegister b total :=
  .block k b (by omega)

/-- Left `k` wires `0 .. k - 1` of `k + b` wires. -/
abbrev locLeft (k b : ℕ) : QRegister k (k + b) :=
  locLeftOf k b (k + b) rfl

/-- Right `b` wires `k .. k + b - 1` of `k + b` wires. -/
abbrev locRight (k b : ℕ) : QRegister b (k + b) :=
  locRightOf k b (k + b) rfl

/-- Computational-basis bijection splitting `k + b` wires into left `k` and right `b` wires. -/
def blockSplitEquiv (k b : ℕ) : Fin (2 ^ (k + b)) ≃ Fin (2 ^ k) × Fin (2 ^ b) where
  toFun g := ((locLeft k b).extractIndex g, (locRight k b).extractIndex g)
  invFun p := (basisBits (k + b)).symm (Fin.addCases (basisBits k p.1) (basisBits b p.2))
  left_inv g := by
    apply (basisBits (k + b)).injective
    rw [(basisBits (k + b)).apply_symm_apply]
    funext idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp only [Fin.addCases_left]
      rw [(locLeft k b).basisBits_extractIndex]
      refine congrArg (basisBits (k + b) g) ?_
      ext
      simp [locLeft, locLeftOf]
    · simp only [Fin.addCases_right]
      rw [(locRight k b).basisBits_extractIndex]
      congr 1
  right_inv := by
    rintro ⟨x, y⟩
    set g := (basisBits (k + b)).symm (Fin.addCases (basisBits k x) (basisBits b y))
    have hg : basisBits (k + b) g = Fin.addCases (basisBits k x) (basisBits b y) :=
      (basisBits (k + b)).apply_symm_apply _
    ext1
    · apply (basisBits k).injective
      funext i
      change basisBits k ((locLeft k b).extractIndex g) i = basisBits k x i
      rw [(locLeft k b).basisBits_extractIndex]
      have hw : locLeft k b i = Fin.castAdd b i := by ext; simp [locLeft, locLeftOf]
      rw [hw]
      exact (congrFun hg (Fin.castAdd b i)).trans (Fin.addCases_left i)
    · apply (basisBits b).injective
      funext j
      change basisBits b ((locRight k b).extractIndex g) j = basisBits b y j
      rw [(locRight k b).basisBits_extractIndex]
      have hw : locRight k b j = Fin.natAdd k j := by ext; simp [locRight, locRightOf]
      rw [hw]
      exact (congrFun hg (Fin.natAdd k j)).trans (Fin.addCases_right j)

@[simp]
theorem extractIndex_locLeft_symm (k b : ℕ) (x : Fin (2 ^ k)) (y : Fin (2 ^ b)) :
    (locLeft k b).extractIndex ((blockSplitEquiv k b).symm (x, y)) = x :=
  congrArg Prod.fst ((blockSplitEquiv k b).apply_symm_apply (x, y))

@[simp]
theorem extractIndex_locRight_symm (k b : ℕ) (x : Fin (2 ^ k)) (y : Fin (2 ^ b)) :
    (locRight k b).extractIndex ((blockSplitEquiv k b).symm (x, y)) = y :=
  congrArg Prod.snd ((blockSplitEquiv k b).apply_symm_apply (x, y))

/-- Exact LSB-first integer decomposition `g.val = x.val + 2 ^ k * y.val` across `locLeft` and
`locRight`. -/
theorem extractIndex_locLeft_val (k b : ℕ) (g : Fin (2 ^ (k + b))) :
    ((locLeft k b).extractIndex g).val = g.val % 2 ^ k := by
  have hlt : g.val % 2 ^ k < 2 ^ k := Nat.mod_lt g.val (Nat.two_pow_pos k)
  suffices hEq : (locLeft k b).extractIndex g = ⟨g.val % 2 ^ k, hlt⟩ from
    congrArg Fin.val hEq
  apply (basisBits k).injective
  funext i
  rw [(locLeft k b).basisBits_extractIndex]
  have hw : ((locLeft k b) i).val = i.val := by simp [locLeft, locLeftOf, QRegister.block]
  simp only [basisBits_eq_div_mod, hw]
  congr 1
  have hdvd : 2 ^ (i.val + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 i.isLt
  have hmod : (g.val % 2 ^ k) % 2 ^ (i.val + 1) = g.val % 2 ^ (i.val + 1) :=
    Nat.mod_mod_of_dvd g.val hdvd
  have hdiv_mod : ∀ m : ℕ, (m / 2 ^ i.val) % 2 = (m % 2 ^ (i.val + 1)) / 2 ^ i.val := by
    intro m
    rw [pow_succ, Nat.mod_mul_right_div_self]
  rw [hdiv_mod (g.val % 2 ^ k), hmod, ← hdiv_mod g.val]

theorem extractIndex_locRight_val (k b : ℕ) (g : Fin (2 ^ (k + b))) :
    ((locRight k b).extractIndex g).val = g.val / 2 ^ k := by
  have hlt : g.val / 2 ^ k < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← pow_add, Nat.add_comm b k]
    exact g.isLt
  suffices hEq : (locRight k b).extractIndex g = ⟨g.val / 2 ^ k, hlt⟩ from
    congrArg Fin.val hEq
  apply (basisBits b).injective
  funext j
  rw [(locRight k b).basisBits_extractIndex]
  have hw : ((locRight k b) j).val = k + j.val := rfl
  simp only [basisBits_eq_div_mod, hw]
  congr 1
  rw [pow_add 2 k j.val, ← Nat.div_div_eq_div_mul]

theorem val_eq_locLeft_add_mul_locRight (k b : ℕ) (g : Fin (2 ^ (k + b))) :
    g.val = ((locLeft k b).extractIndex g).val + 2 ^ k * ((locRight k b).extractIndex g).val := by
  rw [extractIndex_locLeft_val, extractIndex_locRight_val]
  exact (Nat.mod_add_div g.val (2 ^ k)).symm

/-- Tensor-product state vector on `total` wires (`k + b = total`) formed from `ξ : Fin (2^k) → ℂ`
on the left `k` wires and `φ : Fin (2^b) → ℂ` on the right `b` wires. -/
def prodStateOf {k b total : ℕ} (h : k + b = total)
    (ξ : Fin (2 ^ k) → ℂ) (φ : Fin (2 ^ b) → ℂ) : Fin (2 ^ total) → ℂ :=
  fun g ↦ ξ ((locLeftOf k b total h).extractIndex g) * φ ((locRightOf k b total h).extractIndex g)

/-- Tensor-product state vector on `k + b` wires. -/
abbrev prodState {k b : ℕ} (ξ : Fin (2 ^ k) → ℂ) (φ : Fin (2 ^ b) → ℂ) :
    Fin (2 ^ (k + b)) → ℂ :=
  prodStateOf rfl ξ φ

@[simp]
theorem prodState_symm {k b : ℕ} (ξ : Fin (2 ^ k) → ℂ) (φ : Fin (2 ^ b) → ℂ)
    (x : Fin (2 ^ k)) (y : Fin (2 ^ b)) :
    prodState ξ φ ((blockSplitEquiv k b).symm (x, y)) = ξ x * φ y := by
  simp [prodState, prodStateOf, extractIndex_locLeft_symm, extractIndex_locRight_symm]

/-- Fine-angle phase state on the low `b_low` wires of a `(b_low + b_high)`-bit phase-gradient
register. -/
noncomputable def phaseGradientFineLow (b_low b_high : ℕ) : Fin (2 ^ b_low) → ℂ :=
  fun x ↦ (Real.sqrt (2 ^ b_low) : ℂ)⁻¹ *
    Complex.exp (-(2 * Real.pi * Complex.I * x.val) / 2 ^ (b_low + b_high))

/-- LSB-first catalyst sub-slice identity:
In `QuantumComputation`'s LSB-first `basisBits` convention (`g = x + 2^{b_low} y`), a
`(b_low + b_high)`-bit `phaseGradientState` factors as `phaseGradientFineLow b_low b_high` on the
low `b_low` wires (`locLeft b_low b_high = .block 0 b_low _`) tensored with the coarse
`phaseGradientState b_high` on the upper `b_high` wires (`locRight b_low b_high`).
This enables a single `17`-qubit `phaseGradientState 17` to simultaneously serve `14`-bit catalytic
Givens rotations (on `.block 3 14 le_rfl`) and `17`-bit catalytic `QFT†` without extra qubits. -/
theorem phaseGradientState_eq_prodState_top (b_low b_high : ℕ) :
    phaseGradientState (b_low + b_high) =
      prodState (phaseGradientFineLow b_low b_high) (phaseGradientState b_high) := by
  funext g
  simp only [prodState, prodStateOf, phaseGradientState, phaseGradientFineLow]
  have hsqrt :
      (Real.sqrt (2 ^ (b_low + b_high)) : ℂ)⁻¹ =
        (Real.sqrt (2 ^ b_low) : ℂ)⁻¹ * (Real.sqrt (2 ^ b_high) : ℂ)⁻¹ := by
    have hr : Real.sqrt ((2 : ℝ) ^ (b_low + b_high)) =
        Real.sqrt ((2 : ℝ) ^ b_low) * Real.sqrt ((2 : ℝ) ^ b_high) := by
      rw [pow_add, Real.sqrt_mul (by positivity)]
    have hr' : Real.sqrt (2 ^ (b_low + b_high)) =
        Real.sqrt (2 ^ b_low) * Real.sqrt (2 ^ b_high) := by simpa using hr
    rw [hr', Complex.ofReal_mul, _root_.mul_inv_rev, mul_comm]
  have hexp :
      Complex.exp (-(2 * Real.pi * Complex.I * g.val) / 2 ^ (b_low + b_high)) =
        Complex.exp (-(2 * Real.pi * Complex.I * ((locLeft b_low b_high).extractIndex g).val) /
            2 ^ (b_low + b_high)) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((locRight b_low b_high).extractIndex g).val) /
            2 ^ b_high) := by
    rw [← Complex.exp_add]
    congr 1
    rw [val_eq_locLeft_add_mul_locRight b_low b_high g]
    have hpow : (2 : ℂ) ^ (b_low + b_high) = (2 : ℂ) ^ b_low * (2 : ℂ) ^ b_high := pow_add 2 _ _
    have hneL : (2 : ℂ) ^ b_low ≠ 0 := pow_ne_zero _ two_ne_zero
    have hneH : (2 : ℂ) ^ b_high ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [hpow]
    push_cast
    field_simp [hneL, hneH]
    ring
  rw [hsqrt, hexp]
  ring

private theorem locLeft_env_eq_iff_locRight (k b : ℕ) (i j : Fin (2 ^ (k + b))) :
    ((locLeft k b).basisSplitEquiv i).2 = ((locLeft k b).basisSplitEquiv j).2 ↔
      (locRight k b).extractIndex i = (locRight k b).extractIndex j := by
  rw [(locLeft k b).basisSplit_environment_eq_iff, ← (basisBits b).apply_eq_iff_eq, funext_iff]
  simp only [QRegister.AgreeOutside, QRegister.basisBits_extractIndex]
  constructor
  · intro h idx
    apply h (locRight k b idx)
    rintro ⟨l, hl⟩
    have hv := congrArg Fin.val hl
    simp [locLeft, locLeftOf, locRight, locRightOf, QRegister.block] at hv
    omega
  · intro h w hw
    have hge : k ≤ w.val := by
      by_contra hlt
      exact hw ⟨⟨w.val, by omega⟩, by ext; simp [locLeft, locLeftOf]⟩
    have hw_eq : w = locRight k b ⟨w.val - k, by omega⟩ := by
      ext
      simp [locRight, locRightOf]
      omega
    rw [hw_eq]
    exact h ⟨w.val - k, by omega⟩

private theorem locRight_env_eq_iff_locLeft (k b : ℕ) (i j : Fin (2 ^ (k + b))) :
    ((locRight k b).basisSplitEquiv i).2 = ((locRight k b).basisSplitEquiv j).2 ↔
      (locLeft k b).extractIndex i = (locLeft k b).extractIndex j := by
  rw [(locRight k b).basisSplit_environment_eq_iff, ← (basisBits k).apply_eq_iff_eq, funext_iff]
  simp only [QRegister.AgreeOutside, QRegister.basisBits_extractIndex]
  constructor
  · intro h idx
    apply h (locLeft k b idx)
    rintro ⟨r, hr⟩
    have hv := congrArg Fin.val hr
    simp [locLeft, locLeftOf, locRight, locRightOf, QRegister.block] at hv
    omega
  · intro h w hw
    have hlt : w.val < k := by
      by_contra hge
      exact hw ⟨⟨w.val - k, by omega⟩, by ext; simp [locRight, locRightOf]; omega⟩
    have hw_eq : w = locLeft k b ⟨w.val, hlt⟩ := by
      ext
      simp [locLeft, locLeftOf]
    rw [hw_eq]
    exact h ⟨w.val, hlt⟩

/-- `tensorState` with `Pi.single 0 1` on the environment equals `prodState` with
`Pi.single 0 1`. -/
theorem tensorState_single_zero_eq_prodState {k b : ℕ} (ξ : Fin (2 ^ k) → ℂ) :
    (locLeft k b).tensorState ξ (Pi.single 0 1) = prodState ξ (Pi.single 0 1) := by
  funext g
  simp only [QRegister.tensorState, prodState, prodStateOf]
  congr 1
  have h0env : ((locLeft k b).basisSplitEquiv (0 : Fin (2 ^ (k + b)))).2 = 0 := by
    funext e
    rw [(locLeft k b).basisSplitEquiv_apply_snd, basisBits_zero_at]
    rfl
  have h0right : (locRight k b).extractIndex (0 : Fin (2 ^ (k + b))) = 0 := by
    rw [QRegister.extractIndex_eq_zero_iff]
    intro j
    exact basisBits_zero_at (k + b) _
  have hiff : ((locLeft k b).basisSplitEquiv g).2 = 0 ↔ (locRight k b).extractIndex g = 0 := by
    rw [← h0env, ← h0right]
    exact locLeft_env_eq_iff_locRight k b g 0
  by_cases hr : (locRight k b).extractIndex g = 0
  · have hl : ((locLeft k b).basisSplitEquiv g).2 = 0 := hiff.mpr hr
    simp [hl, hr]
  · have hl : ((locLeft k b).basisSplitEquiv g).2 ≠ 0 := mt hiff.mp hr
    simp [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hr]

theorem embedMatrix_locLeft_mulVec_prodState {k b : ℕ}
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (ξ : Fin (2 ^ k) → ℂ) (φ : Fin (2 ^ b) → ℂ) :
    (locLeft k b).embedMatrix A *ᵥ prodState ξ φ = prodState (A *ᵥ ξ) φ := by
  funext g
  simp only [Matrix.mulVec, dotProduct, QRegister.embedMatrix_apply, prodState, prodStateOf]
  rw [← Equiv.sum_comp (blockSplitEquiv k b).symm, Fintype.sum_prod_type]
  have hCollapse : ∀ x' : Fin (2 ^ k),
      (∑ y' : Fin (2 ^ b),
        (A ((locLeft k b).extractIndex g)
          ((locLeft k b).extractIndex ((blockSplitEquiv k b).symm (x', y'))) *
          if ((locLeft k b).basisSplitEquiv g).2 =
              ((locLeft k b).basisSplitEquiv ((blockSplitEquiv k b).symm (x', y'))).2
          then 1 else 0) *
          (ξ ((locLeft k b).extractIndex ((blockSplitEquiv k b).symm (x', y'))) *
            φ ((locRight k b).extractIndex ((blockSplitEquiv k b).symm (x', y'))))) =
      (A ((locLeft k b).extractIndex g) x' * ξ x') * φ ((locRight k b).extractIndex g) := by
    intro x'
    rw [Fintype.sum_eq_single ((locRight k b).extractIndex g)]
    · have hEnv : ((locLeft k b).basisSplitEquiv g).2 =
          ((locLeft k b).basisSplitEquiv
            ((blockSplitEquiv k b).symm (x', (locRight k b).extractIndex g))).2 := by
        rw [locLeft_env_eq_iff_locRight, extractIndex_locRight_symm]
      simp [hEnv, extractIndex_locLeft_symm, extractIndex_locRight_symm, mul_assoc]
    · intro y' hy'
      have hEnv : ((locLeft k b).basisSplitEquiv g).2 ≠
          ((locLeft k b).basisSplitEquiv ((blockSplitEquiv k b).symm (x', y'))).2 := by
        rw [ne_eq, locLeft_env_eq_iff_locRight, extractIndex_locRight_symm]
        exact Ne.symm hy'
      simp [hEnv]
  simp_rw [hCollapse, ← Finset.sum_mul]

theorem embedMatrix_locRight_mulVec_prodState {k b : ℕ}
    (B : Matrix (Fin (2 ^ b)) (Fin (2 ^ b)) ℂ) (ξ : Fin (2 ^ k) → ℂ) (φ : Fin (2 ^ b) → ℂ) :
    (locRight k b).embedMatrix B *ᵥ prodState ξ φ = prodState ξ (B *ᵥ φ) := by
  funext g
  simp only [Matrix.mulVec, dotProduct, QRegister.embedMatrix_apply, prodState, prodStateOf]
  rw [← Equiv.sum_comp (blockSplitEquiv k b).symm, Fintype.sum_prod_type, Finset.sum_comm]
  have hCollapse : ∀ y' : Fin (2 ^ b),
      (∑ x' : Fin (2 ^ k),
        (B ((locRight k b).extractIndex g)
          ((locRight k b).extractIndex ((blockSplitEquiv k b).symm (x', y'))) *
          if ((locRight k b).basisSplitEquiv g).2 =
              ((locRight k b).basisSplitEquiv ((blockSplitEquiv k b).symm (x', y'))).2
          then 1 else 0) *
          (ξ ((locLeft k b).extractIndex ((blockSplitEquiv k b).symm (x', y'))) *
            φ ((locRight k b).extractIndex ((blockSplitEquiv k b).symm (x', y'))))) =
      ξ ((locLeft k b).extractIndex g) * (B ((locRight k b).extractIndex g) y' * φ y') := by
    intro y'
    rw [Fintype.sum_eq_single ((locLeft k b).extractIndex g)]
    · have hEnv : ((locRight k b).basisSplitEquiv g).2 =
          ((locRight k b).basisSplitEquiv
            ((blockSplitEquiv k b).symm ((locLeft k b).extractIndex g, y'))).2 := by
        rw [locRight_env_eq_iff_locLeft, extractIndex_locLeft_symm]
      simp only [hEnv, ↓reduceIte, mul_one, extractIndex_locLeft_symm, extractIndex_locRight_symm]
      ring
    · intro x' hx'
      have hEnv : ((locRight k b).basisSplitEquiv g).2 ≠
          ((locRight k b).basisSplitEquiv ((blockSplitEquiv k b).symm (x', y'))).2 := by
        rw [ne_eq, locRight_env_eq_iff_locLeft, extractIndex_locLeft_symm]
        exact Ne.symm hx'
      simp [hEnv]
  simp_rw [hCollapse, ← Finset.mul_sum]

/-!
## Part 3: Phase-Gradient Catalytic Subroutine Contract & Combinators
-/

/-- Generalized clean-workspace catalytic subroutine contract for an arbitrary catalyst state
`φ_cat : Fin (2 ^ b) → ℂ` on `rCat`:
1. `d` is a **genuine unitary** `wRaw : Unitary (2 ^ (k + b))` on `rAct.concat rCat` with clean
   workspace `rWork` (`RealizesEmbeddedUnitaryWithCleanWorkspace`), so approximate Gridsynth
   catalyst states `|φ̃_b⟩` propagate unitarily with **no** unmodeled decoherence on orthogonal
   catalyst errors;
2. When `rCat` is in `φ_cat`, `wRaw` acts as `U` on `rAct` and leaves `φ_cat` intact. -/
def RealizesCleanCatalyticSubroutineWith
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k b m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rAct : QRegister k n) (rCat : QRegister b n) (rWork : QRegister m n)
    (hac : rAct.DisjointWires rCat)
    (U : Unitary (2 ^ k)) (d : DynamicCircuit Var n) : Prop :=
  ∃ wRaw : Unitary (2 ^ (k + b)),
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace (rAct.concat rCat hac) rWork wRaw d ∧
    ∀ ξ : Fin (2 ^ k) → ℂ,
      wRaw.1 *ᵥ prodState ξ φ_cat = prodState (U.1 *ᵥ ξ) φ_cat

section CatalyticCombinators

variable {Var : Type} [Fintype Var] [DecidableEq Var] {n k b m : ℕ} [NeZero (2 ^ n)]

theorem RealizesCleanCatalyticSubroutineWith.identity
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rAct : QRegister k n) (rCat : QRegister b n) (rWork : QRegister m n)
    (hac : rAct.DisjointWires rCat) :
    RealizesCleanCatalyticSubroutineWith (Var := Var) φ_cat rAct rCat rWork hac 1 .identity := by
  refine ⟨1, DynamicCircuit.realizesEmbeddedUnitaryWithCleanWorkspace_identity _ _, ?_⟩
  intro ξ
  simp

theorem RealizesCleanCatalyticSubroutineWith.congrUnitary
    {φ_cat : Fin (2 ^ b) → ℂ}
    {rAct : QRegister k n} {rCat : QRegister b n} {rWork : QRegister m n}
    {hac : rAct.DisjointWires rCat}
    {U₁ U₂ : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : RealizesCleanCatalyticSubroutineWith φ_cat rAct rCat rWork hac U₁ d)
    (hU : U₁ = U₂) :
    RealizesCleanCatalyticSubroutineWith φ_cat rAct rCat rWork hac U₂ d :=
  hU ▸ hd

theorem RealizesCleanCatalyticSubroutineWith.seq
    {φ_cat : Fin (2 ^ b) → ℂ}
    {rAct : QRegister k n} {rCat : QRegister b n} {rWork : QRegister m n}
    {hac : rAct.DisjointWires rCat}
    (hdisj : (rAct.concat rCat hac).DisjointWires rWork)
    {U₁ U₂ : Unitary (2 ^ k)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : RealizesCleanCatalyticSubroutineWith φ_cat rAct rCat rWork hac U₁ d₁)
    (h₂ : RealizesCleanCatalyticSubroutineWith φ_cat rAct rCat rWork hac U₂ d₂) :
    RealizesCleanCatalyticSubroutineWith φ_cat rAct rCat rWork hac (U₂ * U₁) (.seq d₁ d₂) := by
  obtain ⟨w₁, hw₁, hc₁⟩ := h₁
  obtain ⟨w₂, hw₂, hc₂⟩ := h₂
  refine ⟨w₂ * w₁, hw₁.seq hdisj hw₂, ?_⟩
  intro ξ
  calc
    (w₂ * w₁).1 *ᵥ prodState ξ φ_cat
        = w₂.1 *ᵥ (w₁.1 *ᵥ prodState ξ φ_cat) := by
            rw [Submonoid.coe_mul, Matrix.mulVec_mulVec]
    _ = w₂.1 *ᵥ prodState (U₁.1 *ᵥ ξ) φ_cat := by rw [hc₁]
    _ = prodState (U₂.1 *ᵥ (U₁.1 *ᵥ ξ)) φ_cat := hc₂ (U₁.1 *ᵥ ξ)
    _ = prodState ((U₂ * U₁).1 *ᵥ ξ) φ_cat := by
            rw [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem CatalyticCleanSubroutine.identity
    (rAct : QRegister k n) (rCat : QRegister b n) (rWork : QRegister m n)
    (hac : rAct.DisjointWires rCat) :
    CatalyticCleanSubroutine (Var := Var) rAct rCat rWork hac 1 .identity :=
  RealizesCleanCatalyticSubroutineWith.identity (phaseGradientState b) rAct rCat rWork hac

end CatalyticCombinators

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular

end
